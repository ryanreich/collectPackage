{-# LANGUAGE TemplateHaskell #-}
{- |
Module: CollectPackage
Description: Tool for getting Haskell linking data for a library in a Stack project
Copyright: (c) Ryan Reich, 2018-2019
License: MIT
Maintainer: ryan.reich@gmail.com
Stability: experimental

This tool interprets the Cabal project data, as handled by Stack, in order
to copy (hard link) the required interface files and dynamic libraries for
linking with the library component defined in the project.  This is
different from the easier problem of collecting the dynamic linking
dependencies of an executable, which can be done using standard Linux tools
(@ldd@ and @awk@, primarily), and is a useful part of building a minimal
Docker image around a project that uses the @hint@ package, or the GHC API
in general, which of course requires this linking information to load
modules.  It is quite pointless for installing a project directly onto the
local system, however, since GHC is already present there (if not, this
tool will not work).

When run, the tool takes no arguments, attempts to find the library defined
in a Stack-based cabal project above the current directory, and places the
duplicated interfaces and dynamic libraries into an appropriate structure
in the current directory.  It actually has to be run via @stack exec@,
because it needs the environment stack provides, in particular the
@HASKELL_DIST_DIR@.

This probably only works in Linux right now.

-}

module CollectPackage where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Zip

import Data.Bits
import Data.Bool
import Data.Char
import Data.Function
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

import Distribution.InstalledPackageInfo
import Distribution.Simple.Compiler
import Distribution.Simple.Configure
import Distribution.Simple.PackageIndex
import Distribution.Text
import Distribution.Types.ComponentName
import Distribution.Types.LocalBuildInfo
import Distribution.Types.ComponentLocalBuildInfo
import Distribution.Types.UnitId

import Lens hiding ((<.>))

import GHC.PackageDb hiding (InstalledPackageInfo)
import PackageInfo

import System.Directory
import System.Environment
import System.FilePath
import System.Posix.Files

import Text.Read

-- | Ad-hoc static data collected before starting the main routine
data Info =
  Info
  {
    newRoot :: FilePath,
    ghcVersion :: String
  }

-- | Shorthand.  It has to build on 'IO' because we do serious filesystem
-- operations pretty much everywhere.
type InfoM = ReaderT Info IO

makeLenses ''InstalledPackageInfo
makeLenses ''Info

-- | For the executable
main :: IO ()
main = do
  newRoot <- getCurrentDirectory
  createDirectoryIfMissing True (libSubdir newRoot)
  createDirectoryIfMissing True (packageDBSubdir newRoot)
  (ghcVersion, packageInfo, packageIndex) <- getBuildInfo =<< getProjectRoot newRoot
  let packageInfos = packageInfo : allPackages packageIndex
  flip runReaderT Info{..} $ do
    forM_ packageInfos copyPackage
    createPackageDB packageInfos

-- | Makes a GHC package cache from the given packages.  This is not
-- necessary just for dynamic linking, but is necessary if you are going to
-- use the @hint@ package (or the GHC API in general) as an embedded
-- interpreter that needs to find packages at runtime.
createPackageDB :: [InstalledPackageInfo] -> InfoM ()
createPackageDB packageInfos = do
  Info{..} <- ask
  let newPackageInfos = minimalize . moveRoot <$> packageInfos
      ghcPackageInfos = convertPackageInfoToCacheFormat <$> newPackageInfos
      cacheFilename = packageDBSubdir newRoot </> "package.cache"
  liftIO $ do
    lock <- lockPackageDb cacheFilename
    writePackageDb cacheFilename ghcPackageInfos newPackageInfos
    unlockPackageDb lock

-- | Copies both the interface files and the dynamic libraries
copyPackage :: InstalledPackageInfo -> InfoM ()
copyPackage packageInfo = do
  copyLibraryDirs packageInfo
  copyDynLibs packageInfo
 
-- | Copies the (dynamic only) interface files, as reported by the package info.
copyLibraryDirs :: InstalledPackageInfo -> InfoM ()
copyLibraryDirs InstalledPackageInfo{libraryDirs, importDirs} = do
  Info{..} <- ask
  liftIO $ forM_ (libraryDirs `union` importDirs) $ \libDir -> do
    let newDir = replaceDirectory libDir (libSubdir newRoot)
        cond file = takeExtension file == ".dyn_hi" 
    alreadyCopied <- doesDirectoryExist newDir
    unless alreadyCopied $ fastCopyDir cond newDir libDir

-- | Copies all the dynamic libraries, as reported by the package info.
-- This deals with a few alternatives for possible names, which may include
-- the GHC version (or not; it depends if the package is part of GHC) and
-- may actually be a C library, in which case the binary name does not
-- quite match the library "name".
copyDynLibs :: InstalledPackageInfo -> InfoM ()
copyDynLibs InstalledPackageInfo{libraryDirs,libraryDynDirs,hsLibraries} = do
  Info{..} <- ask
  liftIO $ forM_ nonCLibraries $ \libName -> do
    let prefixedLib = "lib" ++ libName
        libBaseName = addSO $ prefixedLib ++ "-" ++ ghcVersion
        altLibBaseName = addSO prefixedLib 
    oldLibPathM <- altFileExistsInPath libBaseName altLibBaseName &
      sequencePath (libraryDirs `union` libraryDynDirs)
    case oldLibPathM of
      Nothing -> error $ "Dynamic library not found for: " ++ libName
      Just oldLibPath -> do
        let newLibPath = replaceDirectory oldLibPath (libSubdir newRoot)
        alreadyCopied <- doesFileExist newLibPath 
        unless alreadyCopied $ createLink oldLibPath newLibPath
  where
    altFileExistsInPath fileName1 fileName2 path = 
      getFirst <$> liftM2 ((<>) `on` First) 
        (maybeFileExists $ path </> fileName1)
        (maybeFileExists $ path </> fileName2)
    maybeFileExists path = 
      bool Nothing (Just path) <$> doesFileExist path
    nonCLibraries = nub $ removeC <$> hsLibraries
    removeC x = fromMaybe x (stripPrefix "C" x)

-- | The copy is fast because it just hard-links files, so this can't be
-- done cross-device.  The first argument, @cond@, is a predicate
-- determining whether a file in the old directory is to be linked or not.
fastCopyDir :: (FilePath -> Bool) -> FilePath -> FilePath -> IO ()
fastCopyDir cond newDir oldDir = do
  createDirectory newDir
  allFiles <- listDirectory oldDir
  forM_ allFiles $ \file -> do
    let oldFilePath = oldDir </> file
        newFilePath = newDir </> file
    isDirectory <- doesDirectoryExist oldFilePath
    if isDirectory
    then fastCopyDir cond newFilePath oldFilePath
    else when (cond file) $ createLink oldFilePath newFilePath

-- | Looks into the @distdir@, wherever Stack put it, as indicated by the
-- @HASKELL_DIST_DIR@ envvar.  This is the starting point for the entire
-- adventure: all the package and compiler info is found here.
getBuildInfo :: 
  FilePath -> IO (String, InstalledPackageInfo, InstalledPackageIndex)
getBuildInfo projectRoot = do
  distDir <- getEnv "HASKELL_DIST_DIR"
  lbi@LocalBuildInfo{compiler, installedPkgs} <- 
    getPersistBuildConfig (projectRoot </> distDir)
  packageInfo <- getLibComponent lbi
  let CompilerId flavor version = compilerId compiler 
      ghcVersion = display flavor ++ display version
  return (ghcVersion, packageInfo, installedPkgs)

-- | Finds the library component of the project from the build info
getLibComponent :: LocalBuildInfo -> IO InstalledPackageInfo
getLibComponent LocalBuildInfo{componentNameMap, withPackageDB} = do
  case Map.lookup CLibName componentNameMap of
    Nothing -> error $ "Local project does not define a library"
    Just [cLocalBuildInfo] -> do
      let unitID = componentUnitId cLocalBuildInfo
          pkgdb = pkgdbPath $ registrationPackageDB withPackageDB
          confFilePath = pkgdb </> display unitID <.> "conf"
      parseResult <- parseInstalledPackageInfo <$> readFile confFilePath
      case parseResult of
        ParseFailed err -> error $ 
          "Couldn't parse package install configuration file: " ++ confFilePath
        ParseOk _ packageInfo -> return packageInfo
    _ -> error $ "Local project (somehow) defines multiple libraries"

  where
    pkgdbPath (SpecificPackageDB path) = path
    pkgdbPath _ = error "Registration db isn't the project's"

-- | Mimics, hopefully, the ascending recursive process that @stack@ itself
-- uses to find the project root.
getProjectRoot :: FilePath -> IO FilePath
getProjectRoot [pathSeparator] = error "No stack project found"
getProjectRoot dir = do
  atRoot <- doesFileExist $ dir </> "stack" <.> "yaml"
  if atRoot
  then return dir
  else getProjectRoot (takeDirectory dir)

-- | Scans through a list of files until a lookup finally succeeds on one
-- of them.
sequencePath :: (Monad m) => [FilePath] -> (FilePath -> m (Maybe a)) -> m (Maybe a)
sequencePath paths f = go paths Nothing where
  go [] Nothing = return Nothing
  go _ (Just x) = return $ Just x
  go (path : rest) Nothing = f path >>= go rest

-- | Adjusts certain important fields of the package info to reflect its
-- new location.  The package info file hard-codes various paths that, of
-- course, need to be changed when the package is copied to a new place.
moveRoot :: InstalledPackageInfo -> InstalledPackageInfo
moveRoot pkgInfo = pkgInfo
  & _importDirs %~ map chroot
  & _libraryDirs %~ map chroot
  & _includeDirs %~ map chroot
  & _dataDir %~ chroot
  & _libraryDynDirs .~ [libDir]
  & _pkgRoot .~ Just libDir
  where 
    chroot = flip replaceDirectory libDir
    libDir = libSubdir root
    root = [pathSeparator]

-- | Since we don't do anything with the Haddocks, the relevant fields are
-- voided.
minimalize :: InstalledPackageInfo -> InstalledPackageInfo
minimalize pkgInfo = pkgInfo
  & _haddockInterfaces .~ []
  & _haddockHTMLs .~ []

-- | Universal convention for naming a library directory
libSubdir :: FilePath -> FilePath
libSubdir = (</> "lib")

-- | Universal convention for placing the package database
packageDBSubdir :: FilePath -> FilePath
packageDBSubdir = (</> "ghc-pkgdb") . libSubdir

-- | Universal convention for adding the library file extension
addSO :: FilePath -> FilePath
addSO = (<.> "so")
