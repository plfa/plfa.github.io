module PLFA.Build.Gather where

import Control.Monad (forM)
import PLFA.Build.Agda
import PLFA.Build.Prelude

--------------------------------------------------------------------------------
-- Helpers for gathering files
--------------------------------------------------------------------------------

allowOnly :: [FilePath] -> FilterPredicate
allowOnly allowDirs = depth ==? 0 ||? depth ==? 1 &&? filePath ==*? allowDirs ||? depth >? 1

gather :: FilterPredicate -> FilterPredicate -> [FilePath] -> IO [FilePath]
gather p1 p2 dirs = concat <$> traverse (find p1 p2) dirs

gatherAgdaLibs :: [FilePath] -> IO [AgdaLib]
gatherAgdaLibs dirs = do
  agdaLibFiles <- gather always (regularFile &&? extensions ==? ".agda-lib") dirs
  traverse readAgdaLib agdaLibFiles

gatherMdFiles :: [FilePath] -> IO [FilePath]
gatherMdFiles dirs =
  gather always (regularFile &&? extension ==? ".md") dirs

gatherLagdaMdFiles :: [FilePath] -> IO [FilePath]
gatherLagdaMdFiles dirs =
  gather always (regularFile &&? extensions ==? ".lagda.md") dirs

gatherLagdaMdFilesForAgdaLib :: AgdaLib -> IO [FilePath]
gatherLagdaMdFilesForAgdaLib agdaLib =
  gatherLagdaMdFiles (libIncludes agdaLib)

gatherLagdaMdFilesForAgdaLibs :: [AgdaLib] -> IO [(AgdaLib, [FilePath])]
gatherLagdaMdFilesForAgdaLibs agdaLibs =
  forM agdaLibs $ \agdaLib -> do
    lagdaMdFiles <- gatherLagdaMdFilesForAgdaLib agdaLib
    return (agdaLib, lagdaMdFiles)

gatherSassFiles :: [FilePath] -> IO [FilePath]
gatherSassFiles dirs =
  gather always (regularFile &&? extensions ==? ".scss") dirs
