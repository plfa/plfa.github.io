{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}

module PLFA.Build.Staged where

import Control.Monad (forM_)
import Data.Default.Class
import PLFA.Build.Prelude

type Identifier = FilePath

data Stage caches = Stage
  { -- | Maps file identifiers to the output files for this stage.
    nameAction     :: Identifier -> FilePath,
    -- | The build action to perform.
    compileAction  :: caches -> (Identifier -> FilePath) -> (Identifier -> FilePath) -> Identifier -> Action (),
    -- | Create auxiliary rules based on the stage's file mappings.
    auxiliaryRules :: (Identifier -> FilePath) -> (Identifier -> FilePath) -> Rules caches
  }

instance Default (Stage ()) where
  def = Stage
    { nameAction     = id,
      compileAction  = \caches inputPath outputPath key -> return (),
      auxiliaryRules = \inputPath outputPath -> return ()
    }

data SomeStage = forall caches. SomeStage (Stage caches)

runStagesIn :: FilePath -> [SomeStage] -> [Identifier] -> Rules ()
runStagesIn rootDir stages keys = go stages 1 id
  where
    go :: [SomeStage] -> Int -> (Identifier -> FilePath) -> Rules ()
    go [] _ _ = return ()
    go (SomeStage stage : rest) stageNum inputPath = do
      let stageDir = rootDir </> "stage" <> show stageNum
      let outputPath = \key -> normalise (stageDir </> nameAction stage key)
      caches <- auxiliaryRules stage inputPath outputPath
      forM_ keys $ \key -> do
        inputPath key %> \_ -> do
          need (map inputPath keys)
          compileAction stage caches inputPath outputPath key
      go rest (stageNum + 1) outputPath
