module PLFA.Build.Prelude
  ( module Shake,
    module Export,
    foreach
  ) where

import Control.Monad (forM_)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Development.Shake as Shake hiding (readFile', writeFile')
import PLFA.Build.Prelude.ByteString as Export
import PLFA.Build.Prelude.Error as Export
import PLFA.Build.Prelude.FilePath as Export
import PLFA.Build.Prelude.Text as Export
import PLFA.Build.Prelude.Url as Export

foreach :: Monad m => Set a -> (a -> m ()) -> m ()
foreach items act = forM_ (S.toList items) act
