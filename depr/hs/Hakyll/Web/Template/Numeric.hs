{-# LANGUAGE TupleSections #-}

module Hakyll.Web.Template.Numeric
  ( byNumericFieldAsc
  , byNumericFieldDesc
  ) where

import Hakyll
import Data.List as L
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Text.Read (readMaybe)

byNumericFieldAsc :: MonadMetadata m => String -> [Item a] -> m [Item a]
byNumericFieldAsc key = sortOnM $ \i -> do
  maybeInt <- getMetadataField (itemIdentifier i) key
  return $ fromMaybe (0 :: Int) (readMaybe =<< maybeInt)
    where
      sortOnM :: (Monad m, Ord k) => (a -> m k) -> [a] -> m [a]
      sortOnM f xs = map fst . L.sortBy (comparing snd) <$> mapM (\ x -> (x,) <$> f x) xs

byNumericFieldDesc :: MonadMetadata m => String -> [Item a] -> m [Item a]
byNumericFieldDesc key is = reverse <$> byNumericFieldAsc key is
