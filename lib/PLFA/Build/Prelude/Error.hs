module PLFA.Build.Prelude.Error where

import Control.Monad.Except (Except, runExcept)
import Data.Aeson.Types (Result (..))

liftExcept :: MonadFail m => (e -> String) -> Except e a -> m a
liftExcept pretty m = liftEither pretty (runExcept m)

liftEither :: MonadFail m => (e -> String) -> Either e a -> m a
liftEither pretty (Left e) = fail (pretty e)
liftEither _      (Right a) = return a

liftMaybe :: MonadFail m => String -> Maybe a -> m a
liftMaybe errorMessage Nothing  = fail errorMessage
liftMaybe _            (Just a) = return a

liftResult :: MonadFail m => Result a -> m a
liftResult (Error msg) = fail msg
liftResult (Success a) = return a
