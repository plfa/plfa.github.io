{-# LANGUAGE OverloadedStrings #-}

module Hakyll.Web.Template.Context.Metadata where

import           Control.Monad ((<=<))
import           Data.Aeson (Object, Value(..))
import qualified Data.HashMap.Strict as H
import qualified Data.Text as T
import qualified Data.Vector as V
import           Hakyll
import           Text.Printf (printf)

-- |Create a context from a JSON object which loads the included file and uses it to generate a context.
includeContext :: Context String -> Context Object
includeContext ctx = Context $ \k a i -> do
  let o = itemBody i
  v <- lookupObject "include" o
  identifier <- fromFilePath <$> toString v
  unContext (ctx <> metadataContext ctx) k a =<< load identifier

-- |Create a Context based on a JSON Object.
objectContext :: Context String -> Context Object
objectContext ctx = Context $ \k _ i -> do
  let o = itemBody i
  decodeValue ctx =<< lookupObject k o

-- |Decode a JSON Value to a context field.
decodeValue :: Context String -> Value -> Compiler ContextField
decodeValue ctx (Array a) = do
  objs <- mapM (makeItem <=< toObject) (V.toList a)
  return $ ListField (includeContext ctx <> objectContext ctx) objs
decodeValue _ctx (String s) = return . StringField $ T.unpack s
decodeValue _ctx (Number n) = return . StringField $ show n
decodeValue _ctx (Bool   b) = return . StringField $ show b
decodeValue _ctx v          = fail $ printf "Unsupported value '%s'" (show v)

-- |Create a Context based on the Metadata.
metadataContext :: Context String -> Context String
metadataContext ctx = Context $ \k a i -> do
  let identifier = itemIdentifier i
  metadata <- getMetadata identifier
  item <- makeItem metadata
  unContext (objectContext ctx) k a item

lookupObject :: String -> Object -> Compiler Value
lookupObject k o = maybe ifNotFound ifFound (H.lookup (T.pack k) o)
  where
    ifFound    = return
    ifNotFound = fail $ printf "Key '%s' undefined in context '%s'" k (show o)

toObject :: MonadFail m => Value -> m Object
toObject (Object o) = return o
toObject v          = fail $ printf "Not an object '%s'" (show v)

toString :: MonadFail m => Value -> m String
toString (String s) = return (T.unpack s)
toString v          = fail $ printf "Not a string '%s'" (show v)
