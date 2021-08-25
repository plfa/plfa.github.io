{-# LANGUAGE OverloadedStrings #-}

module Hakyll.Web.Template.Context.Metadata
  ( includeContext
  , metadataContext
  , objectContext
  , restoreMetadata
  ) where

import           Control.Monad ((<=<))
import           Data.Aeson (Object, Value(..))
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashMap.Strict as H
import qualified Data.Text as T
import qualified Data.Vector as V
import           Hakyll
import           Text.Printf (printf)
import qualified Data.Yaml as Y


-- |Create a |Context| from the |Metadata| associated with an |Item|.
metadataContext
  :: Context String -- ^ |Context| used when unfolding a JSON |Array| into a |ListField|.
  -> Context String
metadataContext ctx = Context $ \k a i -> do
  let identifier = itemIdentifier i
  metadata <- getMetadata identifier
  item <- makeItem metadata
  unContext (objectContext ctx) k a item

-- |Create a |Context| from a JSON |Object| which loads data from files under "include" keys.
includeContext
  :: Context String -- ^ |Context| used when unfolding a JSON |Array| into a |ListField|.
  -> Context Object
includeContext ctx = Context $ \k a i -> do
  let o = itemBody i
  v <- lookupObject "include" o
  identifier <- fromFilePath <$> toString v
  unContext (ctx <> metadataContext ctx) k a =<< load identifier

-- |Create a |Context| from a JSON |Object|.
objectContext
  :: Context String -- ^ |Context| used when unfolding a JSON |Array| into a |ListField|.
  -> Context Object
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

-- |Lookup the |Value| stored in an |Object| at the given key.
lookupObject :: MonadFail m => String -> Object -> m Value
lookupObject k o = maybe ifNotFound ifFound (H.lookup (T.pack k) o)
  where
    ifFound    = return
    ifNotFound = fail $ printf "Key '%s' undefined in context '%s'" k (show o)

-- |Convert a |Value| to an |Object|, or fail.
toObject :: MonadFail m => Value -> m Object
toObject (Object o) = return o
toObject v          = fail $ printf "Not an object '%s'" (show v)

-- |Convert a |Value| to an |String|, or fail.
toString :: MonadFail m => Value -> m String
toString (String s) = return (T.unpack s)
toString v          = fail $ printf "Not a string '%s'" (show v)


-- |Add the original |Metadata| block back to the file.
restoreMetadata :: Item String -> Compiler (Item String)
restoreMetadata item = do
  metadata <- getMetadata (itemIdentifier item)
  if H.null metadata then
    return item
  else do
    let yaml = "---\n" <> BS.unpack (Y.encode metadata) <> "---\n\n"
    withItemBody (\body -> return (yaml <> body)) item
