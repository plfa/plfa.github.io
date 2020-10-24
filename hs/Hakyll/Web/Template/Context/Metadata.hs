module Hakyll.Web.Template.Context.Metadata where

import           Control.Monad ((<=<))
import           Data.Aeson (Object, Value(..))
import qualified Data.HashMap.Strict as H
import qualified Data.Text as T
import qualified Data.Vector as V
import           Hakyll
import           Text.Printf (printf)

-- |Create a Context based on a JSON Object.
objectContext :: Context String -> Context Object
objectContext ctx = Context $ \k _ i ->
  let o = itemBody i in
  case H.lookup (T.pack k) o of
    Just  v -> decodeValue ctx v
    Nothing -> fail $ printf "Key '%s' undefined in context '%s'" k (show o)

isObject :: Value -> Bool
isObject (Object _) = True
isObject _          = False

isString :: Value -> Bool
isString (String _) = True
isString _          = False

toObject :: MonadFail m => Value -> m Object
toObject (Object o) = return o
toObject v          = fail $ printf "Not an object '%s'" (show v)

toString :: MonadFail m => Value -> m String
toString (String s) = return (T.unpack s)
toString v          = fail $ printf "Not a string '%s'" (show v)

-- |Decode a JSON Value to a context field.
decodeValue :: Context String -> Value -> Compiler ContextField
decodeValue ctx (Array  a)
  | V.all isObject a = do
      objs <- mapM (makeItem <=< toObject) (V.toList a)
      return $ ListField (objectContext ctx) objs
  | V.all isString a = do
      items <- mapM (load . fromFilePath <=< toString) (V.toList a)
      return $ ListField ctx items
decodeValue _ (String s) = return . StringField $ T.unpack s
decodeValue _ (Number n) = return . StringField $ show n
decodeValue _ (Bool   b) = return . StringField $ show b
decodeValue _ v          = fail $ printf "Unsupported value '%s'" (show v)

-- |Create a Context based on the Metadata.
metadataContext :: Context String -> Context String
metadataContext ctx = Context $ \k a i ->
  unContext (objectContext ctx) k a <=< makeItem <=< getMetadata $ itemIdentifier i

