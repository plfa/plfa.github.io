module Hakyll.Web.Template.Context.Title
  ( titlerunningField
  , subtitleField
  ) where

import Hakyll
import Data.List.Extra as L
import Text.Printf (printf)

titlerunningField :: Context String
titlerunningField = Context go
  where
    go "titlerunning" _ i = do
      title <- maybe (fail "No title") return =<< getMetadataField (itemIdentifier i) "title"
      case L.stripInfix ":" title of
        Nothing -> fail "No titlerunning/subtitle distinction"
        Just (titlerunning, _) -> return . StringField $ titlerunning
    go k              _ i = fail $ printf "Missing field %s in context for item %s" k (show (itemIdentifier i))


subtitleField :: Context String
subtitleField = Context go
  where
    go "subtitle" _ i = do
      title <- maybe (fail "No title") return =<< getMetadataField (itemIdentifier i) "title"
      case L.stripInfix ":" title of
        Nothing -> fail "No titlerunning/subtitle distinction"
        Just (_, subtitle) -> return . StringField $ L.trim subtitle
    go k          _ i = fail $ printf "Missing field %s in context for item %s" k (show (itemIdentifier i))
