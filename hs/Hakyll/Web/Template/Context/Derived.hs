{-# LANGUAGE RankNTypes #-}

module Hakyll.Web.Template.Context.Derived where

import Hakyll
import Text.Printf

addDerivedField
  :: String
  -> (forall b. Context b -> [String] -> Item b -> Compiler ContextField)
  -> Context a
  -> Context a
addDerivedField key derive ctx = Context $ \k a i ->
  if k == key then
    derive ctx a i
  else do
    fld <- unContext ctx k a i
    return $
      case fld of
        -- If the field is a list, recursively derive the field for any list items.
        ListField itemCtx items -> ListField (addDerivedField key derive itemCtx) items
        -- Otherwise, simply return the field.
        otherFld                -> otherFld



-- Retrieve a String from the context
getString :: String -> Context a -> [String] -> Item a -> Compiler String
getString key ctx a i = do
  fld <- unContext ctx key a i
  case fld of
    StringField str -> return str
    _ -> fail $ printf "Key '%s' does not return a String" key
