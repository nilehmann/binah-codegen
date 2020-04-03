{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}

module Render
  ( render
  )
where

import           Data.Char
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Text.QuasiText
import           Text.Printf

import           Ast

render :: Decls -> Text
render decls = [embed|
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Model where

import           Database.Persist               ( Key )
import           Database.Persist.TH            ( share
                                                , mkMigrate
                                                , mkPersist
                                                , sqlSettings
                                                , persistLowerCase
                                                )
import           Data.Text                      ( Text )
import qualified Database.Persist              as Persist

import           Binah.Core

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
$(it "\n\n" persistentRecord records)
|~]

{-@
data EntityFieldWrapper record typ < policy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   > = EntityFieldWrapper _
@-}

data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

$(it "\n\n" predicate preds)

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

$(it "\n\n" policy policies)

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

$(it "\n\n" binahRecord records)
|]
 where
  records  = recordDecls decls
  preds    = predDecls decls
  policies = policyDecls decls

persistentRecord :: Rec -> Text
persistentRecord (Rec name fields _) = [embed|
$name
  $(it "\n  " fmtField fields)
|]
  where fmtField (Field name typ _) = printf "%s %s" name typ :: String

predicate :: Pred -> Text
predicate (Pred name argtys) = [embed|
{-@ measure $name :: $(it " -> " id argtys) -> Bool @-}
|]

policy (Policy name args body) = [embed|
{-@ predicate $name $(upper (unwords args)) = $(unwords (map upperIfArg body)) @-}
|]
 where
  upper = map toUpper
  upperIfArg t | t `elem` args = upper t
  upperIfArg t                 = t

binahRecord :: Rec -> Text
binahRecord (Rec recName fields asserts) = [embed|
-- * $recName

{-@ data $recName = $recName
  { $(it "\n  , " fmtField fields)
  }
@-}

$(it "\n\n" (assert recName fields) asserts)

$(entityKey recName)

$(it "\n\n" (entityField recName) fields)
|]
  where fmtField (Field name _ _) = printf "%s :: _" (accessorName recName name) :: String

assert :: String -> [Field] -> Assert -> Text
assert recName fields (Assert body) = [embed|
{-@ invariant {v: $recName | $(it " " f body) } @-}
|]
 where
  fieldNames = map fieldName fields
  f x | x `elem` fieldNames = printf "(%s (entityVal v))" (accessorName recName x)
  f x | x == "entityKey"    = "(entityKey v)"
  f x                       = x

entityKey recName = [embed|
{-@ assume $entityField :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  >
@-}
|]
  where entityField = entityFieldName recName "id"

entityField recName (Field fieldName typ policy) = [embed|
{-@ assume $entityField :: EntityFieldWrapper <
    {\row viewer -> $(fmtPolicy policy)}
  , {\row field  -> field == $accessor (entityVal row)}
  , {\field row  -> field == $accessor (entityVal row)}
  >
@-}
|]
 where
  entityField = entityFieldName recName fieldName
  accessor    = accessorName recName fieldName
  fmtPolicy Nothing           = "True"
  fmtPolicy (Just policyName) = printf "%s row viewer" policyName

accessorName :: String -> String -> String
accessorName recName fieldName = mapHead toLower recName ++ mapHead toUpper fieldName

entityFieldName :: String -> String -> String
entityFieldName recName fieldName = accessorName recName fieldName ++ "'"

mapHead :: (a -> a) -> [a] -> [a]
mapHead f (x : xs) = f x : xs
mapHead _ []       = []

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

it :: (ToText a, ToText c) => a -> (b -> c) -> [b] -> Text
it separator f = T.intercalate (toText separator) . map (toText . f)

class ToText a where
  toText :: a -> Text

instance ToText Text where
  toText t = t

instance ToText [Char] where
  toText = T.pack
