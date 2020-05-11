{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}

module Binah.CodeGen.Render
  ( render
  )
where

import           Data.Char
import           Data.Maybe
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.List                      ( nub )
import           Text.QuasiText
import           Text.Printf

import           Binah.CodeGen.Ast

render :: Binah -> Text
render (Binah decls inline) = [embed|
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--compile-spec" @-}

module Model 
  ( $(it id (exports records) "\n  , ")
  )

where

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
$(it persistentRecord records "\n\n")
$qqEnd

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

$(it predicateDecl preds "\n\n")

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

$(it (uncurry $ policyDecl accessors) policies "\n\n")

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ data BinahRecord record < 
    p :: Entity record -> Bool
  , insertpolicy :: Entity record -> Entity User -> Bool
  , querypolicy  :: Entity record -> Entity User -> Bool 
  >
  = BinahRecord _
@-}
data BinahRecord record = BinahRecord record
{-@ data variance BinahRecord invariant invariant invariant invariant @-}

{-@ persistentRecord :: BinahRecord record -> record @-}
persistentRecord :: BinahRecord record -> record
persistentRecord (BinahRecord record) = record

{-@ measure getJust :: Key record -> Entity record @-}

$(it (binahRecord policies accessors) records "\n\n")

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------

$(fromMaybe "" inline)

|]
 where
  qqEnd    = "|]"
  records  = recordDecls decls
  preds    = predDecls decls
  policies = policyDecls decls
  accessors =
    concatMap (\(Rec name fields _ _) -> map (accessorName name . fieldName) fields) records

exports :: [Rec] -> [String]
exports records =
  ["EntityFieldWrapper(..)", "migrateAll", "BinahRecord", "persistentRecord"]
    ++ mkFuns
    ++ recNames
    ++ entityFields
    ++ recIds
 where
  recNames     = map recName records
  recIds       = map (++ "Id") recNames
  mkFuns       = map ("mk" ++) recNames
  entityFields = concatMap
    (\(Rec name fields _ _) ->
      entityFieldBinahName name "id" : map (entityFieldBinahName name . fieldName) fields
    )
    records

persistentRecord :: Rec -> Text
persistentRecord (Rec name fields _ _) = [embed|
$name
  $(it fmtField fields "\n  ")
|]
  where fmtField (Field name typ _) = printf "%s %s" name typ :: String

predicateDecl :: Pred -> Text
predicateDecl (Pred name argtys) = [embed|
{-@ measure $name :: $(it id argtys " -> ") -> Bool @-}
|]

policyDecl :: [String] -> String -> Policy -> Text
policyDecl accessors name (Policy args body) = [embed|
{-@ predicate $name $(upper (unwords args)) = $(renderReft (f body)) @-}
|]
 where
  upper = map toUpper
  f     = argsToUpper args . insertEntityVal accessors

binahRecord :: [(String, Policy)] -> [String] -> Rec -> Text
binahRecord policies accessors (Rec recName fields asserts insertPolicy) = [embed|
-- * $recName

$(it fmtField fields "\n")

{-@ mk$recName :: 
     $(it id argTys "\n  -> ")
  -> BinahRecord < 
       {\row -> $(it id pred " && ")}
     , {$(fmtPolicyAttr accessors policies insertPolicy)}
     , {$(fmtPolicy accessors disjPolicy)}
     > $recName
@-}
mk$recName $argNames = BinahRecord ($recName $argNames)

{-@ invariant {v: Entity $recName | v == getJust (entityKey v)} @-}

$(it (assert recName fields) asserts "\n\n")

$(entityKey recName)

$(it (entityField policies accessors recName) fields "\n\n")
|]
 where
  fmtField (Field name ty _) =
    printf "{-@ measure %s :: %s -> %s @-}" (accessorName recName name) recName ty :: String
  argNames = unwords $ map (printf "x_%d") [0 .. length fields - 1]
  argTys   = imap (\i (Field name typ _) -> printf "x_%d: %s" i typ :: String) fields
  pred     = imap
    (\i (Field name _ _) ->
      printf "%s (entityVal row) == x_%d" (accessorName recName name) i :: String
    )
    fields
  inlinePolicies = mapMaybe (inlinePolicy . fieldPolicy) fields
  policyRefs     = map getPolicy . nub $ mapMaybe (policyRef . fieldPolicy) fields
  fieldPolicies  = inlinePolicies ++ policyRefs
  getPolicy      = fromJust . flip lookup policies
  policyBodies   = map (\(Policy [row, viewer] body) -> normalizeBody row viewer body) fieldPolicies
  disjPolicy     = Policy ["row", "viewer"] (disjunction policyBodies)

assert :: String -> [Field] -> Assert -> Text
assert recName fields (Assert body) = [embed|
{-@ invariant {v: Entity $recName | $(renderReft (f body))} @-}
|]
 where
  fieldNames = map fieldName fields
  f (ROps refts ops) = ROps (map f refts) ops
  f (RApp   refts  ) = RApp (map f refts)
  f (RParen reft   ) = RParen (f reft)
  f (RConst s) | s `elem` fieldNames =
    RParen (RApp [RConst (accessorName recName s), RParen (RApp [RConst "entityVal", RConst "v"])])
  f (RConst s) | s == "entityKey" = RParen (RApp [RConst "entityKey", RConst "v"])
  f (RConst s)                    = RConst s

entityKey :: String -> Text
entityKey recName = [embed|
{-@ assume $entityFieldBinah :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
$entityFieldBinah :: EntityFieldWrapper $recName $entityFieldPersistent
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  entityFieldBinah      = entityFieldBinahName recName "id"
  entityFieldPersistent = entityFieldPersistentName recName "id"

entityField :: [(String, Policy)] -> [String] -> String -> Field -> Text
entityField policies accessors recName (Field fieldName typ policy) = [embed|
{-@ assume $entityFieldBinah :: EntityFieldWrapper <
    {$(fmtPolicyAttr accessors policies policy)}
  , {\row field  -> field == $accessor (entityVal row)}
  , {\field row  -> field == $accessor (entityVal row)}
  > _ _
@-}
$entityFieldBinah :: EntityFieldWrapper $recName $typ
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  accessor              = accessorName recName fieldName
  entityFieldBinah      = entityFieldBinahName recName fieldName
  entityFieldPersistent = entityFieldPersistentName recName fieldName

fmtPolicy :: [String] -> Policy -> String
fmtPolicy accessors (Policy args body) = printf "\\%s -> %s" (unwords args) renderedBody
  where renderedBody = renderReft (insertEntityVal accessors body)

fmtPolicyAttr :: [String] -> [(String, Policy)] -> PolicyAttr -> String
fmtPolicyAttr accessors policies fieldPolicy = printf "\\%s -> %s" (unwords args) renderedBody
 where
  Policy args body = fromMaybe policyTrue (extractPolicy policies fieldPolicy)
  renderedBody     = renderReft (insertEntityVal accessors body)
  extractPolicy _        NoPolicy              = Nothing
  extractPolicy policies (PolicyRef    name  ) = Just $ fromJust (lookup name policies)
  extractPolicy _        (InlinePolicy policy) = Just policy


accessorName :: String -> String -> String
accessorName recName fieldName = mapHead toLower recName ++ mapHead toUpper fieldName

entityFieldBinahName :: String -> String -> String
entityFieldBinahName recName fieldName = accessorName recName fieldName ++ "'"

entityFieldPersistentName :: String -> String -> String
entityFieldPersistentName recName fieldName = recName ++ mapHead toUpper fieldName

--------------------------------------------------------------------------------
-- | Refinements
--------------------------------------------------------------------------------


renderReft :: Reft -> String
renderReft (ROps refts ops) = unwords $ interleave (map renderReft refts) ops
renderReft (RApp   refts  ) = unwords (map renderReft refts)
renderReft (RParen reft   ) = printf "(%s)" (renderReft reft)
renderReft (RConst s      ) = s

insertEntityVal :: [String] -> Reft -> Reft
insertEntityVal accessors = f
 where
  f (ROps refts ops) = ROps (map f refts) ops
  f (RApp [RConst s, r]) | s `elem` accessors =
    RApp [RConst s, RParen (RApp [RConst "entityVal", f r])]
  f (RApp   refts) = RApp (map f refts)
  f (RParen reft ) = RParen (f reft)
  f (RConst s    ) = RConst s

argsToUpper :: [String] -> Reft -> Reft
argsToUpper args = f
 where
  f (ROps refts ops)           = ROps (map f refts) ops
  f (RApp   refts  )           = RApp (map f refts)
  f (RParen reft   )           = RParen (f reft)
  f (RConst s) | s `elem` args = RConst $ map toUpper s
  f (RConst s)                 = RConst s

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

it :: (ToText sep, ToText b) => (a -> b) -> [a] -> sep -> Text
it f xs sep = T.intercalate (toText sep) . map (toText . f) $ xs

class ToText a where
  toText :: a -> Text

instance ToText Text where
  toText t = t

instance ToText [Char] where
  toText = T.pack

interleave :: [a] -> [a] -> [a]
interleave (x : xs) ys = x : interleave ys xs
interleave []       ys = ys

mapHead :: (a -> a) -> [a] -> [a]
mapHead f (x : xs) = f x : xs
mapHead _ []       = []

imap :: (Int -> a -> b) -> [a] -> [b]
imap f = zipWith f [0 ..]


normalizeBody :: String -> String -> Reft -> Reft
normalizeBody row viewer = f
 where
  f (ROps refts ops) = ROps (map f refts) ops
  f (RApp   refts  ) = RApp (map f refts)
  f (RParen reft   ) = RParen (f reft)
  f (RConst s) | s == row    = RConst "row"
               | s == viewer = RConst "viewer"
               | otherwise   = RConst s
