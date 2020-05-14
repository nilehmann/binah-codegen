{-# LANGUAGE FlexibleContexts #-}
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
import           Data.Function                  ( (&) )
import           Text.QuasiText
import           Text.Printf

import           Binah.CodeGen.Ast
import           Control.Monad                  ( (<=<) )
import           Control.Monad.Reader           ( Reader(..)
                                                , MonadReader(..)
                                                , runReader
                                                , asks
                                                )


import           Binah.CodeGen.Helpers

type Renderer = Reader Env

data Env = Env { envBinah :: Binah, envAccessors :: [String] }

askInline :: MonadReader Env m => m (Maybe String)
askInline = asks $ (\(Binah _ inline) -> inline) . envBinah

askDecls :: MonadReader Env m => ([Decl] -> [a]) -> m [a]
askDecls f = asks (f . binahDecls . envBinah)

askAccessors :: MonadReader Env m => m [String]
askAccessors = asks envAccessors

render :: Binah -> Text
render binah@(Binah decls inline) = runReader binahR (Env binah accessors)
 where
  records = recordDecls decls
  accessors =
    concatMap (\(Rec name items) -> mapFields (accessorName name . fieldName) items) records

binahR :: Renderer Text
binahR = do
  records      <- askDecls recordDecls
  preds        <- askDecls predDecls
  policies     <- askDecls policyDecls
  inline       <- askInline
  binahRecords <- mapM binahRecordR records
  policyDecls  <- mapM policyDeclR policies
  exports      <- exportsR
  return [embed|
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--compile-spec" @-}

module Model 
  ( $(it id exports "\n  , ")
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
data EntityFieldWrapper record typ < querypolicy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   , capability :: Entity record -> Bool
                                   , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                                   > = EntityFieldWrapper _
@-}

data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant invariant invariant @-}

{-@ measure currentUser :: Entity User @-}

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

$(it predicateDecl preds "\n\n")

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

$(it id policyDecls "\n\n")

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

$(it id binahRecords "\n\n")

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------

$(fromMaybe "" inline)

|]
  where qqEnd = "|]"

exportsR :: Renderer [String]
exportsR = do
  records <- askDecls recordDecls
  return
    (  ["EntityFieldWrapper(..)", "migrateAll", "BinahRecord", "persistentRecord"]
    ++ mkRec records
    ++ map recName records
    ++ entityFields records
    ++ recIds records
    )
 where
  recIds       = map ((++ "Id") . recName)
  mkRec        = map (("mk" ++) . recName)
  entityFields = concatMap
    (\(Rec name items) ->
      entityFieldBinahName name "id" : mapFields (entityFieldBinahName name . fieldName) items
    )

persistentRecord :: Rec -> Text
persistentRecord (Rec name items) = [embed|
$name
  $(it fmtField fields "\n  ")
|]
 where
  fmtField (Field name typ _) = printf "%s %s" name typ :: String
  fields = filterFields items

predicateDecl :: Pred -> Text
predicateDecl (Pred name argtys) = [embed|
{-@ measure $name :: $(it id argtys " -> ") -> Bool @-}
|]

policyDeclR :: (String, Policy) -> Renderer Text
policyDeclR (name, (Policy args body)) = do
  accessors <- askAccessors
  let f = argsToUpper args . insertEntityVal accessors
  return [embed|
{-@ predicate $name $(upper (unwords args)) = $(renderReft (f body)) @-}
|]
  where upper = map toUpper

binahRecordR :: Rec -> Renderer Text
binahRecordR record@(Rec recName items) = do
  mkRec        <- mkRecR record
  entityFields <- mapM (entityFieldR record) fields
  return [embed|
-- * $recName
$mkRec

{-@ invariant {v: Entity $recName | v == getJust (entityKey v)} @-}

$(it (assert recName fields) asserts "\n\n")

$(entityKey recName)

$(it id entityFields "\n\n")
|]
 where
  fields  = filterFields items
  asserts = filterAsserts items

mkRecR :: Rec -> Renderer Text
mkRecR (Rec recName items) = do
  accessors <- askAccessors
  policies  <- askDecls policyDecls
  let
    fields       = filterFields items
    insertPolicy = lookupInsertPolicy items
    argNames     = unwords $ map (printf "x_%d") [0 .. length fields - 1]
    argTys       = imap (\i (Field name typ _) -> printf "x_%d: %s" i typ :: String) fields
    pred         = imap
      (\i (Field name _ _) ->
        printf "%s (entityVal row) == x_%d" (accessorName recName name) i :: String
      )
      fields
    inlinePolicies = mapMaybe (inlinePolicy <=< fieldPolicy) fields
    policyRefs     = map (lookupPolicy policies) . nub $ mapMaybe (policyRef <=< fieldPolicy) fields
    fieldPolicies  = inlinePolicies ++ policyRefs
    policyBodies =
      map (\(Policy [row, viewer] body) -> normalizeBody row viewer body) fieldPolicies
    disjPolicy = Policy ["row", "viewer"] (disjunction policyBodies)
  return [embed|
{-@ mk$recName :: 
     $(it id argTys "\n  -> ")
  -> BinahRecord < 
       {\row -> $(it id pred " && ")}
     , {$(fmtPolicyAttr accessors policies insertPolicy)}
     , {$(fmtPolicy accessors disjPolicy)}
     > $recName
@-}
mk$recName $argNames = BinahRecord ($recName $argNames)
|]


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
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
$entityFieldBinah :: EntityFieldWrapper $recName $entityFieldPersistent
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  entityFieldBinah      = entityFieldBinahName recName "id"
  entityFieldPersistent = entityFieldPersistentName recName "id"

entityFieldR :: Rec -> Field -> Renderer Text
entityFieldR (Rec recName items) (Field fieldName typ policy) = do
  policies  <- askDecls policyDecls
  accessors <- askAccessors
  let updatePolicy = findUpdatePolicy policies updatePolicies fieldName entityFieldCapability
  return [embed|

{-@ measure $accessor :: $recName -> $typ @-}

{-@ measure $entityFieldCapability :: Entity $recName -> Bool @-}

{-@ assume $entityFieldBinah :: EntityFieldWrapper <
    {$(fmtPolicyAttr accessors policies policy)}
  , {\row field  -> field == $accessor (entityVal row)}
  , {\field row  -> field == $accessor (entityVal row)}
  , {\old -> $entityFieldCapability old}
  , {$(fmtPolicy accessors updatePolicy)}
  > _ _
@-}
$entityFieldBinah :: EntityFieldWrapper $recName $typ
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  accessor              = accessorName recName fieldName
  entityFieldBinah      = entityFieldBinahName recName fieldName
  entityFieldPersistent = entityFieldPersistentName recName fieldName
  entityFieldCapability = entityFieldCapabilityName recName fieldName
  updatePolicies        = filterUpdates items

fmtPolicy :: [String] -> Policy -> String
fmtPolicy accessors (Policy args body) = printf "\\%s -> %s" (unwords args) renderedBody
  where renderedBody = renderReft (insertEntityVal accessors body)

fmtPolicyAttr :: [String] -> [(String, Policy)] -> Maybe PolicyAttr -> String
fmtPolicyAttr accessors policies fieldPolicy = printf "\\%s -> %s" (unwords args) renderedBody
 where
  Policy args body = fieldPolicy & fmap (extractPolicy policies) & fromMaybe policyTrue2
  renderedBody     = renderReft (insertEntityVal accessors body)

accessorName :: String -> String -> String
accessorName recName fieldName = mapHead toLower recName ++ mapHead toUpper fieldName

entityFieldBinahName :: String -> String -> String
entityFieldBinahName recName fieldName = accessorName recName fieldName ++ "'"

entityFieldPersistentName :: String -> String -> String
entityFieldPersistentName recName fieldName = recName ++ mapHead toUpper fieldName

entityFieldCapabilityName :: String -> String -> String
entityFieldCapabilityName recName fieldName = accessorName recName fieldName ++ "Cap"

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


findUpdatePolicy :: [(String, Policy)] -> [UpdatePolicy] -> String -> String -> Policy
findUpdatePolicy policies updatePolicies fieldName capability = policy
 where
  f (UpdatePolicy fields policyAttr) =
    if fieldName `elem` fields then Just (extractPolicy policies policyAttr) else Nothing
  Policy args body = fromMaybe policyTrue3 (safeHead . mapMaybe f $ updatePolicies)
  policy           = Policy args (implies body (RApp [RConst capability, RConst (head args)]))


extractPolicy :: [(String, Policy)] -> PolicyAttr -> Policy
extractPolicy _        (InlinePolicy policy) = policy
extractPolicy policies (PolicyRef    name  ) = lookupPolicy policies name

-- TODO: Handle not found
lookupPolicy :: [(String, Policy)] -> String -> Policy
lookupPolicy policies = fromJust . flip lookup policies
