{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE FlexibleInstances #-}

module Binah.CodeGen.Render
  ( render
  )
where

import qualified Control.Exception             as Ex
import           Data.Char
import           Data.Maybe
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.List                      ( nub )
import           Data.Function                  ( (&) )
import           Data.FuzzySet                  ( FuzzySet(..) )
import qualified Data.FuzzySet                 as F
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

data UserError = Error String deriving Show

instance Ex.Exception UserError

type Renderer = Reader Env

data Env = Env { envBinah :: Binah, envAccessors :: [String], envPolicyNames :: FuzzySet }

askInline :: MonadReader Env m => m (Maybe String)
askInline = asks $ (\(Binah _ inline) -> inline) . envBinah

askDecls :: MonadReader Env m => ([Decl] -> [a]) -> m [a]
askDecls f = asks (f . binahDecls . envBinah)

askAccessors :: MonadReader Env m => m [String]
askAccessors = asks envAccessors

nameSuggestions :: MonadReader Env m => String -> m [Text]
nameSuggestions name = do
  set <- asks envPolicyNames
  return $ map snd $ F.getWithMinScore 0.7 set (T.pack name)

lookupPolicy :: MonadReader Env m => String -> m Policy
lookupPolicy name = fromJust . lookup name <$> askDecls policyDecls

extractPolicy :: MonadReader Env m => PolicyAttr -> m Policy
extractPolicy (InlinePolicy policy) = return policy
extractPolicy (PolicyRef name _   ) = lookupPolicy name


render :: Binah -> Text
render binah@(Binah decls inline) = runReader binahR (Env binah accessors policyNames)
 where
  records = recordDecls decls
  accessors =
    concatMap (\(Rec name items) -> mapFields (accessorName name . fieldName) items) records
  policyNames = F.fromList $ map (T.pack . fst) (policyDecls decls)

binahR :: Renderer Text
binahR = do
  records      <- askDecls recordDecls
  preds        <- askDecls predDecls
  policies     <- askDecls policyDecls
  imports      <- askDecls importDecls
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
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--compile-spec" @-}

module Model
  ( $(join exports "\n  , ")
  )
where


import           Database.Persist               ( Key )
import           Database.Persist.TH            ( share
                                                , mkMigrate
                                                , mkPersist
                                                , sqlSettings
                                                , persistLowerCase
                                                )
import qualified Database.Persist              as Persist

import           Binah.Core

$(mapJoin ("import " ++) imports "\n")

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------

$(fromMaybe "" inline)

--------------------------------------------------------------------------------
-- | Persistent
--------------------------------------------------------------------------------

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
$(mapJoin persistentRecord records "\n\n")
$qqEnd

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

$(mapJoin predicateDecl preds "\n\n")

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

$(join policyDecls "\n\n")

--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ measure getJust :: Key record -> Entity record @-}

$(join binahRecords "\n\n")

|]
  where qqEnd = "|]"

exportsR :: Renderer [String]
exportsR = do
  records <- askDecls recordDecls
  return
    (  ["migrateAll"]
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
  $(mapJoin fmtField fields "\n  ")
  $(mapJoin fmtUnique uniqueConstraints "\n ")
|]
 where
  fmtField (Field name typ True  _) = printf "%s %s Maybe" name typ
  fmtField (Field name typ False _) = printf "%s %s" name typ :: String
  fields = filterFields items
  fmtUnique (UniqueConstraint name fields) = printf "%s %s" name (unwords fields) :: String
  uniqueConstraints = mapMaybe uniqueItem items

predicateDecl :: Pred -> Text
predicateDecl (Pred name argtys) = [embed|
{-@ measure $name :: $(join argtys " -> ") -> Bool @-}
|]

policyDeclR :: (String, Policy) -> Renderer Text
policyDeclR (name, (Policy args body)) = do
  renderedBody <- renderReft . argsToUpper args <$> insertEntityVal body
  return [embed|{-@ predicate $name $(upper (unwords args)) = $renderedBody @-}|]
  where upper = map toUpper

binahRecordR :: Rec -> Renderer Text
binahRecordR record@(Rec recName items) = do
  mkRec        <- mkRecR record
  entityFields <- mapM (entityFieldR record) fields
  return [embed|
-- * $recName
$mkRec

{-@ invariant {v: Entity $recName | v == getJust (entityKey v)} @-}

$(mapJoin (assert recName fields) asserts "\n\n")

$(entityKey recName)

$(join entityFields "\n\n")
|]
 where
  fields  = filterFields items
  asserts = filterAsserts items

mkRecR :: Rec -> Renderer Text
mkRecR record@(Rec recName items) = do
  refPolicies <- mapM lookupPolicy refPolicies
  let readPolicies = map normalize (inlinePolicies ++ refPolicies)
  visibility   <- fmtPolicy $ unnormalize (policyDisjunction 2 readPolicies)
  insertPolicy <- fmtPolicyAttr insertPolicy
  return [embed|
{-@ mk$recName ::
     $(join argTysWithNames "\n  -> ")
  -> BinahRecord <
       {\row -> $(join pred " && ")}
     , {$insertPolicy}
     , {$visibility}
     > (Entity User) $recName
@-}
mk$recName :: $(join argTys " -> ") -> BinahRecord (Entity User) $recName
mk$recName $argNames = BinahRecord ($recName $argNames)
|]
 where
  fields       = filterFields items
  insertPolicy = lookupInsertPolicy items
  argNames     = unwords $ map (printf "x_%d") [0 .. length fields - 1]
  argTy (Field _ typ True  _) = printf "Maybe %s" typ
  argTy (Field _ typ False _) = typ
  argTysWithNames = imap (\i fld -> printf "x_%d: %s" i (argTy fld) :: String) fields
  argTys = map argTy fields
  pred   = imap
    (\i (Field name _ _ _) ->
      printf "%s (entityVal row) == x_%d" (accessorName recName name) i :: String
    )
    fields
  allReadPolicies = recAllReadPolicies record
  inlinePolicies  = mapMaybe inlinePolicy allReadPolicies
  refPolicies     = nub $ mapMaybe policyRef allReadPolicies


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
  > (Entity User) $recName $entityFieldPersistent
@-}
$entityFieldBinah :: EntityFieldWrapper (Entity User) $recName $entityFieldPersistent
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  entityFieldBinah      = entityFieldBinahName recName "id"
  entityFieldPersistent = entityFieldPersistentName recName "id"

entityFieldR :: Rec -> Field -> Renderer Text
entityFieldR record@(Rec recName items) (Field fieldName typ maybe _) = do
  updatePolicy <- getUpdatePolicy record fieldName >>= fmtPolicy
  readPolicies <- mapM extractPolicy $ recReadPolicies record fieldName
  readPolicy   <- case map normalize readPolicies of
    []           -> fmtPolicy $ policyTrue 2
    readPolicies -> fmtPolicy . unnormalize . policyDisjunction 2 $ readPolicies
  return [embed|
{-@ measure $accessor :: $recName -> $fldTyp @-}

{-@ measure $capability :: Entity $recName -> Bool @-}

{-@ assume $entityFieldBinah :: EntityFieldWrapper <
    {$readPolicy}
  , {\row field -> field == $accessor (entityVal row)}
  , {\field row -> field == $accessor (entityVal row)}
  , {\old -> $capability old}
  , {$updatePolicy}
  > (Entity User) $recName $fldTyp
@-}
$entityFieldBinah :: EntityFieldWrapper (Entity User) $recName $fldTyp
$entityFieldBinah = EntityFieldWrapper $entityFieldPersistent
|]
 where
  fldTyp                = if maybe then printf "(Maybe %s)" typ else typ
  accessor              = accessorName recName fieldName
  entityFieldBinah      = entityFieldBinahName recName fieldName
  entityFieldPersistent = entityFieldPersistentName recName fieldName
  capability            = capabilityName recName fieldName

fmtPolicy :: Policy -> Renderer String
fmtPolicy (Policy args body) = do
  renderedBody <- renderReft <$> insertEntityVal body
  return $ printf "\\%s -> %s" (unwords args) renderedBody

fmtPolicyAttr :: Maybe PolicyAttr -> Renderer String
fmtPolicyAttr policyAttr = do
  policy <- case policyAttr of
    Nothing         -> return (policyTrue 2)
    Just policyAttr -> extractPolicy policyAttr
  fmtPolicy policy

accessorName :: String -> String -> String
accessorName recName fieldName = mapHead toLower recName ++ mapHead toUpper fieldName

entityFieldBinahName :: String -> String -> String
entityFieldBinahName recName fieldName = accessorName recName fieldName ++ "'"

entityFieldPersistentName :: String -> String -> String
entityFieldPersistentName recName fieldName = recName ++ mapHead toUpper fieldName

capabilityName :: String -> String -> String
capabilityName recName fieldName = accessorName recName fieldName ++ "Cap"

--------------------------------------------------------------------------------
-- | Refinements
--------------------------------------------------------------------------------

renderReft :: Reft -> String
renderReft (ROps refts ops) = unwords $ interleave (map renderReft refts) ops
renderReft (RApp   refts  ) = unwords (map renderReft refts)
renderReft (RParen reft   ) = printf "(%s)" (renderReft reft)
renderReft (RConst s      ) = s

insertEntityVal :: Reft -> Renderer Reft
insertEntityVal reft = do
  accessors <- askAccessors
  let f (ROps refts ops) = ROps (map f refts) ops
      f (RApp [RConst s, r]) | s `elem` accessors =
        RApp [RConst s, RParen (RApp [RConst "entityVal", f r])]
      f (RApp   refts) = RApp (map f refts)
      f (RParen reft ) = RParen (f reft)
      f (RConst s    ) = RConst s
  return (f reft)

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

getUpdatePolicy :: Rec -> String -> Renderer Policy
getUpdatePolicy record fieldName = do
  updatePolicies <- mapM extractPolicy $ recUpdatePolicies record fieldName
  case updatePolicies of
    [] -> return nullaryCase
    _  -> return . unnormalize . addCapability . policyDisjunction 3 $ map normalize updatePolicies
 where
  capability  = capabilityName (recName record) fieldName
  nullaryCase = Policy ["old", "_", "_"] (RApp [RConst capability, RConst "old"])
  addCapability policy =
    mapBody1 (\arg1 body -> implies body (RApp [RConst capability, RConst arg1])) policy
