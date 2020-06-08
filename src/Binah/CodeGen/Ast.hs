module Binah.CodeGen.Ast where

import           Data.Data
import           Data.List
import           Data.Maybe
import           Data.Typeable
import           Text.Printf                    ( printf )

import           Binah.CodeGen.Helpers
import           Binah.CodeGen.UX

data Binah = Binah
  { binahDecls  :: [Decl]
  , binahInline :: Maybe String
  }
  deriving Show


----------------------------------------------------------------------------------------------------
-- | Top level declarations
----------------------------------------------------------------------------------------------------

data Decl
  = RecDecl Rec
  | PredDecl Pred
  | PolicyDecl String Policy
  | ImportDecl String
  deriving Show

recordDecls :: [Decl] -> [Rec]
recordDecls = mapMaybe f
 where
  f (RecDecl record) = Just record
  f _                = Nothing

predDecls :: [Decl] -> [Pred]
predDecls = mapMaybe f
 where
  f (PredDecl pred) = Just pred
  f _               = Nothing

policyDecls :: [Decl] -> [(String, Policy)]
policyDecls = mapMaybe f
 where
  f (PolicyDecl name pred) = Just (name, pred)
  f _                      = Nothing

importDecls :: [Decl] -> [String]
importDecls = mapMaybe f
 where
  f (ImportDecl s) = Just s
  f _              = Nothing

----------------------------------------------------------------------------------------------------
-- | Predicates
----------------------------------------------------------------------------------------------------

data Pred = Pred
  { predName   :: String
  , predArgtys :: [String]
  }
  deriving Show

----------------------------------------------------------------------------------------------------
-- | Records
----------------------------------------------------------------------------------------------------

data Rec = Rec
  { recName    :: String
  , recItems   :: [RecItem]
  }
  deriving Show

data RecItem
  = FieldItem Field
  | AssertItem Assert
  | ReadItem ReadPolicy
  | InsertItem PolicyAttr
  | UpdateItem UpdatePolicy
  deriving Show

recReadPolicies :: Rec -> String -> [PolicyAttr]
recReadPolicies (Rec _ items) fieldName = fieldPolicy ++ mapMaybe f items
 where
  fields      = filterFields items
  fieldPolicy = mapMaybe (\(Field n _ _ p) -> if n == fieldName then p else Nothing) fields
  f (ReadItem (ReadPolicy fields policy)) | fieldName `elem` fields = Just policy
  f _ = Nothing

recUpdatePolicies :: Rec -> String -> [PolicyAttr]
recUpdatePolicies (Rec _ items) fieldName = mapMaybe f items
 where
  f (UpdateItem (UpdatePolicy fields policy)) | fieldName `elem` fields = Just policy
  f _ = Nothing

recAllReadPolicies :: Rec -> [PolicyAttr]
recAllReadPolicies (Rec _ items) = fieldPolicies ++ mapMaybe f items
 where
  fieldPolicies = mapMaybe fieldPolicy (filterFields items)
  f (ReadItem (ReadPolicy _ policy)) = Just policy
  f _ = Nothing

fieldItem :: RecItem -> Maybe Field
fieldItem (FieldItem item) = Just item
fieldItem _                = Nothing

mapFields :: (Field -> a) -> [RecItem] -> [a]
mapFields f = mapMaybe (fmap f . fieldItem)

filterFields :: [RecItem] -> [Field]
filterFields = mapFields id

insertItem :: RecItem -> Maybe PolicyAttr
insertItem (InsertItem item) = Just item
insertItem _                 = Nothing

lookupInsertPolicy :: [RecItem] -> Maybe PolicyAttr
lookupInsertPolicy = safeHead . mapMaybe insertItem

assertItem :: RecItem -> Maybe Assert
assertItem (AssertItem item) = Just item
assertItem _                 = Nothing

mapAsserts :: (Assert -> a) -> [RecItem] -> [a]
mapAsserts f = mapMaybe (fmap f . assertItem)

filterAsserts :: [RecItem] -> [Assert]
filterAsserts = mapAsserts id

data Field = Field
  { fieldName   :: String
  , fieldTyp    :: String
  , fieldMaybe  :: Bool
  , fieldPolicy :: Maybe PolicyAttr
  }
  deriving Show

data UpdatePolicy = UpdatePolicy [String] PolicyAttr deriving Show

data ReadPolicy = ReadPolicy [String] PolicyAttr deriving Show

data PolicyAttr
  = InlinePolicy Policy
  | PolicyRef String SourceSpan
  deriving Show

policyRef :: PolicyAttr -> Maybe String
policyRef (PolicyRef name _) = Just name
policyRef _                  = Nothing

inlinePolicy :: PolicyAttr -> Maybe Policy
inlinePolicy (InlinePolicy policy) = Just policy
inlinePolicy _                     = Nothing

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

data Policy = Policy
  { policyArgs :: [String]
  , policyBody :: Reft
  }
  deriving Show

policyTrue :: Int -> Policy
policyTrue nargs = Policy (replicate nargs "_") (RConst "True")

--------------------------------------------------------------------------------
-- | Refinements
--------------------------------------------------------------------------------

data Reft
  = ROps [Reft] [String]
  | RApp [Reft]
  | RParen Reft
  | RConst String
  deriving Show

newtype Assert = Assert Reft deriving Show

disjunction :: [Reft] -> Reft
disjunction []    = RConst "False"
disjunction refts = ROps (map RParen refts) (replicate (length refts - 1) "||")

implies :: Reft -> Reft -> Reft
implies p1 p2 = ROps [RParen p1, RParen p2] ["=>"]

--------------------------------------------------------------------------------
-- | Policies with an alpha normalized refinement
--------------------------------------------------------------------------------

data NormalizedPolicy = NormalizedPolicy Int Reft

normalize :: Policy -> NormalizedPolicy
normalize (Policy args body) = NormalizedPolicy (length args) (f body)
 where
  f (ROps refts ops) = ROps (map f refts) ops
  f (RApp   refts  ) = RApp (map f refts)
  f (RParen reft   ) = RParen (f reft)
  f (RConst s      ) = case elemIndex s args of
    Nothing -> RConst s
    Just i  -> RConst $ normalizedArg i

policyDisjunction :: Int -> [NormalizedPolicy] -> NormalizedPolicy
policyDisjunction nargs policies = NormalizedPolicy nargs (disjunction bodies)
  where bodies = map (\(NormalizedPolicy _ b) -> b) policies

unnormalize :: NormalizedPolicy -> Policy
unnormalize (NormalizedPolicy nargs body) = Policy args body
  where args = map normalizedArg [0 .. nargs - 1]

mapBody1 :: (String -> Reft -> Reft) -> NormalizedPolicy -> NormalizedPolicy
mapBody1 f (NormalizedPolicy nargs body) =
  NormalizedPolicy (max nargs 1) (f (normalizedArg 0) body)

normalizedArg :: Int -> String
normalizedArg = printf "x_%d"
