module Binah.CodeGen.Ast where

import           Data.Typeable
import           Data.Data
import           Data.Maybe


data Binah = Binah
  { binahDecls  :: [Decl]
  , binahInline :: Maybe String
  }
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

data Decl
  = RecDecl Rec
  | PredDecl Pred
  | PolicyDecl String Policy
  deriving Show

data Rec = Rec
  { recName    :: String
  , recFields  :: [Field]
  , recAsserts :: [Assert]
  , recInsertPolicy :: Maybe PolicyAttr
  , recUpdatePolicies :: [UpdatePolicy]
  }
  deriving Show

data UpdatePolicy = UpdatePolicy [String] PolicyAttr deriving Show

data Pred = Pred
  { predName   :: String
  , predArgtys :: [String]
  }
  deriving Show

data Policy = Policy
  { policyArgs :: [String]
  , policyBody :: Reft
  }
  deriving Show

policyTrue2 :: Policy
policyTrue2 = Policy ["x", "y"] (RConst "True")

policyTrue3 :: Policy
policyTrue3 = Policy ["x", "y", "z"] (RConst "True")

data Field = Field
  { fieldName   :: String
  , fieldTyp    :: String
  , fieldPolicy :: Maybe PolicyAttr
  } deriving Show

data PolicyAttr = InlinePolicy Policy | PolicyRef String deriving Show

policyRef :: PolicyAttr -> Maybe String
policyRef (PolicyRef name) = Just name
policyRef _                = Nothing

inlinePolicy :: PolicyAttr -> Maybe Policy
inlinePolicy (InlinePolicy policy) = Just policy
inlinePolicy _                     = Nothing

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
