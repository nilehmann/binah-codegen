module Ast where

import           Data.Typeable
import           Data.Data
import           Data.Maybe

newtype Decls = Decls [Decl] deriving Show

recordDecls :: Decls -> [Rec]
recordDecls (Decls decls) = mapMaybe f decls
 where
  f (RecDecl record) = Just record
  f _                = Nothing

predDecls :: Decls -> [Pred]
predDecls (Decls decls) = mapMaybe f decls
 where
  f (PredDecl pred) = Just pred
  f _               = Nothing

policyDecls :: Decls -> [Policy]
policyDecls (Decls decls) = mapMaybe f decls
 where
  f (PolicyDecl pred) = Just pred
  f _                 = Nothing

data Decl
  = RecDecl Rec
  | PredDecl Pred
  | PolicyDecl Policy
  deriving Show

data Rec = Rec
  { recName    :: String
  , recFields  :: [Field]
  , recAsserts :: [Assert]
  }
  deriving Show

data Pred = Pred
  { predName   :: String
  , predArgtys :: [String]
  }
  deriving Show

data Policy = Policy
  { policyName :: String
  , policyArgs :: [String]
  , policyBody :: [String]
  }
  deriving Show

data Field = Field
  { fieldName   :: String
  , fieldTyp    :: String
  , fieldPolicy :: Maybe String
  } deriving Show

newtype Assert = Assert [String] deriving Show
