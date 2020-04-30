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
  }
  deriving Show

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

data Field = Field
  { fieldName   :: String
  , fieldTyp    :: String
  , fieldPolicy :: FieldPolicy
  } deriving Show

data FieldPolicy = InlinePolicy Policy | PolicyName String | NoPolicy deriving Show

data Reft
  = ROps [Reft] [String]
  | RApp [Reft]
  | RParen Reft
  | RConst String
  deriving Show

newtype Assert = Assert Reft deriving Show
