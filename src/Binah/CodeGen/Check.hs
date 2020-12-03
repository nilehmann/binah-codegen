module Binah.CodeGen.Check
    ( checkBinah
    )
where

import           Control.Monad.Reader           ( Reader(..)
                                                , runReader
                                                , asks
                                                )
import           Data.FuzzySet                  ( FuzzySet(..) )
import qualified Data.FuzzySet                 as F
import           Data.Maybe                     ( isJust )
import           Text.Printf                    ( printf )
import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Binah.CodeGen.Ast
import           Binah.CodeGen.Helpers
import           Binah.CodeGen.UX

type PolicySet = FuzzySet

type RecChecker = Reader RecEnv

data RecEnv = RecEnv { recEnvPolicies :: FuzzySet, recEnvFields :: FuzzySet }

checkBinah :: Binah -> [UserError]
checkBinah (Binah _ decls _) = concatMap (checkRecord policies) (recordDecls decls)
    where policies = F.fromList $ map (T.pack . fst) (policyDecls decls)

checkRecord :: PolicySet -> Rec -> [UserError]
checkRecord policies (Rec _ items) = runReader (concatMapM checkItem items) env
  where
    fields = F.fromList $ map (T.pack . fieldName) (filterFields items)
    env    = RecEnv policies fields

checkItem :: RecItem -> RecChecker [UserError]
checkItem (FieldItem (Field _ _ _ (Just (PolicyRef name ss)))) = checkPolicyRef name ss
checkItem (ReadItem (ReadPolicy _ (PolicyRef name ss))) = checkPolicyRef name ss
checkItem (UpdateItem (UpdatePolicy _ (PolicyRef name ss))) = checkPolicyRef name ss
checkItem (InsertItem (PolicyRef name ss)) = checkPolicyRef name ss
checkItem _ = return []

checkPolicyRef :: String -> SourceSpan -> RecChecker [UserError]
checkPolicyRef name ss = do
    b <- containsPolicy name
    if b then return [] else policyNotFound name ss

containsPolicy :: String -> RecChecker Bool
containsPolicy name = do
    policies <- asks recEnvPolicies
    return . isJust . F.getOneWithMinScore 1.0 policies . T.pack $ name

policyNotFound :: String -> SourceSpan -> RecChecker [UserError]
policyNotFound name ss = do
    suggestions <- nameSuggestions name
    let suggestion = case suggestions of
            []  -> ""
            [s] -> printf ". Did you mean %s?" s
            s   -> printf ". Did you mean any of [%s]?" (join s ", ")
    let msg = printf "Unknown policy %s%s" name suggestion
    return [Error msg ss]

nameSuggestions :: String -> RecChecker [Text]
nameSuggestions name = do
    policies <- asks recEnvPolicies
    return . map snd $ F.getWithMinScore 0.7 policies (T.pack name)
