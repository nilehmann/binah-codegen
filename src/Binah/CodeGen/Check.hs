module Binah.CodeGen.Check
    ( checkBinah
    )
where

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

checkBinah :: Binah -> [UserError]
checkBinah (Binah decls _) = concatMap (checkRecord policies) (recordDecls decls)
    where policies = F.fromList $ map (T.pack . fst) (policyDecls decls)

checkRecord :: PolicySet -> Rec -> [UserError]
checkRecord policies (Rec _ items) = concatMap (checkItem policies) items

checkItem :: PolicySet -> RecItem -> [UserError]
checkItem policies (FieldItem (Field _ _ (Just (PolicyRef name ss)))) =
    [ policyNotFoundError policies name ss | not (policies `contains` name) ]
checkItem policies (ReadItem (ReadPolicy _ (PolicyRef name ss))) =
    [ policyNotFoundError policies name ss | not (policies `contains` name) ]
checkItem policies (UpdateItem (UpdatePolicy _ (PolicyRef name ss))) =
    [ policyNotFoundError policies name ss | not (policies `contains` name) ]
checkItem policies (InsertItem (PolicyRef name ss)) =
    [ policyNotFoundError policies name ss | not (policies `contains` name) ]
checkItem _ _ = []


contains :: PolicySet -> String -> Bool
contains policies = isJust . F.getOneWithMinScore 1.0 policies . T.pack

policyNotFoundError :: PolicySet -> String -> SourceSpan -> UserError
policyNotFoundError policies name = Error msg
  where
    suggestion = case nameSuggestions policies name of
        []  -> ""
        [s] -> printf ". Did you mean %s?" s
        s   -> printf ". Did you mean any of [%s]?" (join s ", ")
    msg = printf "Unknown policy %s%s" name suggestion

nameSuggestions :: PolicySet -> String -> [Text]
nameSuggestions policies name = map snd $ F.getWithMinScore 0.7 policies (T.pack name)
