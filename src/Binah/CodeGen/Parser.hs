{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

module Binah.CodeGen.Parser
  ( parse
  )
where

import           Control.Monad                  ( void )
import           Data.Char
import           Data.Either
import           Data.Void
import           Text.Megaparsec         hiding ( parse )
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.List.NonEmpty            as NE

import           Binah.CodeGen.Ast
import           Binah.CodeGen.UX

type Parser = Parsec Void Text

parse :: FilePath -> Text -> Either (ParseErrorBundle Text Void) Binah
parse = runParser (binahP <* eof)

binahP :: Parser Binah
binahP =
  L.nonIndented scn (Binah <$> many (predDeclP <|> recDeclP <|> policyDeclP) <*> optional inlineP)

inlineP :: Parser String
inlineP = L.symbol scn "#inline" *> many (notFollowedBy eof *> satisfy (const True))

--------------------------------------------------------------------------------
-- | Predicate Decl
--------------------------------------------------------------------------------

predDeclP :: Parser Decl
predDeclP = L.lineFold scn $ \sc' -> do
  let symbol = L.symbol sc'
  symbol "predicate"
  name <- var sc'
  symbol "::"
  argtys <- someTill (tycon sc' <* arrow sc') $ string "Bool"
  scn
  return . PredDecl $ Pred name argtys

--------------------------------------------------------------------------------
-- | Policy Decl
--------------------------------------------------------------------------------

policyDeclP :: Parser Decl
policyDeclP = L.lineFold scn $ \sc' -> do
  let symbol = L.symbol sc'
  symbol "policy"
  name <- policyVar sc'
  symbol "="
  p <- policyP sc'
  scn
  return $ PolicyDecl name p

--------------------------------------------------------------------------------
-- | Record Decl
--------------------------------------------------------------------------------

recDeclP :: Parser Decl
recDeclP = L.indentBlock scn $ do
  name <- tycon sc
  return (L.IndentMany Nothing (return . RecDecl . Rec name) recItemP)

recItemP :: Parser RecItem
recItemP = L.lineFold scn $ \sc' ->
  fieldP sc' <|> assertP sc' <|> readPolicyP sc' <|> insertPolicyP sc' <|> updatePolicyP sc'

fieldP :: Parser () -> Parser RecItem
fieldP sc' = do
  name   <- var sc
  typ    <- tycon sc
  policy <- optional (policyAttrP sc')
  return . FieldItem $ Field name typ policy

updatePolicyP :: Parser () -> Parser RecItem
updatePolicyP sc' = UpdateItem . uncurry UpdatePolicy <$> policyForFieldsP sc' "update"

readPolicyP :: Parser () -> Parser RecItem
readPolicyP sc' = ReadItem . uncurry ReadPolicy <$> policyForFieldsP sc' "read"

insertPolicyP :: Parser () -> Parser RecItem
insertPolicyP sc' = L.symbol sc' "insert" >> (InsertItem <$> policyAttrP sc')

policyForFieldsP :: Parser () -> Text -> Parser ([String], PolicyAttr)
policyForFieldsP sc' action = do
  L.symbol sc' action
  fields <- fieldPatternP sc'
  policy <- policyAttrP sc'
  return (fields, policy)

assertP :: Parser () -> Parser RecItem
assertP sc' = do
  L.symbol sc' "assert"
  AssertItem . Assert <$> between (L.symbol sc' "[") (L.symbol sc "]") (reftP sc')

-- TODO: Implement wildcard
fieldPatternP :: Parser () -> Parser [String]
fieldPatternP sc' = between (symbol "[") (symbol "]") (var sc' `sepBy` symbol ",")
  where symbol = L.symbol sc'


--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

policyAttrP :: Parser () -> Parser PolicyAttr
policyAttrP sc' = policyRefP <|> inlinePolicyP sc'

policyRefP :: Parser PolicyAttr
policyRefP = do
  p1 <- getSourcePos
  char '@'
  name <- policyVar sc
  p2   <- getSourcePos
  return $ PolicyRef name (SS p1 p2)

inlinePolicyP :: Parser () -> Parser PolicyAttr
inlinePolicyP sc' = InlinePolicy <$> between (L.symbol sc' "{") (L.symbol sc "}") (policyP sc')

policyP :: Parser () -> Parser Policy
policyP sc' = do
  let symbol = L.symbol sc'
  symbol "\\"
  args <- someTill (var sc') $ arrow sc'
  body <- reftP (try sc' <|> sc)
  scn
  return $ Policy args body

--------------------------------------------------------------------------------
-- | Refinements
--------------------------------------------------------------------------------

-- We do a very basic parsing of refinements which is enough to insert entityVal
-- when needed.

ascSymbols :: String
ascSymbols = "!#$%&⋆+./<=>?@\\^|-~:"

op :: Parser () -> Parser String
op sc = L.lexeme sc $ some (oneOf ascSymbols <|> symbolChar)

reftP :: Parser () -> Parser Reft
reftP sc = uncurry ROps <$> reftApp sc `sepBy1_` op sc

reftApp :: Parser () -> Parser Reft
reftApp sc = RApp <$> some (reftConst sc <|> reftParen sc)

reftConst :: Parser () -> Parser Reft
reftConst sc' = RConst <$> some (satisfy p) <* sc'
  where p c = not (isSpace c || isSymbol c || c `elem` ascSymbols ++ "()][{}")

reftParen :: Parser () -> Parser Reft
reftParen sc = RParen <$> between (symbol "(") (symbol ")") (reftP sc) where symbol = L.symbol sc

--------------------------------------------------------------------------------
-- | Identifiers
--------------------------------------------------------------------------------

-- TODO: We should probably put other reserved words here as well
reserved :: Parser Text
reserved = "assert" <|> "deriving" <|> "insert" <|> "update" <|> "read"

largeid :: Parser String
largeid = (:) <$> upperChar <*> many (alphaNumChar <|> char '\'')

smallid :: Parser String
smallid = do
  notFollowedBy reserved
  (:) <$> (lowerChar <|> char '_') <*> many (alphaNumChar <|> oneOf ['\'', '_'])

tycon :: Parser () -> Parser String
tycon sc = L.lexeme sc largeid <?> "type constructor"

var :: Parser () -> Parser String
var sc = L.lexeme sc smallid <?> "variable"

policyVar :: Parser () -> Parser String
policyVar sc = L.lexeme sc largeid <?> "policy name"

--------------------------------------------------------------------------------
-- | Spaces
--------------------------------------------------------------------------------

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment empty

--------------------------------------------------------------------------------
-- | Misc
--------------------------------------------------------------------------------

arrow :: Parser () -> Parser Text
arrow sc = L.symbol sc "->"

sepBy1_ :: Parser a -> Parser sep -> Parser ([a], [sep])
sepBy1_ p sep = do
  x        <- p
  (ys, xs) <- unzip <$> many ((,) <$> sep <*> p)
  return (x : xs, ys)
