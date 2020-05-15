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

import           Binah.CodeGen.Ast

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
recItemP = fieldP <|> assertP <|> readPolicyP <|> insertPolicyP <|> updatePolicyP

fieldP :: Parser RecItem
fieldP = do
  name   <- var sc
  typ    <- tycon sc
  policy <- optional policyAttrP
  return . FieldItem $ Field name typ policy

updatePolicyP :: Parser RecItem
updatePolicyP = UpdateItem . uncurry UpdatePolicy <$> policyForFieldsP "update"

readPolicyP :: Parser RecItem
readPolicyP = ReadItem . uncurry ReadPolicy <$> policyForFieldsP "read"

insertPolicyP :: Parser RecItem
insertPolicyP = L.symbol sc "insert" >> (InsertItem <$> policyAttrP)

policyForFieldsP :: Text -> Parser ([String], PolicyAttr)
policyForFieldsP action = do
  L.symbol sc action
  fields <- fieldPatternP
  policy <- policyAttrP
  return (fields, policy)

assertP :: Parser RecItem
assertP = do
  symbol "assert"
  AssertItem . Assert <$> between (symbol "[") (symbol "]") (reft scn)
  where symbol = L.symbol sc


-- TODO: Implement wildcard
fieldPatternP :: Parser [String]
fieldPatternP = fieldListP <|> pure <$> var sc

fieldListP :: Parser [String]
fieldListP = between (symbol "[") (symbol "]") (var scn `sepBy` symbol ",")
  where symbol = L.symbol scn

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------

policyAttrP :: Parser PolicyAttr
policyAttrP = policyRefP <|> inlinePolicyP

policyRefP :: Parser PolicyAttr
policyRefP = PolicyRef <$> (char '@' *> policyVar sc)

inlinePolicyP :: Parser PolicyAttr
inlinePolicyP = InlinePolicy <$> between (symbol "{") (symbol "}") (policyP scn)
  where symbol = L.symbol sc

policyP :: Parser () -> Parser Policy
policyP sc' = do
  let symbol = L.symbol sc'
  symbol "\\"
  args <- someTill (var sc') $ arrow sc'
  body <- reft (try sc' <|> sc)
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

reft :: Parser () -> Parser Reft
reft sc = uncurry ROps <$> reftApp sc `sepBy1_` op sc

reftApp :: Parser () -> Parser Reft
reftApp sc = RApp <$> some (reftConst sc <|> reftParen sc)

reftConst :: Parser () -> Parser Reft
reftConst sc' = RConst <$> some (satisfy p) <* sc'
  where p c = not (isSpace c || isSymbol c || c `elem` ascSymbols ++ "()][{}")

reftParen :: Parser () -> Parser Reft
reftParen sc = RParen <$> between (symbol "(") (symbol ")") (reft sc) where symbol = L.symbol sc

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
  (:) <$> lowerChar <*> many (alphaNumChar <|> char '\'')

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
