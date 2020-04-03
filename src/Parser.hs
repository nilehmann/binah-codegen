{-# LANGUAGE OverloadedStrings #-}

module Parser
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

import           Ast

type Parser = Parsec Void String

parse :: FilePath -> String -> Decls
parse f s = case runParser (decls <* eof) f s of
  Left  pErrs -> Decls []
  Right e     -> e


lineComment :: Parser ()
lineComment = L.skipLineComment "--"

scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment empty

-- TODO: We should exclude other reserved words here as well
reserved :: Parser String
reserved = L.symbol sc "assert"

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

arrow :: Parser () -> Parser String
arrow sc = L.symbol sc "->"

decls :: Parser Decls
decls = L.nonIndented scn $ Decls <$> many (predDecl <|> recDecl <|> policyDecl)

field :: Parser Field
field = do
  name   <- var sc
  ty     <- tycon sc
  policy <- optional (char '@' *> policyVar sc)
  return $ Field name ty policy

assert :: Parser Assert
assert = do
  symbol "assert"
  Assert <$> between (symbol "[") (symbol "]") tokens
 where
  symbol = L.symbol sc
  exclude c = isSpace c || c `elem` ['[', ']']
  tokens = some (satisfy $ not . exclude) `sepBy1` sc

recDecl :: Parser Decl
recDecl = L.indentBlock scn $ do
  name <- tycon sc
  return
    (L.IndentMany Nothing
                  (return . RecDecl . uncurry (Rec name) . partitionEithers)
                  (eitherP field assert)
    )

predDecl :: Parser Decl
predDecl = L.lineFold scn $ \sc' -> do
  let symbol = L.symbol sc'
  symbol "predicate"
  name <- var sc'
  symbol "::"
  argtys <- someTill (tycon sc' <* arrow sc') $ string "Bool"
  scn
  return . PredDecl $ Pred name argtys

policyDecl :: Parser Decl
policyDecl = L.lineFold scn $ \sc' -> do
  let symbol = L.symbol sc'
  symbol "policy"
  name <- policyVar sc'
  symbol "="
  symbol "\\"
  args <- someTill (var sc') $ arrow sc'
  body <- some (satisfy (not . isSpace)) `sepBy1` try sc'
  scn
  return . PolicyDecl $ Policy name args body
