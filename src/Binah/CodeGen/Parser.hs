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
parse = runParser (binah <* eof)

binah :: Parser Binah
binah =
  L.nonIndented scn (Binah <$> many (predDecl <|> recDecl <|> policyDecl) <*> optional inline)

inline :: Parser String
inline = L.symbol scn "#inline" *> many (notFollowedBy eof *> satisfy (const True))

recDecl :: Parser Decl
recDecl = L.indentBlock scn $ do
  name <- tycon sc
  return
    (L.IndentSome Nothing
                  (return . RecDecl . uncurry (Rec name) . partitionEithers)
                  (eitherP field assert)
    )

field :: Parser Field
field = do
  name   <- var sc
  ty     <- tycon sc
  policy <- optional (char '@' *> policyVar sc)
  return $ Field name ty policy

assert :: Parser Assert
assert = do
  symbol "assert"
  Assert <$> between (symbol "[") (symbol "]") (reft sc)
  where symbol = L.symbol sc


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
  body <- reft (try sc' <|> sc)
  scn
  return . PolicyDecl $ Policy name args body

--------------------------------------------------------------------------------
-- | Refinements
--------------------------------------------------------------------------------

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
  where p c = not (isSpace c || isSymbol c || c `elem` ascSymbols ++ "()][")

reftParen :: Parser () -> Parser Reft
reftParen sc = RParen <$> between (symbol "(") (symbol ")") (reft sc) where symbol = L.symbol sc

--------------------------------------------------------------------------------
-- | Identifiers
--------------------------------------------------------------------------------

-- TODO: We should put other reserved words here as well
reserved :: Parser Text
reserved = string "assert" <|> string "deriving"

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
