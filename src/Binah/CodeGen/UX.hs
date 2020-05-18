{-# LANGUAGE RecordWildCards #-}

module Binah.CodeGen.UX
    ( SourceSpan(..)
    , SourcePos(..)
    , UserError(..)
    , mkParseErrors
    , unPos
    )
where

import           Text.Megaparsec

data SourceSpan = SS
  { ssBegin :: !SourcePos
  , ssEnd   :: !SourcePos
  }
  deriving (Eq, Show)

data UserError = ParseError String SourceSpan

--------------------------------------------------------------------------------
-- | Errors
--------------------------------------------------------------------------------

mkParseErrors :: (Stream s, ShowErrorComponent e) => ParseErrorBundle s e -> [UserError]
mkParseErrors ParseErrorBundle {..} = let (r, _) = foldl g ([], bundlePosState) bundleErrors in r
  where
    g (xs, pst) e =
        let pst' = reachOffsetNoLine (errorOffset e) pst
            pos  = pstateSourcePos pst'
            s    = parseErrorTextPretty e
        in  (ParseError s (SS pos pos) : xs, pst')
