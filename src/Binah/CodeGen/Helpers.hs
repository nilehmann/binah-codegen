{-# LANGUAGE FlexibleInstances #-}

module Binah.CodeGen.Helpers where

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

safeHead :: [a] -> Maybe a
safeHead []       = Nothing
safeHead (x : xs) = Just x

mapHead :: (a -> a) -> [a] -> [a]
mapHead f (x : xs) = f x : xs
mapHead _ []       = []

imap :: (Int -> a -> b) -> [a] -> [b]
imap f = zipWith f [0 ..]

interleave :: [a] -> [a] -> [a]
interleave (x : xs) ys = x : interleave ys xs
interleave []       ys = ys

join :: ToText a => [a] -> String -> Text
join = mapJoin id

mapJoin :: (ToText sep, ToText b) => (a -> b) -> [a] -> sep -> Text
mapJoin f xs sep = T.intercalate (toText sep) . map (toText . f) $ xs

class ToText a where
  toText :: a -> Text

instance ToText Text where
    toText t = t

instance ToText [Char] where
    toText = T.pack

concatMapM :: (Traversable t, Monad m) => (a -> m [b]) -> t a -> m [b]
concatMapM f t = concat <$> mapM f t
