module Binah.CodeGen.Helpers where

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
