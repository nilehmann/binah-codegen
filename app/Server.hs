{-# LANGUAGE LambdaCase          #-}

module Server where

import           System.Exit

import           Storm.CodeGen.Lsp 

main :: IO ()
main = do
    run (return ()) >>= \case
        0 -> exitSuccess
        c -> exitWith . ExitFailure $ c

