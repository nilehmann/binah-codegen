module Main where

import           Data.Text
import           System.Environment             ( getArgs )
import           System.IO

import           Parser
import           Render

main :: IO ()
main = do
  srcFile <- getSrcFile
  s       <- readFile srcFile
  putStrLn . unpack . render $ parse srcFile s

getSrcFile :: IO String
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"
