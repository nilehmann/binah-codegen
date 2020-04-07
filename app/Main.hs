module Main where

import qualified Data.Text.IO                  as T
import           System.Environment             ( getArgs )
import           System.IO
import           Text.Megaparsec                ( errorBundlePretty )

import           Parser
import           Render

main :: IO ()
main = do
  srcFile <- getSrcFile
  s       <- readFile srcFile
  case parse srcFile s of
    Left  e     -> putStrLn (errorBundlePretty e)
    Right binah -> T.putStrLn . render $ binah

getSrcFile :: IO String
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"
