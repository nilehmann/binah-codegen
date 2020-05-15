module Main where

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as T
import           System.Environment             ( getArgs )
import           System.IO
import           Text.Megaparsec                ( errorBundlePretty )

import           Binah.CodeGen.Parser
import           Binah.CodeGen.Render

main :: IO ()
main = do
  srcFile <- getSrcFile
  s       <- T.readFile srcFile
  case parse srcFile s of
    Left  e     -> putStrLn (errorBundlePretty e)
    Right binah -> T.putStrLn . render $ binah
    --Right binah -> print binah

getSrcFile :: IO String
getSrcFile = do
  args <- getArgs
  case args of
    [f] -> return f
    _   -> error "Please run with a single file as input"
