module Main where

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as T
import           System.Environment             ( getArgs )
import           System.IO
import           Text.Megaparsec                ( errorBundlePretty )

import           Storm.CodeGen.Check
import           Storm.CodeGen.Parser
import           Storm.CodeGen.Render

main :: IO ()
main = do
  (srcFile, outFile) <- getFiles
  s                  <- T.readFile srcFile
  case parse srcFile s of
    Left  e     -> hPutStrLn stderr (errorBundlePretty e)
    Right storm -> 
      case checkStorm storm of
        []     -> do
          h <- getOutHandle outFile
          T.hPutStrLn h . render $ storm
          hClose h
        --[]     -> print storm
        errors -> hPutStrLn stderr (show errors)

getFiles :: IO (String, String)
getFiles = do
  args <- getArgs
  case args of
    [src]      -> return (src, "-")
    [src, out] -> return (src, out)
    _          -> error "Usage: storm-codegen src [out]"

getOutHandle :: String -> IO Handle
getOutHandle file = if file == "-" then return stdout else openFile file WriteMode
