
import Parser
import Data.Functor

import System.Environment
import System.IO
import Data.ByteString.Builder

main :: IO ()
main = getArgs >>= baz where
  baz [src] = foo src
  baz _     = putStrLn "supply input and output files"

  foo src =
    readFile src <&> parse src >>= bar
    
  bar (Left xs) = putStrLn xs
  bar _         = putStrLn "ok"

{-
  checkArgs [src,dst] = readInput src dst
  checkArgs _         = putStrLn "supply input and output files"
  
  readInput src dst =
    readFile src <&> compile >>= writeOutput src dst

  compile input =
    parse input <&> addPrelude >>= inferExpr >>= transform <&> codegen

  writeOutput _ dst (Right code) = withFile dst WriteMode (flip hPutBuilder code)
  writeOutput src _ (Left err)   = putStrLn (src ++ err)
-}