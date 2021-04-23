import Parser
import Declaration
import Core
import Elaborator
import Normalization
import Substitution
import Modulesystem

import Data.Functor
import Data.Map
import System.Environment
import System.IO
import Data.ByteString.Builder
import Control.Monad

{- here we do IO
get modules and verify, print signatures
-}

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do readFile name >>= \file -> pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files = case mapM (uncurry parse) files >>= checkModules of
    Left e -> putStrLn e
    Right mods -> putStrLn mods


