
import Parser
import Toplevel
import Core
import Elaborator
import Normalization
import Substitution
import Data.Functor
import Data.Map

import System.Environment
import System.IO
import Data.ByteString.Builder

{-

TODO:
  optimize substitution
  fold eatproducts in elab, typecheck
  reachability analysis for erased match expressions
  qualified names in parser
  module names
  a proper module system
  adjust elaborator to deal with parametrized definitions
  adjust parser for parametrized definitions

NEXT UP
  - small step normalization
  - case branch inference
  - default cases
  - inliner for positivity check
  - inliner for termination check
  - nested let-recs
  - equations
  - implicit arguments
  - inductive families
  - equations with the above mentioned
      also considering refutation analysis
  - parametrized blocks?
    (parametrized blocks are only a syntactical convencience, as
    fixpoint and inductive inlining shouldn't rely on it.
    They don't have to, because checking uniformity of parameters is decidable)
  - universes?
-}

{- here we do IO
get args, read input file, check
-}

main :: IO ()
main = getArgs >>= checkArg where
  checkArg [src] = parseFile src
  checkArg _     = putStrLn "supply input and output files"

  parseFile src =
    readFile src <&> parse src >>= checkAst
    
  checkAst (Left xs) = putStrLn xs
  checkAst (Right decls) = do
    putStrLn "parse ok"
    case checkProgram [decls] of
      Left err -> print err
      Right xs -> putStrLn "check ok"
      


