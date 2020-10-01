
import Parser
import Declaration
import Core
import Elaborator
import Normalization
import Substitution
import ModuleSystem

import Data.Functor
import Data.Map
import System.Environment
import System.IO
import Data.ByteString.Builder
import Control.Monad

{-
CONSIDER:
While equations with inductive families are not easy, plain pattern matching on indexed types might be.
Existing literature on dependent pattern matching usually includes inductive families, so implementing
equations twice over may be an inefficient approach. So, consider implementing inductive familes before
equations.

CHANGES TO CORE:
  - re-evaluate whether rolled apps are worth the trouble (probably,maybe?)
  - unabstract case branches for default cases, keep names, mults, types, ctorname
  - add reachability annotations to branches in match expressions
  - consider necessity of type annotations in let, given that inference is still
    decidable if lambdas and matches are annotated and lets are not

  - consider the possibility of type annotations in const
    pros: no need for globs in typechecking
    cons: how do we ensure type-correctness of references with respect to global state?
          maybe just keep the globe around
  paramno changes:
  - add uni-paramno to FixRef for inlining
  - add uni-paramno to IndRef for inlining
  - keep paramno in ConRef    for reduction/checking
  - add paramno to inductive in globs
  - paramno and uniparamno are needed in glob only for core check

TODO:
  - improve termination error messages
  - default cases
  - inliner for positivity check
  - inliner for termination check
  - metavariables + level 1 implicit args
  - nested let-recs?
  - destructuring lets?
  - reachability analysis for erased match expressions, in increasing order of difficulty:
    - syntactic: empty case expressions are unreachable -> update core
    - type driven: terms of uninhabited types are unreachable
    - proof searching: terms in inconsistent contexts are unreachable
  - equations
  - implicit arguments -> consider how metavariables are inserted for implicit arguments.
    Options, in increasing order of expressiveness/difficulty:
      1 constants have a number indicating the first nth arguments are implicit.
        easy implement, covers most use cases
      2 constants have implicitness annotations,
        a slightly nontrivial implementation could lambda-abstract explicit args and give
        meta's to implicit args when a constant name is elaborated
      3 adding implict product types, lambda abstractions and applications a la agda/lean are the most powerful,
        and also the most intrusive. They will certainly require plicity annotations in the core, and allow
        the expression of a lot of terms than can never be implicitly instantiated
  - inductive families
  - equations with the above mentioned
      also considering refutation analysis
  - parametrized blocks?
    (parametrized blocks are only a syntactical convencience, as
    fixpoint and inductive inlining shouldn't rely on it.
    They don't have to, because checking uniformity of parameters is decidable)

consider idris-style universes vs the COC impredicative sort.
  pros:
    - no need for separate definitions of, for example, lists of types and lists of terms
      consider how much of a gain that is for mere programmers, not logicians
    - consistency with excluded middle
  cons:
    - more complicated
    - give up on impredicative encodings, consider how heavy a loss that really is given that
      impredicative encodings seem to be subsumed by indexed inductive types
    - one must choose between:
      1 fixing universe levels in core for simple trusted universe consistency verification,
        at the cost of having to elaborate a complete program before translating to core, or
        lifting definitions in core
      2 adding universe polymorphism to kernel
      3 adding universe constraint solving to kernel

on codegen:
1 lambda's are lifted to partially applied constants (hash-consed?)
2 all constants have a boxed and direct entry point
  direct entry deals with flattened, erased datastructures
  box entry points deal with unboxing of args and boxing of results
3 all constants are fully eta-expanded
  large eliminations make things quite difficult
we can distinguish the following cases:
  1 fully applied const => jump to entry
  2 partially applied const => make specialized pap
  3 fully applied arg => obtain index and closure, jump
  4 partially applied arg => make general pap

funny ideas:
  lift all lambdas
  monomorphize + deduplicate all calls to constants with closed terms as arguments
  do special reduction that shares subexpressions, like so:
    (\x -> b)e => let x = e in b
  for flat program extraction, reduction has to be more extreme:
    all calls to higher order functions with closures must be inlined, such that the 
    closure is no longer necessary. This is quite complicated


-}

{- here we do IO
get modules and verify, no output yet
-}

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do readFile name >>= \file -> pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files = case mapM (uncurry parse) files >>= checkModules of
    Left e -> putStrLn e
    Right mods -> putStrLn mods


