module Core where

import Data.Map
import Parser(Info)
import Multiplicity

{-
Revise core:
  remove:
  - mutual inductive types
  - fixpoints (mutual or otherwise)
  replace with
  - non-mutual inductive types
  - eliminators (with quantifications, large eliminations)
  
complications with sorts and multiplicities necessitates
considering eliminators as a separate case

consider giving constructors a separate case in Term
pro : simplifiy elimination
con : distinguish partial application
      considering ctors as funs may be useful
      more cases = more complex
  
Inductive objects now have:
  - one sort
  - some introduction rules
  - one eliminator, with cases for each constructor

When typechecking:
  given parameters (?), motive and multiplicity (and selectors),
  the elimination rule provides an adequate type for each branch.

When reducing:
  given an elimination expression with a term in head-normal form (constructor),
  the computation rule must pick a branch and put the subdata/IH's in context with
  correct multiplicities

On Multiplicity selectors:
  When an eliminee may only be used once, an eliminating branch may not use one of its
  linear subdata and its corresponding inductive hypothesis both. To prevent this,
  for each elimination branch, the elimination rule must keep a pairing of linear subdata
  and their respective IH's and count them as one.

NEVERMIND:
- mutual/nested recursive types are non-trivial, so Fixpoint objects have preference
- multiplicity sensitive case distinction can be simplified
- recursive argument checking has to be done anyway

INSTEAD:
  types/function still not mutual
  fixpoint objects keep track to uniform parameters: params that are passed unmodified to
  recursive calls. This is allows monomorphisation, which is useful for:
    - termination checking higher-order calls
    - efficiency

ON MULTIPLICITY CHECKING
  implement top down multiplicity checking for better messages and straightforward case distinction checks
  note: application multiplies all free variables in its argument, not in local variables!
  so keep the expected multiplicity in the context, and multiply the context when entering applications
-}

data Term
  = Var   Info Int
  | Sort  Info Int
  | App   Info Term Term
  | Lam   Info Mult String Term Term
  | Pi    Info Mult String Term Term
  | Let   Info Mult String Term Term Term
  | Case  Info CaseDistinction
  | Const Info Reference

data Reference
  = IndRef  Int         -- name
  | FixRef  Int Int Int -- name, recparamno, height
  | ConRef  Int Int     -- name, constructor nr
  | DefRef  Int Int     -- name, height
  | DeclRef Int         -- name,

data CaseDistinction = CaseDistinction {
  elimType  :: Int,    -- name of inductive type
  elimMult  :: Mult,   -- multiplicity of the eliminee
  eliminee  :: Term,   -- duh
  motive    :: Term,   -- return type of the expression, quantified over the eliminee
  branches  :: [Term]} -- duh

data Fixpoint = Fixpoint {
  fixType    :: Term,
  fixBody    :: Term,
  recParamno :: Int,
  uniParamno :: Int,
  fixHeight  :: Int}

data Inductive = Inductive {
  indSort    :: Term,
  introRules :: [Term]}
  
type Definition = (Term,Term,Int) -- type, body, height

type Declaration = Term -- just the type

data Globals = Globals {
  globalInd  :: Map Int Inductive,
  globalFix  :: Map Int Fixpoint,
  globalDef  :: Map Int Definition,
  globalDecl :: Map Int Declaration}

data Hypothesis = Hypothesis {
  hypName :: String,
  hypMult :: Mult,
  hypType :: Term,
  hypDef  :: Maybe Term}

type Context = [Hypothesis]

data Error
  
