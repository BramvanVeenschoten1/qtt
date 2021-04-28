module Core where

import Data.Map

data Mult = Zero | One | Many deriving (Eq,Ord)

data Term
  = Box
  | Star
  | Var   Int
  | App   Term [Term]
  | Lam   Mult String Term Term
  | Pi    Mult String Term Term
  | Let   String Term Term Term -- type, bindee, body
  | Case  CaseDistinction
  | Const String Reference

{-
  the heigt of fixpoints and definitions indicate the length of chains of definitions
  they depend upon and is used as a heuristic for reduction
  
  uniparamno for fixpoints and inductive types is highest the number of the first parameters that are
  uniformly applied to *all recursive occurrences* in the bodies/constructors and are used for
  termination checking and positivity checking respectively
  
  recparamno for fixpoints indicates the argument that is supposed to decrease in each recursive call,
  used to ensure termination in reduction
  
  the paramno of an inductive type refers to the highest number of the first parameters that are uniformly applied
  in the *return types* of each constructor. This means the values of parameters are constant and can be inferred from the type of
  the inductive object, so they don't need to be considered in pattern matching, the motive need not abstract over them and
  they are not needed at runtime.
-}
data Reference
  = IndRef  Int Int Int         -- obj_id, defno, uniparamno
  | FixRef  Int Int Int Int Int -- obj_id, defno, recparamno, height, uniparamno
  | ConRef  Int Int Int Int     -- obj_id, defno, constructor nr, paramno
  | DefRef  Int Int             -- obj_id, height
  | DeclRef Int                 -- obj_id,
  deriving (Eq,Ord,Show)

data CaseDistinction = CaseDistinction {
  elimType :: Term, -- type of eliminee
  elimMult :: Mult, -- multiplicity of the eliminee
  eliminee :: Term, -- the inductive object being inspected
  motive   :: Term, -- return type of the expression, abstracted over the eliminee
  branches :: [(Bool,Term)]}

data Fixpoint = Fixpoint {
  fixType    :: Term,
  fixBody    :: Term,
  recParamno :: Int}

data Inductive = Inductive {
  isLarge    :: Bool, -- The Inductive type is large if it embeds Type. In this case, large elimination is not allowed.
  indSort    :: Term,
  paramno    :: Int, -- is computable from unroll Pi
  introRules :: [(String,Int,Term)]} -- [(name, paramno, ty)]
  
type Definition = (Term,Term) -- type, body

type Declaration = Term

data Objects = Objects {
  globalInd  :: Map Int [Inductive],
  globalFix  :: Map Int [Fixpoint],
  globalDef  :: Map Int Definition,
  globalDecl :: Map Int Declaration}

data Hypothesis = Hypothesis {
  hypName :: String,
  hypType :: Term,
  hypDef  :: Maybe Term}

type Context = [Hypothesis]

--fromJust' n = maybe (error (show n)) id
