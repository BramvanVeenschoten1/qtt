module Core where

import Data.Map

data Mult = Zero | One | Many deriving (Eq,Ord)

instance Show Mult where
  show Zero = "0"
  show One  = "1"
  show Many = "w"
  
-- In the spirit of structuralism, objects have no intrinsic names,
-- so this string in the Const constructor is just the qualified name
-- in that context

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

data Reference
  = IndRef  Int Int         -- name, defno
  | FixRef  Int Int Int Int -- name, defno, recparamno, height
  | ConRef  Int Int Int Int -- name, defno, constructor nr, paramno
  | DefRef  Int Int         -- name, height
  | DeclRef Int             -- name,
  deriving (Eq,Ord,Show)

data Branch = Branch {
  ctorName  :: String,
  isDefault :: Bool,
  ctorArgs  :: [(Mult,String,Term)],
  branchRhs :: Term}

data CaseDistinction = CaseDistinction {
  elimType :: (Int,Int),   -- type info of eliminee: obj_id, defno
  elimMult :: Mult,        -- multiplicity of the eliminee
  eliminee :: Term,        -- duh
  motive   :: Term,        -- return type of the expression, abstracted over the eliminee
  branches :: [Term]}      -- lambda abstracted branches are a thing now

data Fixpoint = Fixpoint {
  fixType    :: Term,
  fixBody    :: Term,
  recParamno :: Int}

data Inductive = Inductive {
  indSort    :: Term,
  introRules :: [Term]}
  
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
