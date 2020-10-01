module Prettyprint where

import Lexer(Loc)
import Parser(Binder(..))
import Core
import Elaborator
import Typechecker

import Data.Map
import Data.List

-- this is a bad joke now
instance Show Error where
  show x = case x of
    Msg msg -> msg
    NameAlreadyDefined qname loc -> showQName qname ++ " has already been defined here:\n" ++ show loc
    NoSuitableDefinition name loc -> show loc ++ "no definition for " ++ name ++ " is suitable."
    Ambiguity name loc qnames -> show loc ++ "Cannot infer suitable definition for " ++ name ++ ", candidates are: \n" ++ list_names qnames
    UnboundVar loc -> show loc ++ " unbound variable"
    
    Nonterminating loc -> show loc ++ " non terminating fixpoint"
    SynthLambda loc -> show loc ++ " cannot infer type of un-annotated lambda expression"
    SynthMatch loc -> show loc ++ " cannot infer type of match expression without motive"
    SynthParam loc -> show loc ++ " cannot infer type of an inductive parameter"
    
    ExpectedFunction loc _ -> show loc ++ "expected a function but got something else"
    InvalidSort _ -> "an invalid sort, somewhere"
    ExpectedInductive _ -> "expected an inductive type, somewhere"
    InvalidConstructor bind ref -> show (binderLoc bind) ++ binderName bind ++ " is not a constructor of " ++ "[PLACEHOLDER]"
    MissingCase loc ref -> show loc ++ " match does not cover all cases"
    ConstructorArity loc ref -> show loc ++ " mismath between given number of arguments and arity of constructor in match expression"
    InconvertibleTypes loc ctx t0 t1 ->
      show loc ++ "inconvertible types, expected:\n" ++ showTerm ctx t0 ++ "\n but got:\n" ++ showTerm ctx t1
    
    Unused loc -> show loc ++ "Linear variable is unused"
    RelevantUse loc -> show loc ++ "Erased variable is used in relevant context"
    MultipleUse loc -> show loc ++ "Linear variable is already used once"
    UnrestrictedUse loc -> show loc ++ "Linear variable is used in unrestricted context"
    IntersectUse loc -> show loc ++ "Linear variabel is not used consistently across branches"    
    
    x -> "not ok"


showGlobalNames :: Objects -> GlobalNames -> String
showGlobalNames obs = foldrWithKey (\key val acc -> "module " ++ key ++ "\n" ++ showNameSpace obs val ++ acc) ""

showNameSpace :: Objects -> NameSpace -> String
showNameSpace obs (_,qnames) = foldrWithKey  (\key (_,ref) acc -> "  " ++ showQName key ++ " : " ++ showTerm [] (typeofRef obs ref) ++ "\n" ++ acc) "" qnames

showTerm :: Context -> Term -> String
showTerm ctx x = case x of
  Box -> "?"
  Star -> "Type"
  Var n -> hypName (ctx !! n)
  
  App f xs ->
    ((case f of
      Lam _ _ _ _ -> embrace
      Case _ -> embrace
      Let _ _ _ _ -> embrace
      _ -> id) (showTerm ctx f)) ++ " " ++
    (intercalate " " (fmap (\x -> (case x of
      App _ _ -> embrace
      Lam _ _ _ _ -> embrace
      Pi _ _ _ _ -> embrace
      Case _ -> embrace
      Let _ _ _ _ -> embrace
      _ -> id) (showTerm ctx x)) xs))
  
  lam @ (Lam m s ta b) -> showLam 0 ctx lam
  Pi  m s ta tb -> "Pi " ++ show m ++ " " ++ s ++ " : " ++ showTerm ctx ta ++ ", " ++ showTerm (push s ctx) tb
  Let s ta a b -> "let " ++ s ++ " = " ++ showTerm ctx a ++ " in " ++ showTerm (push s ctx) b
  Const x _ -> x
  
  -- will have to do without constructor names for now
  Case distinct -> "match " ++ showTerm ctx (eliminee distinct) ++ " with" ++ showBranches ctx (branches distinct)
  where
    push s ctx = Hypothesis s undefined undefined : ctx
    
    showBranches ctx branches = concat (fmap (\branch -> " | " ++ 
      (case branch of Case _ -> embrace; _ -> id) (showTerm ctx branch)) branches)
    
    embrace x = "(" ++ x ++ ")"
    
    showArgs 0 _ = ""
    showArgs n (hyp:hyps) = showArgs (n - 1) hyps ++  "(" ++ hypName hyp ++ " : " ++ showTerm hyps (hypType hyp) ++ ")"
    
    showLam n ctx (Lam m s ta b) = showLam (n + 1) (Hypothesis s ta Nothing : ctx) b
    showLam n ctx b = "fun " ++ showArgs n ctx ++ " -> " ++ showTerm ctx b
    
showContext :: Context -> String
showContext [] = ""
showContext (hyp:ctx) = showContext ctx ++ "\n" ++ hypName hyp ++ " : " ++ showTerm ctx (hypType hyp)

list_names names = intercalate "\n" (fmap showQName names)

showQName :: [String] -> String
showQName = intercalate "."