module Prettyprint where

import Lexer(Loc)
import Parser(Binder(..))
import Core
import Elaborator
import Utils

import Data.Map
import Data.List

instance Show Mult where
  show Zero = " 0"
  show One  = " 1"
  show Many = ""

showGlobalNames :: Objects -> GlobalNames -> String
showGlobalNames obs = foldrWithKey (\key val acc -> "module " ++ key ++ "\n" ++ showNameSpace obs val ++ acc) ""

showNameSpace :: Objects -> NameSpace -> String
showNameSpace obs (_,qnames) = foldrWithKey  (\key (_,ref) acc -> "  " ++ showQName key ++ " : " ++ showTerm [] (typeofRef obs ref) ++ "\n" ++ acc) "" qnames

showTerm :: Context -> Term -> String
showTerm ctx x = case x of
  Box -> "?"
  Star -> "Type"
  Var n -> maybe ("$" ++ show n) (\x -> if hypName x == "" then "$" ++ show n else hypName x) (nth n ctx) --(ctx !! n)
  
  App f xs ->
    ((case f of
      Lam _ _ _ _ -> embrace
      Case _ -> embrace
      Let _ _ _ _ -> embrace
      App _ _ -> error "nested apps"
      _ -> id) (showTerm ctx f)) ++ " " ++
    (intercalate " " (fmap (\x -> (case x of
      App _ _ -> embrace
      Lam _ _ _ _ -> embrace
      Pi _ _ _ _ -> embrace
      Case _ -> embrace
      Let _ _ _ _ -> embrace
      _ -> id) (showTerm ctx x)) xs))
  
  lam @ (Lam m s ta b) -> showLam 0 ctx lam
  Pi m "" ta tb -> f (showTerm ctx ta) ++ showArrow m ++ showTerm (push "" ta ctx) tb where
    f = case ta of
      Pi _ _ _ _ -> embrace
      _ -> id
  Pi m s ta tb -> "Pi" ++ show m ++ " " ++ s ++ " : " ++ f (showTerm ctx ta) ++ ", " ++ showTerm (push s ta ctx) tb where
    f = case ta of
      Pi _ _ _ _ -> embrace
      _ -> id
  Let s ta a b -> "let " ++ s ++ " = " ++ showTerm ctx a ++ " in " ++ showTerm (push s ta ctx) b
  Const x ref -> if Prelude.null x  then "(" ++ show ref ++ ")" else x
  
  -- will have to do without constructor names for now
  Case distinct -> "match " ++ showTerm ctx (eliminee distinct) ++ " with " ++
    concat (fmap (showBranch ctx . snd) (branches distinct))
  where
    push s t ctx = Hypothesis s t Nothing : ctx
    
    showArrow Zero = " => "
    showArrow One  = " -o "
    showArrow Many = " -> "
    
    showBranch ctx rhs = "| " ++ (case rhs of Case _ -> embrace; _ -> id) (showTerm ctx rhs)
    
    embrace x = "(" ++ x ++ ")"
    
    showArgs 0 _ = ""
    showArgs n (hyp:hyps) = showArgs (n - 1) hyps ++  "(" ++ hypName hyp ++ " : " ++ showTerm hyps (hypType hyp) ++ ")"
    
    showLam n ctx (Lam m s ta b) = showLam (n + 1) (Hypothesis s ta Nothing : ctx) b
    showLam n ctx b = "fun " ++ showArgs n ctx ++ " -> " ++ showTerm ctx b
    
showContext :: Context -> String
showContext [] = ""
showContext (hyp:ctx) = showContext ctx ++ "\n" ++ hypName hyp ++ " : " ++ showTerm ctx (hypType hyp) ++ f (hypDef hyp) where
  f Nothing = ""
  f (Just x) = " = " ++ showTerm ctx x

list_names names = intercalate "\n" (fmap showQName names)

showQName :: [String] -> String
showQName = intercalate "."