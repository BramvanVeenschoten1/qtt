module Inductive where

import Lexer(Span,Charray,showSpan)
import Parser hiding (Inductive)
import Data.Map
import Data.List(lookup,intercalate,elemIndex,nub)
import Data.Maybe
import Data.Function
import Environment
import Multiplicity
import Normalization
import Typecheck

type Family = Map PSymbol Expr
type Parent = PSymbol

constructorArity :: Ctor -> Int
constructorArity (_,ty) = arity ty where
  arity (EPi _ _ _ _ b) = 1 + arity b
  arity _ = 0

constructorFamily :: Ctor -> Expr
constructorFamily (_,ty) = family ty where
 family (EPi _ _ _ _ b) = family b
 family b = b

checkConstructor :: Env -> (PSymbol,Expr) -> Map Symbol Expr -> Ctor -> Either String ()
checkConstructor env parent fam (binder,expr) = let
  env' = foldrWithKey insertParameter env fam
  
  traverse (EPi s m v ta tb) = positive fam ta *> traverse tb
  traverse r = checkReturn r
  
  positive fam (EApply _ f a) = positive fam f *> free fam a
  positive fam (EPi _ _ _ ta tb) = positive fam tb *> free fam ta
  positive fam (ELambda _ _ _ _ b) = positive fam b
  positive fam (ELetRec s _ _) = err env (Just s) "let rec not allowed in constructor"
  positive fam (EMatch s _ _) = err env (Just s) "match not allowed in constructor"
  positive _ _ = pure ()
  
  free fam (EApply _ f a) = free fam f *> free fam a
  free fam (EPi _ _ (Just v) ta tb) = free fam ta *> free (delete v fam) tb
  free fam (EPi _ _ _ ta tb) = free fam ta *> free fam tb
  free fam (ELambda _ _ v _ b) = free (delete v fam) b
  free fam (EVar s v) = case lookup v fam of
    Nothing -> pure ()
    Just _ -> err env (Just s) "negative occurence of inductive type in constructor"
  free fam (ELetRec s _ _) = err env (Just s) "let rec not allowed in constructor"
  free fam (EMatch s _ _) = err env (Just s) "match not allowed in constructor"
  free _ _ = pure ()
  
  checkReturn (EVar s v)
    | v == binderPSymbol (fst parent) = pure ()
  checkReturn (EApply s f a) = checkReturn f
  checkReturn x = err env (Just (exprInfo x)) "return type of constructor must be parent type"
  
  in do
    infer env' expr
    traverse expr

checkDuplicates :: Env -> (Binder, Expr, [(Binder,Expr)]) -> Either String ()
checkDuplicates env (binder,_,ctors)
  | length names == length (nub names) = pure ()
  | otherwise = err env (binderSpan binder) "duplicate constructor definitions in inductive type"
  where names = (binderPSymbol . fst) <$> ctors

checkInductive :: Env -> Span -> [(Binder, Expr, [(Binder,Expr)])] -> Either String Env
checkInductive env span ind = do
  let (binders,sorts,ctors) = unzip3 ind
      spans = binderSpan <$> binders
      names = binderPSymbol <$> binders
  mconcat (check env (EConst Nothing Box) <$> sorts)
  mconcat (checkDuplicates env <$> ind)
  mconcat ((\(binder,_,ctors) -> (mconcat (checkConstructor env binder <$> ctors))) <$> ind)
  
  checkConstructor env families <$> zip names ctors
  undefined

checkPositive    = undefined

checkModule :: Env -> Module -> Either String ()
checkModule env EmptyModule = pure ()
checkModule env (IndDecl span ind rest) = do
  env' <- checkInductive env span ind
  checkModule env' rest

checkTerminating = undefined
checkMatch       = undefined
checkDecl        = undefined
checkRecDecl     = undefined