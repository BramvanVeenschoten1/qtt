module Normalization where

import Lexer(Span,Charray,showSpan)
import Parser hiding (Inductive)
import Data.Map
import Data.List(lookup,intercalate, elemIndex)
import Data.Maybe
import Data.Function
import Environment
import Multiplicity

occurs :: PSymbol -> Expr -> Bool
occurs v (ELambda _ _ v' _ b)
  | v /= binderPSymbol v' = occurs v b
occurs v (EPi _ _ (Just v') ta tb)
  | v /= binderPSymbol v' = occurs v ta || occurs v tb
  | otherwise = occurs v ta
occurs v (EPi _ _ _ ta tb) = occurs v ta || occurs v tb
occurs v (EApply _ f x) = occurs v f || occurs v x
occurs v (EVar _ v')
  | v == v' = True
occurs _ _ = False

normalize :: Redexes -> Expr -> Expr
normalize env (EVar s v) = case Data.Map.lookup v env of
  Nothing -> EVar s v
  Just x  -> normalize env x -- zeta/delta/alphabetsoup reduction
normalize env (EApply s f a) = let
  a' = normalize env a
  in case normalize env f of
    ELambda _ _ v _ b -> normalize env (subst (binderPSymbol v) a' b) -- beta reduction
    f' -> EApply s f' a'
normalize env (ELambda s m v t b) = let
  b' = normalize env b
  in case b' of
    EApply _ f a ->
      if occurs (binderPSymbol v) f
      then ELambda s m v t b'
      else f -- eta reduction
    b' -> ELambda s m v t b'
normalize env (EPi s m v ta tb) = EPi s m v (normalize env ta) (normalize env tb)
normalize env (ELet s v a ta b) = normalize env (subst v (normalize a) b)
normalize env x = x

subst :: PSymbol -> Expr -> Expr -> Expr
subst n e (ELambda s m v ta tb)
  | n == binderPSymbol v = ELambda s m v (subst n e <$> ta) tb
  | otherwise = ELambda s m v (subst n e <$> ta) (subst n e tb)
subst n e (EPi s m (Just v) ta tb)
  | n == binderPSymbol v = EPi s m (Just v) (subst n e ta) tb
  | otherwise =  EPi s m (Just v) (subst n e ta) (subst n e tb)
subst n e (EPi s m v ta tb) = EPi s m v (subst n e ta) (subst n e tb)
subst n e (EApply s f x) = EApply s (subst n e f) (subst n e x)
subst _ _ x = x

equiv :: Redexes -> Expr -> Expr -> Bool
equiv env x y = go (normalize env x) (normalize env y) where
  go (ELambda _ m v _ e) (ELambda _ m' v' _ e') = m == m' &&
    go e (subst (binderPSymbol v) (EVar Nothing (binderPSymbol v')) e')
  go (EPi _ m (Just v) ta tb) (EPi _ m' (Just v') ta' tb') = m == m' && go ta ta' &&
    go tb (subst (binderPSymbol v) (EVar Nothing (binderPSymbol v')) tb')
  go (EPi _ m Nothing ta tb) (EPi _ m' Nothing ta' tb') = m == m' && go ta ta' && go tb tb'
  go (EVar _ x)(EVar _ y) = x == y
  go (EConst _ x)(EConst _ y) = x == y
  go (EApply _ f x) (EApply _ f' x') = go f f' && go x x'
  go x y = False
