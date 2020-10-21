module Substitution where

import Iterator
import Core
import Data.List

{- here be substitution and lifting -}

liftFrom :: Int -> Int -> Term -> Term
liftFrom k n = f k where
  f k (Var m)
    | m >= k = Var (m + n)
  f k t = Iterator.map (const (+1)) k f t

lift :: Int -> Term -> Term
lift = liftFrom 0

psubst :: [Term] -> Term -> Term
psubst args = f 0 where
  nargs = length args
  
  f k (t @ (Var n))
    | n >= k + nargs = Var (n - nargs) -- free
    | n < k = t -- local
    | otherwise = lift k (args !! (n - k)) -- in bounds
  f k (t @ (App fun args)) = g (f k fun) (fmap (f k) args)
  f k t = Iterator.map (const (+1)) k f t
  
  g (Lam _ _ _ body) (arg:args) = g (psubst [arg] body) args
  g fun [] = fun
  g (App f args) args' = App f (args ++ args')
  g fun args = App fun args

subst :: Term -> Term -> Term
subst = psubst . (:[])

instantiateCtor :: [Term] -> Term -> Term
instantiateCtor params t = psubst (reverse params) (dropDomains (length params) t) where
  dropDomains :: Int -> Term -> Term
  dropDomains 0 tb = tb
  dropDomains n (Pi _ _ _ tb) = dropDomains (n - 1) tb

{- substitute recursive occurrences of inductives or fixpoints for positiviy/termination analysis -}
substWithDummy :: Int -> Term -> Term
substWithDummy block_no = f () where
  f _ (Const _ (IndRef obj_id _ _))
    | obj_id == block_no = Box
  f _ (App (Const _ (IndRef obj_id _ upno)) args)
    |  obj_id == block_no = let
      right_args = Data.List.drop upno args
      in if Prelude.null right_args
         then Box
         else App Box right_args
  f _ (App (Const _ (FixRef obj_id _ _ _ upno)) args)
    | obj_id == block_no = let
    right_args = Data.List.drop upno args
    in if Prelude.null right_args
      then Box
      else App Box (fmap (f ()) right_args)
  f _ t = Iterator.map (const id) () f t