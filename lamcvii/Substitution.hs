module Substitution where

import Iterator
import Core

{- here be substitution and lifting -}

-- re-check for 0 based indices
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