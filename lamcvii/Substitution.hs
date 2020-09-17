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
  f k (t @ (App fun args)) =
    let foo (Lam _ _ _ body) (arg:args) = foo (psubst [arg] body) args
        foo fun [] = fun
        foo fun args = App fun args
        
        bar args body = psubst args body
      
      in foo (f k fun) (fmap (f k) args)
      
  f k t = Iterator.map (const (+1)) k f t

subst :: Term -> Term -> Term
subst = psubst . (:[])