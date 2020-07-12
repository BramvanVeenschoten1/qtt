module Substitution where

import Iterator
import Core

liftFrom :: Int -> Int -> Term -> Term
liftFrom k n = f k where
  f k (Var i m)
    | m >= k = Var i (m + n)
  f k t = Iterator.map (const (+1)) k f t

lift :: Int -> Term -> Term
lift = liftFrom 1

psubst :: [Term] -> Term -> Term
psubst args = f 1 where
  nargs = length args
  
  f k (t @ (Var i n))
    | n >= k + nargs = if nargs == 0 then t else Var i (n - nargs)
    | n < k = t
    | otherwise = lift (k - 1) (args !! (n - k))
  f k (t @ (App i fun arg)) =
    let arg' = f k arg in
      case f k fun of
        Lam _ _ _ src body -> psubst [arg] body
        fun -> App i fun arg'

subst :: Term -> Term -> Term
subst = psubst . (:[])