module Iterator where

import Core
import Data.List

{-
fold visits the term t accumulating in

acc the result of the applications of

f to subterms;

k is an input parameter for f and should be understood as the information required by f in order
to correctly process a subterm.
This information may (typically) change when passing binders, and in this case

g is in charge to update k
-}

fold :: (Hypothesis -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold g k f t acc = case t of
  App _ fun arg -> f k fun (f k arg acc)
  Pi  _ mult name src dst -> f k src (f (g (mult, name, src, Nothing) k) dst acc)
  Lam _ mult name src dst -> f k src (f (g (mult, name, src, Nothing) k) dst acc)
  Let _ mult name ty t body -> f k ty (f k t (f (g (mult, name, ty, Just t) k) body acc))
  Match _ _ ty t arms -> foldr (f k) (f k t (f k ty acc)) arms
  _ -> acc

{-
fold2 :: (Hypothesis -> k -> k) -> k -> (k -> a -> Term -> a) -> a -> Term -> a
fold2 g k f acc t = case t of
  App _ fun arg -> f k (f k acc fun) arg
  Pi  _ mult name src dst -> f (g (mult, name, src, Nothing) k) (f k acc src) dst
  Lam _ mult name src body -> f (g (mult, name, src, Nothing) k) (f k acc src) body
  Let _ mult name ty t body -> f (g (mult, name, ty, Just t) k) (f k (f k acc ty) t) body
  Match _ _ ty scrutinee arms -> foldl' (f k) (f k (f k acc ty) scrutinee) arms
  _ -> acc
-}

map :: (Hypothesis -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map g k f t = case t of
  App info fun arg -> App info (f k fun) (f k arg)
  Pi  info mult name src dst -> Pi info mult name (f k src) (f (g (mult, name, src, Nothing) k) dst)
  Lam info mult name src dst -> Lam info mult name (f k src) (f (g (mult, name, src, Nothing) k) dst)
  Let info mult name ty t body -> Let info mult name (f k ty) (f k t) (f (g (mult, name, ty, Just t) k) body)
  Match info ref ty scrutinee arms -> Match info ref (f k ty) (f k scrutinee) (fmap (f k) arms)