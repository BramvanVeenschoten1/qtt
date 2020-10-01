module Iterator where

import Core
import Data.List

{- based on the matita kernel -}
{- here we have utilities for iterating over core terms -}

nth :: Int -> [a] -> Maybe a
nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n-1) xs
nth _ _ = Nothing


{-
fold visits the term t accumulating in

acc the result of the applications of

f to subterms;

ctx is an input parameter for f and should be understood as the information required by f in order
to correctly process a subterm.
This information may (typically) change when passing binders, and in this case

g is in charge to update ctx
-}
fold :: (Hypothesis -> k -> k) -> k -> (k -> Term -> a -> a) -> Term -> a -> a
fold push ctx f t acc = case t of
  App fun args -> f ctx fun (foldr (f ctx) acc args)
  Pi  mult name src dst -> f ctx src (f (push (Hypothesis name src Nothing) ctx) dst acc)
  Lam mult name src dst -> f ctx src (f (push (Hypothesis name src Nothing) ctx) dst acc)
  Let name ty t body -> f ctx ty (f ctx t (f (push (Hypothesis name ty (Just t)) ctx) body acc))
  Case dat -> foldr (f ctx) (f ctx (motive dat) (f ctx (eliminee dat) acc)) (branches dat)
  _ -> acc

map :: (Hypothesis -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map push ctx f t = case t of
  App fun args -> App (f ctx fun) (fmap (f ctx) args)
  Pi  mult name src dst -> Pi mult name (f ctx src) (f (push (Hypothesis name src Nothing) ctx) dst)
  Lam mult name src dst -> Lam mult name (f ctx src) (f (push (Hypothesis name src Nothing) ctx) dst)
  Let name ty t body -> Let name (f ctx ty) (f ctx t) (f (push (Hypothesis name ty (Just t)) ctx) body)
  Case dat -> Case (dat {
      eliminee = f ctx (eliminee dat),
      motive   = f ctx (motive dat),
      branches = fmap (f ctx) (branches dat)})
  t -> t
