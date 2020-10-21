module Iterator where

import Core

import Data.List
import Data.Maybe
import Data.Map hiding (foldr)

{- based on the matita kernel -}
{- here we have utilities for iterating over core terms -}

nth :: Int -> [a] -> Maybe a
nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n-1) xs
nth _ _ = Nothing

{- get the largest number of parameters that are uniformly applied to all recursive occurences -}
{- may be useable for fixpoints as well? -}
getUniparamno :: Term -> Int -> Int
getUniparamno = f 0 where
  eatArgs n (Var m : args)
    | n == m = 1 + eatArgs (n - 1) args
  eatArgs _ _ = 0

  f k (App (Var m) args) acc
    | m >= k = min acc (eatArgs (k - 1) args)
  f k t a = Iterator.fold (const (+1)) k f t a
 
-- use fold
heightOf :: Term -> Int
heightOf t = case t of
  App f xs -> maximum (heightOf f : fmap heightOf xs)
  Lam _ _ _ b -> heightOf b
  Let _ _ a b -> max (heightOf a) (heightOf b)
  Case distinct -> let
    arms = fmap (heightOf . snd) (branches distinct)
    elim = heightOf (eliminee distinct)
    in maximum (elim : arms)
  Const _ (FixRef _ _ _ h _) -> h
  Const _ (DefRef _ h) -> h
  _ -> 0

heightOf' :: Term -> Int
heightOf' t = f () t 0 where
--  f :: () -> Term -> Int -> Int
  f _ (Const _ (FixRef _ _ _ h _)) = max h
  f _ (Const _ (DefRef _ h)) = max h
  f _ t = Iterator.fold (const id) () f t

typeofRef :: Objects -> Reference -> Term
typeofRef glob ref = case ref of
  IndRef i j _     -> indSort (getObject glob globalInd i !! j)
  FixRef i j _ _ _ -> fixType (getObject glob globalFix i !! j)
  ConRef i j k _   -> let (_,_,ty) = introRules (getObject glob globalInd i !! j) !! k in ty
  DefRef i _       -> fst (getObject glob globalDef i)
  DeclRef i        -> getObject glob globalDecl i
  where
    getObject obs f i = fromJust (Data.Map.lookup i (f obs))
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
  Case dat -> let
    in foldr (f ctx) (f ctx (motive dat) (f ctx (eliminee dat) acc)) (fmap snd (branches dat))
  _ -> acc

map :: (Hypothesis -> k -> k) -> k -> (k -> Term -> Term) -> Term -> Term
map push ctx f t = case t of
  App fun args -> App (f ctx fun) (fmap (f ctx) args)
  Pi  mult name src dst -> Pi mult name (f ctx src) (f (push (Hypothesis name src Nothing) ctx) dst)
  Lam mult name src dst -> Lam mult name (f ctx src) (f (push (Hypothesis name src Nothing) ctx) dst)
  Let name ty t body -> Let name (f ctx ty) (f ctx t) (f (push (Hypothesis name ty (Just t)) ctx) body)
  Case dat -> let
    {-mapArgs ctx [] = (ctx, [])
    mapArgs ctx ((mult,name,ty):args) = let
      ty' = f ctx ty
      (ctx',args') = mapArgs (push (Hypothesis name ty Nothing) ctx) args
      in (ctx', ((mult,name,ty') : args))

    mapBranch' branch = let
      
      (ctx',args') = mapArgs branch ctx (ctorArgs branch)
      
      rhs' = fmap (f ctx') (branchRhs branch)
      
      in undefined-}

    mapBranch (flag,rhs) = (flag, f ctx rhs)
    
    in Case (dat {
      eliminee = f ctx (eliminee dat),
      motive   = f ctx (motive dat),
      branches = fmap mapBranch (branches dat)})
  t -> t
