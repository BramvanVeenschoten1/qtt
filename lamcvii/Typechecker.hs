module Typechecker where

import Core
import Substitution
import Normalization
import Data.Map hiding (fold)
import Data.Maybe
import Prelude hiding (lookup)
import Iterator(fold)

{- here we do:
  operations on well-typed terms
-}

-- use fold
heightOf :: Term -> Int
heightOf t = case t of
  App f xs -> max (heightOf f) (maximum (fmap heightOf xs))
  Lam _ _ _ b -> heightOf b
  Let _ _ a b -> max (heightOf a) (heightOf b)
  Case distinct -> let
    arms = branches distinct
    h    = heightOf (eliminee distinct)
    in if Prelude.null arms
      then h
      else max h (maximum (fmap heightOf arms))
  Const _ (FixRef _ _ _ h) -> h
  Const _ (DefRef _ h) -> h
  _ -> 0

typeofRef :: Objects -> Reference -> Term
typeofRef glob ref = case ref of
  IndRef i j     -> indSort (getObject glob globalInd i !! j)
  FixRef i j _ _ -> fixType (getObject glob globalFix i !! j)
  ConRef i j k _ -> introRules (getObject glob globalInd i !! j) !! k
  DefRef i _     -> fst (getObject glob globalDef i)
  DeclRef i      -> getObject glob globalDecl i
  where
    getObject obs f i = fromJust (Data.Map.lookup i (f obs))

