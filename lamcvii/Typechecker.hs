module Typechecker where

import Core
import Substitution
import Normalization
import Data.Map
import Data.Maybe
import Prelude hiding (lookup)

{- here we do:
  operations on well-typed terms
-}

-- use fold
heightOf :: Term -> Int
heightOf t = case t of
  App f xs -> max (heightOf f) (maximum (fmap heightOf xs))
  Lam _ _ _ b -> heightOf b
  Let _ _ a b -> max (heightOf a) (heightOf b)
  Case distinct -> max (heightOf (eliminee distinct)) (maximum (fmap heightOf (branches distinct)))
  Const _ (FixRef _ _ _ h) -> h + 1
  Const _ (DefRef _ h) -> h + 1
  _ -> 0

typeofRef :: Globals -> Reference -> Term
typeofRef glob ref = case ref of
  IndRef i j     -> indSort (getObject glob globalInd i !! j)
  FixRef i j _ _ -> fixType (getObject glob globalFix i !! j)
  ConRef i j k _ -> introRules (getObject glob globalInd i !! j) !! k
  DefRef i _ -> let (ty,_,_) = getObject glob globalDef i in ty
  DeclRef i  -> getObject glob globalDecl i
  where
    getObject obs f i = fromJust (Data.Map.lookup i (f obs))

typeOf :: Globals -> Context -> Term -> Term
typeOf glob ctx Box = error "type of unmentionable box"
typeOf glob ctx Star = Box
typeOf glob ctx (Const _ ref) = typeofRef glob ref
typeOf glob ctx (Var n) = hypType (ctx !! n)
typeOf glob ctx (App f xs) = let
    eatProducts tf [] = tf
    eatProducts tf (x:xs) = let
      (Pi _ _ _ tf') = whd glob ctx tf
      in subst x tf'
    in eatProducts (typeOf glob ctx f) xs
    -- make fold
typeOf glob ctx (Pi m v ta tb) = let
  ka = typeOf glob ctx ta
  hyp = Hypothesis {
            hypType = ta,
            hypName = v,
            hypDef = Nothing}
  in typeOf glob (hyp : ctx) tb
typeOf glob ctx (Lam m v ta b) = let
  hyp = Hypothesis {
    hypType = ta,
    hypName = v,
    hypDef = Nothing}
  in typeOf glob (hyp : ctx) b
typeOf glob ctx (Let v ta a b) = let
  hyp = Hypothesis {
    hypType = ta,
    hypName = v,
    hypDef = Just a}
  in typeOf glob (hyp : ctx) b
typeOf glob ctx (Case dat) = App (motive dat) [eliminee dat]