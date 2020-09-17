module Multiplicity where

import Core
import Lexer(Loc)
import Data.List

{- here we do basic operations related to multiplicities 
-}

data Use
  = Nouse
  | Oneuse Mult Loc
  | Adduse Use Use
  | CaseUse Loc [Use]

type Uses = [Use]

times :: Mult -> Mult -> Mult
times Zero _ = Zero
times _ Zero = Zero
times One x  = x
times x  One = x
times _  _   = Many

plus :: Mult -> Mult -> Mult
plus Zero x   = x
plus One Zero = One
plus _   _    = Many

useSum :: Use -> Mult
useSum Nouse = Zero
useSum (Oneuse x _) = x
useSum (Adduse x y) = plus (useSum x)(useSum y)
useSum (CaseUse _ xs) = f (fmap useSum xs) where
  f xs
    | all (== Zero) xs = Zero
    | all (== One) xs = One
    | otherwise = Many

noUses :: Uses
noUses = repeat Nouse

plusUses :: Uses -> Uses -> Uses
plusUses = zipWith Adduse

timesUses :: Mult -> Uses -> Uses
timesUses Zero = const noUses
timesUses One  = id
timesUses Many = fmap f where
  f Nouse = Nouse
  f (Oneuse m x) = Oneuse (timesMany m) x
  f (Adduse x y) = Adduse (f x) (f y)
  f (CaseUse info xs) = CaseUse info (fmap f xs)

  timesMany Zero = Zero
  timesMany _    = Many

branchUses :: Loc -> [Uses] -> Uses
branchUses info [] = noUses
branchUses info xs = fmap (CaseUse info) (transpose xs)