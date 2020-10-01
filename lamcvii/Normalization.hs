module Normalization where

import Data.Map
import Data.List(lookup,intercalate, elemIndex,foldl)
import Data.Maybe
import Data.Function
import Core
import Multiplicity
import Substitution
import Iterator
--import Prettyprint
import Debug.Trace

{- here we evalutate terms and test their equality -}


{- Alternative definitions for reduce, unwind -}
data Config = Config Int [Config] Term [Config] -- env depth, env, term, stack

mkConf t = Config 0 [] t []
  
unwind1 :: Config -> Term
unwind1 (Config k e t s)
  | Prelude.null s = psubst (fmap unwind1 e) t
  | otherwise = App (psubst (fmap unwind1 e) t) (fmap unwind1 s)

unwind2 :: Int -> [Term] -> Term -> [Term] -> Term
unwind2 k e t s
  | Prelude.null s = psubst e t
  | otherwise = App (psubst e t) s

reduce1 :: Objects -> Int -> Context -> Config -> (Config,Bool)
reduce1 glob delta ctx (Config k e t s) = f k e t s where
  f :: Int -> [Config] -> Term -> [Config] -> (Config,Bool)
  f k e (t @ (Var n)) s
    | n < k = let Config k' e' t' s' = e !! n in f k' e' t' (s' ++ s)
    | otherwise = case hypDef (ctx !! (n - k)) of
      Nothing -> (Config k e t s, True)
      Just x -> f 0 [] (lift (n - k + 1) x) s
  f k e (Lam _ _ _ t) (p : s) = f (k + 1) (p : e) t s
  f k e (Let _ _ m t) s = f (k + 1) (fst (f k e m []) : e) t s
  f k e (App g xs) s = f k e g (fmap (\x -> fst (f k e x [])) xs ++ s)
  f k e (t @ (Const _ (DefRef i height))) s
    | delta >= height = (Config k e t s, False)
    | otherwise = f 0 [] (snd (fromJust (Data.Map.lookup i (globalDef glob)))) s
  f k e (t @ (Const _ (FixRef i j recparamno height))) s = case fmap (fst . reduce1 glob 0 ctx) (nth recparamno s) of
    Just (Config _ _ (Const _ (ConRef _ _ _ _)) _) ->
      if delta >= height
      then (Config k e t s, False)
      else f 0 [] (fixBody ((fromJust (Data.Map.lookup i (globalFix glob))) !! j)) s
    _ -> (Config k e t s, True)
  f k e (t @ (Case (CaseDistinction _ _ eliminee _ branches))) s =
    case f k e eliminee [] of
      (Config _ _ (Const _ (ConRef _ _ i pno)) s',_) -> let
        s'' = Prelude.drop pno s'
        in f k e (branches !! i) (s'' ++ s)
      _ -> (Config k e t s, True)
  f k e t s = (Config k e t s, True)

unwind = unwind1
reduce = reduce1

whd :: Objects -> Context -> Term -> Term
whd glob ctx t = unwind (fst (reduce glob 0 ctx (mkConf t)))

-- if flag = True, check equality, else, a `subtype of` b
sub :: Objects -> Context -> Bool -> Term -> Term -> Bool    
sub glob ctx flag t0 t1 = alpha_eq ctx flag t0 t1 || machineEq flag t0 t1 where
  alpha_eq ctx flag t0 t1 = case (t0,t1) of
    (Box,Box) -> True
    (Star, Star) -> True
    (Var n0, Var n1) -> n0 == n1
    (Const _ ref,Const _ ref1) -> ref == ref1
    (App f0 xs0, App f1 xs1) -> sub glob ctx flag f0 f1 && and (zipWith (sub glob ctx flag) xs0 xs1)
    (Lam m n src t0, Lam _ _ _ t1) -> let
      hyp = Hypothesis {hypName = n, hypType = src, hypDef = Nothing}
      in sub glob (hyp : ctx) flag t0 t1
    (Pi m0 n0 ta0 tb0, Pi m1 _ ta1 tb1) -> let
      hyp = Hypothesis {hypName = n0, hypType = ta0, hypDef = Nothing}
      in (m0 == m1 || (not flag && m1 == Many)) &&
          sub glob ctx flag ta1 ta0 && sub glob (hyp : ctx) flag tb0 tb1 
    (Let n ty0 s0 t0, Let _ ty1 s1 t1) -> let
      hyp = Hypothesis {hypName = n, hypType = ty0, hypDef = Just s0}
      in sub glob ctx flag ty0 ty1 && sub glob ctx flag s0 s1 && sub glob (hyp : ctx) flag t0 t1
    (Case ref, Case ref1) ->
      elimType ref == elimType ref1 &&
      sub glob ctx flag (eliminee ref) (eliminee ref1) &&
      and (zipWith (sub glob ctx flag) (branches ref) (branches ref1))
    _ -> False
  
  heightOf (Const _ (DefRef _ h)) = h
  heightOf (Const _ (FixRef _ _ _ h)) = h
  heightOf (App (Const _ (DefRef _ h)) _) = h
  heightOf (App (Const _ (FixRef _ _ _ h)) _) = h
  heightOf _ = 0
  
  whdm = reduce glob maxBound ctx
  
  machineEq flag = on (convertMachines flag) (whdm . mkConf)
  
  smallDeltaStep :: Bool -> (Config,Bool) -> (Config,Bool) -> Bool
  smallDeltaStep flag (m0 @ ((Config _ _ t0 _), norm0)) (m1 @ ((Config _ _ t1 _), norm1)) = let
    h0 = heightOf t0
    h1 = heightOf t1
    
    delta
      | norm0     = h1 - 1
      | norm1     = h0 - 1
      | h0 == h1  = max 0 (h0 - 1)
      | otherwise = min h0 h1
      
    m0' = reduce glob delta ctx (fst m0)
    m1' = reduce glob delta ctx (fst m1)
    
    proceed
      | norm0     = convertMachines flag m0  m1'
      | norm1     = convertMachines flag m0' m1
      | otherwise = convertMachines flag m0' m1'
    in proceed
  
  convertMachines flag (m0 @ ((Config k0 e0 t0 s0),norm0)) (m1 @ ((Config k1 e1 t1 s1),norm1)) =
    (alpha_eq ctx flag (unwind (Config k0 e0 t0 [])) (unwind (Config k1 e1 t1 [])) &&
      and (zipWith (on (convertMachines True) whdm) s0 s1)) ||
        {-flip const (trace (
          showTerm ctx (unwind (fst m0)) ++ "\n" ++
          showTerm ctx (unwind (fst m1)) ++ "\n"))-}
            (not (norm0 && norm1) && smallDeltaStep flag m0 m1)

