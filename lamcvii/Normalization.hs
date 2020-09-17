module Normalization where

import Data.Map
import Data.List(lookup,intercalate, elemIndex,foldl)
import Data.Maybe
import Data.Function
import Core
import Multiplicity
import Substitution
import Iterator

{- here we evalutate terms and test their equality -}

data Config = Config Int [Config] Term [Config] -- env depth, env, term, stack

mkConf t = Config 0 [] t []
  
unwind :: Config -> Term
unwind (Config k e t s)
  | Prelude.null s = psubst (fmap unwind e) t
  | otherwise = App (psubst (fmap unwind e) t) (fmap unwind s)

{- applicative order reduction machine -}

unwind2 :: Int -> [Term] -> Term -> [Term] -> Term
unwind2 k e t s = App (psubst e t) s

reduce2 :: Globals -> Context -> Term -> Term
reduce2 glob ctx t = f 0 [] t [] where
  f :: Int -> [Term] -> Term -> [Term] -> Term
  f k e (t @ (Var n)) s
    | n < k = f 0 [] (e !! n) s
    | otherwise = case hypDef (ctx !! (n - k)) of
        Nothing -> unwind2 k e t s
        Just x -> f 0 [] (lift (n - k) x) s
  f k e (Lam _ _ _ t) (p : s) = f (k + 1) (p : e) t s
  f k e (Let _ _ m t) s = f (k + 1) (f k e m [] : e) t s
  f k e (App g xs) s = f k e g (fmap (\x -> f k e x []) xs ++ s)
  f k e (Const _ (DefRef i _)) s = let
    Just (_,body,_) = Data.Map.lookup i (globalDef glob)
    in f 0 [] body s
  f k e (t @ (Const _ (FixRef i j recparamno _))) s = case nth recparamno s of
    Just (Const _ (ConRef _ _ _ _)) -> f 0 [] (fixBody ((fromJust (Data.Map.lookup i (globalFix glob))) !! j)) s
    _ -> unwind2 k e t s
  f k e (t @ (Case (CaseDistinction _ _ eliminee _ branches))) s =
    case f k e eliminee [] of
      App (Const _ (ConRef _ _  i pno)) s' -> let
        s'' = Prelude.drop pno s'
        in f k e (branches !! i) (s'' ++ s)
      _ -> unwind2 k e t s
  f k e t s = unwind2 k e t s

{- end applicative machine -}

reduce :: Globals -> Context -> Config -> Config
reduce glob ctx (Config k e t s) = f k e t s where
  f :: Int -> [Config] -> Term -> [Config] -> Config
  f k e (t @ (Var n)) s
    | n < k = let Config k' e' t' s' = e !! n in f k' e' t' (s' ++ s)
    | otherwise = case hypDef (ctx !! (n - k)) of
      Nothing -> Config k e t s
      Just x -> f 0 [] (lift (n - k + 1) x) s
  f k e (Lam _ _ _ t) (p : s) = f (k + 1) (p : e) t s
  f k e (Let _ _ m t) s = f (k + 1) (f k e m [] : e) t s
  f k e (App g xs) s = f k e g (fmap (\x -> f k e x []) xs ++ s)
  f k e (Const _ (DefRef i _)) s =
    let Just (_,body,_) = Data.Map.lookup i (globalDef glob) in f 0 [] body s
  f k e (t @ (Const _ (FixRef i j recparamno _))) s = case nth recparamno s of
    Just (Config _ _ (Const _ (ConRef _ _ _ _)) _) -> f 0 [] (fixBody ((fromJust (Data.Map.lookup i (globalFix glob))) !! j)) s
    _ -> Config k e t s
  f k e (t @ (Case (CaseDistinction _ _ eliminee _ branches))) s =
    case f k e eliminee [] of
      Config _ _ (Const _ (ConRef _ _ i pno)) s' -> let
        s'' = Prelude.drop pno s'
        in f k e (branches !! i) (s'' ++ s)
      _ -> Config k e t s
  f k e t s = Config k e t s


whd :: Globals -> Context -> Term -> Term
whd glob ctx t = unwind (reduce glob ctx (mkConf t))

-- if flag = True, check equality, else, a `subtype of` b
sub :: Globals -> Context -> Bool -> Term -> Term -> Bool    
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
  
  whdm = reduce glob ctx
  
  machineEq flag t0 t1 = convertMachines flag (whdm (mkConf t0)) (whdm (mkConf t1))
  
  convertMachines flag (m0 @ (Config k0 e0 t0 s0)) (m1 @ (Config k1 e1 t1 s1)) =
    alpha_eq ctx flag (unwind (Config k0 e0 t0 [])) (unwind (Config k1 e1 t1 [])) &&
      and (zipWith (\t0 t1 -> convertMachines True (whdm t0) (whdm t1)) s0 s1)

