
{-
check module:
  check inductive
    check well-formedness
    check strict positivity
  check decl
    check letrec
      check termination
    check match
      unify branches
  
  keep track of constructors: in type,
  
  matches must be: complete, simple

  matches replaces variables with constructors: (both type indices and scrutinees)
    keep redex map?

  compiled matches:
    keep structure or lambda-encode?
  
  bonus: do unification of holes
-}

module Typecheck where

import Lexer(Span,Charray,showSpan)
import Parser hiding (Inductive)
import Data.Map
import Data.List(lookup,intercalate, elemIndex)
import Data.Maybe
import Data.Function
import Environment
import Multiplicity
import Normalization

err :: Env -> Maybe Span -> String -> Either String a
err env Nothing msg = Left (filename env ++ ": " ++ msg)
err env (Just span) msg = Left (showSpan (filename env) (source env) span ++ msg)

checkMult :: Env -> Mult -> (Mult,[Span]) -> Maybe Span -> Either String ()
checkMult env m u s = check m (fst u) s (concat (showSpan (filename env)(source env) <$> snd u)) where
  check One  Zero s s' = err env s "Linear variable is unused"
  check One  Many s s' = err' s' "Attempting unrestricted use of linear variable"
  check Zero One  s s' = err' s' "Attempting use of erased variable"
  check Zero Many s s' = err' s' "Attempting use of erased variable"
  check _    _    _ _  = return ()
  
  err' span msg = Left (span ++ msg)

check :: Env -> Expr -> Expr -> Either String Uses
check env tb (ELet s (Binder {binderPSymbol = v}) ta a b) = do
  (ua,ta) <- (case ta of
    Nothing -> infer env a
    Just ta -> do
      infer env ta
      ua <- check env ta a
      pure (ua,ta))
  ub <- check (insertParam v ta (insertRedex v a env)) tb b
  let m = fst (getUse v ub)
  pure (ctxplus (delete v ub) (ctxtimes m ua))
check env tb (ELambda s m' (Binder {binderPSymbol = v, binderSpan = s'}) ta' b) = do
  (m, v', ta, tb) <- (case normalize (redexes env) tb of
    EPi _ m v' ta tb -> pure (m, v', ta, tb)
    tb -> err env s ("expected a term of type " ++ show tb ++ ", but got an abstraction"))
  
  if m == m'
  then pure ()
  else err env s ("expected abstraction with multiplicity " ++ show m ++ ", but got " ++ show m')

  case ta' of
    Nothing -> pure ()
    Just ta' ->
      if equiv (redexes env) ta ta'
      then pure ()
      else err env s ("expected type is " ++ show ta ++
                      " but but annotation is " ++ show ta')
  
  ub <- check (insertParam v ta env) (maybe tb (\v' -> subst (binderPSymbol v') (EVar Nothing v) tb) v') b
  checkMult env m (getUse v ub) s'
  pure (delete v ub)
check env tx (EMatch _ _ _) = error "checking match-expressions is not implemented"
check env tx (ELetRec _ _ _) = error "checking letrec-expressions is not implemented"
check env tx x = do
  (ux,tx') <- infer env x
  
  if equiv (redexes env) tx tx'
  then pure ux
  else err env (exprInfo x) ("expected a term of type:\n" ++ show tx ++ "\nbut got:\n" ++ show tx' ++ "\n")

infer :: Env -> Expr -> Either String (Uses,Expr) 
infer env (EConst _ Star) = pure (empty, EConst Nothing Box)
infer env (EVar s v) = case Data.Map.lookup v (parameters env) of--return (singleton v (One, [s]), fromJust (Data.Map.lookup v env), x)
  Just t -> pure (singleton v (One, catMaybes [s]),t) 
infer env (ELambda s _ _ Nothing _) = err env s "cannot infer type of un-annotated lambda expression"
infer env (EMatch s _ _) = err env s "cannot infer type of match-expression"
infer env (ELambda s m (Binder{binderSpan = s', binderPSymbol = v}) (Just ta) b) = do
  infer env ta
  (ub,tb) <- infer (insertParam v ta env) b
  
  checkMult env m (getUse v ub) s'
            
  let tf = EPi s m (Just (Binder s' v)) ta tb
  
  infer env ta

  pure (delete v ub, tf)
infer env (EPi s m v ta tb) = do
  (ua,ka) <- infer env ta
  (ub,kb) <- infer (maybe env (\v -> insertParam v ta env) (binderPSymbol <$> v)) tb
  
  let r  = pure (ctxplus ua ub, kb)
  
  case (ka,kb) of
    (EConst _ Star, EConst _ Star) -> r
    (EConst _ Box , EConst _ Star) -> r
    (EConst _ Star, EConst _ Box)  -> r
    (EConst _ Box , EConst _ Box)  -> r
    _ -> err env s ("\ninvalid types:\n" ++ show ta ++ " : " ++ show ka
                                    ++ "\n" ++ show tb ++ " : " ++ show kb)
                                 
infer env (EApply s f a) = do
  (uf,tf) <- infer env f

  let tf' = normalize (redexes env) tf
  (v, m, ta, tb) <- (case tf' of
    EPi _ m v ta tb -> pure (v, m, ta, tb)
    x -> err env s ("application expects function type, but got: " ++ show x))

  ua <- check env ta a
  
  let tb' = maybe tb (\v' -> subst (binderPSymbol v') a tb) v
  
  pure (ctxplus uf (ctxtimes m ua), tb')
infer env (ELet s (Binder{binderPSymbol = v}) ta a b) = do
  (ua,ta) <- case ta of
    Nothing -> infer env a
    Just ta -> do
      ua <- check env ta a
      pure (ua,ta)

  (ub,tb) <- infer (insertParam v ta env) b
  let uv = fst (getUse v ub)
  pure (ctxplus (delete v ub) (ctxtimes uv ua), tb)
infer env (ELetRec _ _ _) = error "inference of let-rec expressions is not yet implemented"
