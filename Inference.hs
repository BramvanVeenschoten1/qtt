module Inference where

import Lexer(Span)
import Parser
import Generator
import Data.Map
import Data.Maybe
import Data.Either
import Data.List(lookup, intercalate)

type Uses = Map Var (Mult,[Span])
type Env  = Map Var Expr

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

intersect :: Mult -> Mult -> Mult
intersect Zero Zero = Zero
intersect One  One  = One
intersect _    _    = Many

ctxtimes :: Mult -> Uses -> Uses
ctxtimes m = fmap f where
  f (m', s) = (times m m', s)

ctxplus :: Uses -> Uses -> Uses
ctxplus = unionWith f where
  f (m,s) (m',s') = (plus m m', s ++ s')

ctxinter :: Uses -> Uses -> Uses
ctxinter xs ys = Prelude.foldr f ys (toList xs) where
  f (v,(m,s)) = case Data.Map.lookup v ys of
    Nothing -> insert v (intersect m Zero, s)
    Just (m',s') -> insert v (intersect m m', s ++ s')

getUse :: Var -> Uses -> (Mult,[Span])
getUse v = maybe (Zero,[]) id . Data.Map.lookup v

showEnv :: Env -> String
showEnv = intercalate "\n" . fmap f . toList where
  f (x,y) = show x ++ " : " ++ show y

indexExpr :: Expr -> Gen Expr
indexExpr = index empty where
  index env (c @ (EConst _ _)) = return c
  index env (EVar (Var s v _) _) = case Data.Map.lookup v env of
      Nothing    -> err (show s ++ "unbound variable: " ++ v)
      Just (n,x) -> return (EVar (Var s v n) x)
  index env (EApp s l r) = EApp s <$> index env l <*> index env r
  index env (ELam s m (Var s' v _) ta b) = do
    n <- get
    ELam s m (Var s' v n) <$> f env ta <*> index (insert v (n,Nothing) env) b
  index env (EPi s m (Just (Var s' v _)) ta tb) = do
    n <- get
    EPi s m (Just (Var s' v n)) <$> index env ta <*> index (insert v (n,Nothing) env) tb
  index env (EPi s m Nothing ta tb) = EPi s m Nothing <$> index env ta <*> index env tb
  index env (ELet s (Var s' v _) ta a b) = do
    n  <- get
    ta <- f env ta
    a  <- index env a
    ELet s (Var s' v n) ta a <$> index (insert v (n,Just a) env) b
  index env (ESig s m Nothing ta tb) = ESig s m Nothing <$> index env ta <*> index env tb
  index env (ESig s m (Just (Var s' v _)) ta tb) = do
    n <- get
    ESig s m (Just (Var s' v n)) <$> index env ta <*> index (insert v (n,Nothing) env) tb
  index env (ElimB s c a b) = ElimB s <$> index env c <*> index env a <*> index env b
  index env (EPair s a b) = EPair s <$> index env a <*> index env b
  index env (ElimU s a b) = ElimU s <$> index env a <*> index env b
  index env (ElimP s (Var s' v _) (Var s'' v' _) a b) = do
    n  <- get
    n' <- get
    a  <- index env a
    b  <- index (insert v (n,Nothing) (insert v' (n', Nothing) env)) b
    return (ElimP s (Var s' v n) (Var s'' v' n') a b)    
  
  f env = maybe (return Nothing) (fmap Just . index env)

subst :: Var -> Expr -> Expr -> Expr
subst v e (lam @ (ELam s m v' ta b)) -- = ELam s m v' (subst v e <$> ta) (subst v e b)
  | v == v'   = lam
  | otherwise = ELam s m v' (subst v e <$> ta) (subst v e b)
subst v e (pi @ (EPi  s m v' ta tb))
  | (Just v) == v' = pi
  | otherwise      = EPi  s m v' (subst v e ta) (subst v e tb)
subst v e (sig @ (ESig s m v' ta tb))
  | (Just v) == v' = sig
  | otherwise      = ESig s m v' (subst v e ta) (subst v e tb)
subst v e (EApp s f a)         = EApp s      (subst v e f)      (subst v e a)
subst v e (ELet s v' ta a b)   = ELet s   v' (subst v e <$> ta) (subst v e a) (subst v e b)
subst v e (ElimB s c a b)      = ElimB s (subst v e c) (subst v e a) (subst v e b)
subst v e (ElimP s v' v'' a b) = ElimP s v' v'' (subst v e a) (subst v e b)
subst v e (EPair s a b)        = EPair s (subst v e a) (subst v e b)
subst v e (ElimU s a b)        = ElimU s (subst v e a) (subst v e b)
subst v e (EVar v' _)
  | v == v'  = e
subst _ _ x = x

occurs :: Var -> Expr -> Bool
occurs v (ELam _ _ _ (Just ta) b) = occurs v ta || occurs v b
occurs v (ELam _ _ _ Nothing   b) =                occurs v b
occurs v (EPi  _ _ _       ta tb) = occurs v ta || occurs v tb
occurs v (ELet _ _ (Just ta) a b) = occurs v ta || occurs v a  || occurs v b
occurs v (ELet _ _ Nothing   a b) =                occurs v a  || occurs v b
occurs v (EApp _             f a) = occurs v f  || occurs v a
occurs v (ElimB _ c a b)          = occurs v c  || occurs v a  || occurs v b
occurs v (ElimP _ _ _ a b)        = occurs v a  || occurs v b
occurs v (EPair _ a b)            = occurs v a  || occurs v b
occurs v (ElimU _ a b)            = occurs v a  || occurs v b
occurs v (EVar v' _)              = v == v'
occurs _ _  = False

normalize :: Expr -> Expr
normalize (ELam s m v ta b)  = ELam s m v ta (normalize b)
normalize (EPi  s m v ta tb) = EPi s m v (normalize ta) (normalize tb)
normalize (EApp s f a) = case normalize f of
  ELam _ _ v _ b -> normalize (subst v (normalize a)  b)
  f'         -> EApp s f' (normalize a)
normalize (EPair s a b) = EPair s (normalize a) (normalize b)
normalize (ElimP s v v' a b) = let
  na = normalize a
  in case na of
    EPair _ a' b' -> normalize (subst v a' (subst v' b' b))
    _ -> ElimP s v v' na (normalize b)
normalize (ElimB s c a b) = let
  nc = normalize c
  na = normalize a
  nb = normalize b
  in case nc of
    EConst _ TT -> na
    EConst _ FF -> nb
    _ -> ElimB s nc na nb
normalize (ElimU _ _ b) = normalize b
normalize (ELet _ v _ a b)  = normalize (subst v (normalize a) b)
normalize (EVar _ (Just x)) = normalize x
normalize c = c

equiv :: Expr -> Expr -> Bool
equiv = eq where
  eq (ELam _ m v (Just ta) b)  (ELam _ m' v' (Just ta') b')  = eq ta ta' && eq  b (subst v' (EVar v Nothing) b') && m == m'
  eq (ELam _ m v Nothing b)    (ELam _ m' v' Nothing b')     = eq  b (subst v' (EVar v Nothing) b') && m == m'
  eq (EPi  _ m (Just v) ta tb) (EPi  _ m' (Just v') ta' tb') = eq ta ta' && eq tb (subst v' (EVar v Nothing) tb') && m == m'
  eq (EPi  _ m Nothing ta tb)  (EPi  _ m' Nothing ta' tb')   = eq ta ta' && eq tb tb' && m == m'
  eq (EApp _ f a)              (EApp _ f' a')                = eq f  f'  && eq  a  a'
  eq (EPair _ a b)             (EPair _ a' b')               = eq a  a'  && eq  b  b'
  eq (ElimP _ v v' a b)        (ElimP _ v'' v''' a' b')      = eq a  a'  && eq b (subst v'' (EVar v Nothing) (subst v''' (EVar v' Nothing) b'))
  eq (ElimU _ a b)             (ElimU _ a' b')               = eq a  a'  && eq b b'
  eq (ElimB _ c a b)           (ElimB _ c' a' b')            = eq c  c'  && eq a a' && eq b b'
  eq (ESig _ m Nothing ta tb)  (ESig _ m' Nothing ta' tb')   = eq ta ta' && eq tb tb' && m == m'
  eq (ESig _ m (Just v) ta tb) (ESig _ m' (Just v') ta' tb') = eq ta ta' && eq tb (subst v' (EVar v Nothing) tb') && m == m'
  eq (EConst _ c)              (EConst _ c')                 = c == c'
  eq (EVar v _)                (EVar v' _)                   = v == v'
  eq x                          y                            = False -- error ("\n" ++ show x ++ "\n" ++ show y)

checkMult :: Mult -> (Mult,[Span]) -> Span -> Either String ()
checkMult m u s = check m (fst u) (show s) (concat (show <$> snd u)) where
  check One  Zero s s' = Left (s  ++ "Linear variable is unused")
  check One  Many s s' = Left (s' ++ "Attempting unrestricted use of linear variable")
  check Zero One  s s' = Left (s' ++ "Attempting use of erased variable")
  check Zero Many s s' = Left (s' ++ "Attempting use of erased variable")
  check _    _    _ _  = return ()

inferConstant :: Constant -> Either String (Uses,Expr)
inferConstant c = return (empty, EConst emptySpan c') where
  c' = case c of
    Star    -> Box
    IntType -> Star
    Num x   -> IntType
    TT      -> Bool
    FF      -> Bool
    Bool    -> Star
    Unit    -> TUnit
    TUnit   -> Star

check :: Env -> Expr -> Expr -> Either String (Uses,Expr)
check env tb (ELet s v ta a b) = do
  (ua,ta,ra) <- (case ta of
    Nothing -> infer env a
    Just ta -> do
      infer env ta
      (ua,ra) <- check env ta a
      return (ua,ta,ra))

  (ub,rb) <- check (insert v ta env) tb b
  let m = fst (getUse v ub) 
      r = case m of
            Zero -> rb
            One  -> subst v ra rb
            _    -> ELet s v Nothing ra rb
  return (ctxplus (delete v ub) (ctxtimes m ua), r)
check env tb (ELam s m' (v @ (Var s' _ _)) ta' b) = do
  (m, v', ta, tb) <- (case normalize tb of
    EPi _ m v' ta tb -> return (m, v', ta, tb)
    tb -> Left (show s ++ "expected a term of type " ++ show tb ++ ", but got an abstraction"))

  if m == m' || m' == Many
  then return ()
  else Left (show s ++ "expected abstraction with multiplicity " ++ show m ++ ", but got " ++ show m')

  case ta' of
    Nothing  -> return ()
    Just ta' ->
      let nta  = normalize ta
          nta' = normalize ta'
        in
          if equiv nta nta'
          then return ()
          else Left (show s' ++
            "expected type is " ++ show nta ++
            " but but annotation is " ++ show nta')
  
  (ub,rb) <- check (insert v ta env) (maybe tb (\v' -> subst v' (EVar v Nothing) tb) v') b
  checkMult m (getUse v ub) s'
  let r = case m of
            Zero -> rb
            _    -> ELam s m v Nothing rb
  return (delete v ub, r)
check env tx (EPair s a b) = do
  (s', m, v, ta, tb) <- (case normalize tx of
    ESig s m v ta tb -> return (s,m,v,ta,tb)
    x -> Left (show s ++ "Expected some dependent pair, but got: " ++ show x))
  
  (ua,ra) <- check env ta a
  (ub,rb) <- check env (maybe tb (\v -> subst v a tb) v) b
  let r = if m == Zero then rb else EPair s ra rb
  return (ctxplus (ctxtimes m ua) ub, r)
check env tx (ElimB s c a b) = do
  (uc,rc) <- check env (EConst emptySpan Bool) c
  (ua,ra) <- check env tx a
  (ub,rb) <- check env tx b
  return (ctxplus uc (ctxinter ua ub), ElimB s rc ra rb)
check env tx (ElimU s a b) = do
  (ua,_)  <- check env (EConst emptySpan TUnit) a
  (ub,rb) <- check env tx b
  return (ctxplus ua ub, rb)
check env tx (ElimP s v v' a b) = do
  (ua,ta,ra) <- infer env a
  
  (s', m, v'', ta, tb) <- (case normalize ta of
    ESig s' m v'' ta tb -> return (s', m, v'', ta, tb)
    x -> Left (show s ++ "expected a dependent pair, but got: " ++ show x))
  
  let tb' = (case v'' of
              Nothing -> tb
              Just v'' -> subst v'' (EVar v Nothing) tb)
      env' = insert v ta (insert v' tb' env)
  
  (ub,rb) <- check env' tx b
  let (uv ,_) = getUse v  ub
      (uv',_) = getUse v' ub
      ua' = if times m uv' == uv
            then ctxtimes uv' ua
            else ctxtimes Many ua
      r = (case (uv',m) of
            (Zero,_) -> rb
            (_,Zero) -> ELet s v' Nothing ra rb
            _        -> ElimP s v v' ra rb)
  
  return (ctxplus ua' ub, r)
check env tx x = do  
  (ux, tx', rx) <- infer env x
  
  let ntx  = normalize tx
      ntx' = normalize tx'
  if equiv ntx ntx'
  then return (ux,rx)
  else Left (show (spanof x) ++ "expected a term of type:\n" ++ show ntx ++ "\nbut got:\n" ++ show ntx' ++ "\n") 
  where
    spanof (ELam s _ _ _ _) = s
    spanof (EPi s _ _ _ _) = s
    spanof (EApp s _ _) = s
    spanof (ELet s _ _ _ _) = s
    spanof (EConst s _) = s
    spanof (EVar (Var s _ _) _) = s
    spanof (ESig s _ _ _ _) = s

infer :: Env -> Expr -> Either String (Uses,Expr,Expr) 
infer env (x @ (EConst _ c)) = do
  (uk, tk) <- inferConstant c
  return (uk, tk, x)
infer env (x @ (EVar (v @ (Var s _ _)) _)) = case Data.Map.lookup v env of--return (singleton v (One, [s]), fromJust (Data.Map.lookup v env), x)
  Just t -> return (singleton v (One,[s]),t, x)
  Nothing -> Left(show s ++ show v ++ "\n\n" ++ showEnv env)
infer env (ELam s _ _ Nothing _) = Left (show s ++ "cannot infer type of un-annotated lambda expression")
infer env (EPair s a b) = Left (show s ++ "cannot infer type of pair")
infer env (ELam s m (v @ (Var s' _ n)) (Just ta) b) = do
  infer env ta
  (ub,tb,rb) <- infer (insert v ta env) b
  
  checkMult m (getUse v ub) s'
  
  let tf = EPi s m (if occurs v tb then Just v else Nothing) ta tb
      r = case m of
            Zero -> rb
            _    -> ELam s m v Nothing rb
            
  infer env tf

  return (delete v ub, tf, r)
infer env (EPi s m v ta tb) = do
  (_,ka,ra) <- infer env ta
  (_,kb,rb) <- infer (maybe env (\v -> insert v ta env) v) tb
  
  let r  = return (empty, kb, EPi s m v ra rb)
  
  case (ka,kb) of
    (EConst _ Star, EConst _ Star) -> r
    (EConst _ Box , EConst _ Star) -> r
    (EConst _ Star, EConst _ Box)  -> r
    (EConst _ Box , EConst _ Box)  -> r
    _ -> Left (show s ++ "\ninvalid types:\n" ++ show ta ++ " : " ++ show ka
                                    ++ "\n" ++ show tb ++ " : " ++ show kb)
infer env (EApp s f a) = do
  (uf,tf,rf) <- infer env f

  let tf' = normalize tf
  (v, m, ta, tb) <- (case tf' of
    EPi _ m v ta tb -> return (v, m, ta, tb)
    x -> Left (show s ++ "application expects function type, but got: " ++ show x))

  (ua,ra) <- check env ta a
  
  let r = case m of
            Zero -> rf
            _    -> EApp s rf ra 
  return (ctxplus uf (ctxtimes m ua), maybe tb (\v -> subst v a tb) v, r)
infer env (ELet s v ta a b) = do
  (ua,ta,ra) <- case ta of
    Nothing -> infer env a
    Just ta -> do
      (ua,ra) <- check env ta a
      return (ua,ta,ra)

  (ub,tb,rb) <- infer (insert v ta env) b
  let uv = fst (getUse v ub)
      r = case uv of
            Zero -> rb
            One  -> subst v ra rb
            _    -> ELet s v Nothing ra rb
  return (ctxplus (delete v ub) (ctxtimes uv ua), tb, r)
infer env (ESig s m v ta tb) = do
  (_,ka,ra) <- infer env ta
  (_,kb,rb) <- infer (maybe env (\v -> insert v ta env) v) tb
  
  let r = return (empty, kb, ESig s m v ra rb)
  
  case (ka,kb) of
    (EConst _ Star, EConst _ Star) -> r
    (EConst _ Box , EConst _ Star) -> r
    (EConst _ Star, EConst _ Box)  -> r
    (EConst _ Box , EConst _ Box)  -> r
    _ -> Left (show s ++ "\ninvalid types:\n" ++ show ta ++ " : " ++ show ka
                                    ++ "\n" ++ show tb ++ " : " ++ show kb)
infer env (ElimP s v v' a b) = do
  (ua,ta,ra) <- infer env a
  
  (s', m, v'', ta, tb) <- (case normalize ta of
    ESig s' m v'' ta tb -> return (s', m, v'', ta, tb)
    x -> Left (show s ++ "expected a dependent pair, but got: " ++ show x))
  
  let tb' = (case v'' of
              Nothing -> tb
              Just v'' -> subst v'' (EVar v Nothing) tb)
      env' = insert v ta (insert v' tb' env)
  
  (ub,tb,rb) <- infer env' b
  let (uv ,_) = getUse v  ub
      (uv',_) = getUse v' ub
      ua' = if times m uv' == uv
            then ctxtimes uv' ua
            else ctxtimes Many ua
      r = (case (uv',m) of
            (Zero,_) -> rb
            (_,Zero) -> ELet s v' Nothing ra rb
            _        -> ElimP s v v' ra rb)
  
  return (ctxplus ua' ub, tb, r)
infer env (ElimB s c t e) = do
  (uc,rc)    <- check env (EConst emptySpan Bool) c
  (ut,tt,rt) <- infer env t
  (ue,re)    <- check env tt e
  return (ctxplus uc (ctxinter ut ue), tt, ElimB s rc rt re)
infer env (ElimU s a b) = do
  (ua,ra) <- check env (EConst emptySpan TUnit) a
  (ub,tb,rb) <- infer env b
  return (ctxplus ua ub, tb, rb)

inferExpr :: Expr -> Either String Expr
inferExpr x = do
  y       <- run 0 (indexExpr x)
  (_,_,x) <- infer empty y
  return x