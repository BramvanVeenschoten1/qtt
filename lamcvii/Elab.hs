module Elab where

import qualified Core as C

import Data.List
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Functor
import Data.Map hiding (foldr)
import Data.Either
import Data.Maybe

import Lexer(Loc)
import Parser(Binder)
import Normalization
import Substitution
import Utils
import Multiplicity
import Parser
import Core hiding (Branch,Inductive)
import Elaborator
import Prettyprint
import Debug.Trace

{-
  here we typecheck the abstract syntax tree (AST),
  using a basic bidirectional checking algorithm,
  also resolving variable names with type-driven name resolution
-}
toMult :: Int -> Mult
toMult 0 = Zero
toMult 1 = One
toMult _ = Many

convertible :: Objects -> Context -> Loc -> Term -> Term -> Elab ()
convertible glob ctx loc t0 t1 =
  if Normalization.sub glob ctx False t0 t1
  then pure ()
  else TypeError (show loc ++ "inconvertible types:\n" ++ showTerm ctx t0 ++ "and:\n" ++ showTerm ctx t1)

-- look up a qualified name in the symbol table
lookupQualified :: ElabState -> Loc -> QName -> Elab (Term,Term,Uses)
lookupQualified glob loc qname =
  case lookupQName qname glob of
    Nothing -> err (show loc ++ "unknown name: " ++ showQName qname)
    Just (_,ref) -> pure (Const (showQName qname) ref, typeofRef (globalObjects glob) ref, noUses)

-- look up a name in the symbol table and lookup Unqualified if appropriate
lookupUnqualified :: ElabState -> Loc -> Name -> Elab (Term,Term,Uses)
lookupUnqualified glob loc name = let
  in case lookupName name glob of
    Nothing -> TypeError (show loc ++ "unbound variable")
    Just [qname] -> case lookupQName qname glob of
      Nothing -> err (show loc ++ "object belonging to name not present: " ++ showQName qname)
      Just (_,ref) -> pure (C.Const name ref, typeofRef (globalObjects glob) ref, noUses)
    Just xs -> do
      mapM (\qname ->
        case lookupQName qname glob of
          Nothing -> err (show loc ++ "name not present: " ++ showQName qname)
          Just (_,ref) -> pure (qname, Clear (C.Const name ref,(typeofRef (globalObjects glob) ref), noUses))) xs >>=
        Ambiguous name loc

-- lookup a name in the context and return appropriate uses if present
lookupCtx :: Context -> Loc -> Name -> Maybe (Term,Term,Uses)
lookupCtx ctx loc name = f 0 ctx where
  f n [] = Nothing
  f n (hyp:hyps)
    | name == hypName hyp = pure (Var n, lift (n + 1) (hypType hyp), (Oneuse One loc) : noUses)
    | otherwise = fmap (\(t,ty,u) -> (t,ty,Nouse:u)) (f (n + 1) hyps)

-- check if a term is a valid sort
checkSort :: Objects -> Context -> Loc -> Term -> Elab ()
checkSort glob ctx loc x = case whd glob ctx x of
  Star -> pure ()
  Box -> pure ()
  _ -> err (show loc ++ "Invalid sort:\n" ++ showTerm ctx x)

-- check variable usage against given multiplicity
checkArgMult :: Loc -> Mult -> Use -> Elab ()
checkArgMult _ Many _ = pure ()
checkArgMult _ Zero uses = f uses where
  f Nouse           = pure ()
  f (Oneuse Zero _) = pure ()
  f (Oneuse _ loc) = TypeError (show loc ++ "relevant use of erased variable")
  f (CaseUse loc xs) = mapM_ f xs
  f (Adduse x y) = f x *> f y
checkArgMult loc One uses = checkOne uses where

  checkOne Nouse = TypeError (show loc ++ "linear variable is unused")
  checkOne (Oneuse Zero _) = TypeError (show loc ++ "linear variable is unused")
  checkOne (Oneuse One _) = pure ()
  checkOne (Oneuse Many loc) = TypeError (show loc ++ "unrestricted use of linear variable")
  checkOne (Adduse x y) = do
    m <- checkMaybe x
    if m
    then checkNone y
    else checkOne y
  checkOne (CaseUse loc' xs) = mapM_ checkOne xs
  
  checkNone Nouse = pure ()
  checkNone (Oneuse Zero _) = pure ()
  checkNone (Oneuse One loc) = TypeError (show loc ++ "multiple uses of linear variable")
  checkNone (Oneuse Many loc) = TypeError (show loc ++ "unrestricted use of linear variable")
  checkNone (Adduse x y) = checkNone x *> checkNone y
  checkNone (CaseUse loc' xs) = mapM_ checkNone xs
  
  checkMaybe Nouse = pure False
  checkMaybe (Oneuse Zero _) = pure False
  checkMaybe (Oneuse One _) = pure True
  checkMaybe (Oneuse Many loc) = TypeError (show loc ++ "unrestricted use of linear variable")
  checkMaybe (Adduse x y) = do
    m <- checkMaybe x
    if m
    then checkNone y *> pure True
    else checkMaybe y
  checkMaybe (CaseUse loc' xs) = do
    uses <- mapM checkMaybe xs
    if and uses || not (or uses)
    then pure (or uses)
    else TypeError (show loc' ++ "linear variable is not used consistently across match arms")

{-
Given the ast for some branches, identify the constructors and/or default case that are covered.
The last case of a match may be default if it has no arguments and its name is not a constructor name.
-}
identifyBranches :: ElabState -> Context -> Int -> Int -> [Branch] -> Elab ([(Int,Branch)], [String], Maybe Branch)
identifyBranches glob ctx obj_id defno = f where
        
  g (_,ConRef obj_id' defno' constrno _) acc
    | obj_id == obj_id' && defno == defno' = pure constrno
  g _ acc = acc

  f [] = pure ([],[],Nothing)
  f ((branch @ (loc,ctor_binder,ctor_args,rhs)) : xs) = do
    let ctor_name = binderName ctor_binder
        ctor_loc  = binderLoc ctor_binder

        refs = fmap (fmap (fromJust . flip lookupQName glob)) (lookupName ctor_name glob)
        
    (found_branches, found_ctors, default_branch) <- identifyBranches glob ctx obj_id defno xs
    
    if elem ctor_name found_ctors
    then TypeError (show loc ++ "duplicate cases in match expression")
    else pure ()
        
    case refs >>= foldr g Nothing of
      Just id -> pure ((id,branch) : found_branches, ctor_name : found_ctors, default_branch)
      Nothing ->
        if Prelude.null xs && Prelude.null ctor_args
        then pure ([], [], Just branch)
        else TypeError (show loc ++ "'" ++ ctor_name ++ "' is not a constructor name of this type")

-- check a match expression against a given motive
checkMatch ::  ElabState -> Context -> Loc -> Mult -> Expr -> Term -> [Branch] -> Elab (Term,Term,Uses)
checkMatch glob ctx loc mult scrutinee motive branches = do
  let obs = globalObjects glob
  
  when (mult == Zero && length branches > 1)
    (err (show loc ++ "an erased case distinction can have at most one branch"))

  (eliminee,elim_ty,elim_uses) <- synth glob ctx scrutinee
  
  (obj_id,defno,indparams) <- case whd obs ctx elim_ty of
    App (Const _ (IndRef obj_id defno _)) args -> pure (obj_id,defno,args)
    Const _ (IndRef obj_id defno _) -> pure (obj_id,defno,[])
    _ -> err (
      show loc ++
      showContext ctx ++
      "\n expected a term of some inductive type, but the expression:\n" ++
      showTerm ctx eliminee ++
      "\n is of type:\n" ++
      showTerm ctx elim_ty)
  
  (branch_list, _, default_branch) <- identifyBranches glob ctx obj_id defno branches
  
  let C.Inductive {paramno = pno, introRules = ctors, isLarge = large} =
        maybe (error "2") id (Data.Map.lookup obj_id (globalInd (globalObjects glob))) !! defno
        
      motive_sort = sortOf obs ctx motive
      
      (ctor_names,ctor_arities,ctor_tys) = unzip3 ctors

      checkBranch :: Int -> Term -> Elab ((Bool, Term), Uses)
      checkBranch ctorno ctor_ty = do
        let
          ctor_name = ctor_names !! ctorno
        
          instantiated_ctor_ty = instantiateCtor indparams ctor_ty
          
          unroll :: Term -> ([Mult],[Term]) -> ([Mult],[Term])
          unroll (Pi m _ ta tb) (mults, tys) = unroll tb (times mult m : mults, ta : tys)
          unroll tb acc = acc
          
          (mults,arg_tys) = unroll instantiated_ctor_ty mempty
          
          ctor_arity = length arg_tys
          
          countDown n
            | n > 0 = Var (n - 1) : countDown (n - 1)
            | otherwise = []
          
          applied_ctor = App (Const ctor_name (ConRef obj_id defno ctorno pno)) (fmap (lift ctor_arity) indparams ++ countDown ctor_arity)
          
          expected_branch_ty = App (lift ctor_arity motive) [applied_ctor]
          
        case Data.List.lookup ctorno branch_list of
          Nothing -> case default_branch of
            Nothing -> err (show loc ++ " match does not cover all cases")
            Just (loc,arg,[],rhs) -> do
              let
                {-
                  what to do instead: 
                  - lambda-abstract over the subdata
                  - reconstruct the eliminee
                  - put the eliminee in context
                  - check default branch
                  - build as let-expression
                -}
                arg_name = binderName arg
              
                update = fmap (\ty -> Hypothesis "$" ty Nothing) arg_tys
                
                reconstructed_eliminee =
                  App
                    (Const "" (ConRef obj_id defno ctorno (length indparams)))
                    (indparams ++ countDown ctor_arity)
                
                ctx' = Hypothesis arg_name elim_ty (Just reconstructed_eliminee) : (update ++ ctx)
                
              (rhs,uses) <- check glob ctx' rhs expected_branch_ty
              
              let elim_uses : uses' = uses
                  uses'' = Data.List.drop ctor_arity uses'
                  
                  arg_uses = fmap (\m -> Oneuse m loc) mults
                  
                  env = zip3 mults (repeat "$") arg_tys
                  
                  rhs' = Let arg_name elim_ty reconstructed_eliminee rhs
                  
                  branch_rhs = Data.List.foldl (\acc (m,n,t) -> Lam m n t acc) rhs' env
    
              sequence_ (zipWith3 checkArgMult (repeat loc) mults arg_uses)
              
              pure ((False,branch_rhs), uses')

          Just (loc,ctor_binder,args,rhs) -> do
            let
              given_arity = length args
              
              (arg_locs,arg_names) = unzip (fmap (\b -> (binderLoc b, binderName b)) (reverse args))
              
              update = zipWith (\name ty -> Hypothesis name ty Nothing) arg_names arg_tys
              
              ctx' = update ++ ctx
            
            if given_arity == ctor_arity
            then pure ()
            else err (show loc ++ "expected " ++ show ctor_arity ++ " arguments in case-expression, but got " ++ show given_arity)
            
            (rhs,uses) <- check glob ctx' rhs expected_branch_ty
            
            let
              (args_uses, uses') = Data.List.splitAt ctor_arity uses
  
              env = zip3 mults arg_names arg_tys
          
              branch_rhs = Data.List.foldl (\acc (m,n,t) -> Lam m n t acc) rhs env
  
            sequence_ (zipWith3 checkArgMult arg_locs mults args_uses)
            
            pure ((False,branch_rhs), uses')

  case motive_sort of
    Box -> when large (err (show loc ++ "large eliminations on large inductive types are not allowed"))
    _ -> when False (trace "some allowed elimination" (pure ()))

  (branches, uses) <- fmap unzip (zipWithM checkBranch [0..] ctor_tys)
  
  let result_type = App motive [eliminee]
  
      result = Case (CaseDistinction {
        elimType = elim_ty,
        elimMult = mult,
        eliminee = eliminee,
        motive   = motive,
        branches = branches})
      
      result_uses = plusUses (timesUses mult elim_uses) (branchUses loc uses)
  
  pure (result,result_type,result_uses)


-- check or synthesise the binding of a let expression
checkLetBinding :: ElabState -> Context -> Binder -> Maybe Expr -> Expr -> Elab (Term,Term,Uses)
checkLetBinding glob ctx bind Nothing a = synth glob ctx a
checkLetBinding glob ctx bind (Just ta) a = do
  let la = exprLoc ta
  (ta,ka,_) <- synth glob ctx ta
  checkSort (globalObjects glob) ctx la ka
  (a,ua) <- check glob ctx a ta
  pure (a,ta,ua)

-- for the given expression, compute its corresponding core term, its type and the usage environment
synth :: ElabState -> Context -> Expr -> Elab (Term,Term,Uses)
synth glob ctx expr = case expr of
  EHole  loc -> err "Holes are not implemented"
  EType  loc -> pure (Star, Box, noUses)
  EName  loc qname -> lookupQualified glob loc qname
  EVar   loc name -> maybe (lookupUnqualified glob loc name) pure (lookupCtx ctx loc name)
  EApply loc f xs -> do
    (f,tf,uf) <- synth glob ctx f
    
    (args,tapp,uargs) <- checkArgs tf xs
    
    pure (App f args, tapp, plusUses uf uargs) where
    
      checkArgs tf [] = pure ([],tf,noUses)
      checkArgs tf (arg:args) = do
        case whd (globalObjects glob) ctx tf of
          Pi m name ta tb -> do
            (a,ua) <- check glob ctx arg ta
            (args',tb',uargs) <- checkArgs (subst a tb) args
            pure (a:args', tb', plusUses (timesUses m ua) uargs)
          x -> TypeError (
                  show loc ++ "\n" ++
                  showContext ctx ++ "\n" ++
                  "application expected some function, but got:\n" ++
                  showTerm ctx x ++ "\n")
  ELet loc bind ta a b -> do
    (a,ta,ua) <- checkLetBinding glob ctx bind ta a
    let name = binderName bind
        hyp = Hypothesis name ta (Just a)
    (b,tb,ub0) <- synth glob (hyp : ctx) b
    let ux : ub = ub0
        u = useSum ux
    pure (Let name ta a b, subst a tb, plusUses (timesUses u ua) ub)
  ELambda loc _ _ Nothing _ -> err (show loc ++ showContext ctx ++ "\n\ncannot infer lambda")--TypeError (SynthLambda loc)
  ELambda loc m' bind (Just ta) b -> do
    let m = toMult m'
        la = exprLoc ta
    (ta,ka,_) <- synth glob ctx ta
    checkSort (globalObjects glob) ctx la ka
    let name = binderName bind
        loc' = binderLoc bind
        hyp = Hypothesis {
          hypName = name,
          hypType = ta,
          hypDef  = Nothing}
    (b,tb,ub0) <- synth glob (hyp : ctx) b
    let ux : ub = ub0
    checkArgMult loc' m ux
    pure (Lam m name ta b, Pi m name ta tb, ub)
  EPi loc m' bind ta tb -> do
    let m  = toMult m'
        la = exprLoc ta
        lb = exprLoc tb
    (ta,ka,_) <- synth glob ctx ta
    let name = maybe "" binderName bind
        hyp = Hypothesis {
          hypName = name,
          hypType = ta,
          hypDef  = Nothing}
    (tb,kb,_) <- synth glob (hyp : ctx) tb
    checkSort (globalObjects glob) ctx la ka
    checkSort (globalObjects glob) ctx lb kb
    let name = maybe "" binderName bind
    pure (Pi m name ta tb, kb, noUses)
  EMatch loc mult term motive cases -> do
    motive <- (case motive of
      Nothing -> TypeError (show loc ++ "cannot synthesise motive for match expression")
      Just motive -> pure motive)
    
    let motive_loc = exprLoc motive
 
    (motive',moty,_) <- synth glob ctx motive
    (_, ta, _) <- synth glob ctx term
    
    case whd (globalObjects glob) ctx moty of
      Pi m _ ta' tb -> do
        convertible (globalObjects glob) ctx motive_loc ta ta'
      x -> err (
              show loc ++ "\n" ++
              showContext ctx ++ "\n" ++
              "motive expected some function, but got:\n" ++
              showTerm ctx x ++ "\n")
  
    checkMatch glob ctx loc (toMult mult) term motive' cases
  ELetRec loc funs a -> do
    err "nested let-recs are not implemented"

-- check an expression agains a given type and compute the corresponding core term
check :: ElabState -> Context -> Expr -> Term -> Elab (Term,Uses)
check glob ctx expr ty = case expr of
  ELambda loc _ bind Nothing b -> do
    (m, ta, tb) <- (case whd (globalObjects glob) ctx ty of
        Pi m _ ta tb -> pure (m, ta, tb)
        x -> -- TypeError (ExpectedFunction loc x))
            err (
              show loc ++
              showContext ctx ++ "\n" ++
              "(Lam-0) expected some function, but got:\n" ++
              showTerm ctx x ++ "\n"))
    let name = binderName bind
        loc' = binderLoc bind
        hyp = Hypothesis {
            hypName = name,
            hypType = ta,
            hypDef  = Nothing}
    (b,ub0) <- check glob (hyp : ctx) b tb
    let ux : ub = ub0
    checkArgMult loc' m ux
    pure (Lam (useSum ux) name ta b, ub)
  ELambda loc _ bind (Just ta) b -> do
    (ta,_,_) <- synth glob ctx ta
    let ty' = whd (globalObjects glob) ctx ty
    (m, ta', tb) <- (case ty' of
        Pi m _ ta tb -> pure (m, ta, tb)
        x -> err (
              show loc ++
              showContext ctx ++ "\n" ++
              "(@Lam) expected some function, but got:\n" ++
              showTerm ctx ty ++ "\n" ++
              showTerm ctx ty' ++ "\n"))
    let name = binderName bind
        loc' = binderLoc bind
        hyp = Hypothesis {
            hypName = name,
            hypType = ta,
            hypDef  = Nothing}
    
    if Normalization.sub (globalObjects glob) ctx False ta' ta
    then pure ()
    else
      err (show loc ++ "\n" ++
        "in context:\n" ++
        showContext ctx ++ "\n" ++
        "The argument is expected to have type:\n" ++
        showTerm ctx ty ++ "\n" ++
        "but has been given type:\n" ++
        showTerm ctx ta)
    
    (b,ub0) <- check glob (hyp : ctx) b tb
    
    (ux,ub) <- (case ub0 of
      (ux:ub) -> pure (ux,ub)
      _ -> err (show loc ++ showContext ctx ++ "\nempty usage list should be infinite"))    
    
    let ux : ub = ub0
    checkArgMult loc' m ux
    pure (Lam (useSum ux) name ta b, ub)
  ELet loc bind ta a b -> do
    (a,ta,ua) <- checkLetBinding glob ctx bind ta a
    let name = binderName bind
        hyp = Hypothesis name ta (Just a)
    (b,ub0) <- check glob (hyp : ctx) b (lift 1 ty)
    let ux : ub = ub0
        u = useSum ux
    pure (Let name ta a b, plusUses (timesUses u ua) ub)
  EMatch loc mult scrutinee Nothing branches -> do
    (_,ta,_) <- synth glob ctx scrutinee
    (t,_,u) <- checkMatch glob ctx loc (toMult mult) scrutinee (Lam Many "" ta (lift 1 ty)) branches
    pure (t,u)
  x -> do
    (a,ta,ua) <- synth glob ctx x
    
    let ty' = whd (globalObjects glob) ctx ty
        ta' = whd (globalObjects glob) ctx ta
    
    if Normalization.sub (globalObjects glob) ctx False ta ty
    then pure ()
    else
      err (show (exprLoc x) ++ "\n" ++
        "in context:\n" ++
        showContext ctx ++ "\n" ++
        "expected type:\n" ++
        showTerm ctx ty' ++ "\n" ++
        "but expression:\n" ++
        showTerm ctx a ++ "\n" ++
        "has type:\n" ++
        showTerm ctx ta')
    
    pure (a,ua)

