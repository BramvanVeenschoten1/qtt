
module Toplevel where

import qualified Core as C
import Core hiding (Inductive,Fixpoint)
import Elaborator
import Elab
import Iterator
import Normalization
import Substitution
import Parser
import Data.Set
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)
import Typechecker
import Multiplicity
import Lexer(Loc)
import Prettyprint

{-
  here we process top-level definitions
  
  and check top-level definitions
  
  add module name qualifiers
-}

freshName :: GlobalState -> (Int,GlobalState)
freshName glob = (newName glob, glob {newName = newName glob + 1})

ensureUnique :: GlobalState -> QName -> Either Error ()
ensureUnique glob qname = case Data.Map.lookup qname (qsymbolTable glob) of
  Nothing -> pure ()
  Just (info,_) -> Left (NameAlreadyDefined qname info)

updateSymbols :: Name -> QName -> Map Name [QName] -> Map Name [QName]
updateSymbols name qname table = case Data.Map.lookup name table of
  Nothing -> Data.Map.insert name [qname] table
  Just qnames -> Data.Map.insert name (qname : qnames) table

synth' glob expr = disambiguate (synth glob [] expr)
check' glob expr ty = disambiguate (check glob [] expr ty)

checkInductive :: GlobalState -> [Inductive] -> Either Error GlobalState
checkInductive glob defs = do
  let f :: Context -> [Param] -> Result Context
      f ctx ((_,bind,Nothing):_) = TypeError (SynthParam (binderLoc bind))
      f ctx ((_,bind,Just ty):params) = do
        (ty,_,_) <- synth glob ctx ty
        f (Hypothesis (binderName bind) ty Nothing : ctx) params
      f ctx [] = pure ctx
      
      defcount = length defs
      
      checkParams (_,_,params,_) = disambiguate (f [] params)
      
      arity ctx = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc) Star ctx
      
      (infos,def_locs,names,qnames,ctors) = unzip5 (fmap (\(info,bind,_,ctors) ->
        let name = binderName bind in
          (info, binderLoc bind, name, [name],ctors)) defs)
    
      ctor_names = fmap (fmap (binderName . fst)) ctors
      
      ctor_qnames :: [QName]
      ctor_qnames = concat (zipWith (\qname ctornames -> fmap (\name -> qname ++ [name]) ctornames) qnames ctor_names)
  
  mapM_ (ensureUnique glob) ctor_qnames
  mapM_ (ensureUnique glob) qnames

  params <- mapM checkParams defs
  
  let arities = fmap arity params
  
      arities_ctx = reverse (zipWith (\name ty -> Hypothesis name ty Nothing) names arities)
      
      expectedType defno paramno depth = App
        (Var (depth - defno - 1))
        (fmap (\n -> Var (depth - defcount - paramno + n))
          (reverse [0 .. paramno - 1]))

      allOccurrencesPositive :: Globals -> Context -> Loc -> Int -> Int -> Int -> Int -> Term -> Either Error ()
      allOccurrencesPositive glob ctx loc defno paramno n nn t = f (whd glob ctx t) where
        f (Pi _ name ta tb) = do
          let ctx' = Hypothesis name ta Nothing : ctx
          if doesNotOccur ctx' 0 0 tb
          then strictlyPositive glob ctx loc n nn ta
          else if doesNotOccur ctx n nn ta
               then pure ()
               else Left (Msg (show loc ++ "1 Non-strictly positive occurrence in inductive definition"))
          allOccurrencesPositive glob ctx' loc defno paramno (n+1)(nn+1) tb
        f tb = do
          let tb' = expectedType defno paramno (length ctx)
          if Normalization.sub glob ctx True tb tb'
          then pure ()
          else 
            Left (Msg (show loc ++ showContext ctx ++
                  "\nexpected constructor return type:\n" ++
                  showTerm ctx tb' ++
                  "\nbut got:\n" ++
                  showTerm ctx tb))

      strictlyPositive :: Globals -> Context -> Loc -> Int -> Int -> Term -> Either Error ()
      strictlyPositive glob ctx loc n nn t = f (whd glob ctx t) where
        f t | doesNotOccur ctx n nn t = pure ()
        f (Pi _ name ta tb) = do
          if doesNotOccur ctx n nn ta
          then strictlyPositive glob (Hypothesis name ta Nothing : ctx) loc (n+1) (nn+1) tb
          else Left (Msg (show loc ++ "3 Non-strictly positive occurrence in inductive definition"))
        f (App fun args) = do
          if all (doesNotOccur ctx n nn) args
          then pure ()
          else Left (Msg (show loc ++ "4 Non-strictly positive occurrence in inductive definition"))
        f (Var n) = pure ()
        f _ = Left (Msg (show loc ++ "5 Non-strictly positive occurrence in inductive definition"))
      
      doesNotOccur :: Context -> Int -> Int -> Term -> Bool
      doesNotOccur ctx n nn t = f 0 t True where
        f k (Var m) _
          | m >= n + k && m <= nn + k = False
          | m < k && m > nn + k = True
          | otherwise = case hypDef (ctx !! (m - k)) of
            Just bo -> f 0 (lift (m - k) bo) True
            Nothing -> True
        f k t _ = Iterator.fold (const (+1)) k f t True

      checkCtor :: Context -> Int -> Int -> Ctor -> Either Error (String,Term)
      checkCtor ctx defno paramno (bind,expr) = do
        (t,_,_) <- disambiguate (synth glob ctx expr)
        allOccurrencesPositive (globalObjects glob) ctx (exprLoc expr) defno paramno (length ctx - defcount) (length ctx) t
        pure (binderName bind,t)
      
      checkDef :: (Int,Context,[Ctor]) -> Either Error [(String,Term)]
      checkDef (defno, params, ctors) = do
        mapM (checkCtor (params ++ arities_ctx) defno (length params)) ctors

  ctor_tys <- mapM checkDef (zip3 [0..] params ctors)

  let fresh_id = newName glob
  
      def_refs = fmap (IndRef fresh_id) [0..]
      
      def_consts = zipWith Const names def_refs
  
      def_name_loc_refs = zip qnames (zip def_locs def_refs)
  
      abstract_ctor :: Context -> [(String,Term)] -> [(String,Term)]
      abstract_ctor params ctors = fmap (\(name,ctor) -> (name, f ctor params)) ctors where
        f = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc)
      
      abstracted_ctors :: [[(String,Term)]]
      abstracted_ctors = zipWith abstract_ctor params ctor_tys
      
      ctor_instances = fmap (fmap (\(name,ctor) -> psubst (reverse def_consts) ctor)) abstracted_ctors
      
      ctor_refs :: [C.Reference]
      ctor_refs = concat (zipWith3 (\ctors params defno -> zipWith (\_ ctorno -> ConRef fresh_id defno ctorno (length params)) ctors [0..]) ctor_instances params [0..])
      
      ctor_locs = concat (fmap (fmap (exprLoc . snd)) ctors)
      
      ctor_ref_names = zip ctor_qnames ctor_refs
      
      ctor_ref_name_locs = zip ctor_qnames (zip ctor_locs ctor_refs)
      
      ctor_loc_name_pairs = zip ctor_locs ctor_qnames
      
      obs = globalObjects glob
      
      object = zipWith C.Inductive arities ctor_instances
      
      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
      name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames
      
      glob2 = GlobalState {
        newName = fresh_id + 1,
        symbolTable = Data.List.foldr (uncurry updateSymbols) (symbolTable glob) name_names,
        qsymbolTable = Data.List.foldr (uncurry Data.Map.insert) (qsymbolTable glob) name_loc_refs,
        globalObjects = obs{globalInd = Data.Map.insert fresh_id object (globalInd obs)}}

  pure glob2

data Subdata
  = Recursive Int -- a recursive occurrence and its number
  | Seed Int -- an argument to the function and its number
  | Sub Int -- a term smaller than an argument and the number of said argument
  | Safe -- a variable that is neither recursive nor smaller

type RecCalls = [(Int,[Maybe Int])] -- callee defno, (caller argno, callee argno)

{-
  returns a list of recursive calls, with for each callee argument whether it is a subdatum and
  which caller argument it is derived from if so
-}
getRecursiveCalls :: Globals -> Context -> [Subdata] -> Term -> RecCalls
getRecursiveCalls glob ctx subs t = getRecCalls ctx subs (Just 0) t where
  -- find if a term is a seed or smaller than a seed, returns argument number if so
  isSeed :: Context -> [Subdata] -> Term -> Maybe Int
  isSeed ctx subs t = case whd glob ctx t of
    Var n -> case subs !! n of
      Seed m -> Just m
      Sub m -> Just m
      _ -> Nothing
    App f x -> isSeed ctx subs f
    _ -> Nothing
  
  -- find if a term is smaller and if so, return argument number
  isSmaller :: Context -> [Subdata] -> Term -> Maybe Int
  isSmaller ctx subs t = case whd glob ctx t of
    Var n -> case subs !! n of
      Sub m -> Just m
      _ -> Nothing
    App f x -> isSmaller ctx subs f
    _ -> Nothing
  
  -- check whether a term returns an inductive type
  returnsInductive ctx ta = case whd glob ctx ta of
    Pi _ name ta tb -> returnsInductive (Hypothesis name ta Nothing : ctx) tb
    App fun _ -> returnsInductive ctx fun
    Const _ (IndRef _ _) -> True
    _ -> False
  
  -- traverse the body of a fixpoint function and gather recursive path information
  getRecCalls :: Context -> [Subdata] -> Maybe Int -> Term -> RecCalls
  getRecCalls ctx subs argc t = case whd glob ctx t of
    Var n -> case subs !! n of
      Recursive defno -> [(defno,[])]
      _ -> []
    App fun args -> let
      arg_calls = concatMap (getRecCalls ctx subs Nothing) args
      in case fun of
        Var n -> case subs !! n of
          Recursive defno -> let
            small_args = fmap (isSmaller ctx subs) args
            in (defno, small_args) : arg_calls
          _ -> arg_calls
        _ -> arg_calls
    Lam _ name ta b -> getRecCalls (Hypothesis name ta Nothing : ctx) ((maybe Safe Seed argc) : subs) (fmap (+1) argc) b
    Pi _ name ta tb -> getRecCalls (Hypothesis name ta Nothing : ctx) (Safe : subs) Nothing tb
    Let name ta a b -> getRecCalls (Hypothesis name ta (Just a) : ctx) (Safe : subs) Nothing b
    Case distinct -> let
      (obj_id,defno) = elimType distinct
      
      block = fromJust (Data.Map.lookup obj_id (globalInd glob))
      
      def = block !! defno
      
      unrollProduct (Pi _ _ _ tb) = 1 + unrollProduct tb
      unrollProduct _ = 0
      
      paramno = unrollProduct (indSort def)
      
      ctor_arities = fmap (\x -> unrollProduct x - paramno) (introRules def)
      
      elimineeIsSeed = isSeed ctx subs (eliminee distinct)
      
      unrollArgs :: Context -> [Subdata] -> Int -> Term -> RecCalls
      unrollArgs ctx subs 0 branch = getRecCalls ctx subs argc branch
      unrollArgs ctx subs m (Lam _ name ta b) = let
        cont sub = unrollArgs (Hypothesis name ta Nothing : ctx) (sub : subs) (m - 1) b
        in case elimineeIsSeed of
          Nothing -> cont Safe
          Just k ->
            if returnsInductive ctx ta
            then cont (Sub k)
            else cont Safe
      
      in concat (zipWith (unrollArgs ctx subs) ctor_arities (branches distinct))
    _ -> []

{-
Check the totality of a fixpoint by computing recursive parameters of the mutually recursive functions.
a fixpoint is guarded if in each recursive call, the recursive parameter of the callee is smaller than the
recursive parameter of the caller. What exactly constitutes a smaller argument is defined in getRecursiveCalls.

First, the bodies of the fixpoint are traversed to gather all recursive call,
along with each call the parameters that are smaller.

Finding the parameters is done by lazily traversing all possible configurations of recursive parameters,
then returning the first that is completely guarded, if it exists.
-}
checkTerminating :: Globals -> Context -> [Term] -> Maybe [Int]
checkTerminating glob signatures bodies = let
  defcount = length bodies

  subs = fmap Recursive [0 .. defcount - 1]
  
  rec_calls = fmap (getRecursiveCalls glob signatures subs) bodies
  
  {-
    compute the possibly recursive parameters for the current definition.
    The candidates are constrained by 3 factors:
    - previous definitions in the same fixpoint will have been assigned a recursive parameter,
      so only the argument that guards these calls is allowed
    - The nth parameter passed to the recursive call is only guarded if it is
      smaller than the nth parameter of the function itself
    - Other definitions are not yet constrained, but serve as heuristic.
      so for each argument, if a term smaller than it is passed to a later function,
      it becomes a candidate.
  -}
  allowed_args :: Int -> RecCalls -> [Int] -> [Int]
  allowed_args defno calls recparams = let
  
    
    intersect' xs ys = [x | x <- xs, elem x ys]
    
    inter :: (Int,[Maybe Int]) -> [Int] -> [Int]
    inter (defno',args) acc = let
      allowed :: [Int]
      allowed
          -- in calls to self, caller and callee recparamno have to be the same
        | defno == defno' =  [x | (x,y) <- zip [0..] args, Just x == y]
        | otherwise = case nth defno' recparams of
          -- in calls to previously constrained functions, 
          -- only the caller argument that the callees' recursive argument is derived from is allowed
          Just n -> maybe [] (:[]) (join (nth n args))
          -- other calls are only limited to smaller arguments
          Nothing -> Data.List.nub (catMaybes args)
      in intersect' allowed acc

    in Data.List.foldr inter [0..] calls
  
  -- check recursive calls to defno in all previous definitions
  checkCalls :: Int -> Int -> [Int] -> Maybe ()
  checkCalls callee callee_recparamno recparams = zipWithM_ (mapM_ . checkCall) recparams rec_calls where
    --checkCall :: Int -> RecCalls -> Maybe ()
    checkCall caller_paramno (defno,args)
      -- only calls to defno need to be checked, the argument in the given callee_recparamno position must be
      -- derived from the recursive argument of the caller
      | callee == defno = case join (nth callee_recparamno args) of
        Just argno -> if caller_paramno == argno then pure () else Nothing
        Nothing -> Nothing
      | otherwise = pure ()
  
  -- given the recursive calls, find an assignment of recursive parameters to definitions such that
  -- the fixpoint is guarded
  solve :: Int -> [Int] -> Maybe [Int]
  solve defno recparams
    | defno >= defcount = pure recparams
    | otherwise = let
      -- with the given constraints, get the possibly recursive arguments
      allowed = allowed_args defno (rec_calls !! defno) recparams
      
      -- for a given recursive argument, check the guardedness of its calls in previous definitions,
      -- then continue with the other definitions
      pick :: Int -> Maybe [Int]
      pick x = checkCalls defno x recparams *> solve (defno + 1) (recparams ++ [x])
      
      -- try every possibly allowed argument if necessary
      in Data.List.foldr (<|>) Control.Applicative.empty (fmap pick allowed)

  in solve 0 []


checkDecl :: GlobalState -> Decl -> Either Error GlobalState
checkDecl glob decl = case decl of
  Inductive defs -> checkInductive glob defs
  Fixpoint defs -> do
    let 
      checkSignature (_, bind, ty, body) = do
        (ty,kind,_) <- synth' glob ty
        pure (Hypothesis (binderName bind) ty Nothing)
    
      checkBody ctx (_,_,_,body) ty = fmap fst (disambiguate (check glob ctx body ty))
      
      (infos,names,qnames) = unzip3 (fmap (\(info,bind,_,_) ->
        let name = binderName bind in (info, name, [name])) defs)
    
    mapM_ (ensureUnique glob) qnames

    signatures <- mapM checkSignature defs

    checked_bodies <- sequence (zipWith (checkBody signatures) defs (fmap hypType signatures))
    
    rec_args <- maybe (Left (Nonterminating infos)) Right (checkTerminating (globalObjects glob) signatures checked_bodies)
    
    let obj_id = newName glob
    
        refs = zipWith (\defno rec_arg -> FixRef obj_id defno rec_arg 0) [0.. length defs - 1] rec_args
        
        consts = zipWith Const names refs
        
        heights = fmap heightOf checked_bodies
        
        recursive_bodies = fmap (psubst consts) checked_bodies
    
        bodies = zipWith4 C.Fixpoint (fmap hypType signatures) recursive_bodies rec_args heights
       
        obs = globalObjects glob
      
        dummy_ctx = repeat (Hypothesis "" undefined undefined)
      
    let glob2 = glob {
          newName = obj_id + 1,
          symbolTable = Data.List.foldr (uncurry updateSymbols) (symbolTable glob) (zip names qnames),
          qsymbolTable = Data.List.foldr (uncurry Data.Map.insert) (qsymbolTable glob) (zip qnames (zip infos refs)),
          globalObjects = obs{globalFix = Data.Map.insert obj_id bodies (globalFix obs)}}
    
    pure glob2

  Constant info bind ty body -> do
    (body,ty) <- (case ty of
      Nothing -> do
        (body,ty,_) <- synth' glob body
        pure (body,ty)
      Just ty -> do
        (ty,kind,_) <- synth' glob ty
        (body,_) <- check' glob body ty
        pure (body,ty))
    ensureUnique glob [binderName bind]
    let height = heightOf body
        name = binderName bind
        qname = [name]
        obs = globalObjects glob
        obj_id = newName glob
        ref = DefRef obj_id 0
        glob2 = glob {
          newName = obj_id + 1,
          symbolTable = updateSymbols name qname (symbolTable glob),
          qsymbolTable = Data.Map.insert qname (info,ref) (qsymbolTable glob),
          globalObjects = obs {globalDef = Data.Map.insert obj_id (ty,body,0) (globalDef obs)}}
    
    
    pure glob2
        
  Postulate info bind ty -> do
    let lt = exprLoc ty
    (ty,kind,_) <- disambiguate (synth glob [] ty)
    disambiguate (checkSort (globalObjects glob) [] lt kind)
    ensureUnique glob [binderName bind]
    let name = binderName bind
        qname = [name]
        obs = globalObjects glob
        obj_id = newName glob
        ref = DeclRef obj_id
        glob2 = glob {
          newName = obj_id + 1,
          symbolTable = updateSymbols name qname (symbolTable glob),
          qsymbolTable = Data.Map.insert qname (info,ref) (qsymbolTable glob),
           globalObjects = obs {globalDecl = Data.Map.insert obj_id ty (globalDecl obs)}}
    pure glob2
    
-- add some stuff about qualifying names
checkModule :: GlobalState -> Module -> Either Error GlobalState
checkModule = foldM checkDecl

checkProgram :: [Module] -> Either Error ()
checkProgram = foldM_ checkModule (GlobalState 0 Data.Map.empty Data.Map.empty (C.Globals Data.Map.empty Data.Map.empty Data.Map.empty Data.Map.empty))