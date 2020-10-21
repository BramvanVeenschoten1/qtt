
module Declaration where

import Data.Set
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)
import Debug.Trace

import qualified Core as C
import Core hiding (Inductive,Fixpoint)
import Elaborator
import Elab
import Iterator
import Normalization
import Substitution
import Parser
import Multiplicity
import Lexer(Loc)
import Prettyprint
import Inductive
import Termination

{-
  here we process top-level declarations
-}

ensureUnique :: ElabState -> QName -> Either Error ()
ensureUnique glob qname = case lookupQName qname glob of
  Nothing -> pure ()
  Just (info,_) -> Left (NameAlreadyDefined qname info)

updateNameSpace :: [(QName, Loc, Reference)] -> NameSpace -> NameSpace
updateNameSpace names (shorts,longs) = let
  shorts' = Data.List.foldr (\(qname,_,_) -> insertWith (++) (last qname) [qname]) shorts names
  longs' = Data.List.foldr (\(qname,loc,ref) -> Data.Map.insert qname (loc,ref)) longs names
  in (shorts', longs')

synth' glob expr = disambiguate (synth glob [] expr)
check' glob expr ty = disambiguate (check glob [] expr ty)

checkInductive :: ElabState -> [Inductive] -> Either Error ElabState
checkInductive glob defs = do
  let (infos,def_locs,names,qnames,ctors) = unzip5 (fmap (\(info,bind,_,ctors) ->
        let name = binderName bind in
          (info, binderLoc bind, name, [moduleName glob, name],ctors)) defs)

      ctor_names = fmap (fmap (binderName . fst)) ctors
      
      ctor_qnames = concat (zipWith (\qname ctornames -> fmap (\name -> qname ++ [name]) ctornames) qnames ctor_names)
  
  mapM_ (ensureUnique glob) ctor_qnames
  mapM_ (ensureUnique glob) qnames

  let 
      f :: Context -> [Param] -> Result Context
      f ctx ((_,bind,Nothing):_) = TypeError (SynthParam (binderLoc bind))
      f ctx ((_,bind,Just ty):params) = do
        (ty,_,_) <- synth glob ctx ty
        f (Hypothesis (binderName bind) ty Nothing : ctx) params
      f ctx [] = pure ctx
      
      checkParams :: Inductive -> Either Error Context
      checkParams (_,_,params,_) = disambiguate (f [] params)

  params <- mapM checkParams defs
  
  let 
  
      arity :: Context -> Term
      arity = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc) Star
      
      defcount = length defs
    
      arities = fmap arity params
  
      arities_ctx = reverse (zipWith (\name ty -> Hypothesis name ty Nothing) names arities)

      checkCtor :: Context -> Int -> Int -> Ctor -> Either Error Term
      checkCtor ctx defno paramno (bind,expr) = do
        (t,_,_) <- disambiguate (synth glob ctx expr)
        allOccurrencesPositive (globalObjects glob) ctx (exprLoc expr) defcount defno paramno (length ctx - defcount) (length ctx) t
        pure t
      
      checkDef :: (Int,Context,[Ctor]) -> Either Error [Term]
      checkDef (defno, params, ctors) = do
        mapM (checkCtor (params ++ arities_ctx) defno (length params)) ctors

  (ctor_tys) <- mapM checkDef (zip3 [0..] params ctors)

  let fresh_id = newName glob
      
      abstractCtors :: Context -> [Term] -> [Term]
      abstractCtors params ctors = fmap (flip f params) ctors where
        f = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc)
      
      abstracted_ctors = zipWith abstractCtors params ctor_tys
      
      computeArity (Pi _ _ _ b) = 1 + computeArity b
      computeArity _ = 0
      
      ctor_arities = fmap (fmap computeArity) ctor_tys -- compute arities
      
      uniparamno = Data.List.foldr getUniparamno (minimum (fmap length params)) (concat abstracted_ctors)
  
      def_refs = fmap (\defno -> IndRef fresh_id defno uniparamno) [0..]
      
      def_consts = zipWith Const names def_refs
  
      def_name_loc_refs = zip3 qnames def_locs def_refs
      
      ctor_instances = fmap (fmap (psubst (reverse def_consts))) abstracted_ctors
      
      ctor_refs = concat (zipWith3 (\ctors params defno -> fmap (\ctorno -> ConRef fresh_id defno ctorno (length params)) [0.. length ctors - 1]) ctor_instances params [0..])
      
      ctor_locs = concat (fmap (fmap (exprLoc . snd)) ctors)
      
      ctor_ref_name_locs = zip3 ctor_qnames ctor_locs ctor_refs
      
      obs = globalObjects glob
      
      object = zipWith5 (\arity ctor_names ctor_arities ctor_tys params ->
        C.Inductive {
          indSort = arity,
          paramno = length params,
          introRules = zip3 ctor_names ctor_arities ctor_tys}) arities ctor_names ctor_arities ctor_instances params
      
      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
      name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames
  
  when (names == ["Acc"]) $ do
    trace (showTerm [] (head (head abstracted_ctors))) (pure ())
    trace (show ctor_arities) (pure ())
    
  trace (show qnames ++ " " ++ show uniparamno ++ "\n") (pure ())
  
  pure  glob {
    newName = fresh_id + 1,
    internalNames = updateNameSpace name_loc_refs (internalNames glob),
    globalObjects = obs{globalInd = Data.Map.insert fresh_id object (globalInd obs)}}


checkDefinition :: ElabState -> [Function] -> Either Error ElabState
checkDefinition glob defs = do
  let 
    checkSignature (_, bind, ty, body) = do
      (ty,kind,_) <- synth' glob ty
      pure (Hypothesis (binderName bind) ty Nothing)
  
    checkBody ctx (_,_,_,body) ty = fmap fst (disambiguate (check glob ctx body ty))
    
    (locs,names,qnames) = unzip3 (fmap (\(info,bind,_,_) ->
      let name = binderName bind in (info, name, [moduleName glob, name])) defs)
  
  mapM_ (ensureUnique glob) qnames

  signatures <- mapM checkSignature defs

  checked_bodies <- zipWithM (checkBody signatures) defs (fmap hypType signatures)
  
  let obj_id = newName glob
      
      height = 1 + maximum (fmap heightOf checked_bodies)
     
      obs = globalObjects glob
      
      uniparamno = Data.List.foldr getUniparamno maxBound checked_bodies
      
      rec_calls = fmap (getRecursiveCalls (globalObjects glob) signatures) checked_bodies
      
      (non_recs, rec_calls') = filterNonRecs [] rec_calls
      
      -- an association list of definition numbers to object ids for non-recursive definitions
      non_rec_ids = zip non_recs [obj_id  ..]
      
      traverseRecs :: Int -> [Int] -> [(Int,Int)]
      traverseRecs n [] = []
      traverseRecs n (x:xs)
        | elem x non_recs = traverseRecs n xs
        | otherwise = (n,x) : traverseRecs (n + 1) xs
      
      -- an association list of definition numbers to shifted definition numbers after removing non-recursive definitions
      rec_defnos = traverseRecs 0 [0 .. length signatures - 1]
      
      updateCall :: RecCall -> RecCall
      updateCall (defno,args) = (fromJust (Data.List.lookup defno rec_defnos), args)
      
      -- recursive calls, with defnos shifted to accomodate removal of non-recursive functions
      rec_calls'' = fmap (fmap updateCall) rec_calls'
  
  rec_args <- maybe (Left (Nonterminating locs)) Right (findRecparams rec_calls'')
  let
    fix_id = obj_id + length non_rec_ids
  
    makeRef :: Int -> Reference
    makeRef defno
      | elem defno non_recs = DefRef (fromJust (Data.List.lookup defno non_rec_ids)) height
      | otherwise = let
        rec_defno = fromJust (Data.List.lookup defno rec_defnos)
        rec_arg = rec_args !! rec_defno
        in FixRef fix_id rec_defno rec_arg height uniparamno
    
    refs = fmap makeRef [0..]
    
    consts = zipWith Const names refs
    
    typed_bodies = zipWith3 (\defno sig body -> (defno, hypType sig, psubst consts body)) [0..] signatures checked_bodies
    
    (def_objects, fix_bodies) = Data.List.partition (\(x,_,_) -> elem x non_recs) typed_bodies
    
    fix_object = zipWith (\(_,ty,bo) rec_arg -> C.Fixpoint ty bo rec_arg) fix_bodies rec_args
    
    insertDefs :: Map Int Definition -> Map Int Definition
    insertDefs mp = Data.List.foldr (\(defno,ty,bo) -> Data.Map.insert (fromJust (Data.List.lookup defno non_rec_ids)) (ty,bo)) mp def_objects

    insertFix
      | Prelude.null fix_bodies = id
      | otherwise = Data.Map.insert fix_id fix_object

    new_id
      | Prelude.null fix_bodies = fix_id
      | otherwise = fix_id + 1

  --trace (show names ++ "\n" ++ show uniparamno ++ "\n\n") (pure ())
  
  pure glob {
    newName = new_id,
    internalNames = updateNameSpace (zip3 qnames locs refs) (internalNames glob),
    globalObjects = obs {
      globalDef = insertDefs (globalDef obs),
      globalFix = insertFix (globalFix obs)}}

checkDecl :: ElabState -> Decl -> Either Error ElabState
checkDecl glob decl = {-trace (show (declNames decl) ++ "\n") $ -} case decl of
  Inductive defs -> checkInductive glob defs
  Definition defs -> checkDefinition glob defs
  Postulate loc bind ty -> do
    let lt = exprLoc ty
    (ty,kind,_) <- disambiguate (synth glob [] ty)
    disambiguate (checkSort (globalObjects glob) [] lt kind)
    let name = binderName bind
        qname = [moduleName glob, name]
        obs = globalObjects glob
        obj_id = newName glob
        ref = DeclRef obj_id
    ensureUnique glob qname
    pure glob {
      newName = obj_id + 1,
      internalNames = updateNameSpace [(qname, loc, ref)] (internalNames glob),
      globalObjects = obs {globalDecl = Data.Map.insert obj_id ty (globalDecl obs)}}
