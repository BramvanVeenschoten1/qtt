
module Declaration where

import Data.Set
import Data.Map
import Data.List
import Data.Maybe
import Control.Monad
import Control.Applicative hiding (Const)

import qualified Core as C
import Core hiding (Inductive,Fixpoint)
import Elaborator
import Elab
import Iterator
import Normalization
import Substitution
import Parser
import Typechecker
import Multiplicity
import Lexer(Loc)
import Prettyprint
import Inductive
import Termination

{-
let's discuss modules. Here's what we need, in decreasing order of importance.
- internal module names, for disambiguation
- import declarations, to limit the name search space
- export declarations, to further encapsulation
- qualified imports, to further refine the name search space
- incorporate directory structure in module system? (eg. A.B.C.foo)
- interfaces?

- keep a global map of modules with their internal names
- hiding and showing names from modules should be easy
- when compiling one module, keep a namespace of imported modules

preprocess:
  1 parse all modules
  2 process module names
  3 associate module names with file names
compilation scheme:
  1 push module name on the stack
  2 process imports
  3 if an import is in the stack, report a circularity
  4 compile imports
  5 compile current module
  6 add current module to compiled modules

interesting idea:
  specify entry point, compile incrementally
  build file:
  1 specify map from filenames to module names
  2 don't compile unused functions (unless ambiguity happens)
  3 don't even parse unused modules
  => we want early detection of errors
      verifying => no
      codegen => yes

we can keep modules separate from the global object space, because
modules only manage names and accessibility. So we have:
  - an intermodular namespace, where we keep track of modules,
    their names and the names they contain
  - an intramodular namespace, where we keep track of imported names,
    and newly defined names

-}

{-
  here we process top-level definitions
  
  and check top-level definitions
  
  add module name qualifiers
-}

ensureUnique :: ElabState -> QName -> Either Error ()
ensureUnique glob qname = case lookupQName qname glob of
  Nothing -> pure ()
  Just (info,_) -> Left (NameAlreadyDefined qname info)

updateNameSpace :: [(QName, (Loc,Reference))] -> NameSpace -> NameSpace
updateNameSpace names (shorts,longs) = let
  foo (qname,_) acc = insertWith (++) (last qname) qname acc
  shorts' = Data.List.foldr (\(qname,_) -> insertWith (++) (last qname) [qname]) shorts names
  longs' = Data.List.foldr (uncurry Data.Map.insert) longs names
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
      arity ctx = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc) Star ctx
      
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

  ctor_tys <- mapM checkDef (zip3 [0..] params ctors)

  let fresh_id = newName glob
  
      def_refs = fmap (IndRef fresh_id) [0..]
      
      def_consts = zipWith Const names def_refs
  
      def_name_loc_refs = zip qnames (zip def_locs def_refs)

      abstract_ctor :: Context -> [Term] -> [Term]
      abstract_ctor params ctors = fmap (flip f params) ctors where
        f = Data.List.foldl (\acc hyp -> Pi Zero (hypName hyp) (hypType hyp) acc)
      
      ctor_instances = fmap (fmap (psubst (reverse def_consts))) (zipWith abstract_ctor params ctor_tys)
      
      ctor_refs = concat (zipWith3 (\ctors params defno -> fmap (\ctorno -> ConRef fresh_id defno ctorno (length params)) [0.. length ctors - 1]) ctor_instances params [0..])
      
      ctor_locs = concat (fmap (fmap (exprLoc . snd)) ctors)
      
      ctor_ref_name_locs = zip ctor_qnames (zip ctor_locs ctor_refs)
      
      obs = globalObjects glob
      
      object = zipWith C.Inductive arities ctor_instances
      
      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
      name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames

  pure  glob {
    newName = fresh_id + 1,
    internalNames = updateNameSpace name_loc_refs (internalNames glob),
    globalObjects = obs{globalInd = Data.Map.insert fresh_id object (globalInd obs)}}

checkDecl :: ElabState -> Decl -> Either Error ElabState
checkDecl glob decl = case decl of
  Inductive defs -> do
    -- do the things here
    checkInductive glob defs
  Definition defs -> do
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
        
        rec_calls = fmap (getRecursiveCalls (globalObjects glob) signatures) checked_bodies
    
    -- Now the syntax for toplevel definitions are recursive by default, so non-recursive definitions are
    -- treated as a special case here
    case rec_calls of
      [[]] ->
        let [checked_body] = checked_bodies
            [name] = names
            [qname] = qnames
            [loc] = locs
            [ty] = fmap hypType signatures
            ref = DefRef obj_id height
            const = Const name ref
            recursive_body = psubst (error (show loc ++ "definition is recursive and non-recursive")) checked_body
            body = (ty,checked_body)
        in pure  glob {
          newName = obj_id + 1,
          internalNames = updateNameSpace [(qname, (loc,ref))] (internalNames glob),
          globalObjects = obs{globalDef = Data.Map.insert obj_id body (globalDef obs)}}
      _ -> case findRecparams rec_calls of
        Nothing -> Left (Nonterminating locs)
        Just rec_args ->
          let refs = zipWith (\defno rec_arg -> FixRef obj_id defno rec_arg height) [0.. length defs - 1] rec_args
              
              consts = zipWith Const names refs
              
              recursive_bodies = fmap (psubst consts) checked_bodies
          
              bodies = zipWith3 C.Fixpoint (fmap hypType signatures) recursive_bodies rec_args
            
          in pure glob {
            newName = obj_id + 1,
            internalNames = updateNameSpace (zip qnames (zip locs refs)) (internalNames glob),
            globalObjects = obs{globalFix = Data.Map.insert obj_id bodies (globalFix obs)}}
        
  Postulate loc bind ty -> do
    let lt = exprLoc ty
    (ty,kind,_) <- disambiguate (synth glob [] ty)
    disambiguate (checkSort (globalObjects glob) [] lt kind)
    ensureUnique glob [binderName bind]
    let name = binderName bind
        qname = [moduleName glob, name]
        obs = globalObjects glob
        obj_id = newName glob
        ref = DeclRef obj_id
    pure glob {
      newName = obj_id + 1,
      internalNames = updateNameSpace [(qname, (loc,ref))] (internalNames glob),
      globalObjects = obs {globalDecl = Data.Map.insert obj_id ty (globalDecl obs)}}
