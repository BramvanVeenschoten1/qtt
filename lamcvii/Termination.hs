module Termination where

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
import Multiplicity
import Lexer(Loc)
import Prettyprint
import Debug.Trace

{-
  nested function calls will be handled in getRecursiveCalls
-}

data Subdata
  = Recursive Int -- a recursive occurrence and its number
  | Seed Int -- an argument to the function and its number
  | Sub Int -- a term smaller than an argument and the number of said argument
  | Other -- a variable that is neither recursive nor smaller

-- information on which debruijn indices are possibly recursive arguments
-- with regular inference, all top-level lambda arguments are possibly recursive
-- with nested inference, the recursive argument is already known
data RecArg
  = Past
  | Unknown Int
  | Known Int Int Int

argSucc :: RecArg -> RecArg
argSucc Past = Past
argSucc (Unknown x) = Unknown (x + 1)
argSucc (Known x recpno unipno) = Known (x + 1) recpno unipno

isRecArg :: RecArg -> Subdata
isRecArg Past = Other
isRecArg (Unknown x) = Seed x
isRecArg (Known x recpno unipno)
  | x == recpno - unipno = Seed recpno
  | otherwise = Other

type RecCall = (Int,[Maybe Int]) -- callee defno, [(caller argno, callee argno)]

{-
  returns a list of recursive calls, with for each callee argument whether it is a subdatum and
  which caller argument it is derived from if so
-}
getRecursiveCalls :: Objects -> Context -> Term -> [RecCall]
getRecursiveCalls glob ctx = getRecCalls ctx (fmap Recursive [0 .. length ctx - 1]) (Unknown 0) where
  -- find if a term is a seed or smaller than a seed, returns argument number if so
  isSeed :: Context -> [Subdata] -> Term -> Subdata
  isSeed ctx subs t = case whd glob ctx t of
    Var n -> subs !! n
    App f x -> isSeed ctx subs f
    _ -> Other
  
  -- check whether some match branches are all subterms of some seed
  isCaseSmaller :: [Maybe Int] -> Maybe Int
  isCaseSmaller [] = Nothing
  isCaseSmaller (Just n : xs)
    | all (\x -> (==) (Just n) x) xs = Just n
    | otherwise = Nothing
  
  -- find if a term is smaller and if so, return argument number
  isSmaller :: Context -> [Subdata] -> Term -> Maybe Int
  isSmaller ctx subs t = case whd glob ctx t of
    Var n -> case subs !! n of
      Sub m -> Just m
      _ -> Nothing
    App f x -> isSmaller ctx subs f
    Case dat -> isCaseSmaller (fmap (isSmaller ctx subs . snd) (branches dat))
    _ -> Nothing
  
  -- check whether a term returns an inductive type
  returnsInductive ctx ta = case whd glob ctx ta of
    Pi _ name ta tb -> returnsInductive (Hypothesis name ta Nothing : ctx) tb
    App fun _ -> returnsInductive ctx fun
    Const _ (IndRef _ _ _) -> True
    _ -> False
  
  -- traverse the body of a fixpoint function and gather recursive path information
  getRecCalls :: Context -> [Subdata] -> RecArg -> Term -> [RecCall]
  getRecCalls ctx subs argc t = case whd glob ctx t of
    Var n -> case subs !! n of
      Recursive defno -> [(defno,[])]
      _ -> []
    App (Const _ (FixRef obj_id defno recparamno height uniparamno)) args -> let
      (left_args,right_args) = Data.List.splitAt uniparamno args
      left_calls = concatMap (getRecCalls ctx subs Past) left_args
      right_calls = concatMap (getRecCalls ctx subs Past) right_args
      
      fix_bodies = fmap fixBody (fromJust (Data.Map.lookup obj_id (globalFix glob)))
      
      dummy_bodies = fmap (substWithDummy obj_id) fix_bodies
      
      applied_bodies = fmap (\fun -> App fun left_args) dummy_bodies
      
      expand = Data.List.concatMap (getRecCalls ctx subs (Known 0 recparamno uniparamno)) applied_bodies 
      
      traceExpand = trace (
        show (fmap (showTerm ctx) dummy_bodies) ++ "\n" ++
        show (fmap (showTerm ctx . whd glob ctx) applied_bodies) ++ "\n" ++
        show expand ++ "\n") expand
      
      in if Prelude.null left_calls
        then right_calls
        else traceExpand ++ right_calls
    App fun args -> let
      arg_calls = concatMap (getRecCalls ctx subs Past) args
      in case fun of
        Var n -> case subs !! n of
          Recursive defno -> let
            small_args = fmap (isSmaller ctx subs) args
            in (defno, small_args) : arg_calls
          _ -> arg_calls
        _ -> arg_calls
    Lam _ name ta b -> getRecCalls (Hypothesis name ta Nothing : ctx) (isRecArg argc : subs) (argSucc argc) b
    Let name ta a b -> getRecCalls (Hypothesis name ta (Just a) : ctx) (isRecArg argc : subs) (argSucc argc) b
    Pi _ name ta tb -> getRecCalls (Hypothesis name ta Nothing : ctx) (Other : subs) Past tb
    Case distinct -> let
      (obj_id,defno) = case whd glob ctx (elimType distinct) of
        App (Const _ (IndRef obj_id defno _)) _ -> (obj_id,defno)
        Const _ (IndRef obj_id defno _) -> (obj_id,defno)
        x -> error (showTerm ctx x)
      
      block = fromJust (Data.Map.lookup obj_id (globalInd glob))
      
      def = block !! defno
      
      ctor_arities = fmap (\(_,x,_) -> x) (introRules def)
      
      elimineeIsSeed = isSeed ctx subs (eliminee distinct)
      
      unrollArgs :: Context -> [Subdata] -> Int -> Term -> [RecCall]
      unrollArgs ctx subs 0 branch = getRecCalls ctx subs argc branch
      unrollArgs ctx subs m (Lam _ name ta b) = let
        cont sub = unrollArgs (Hypothesis name ta Nothing : ctx) (sub : subs) (m - 1) b
        in case elimineeIsSeed of
          Other -> cont Other
          Sub k ->
            if returnsInductive ctx ta
            then cont (Sub k)
            else cont Other
          Seed k ->
            if returnsInductive ctx ta
            then cont (Sub k)
            else cont Other
          
      regular_calls = concat (zipWith (unrollArgs ctx subs) ctor_arities (fmap snd (branches distinct)))
      
      
      in regular_calls
    _ -> []

{-
  because it simplifies subsequent termination checks, improves reduction behaviour,
  and subsumes the special case in Declaration.hs.

  return list of non_recs and new rec_calls
  
  graph ordering between non-recursive calls is preserved in the list
  
  non-recursive bodies are filtered from the result list.
 -}
 
filterNonRecs :: [Int] -> [[RecCall]] -> ([Int],[[RecCall]])
filterNonRecs non_recs rec_calls = let
    tagged_rec_calls = zip [0..] rec_calls
    
    -- give the numbers of the definitions that do no recursive calls, if they haven't been shown to be non-recursive
    -- in a previous iteration
    isEmpty :: (Int,[RecCall]) -> [Int] -> [Int]
    isEmpty (defno,calls) acc
      | elem defno non_recs = acc
      | Prelude.null calls = defno : acc
      | otherwise = acc
    
    new_non_recs = Data.List.foldr isEmpty [] tagged_rec_calls
    
    new_rec_calls = fmap (Data.List.filter (\call -> not (elem (fst call) new_non_recs))) rec_calls
  in if Prelude.null new_non_recs
     then (non_recs, new_rec_calls)
     else filterNonRecs (non_recs ++ new_non_recs) new_rec_calls


{-
  Given the recursive calls, check the totality of a fixpoint by computing recursive parameters of the mutually recursive functions.
  a fixpoint is guarded if in each recursive call, the recursive parameter of the callee is smaller than the
  recursive parameter of the caller. What exactly constitutes a smaller argument is defined in getRecursiveCalls.

  Finding the parameters is done by lazily traversing all possible configurations of recursive parameters,
  then returning the first that is completely guarded, if it exists.
-}
findRecparams :: [[RecCall]] -> Maybe [Int]
findRecparams rec_calls = let
  defcount = length rec_calls
  
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
  allowed_args :: Int -> [RecCall] -> [Int] -> [Int]
  allowed_args defno calls recparams = let
    
    inter :: RecCall -> [Int] -> [Int]
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
          
      -- we use a special intersection that works with an infinite list as acc
      in [x | x <- allowed, elem x acc]

    in Data.List.foldr inter [0..] calls
  
  -- check recursive calls to defno in all previous definitions
  checkCalls :: Int -> Int -> [Int] -> Maybe ()
  checkCalls callee callee_recparamno recparams = zipWithM_ (mapM_ . checkCall) recparams rec_calls where
    --checkCall :: Int -> [RecCall] -> Maybe ()
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
      in Data.List.foldr (<|>) Nothing (fmap pick allowed)
  
  in solve 0 []