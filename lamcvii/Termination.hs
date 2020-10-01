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
import Typechecker
import Multiplicity
import Lexer(Loc)
import Prettyprint

{-
  Things to add:
  - nested calls to Defs
  - nested calls to Fix
  - decent error messages
-}

data Subdata
  = Recursive Int -- a recursive occurrence and its number
  | Seed Int -- an argument to the function and its number
  | Sub Int -- a term smaller than an argument and the number of said argument
  | Other -- a variable that is neither recursive nor smaller

type RecCall = (Int,[Maybe Int]) -- callee defno, (caller argno, callee argno)

{-
  returns a list of recursive calls, with for each callee argument whether it is a subdatum and
  which caller argument it is derived from if so
-}
getRecursiveCalls :: Objects -> Context -> Term -> [RecCall]
getRecursiveCalls glob ctx = getRecCalls ctx (fmap Recursive [0 .. length ctx - 1]) (Just 0) where
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
  getRecCalls :: Context -> [Subdata] -> Maybe Int -> Term -> [RecCall]
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
    Lam _ name ta b -> getRecCalls (Hypothesis name ta Nothing : ctx) ((maybe Other Seed argc) : subs) (fmap (+1) argc) b
    Pi _ name ta tb -> getRecCalls (Hypothesis name ta Nothing : ctx) (Other : subs) Nothing tb
    Let name ta a b -> getRecCalls (Hypothesis name ta (Just a) : ctx) (Other : subs) Nothing b
    Case distinct -> let
      (obj_id,defno) = elimType distinct
      
      block = fromJust (Data.Map.lookup obj_id (globalInd glob))
      
      def = block !! defno
      
      unrollProduct (Pi _ _ _ tb) = 1 + unrollProduct tb
      unrollProduct _ = 0
      
      paramno = unrollProduct (indSort def)
      
      ctor_arities = fmap (\x -> unrollProduct x - paramno) (introRules def)
      
      elimineeIsSeed = isSeed ctx subs (eliminee distinct)
      
      unrollArgs :: Context -> [Subdata] -> Int -> Term -> [RecCall]
      unrollArgs ctx subs 0 branch = getRecCalls ctx subs argc branch
      unrollArgs ctx subs m (Lam _ name ta b) = let
        cont sub = unrollArgs (Hypothesis name ta Nothing : ctx) (sub : subs) (m - 1) b
        in case elimineeIsSeed of
          Nothing -> cont Other
          Just k ->
            if returnsInductive ctx ta
            then cont (Sub k)
            else cont Other
      
      in concat (zipWith (unrollArgs ctx subs) ctor_arities (branches distinct))
    _ -> []


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
      in Data.List.foldr (<|>) Control.Applicative.empty (fmap pick allowed)
  
  in solve 0 []