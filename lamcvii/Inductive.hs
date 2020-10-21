module Inductive where

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

assert :: Bool -> String -> Either Error ()
assert True _ = pure ()
assert False msg = Left (Msg msg)

allOccurrencesPositive :: Objects -> Context -> Loc -> Int -> Int -> Int -> Int -> Int -> Term -> Either Error ()
allOccurrencesPositive glob ctx loc defcount defno paramno n nn t = f (whd glob ctx t) where
  f (Pi _ name ta tb) = do
    let ctx' = Hypothesis name ta Nothing : ctx
    
    if doesNotOccur ctx' 0 0 tb
    then strictlyPositive glob ctx loc n nn ta
    else assert (doesNotOccur ctx n nn ta) (show loc ++ "Recursive arguments may not be depended upon")
         
    allOccurrencesPositive glob ctx' loc defcount defno paramno (n+1)(nn+1) tb
  f tb = let
    depth = length ctx
    
    tb' = App
      (Var (depth - defno - 1))
      (fmap (\n -> Var (depth - defcount - paramno + n))
        (reverse [0 .. paramno - 1]))

    in assert (Normalization.sub glob ctx True tb tb')
              (show loc ++
                 showContext ctx ++
                 "\nexpected constructor return type:\n" ++
                 showTerm ctx tb' ++
                 "\nbut got:\n" ++
                 showTerm ctx tb)

strictlyPositive :: Objects -> Context -> Loc -> Int -> Int -> Term -> Either Error ()
strictlyPositive glob ctx loc n nn t = f (whd glob ctx t) where
  f t | doesNotOccur ctx n nn t = pure ()
  f (Pi _ name ta tb) = do
    assert (doesNotOccur ctx n nn ta)
           (show loc ++ "Recursive occurrence in negative position")
  
    strictlyPositive glob (Hypothesis name ta Nothing : ctx) loc (n+1) (nn+1) tb
  f (App (Const _ (IndRef obj_id _ uniparamno)) args) = do
    let (left_params,right_params) = Data.List.splitAt uniparamno args
        block = fromJust (Data.Map.lookup obj_id (globalInd glob))
        ctors = concat (fmap introRules block)
        ctors' = fmap (\(_,_,ty) -> instantiateCtor left_params ty) ctors

    assert (all (doesNotOccur ctx n nn) right_params)
           (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")
    
    mapM_ (weaklyPositive glob ctx loc n nn obj_id) ctors'
  f (App fun args) = 
    assert (all (doesNotOccur ctx n nn) args)
           (show loc ++ "Cannot determine strict positivity of recursive occurrence in function call")
  f (Var n) = pure ()
  f _ = Left (Msg (show loc ++ "Strict positivity check wildcard error"))

{- 
   why does matita:
   - disallow nesting in mutual types?
   - disallow deeper levels of nesting?
   - add the inspected type to the context?
   => we'll ignore these
-}
weaklyPositive :: Objects -> Context -> Loc -> Int -> Int -> Int -> Term -> Either Error ()
weaklyPositive glob ctx loc n nn block_no t = f ctx n nn (substWithDummy block_no t) where
  f :: Context -> Int -> Int -> Term -> Either Error ()
  f ctx n nn te = case whd glob ctx te of
    Box -> pure ()
    App Box args ->
      assert (all (doesNotOccur ctx n nn) args)
             (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")
    Pi _ name ta tb -> do
      let ctx' = Hypothesis name ta Nothing : ctx
      f ctx' (n+1) (nn+1) tb
      if doesNotOccur ctx' 0 0 tb
      then strictlyPositive glob ctx loc n nn ta
      else  assert (doesNotOccur ctx n nn ta)
                   (show loc ++ "Recursive occurrence in negative position")

doesNotOccur :: Context -> Int -> Int -> Term -> Bool
doesNotOccur ctx n nn t = f 0 t True where
  f _ _ False = False
  f k (Var m) _
    | m >= n + k && m <= nn + k = False
    | m < k && m > nn + k = True
    | otherwise = case nth (m - k) ctx >>= hypDef of
      Just bo -> f 0 (lift (m - k) bo) True
      Nothing -> True
  f k t _ = Iterator.fold (const (+1)) k f t True