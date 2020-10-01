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
import Typechecker
import Multiplicity
import Lexer(Loc)
import Prettyprint

allOccurrencesPositive :: Objects -> Context -> Loc -> Int -> Int -> Int -> Int -> Int -> Term -> Either Error ()
allOccurrencesPositive glob ctx loc defcount defno paramno n nn t = f (whd glob ctx t) where
  f (Pi _ name ta tb) = do
    let ctx' = Hypothesis name ta Nothing : ctx
    if doesNotOccur ctx' 0 0 tb
    then strictlyPositive glob ctx loc n nn ta
    else if doesNotOccur ctx n nn ta
         then pure ()
         else Left (Msg (show loc ++ "1 Non-strictly positive occurrence in inductive definition"))
    allOccurrencesPositive glob ctx' loc defcount defno paramno (n+1)(nn+1) tb
  f tb = do
    let depth = length ctx
    
        tb' = App
          (Var (depth - defno - 1))
          (fmap (\n -> Var (depth - defcount - paramno + n))
            (reverse [0 .. paramno - 1])) 

    if Normalization.sub glob ctx True tb tb'
    then pure ()
    else 
      Left (Msg (show loc ++ showContext ctx ++
            "\nexpected constructor return type:\n" ++
            showTerm ctx tb' ++
            "\nbut got:\n" ++
            showTerm ctx tb))

strictlyPositive :: Objects -> Context -> Loc -> Int -> Int -> Term -> Either Error ()
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