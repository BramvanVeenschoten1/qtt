module Elaborator where

import Core as C

import Prelude hiding (lookup)
import Data.List hiding (lookup, insert)
import Control.Monad
import Control.Applicative hiding (Const)
import Data.Functor
import Data.Map
import Data.Either
import Data.Maybe

import Lexer(Loc)
import Normalization
import Substitution
import Typechecker
import Multiplicity
import Parser
import Core(Term(..), Context)

data Error
  -- namespace errors, always fatal
  = Msg String
  | NameAlreadyDefined QName Loc
  | NoSuitableDefinition Name Loc
  | Ambiguity Name Loc [QName]
  | UnboundVar Loc
  -- totality
  | Nonterminating [Loc]
  | Nonpositive [Loc]
  -- fatal type errors
  | SynthLambda Loc
  | SynthMatch Loc
  | SynthParam Loc
  -- ambiguous type errors
  | ExpectedFunction Loc Term
  | InvalidSort Term
  | ExpectedInductive Term
  | InvalidConstructor Binder C.Reference
  | MissingCase Loc C.Reference
  | ConstructorArity Loc C.Reference
  | InconvertibleTypes Loc Context Term Term
  -- multiplicity errors, always ambiguous
  | Unused Loc -- linear variable is unused
  | RelevantUse Loc -- erased argument used relevantly
  | MultipleUse Loc -- linear variable already used once
  | UnrestrictedUse Loc -- linear variable in unrestricted context
  | IntersectUse Loc -- linear variable is used inconsistently across match arms

err msg = TypeError (Msg msg)

data Result a
  = Clear a
  | TypeError Error
  | Ambiguous Name Loc [(QName, Result a)]

instance Functor Result where
  fmap f (TypeError err) = TypeError err
  fmap f (Clear x) = Clear (f x)
  fmap f (Ambiguous n i xs) = Ambiguous n i (fmap (\(n,x) -> (n,fmap f x)) xs)

instance Applicative Result where
  pure = Clear
  
  (TypeError err) <*> x = TypeError err
  (Clear f) <*> x = fmap f x
  (Ambiguous n i fs) <*> x = Ambiguous n i (fmap (\(n,f) -> (n, f <*> x)) fs)
  
instance Alternative Result where
  empty = TypeError (error "empty result")
  
  TypeError _ <|> x = x
  x <|> _ = x
  
instance Monad Result where
  return = pure
  
  TypeError err  >>= f = TypeError err
  Clear x        >>= f = f x
  Ambiguous n i xs >>= f = Ambiguous n i (fmap (\(n,x) -> (n, x >>= f)) xs)

compress :: Result a -> Result a
compress (Ambiguous n i xs) = g (Data.List.foldr f [] xs) where
  f (n,x) acc = case compress x of
    TypeError _ -> acc
    x -> (n,x) : acc

  g [] = TypeError (NoSuitableDefinition n i)
  g [(_,x)] = x
  g xs = Ambiguous n i xs
compress x = x

disambiguate :: Result a -> Either Error a
disambiguate result = case compress result of
  Clear x -> Right x
  TypeError err -> Left err
  Ambiguous n i xs -> Left (Ambiguity n i (fmap fst xs))

data GlobalState = GlobalState {
  newName       :: Int,
  symbolTable   :: Map Name [QName],
  qsymbolTable  :: Map QName (Loc, C.Reference),
  globalObjects :: C.Globals}

type Elab a = Result a