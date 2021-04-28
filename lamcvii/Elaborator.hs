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
import Substitution
import Multiplicity
import Parser
import Core(Term(..), Context)

err = TypeError

type Error = String

type NameSpace = (Map Name [QName], Map QName (Loc, C.Reference))

type GlobalNames = Map Name NameSpace

mergeNameSpace :: NameSpace -> NameSpace -> NameSpace
mergeNameSpace (n0,q0) (n1,q1) = (Data.Map.unionWith (++) n0 n1, Data.Map.union q0 q1)

emptyNameSpace :: NameSpace
emptyNameSpace = (Data.Map.empty,Data.Map.empty)

emptyObjects = C.Objects Data.Map.empty Data.Map.empty Data.Map.empty Data.Map.empty

lookupQName :: QName -> ElabState -> Maybe (Loc,C.Reference)
lookupQName qname glob = lookup qname (Data.Map.union (snd (internalNames glob)) (snd (importedNames glob)))

lookupName :: Name -> ElabState -> Maybe [QName]
lookupName name glob = lookup name (unionWith (++) (fst (importedNames glob)) (fst (internalNames glob)))

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
  
  TypeError err <*> x = TypeError err
  Clear f <*> x = fmap f x
  Ambiguous n i fs <*> x = Ambiguous n i (fmap (\(n,f) -> (n, f <*> x)) fs)
  
instance Alternative Result where
  empty = TypeError (error "empty result")
  
  TypeError _ <|> x = x
  x <|> _ = x
  
instance Monad Result where
  return = pure
  
  TypeError err    >>= f = TypeError err
  Clear x          >>= f = f x
  Ambiguous n i xs >>= f = Ambiguous n i (fmap (\(n,x) -> (n, x >>= f)) xs)

compress :: Result a -> Result a
compress (Ambiguous n i xs) = g (Data.List.foldr f [] xs) where
  f (n,x) acc = case compress x of
    TypeError _ -> acc
    x -> (n,x) : acc

  g [] = TypeError (show i ++ "no suitable definition for " ++ n)
  g [(_,x)] = x
  g xs = Ambiguous n i xs
compress x = x

disambiguate :: Result a -> Either Error a
disambiguate result = case compress result of
  Clear x -> Right x
  TypeError err -> Left err
  Ambiguous n i xs -> Left (show i ++ "ambiguous name: " ++ n)

data ElabState = ElabState {
  newName       :: Int,
  moduleName    :: Name,
  importedNames :: NameSpace,
  internalNames :: NameSpace,
  globalObjects :: C.Objects}

type Elab a = Result a