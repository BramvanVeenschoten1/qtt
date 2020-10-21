module Parser where

import Lexer
import Control.Applicative
import Data.List
import Data.Function
import Data.Array.Unboxed
import Data.Maybe

-- replace mult by Maybe Int or sumthin
import Core(Mult(..))

type Name = String
type QName = [String]

data Binder = Binder {binderLoc :: Loc, binderName :: Name}

instance Eq Binder where
  (==) = on (==) binderName

instance Ord Binder where
  compare = on compare binderName

instance Show Binder where
  show = binderName

type Param = (Mult,Binder, Maybe Expr)

type Ctor = (Binder, Expr)

type Inductive = (Loc, Binder, [Param], [Ctor])

type Function = (Loc, Binder, Expr, Expr)

type Module = (String,[String],[Decl])

type Branch = (Loc,Binder,[Binder],Expr)

data Decl 
  = Inductive [Inductive]
  | Definition [Function]
  | Postulate Loc Binder Expr

data Expr 
  = EHole   Loc
  | EType   Loc
  | EName   Loc [String]
  | EVar    Loc Name
  | EApply  Loc Expr [Expr]
  | ELet    Loc Binder (Maybe Expr) Expr Expr
  | ELambda Loc Mult Binder (Maybe Expr) Expr
  | EPi     Loc Mult (Maybe Binder) Expr Expr
  | ELetRec Loc [Function] Expr
  | EMatch  Loc Mult Expr (Maybe Expr) [Branch]

showArrow Zero = " => "
showArrow One  = " -o "
showArrow Many = " -> "

exprLoc (EType s) = s
exprLoc (EHole s) = s
exprLoc (EName s _) = s
exprLoc (EVar s _) = s
exprLoc (EApply s _ _) = s
exprLoc (ELambda s _ _ _ _) = s
exprLoc (ELet s _ _ _ _) = s
exprLoc (EPi s _ _ _ _) = s
exprLoc (ELetRec s _ _) = s
exprLoc (EMatch s _ _ _ _) = s

mkBinder :: (Loc,String) -> Binder
mkBinder = uncurry Binder

primary = do
  ws
  begin <- getCursor
  (span, t) <- spanned token
  case t of
    Symbol x     -> qname begin x
    Pct "_"      -> pure (EHole span)
    Pct "Type"   -> pure (EType span)
    Pct "Pi"     -> parseProduct begin
    Pct "match0" -> match Zero begin
    Pct "match1" -> match One  begin
    Pct "match"  -> match Many begin
    Pct "fun"    -> lam begin
    Pct "let"    -> lett begin
    Pct "("      -> expr <* expect ")" "closing ')' after expression"
    x            -> err span "some expression" (show x)

qname :: Cursor -> String -> Parser Expr
qname begin x = do
  t <- peek token
  case t of
    Pct "." -> do
      xs <- tail
      end <- getCursor
      span <- makeLoc begin end
      pure (EName span (x:xs))
    _ -> do
      end <- getCursor
      span <- makeLoc begin end
      pure (EVar span x)
  where
    tail = do
      token
      x <- expectSymbol "symbol after '.' in qualified name"
      t <- peek token
      case t of
        Pct "." -> do
          xs <- tail
          pure (x : xs)
        _ -> pure [x]

mult :: Parser Mult
mult = do
  t <- peek token
  case t of
    Number 0 -> token *> pure Zero
    Number 1 -> token *> pure One
    _        ->          pure Many

annot :: Parser (Maybe Expr)
annot = do
  t <- peek token
  case t of
    Pct ":" -> token *> fmap Just expr
    _ -> pure Nothing

annotParam :: Parser [Param]
annotParam = do
  m <- mult
  bs <- some (mkBinder <$> spanned (expectSymbol "name in parameter list"))
  ty <- annot
  pure (fmap (\b -> (m,b,ty)) bs)

param :: Parser [Param]
param = do
  t <- peek token
  case t of
    Pct "(" -> token *> annotParam <* f ")"
    Pct "{" -> token *> annotParam <* f "}"
    _ -> annotParam
  where f close = expect close ("closing '" ++ close ++ "' after parameter")

params :: Parser [Param]
params = do
  t <- peek token
  case t of
    Symbol _ -> someParams 
    Pct "(" -> someParams
    Pct "{" -> someParams
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (++) <$> param <*> params

lam :: Cursor -> Parser Expr
lam begin = do
  ps <- someParams
  expect "->" "'->' after params in lambda expression"
  body <- expr
  end <- getCursor
  span <- makeLoc begin end
  let f (m,v,ta) = ELambda span m v ta
  pure (foldr f body ps)

parseProduct :: Cursor -> Parser Expr
parseProduct begin = do
  ps <- someParams
  expect "," "',' after params in Pi expression"
  body <- expr
  end <- getCursor
  span <- makeLoc begin end
  if all (\(_,_,ta) -> isJust ta) ps
  then pure ()
  else err2 span "parameters in Pi expressions must have type annotations"
  let f (m,v,Just ta) = EPi span m (Just v) ta
  pure (foldr f body ps)

pattern :: Parser (Binder,[Binder])
pattern = (,) <$> ctor <*> many args where
  ctor = mkBinder <$> spanned (expectSymbol "constructor in match arm")
  args = do
    (span,t) <- spanned token
    case t of
      Pct "_"  -> pure (mkBinder (span, "_"))
      Symbol x -> pure (mkBinder (span, x))
      x -> err span "some variable or wildcard" (show x)

match :: Mult -> Cursor -> Parser Expr
match m begin = do
  scrutinee <- expr
  t <- peek token
  motive <- (case t of
    Pct "return" -> token *> fmap Just expr
    _ -> pure Nothing)
  expect "with" "'with' after scrutinee in match-expression"
  a <- arms
  end <- getCursor
  span <- makeLoc begin end
  pure (EMatch span m scrutinee motive a)
  where
    arms = do
      begin <- getCursor
      t <- peek token
      case t of
        Pct "|" -> token *> arm begin
        _       -> pure []
    arm begin = do
      (ctor,args) <- pattern
      expect "->" "'->' after pattern in match-arm"
      e <- expr
      end <- getCursor
      span <- makeLoc begin end
      xs <- arms
      pure ((span,ctor,args,e):xs)

app :: Parser Expr
app = do
  ws
  begin <- getCursor
  prim <- primary
  borgs <- args
  end <- getCursor
  span <- makeLoc begin end
  if Prelude.null borgs
  then pure prim
  else pure (EApply span prim borgs)
  where
  args = do
    t <- peek token
    case t of
      Symbol _     -> f
      Pct "Pi"     -> f
      Pct "fun"    -> f
      Pct "let"    -> f
      Pct "match"  -> f
      Pct "match0" -> f
      Pct "match1" -> f
      Pct "_"      -> f
      Pct "("      -> f
      _            -> pure []

  f = (:) <$> primary <*> args

unfoldParams :: [Param] -> (Maybe Expr, Expr) -> (Maybe Expr, Expr)
unfoldParams [] x = x
unfoldParams ((m, v, t) : ps) x = let
  span = exprLoc (snd x)

  (ty', body') = unfoldParams ps x
  
  ty'' = EPi span m (Just v) <$> t <*> ty'
  body'' = ELambda span m v t body'
  in (ty'', body'')

letBinding :: Parser (Binder, Maybe Expr, Expr)
letBinding = do
  v <- mkBinder <$> spanned (expectSymbol "variable in let-binding")
  ps <- params
  (span,t) <- spanned token
  let
    f ty = do
      b <- expr
      let (ty', b') = unfoldParams ps (ty, b)
      pure (v, ty', b')
  case t of
    Pct ":" -> expr <* expect "=" "'=' after type in let-binding" >>= (f . Just)
    Pct "=" -> f Nothing
    x -> err span "':' or '='" (show x)
  
lett :: Cursor -> Parser Expr
lett begin = do
  (v,t,b) <- letBinding
  expect "in" "'in' after binding in let-expression"
  e <- expr
  end <- getCursor
  span <- makeLoc begin end
  pure (ELet span v t b e)

arrow :: Parser Expr
arrow = do
  ws
  begin <- getCursor
  lhs   <- app
  t     <- peek token
  case t of
    Pct "=>" -> f begin lhs Zero
    Pct "-o" -> f begin lhs One
    Pct "->" -> f begin lhs Many
    _ -> return lhs
    where
      f begin lhs m = do
        token
        rhs <- arrow
        end <- getCursor
        span <- makeLoc begin end
        return (EPi span m Nothing lhs rhs)

expr :: Parser Expr
expr = arrow

bindings :: Parser [Function]
bindings = do
  (span,(v,t,b)) <- spanned letBinding
  t' <- (case t of
    Nothing -> err2 span "recursive bindings must have type annotations"
    Just t -> pure t)
  let bind = (span, v, t', b) 
  t <- peek token
  case t of
    Pct "and" -> (:) bind <$> (token *> bindings)
    _ -> pure [bind]

constructors :: Parser [Ctor]
constructors = do
  t <- peek token
  case t of
    Pct "|" -> do
      token
      name <- mkBinder <$> spanned (expectSymbol "name in constructor definition")
      expect ":" ": after name in constructor definition"
      ty <- expr
      ctors <- constructors
      pure ((name, ty) : ctors)
    _ -> pure []

inductive :: Cursor -> Parser [Inductive]
inductive begin = do
  name <- mkBinder <$> spanned (expectSymbol "name in inductive definition")
  ps <- params
  ctors <- constructors
  end <- getCursor
  span <- makeLoc begin end
  let res = (span, name, ps, ctors)
  ws
  begin <- getCursor
  t <- peek token
  case t of
    Pct "and" -> (:) res <$> (token *> inductive begin)
    _ -> pure [res]

post :: Cursor -> Parser Decl
post begin = do
  name <- mkBinder <$> spanned (expectSymbol "name after 'var' keyword in postulate")
  expect ":" "':' after name in postulate"
  ty <- expr
  end <- getCursor
  span <- makeLoc begin end
  pure (Postulate span name ty)

parseDecls :: Parser [Decl]
parseDecls = do
  ws
  begin <- getCursor
  (span,t) <- spanned token
  case t of
    Pct ""     -> pure []
    Pct "def"  -> f (Definition <$> bindings)
    Pct "var"  -> f (post begin)
    Pct "data" -> f (Inductive <$> inductive begin)
    x -> err span "some declaration" (show x)
    where f p = (:) <$> p <*> parseDecls

parseImports = do
  t <- peek token
  case t of
    Pct "import" -> do
      token
      name <- expectSymbol "name after 'import'"
      names <- parseImports
      pure (name:names)
    _ -> pure []

parseModule :: Parser Module
parseModule = do
  expect "module" "module name declaration"
  name <- expectSymbol "name after 'module'"
  imports <- parseImports
  decls <- parseDecls
  pure (name,imports,decls)

parse :: Filename -> String -> Either ParseError Module
parse name input = fst <$> Lexer.parse parseModule name (listArray (0,length input - 1) input) (Cursor 0 0 0 0)
