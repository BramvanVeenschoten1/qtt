module Parser where

import Lexer
import Control.Applicative
import Data.List
import Data.Function
import Data.Array.Unboxed
import Multiplicity
  
type Name = String
type QName = [String]

data Binder = Binder {binderSpan :: Maybe Span, binderName :: Name}

instance Eq Binder where
  (==) = on (==) binderName

instance Ord Binder where
  compare = on compare binderName

instance Show Binder where
  show = binderName

type Param = (Mult,Binder, Maybe Expr)

type CParam = (Mult, Maybe Binder, Expr)

type Ctor = (Binder, [CParam])

type Inductive = (Info, Binder, [Param], [Ctor])

type Function = (Info, Binder, Expr, Expr)

type Info = Maybe Span

type Module = [Decl]

data Decl 
  = Inductive [Inductive]
  | Fixpoint [Function]
  | Constant Info Binder (Maybe Expr) Expr
  | Postulate Info Binder Expr

data Expr 
  = EHole   Info Int
  | EType   Info Int
  | EVar    Info Name
  | EApply  Info Expr Expr
  | ELet    Info Binder (Maybe Expr) Expr Expr
  | ELambda Info Mult Binder (Maybe Expr) Expr
  | EPi     Info Mult (Maybe Binder) Expr Expr
  | ELetRec Info [Function] Expr
  | EMatch  Info Expr [(Binder,[Binder],Expr)]
 
showCases = foldr (\(ctor,args,expr) -> (++) (" | " ++ show ctor ++ " " ++ show args ++ " -> " ++ show expr)) ""
showAnnot = maybe "" ((++) " : " . show)
showBindings = foldr (\(_,v,ta,a) -> (++) (show v ++ " : " ++ show ta ++ " = " ++ show a ++ "; ")) ""

instance Show Expr where
  show (EHole _ x)              = "_"
  show (EType _ _)              = "Type"
  show (EVar _ x)               = x
  show (EApply _ l r)           = "(" ++ show l ++ " " ++ show r ++ ")"
  show (ELet _ v ta a b)        = "let " ++ show v ++ showAnnot ta ++ " = " ++ show a ++ " in " ++ show b
  show (ELambda _ m v ta b)     = "fun" ++ show m ++ " " ++ show v ++ showAnnot ta ++ " -> " ++ show b ++ "]"
  show (EPi _ m (Just v) ta tb) = "Pi " ++ show m ++ " " ++ show v ++ " : " ++ show ta ++ ", " ++ show tb
  show (EPi _ m Nothing ta tb)  = "(" ++ show ta ++ showArrow m ++ show tb ++ ")"    
  show (ELetRec _ b e)          = "let rec " ++ showBindings b ++ " in " ++ show e
  show (EMatch _ s cases)       = "match " ++ show s ++ " with" ++ showCases cases

showArrow Zero = " => "
showArrow One  = " -o "
showArrow Many = " -> "

exprInfo (EType s _) = s
exprInfo (EHole s _) = s
exprInfo (EVar s _) = s
exprInfo (EApply s _ _) = s
exprInfo (ELambda s _ _ _ _) = s
exprInfo (ELet s _ _ _ _) = s
exprInfo (EPi s _ _ _ _) = s
exprInfo (ELetRec s _ _) = s
exprInfo (EMatch s _ _) = s

mkBinder :: (Span,String) -> Binder
mkBinder (s,xs) = Binder (Just s) xs

primary = do
  ws
  begin <- getCursor
  (span, t) <- spanned token
  let s = Just span
  case t of
    Symbol x    -> pure (EVar s x)
    Pct "_"     -> pure (EHole s undefined)
    Pct "Type"  -> pure (EType s 0)
    Pct "Pi"    -> quant begin
    Pct "match" -> match begin
    Pct "fun"   -> lam begin
    Pct "("     -> expr <* expect ")" "closing ')' after expression"
    x           -> err span "some expression" (show x)

mult :: Parser Mult
mult = do
  t <- peek token
  case t of
    Number 0 -> token *> pure Zero
    Number 1 -> token *> pure One
    _        ->          pure Many

param :: Parser Param
param = do
  (span,t) <- spanned token
  case t of
    Symbol x -> pure (Many, mkBinder (span, x), Nothing)
    Pct "(" -> do
      m <- mult
      b <- mkBinder <$> spanned (expectSymbol "name in parameter list")
      t <- peek token
      ty <- (case t of
        Pct ":" -> do
          token
          Just <$> expr
        _ -> pure Nothing)
      expect ")" "closing ')' after parameter"
      pure (m,b,ty)        
      
params :: Parser [Param]
params = do
  t <- peek token
  case t of
    Symbol _ -> someParams 
    Pct "(" -> someParams
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (:) <$> param <*> params

lam :: Cursor -> Parser Expr
lam begin = do
  ps <- someParams
  expect "->" "'->' after params in lambda expression"
  body <- expr
  end <- getCursor
  let f (m,v,ta) = ELambda (Just (makeSpan begin end)) m v ta
  pure (foldr f body ps)

quant :: Cursor -> Parser Expr
quant begin = do
  m <- mult
  v <- mkBinder <$> spanned (expectSymbol "parameter in dependent product type")
  expect ":" "':' after variable in dependent product type"
  ta <- expr
  expect "," "',' after binder in dependent product type"
  tb <- expr
  end <- getCursor
  pure (EPi (Just (makeSpan begin end)) m (Just v) ta tb)

pattern :: Parser (Binder,[Binder])
pattern = (,) <$> ctor <*> many args where
  ctor = mkBinder <$> spanned (expectSymbol "constructor in match arm")
  args = do
    (span,t) <- spanned token
    case t of
      Pct "_"  -> pure (mkBinder (span, "_"))
      Symbol x -> pure (mkBinder (span, x))
      x -> err span "some variable or wildcard" (show x)

match :: Cursor -> Parser Expr
match begin = do
  scrutinee <- expr
  expect "with" "'with' after scrutinee in match-expression"
  a <- arms
  end <- getCursor
  pure (EMatch (Just (makeSpan begin end)) scrutinee a)
  where
    arms = do
      t <- peek token
      case t of
        Pct "|" -> token *> arm
        _       -> pure []
    arm = do
      (ctor,args) <- pattern
      expect "->" "'->' after pattern in match-arm"
      e <- expr
      xs <- arms
      pure ((ctor,args,e):xs)

app :: Parser Expr
app = g <$> (ws *> getCursor) <*> primary <*> args where
  args = do
    t <- peek token
    case t of
      Symbol _    -> f
      Pct "Pi"    -> f
      Pct "fun"   -> f
      Pct "match" -> f
      Pct "_"     -> f
      Pct "("     -> f
      _           -> pure []

  f :: Parser [(Expr,Cursor)]
  f = (:) <$> ((,) <$> primary <*> getCursor) <*> args

  g _ x [] = x
  g begin x ((y,end):ys) = g begin (EApply (Just (makeSpan begin end)) x y) ys

lett :: Cursor -> Parser Expr
lett begin = do
  t <- peek token
  case t of
    Pct "rec" -> token *> letrec begin
    _ -> nonrec begin

unfoldParams :: [Param] -> (Maybe Expr, Expr) -> (Maybe Expr, Expr)
unfoldParams [] x = x
unfoldParams ((m, v, t) : ps) x = let
  (ty', body') = unfoldParams ps x
  
  ty'' = EPi Nothing m (Just v) <$> t <*> ty'
  body'' = ELambda Nothing m v t body'
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
  
nonrec :: Cursor -> Parser Expr
nonrec begin = do
  (v,t,b) <- letBinding
  expect "in" "'in' after binding in let-expression"
  e <- expr
  end <- getCursor
  pure (ELet (Just (makeSpan begin end)) v t b e)

letrec :: Cursor -> Parser Expr
letrec begin = do
  funs <- bindings
  expect "in" "'in' after bindings in let rec expresssion"
  e <- expr
  end <- getCursor
  pure (ELetRec (Just (makeSpan begin end)) funs e)

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
        return (EPi (Just (makeSpan begin end)) m Nothing lhs rhs)

expr :: Parser Expr
expr = arrow

bindings :: Parser [Function]
bindings = do
  (span,(v,t,b)) <- spanned letBinding
  t' <- (case t of
    Nothing -> err2 span "recursive bindings must have type annotations"
    Just t -> pure t)
  let bind = (Just span, v, t', b) 
  t <- peek token
  case t of
    Pct "and" -> (:) bind <$> (token *> bindings)
    _ -> pure [bind]

recDecl :: Parser Decl
recDecl = do
  binds <- bindings
  pure (Fixpoint binds)

nonRecDecl :: Cursor -> Parser Decl
nonRecDecl begin = do
  (v,t,b) <- letBinding
  end <- getCursor
  pure (Constant (Just (makeSpan begin end)) v t b)

decl :: Cursor -> Parser Decl
decl begin = do
  t <- peek token
  case t of
    Pct "rec" -> token *> recDecl
    _ -> nonRecDecl begin

ctorParam :: Parser CParam
ctorParam = f <|> g <|> h where
  f = do
    (span,v) <- spanned (expectSymbol "")
    pure (Many, Nothing, EVar (Just span) v)
  g = do
    expect "(" ""
    m <- mult
    v <- mkBinder <$> spanned (expectSymbol "")
    expect ":" ""
    e <- expr
    expect ")" ""
    pure (m,Just v, e)
  h = do
    expect "(" ""
    m <- mult
    e <- expr
    expect ")" "closing ')' after parameter"
    pure (m,Nothing,e)

ctorParams :: Parser [CParam]
ctorParams = do
  t <- peek token
  case t of
    Pct "(" -> someParams
    Symbol _ -> someParams
    _ -> pure []
    where
      someParams = (:) <$> ctorParam <*> ctorParams

constructors :: Parser [Ctor]
constructors = do
  t <- peek token
  case t of
    Pct "|" -> do
      token
      name <- mkBinder <$> spanned (expectSymbol "name in constructor definition")
      ps <- ctorParams
      ctors <- constructors
      pure ((name, ps) : ctors)
    _ -> pure []

inductive :: Cursor -> Parser [Inductive]
inductive begin = do
  name <- mkBinder <$> spanned (expectSymbol "name in inductive definition")
  ps <- params
  expect "=" "'=' after parameters in inductive definition"
  ctors <- constructors
  end <- getCursor
  let res = (Just (makeSpan begin end), name, ps, ctors)
  ws
  begin <- getCursor
  t <- peek token
  case t of
    Pct "and" -> (:) res <$> inductive begin
    _ -> pure [res]

post :: Cursor -> Parser Decl
post begin = do
  name <- mkBinder <$> spanned (expectSymbol "name after 'val' keyword in postulate")
  expect ":" "':' after name in postulate"
  ty <- expr
  end <- getCursor
  pure (Postulate (Just (makeSpan begin end)) name ty)

parseModule :: Parser Module
parseModule = do
  ws
  begin <- getCursor
  (span,t) <- spanned token
  case t of
    Pct ""     -> pure []
    Pct "let"  -> f (decl begin)
    Pct "val"  -> f (post begin)
    Pct "type" -> f (Inductive <$> inductive begin)
    x -> err span "some declaration" (show x)
    where f p = (:) <$> p <*> parseModule

parse :: Filename -> String -> Either ParseError Module
parse name input = fst <$> Lexer.parse parseModule name (listArray (0,length input - 1) input) (Cursor 0 0 0 0)
