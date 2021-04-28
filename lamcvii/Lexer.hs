module Lexer where

import Control.Applicative
import Data.Char
import Data.Either
import Control.Monad
import Data.Foldable (asum)
import Data.Array.Unboxed

puncts = [
  ">>",  "<<",  "==", "=>", "!=", "<=" , ">=", "->" , "-o", "+" , "-" ,
  "*"  , "/\\", "/" ,  "%" , "&" , "|"  , "^" ,  "=" , "()", "(" , ")" ,
  "["  , "]", "{", "}", "_",
  "<"  ,  ">" , "!" , ";" , "\\" ,  ".", ":", ","]

keywords = [
  "module",
  "import",
  "var",
  "data",
  "def",
  "and",
  "let",
  "in",
  "match",
  "match0",
  "match1",
  "return",
  "with",
  "fun", 
  "Pi", 
  "Type"]

data Cursor = Cursor {
  cursorIndex :: Int,
  cursorBegin :: Int,
  line        :: Int,
  col         :: Int}

data Token
  = Symbol String
  | Number Int
  | Pct    String
  | Str    [Int]
  deriving (Eq)

data Loc = Loc {
  fileName  :: String,
  charray   :: Charray,
  lineBegin :: Int,
  startLine :: Int,
  startCol  :: Int,
  endLine   :: Int,
  endCol    :: Int}

type ParseError = String
type Filename = String
type Charray = UArray Int Char

newtype Parser a = Parser {parse :: Filename -> Charray -> Cursor -> Either ParseError (a,Cursor)}

instance Show Token where
  show (Symbol s) = s 
  show (Number n) = show n
  show (Pct    p) = p
  show (Str  str) = chr <$> str

instance Functor Parser where
  fmap f (Parser p) = Parser $ \src arr c -> do
    (r,c) <- p src arr c
    pure (f r, c)

instance Applicative Parser where
  pure x = Parser $ \_ _ c -> pure (x, c)
  Parser f <*> Parser x = Parser $ \src arr c -> do
    (r1, c1) <- f src arr c
    (r2, c2) <- x src arr c1
    pure (r1 r2, c2)

instance Alternative Parser where
  empty = Parser $ \_ _ _ -> Left ""
  Parser a <|> Parser b = Parser $ \src arr c ->
    case a src arr c of
      Left _ -> b src arr c
      x      -> x

instance Monad Parser where
  return = pure
  Parser x >>= f = Parser $ \src arr c -> do
    (r1, c1) <- x src arr c
    parse (f r1) src arr c1

len :: Charray -> Int
len = (+1) . snd . bounds

instance Show Loc where
  show (Loc {
    fileName  = src,
    charray   = arr,
    lineBegin = lineBegin,
    startCol  = startCol,
    startLine = startLine,
    endCol    = endCol,
    endLine   = endLine}) =
    let
      break i = if i >= len arr then ("",i) else
                let x = arr ! i in
                if x == '\n' then ("",i+1) else
                let (xs,j) = break (i + 1) in (x:xs,j)

      eatLines n i = if n <= 0 then "" else let
        (first,rest) = break i
        in first ++ "\n" ++ eatLines (n - 1) rest

      (first,rest) = break lineBegin
      
      header = src ++ ":" ++ show startLine ++ ":" ++ show startCol ++ ":\n"
      underline = replicate startCol ' ' ++ replicate (endCol - startCol) '^' ++ "\n"
      upline = replicate startCol '_' ++ "^\n"
      downline = replicate endCol   '_' ++ "^\n"
      middle = eatLines (endLine - startLine) rest
      multiline =  upline ++ middle ++ downline
    in header ++ first ++ "\n" ++ (if startLine == endLine then underline else multiline)

makeLoc :: Cursor -> Cursor -> Parser Loc
makeLoc x y = Parser (\src arr c -> Right (Loc {
  fileName  = src,
  charray   = arr,
  lineBegin = cursorBegin x,
  startCol  = col x,
  startLine = line x,
  endCol    = col y,
  endLine   = line y}, c))

err :: Loc -> String -> String -> Parser a
err span msg e = Parser $ \_ _ c -> Left $
  show span ++ "\nexpected " ++ msg ++ ", but got: \'" ++ e ++ "\'"

err2 span msg = Parser $ \_ _ c -> Left $
  show span ++ msg

eof :: Parser Token
eof = Parser $ \src arr c ->
    if cursorIndex c >= len arr then pure (Pct "", c) else Left ""

getCursor :: Parser Cursor
getCursor = Parser $ \src arr c -> pure (c,c)

char :: Parser Char
char = Parser $ \src arr c ->
  if cursorIndex c >= len arr then
    Left $ src ++ ": Unexpected end of input"
  else
    let
      x = arr ! cursorIndex c
      c' = if x == '\n' then Cursor {
          cursorIndex = cursorIndex c + 1,
          cursorBegin = cursorIndex c + 1,
          col         = 0,
          line        = line c + 1}
        else Cursor {
          cursorIndex = cursorIndex c + 1,
          cursorBegin = cursorBegin c,
          col         = col c + 1,
          line        = line c}
    in pure (x,c')

peek :: Parser a -> Parser a
peek (Parser p) = Parser $ \src arr c -> do
  (r,_) <- p src arr c
  pure (r,c)

parseIf :: (Char -> Bool) -> Parser Char
parseIf f = do
  x <- char
  guard (f x)
  pure x
  
spanned :: Parser a -> Parser (Loc,a)
spanned p = do
  ws
  begin <- getCursor
  item  <- p
  end   <- getCursor
  span  <- makeLoc begin end
  pure (span, item)

string :: String -> Parser String
string = sequence . map (parseIf . (==))

ws = comment *> ws <|> parseIf isSpace *> ws <|> pure () where
  comment = string "(*" *> rest
  rest    = string "*)" <|> comment *> rest <|> char *> rest

ident = (:) <$> parseIf (\x -> x == '_'|| isAlpha x)
  <*> many (parseIf (\x -> x == '_'|| isAlphaNum x))

number = Number . read <$> some (parseIf isDigit)

symbol = f <$> ident where
  f s | elem s keywords = Pct s
      | otherwise       = Symbol s

punct = Pct <$> asum (string <$> puncts)

codepoint n = foldr (\x acc -> 16 * acc + digitToInt x) 0
  <$> sequence (replicate n (parseIf isHexDigit))

charLiteral = char *> (Number <$> regular) <* (spanned char >>= quote) where
  quote (_, '\'') = pure ()
  quote (span, _) = err2 span "error: expected ' after character literal"

  regular = do
    (span,x) <- spanned char
    case x of
      '\'' -> err2 span "error: character literals may not be empty"
      '\\' -> do
        (span,x) <- spanned char
        case x of
          '\\' -> pure $ ord '\\'
          '\'' -> pure $ ord '\''
          'n'  -> pure $ ord '\n'
          't'  -> pure $ ord '\t'
          'x'  -> codepoint 2
          'u'  -> codepoint 4
          'U'  -> codepoint 8
          _    -> err2 span "invalid escape sequence\n"
      x -> pure $ ord x

stringLiteral = char *> (Str <$> elements) where
  rest x = (:) <$> x <*> elements
  elements = do
    next <- char
    case next of
      '"'  -> pure []
      '\\' -> do
        (span,x) <- spanned char
        case x of
          '\\' -> rest $ pure $ ord '\\'
          '"'  -> rest $ pure $ ord '"' 
          'n'  -> rest $ pure $ ord '\n'
          't'  -> rest $ pure $ ord '\t'
          'x'  -> rest $ codepoint 2
          'u'  -> rest $ codepoint 4
          'U'  -> rest $ codepoint 8
          _    -> err2 span "invalid escape sequence\n"
      x -> rest $ pure $ ord x

token = ws *> (eof <|> (peek char >>= f)) where
  f '"'   = stringLiteral
  f '\''  = charLiteral
  f _     = number <|> symbol <|> punct <|> badChar
  badChar = fst <$> spanned char >>= flip err2 "unexpected character\n"

expectSymbol :: String -> Parser String
expectSymbol msg = spanned token >>= f where
  f (_,Symbol s) = pure s
  f (span,e)     = err span msg (show e)

expect :: String -> String -> Parser String
expect x msg = spanned token >>= f where
  f (_, Pct y)
    | x == y = pure y
  f (span,e) = err span msg (show e)