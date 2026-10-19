{-
  Parsing routines based on the principles of "monadic parsing", explained lightly in the comments.

  For additional background on that technique, see Ch.13 of Graham Hutton's
  _Programming in Haskell_, 2nd edition (available in the BCX library), or watch his
  Computerphile video [Functional Parsing](https://www.youtube.com/watch?v=dDtZLm7HIJs).
-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns -Wno-noncanonical-monad-instances #-}

module Parser where

import Data.Char

import Control.Applicative
import System.IO
import Control.Exception

import LTypes
import PySupport

-- We begin by defining the type of parsers for a type, which you may
-- observe is a variation of the state monad.  The idea is to keep track of both
-- the remaining input as well as the current line number in order to
-- produce better error messages.

newtype Parser a = Parser { runParser :: (Int,String) -> Either ParseError (a,Int,String) }

data ParseError = ParseError { errLine :: Int, errRest :: String }

instance Show ParseError where
  show (ParseError errLine errRest) = show errLine ++ ":" ++ take 4 errRest ++
                                      if length errRest > 4 then "..." else ""

-- to use the monadic parsing technique we need to first show that Parser is a Monad...
instance Monad Parser where
  return x = Parser (\(i,s) -> Right (x,i,s))

  p >>= f  = Parser (\(i,s) -> case runParser p (i,s) of
                                 Left err -> Left err
                                 Right (x,i',s') -> runParser (f x) (i',s'))

-- We also add some boilerplate code to derive Functor and Applicative
-- instances from the Monad instance.
instance Functor Parser where
  fmap f p = p >>= \x -> return (f x)

instance Applicative Parser where
  pure = return
  pf <*> p = pf >>= \f -> p >>= \x -> return (f x)

-- Finally we define an Alternative instance, which makes it convenient
-- to write backtracking parsers.
instance Alternative Parser where
  empty = Parser (\(i,s) -> Left (ParseError i s))

  p1 <|> p2 = Parser (\(i,s) -> case runParser p1 (i,s) of
                                  Right (x,i',s') -> Right (x,i',s')
                                  Left err -> runParser p2 (i,s))

-- Now we can start writing some basic parser combinators.

-- The "next" parser just reads one character of the input and returns
-- it, while keeping track of the current line number.  Note there
-- must be at least one character of input for "next" to succeed.
next :: Parser Char
next = Parser $ \(i,s) -> case s of
                            []     -> Left (ParseError i [])
                            (x:s') -> Right (x,i + if x == '\n' then 1 else 0,s')

-- Dually, the "end" parser detects when we have reached the end of input.
end :: Parser ()
end = Parser $ \(i,s) -> if null s then Right ((),i,"") else Left (ParseError i s)

-- sat p parses a character satisfying the predicate p
sat :: (Char -> Bool) -> Parser Char
sat p = do
  x <- next
  if p x then return x else empty

-- char c just parses the specific character c
char :: Char -> Parser Char
char c = sat (==c)

-- string s just parses the specific string s
string :: String -> Parser String
string []     = return []
string (c:cs) = char c >> string cs >> return (c:cs)

-- list p turns a parser of p's into a parser of lists of p's.  It is
-- defined in mutual recursion with listne p, which builds a parser of
-- non-empty lists of p's.
list, listne :: Parser a -> Parser [a]
list p = listne p <|> pure []
listne p = do
  x <- p
  xs <- list p
  return (x:xs)

-- separatedBy p q is similar, parsing a non-empty list of p's separated by q's
separatedBy :: Parser a -> Parser b -> Parser [a]
separatedBy p q = do
  x <- p
  xs <- list (q >> p)
  return (x:xs)

-- parse some spaces
spaces = list (sat isSpace)

-- parse a newline
newline :: Parser ()
newline = (string "\r\n" <|> string "\n") >> return ()

-- the paren parser combinator turns a parser of something into a
-- parser of something wrapped in parentheses
paren :: Parser a -> Parser a
paren p = do
  char '('
  spaces
  x <- p
  spaces
  char ')'
  return x

-- Using these basic parsers and parser combinators, we now define a
-- parser for extended lexicon files.

-- lexicon words should begin with an uppercase letter follows by a string of lowercase letters
word :: Parser String
word = do
  x <- sat isUpper
  xs <- list (sat isLower)
  return (x:xs)

-- parse a Lambek type
ltp :: Parser LTp
ltp = ltpDiv <|> ltpFactor

ltpFactor = ltpAtm <|> paren ltp

ltpAtm :: Parser LTp
ltpAtm = do
  x <- sat isLower
  xs <- list (sat isAlphaNum)
  return (Atm (x:xs))

ltpDiv = divL <|> divR

divL :: Parser LTp
divL = do
  t1 <- ltpFactor
  spaces
  string "\\"
  spaces
  t2 <- ltp
  return (DivL t1 t2)

divR :: Parser LTp
divR = do
  t1 <- ltpFactor
  spaces
  string "/"
  spaces
  t2 <- ltp
  return (DivR t1 t2)

-- parse a single lexicon item
lex_item :: Parser (String,LTp,PythonCode)
lex_item = do
  spaces
  w <- word
  spaces
  char ':'
  spaces
  t <- ltp
  spaces
  char '='
  spaces
  def <- list (sat (\c -> c/='.' && c/='\n'))
  char '.'
  newline
  return (w,t,PCode def)

-- parse an entire lexicon
lexicon :: Parser (Lexicon PythonCode)
lexicon = do
  string "SENTENCE"
  spaces
  char ':'
  spaces
  s <- ltp
  spaces
  char '.'
  newline
  items <- list lex_item
  list newline
  end
  return (Lexicon items s)

-- call a parser on the contents of a file
parseFile :: Parser a -> FilePath -> IO (Either IOError (Either ParseError a))
parseFile p fname = try $ do
  content <- readFile fname
  case runParser p (1,content) of
    Left err      -> return (Left err)
    Right (x,_,_) -> return (Right x)

