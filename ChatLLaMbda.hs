import Data.Char
import Data.List (intercalate)
import System.IO
import Control.Exception

import LTypes
import LExp
import Deriv
import qualified Lambek

import Parser
import PySupport

-- Make it easier to look up words in the lexicon:
-- "standardize" the capitalization of a word: make the first letter uppercase and the following letters lowercase.
stdize :: String -> String
stdize []       = []
stdize (c:cs)   = toUpper c : map toLower cs

-- how many readings we print before summarising
maxShown :: Int
maxShown = 6

-- read-eval-print-loop.  The last argument remembers the derivations of the previous sentence so that ":tree" can print them.
repl :: Lexicon PythonCode -> PythonHandle -> [Deriv] -> IO ()
repl elx phandle lastDerivs = do
  putStr "> "
  line <- getLine
  case words line of
    []                  -> repl elx phandle lastDerivs
    [":quit"]           -> putStrLn "Bye."
    [":help"]           -> help >> repl elx phandle lastDerivs
    [":tree"]           -> trees lastDerivs >> repl elx phandle lastDerivs
    [":lexicon"]        -> showLexicon elx >> repl elx phandle lastDerivs
    ws'                 -> do
      derivs <- answer elx ws' (map stdize ws')
      repl elx phandle derivs

-- Report on one sentence, returning its derivations for a later ":tree". We keep the words as typed, as well as the standardized 
-- ones, so that messages quote the user.
answer :: Lexicon PythonCode -> [String] -> [String] -> IO [Deriv]
answer elx orig ws = do
  let ps     = Lambek.parses elx ws
      derivs = map Lambek.pDeriv ps
      terms  = Lambek.readings elx ws
  if null terms
    then do
      putStrLn "That is not a well-formed sentence."
      explain elx orig ws
      return []
    else do
      case terms of
        [_] -> putStrLn "I can derive your sentence as follows:"
        _   -> putStrLn ("That sentence is ambiguous (" ++ show (length terms)
                         ++ " readings):")
      mapM_ (putStrLn . ("   " ++) . prettyLExp) (take maxShown terms)
      if length terms > maxShown
        then putStrLn ("   ... and " ++ show (length terms - maxShown) ++ " more")
        else return ()
      return derivs

-- say something useful about why a sentence was rejected
explain :: Lexicon PythonCode -> [String] -> [String] -> IO ()
explain elx orig ws =
  case Lambek.unknownWords elx ws of
    (u:us) -> putStrLn ("   I do not know the word(s): " ++ intercalate ", " (u:us))
    []     ->
      case length (Lambek.longestGoodPrefix elx ws) of
        0 -> putStrLn "   None of it parses as a sentence."
        n -> putStrLn ("   I got as far as \"" ++ unwords (take n orig)
                       ++ "\"; the rest does not fit.")

-- print the proof trees of the previous sentence
trees :: [Deriv] -> IO ()
trees [] = putStrLn "No derivations to show yet."
trees ds = sequence_
  [ do putStrLn ("Derivation " ++ show i ++ " of " ++ show (length ds) ++ ":")
       printDeriv d
       putStrLn ("   as a lambda expression: " ++ prettyLExp (toLExp d))
       putStrLn ""
  | (i,d) <- zip [1 :: Int ..] (take maxShown ds) ]

showLexicon :: Lexicon PythonCode -> IO ()
showLexicon elx = do
  putStrLn ("Sentence type: " ++ showLTp (stp elx))
  sequence_ [ putStrLn ("   " ++ w ++ " : " ++ showLTp t) | (w,t,_) <- items elx ]

help :: IO ()
help = mapM_ putStrLn
  [ "Type a sentence, or one of:"
  , "   :tree      show the proof trees of the last sentence"
  , "   :lexicon   list the words I know"
  , "   :help      this message"
  , "   :quit      stop"
  ]

main :: IO ()
main = do
  -- send console output immediately to the user
  hSetBuffering stdout NoBuffering
  -- input a lexicon file
  elx <- getLex
  -- input a database of facts
  db <- getDB
  -- launch a Python interpreter
  phandle <- launchPython db
  -- start the read-eval-print loop
  putStrLn "Starting chat...  (:help for commands)"
  repl elx phandle []
  where
    getDB :: IO PythonCode
    getDB = do
      putStr "Facts about the world: "
      dname <- getLine
      mdb <- try (readFile dname) :: IO (Either IOError String)
      case mdb of
        Left err -> putStrLn ("Error loading file " ++ show err) >> getDB
        Right db -> return (PCode db)

    getLex :: IO (Lexicon PythonCode)
    getLex = do
      putStr "Lexicon file: "
      lname <- getLine
      res <- parseFile lexicon lname
      case res of
        Left err -> putStrLn ("Error loading file " ++ show err) >> getLex
        Right (Left err) -> putStrLn ("parse error at " ++ lname ++ ":" ++ show err) >> getLex
        Right (Right lex) -> return lex
