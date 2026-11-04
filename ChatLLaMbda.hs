import Data.List (intercalate, nub)
import System.IO
import Control.Exception

import LTypes
import LExp
import Deriv
import Eval
import Ambiguity
import qualified Lambek

import Parser
import PySupport

-- how many readings we print before summarising
maxShown :: Int
maxShown = 6

-- read-eval-print-loop.  The last argument remembers the derivations of the previous sentence so that ":tree" can print them.
repl :: Lexicon PythonCode -> Laws -> [LTp] -> PythonHandle -> [Deriv] -> IO ()
repl elx laws goals phandle lastDerivs = do
  putStr "> "
  line <- getLine
  case words line of
    []                  -> repl elx laws goals phandle lastDerivs
    [":quit"]           -> putStrLn "Bye."
    [":help"]           -> help >> repl elx laws goals phandle lastDerivs
    [":tree"]           -> trees lastDerivs >> repl elx laws goals phandle lastDerivs
    [":lexicon"]        -> showLexicon elx goals >> repl elx laws goals phandle lastDerivs
    ws'                 -> do
      derivs <- answer elx laws goals phandle ws' (map Lambek.stdize ws')
      repl elx laws goals phandle derivs

-- Report on one sentence, returning its derivations for a later ":tree". We keep the words as typed, as well as the standardized 
-- ones, so that messages quote the user.

-- When several readings agree on an answer we just give the answer; only a disagreement is worth bothering the user with.  Note that agreeing
-- here means agreeing *in this world*, which is weaker than meaning the same thing.

answer :: Lexicon PythonCode -> Laws -> [LTp] -> PythonHandle -> [String] -> [String] -> IO [Deriv]
answer elx laws goals phandle orig ws = do
  -- tried as a declarative first, then as a question
  let ps = Lambek.sensesAny laws text elx goals ws
  if null ps
    then do
      putStrLn "That is not a well-formed sentence."
      explain elx goals orig ws
      return []
    else do
      vals <- mapM (\p -> evalLExp phandle (Lambek.pEntries p) (Lambek.pLExp p)) ps
      case nub vals of
        [v] -> putStrLn v
        _   -> do
          putStrLn "That sentence is ambiguous"
          sequence_ [ putStrLn ("Sense [" ++ prettyLExp (Lambek.pLExp p) ++ "]: " ++ v)
                    | (p,v) <- take maxShown (zip ps vals) ]
          if length ps > maxShown
            then putStrLn ("... and " ++ show (length ps - maxShown) ++ " more")
            else return ()
      return (map Lambek.pDeriv ps)

-- say something useful about why a sentence was rejected
explain :: Lexicon PythonCode -> [LTp] -> [String] -> [String] -> IO ()
explain elx goals orig ws =
  case Lambek.unknownWords elx ws of
    (u:us) -> putStrLn ("   I do not know the word(s): " ++ intercalate ", " (u:us))
    []     ->
      case length (Lambek.longestGoodPrefix elx goals ws) of
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

showLexicon :: Lexicon PythonCode -> [LTp] -> IO ()
showLexicon elx goals = do
  putStrLn ("Goal types: " ++ intercalate ", " (map showLTp goals))
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
  -- input a lexicon file, which also declares any algebraic laws
  (elx,laws,goals) <- getLex
  -- input a database of facts
  db <- getDB
  -- launch a Python interpreter, then load our helper and the world into it
  phandle <- launchPython (PCode "")
  startEval phandle db
  -- start the read-eval-print loop
  putStrLn "Starting chat...  (:help for commands)"
  repl elx laws goals phandle []
  where
    getDB :: IO PythonCode
    getDB = do
      putStr "Facts about the world: "
      dname <- getLine
      mdb <- try (readFile dname) :: IO (Either IOError String)
      case mdb of
        Left err -> putStrLn ("Error loading file " ++ show err) >> getDB
        Right db -> return (PCode db)

    getLex :: IO (Lexicon PythonCode, Laws, [LTp])
    getLex = do
      putStr "Lexicon file: "
      lname <- getLine
      res <- parseFile lexicon lname
      case res of
        Left err -> putStrLn ("Error loading file " ++ show err) >> getLex
        Right (Left err) -> putStrLn ("parse error at " ++ lname ++ ":" ++ show err) >> getLex
        Right (Right loaded) -> return loaded
