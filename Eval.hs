{-
  Interpreting a derivation by its meaning in the world.

  A derivation gives us a lambda expression whose free variables are the word positions of the sentence, 
  and the lexicon gives each of those positions a Python expression.  Reading application as application and 
  abstraction as a Python lambda turns the whole thing into one Python expression, which we hand to the interpreter.
-}

module Eval where

import Data.Char (isAlphaNum, isSpace)
import Data.List (dropWhileEnd)
import System.IO

import LExp
import PySupport

-- -------------------------------------
-- what a lexicon entry means
-- -------------------------------------

{-
  An entry gives a Python expression for the meaning of a word, and may give a second one that explains instead of computing.
  Reading the same lambda term with the explaining value in place of the meaning produces a sentence about why the answer came out
  as it did.
-}
data Sem = Sem { semMain :: PythonCode, semWhy :: Maybe PythonCode }

-- the meaning of whichever entry each position chose
mainEnv :: [(Var,Sem)] -> [(Var,PythonCode)]
mainEnv env = [ (x,semMain s) | (x,s) <- env ]

-- Readings are told apart by the entries they chose, and the meaning identifies the entry.
showSem :: Sem -> String
showSem = text . semMain

-- -------------------------------------
-- lambda expressions as Python
-- -------------------------------------

-- "env" maps each word position to the semantic value of the lexicon entry that the derivation chose for it.
pyExpr :: [(Var,PythonCode)] -> LExp -> String
pyExpr env (V x) =
  case lookup x env of
    Just (PCode s) -> "(" ++ s ++ ")"
    Nothing        -> pyName x
pyExpr env (A e1 e2) = pyExpr env e1 ++ "(" ++ pyExpr env e2 ++ ")"
pyExpr env (L x e)   = "(lambda " ++ pyName x ++ ": " ++ pyExpr env e ++ ")"

-- The variables introduced by the R and R' rules are single letters, which can collide with a name in the world file ("a", say).  
-- Prefixing them keeps our bindings out of the world's namespace.
pyName :: Var -> String
pyName x = "v_" ++ map keep x
  where keep c = if isAlphaNum c || c == '_' then c else '_'

-- --------------------------------------
-- talking to the interpreter
-- --------------------------------------

sendLine :: PythonHandle -> String -> IO ()
sendLine (hin,_,_,_) s = hPutStrLn hin s

{-
  runPythonCode reads exactly one line of stdout, so every query has to print exactly one line and must never raise: a traceback 
  goes to the stderr handle that nobody reads, and the read would then block forever.

  A wh-question answers with a collection, so those are joined into one readable line, and a yes/no question answers with a string, 
  which is shown as is.  Everything else goes through repr, which gives True and False for declaratives.

  We also install "names", which lexicon authors can call to list a set of individuals.
-}
helperCode :: String
helperCode =
  "exec(\"def _ans(th):\\n try:\\n  v = th()\\n"
  ++ "  if isinstance(v,str): return v\\n"
  ++ "  if isinstance(v,(list,tuple,set,frozenset)):\\n"
  ++ "   return ', '.join(sorted(map(str,v))) or '(nobody)'\\n"
  ++ "  return repr(v)\\n"
  ++ " except Exception as e:\\n  return 'ERROR: '+type(e).__name__+': '+str(e)\\n"
  ++ "def names(xs):\\n return ', '.join(sorted(xs)) or 'nobody'\\n\")"

loadWorld :: PythonHandle -> PythonCode -> IO ()
loadWorld ph (PCode src) = sendLine ph ("exec(" ++ pyString src ++ ")")

-- a Python double-quoted string literal holding the given text
pyString :: String -> String
pyString s = "\"" ++ concatMap esc s ++ "\""
  where
    esc '\\' = "\\\\"
    esc '"'  = "\\\""
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc c    = [c]

-- send the helper and the world; call once before evaluating anything
startEval :: PythonHandle -> PythonCode -> IO ()
startEval ph@(hin,hout,_,_) world = do
  hSetEncoding hin utf8
  hSetEncoding hout utf8
  sendLine ph helperCode
  loadWorld ph world
  -- skip whatever Python prints on startup (VS Code adds a line), otherwise all answers are off by one
  sendLine ph ("print(" ++ pyString syncMarker ++ ")")
  skipTo syncMarker
  where
    skipTo m = do
      l <- hGetLine hout
      if trim l == m then return () else skipTo m

syncMarker :: String
syncMarker = "--chatllambda-ready--"

-- evaluate one reading, returning what Python printed
evalLExp :: PythonHandle -> [(Var,PythonCode)] -> LExp -> IO String
evalLExp ph env e = do
  out <- runPythonCode ph (PCode ("print(_ans(lambda: " ++ pyExpr env e ++ "))"))
  return (trim out)

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

-- --------------------------------------
-- explaining an answer
-- --------------------------------------

{-
  Only the head word is read in explaining mode.

  The head is the word the whole sentence is an application of: the quantifier in "every cat sleeps", the conjunction in "A and B".
  That is the word that knows why the answer came out as it did, and it still receives the ordinary meanings of its arguments, which
  is what it expects.  Swapping an inner word as well would hand it a sentence where it wants a meaning.
-}
headVar :: LExp -> Maybe Var
headVar (V x)   = Just x
headVar (A e _) = headVar e
headVar (L _ e) = headVar e

-- Nothing when the head word of this reading has nothing to say
explainLExp :: PythonHandle -> [(Var,Sem)] -> LExp -> IO (Maybe String)
explainLExp ph env e =
  case headVar e of
    Nothing -> return Nothing
    Just x  ->
      case lookup x env >>= semWhy of
        Nothing  -> return Nothing
        -- the head is first in the environment, so this value hides its meaning
        Just why -> fmap Just (evalLExp ph ((x,why) : mainEnv env) e)
