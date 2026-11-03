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
-}
helperCode :: String
helperCode =
  "exec(\"def _ans(th):\\n try:\\n  return repr(th())\\n"
  ++ " except Exception as e:\\n  return 'ERROR: '+type(e).__name__+': '+str(e)\\n\")"

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

-- evaluate one reading, returning what Python printed
evalLExp :: PythonHandle -> [(Var,PythonCode)] -> LExp -> IO String
evalLExp ph env e = do
  out <- runPythonCode ph (PCode ("print(_ans(lambda: " ++ pyExpr env e ++ "))"))
  return (trim out)

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace
