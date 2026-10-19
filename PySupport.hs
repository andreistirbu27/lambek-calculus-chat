module PySupport where

import System.IO
import System.Process
import Control.Exception (evaluate)

newtype PythonCode = PCode { text :: String }
type PythonHandle = (Handle,Handle,Handle,ProcessHandle)

-- start a Python interpreter in interactive mode, load some code, and return handle
launchPython :: PythonCode -> IO PythonHandle
launchPython prelude = do
  (Just hin, Just hout, Just herr, ph) <-
    createProcess (proc "python3" ["-i"])
    { std_in  = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
  hSetBuffering hin LineBuffering
  hSetBuffering hout NoBuffering
  hPutStrLn hin "import sys"
  hPutStrLn hin "sys.ps1 = ''"
  hPutStr hin (text prelude)
  return (hin,hout,herr,ph)
  
-- run some Python code and return the results
runPythonCode :: PythonHandle -> PythonCode -> IO String
runPythonCode (hin,hout,herr,ph) code = do
  hPutStrLn hin "\n"
  hPutStrLn hin (text code)
  aout <- hGetLine hout
  return aout
