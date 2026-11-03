import Data.List (sort)
import System.Exit

import LTypes
import LExp
import Deriv
import Parser
import PySupport
import qualified Lambek


grammatical :: [(String,Bool)]
grammatical =
  [ ("Seamus is hungry and"      , False)
  , ("Seamus is hungry and grey" , True)
  , ("Conor sleeps"              , True)
  , ("every cat sleeps"          , True)
  , ("every grey cat sleeps"     , True)
  , ("someone fears Fiona"       , True)
  , ("every cat fears a dog"     , True)
  -- a few of our own
  , ("Conor chases"              , False)
  , ("sleeps Conor"              , False)
  , ("Conor fears Fiona"         , True)
  , ("Conor flies"               , False)   -- unknown word
  ]

derivedTerms :: [(String,[String])]
derivedTerms =
  [ ("Seamus is hungry and grey", ["Is_2 Seamus_1 (And_4 Hungry_3 Grey_5)"])
  , ("Conor sleeps"             , ["Sleeps_2 Conor_1"])
  , ("every cat sleeps"         , ["Every_1 Cat_2 (\\a. Sleeps_3 a)"])
  , ("every grey cat sleeps"    , ["Every_1 (Grey_2 Cat_3) (\\a. Sleeps_4 a)"])
  , ("every cat fears a dog"    , [ "Every_1 Cat_2 (\\a. A_4 Dog_5 (\\b. Fears_3 a b))"
                                  , "A_4 Dog_5 (\\a. Every_1 Cat_2 (\\b. Fears_3 b a))" ])
  ]

-- ----------------------------------------
-- the harness
-- ----------------------------------------

main :: IO ()
main = do
  res <- parseFile lexicon "animals.elx"
  case res of
    Left err                -> die ("could not read animals.elx: " ++ show err)
    Right (Left err)        -> die ("could not parse animals.elx: " ++ show err)
    Right (Right lex)       -> do
      rs <- sequence (checks lex)
      let failed = length (filter not rs)
      putStrLn ""
      putStrLn (show (length rs - failed) ++ "/" ++ show (length rs) ++ " checks passed")
      if failed == 0 then exitSuccess else exitFailure

checks :: Lexicon PythonCode -> [IO Bool]
checks lex =
  [ check ("grammatical: " ++ s) (Lambek.isGrammatical lex (sentence s) == want)
  | (s,want) <- grammatical ]
  ++
  [ check ("terms: " ++ s) (sort (map prettyLExp (Lambek.readings lex (sentence s))) == sort want)
  | (s,want) <- derivedTerms ]
  ++
  [ check ("decide agrees with derive: " ++ s)
          (Lambek.isGrammatical lex (sentence s) == not (null (Lambek.readings lex (sentence s))))
  | (s,_) <- grammatical ]
  ++
  [ check ("derivations read back as their terms: " ++ s)
          (all wellFormed (Lambek.parses lex (sentence s)))
  | (s,_) <- derivedTerms ]

-- every free variable of the term should be one of the lexicon positions that the parse chose
wellFormed :: Lambek.Parse PythonCode -> Bool
wellFormed p = all (`elem` map fst (Lambek.pEntries p)) (freeNonBound (Lambek.pLExp p))
  where freeNonBound = free

sentence :: String -> [String]
sentence = map std . words
  where std []     = []
        std (c:cs) = toUpperC c : map toLowerC cs
        toUpperC c = if c >= 'a' && c <= 'z' then toEnum (fromEnum c - 32) else c
        toLowerC c = if c >= 'A' && c <= 'Z' then toEnum (fromEnum c + 32) else c

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "  ok   " else "  FAIL ") ++ name)
  return ok
