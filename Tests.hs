import Data.List (nub, sort)
import System.Exit

import LTypes
import LExp
import Eval
import Ambiguity
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

{-
  How many readings a sentence has before and after quotienting by the laws that animals.elx declares (ASSOC : And).

  The first sentence is an example given in the project's description: two bracketings of "and", one meaning.
  The second is ambiguous: two quantifier scopings that disagree about the world
-}
senseCounts :: [(String,Int,Int)]
senseCounts =
  [ ("Seamus sleeps and Seamus is grey and Seamus fears Dara", 2, 1)
  , ("every cat fears a dog"                                 , 2, 2)
  , ("Seamus is hungry and grey"                             , 1, 1)
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
    Right (Right (elx,laws)) -> do
      world <- readFile "aniworld.py"
      ph <- launchPython (PCode "")
      startEval ph (PCode world)
      rs <- sequence (checks laws elx ++ evalChecks laws elx ph)
      let failed = length (filter not rs)
      putStrLn ""
      putStrLn (show (length rs - failed) ++ "/" ++ show (length rs) ++ " checks passed")
      if failed == 0 then exitSuccess else exitFailure

checks :: Laws -> Lexicon PythonCode -> [IO Bool]
checks laws elx =
  [ check ("grammatical: " ++ s) (Lambek.isGrammatical elx (Lambek.sentence s) == want)
  | (s,want) <- grammatical ]
  ++
  [ check ("terms: " ++ s) (sort (map prettyLExp (Lambek.readings text elx (Lambek.sentence s))) == sort want)
  | (s,want) <- derivedTerms ]
  ++
  [ check ("decide agrees with derive: " ++ s)
          (Lambek.isGrammatical elx (Lambek.sentence s) == not (null (Lambek.readings text elx (Lambek.sentence s))))
  | (s,_) <- grammatical ]
  ++
  [ check ("readings modulo alpha: " ++ s)
          (length (Lambek.senses noLaws text elx (Lambek.sentence s)) == nAlpha)
  | (s,nAlpha,_) <- senseCounts ]
  ++
  [ check ("readings modulo declared laws: " ++ s)
          (length (Lambek.senses laws text elx (Lambek.sentence s)) == nLaws)
  | (s,_,nLaws) <- senseCounts ]
  ++
  [ check ("derivations read back as their terms: " ++ s)
          (all wellFormed (Lambek.parses elx (Lambek.sentence s)))
  | (s,_) <- derivedTerms ]

-- every free variable of the term should be one of the lexicon positions that the parse chose
evaluated :: [(String,[String])]
evaluated =
  [ ("Seamus sleeps and Seamus is grey", ["True"])
  , ("Conor sleeps"                    , ["False"])
  , ("every cat sleeps"                , ["False"])
  , ("every grey cat sleeps"           , ["True"])
  , ("every cat fears a dog"           , ["False","True"])   -- ambiguous
  ]

-- Evaluating every reading of a sentence should give the correct answers.  These run in order against one interpreter, which also
-- checks that the one-line protocol stays in step across many queries.
evalChecks :: Laws -> Lexicon PythonCode -> PythonHandle -> [IO Bool]
evalChecks laws elx ph =
  [ do vals <- mapM (\p -> evalLExp ph (Lambek.pEntries p) (Lambek.pLExp p))
                    (Lambek.senses laws text elx (Lambek.sentence s))
       check ("evaluates: " ++ s) (nub (sort vals) == want)
  | (s,want) <- evaluated ]

wellFormed :: Lambek.Parse PythonCode -> Bool
wellFormed p = all (`elem` map fst (Lambek.pEntries p)) (free (Lambek.pLExp p))

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "  ok   " else "  FAIL ") ++ name)
  return ok
