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
  (elx,laws,goals,ph)     <- domain "animals.elx" "aniworld.py"
  (celx,claws,cgoals,cph) <- domain "courses.elx" "uniworld.py"
  rs <- sequence (checks laws elx
                  ++ evalChecks laws goals elx ph evaluated
                  ++ whyChecks laws goals elx ph
                  ++ evalChecks claws cgoals celx cph courseEvaluated)
  let failed = length (filter not rs)
  putStrLn ""
  putStrLn (show (length rs - failed) ++ "/" ++ show (length rs) ++ " checks passed")
  if failed == 0 then exitSuccess else exitFailure

-- read a lexicon and start an interpreter holding its world
domain :: FilePath -> FilePath -> IO (Lexicon Sem, Laws, [LTp], PythonHandle)
domain elxFile worldFile = do
  res <- parseFile lexicon elxFile
  case res of
    Left err         -> die ("could not read " ++ elxFile ++ ": " ++ show err)
    Right (Left err) -> die ("could not parse " ++ elxFile ++ ": " ++ show err)
    Right (Right (elx,laws,goals)) -> do
      world <- readFile worldFile
      ph <- launchPython (PCode "")
      startEval ph (PCode world)
      return (elx,laws,goals,ph)

checks :: Laws -> Lexicon Sem -> [IO Bool]
checks laws elx =
  [ check ("grammatical: " ++ s) (Lambek.isGrammatical elx (Lambek.sentence s) == want)
  | (s,want) <- grammatical ]
  ++
  [ check ("terms: " ++ s) (sort (map prettyLExp (Lambek.readings showSem elx (Lambek.sentence s))) == sort want)
  | (s,want) <- derivedTerms ]
  ++
  [ check ("decide agrees with derive: " ++ s)
          (Lambek.isGrammatical elx (Lambek.sentence s) == not (null (Lambek.readings showSem elx (Lambek.sentence s))))
  | (s,_) <- grammatical ]
  ++
  [ check ("readings modulo alpha: " ++ s)
          (length (Lambek.senses noLaws showSem elx (Lambek.sentence s)) == nAlpha)
  | (s,nAlpha,_) <- senseCounts ]
  ++
  [ check ("readings modulo declared laws: " ++ s)
          (length (Lambek.senses laws showSem elx (Lambek.sentence s)) == nLaws)
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
  -- questions, answered at the QUESTION goal type
  , ("who sleeps"                      , ["Seamus"])
  , ("who is hungry"                   , ["Conor, Dara, Ronan"])
  , ("who is grey"                     , ["Seamus, Tara"])
  , ("who chases Fiona"                , ["Dara"])
  , ("which cat sleeps"                , ["Seamus"])
  , ("Conor chases who"                , ["Tara"])
  , ("Tara fears who"                  , ["Conor, Seamus"])
  , ("who swims"                       , ["Brian, Fiona"])
  -- yes/no questions, and the "does" inversion
  , ("does Conor sleep"                , ["No"])
  , ("does Seamus sleep"               , ["Yes"])
  , ("does Conor chase Tara"           , ["Yes"])
  , ("does Tara chase Conor"           , ["No"])
  , ("is Conor hungry"                 , ["Yes"])
  , ("is Seamus hungry"                , ["No"])
  , ("who does Conor fear"             , ["Fiona"])
  , ("who does Tara fear"              , ["Conor, Seamus"])
  , ("who does Dara chase"             , ["Fiona"])
  -- the declaratives these invert must still read as declaratives
  , ("Conor is hungry"                 , ["True"])
  , ("Conor chases Tara"               , ["True"])
  ]

-- Evaluating every reading of a sentence should give the correct answers.  These run in order against one interpreter, which also
-- checks that the one-line protocol stays in step across many queries.
evalChecks :: Laws -> [LTp] -> Lexicon Sem -> PythonHandle -> [(String,[String])] -> [IO Bool]
evalChecks laws goals elx ph table =
  [ do vals <- mapM (\p -> evalLExp ph (mainEnv (Lambek.pEntries p)) (Lambek.pLExp p))
                    (Lambek.sensesAny laws showSem elx goals (Lambek.sentence s))
       check ("evaluates: " ++ s) (nub (sort vals) == want)
  | (s,want) <- table ]

{-
  The explanation of each reading, in the order the readings come out.  Nothing where the head word of the reading has no
  explaining value: a wh-question is answered, not explained.

  "every cat fears a dog" is the case worth having: the two scopings disagree, and each explains itself.
-}
explained :: [(String,[Maybe String])]
explained =
  [ ("every cat sleeps"                , [Just "no, not Conor"])
  , ("every grey cat sleeps"           , [Just "yes, all of Seamus"])
  , ("Conor sleeps"                    , [Just "no; the ones who sleep are Seamus"])
  , ("Conor chases Tara"               , [Just "yes; Conor chases Tara"])
  , ("Conor is hungry"                 , [Just "yes; that holds of Conor, Dara, Ronan"])
  , ("Seamus sleeps and Seamus is grey", [Just "both parts hold"])
  , ("Conor sleeps and Seamus is grey" , [Just "only the second part holds"])
  , ("someone swims"                   , [Just "yes, Brian, Fiona"])
  , ("every cat fears a dog"           , [Just "yes, all of Conor, Seamus", Just "no, none of Dara, Fiona"])
  , ("is Conor hungry"                 , [Just "yes; that holds of Conor, Dara, Ronan"])
  , ("who sleeps"                      , [Nothing])
  ]

whyChecks :: Laws -> [LTp] -> Lexicon Sem -> PythonHandle -> [IO Bool]
whyChecks laws goals elx ph =
  [ do got <- mapM (\p -> explainLExp ph (Lambek.pEntries p) (Lambek.pLExp p))
                   (Lambek.sensesAny laws showSem elx goals (Lambek.sentence s))
       check ("explains: " ++ s) (got == want)
  | (s,want) <- explained ]

{-
  The second domain, which asks the same kinds of question of a different world.  Quantification there ranges over people and
  courses together, so "who" and "what" restrict to one sort each, and nouns can carry a relative clause.
-}
courseEvaluated :: [(String,[String])]
courseEvaluated =
  [ ("Ana takes logic"                      , ["True"])
  , ("Boris takes logic"                    , ["False"])
  , ("Mira teaches logic"                   , ["True"])
  , ("logic is hard"                        , ["True"])
  , ("every student passes"                 , ["False"])
  , ("every course is hard"                 , ["False"])
  -- ambiguous here too: every teacher teaches some course, but no one course is taught by both
  , ("every teacher teaches a course"       , ["False","True"])
  , ("every student that passes takes logic", ["False"])
  , ("someone teaches topology"             , ["True"])
  , ("who passes"                           , ["Ana, Chen, Elena"])
  , ("who takes logic"                      , ["Ana, Elena"])
  , ("who teaches algebra"                  , ["Nadia"])
  , ("which student passes"                 , ["Ana, Chen, Elena"])
  , ("what does Ana take"                   , ["algebra, logic"])
  , ("what does Elena take"                 , ["logic, topology"])
  , ("does Chen pass"                       , ["Yes"])
  , ("does Boris pass"                      , ["No"])
  , ("is algebra hard"                      , ["No"])
  ]

wellFormed :: Lambek.Parse Sem -> Bool
wellFormed p = all (`elem` map fst (Lambek.pEntries p)) (free (Lambek.pLExp p))

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "  ok   " else "  FAIL ") ++ name)
  return ok
