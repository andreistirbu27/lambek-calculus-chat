{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-
  Lambek's decision procedure for the product-free fragment, and the derivation search built on top of it.

  The six rules, writing  gamma --> b  for right-inversion judgments and gammaL [a] gammaR --> p  for left-focused ones:

      a, gamma --> b                gamma, a --> b
    ------------------ R          ------------------ R'
     gamma --> a \ b                gamma --> b / a

     gammaL [a] gammaR --> p
    ------------------------- F     ----------- X
     gammaL, a, gammaR --> p         [p] --> p

     gammaL2 --> a    gammaL1 [b] gammaR --> p
    ------------------------------------------- L
       gammaL1, gammaL2 [a \ b] gammaR --> p

     gammaR1 --> a    gammaL [b] gammaR2 --> p
    ------------------------------------------- L'
       gammaL [b / a] gammaR1, gammaR2 --> p

-}

module Lambek where

import Data.Char (toUpper, toLower)
import Data.List (nub, nubBy)

import LTypes
import LExp
import Deriv
import Ambiguity

-- ----------------------------------------------------------
-- words in, as the lexicon spells them
-- ----------------------------------------------------------

-- Lexicon words are one capital then lowercase, so standardize the user's
-- capitalization before looking anything up.  Both the chat loop and the
-- tests go through here, so they cannot drift apart.
stdize :: String -> String
stdize []     = []
stdize (c:cs) = toUpper c : map toLower cs

-- split a line of input into standardized words
sentence :: String -> [String]
sentence = map stdize . words

-- -------------------------------------------------------------------
-- W1: deciding entailment
-- -------------------------------------------------------------------

-- dec_rinv gamma b  is True exactly when  gamma --> b  is derivable
dec_rinv :: [LTp] -> LTp -> Bool
dec_rinv gamma (DivL a b) = dec_rinv (a : gamma) b
dec_rinv gamma (DivR b a) = dec_rinv (gamma ++ [a]) b
dec_rinv gamma (Atm p) =
  or [ dec_lfoc (take k gamma) (gamma !! k) (drop (k+1) gamma) p
     | k <- [0 .. length gamma - 1] ]

-- dec_lfoc gammaL a gammaR p  is True exactly when  gammaL [a] gammaR --> p is derivable
dec_lfoc :: [LTp] -> LTp -> [LTp] -> Atm -> Bool
dec_lfoc gammaL (DivL a b) gammaR p =
  or [ dec_rinv (drop k gammaL) a && dec_lfoc (take k gammaL) b gammaR p
     | k <- [0 .. length gammaL] ]
dec_lfoc gammaL (DivR b a) gammaR p =
  or [ dec_rinv (take k gammaR) a && dec_lfoc gammaL b (drop k gammaR) p
     | k <- [0 .. length gammaR] ]
dec_lfoc gammaL (Atm q) gammaR p =
  null gammaL && null gammaR && q == p

-- A list of words is a grammatical sentence when some choice of lexicon entry for each word yields a context entailing the sentence type.  
-- A word with no entry at all makes the product below empty, so the sentence is rejected.
isGrammatical :: Lexicon sem -> [String] -> Bool
isGrammatical elx ws = isGrammaticalAt elx [stp elx] ws

-- the same, but accepting any of several goal types.  A lexicon that declares a QUESTION type has two: declaratives derive s, questions derive q.
isGrammaticalAt :: Lexicon sem -> [LTp] -> [String] -> Bool
isGrammaticalAt elx goals ws =
  not (null ws) &&
  or [ dec_rinv gamma g | g <- goals, gamma <- sequence (typesOf elx ws) ]

-- the types each word can have, in sentence order
typesOf :: Lexicon sem -> [String] -> [[LTp]]
typesOf elx ws = [ [ t | (w',t,_) <- items elx, w' == w ] | w <- ws ]

-- --------------------------------------------------------------
-- W3: searching for derivations
-- --------------------------------------------------------------

-- der_rinv and der_lfoc mirror dec_rinv and dec_lfoc, except that they return every derivation found instead of a yes/no answer, 
-- and the context now carries a variable for each type.
der_rinv :: Ctx -> LTp -> [Deriv]
der_rinv gamma (DivL a b) =
  [ Node (Rinv gamma (DivL a b)) (RuR x) [d] | d <- der_rinv ((x,a) : gamma) b ]
  where x = freshVar gamma
der_rinv gamma (DivR b a) =
  [ Node (Rinv gamma (DivR b a)) (RuR' x) [d] | d <- der_rinv (gamma ++ [(x,a)]) b ]
  where x = freshVar gamma
der_rinv gamma (Atm p) =
  [ Node (Rinv gamma (Atm p)) (RuF x) [d]
  | k <- [0 .. length gamma - 1]
  , let (x,a) = gamma !! k
  , d <- der_lfoc (take k gamma) a (drop (k+1) gamma) p
  ]

der_lfoc :: Ctx -> LTp -> Ctx -> Atm -> [Deriv]
der_lfoc gammaL (DivL a b) gammaR p =
  [ Node (Lfoc gammaL (DivL a b) gammaR p) RuL [dA,dK]
  | k  <- [0 .. length gammaL]
  , dA <- der_rinv (drop k gammaL) a
  , dK <- der_lfoc (take k gammaL) b gammaR p
  ]
der_lfoc gammaL (DivR b a) gammaR p =
  [ Node (Lfoc gammaL (DivR b a) gammaR p) RuL' [dA,dK]
  | k  <- [0 .. length gammaR]
  , dA <- der_rinv (take k gammaR) a
  , dK <- der_lfoc gammaL b (drop k gammaR) p
  ]
der_lfoc gammaL (Atm q) gammaR p
  | null gammaL && null gammaR && q == p =
      [ Node (Lfoc gammaL (Atm q) gammaR p) RuX [] ]
  | otherwise = []

-- The R and R' rules invent variables.  Words are named "Word_position", which always starts with a capital, so single lowercase letters 
-- don't clash with them.
freshVar :: Ctx -> Var
freshVar gamma =
  case [ v | v <- candidates, v `notElem` used ] of
    (v:_) -> v
    []    -> "z" ++ show (length used)
  where
    used       = map fst gamma
    candidates = [ [c] | c <- ['a' .. 'z'] ]

-- ---------------------------------------------------
-- parsing a sentence
-- ---------------------------------------------------

{-
  A derivation is only meaningful relative to one choice of lexicon entry per word, and the variable name does not record that choice: 
  "Hungry_3" could be the "adj" entry or the "n / n" entry.  So each parse carries the assignment of semantic values to variables that produced it.
-}
data Parse sem = Parse
  { pDeriv   :: Deriv          -- the derivation
  , pEntries :: [(Var,sem)]    -- the lexicon entry used at each position
  }

-- the lambda expression a parse denotes
pLExp :: Parse sem -> LExp
pLExp = toLExp . pDeriv

-- every parse of a sentence, over every choice of entries
parses :: Lexicon sem -> [String] -> [Parse sem]
parses elx = parsesAt elx (stp elx)

-- every parse of a sentence at a given goal type
parsesAt :: Lexicon sem -> LTp -> [String] -> [Parse sem]
parsesAt elx goal ws =
  [ Parse d [ (x,s) | (x,_,s) <- choice ]
  | choice <- sequence (entriesOf elx ws)
  , d <- der_rinv [ (x,t) | (x,t,_) <- choice ] goal
  ]

-- the entries each word can use, labelled by its position in the sentence
entriesOf :: Lexicon sem -> [String] -> [[(Var,LTp,sem)]]
entriesOf elx ws =
  [ [ (w ++ "_" ++ show i, t, s) | (w',t,s) <- items elx, w' == w ]
  | (i,w) <- zip [1 :: Int ..] ws ]

{-
  One parse per distinct reading.

  Two parses count as the same reading when their canonical forms agree, which covers three things at once:
  1. alpha-equivalence (equality on LExp already is alpha-equivalence)
  2. the algebraic laws the lexicon declares for its words
  3. the entries each reading chose 
  "showSem" renders a semantic value, so that two readings using *different* entries for the same word are never merged;

-}
senses :: Laws -> (sem -> String) -> Lexicon sem -> [String] -> [Parse sem]
senses laws showSem elx = sensesAt laws showSem elx (stp elx)

sensesAt :: Laws -> (sem -> String) -> Lexicon sem -> LTp -> [String] -> [Parse sem]
sensesAt laws showSem elx goal ws = nubBy sameSense (parsesAt elx goal ws)
  where
    sameSense p q = key p == key q
    key p = canonical laws [ (v, showSem s) | (v,s) <- pEntries p ] (pLExp p)

-- The readings at the first goal type that yields any, so a declarative is read as a declarative and only then as a question.  
-- The chat loop and the tests both come through here.
sensesAny :: Laws -> (sem -> String) -> Lexicon sem -> [LTp] -> [String] -> [Parse sem]
sensesAny laws showSem elx goals ws =
  case dropWhile null [ sensesAt laws showSem elx g ws | g <- goals ] of
    (ps:_) -> ps
    []     -> []

-- the distinct readings of a sentence, as lambda expressions, ignoring any
-- laws the lexicon declares
readings :: (sem -> String) -> Lexicon sem -> [String] -> [LExp]
readings showSem elx ws = map pLExp (senses noLaws showSem elx ws)

-- ----------------------------------------------------
-- W2: explaining a rejection
-- ----------------------------------------------------

-- words the lexicon has never heard of
unknownWords :: Lexicon sem -> [String] -> [String]
unknownWords elx ws = nub [ w | w <- ws, null [ () | (w',_,_) <- items elx, w' == w ] ]

-- the longest prefix of the input that stands on its own at one of the goal types, usually pointing out where things went wrong
longestGoodPrefix :: Lexicon sem -> [LTp] -> [String] -> [String]
longestGoodPrefix elx goals ws =
  last ([] : [ p | n <- [1 .. length ws], let p = take n ws, isGrammaticalAt elx goals p ])
