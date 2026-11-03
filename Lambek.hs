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

import Data.List (nub)

import LTypes
import LExp
import Deriv

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
isGrammatical lex ws =
  not (null ws) &&
  or [ dec_rinv gamma (stp lex) | gamma <- sequence (typesOf lex ws) ]

-- the types each word can have, in sentence order
typesOf :: Lexicon sem -> [String] -> [[LTp]]
typesOf lex ws = [ [ t | (w',t,_) <- items lex, w' == w ] | w <- ws ]

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
parses lex ws =
  [ Parse d [ (x,s) | (x,_,s) <- choice ]
  | choice <- sequence (entriesOf lex ws)
  , d <- der_rinv [ (x,t) | (x,t,_) <- choice ] (stp lex)
  ]

-- the entries each word can use, labelled by its position in the sentence
entriesOf :: Lexicon sem -> [String] -> [[(Var,LTp,sem)]]
entriesOf lex ws =
  [ [ (w ++ "_" ++ show i, t, s) | (w',t,s) <- items lex, w' == w ]
  | (i,w) <- zip [1 :: Int ..] ws ]

-- the distinct readings of a sentence, as lambda expressions.  Equality on LExp is alpha-equivalence, so nub collapses derivations 
-- that differ only in their choice of bound variable names.
readings :: Lexicon sem -> [String] -> [LExp]
readings lex ws = nub (map pLExp (parses lex ws))

-- ----------------------------------------------------
-- W2: explaining a rejection
-- ----------------------------------------------------

-- words the lexicon has never heard of
unknownWords :: Lexicon sem -> [String] -> [String]
unknownWords lex ws = nub [ w | w <- ws, null [ () | (w',_,_) <- items lex, w' == w ] ]

-- the longest prefix of the input that is a grammatical sentence on its own, usually pointing out where things went wrong
longestGoodPrefix :: Lexicon sem -> [String] -> [String]
longestGoodPrefix lex ws =
  last ([] : [ p | n <- [1 .. length ws], let p = take n ws, isGrammatical lex p ])
