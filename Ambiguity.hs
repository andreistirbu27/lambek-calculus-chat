{-
  Deciding when two readings of a sentence are really the same reading.

  The calculus produces several derivations of

      Seamus sleeps and Seamus is grey and Seamus fears Dara

  because "and" can be bracketed either way:

      And_3 (Sleeps_2 Seamus_1) (And_7 (Is_5 Seamus_4 Grey_6) (Fears_9 ...))
      And_7 (And_3 (Sleeps_2 Seamus_1) (Is_5 Seamus_4 Grey_6)) (Fears_9 ...)

  These are different lambda expressions, not alpha-equivalent, not beta-equal, and even the head variables differ, 
  since the two occurrences of "and" sit at different positions in the sentence.  They agree only because "and" is associative, 
  which is a fact about its meaning that the calculus knows nothing about.

  So the lexicon declares the laws its words satisfy and we quotient terms by them: "canonical" rewrites a term to a normal form 
  for the declared laws, and two readings are the same reading when their normal forms agree.
-}

module Ambiguity where

import LExp

-- the words a lexicon declares associative
data Laws = Laws { assocWords :: [String] }
  deriving (Show,Eq)

noLaws :: Laws
noLaws = Laws []

-- the word a position variable came from: "And_3" -> "And"
wordOfVar :: Var -> String
wordOfVar = takeWhile (/= '_')

{-
  A normal form for the declared laws.

  Step one renames every lexicon variable to its word together with the semantic value its entry supplied, so two occurrences of "and" at
  different positions become the same operator; but two *different* entries for "and" (the one at s \ (s / s) and the one at adj \ (adj / adj)) 
  stay distinct, and readings that use different entries are never merged.

  Step two flattens nested applications of an associative operator and rebuilds them right-nested.
-}
canonical :: Laws -> [(Var,String)] -> LExp -> LExp
canonical laws env = reassoc laws . rename (keyOf env)

keyOf :: [(Var,String)] -> Var -> Var
keyOf env x =
  case lookup x env of
    Just s  -> wordOfVar x ++ "=" ++ s
    Nothing -> x

reassoc :: Laws -> LExp -> LExp
reassoc laws e =
  case e of
    A (A (V op) _) _
      | isAssoc laws op -> rebuild op (gather laws op e)
    A e1 e2             -> A (reassoc laws e1) (reassoc laws e2)
    L x e1              -> L x (reassoc laws e1)
    V x                 -> V x

-- all the operands of a chain of applications of one associative operator
gather :: Laws -> Var -> LExp -> [LExp]
gather laws op (A (A (V op') x) y)
  | op' == op = gather laws op x ++ gather laws op y
gather laws _ e = [reassoc laws e]

-- right-nested is the normal form we pick; any fixed choice would do
rebuild :: Var -> [LExp] -> LExp
rebuild op = foldr1 (\x y -> A (A (V op) x) y)

isAssoc :: Laws -> Var -> Bool
isAssoc laws op = wordOfKey op `elem` assocWords laws

-- the word part of a renamed variable, "And=lambda x : ..." -> "And"
wordOfKey :: Var -> String
wordOfKey = takeWhile (/= '=')
