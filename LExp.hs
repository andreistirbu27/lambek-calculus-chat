{-# OPTIONS_GHC -Wno-x-partial #-}

module LExp where

import Data.List

type Var = String
data LExp = V Var | A LExp LExp | L Var LExp
  deriving (Show,Read)

isVar, isApp, isLam :: LExp -> Bool
isVar (V _)   = True
isVar _       = False
isApp (A _ _) = True
isApp _       = False
isLam (L _ _) = True
isLam _       = False

-- pretty-printing routines for lambda expressions

parenIf :: Bool -> String -> String
parenIf b s = if b then "(" ++ s ++ ")" else s

prettyLExp  :: LExp -> String
prettyLExp (V x)     = x
prettyLExp (A t1 t2) = parenIf (isLam t1) (prettyLExp t1) ++ " " ++ parenIf (not $ isVar t2) (prettyLExp t2)
prettyLExp (L x t1)  = "\\" ++ x ++ ". " ++ prettyLExp t1

printLExp :: LExp -> IO ()
printLExp = putStrLn . prettyLExp

-- compute the list of free vars of an expression
free :: LExp -> [Var]
free (V x)     = [x]
free (A t1 t2) = free t1 `union` free t2
free (L x t1)  = free t1 \\ [x]

-- apply a variable renaming
rename :: (Var -> Var) -> LExp -> LExp
rename f (V x)     = V (f x)
rename f (A t1 t2) = A (rename f t1) (rename f t2)
rename f (L x t1)  = L (f x) (rename f t1)

-- apply a variable swapping
swapname :: (Var,Var) -> LExp -> LExp
swapname (x,y) = rename (\z -> if z == x then y else if z == y then x else z)

-- test for alpha-equivalence
alphaEq :: LExp -> LExp -> Bool
alphaEq (V x1)    (V x2)    = x1 == x2
alphaEq (A t1 u1) (A t2 u2) = alphaEq t1 t2 && alphaEq u1 u2
alphaEq (L x1 t1) (L x2 t2) = alphaEq t1 (swapname (x2,x1) t2)
alphaEq _         _         = False

-- equality of lambda expressions is given by alpha-equivalence
instance Eq LExp where
  t1 == t2 = alphaEq t1 t2

-- returns a variable that is fresh for a list of terms
fresh :: [LExp] -> Var
fresh ts = case named_vars \\ fvs of
  []     -> maximum fvs ++ "'"
  (x:xs) -> x
  where
    named_vars = [[c] | c <- ['a'..'z']]
    fvs = concatMap free ts

-- capture-avoiding substitution
subst :: (LExp,Var) -> LExp -> LExp
subst (u,x) t =
  case t of
    V y
      | y == x                -> u
      | otherwise             -> V y
    A t1 t2                   -> A (subst (u,x) t1) (subst (u,x) t2)
    L y t1
      | y == x                -> L y t1
      | not (y `elem` free u) -> L y (subst (u,x) t1)
      | otherwise             -> L z (subst (u,x) t1')
        where
          z = fresh [V x, t1, u]
          t1' = rename (\w -> if w == y then z else w) t1

-- datatype of one-hole contexts for lambda expressions
data LExpCxt = Hole | A'1 LExpCxt LExp | A'2 LExp LExpCxt | L' Var LExpCxt
  deriving (Show,Eq)

-- we represent contexts "inside-out", i.e., with the parts of the
-- context nearest to the hole at the top-level.
-- The plugging function is defined accordingly.
plug :: LExpCxt -> LExp -> LExp
plug Hole       d = d
plug (A'1 c e2) d = plug c (A d e2)
plug (A'2 e1 c) d = plug c (A e1 d)
plug (L' x c)   d = plug c (L x d)

-- a pointer to a subexpression is a pair of a context and an expression (i.e., a "zipper")
type LExpPtr = (LExpCxt,LExp)

-- generate pointers to all subexpressions of a given expression, in a left-to-right preorder traversal
subexp :: LExp -> [LExpPtr]
subexp e = go Hole e
  where
    go :: LExpCxt -> LExp -> [LExpPtr]
    go c e = (c,e) :      -- focus on the root expression, or
             case e of    -- focus on a proper sub-expression
               A e1 e2 -> go (A'1 c e2) e1  -- focus on a subexpression of the function of an application, or
                       ++ go (A'2 e1 c) e2  -- focus on a subexpression of the argument of an application
               L x e1  -> go (L' x c) e1    -- focus on a subexpression of the body of an abstraction
               V x     -> []                -- can't focus on a proper subexpression of a variable or constant, since they have none

-- generate pointers to all beta-redices in a given expression, starting with the leftmost outermost redices
redex :: LExp -> [LExpPtr]
redex t = [(k,u) | (k,u@(A (L _ _) _)) <- subexp t]

-- perform a non-deterministic step of beta reduction, trying leftmost outermost redices first
stepBeta :: LExp -> [LExp]
stepBeta t = do
  (k, A (L x t1) t2) <- redex t
  return $ plug k (subst (t2,x) t1)

-- test if an expression is beta normal
isNormal :: LExp -> Bool
isNormal t = null (stepBeta t)

-- normalize an expression
normalize :: LExp -> LExp
normalize t = until isNormal (head . stepBeta) t
