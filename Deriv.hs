{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-
  Sequent calculus derivations, the lambda expressions they denote, and a
  Gentzen-style pretty printer.

  We keep derivations as explicit trees rather than returning bare lambda expressions (as the project's specs suggests), because a lambda
  expression forgets which position the F rule focused on and how the L/L' rules split the context.
  "toLExp" recovers the lambda expression, so nothing is lost.
-}

module Deriv where

import Data.List (intercalate, transpose)

import LTypes
import LExp

-- a context is a list of types, each labelled by the variable standing for it
type Ctx = [(Var,LTp)]

-- the two judgment forms
data Sequent
  = Rinv Ctx LTp          -- gamma             --> b
  | Lfoc Ctx LTp Ctx Atm  -- gammaL [ a ] gammaR --> p
  deriving (Show,Eq)

-- the six rules.  R, R' and F record the variable they introduce or focus on.
data Rule = RuX | RuR Var | RuR' Var | RuF Var | RuL | RuL'
  deriving (Show,Eq)

-- a derivation node: its conclusion, the rule applied, and its premises.
-- Storing the conclusion at every node is ~redundant, but it makes printing a single recursive function instead of threading contexts around.
data Deriv = Node Sequent Rule [Deriv]
  deriving (Show,Eq)

conclusion :: Deriv -> Sequent
conclusion (Node s _ _) = s

-- how many derivation steps (useful for preferring simpler readings)
size :: Deriv -> Int
size (Node _ _ ds) = 1 + sum (map size ds)

-- --------------------------------------------------------
-- reading a derivation back as a lambda expression
-- --------------------------------------------------------

-- R and R' become lambda abstraction and F becomes a variable applied to the arguments collected by the left-focused subderivation.
toLExp :: Deriv -> LExp
toLExp (Node _ (RuR x)  [d]) = L x (toLExp d)
toLExp (Node _ (RuR' x) [d]) = L x (toLExp d)
toLExp (Node _ (RuF x)  [d]) = foldl A (V x) (spine d)
toLExp d = error ("toLExp: not a right-inversion derivation: " ++ show d)

-- A left-focused derivation of  gammaL [a] gammaR --> p  denotes a term with a hole,  [] e1 ... en.  We return the list of arguments 
-- e1 ... en; the L and L' rules each contribute one argument on the left, and X closes the list.
spine :: Deriv -> [LExp]
spine (Node _ RuX  [])      = []
spine (Node _ RuL  [dA,dK]) = toLExp dA : spine dK
spine (Node _ RuL' [dA,dK]) = toLExp dA : spine dK
spine d = error ("spine: not a left-focused derivation: " ++ show d)

-- ------------------------------------------------------------
-- printing types and sequents
-- ------------------------------------------------------------

-- Both divisions are right-associative with no relative precedence, so dropping the parentheses on the right would
-- still round-trip -- but "np \ (s / np)" is easier to read than "np \ s / np", and it matches how the lexicon files write their types.
showLTp :: LTp -> String
showLTp (Atm p)    = p
showLTp (DivL a b) = showFactor a ++ " \\ " ++ showFactor b
showLTp (DivR b a) = showFactor b ++ " / " ++ showFactor a

showFactor :: LTp -> String
showFactor (Atm p) = p
showFactor t       = "(" ++ showLTp t ++ ")"

showCtx :: Ctx -> String
showCtx gamma = intercalate ", " [ x ++ ":" ++ showLTp a | (x,a) <- gamma ]

showSequent :: Sequent -> String
showSequent (Rinv gamma b) = showCtx gamma ++ " --> " ++ showLTp b
showSequent (Lfoc gammaL a gammaR p) =
  concat [ left, "[" ++ showLTp a ++ "]", right, " --> ", p ]
  where
    left  = if null gammaL then "" else showCtx gammaL ++ " "
    right = if null gammaR then "" else " " ++ showCtx gammaR

showRule :: Rule -> String
showRule RuX      = "X"
showRule (RuR _)  = "R"
showRule (RuR' _) = "R'"
showRule (RuF x)  = "F " ++ x
showRule RuL      = "L"
showRule RuL'     = "L'"

-- -----------------------------------------------------------
-- printing a derivation as a proof tree
-- -----------------------------------------------------------

prettyDeriv :: Deriv -> String
prettyDeriv = unlines . map stripEnd . block
  where stripEnd = reverse . dropWhile (== ' ') . reverse

printDeriv :: Deriv -> IO ()
printDeriv = putStr . prettyDeriv

-- Render a derivation as a block of lines, premises above a labelled bar and the conclusion centred underneath.
block :: Deriv -> [String]
block (Node s r ds) = map (center width) (above ++ [bar, concl])
  where
    concl = showSequent s
    above = sideBySide (map block ds)
    -- the bar spans the wider of the premises and the conclusion
    inner = maximum (map length (concl : above))
    bar   = replicate inner '-' ++ "  " ++ showRule r
    width = maximum (map length (bar : concl : above))

-- place blocks next to each other so that their conclusions all sit on the same line
sideBySide :: [[String]] -> [String]
sideBySide []     = []
sideBySide blocks = map (intercalate "   ") (transpose padded)
  where
    height = maximum (map length blocks)
    padded = [ pad b | b <- blocks ]
    pad b  = replicate (height - length b) (replicate (blockWidth b) ' ')
             ++ [ padTo (blockWidth b) l | l <- b ]
    blockWidth b = maximum (0 : map length b)

padTo :: Int -> String -> String
padTo n s = s ++ replicate (n - length s) ' '

center :: Int -> String -> String
center n s = replicate left ' ' ++ s
  where left = (n - length s) `div` 2
