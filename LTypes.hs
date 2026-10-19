module LTypes where

type Atm = String
data LTp = Atm Atm | DivL LTp LTp | DivR LTp LTp
  deriving (Show,Eq)

data Lexicon sem = Lexicon { items :: [(String,LTp,sem)] , stp :: LTp }
