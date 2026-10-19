{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lambek where

import LTypes

dec_rinv :: [LTp] -> LTp -> Bool
dec_rinv gamma b = undefined

dec_lfoc :: [LTp] -> LTp -> [LTp] -> Atm -> Bool
dec_lfoc gammaL a gammaR p = undefined

isGrammatical :: Lexicon sem -> [String] -> Bool
isGrammatical lex ws = undefined

