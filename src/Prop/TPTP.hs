module Prop.TPTP(parse, parseText, parseHandle, parseFile, TPTPState(..)) where
{-|
  Convert TPTP format to propositional formulas
 -}

import System.IO (Handle)
import Data.Text (Text)
import Prop
import TPTP (FormulaSig(..), TPTPState(..))
import qualified TPTP

struct :: FormulaSig () Formula
struct = FormulaStruct {
           tVar = \_ _ -> error "not a propositional formula"
         , tFun = \_ _ _ -> error "not a propositional formula"
         , tPred = \_ i _ -> Atom i
         , tEqual = \_ _ -> error "not a propositional formula"
         , tTrue = And []
         , tFalse = Or []
         , tNeg = \x -> Impl [x] (Or [])
         , tImpl = \x y -> Impl [x] y
         , tAssume = Impl
         , tAnd = \x y -> And [x, y]
         , tOr = \x y -> Or [x, y]
         , tAll = \_ _ -> error "not a propositional formula"
         , tEx = \_ _ -> error "not a propositional formula"
         }

parse :: String -> IO (Formula, TPTPState)
parse = TPTP.parse struct

parseText :: Text -> IO (Formula, TPTPState)
parseText = TPTP.parseText struct

parseHandle :: Handle -> IO (Formula, TPTPState)
parseHandle = TPTP.parseHandle struct

parseFile :: FilePath -> IO (Formula, TPTPState)
parseFile = TPTP.parseFile struct
