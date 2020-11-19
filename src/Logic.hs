{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Logic where
{-
   Generic logic for IPL-based proof search
-}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

class Prunable c where
    prune :: c -> Maybe c

class (Prunable c, Monoid c) => PConstraints c a where
    addConstraint :: c -> a -> a -> Maybe c

type PFill p = [p] -> p

class PGenerator p a where
    fillElimAtom :: Context a -> Elim a -> PFill p
    fillImpl :: Context a -> Int -> PFill p
    fillAnd :: Context a -> PFill p
    fillDisj :: Context a -> Int -> PFill p

data PFormula a = PAtom Int a
                | PImpl [[Elim a]] (PFormula a)
                | PAnd [PFormula a]
                | POr [PFormula a]
                | PEx Int (PFormula a)

-- | Eliminator chain
data Elim a = Elim {
      -- | The target is an atom or a disjunction
      target :: !(PFormula a)
    , subgoals :: ![PFormula a]
    , var :: !Int
    , elims :: ![Eliminator]
    -- ^ optimisation: empty list means only EApp
    , exVarsNum :: !Int
    }

data Eliminator = EApp | EProj Int deriving Eq

data PCmd = PElimAtom Int | PElimDisj | PIntros | PSplit

data Context a = Context {
      lastPrfBinderNum :: Int
    , elimAtom :: IntMap [Elim a]
    , elimDisj :: [Elim a]
    , lastExBinderNum :: Int
    , lastCmd :: !PCmd
    }

extendContext :: Context a -> [Elim a] -> Context a
extendContext ctx es =
    (foldl updateContext ctx es){ lastPrfBinderNum = lastPrfBinderNum ctx + 1 }
    where
      updateContext :: Context a -> Elim a -> Context a
      updateContext ctx e =
          case target e of
            PAtom i _ -> ctx{ elimAtom = newElimAtom }
                where
                  newElimAtom =
                      case IntMap.lookup i (elimAtom ctx) of
                        Just l -> IntMap.insert i (e:l) (elimAtom ctx)
                        Nothing -> IntMap.insert i [e] (elimAtom ctx)
            _ -> ctx{ elimDisj = e : elimDisj ctx }

emptyContext :: Context a
emptyContext = Context {
                 lastPrfBinderNum = -1
               , elimAtom = IntMap.empty
               , elimDisj = []
               , lastExBinderNum = -1
               , lastCmd = PIntros
               }
