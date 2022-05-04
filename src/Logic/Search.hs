{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Logic.Search (SearchOpts(..), defaultSearchOpts, search) where
{-|
  Generic proof search based on IPL proof search
 -}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import Data.Foldable
import qualified Search
import Grammar
import Logic

data SearchOpts = SearchOpts {
      soRefineAll :: Bool
    }

defaultSearchOpts :: SearchOpts
defaultSearchOpts = SearchOpts {
                      soRefineAll = False
                    }

search :: (Ord a, PConstraints c a, PGenerator p a) =>
          SearchOpts -> c -> PFormula a -> [p]
search opts c x = map (\x -> dtFill x []) (Search.search opts (startPTerm c x))

--------------------------------------------------------------------------------------

instance (PConstraints c a, PGenerator p a) =>
    Grammar SearchOpts (DTerm c p) (Nonterminal a) where
  expand _ (Nonterminal cmd ctx (PAtom i a)) = expandAtom cmd ctx i a
  expand _ (Nonterminal _ ctx (PImpl es tau)) = [expandImpl ctx es tau]
  expand _ (Nonterminal cmd ctx (PAnd cs)) = [expandAnd cmd ctx cs]
  expand _ (Nonterminal cmd ctx (POr ds)) = expandOr cmd ctx ds

instance (PConstraints c a, PGenerator p a) => Search.Proof SearchOpts (PTerm c p a) where
    refine g = if soRefineAll g then refineAll g else refineFirst g
    final _ x = dtHolesNum x == 0
    prune _ x =
        case prune (dtConstraints x) of
          Just c' -> Just $! x{ dtConstraints = c' }
          Nothing -> Nothing

--------------------------------------------------------------------------------------

data Context a = Context {
      lastPrfBinderNum :: !Int
    , lastExBinderNum :: !Int
    , elimAtom :: IntMap [Elim a]
    , elimDisj :: [Elim a]
    }

emptyContext :: Context a
emptyContext = Context {
                 lastPrfBinderNum = -1
               , lastExBinderNum = -1
               , elimAtom = IntMap.empty
               , elimDisj = []
               }

-- | 'extendContext ctx es' adds the eliminator chains in 'es' to the
-- context, assigning the next bound variable number
-- ('lastExBinderNum' + 1) to *each* of them; 'lastExBinderNum' gets
-- increased by 1.
extendContext :: Context a -> [Elim a] -> Context a
extendContext ctx es =
    (foldl' updateContext ctx es){ lastPrfBinderNum = v }
    where
      v = lastPrfBinderNum ctx + 1
      updateContext :: Context a -> Elim a -> Context a
      updateContext ctx e =
          case target e' of
            TAtom i _ -> ctx{ elimAtom = newElimAtom }
                where
                  newElimAtom =
                      case IntMap.lookup i (elimAtom ctx) of
                        Just l -> IntMap.insert i (e':l) (elimAtom ctx)
                        Nothing -> IntMap.insert i [e'] (elimAtom ctx)
            _ -> ctx{ elimDisj = e' : elimDisj ctx }
          where
            e' = e{var = v}

data PCmd = PElim !Int | PIntros | PInj

-- | 'Nonterminal lastCmd context goal'
data Nonterminal a = Nonterminal !PCmd !(Context a) !(PFormula a)

type PTerm c p a = DTerm c p (Nonterminal a)

mkPTerm :: PConstraints c a =>
           [Nonterminal a] -> c -> PFill p -> PTerm c p a
mkPTerm holes c fill = DTerm {
                         dtSize = 1
                       , dtHolesNum = length holes
                       , dtHoles = holes
                       , dtFill = fill
                       , dtConstraints = c
                       }

mkHoles :: PCmd -> Context a -> [PFormula a] -> [Nonterminal a]
mkHoles cmd ctx = map (Nonterminal cmd ctx)

startPTerm :: PConstraints c a => c -> PFormula a -> PTerm c p a
startPTerm c x = mkPTerm [Nonterminal PIntros emptyContext x] c head

updateElimCtx :: Context a -> Elim a -> Context a
updateElimCtx ctx e = if exVarsNum e == 0 then
                          ctx
                      else
                          ctx{lastExBinderNum = lastExBinderNum ctx + exVarsNum e}

applyElimAtom :: (PConstraints c a, PGenerator p a) =>
                 Context a -> a -> Elim a -> Maybe (PTerm c p a)
applyElimAtom ctx a e =
    case addConstraint mempty a (targetAtom e) of
      Just c -> Just $! mkPTerm holes c fill
          where
            holes = mkHoles (PElim (var e)) (updateElimCtx ctx e) (subgoals e)
            fill = fillElimAtom (lastPrfBinderNum ctx) e
      Nothing -> Nothing

applyElimDisj :: (PConstraints c a, PGenerator p a) =>
                 Context a -> PFormula a -> Elim a -> PTerm c p a
applyElimDisj ctx goal e = mkPTerm holes mempty fill
    where
      holes = mkHoles (PElim (var e)) uctx (subgoals e) ++
              map (\ctx' -> Nonterminal PIntros ctx' goal) ctxs
      fill = fillElimDisj (lastPrfBinderNum ctx) e
      uctx = updateElimCtx ctx e
      ctxs = map (extendContext uctx) elims
      elims = targetDisj e

applyAllElimDisj :: (PConstraints c a, PGenerator p a) =>
                    PCmd -> Context a -> PFormula a -> [PTerm c p a]
applyAllElimDisj PIntros ctx goal = map (applyElimDisj ctx goal) (elimDisj ctx)
applyAllElimDisj _ _ _ = []

expandAtom :: (PConstraints c a, PGenerator p a) =>
              PCmd -> Context a -> Int -> a -> [PTerm c p a]
expandAtom cmd ctx i a = l1 ++ l2
    where
      l1 = case IntMap.lookup i (elimAtom ctx) of
             Just l -> mapMaybe (applyElimAtom ctx a) l
             Nothing -> []
      l2 = applyAllElimDisj cmd ctx (PAtom i a)

expandImpl :: (PConstraints c a, PGenerator p a) =>
              Context a -> [[Elim a]] -> PFormula a -> PTerm c p a
expandImpl ctx antecedents succedent = mkPTerm holes mempty (fillImpl $! n)
    where
      holes = [Nonterminal PIntros ctx' succedent]
      n = length antecedents
      ctx' = foldl' extendContext ctx antecedents

expandAnd :: (PConstraints c a, PGenerator p a) =>
             PCmd -> Context a -> [PFormula a] -> PTerm c p a
expandAnd cmd ctx conjuncts = mkPTerm (mkHoles cmd ctx conjuncts) mempty fillAnd

expandDisj :: (PConstraints c a, PGenerator p a) =>
              Context a -> Int -> PFormula a -> PTerm c p a
expandDisj ctx i tau = mkPTerm [Nonterminal PInj ctx tau] mempty (fillDisj i)

expandOr :: (PConstraints c a, PGenerator p a) =>
            PCmd -> Context a -> [PFormula a] -> [PTerm c p a]
expandOr cmd ctx disjuncts = l1 ++ l2
    where
      l1 = zipWith (expandDisj ctx) [0..] disjuncts
      l2 = applyAllElimDisj cmd ctx (POr disjuncts)
