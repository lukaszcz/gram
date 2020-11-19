{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Logic.Search where
{-
   Generic proof search based on IPL proof search
-}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import qualified Search
import Grammar
import Logic

data SearchOpts = SearchOpts {
      soRefineAll :: Bool
    }

instance (PConstraints c a, PGenerator p a) =>
    Grammar SearchOpts (DTerm c p) (Nonterminal a) where
  expand _ (Nonterminal ctx (PAtom i a)) = expandAtom ctx i a
  expand _ (Nonterminal ctx (PImpl es tau)) = [expandImpl ctx es tau]
  expand _ (Nonterminal ctx (PAnd cs)) = [expandAnd ctx cs]
  expand _ (Nonterminal ctx (POr ds)) = expandOr ctx ds

instance (PConstraints c a, PGenerator p a) => Search.Proof SearchOpts (PTerm c p a) where
    refine g = if soRefineAll g then refineAll g else refineFirst g
    final _ x = dtHolesNum x == 0
    prune _ x =
        case prune (dtConstraints x) of
          Just c' -> Just $! x{ dtConstraints = c' }
          Nothing -> Nothing

search :: (Ord a, PConstraints c a, PGenerator p a) =>
          SearchOpts -> c -> PFormula a -> [p]
search opts c x = map (\x -> dtFill x []) (Search.search opts (startPTerm c x))

--------------------------------------------------------------------------------------

data Nonterminal a = Nonterminal {
      context :: !(Context a)
    , goal :: !(PFormula a)
    }

type PTerm c p a = DTerm c p (Nonterminal a)

mkPTerm :: PConstraints c a => Context a -> [PFormula a] -> c -> PFill p -> PTerm c p a
mkPTerm ctx holes c fill = DTerm {
                             dtSize = 1
                           , dtHolesNum = length holes
                           , dtHoles = map (Nonterminal ctx) holes
                           , dtFill = fill
                           , dtConstraints = c
                           }

startPTerm :: PConstraints c a => c -> PFormula a -> PTerm c p a
startPTerm c x = mkPTerm emptyContext [x] c head

mkConstraint :: PConstraints c a => a -> Elim a -> Maybe c
mkConstraint x e =
    case target e of
      PAtom _ y -> addConstraint mempty x y
      _ -> Just mempty

applyElimAtom :: (PConstraints c a, PGenerator p a) =>
                 Context a -> a -> Elim a -> Maybe (PTerm c p a)
applyElimAtom ctx a e =
    case mkConstraint a e of
      Just c -> Just $! mkPTerm ctx (subgoals e) c (fillElimAtom ctx e)
      Nothing -> Nothing

expandAtom :: (PConstraints c a, PGenerator p a) =>
              Context a -> Int -> a -> [PTerm c p a]
expandAtom ctx i a =
    case IntMap.lookup i (elimAtom ctx) of
      Just l -> mapMaybe (applyElimAtom ctx a) l
      Nothing -> []

expandImpl :: (PConstraints c a, PGenerator p a) =>
              Context a -> [[Elim a]] -> PFormula a -> PTerm c p a
expandImpl ctx antecedents succedent =
    mkPTerm ctx' [succedent] mempty (fillImpl ctx' $! n)
    where
      n = length antecedents
      elims = map (\(v,es) -> map (\e -> e{var = v}) es) $
              zip [lastPrfBinderNum ctx + 1..] antecedents
      ctx' = foldl extendContext ctx elims

expandAnd :: (PConstraints c a, PGenerator p a) =>
             Context a -> [PFormula a] -> PTerm c p a
expandAnd ctx conjuncts = mkPTerm ctx conjuncts mempty (fillAnd ctx)

expandDisj :: (PConstraints c a, PGenerator p a) =>
              Context a -> Int -> PFormula a -> PTerm c p a
expandDisj ctx i tau = mkPTerm ctx [tau] mempty (fillDisj ctx i)

expandOr :: (PConstraints c a, PGenerator p a) =>
            Context a -> [PFormula a] -> [PTerm c p a]
expandOr ctx disjuncts =
    map (uncurry (expandDisj ctx)) (zip [0..] disjuncts)
