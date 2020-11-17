{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Prop.Search where
{-
   Intuitionistic propositional logic: proof search
-}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Grammar
import Prop

data Eliminator = EApp | EProj Int

-- | Eliminator chain
data Elim = Elim {
      -- | The target is an atom or a disjunction
      target :: Formula
    , subgoals :: [Formula]
    , var :: Int
    , elims :: [Eliminator] -- TODO: optimisation - empty list means only EApp
    }

-- | 'mkElim v tau' creates the list of eliminator chains associated
-- with the declaration (Var v) : tau
mkElim :: Int -> Formula -> [Elim]
mkElim v tau = mkelim tau [] []
    where
      mkelim :: Formula -> [Formula] -> [Eliminator] -> [Elim]
      mkelim tau@(Atom _) gs es = [Elim { target = tau
                                      , subgoals = reverse gs
                                      , var = v
                                      , elims = reverse es }]
      mkelim tau@(Or _) gs es = [Elim { target = tau
                                    , subgoals = reverse gs
                                    , var = v
                                    , elims = reverse es }]
      mkelim (Impl l tau) gs es =
          mkelim tau ((reverse l) ++ gs) (replicate (length l) EApp)
      mkelim (And l) gs es =
          concatMap (\(tau, k) -> mkelim tau gs (EProj k:es)) (zip l [0..])

data Context = Context {
      lastBindingNum :: Int
    , elimAtom :: IntMap [Elim]
    , elimDisj :: [Elim]
    }

updateContext :: Context -> Elim -> Context
updateContext ctx e =
    case target e of
      Atom i -> ctx{ elimAtom = newElimAtom }
          where
            newElimAtom =
                case IntMap.lookup i (elimAtom ctx) of
                  Just l -> IntMap.insert i (e:l) (elimAtom ctx)
                  Nothing -> IntMap.insert i [e] (elimAtom ctx)
      _ -> ctx{ elimDisj = e : elimDisj ctx }

extendContext :: Context -> [Elim] -> Context
extendContext ctx es =
    (foldl updateContext ctx es){ lastBindingNum = lastBindingNum ctx + 1 }

data Nonterminal = Nonterminal !Context !Formula

type PTerm = Grammar.DTerm ProofTerm Nonterminal
type PFill = [ProofTerm] -> ProofTerm

mkPTerm :: Context -> [Formula] -> PFill -> PTerm
mkPTerm ctx holes fill = Grammar.DTerm {
                           Grammar.dtSize = 1
                         , Grammar.dtHolesNum = length holes
                         , Grammar.dtHoles = map (Nonterminal ctx) holes
                         , Grammar.dtFill = fill
                         }

fillElimAtom :: Context -> Elim -> PFill
fillElimAtom ctx e l = mkargs (app (Var (lastBindingNum ctx - var e))) (elims e) l []
    where
      mkargs h [] l acc = h (reverse acc)
      mkargs h (EApp:es) (x:l) acc = mkargs h es l (x:acc)
      mkargs h (EProj k:es) l acc = mkargs (app (Proj k (h (reverse acc)))) es l []
      app x [] = x
      app x l = App x l

applyElimAtom :: Context -> Elim -> PTerm
applyElimAtom ctx e = mkPTerm ctx (subgoals e) (fillElimAtom ctx e)

expandAtom :: Context -> Int -> [PTerm]
expandAtom ctx i =
    case IntMap.lookup i (elimAtom ctx) of
      Just l -> map (applyElimAtom ctx) l
      Nothing -> []

fillImpl :: Int -> PFill
fillImpl n [x] = iterate Lam x !! n

expandImpl :: Context -> [Formula] -> Formula -> PTerm
expandImpl ctx antecedents succedent = mkPTerm ctx' [succedent] (fillImpl $! n)
    where
      n = length antecedents
      elims = map (uncurry mkElim) (zip [lastBindingNum ctx + 1..] antecedents)
      ctx' = foldl extendContext ctx elims

fillAnd :: PFill
fillAnd = Tuple

expandAnd :: Context -> [Formula] -> PTerm
expandAnd ctx conjuncts = mkPTerm ctx conjuncts fillAnd

fillDisj :: Int -> PFill
fillDisj i [x] = Inj i x

expandDisj :: Context -> Int -> Formula -> PTerm
expandDisj ctx i tau = mkPTerm ctx [tau] (fillDisj i)

expandOr :: Context -> [Formula] -> [PTerm]
expandOr ctx disjuncts =
    map (uncurry (expandDisj ctx)) (zip [0..] disjuncts)

newtype PGrammar = PGrammar Int

instance Grammar.Grammar PGrammar (Grammar.DTerm ProofTerm) Nonterminal where
    expand g (Nonterminal ctx (Atom i)) = expandAtom ctx i
    expand g (Nonterminal ctx (Impl as tau)) = [expandImpl ctx as tau]
    expand g (Nonterminal ctx (And cs)) = [expandAnd ctx cs]
    expand g (Nonterminal ctx (Or ds)) = expandOr ctx ds
