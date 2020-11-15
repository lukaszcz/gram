module Prop.Search where
{-
   Intuitionistic propositional logic: proof search
-}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Grammar
import qualified Search
import Prop hiding (Term)

data Eliminator = EApp | EProj Int

-- | Eliminator chain
data Elim a = Elim {
      target :: a
    , subgoals :: [Formula]
    , var :: Int
    , elims :: [Eliminator]
    }

type ElimAtom = Elim Int
type ElimDisj = Elim [Formula]

data Context = Context {
      lastBindingNum :: Int
    , elimAtom :: IntMap [ElimAtom]
    , elimDisj :: [ElimDisj]
    }

data Nonterminal = Nonterminal !Formula !Context

data PropGrammar a = PropGrammar a Context
type PropTerm a = Grammar.DTerm a Nonterminal

mkPropTerm :: Context -> [Formula] -> ([a] -> a) -> PropTerm a
mkPropTerm ctx holes fill = Grammar.DTerm {
                                Grammar.dtSize = 1
                              , Grammar.dtHolesNum = length holes
                              , Grammar.dtHoles = map (\x -> Nonterminal x ctx) holes
                              , Grammar.dtFill = fill
                              }

applyElim :: TermSig a => Context -> Elim b -> PropTerm a
applyElim ctx e = mkPropTerm ctx (subgoals e) fill
    where
      fill l = mkargs (app (tVar (var e))) (elims e) l []
      mkargs h [] l acc = h (reverse acc)
      mkargs h (EApp:es) (x:l) acc = mkargs h es l (x:acc)
      mkargs h (EProj k:es) l acc = mkargs (app (tProj k (h (reverse acc)))) es l []
      app x [] = x
      app x l = tApp x l

expandAtom :: TermSig a => Context -> Int -> [PropTerm a]
expandAtom ctx a =
    case IntMap.lookup a (elimAtom ctx) of
      Just l -> map (applyElim ctx) l
      Nothing -> []
