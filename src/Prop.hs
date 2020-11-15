module Prop where
{- Intuitionistic propositional logic
-}

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Grammar

data Formula = Atom Int
             | And [Formula]
             | Or [Formula]
             | Impl [Formula] Formula

-- | Proof terms in de Bruijn representation
data Term = Var Int
          | App Term Term
          | Proj Int Term
          | Lam Term
          | Case [Term]
          -- ^ 'case t : A_1 \/ .. \/ A_n of x_1 => t_1 | .. | x_n => t_n' -->
          -- 'Case [Lam t_1, .., Lam t_n]'
          | Let Term Term
          -- ^ 'let x = t in u' --> 'Let t (Lam u)'

data TermSig a = TermSig {
      tVar :: Int -> a
    , tApp :: a -> [a] -> a
    , tProj1 :: a -> a
    , tProj2 :: a -> a
    , tLam :: a -> a
    , tCase :: [a] -> a
    , tLet :: a -> a -> a
    }

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
      bindingsNum :: Int
    , elimAtom :: IntMap ElimAtom
    , elimDisj :: [ElimDisj]
    }

data Nonterminal = Nonterminal {
      goal :: Formula
    , context :: Context
    }

type PropTerm a = Grammar.DTerm TermSig a
