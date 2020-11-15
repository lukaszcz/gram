module Prop where
{-
   Intuitionistic propositional logic: formulas and proof terms
-}

data Formula = Atom Int
             | And [Formula]
             | Or [Formula]
             | Impl [Formula] Formula

-- | Proof terms in de Bruijn representation
data Term = Var Int
          | App Term [Term]
          | Proj Int Term
          | Lam Term
          | Case [Term]
          -- ^ 'case t : A_1 \/ .. \/ A_n of x_1 => t_1 | .. | x_n => t_n' -->
          -- 'Case [Lam t_1, .., Lam t_n]'
          | Let Term Term
          -- ^ 'let x = t in u' --> 'Let t (Lam u)'

class TermSig a where
    tVar :: Int -> a
    tApp :: a -> [a] -> a
    tProj :: Int -> a -> a
    tLam :: a -> a
    tCase :: [a] -> a
    tLet :: a -> a -> a

instance TermSig Term where
    tVar = Var
    tApp = App
    tProj = Proj
    tLam = Lam
    tCase = Case
    tLet = Let
