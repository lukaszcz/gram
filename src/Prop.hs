module Prop where
{-
   Intuitionistic propositional logic: formulas and proof terms
-}

data Formula = Atom Int
             | Impl [Formula] Formula
             | And [Formula]
             | Or [Formula]

-- | Proof terms in zero-based de Bruijn representation
data ProofTerm = Var Int
               | App ProofTerm [ProofTerm]
               | Lam ProofTerm
               | Proj Int ProofTerm
               | Tuple [ProofTerm]
               | Case [ProofTerm]
               -- ^ 'case t : A_1 \/ .. \/ A_n of x_1 => t_1 | .. | x_n => t_n' -->
               -- 'Case [t_1, .., t_n]'
               | Inj Int ProofTerm
               | Let ProofTerm ProofTerm
               -- ^ 'let x = t in u' --> 'Let t u'

mapFormula :: (Formula -> Formula) -> Formula -> Formula
mapFormula f (Atom i) = f (Atom i)
mapFormula f (Impl l x) = f (Impl (map (mapFormula f) l) (mapFormula f x))
mapFormula f (And l) = f (And (map (mapFormula f) l))
mapFormula f (Or l) = f (Or (map (mapFormula f) l))

compressFormulaRoot :: Formula -> Formula
compressFormulaRoot (Impl l1 (Impl l2 x)) = compressFormulaRoot (Impl (l1 ++ l2) x)
compressFormulaRoot (And l) = And (concatMap expand l)
    where
      expand (And l) = concatMap expand l
      expand x = [x]
compressFormulaRoot (Or l) = Or (concatMap expand l)
    where
      expand (Or l) = concatMap expand l
      expand x = [x]
compressFormulaRoot x = x

compressFormula :: Formula -> Formula
compressFormula = mapFormula compressFormulaRoot
