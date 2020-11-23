{-# LANGUAGE MultiParamTypeClasses #-}
module Prop where
{-
   Intuitionistic propositional logic: formulas and proof terms
-}

import Logic

data Formula = Atom Int
             | Impl [Formula] Formula
             | And [Formula]
             -- ^ top is represented by @And []@
             | Or [Formula]
             -- ^ bottom is represented by @Or []@

-- | Proof terms in zero-based de Bruijn representation
data ProofTerm = Var Int
               | App ProofTerm [ProofTerm]
               | Lam Int ProofTerm
               | Proj Int ProofTerm
               | Tuple [ProofTerm]
               | Case ProofTerm [ProofTerm]
               -- ^ 'case t : A_1 \/ .. \/ A_n of x_1 => t_1 | .. | x_n => t_n' -->
               -- 'Case t [t_1, .., t_n]'
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

toPFormula :: Formula -> PFormula ()
toPFormula (Atom i) = PAtom i ()
toPFormula (Impl as tau) = PImpl (map toElim as) (toPFormula tau)
toPFormula (And as) = PAnd (map toPFormula as)
toPFormula (Or as) = POr (map toPFormula as)

-- | 'toElim tau' creates the list of eliminator chains associated
-- with a declaration of 'tau'; the 'var' field is set to 0
toElim :: Formula -> [Elim ()]
toElim (Impl gs (Atom i)) = [Elim { target = TAtom i ()
                                  , subgoals = map toPFormula gs
                                  , var = 0
                                  , elims = []
                                  , exVarsNum = 0 }]
toElim (Impl gs (Or l)) = [Elim { target = TDisj (map toElim l)
                                , subgoals = map toPFormula gs
                                , var = 0
                                , elims = []
                                , exVarsNum = 0 }]
toElim tau = mkelim tau [] []
    where
      mkelim :: Formula -> [PFormula ()] -> [Eliminator] -> [Elim ()]
      mkelim (Atom i) gs es = [Elim { target = TAtom i ()
                                    , subgoals = reverse gs
                                    , var = 0
                                    , elims = reverse es
                                    , exVarsNum = 0 }]
      mkelim (Or l) gs es = [Elim { target = TDisj (map toElim l)
                                  , subgoals = reverse gs
                                  , var = 0
                                  , elims = reverse es
                                  , exVarsNum = 0 }]
      mkelim (Impl l tau) gs es =
          mkelim tau (reverse (map toPFormula l) ++ gs) (replicate (length l) EApp ++ es)
      mkelim (And l) gs es =
          concatMap (\(tau, k) -> mkelim tau gs (EProj k:es)) (zip l [0..])

mkElimArgs :: ProofTerm -> [Eliminator] -> [ProofTerm] -> ProofTerm
mkElimArgs h elims l =
    if elims == [] then
        app h l
    else
        mkargs (app h) elims l []
    where
      mkargs h [] _ acc = h (reverse acc)
      mkargs _ (EApp:_) [] _ = undefined -- lengths are supposed to be equal
      mkargs h (EApp:es) (x:l) acc = mkargs h es l (x:acc)
      mkargs h (EProj k:es) l acc = mkargs (app (Proj k (h (reverse acc)))) es l []
      app x [] = x
      app x l = App x l

instance PFiller ProofTerm where
    fillImpl n l = Lam n (head l)
    fillAnd = Tuple
    fillDisj i l = Inj i (head l)

instance PGenerator ProofTerm () where
    fillElimAtom lastBinder e = mkElimArgs (Var (lastBinder - var e)) (elims e)
    fillElimDisj lastBinder e l = Case h l2
        where
          (l1, l2) = splitAt n l
          h = mkElimArgs (Var (lastBinder - var e)) (elims e) l1
          n = length (subgoals e)
