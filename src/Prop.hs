{-# LANGUAGE MultiParamTypeClasses #-}
module Prop where
{-
   Intuitionistic propositional logic: formulas and proof terms
-}

import Logic

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

toPFormula :: Formula -> PFormula ()
toPFormula (Atom i) = PAtom i ()
toPFormula (Impl as tau) = PImpl (map (toElim 0) as) (toPFormula tau)
toPFormula (And as) = PAnd (map toPFormula as)
toPFormula (Or as) = POr (map toPFormula as)

-- | 'toElim v tau' creates the list of eliminator chains associated
-- with the declaration (Var v) : tau
toElim :: Int -> Formula -> [Elim ()]
toElim v (Impl gs (Atom i)) = [Elim { target = PAtom i ()
                                       , subgoals = map toPFormula gs
                                       , var = v
                                       , elims = []
                                       , exVarsNum = 0 }]
toElim v (Impl gs (Or l)) = [Elim { target = POr (map toPFormula l)
                                  , subgoals = map toPFormula gs
                                  , var = v
                                  , elims = []
                                  , exVarsNum = 0 }]
toElim v tau = mkelim tau [] []
    where
      mkelim :: Formula -> [PFormula ()] -> [Eliminator] -> [Elim ()]
      mkelim tau@(Atom _) gs es = [Elim { target = toPFormula tau
                                        , subgoals = reverse gs
                                        , var = v
                                        , elims = reverse es
                                        , exVarsNum = 0 }]
      mkelim tau@(Or _) gs es = [Elim { target = toPFormula tau
                                      , subgoals = reverse gs
                                      , var = v
                                      , elims = reverse es
                                      , exVarsNum = 0 }]
      mkelim (Impl l tau) gs es =
          mkelim tau (reverse (map toPFormula l) ++ gs) (replicate (length l) EApp)
      mkelim (And l) gs es =
          concatMap (\(tau, k) -> mkelim tau gs (EProj k:es)) (zip l [0..])

instance PGenerator ProofTerm () where
    fillElimAtom ctx e l =
        let h = Var (lastPrfBinderNum ctx - var e) in
        if elims e == [] then
            app h l
        else
            mkargs (app h) (elims e) l []
        where
          mkargs h [] l acc = h (reverse acc)
          mkargs h (EApp:es) (x:l) acc = mkargs h es l (x:acc)
          mkargs h (EProj k:es) l acc = mkargs (app (Proj k (h (reverse acc)))) es l []
          app x [] = x
          app x l = App x l
    fillImpl ctx n [x] = iterate Lam x !! n
    fillAnd ctx = Tuple
    fillDisj ctx i [x] = Inj i x
