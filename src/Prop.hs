{-# LANGUAGE MultiParamTypeClasses #-}
module Prop where
{-|
  Intuitionistic propositional logic: formulas and proof terms
 -}

import Logic

data Formula = Atom Int
             | Impl [Formula] Formula
             | And [Formula]
             -- ^ @top@ is represented by @And []@
             | Or [Formula]
             -- ^ @bottom@ is represented by @Or []@

-- | Proof terms in zero-based de Bruijn representation
data ProofTerm = Spine Int [ProofElim]
               | Lam Int ProofTerm
               | Tuple [ProofTerm]
               | Case Int [ProofElim] [ProofTerm]
               -- ^ @case (x u_1 .. u_m) : A_1 \/ .. \/ A_n of x_1 => t_1 | .. | x_n => t_n@ -->
               -- @Case x [u_1, .., u_m] [t_1, .., t_n]@
               | Inj Int ProofTerm

data ProofElim = App ProofTerm | Proj Int

mapProofTerm :: (Int -> ProofTerm -> ProofTerm) -> ProofTerm -> ProofTerm
mapProofTerm f t = pmap 0 t
    where
      pmap m (Spine j l) = f m (Spine j (map (pmapElim m) l))
      pmap m (Lam k x) = f m (Lam k (pmap (m + k) x))
      pmap m (Tuple l) = f m (Tuple (map (pmap m) l))
      pmap m (Case j l1 l2) = f m (Case j (map (pmapElim m) l1) (map (pmap m) l2))
      pmap m (Inj j x) = f m (Inj j (pmap m x))
      pmapElim m (App x) = App (pmap m x)
      pmapElim _ e = e

shiftBinders :: Int -> ProofTerm -> ProofTerm
shiftBinders n = mapProofTerm shift
    where
      shift m (Spine j l) = Spine (if j >= m then j + n else j) l
      shift m (Case j l1 l2) = Case (if j >= m then j + n else j) l1 l2
      shift _ x = x

mapFormula :: (Formula -> Formula) -> Formula -> Formula
mapFormula f (Atom i) = f (Atom i)
mapFormula f (Impl l x) = f (Impl (map (mapFormula f) l) (mapFormula f x))
mapFormula f (And l) = f (And (map (mapFormula f) l))
mapFormula f (Or l) = f (Or (map (mapFormula f) l))

toPFormula :: Formula -> PFormula ()
toPFormula (Atom i) = PAtom i ()
toPFormula (Impl as tau) = PImpl (map toElim as) (toPFormula tau)
toPFormula (And as) = PAnd (map toPFormula as)
toPFormula (Or as) = POr (map toPFormula as)

-- | @toElim tau@ creates the list of eliminator chains associated
-- with a declaration of @tau@; the 'var' field is set to 0
toElim :: Formula -> [Elim ()]
toElim (Impl gs (Atom i)) = [Elim { target = TAtom i ()
                                  , subgoals = map toPFormula gs
                                  , var = 0
                                  , elims = [] -- optimisation: [] means only EApp
                                  , exVarsNum = 0 }]
toElim (Impl gs (Or l)) = [Elim { target = TDisj (map toElim l)
                                , subgoals = map toPFormula gs
                                , var = 0
                                , elims = [] -- optimisation: [] means only EApp
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

mkSpine :: [Eliminator] -> [ProofTerm] -> [ProofElim]
mkSpine [] [] = []
mkSpine (EApp:l1) (x:l2) = App x : mkSpine l1 l2
mkSpine (EProj j:l1) l2 = Proj j : mkSpine l1 l2
mkSpine _ _ = error "bad spine"

instance PFiller ProofTerm where
    fillImpl n l = Lam n (head l)
    fillAnd = Tuple
    fillDisj i l = Inj i (head l)

instance PGenerator ProofTerm () where
    fillElimAtom lastBinder e l = Spine (lastBinder - var e) (mkSpine (elims e) l)
    fillElimDisj lastBinder e l = Case (lastBinder - var e) (mkSpine (elims e) l1) l2
        where
          (l1, l2) = splitAt n l
          n = length (subgoals e)
