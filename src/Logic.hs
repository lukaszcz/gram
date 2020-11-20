{-# LANGUAGE MultiParamTypeClasses #-}
module Logic where
{-
   Generic logic for IPL-based proof search
-}

class Prunable c where
    prune :: c -> Maybe c

class (Prunable c, Monoid c) => PConstraints c a where
    addConstraint :: c -> a -> a -> Maybe c

type PFill p = [p] -> p

class PFiller p where
    -- | 'fillImpl n' where 'n' is the number of antecedents
    fillImpl :: Int -> PFill p
    fillAnd :: PFill p
    -- | 'fillDisj n' where 'n' is the number of disjuncts
    fillDisj :: Int -> PFill p

-- | A typeclass of proof generators: 'p' is the type of generated
-- proofs, 'a' is the type of atoms
class PFiller p => PGenerator p a where
    -- | 'fillElimAtom lastBinder e'
    fillElimAtom :: Int -> Elim a -> PFill p
    -- | 'fillElimDisj lastBinder e'; the holes corresponding to the
    -- eliminator subgoals are at the front of the holes list, the
    -- remaining holes correspond to case branches
    fillElimDisj :: Int -> Elim a -> PFill p

-- | Formulas: 'a' is the type of atoms
data PFormula a = PAtom Int a
                | PImpl [[Elim a]] (PFormula a)
                | PAnd [PFormula a]
                | POr [PFormula a]
                | PEx Int (PFormula a)

-- | The eliminator chain target is an atom or a disjunction
data ETarget a = TAtom Int a | TDisj [[Elim a]]

-- | Eliminator chain
data Elim a = Elim {
      target :: !(ETarget a)
    , subgoals :: ![PFormula a]
    , var :: !Int
    , elims :: ![Eliminator]
    -- ^ 'elims' optimisation: empty list means only EApp
    , exVarsNum :: !Int
    }

data Eliminator = EApp | EProj Int deriving Eq

targetAtom :: Elim a -> a
targetAtom e = case target e of
                 TAtom _ a -> a
                 TDisj _ -> error "expected an atom in eliminator chain target"

targetDisj :: Elim a -> [[Elim a]]
targetDisj e = case target e of
                 TAtom _ _ -> error "expected a disjunction in eliminator chain target"
                 TDisj l -> l
