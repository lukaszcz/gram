{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Grammar where
{-
  Abstract context-free grammar interface.
 -}

import Utils

-- | 'a' is the type of nonterminals, 't' provides the structure of
-- generated elements
class Term t a where
    -- | List of holes - all nonterminals in the proof term.
    holes :: t a -> [a]
    -- | Number of holes.
    holesNum :: t a -> Int
    holesNum p = length (holes p)
    -- | Fills the holes with the given proof terms. Assumption: the
    -- number of terms provided is less or equal to the number of
    -- holes.
    fill :: t a -> [t a] -> t a
    -- | 'fillFirst p x' Fills the first hole in 'p' with 'x'
    fillFirst :: t a -> t a -> t a
    fillFirst p x = fill p [x]

class Term t a => Grammar g t a where
    -- | Expansion of a nonterminal - all possibilities
    expand :: g -> a -> [t a]

refineAll :: Grammar g t a => g -> t a -> [t a]
refineAll g p =
    map (fill p) $
    -- create all possible combinations
    foldr (\h acc -> h >>= \x -> map (x:) acc) [[]] $
    -- expand all holes
    map (expand g) (holes p)

refineFirst :: Grammar g t a => g -> t a -> [t a]
refineFirst g p =
    case holes p of
      (h:_) -> map (fillFirst p) (expand g h)
      [] -> [p]

-- | Delayed terms: terms represented by a list of holes and a
-- function which when supplied with the concrete terms for the holes
-- returns a concrete term representation of the delayed term.
data DTerm a b = DTerm {
      dtSize :: !Int
    , dtHolesNum :: !Int
    , dtHoles :: [b]
    , dtFill :: [a] -> a
    }

instance Term (DTerm a) b where
    holes = dtHoles
    holesNum = dtHolesNum
    fill p l = DTerm {
                 dtSize = dtSize p + sum (map dtSize l)
               , dtHolesNum = dtHolesNum p + length newHoles - filledHolesNum
               , dtHoles = newHoles ++ drop filledHolesNum (dtHoles p)
               , dtFill =
                   \l' ->
                       let ls = group (map dtHolesNum l) l'
                       in dtFill p (map (\(x,y) -> dtFill x y) (zip l ls))
               }
        where
          newHoles = concatMap dtHoles l
          filledHolesNum = length l
    fillFirst p x = DTerm {
                      dtSize = dtSize p + dtSize x
                    , dtHolesNum = dtHolesNum p + length newHoles - 1
                    , dtHoles = newHoles ++ tail (dtHoles p)
                    , dtFill =
                        \l' ->
                            let (l1, l2) = splitAt (dtHolesNum x) l'
                            in dtFill p (dtFill x l1 : l2)
                    }
        where
          newHoles = dtHoles x

-- | Priority comparison on delayed terms.
compareDTermPrio :: DTerm a b -> DTerm a b -> Ordering
compareDTermPrio x y =
    if dtHolesNum x == 0 then
        if dtHolesNum y > 0 then
            LT
        else
            compare (dtSize x) (dtSize y)
    else
        compare (4 * dtHolesNum x + dtSize x) (4 * dtHolesNum y + dtSize y)

instance Eq (DTerm a b) where
    x == y = compareDTermPrio x y == EQ

instance Ord (DTerm a b) where
    compare = compareDTermPrio
