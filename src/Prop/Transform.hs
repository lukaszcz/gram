module Prop.Transform where
{-|
  Tranformations of propositional formulas and proofs.
 -}

import Data.Foldable
import Prop

data Transformer = Transformer {
      transform :: Formula -> Formula
      -- | @reconstr phi p@ converts the proof @p@ of @transform phi@
      -- into a proof of @phi@
    , reconstr :: Formula -> ProofTerm -> ProofTerm
    }

compressTransformer :: Transformer
compressTransformer = Transformer {
                        transform = compressFormula
                      , reconstr = decompressProof []
                      }

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

data Tree a = Leaf a | Node [Tree a]

getLeaf :: Int -> Tree a -> (a, [Int])
getLeaf 0 (Leaf a) = (a, [])
getLeaf k (Node l) = case get 0 l k of
                       Left p -> p
                       Right _ -> error "getLeaf"
    where
      -- get j l k: j - how many children already processes; l - list
      -- of remaining children; k - index; returns: Left (element,
      -- path) or Right (index into the rest of the tree)
      get :: Int -> [Tree a] -> Int -> Either (a, [Int]) Int
      get _ [] k = Right k
      get j ((Node l'):l) k = case get 0 l' k of
                                Left (x, p) -> Left (x, j:p)
                                Right k' -> get (j+1) l k'
      get j ((Leaf x):l) k =
          if k == 0 then
              Left (x, [j])
          else
              get (j+1) l (k-1)
getLeaf _ _ = error "getLeaf: out of scope"

zipTreeList :: (a -> b -> c) -> ([c] -> c) -> Tree a -> [b] -> (c, [b])
zipTreeList f1 _ (Leaf x) (y:ys) = (f1 x y, ys)
zipTreeList _ _ (Leaf _) [] = error "zipTreeList"
zipTreeList f1 f2 (Node l) ys = (f2 xs', ys')
    where
      (xs', ys') = foldl' zipper ([], ys) l
      zipper p@(_, []) _ = p
      zipper (xs, ys) t = (x:xs, ys')
          where (x, ys') = zipTreeList f1 f2 t ys

toOrTree :: Formula -> Tree Formula
toOrTree (Or l) = Node $ map toOrTree l
toOrTree x = Leaf x

toAndTree :: Formula -> Tree Formula
toAndTree (And l) = Node $ map toAndTree l
toAndTree x = Leaf x

decompressProof :: [Formula] -> Formula -> ProofTerm -> ProofTerm
decompressProof env (Impl l x) (Lam k p) =
    if n == k then
        Lam n (decompressProof env' x p)
    else
        Lam n (decompressProof env' x (Lam (k - n) p))
    where
      n = length l
      env' = (reverse l) ++ env
decompressProof env ty@(And _) (Tuple l) =
    fst $ zipTreeList (decompressProof env) Tuple (toAndTree ty) l
decompressProof env ty@(Or _) (Inj k z) = foldl' (flip Inj) z' path
    where
      (ty', path) = getLeaf k (toOrTree ty)
      z' = decompressProof env ty' z
decompressProof env _ (Case i l1 l2) =
    (fst $ zipTreeList (\x y n -> shiftBinders n (decompressProof env x y))
             (\fs n -> (if n == 0 then Case i l' else Case 0 []) (map (\f -> f (n+1)) fs))
             (toOrTree target) l2) 0
    where
      ty = env !! i
      l' = decompressSpine env ty l1
      target = spineTarget ty l1
decompressProof env _ (Spine i l) = Spine i (decompressSpine env (env !! i) l)
decompressProof _ _ _ = error "proof not in focused normal form"

decompressSpine :: [Formula] -> Formula -> [ProofElim] -> [ProofElim]
decompressSpine _ _ [] = []
decompressSpine env (Impl tys ty) l =
    zipWith decompApp tys l ++ decompressSpine env ty (drop (length tys) l)
    where
      decompApp ty (App x) = App (decompressProof env ty x)
      decompApp _ _ = error "bad spine"
decompressSpine env ty ((Proj k):l) = map Proj path ++ decompressSpine env ty' l
    where
      (ty', path) = getLeaf k (toAndTree ty)
decompressSpine _ _ _ = error "bad spine"

spineTarget :: Formula -> [ProofElim] -> Formula
spineTarget ty [] = ty
spineTarget (Impl tys ty) l = spineTarget ty (drop (length tys) l)
spineTarget ty ((Proj k):l) = spineTarget ty' l
    where
      (ty', _) = getLeaf k (toAndTree ty)
spineTarget _ _ = error "bad spine"
