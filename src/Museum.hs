-- | Signature for the 'Proof' typeclass
data ProofSig a = ProofSig {
      refinep :: a -> [a]
    , finalp :: a -> Bool
    , prunep :: a -> Maybe a
    }

data ProofStruct a = ProofStruct {
      sigp :: ProofSig a
    , proof :: a
    }

instance Eq a => Eq (ProofStruct a) where
    x == y = proof x == proof y

instance Ord a => Ord (ProofStruct a) where
    compare x y = compare (proof x) (proof y)

instance Proof a => Proof (ProofStruct a) where
    refine p = map (\x -> ProofStruct (sigp p) x) (refinep (sigp p) (proof p))
    final p = finalp (sigp p) (proof p)
    prune p = do
      x <- prunep (sigp p) (proof p)
      return $ ProofStruct (sigp p) x
