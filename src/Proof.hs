module Proof where

-- | 'ProofSig' contains operations on a proof tree specified by an
-- abstract proof grammar
data ProofSig g = ProofSig {
      -- | Expand some nonterminals in the given proof tree.
      refine :: g -> g
      -- | Are there no nonterminals in the proof tree?
    , final :: g -> Bool
      -- | Perform (partial) post-processing. Return 'None' if the
      -- argument is filtered-out by the post-processing.
    , prune :: g -> Maybe g
    }
