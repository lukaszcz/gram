{-# LANGUAGE MultiParamTypeClasses #-}
module Search where
{-
  Searching for proof trees generated by an abstract grammar.
 -}

import qualified Data.PQueue.Min as PQueue
import Data.List

-- | 'Proof' is a typeclass of proof trees specified by an
-- abstract proof grammar g
class Proof g a where
    -- | Expand some nonterminals in the given proof tree.
    refine :: g -> a -> [a]
    -- | Are there no nonterminals in the proof tree?
    final :: g -> a -> Bool
    -- | Perform (partial) post-processing. Return 'None' if the
    -- argument is filtered-out by the post-processing.
    prune :: g -> a -> Maybe a

searchq :: (Ord a, Proof g a) => g -> PQueue.MinQueue a -> [a]
searchq g q =
    case PQueue.minView q of
      Just (p, q') ->
          case prune g p of
            Just p' ->
                let (l1, l2) = partition (final g) (refine g p')
                in l1 ++ searchq g (foldr PQueue.insert q' l2)
            Nothing ->
                searchq g q'
      Nothing ->
          []

search :: (Ord a, Proof g a) => g -> a -> [a]
search g p = searchq g (PQueue.insert p PQueue.empty)
