import Base
import ./ITERATOR_COMPONENT_PROOF.bend as IteratorComponents
import ./TREE_MAP_COMPONENT_PROOF.bend as TreeMapComponents
import ./END_TO_END.bend as End

# Root includes partial indexed TreeMap component laws. Full indexed
# refinement is still missing, and the pre-existing deque migration fails.
# Checks END_TO_END.bend and, through it,
# every proofs/<id>.bend entry, proofs/lru.bend and the retained LRU closure.
