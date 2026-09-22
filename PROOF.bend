import Base
import ./ITERATOR_COMPONENT_PROOF.bend as IteratorComponents
import ./END_TO_END.bend as End

# Single proof root: checks END_TO_END.bend (all public laws) and, through it,
# every proofs/<id>.bend entry, proofs/lru.bend and the retained LRU closure.
