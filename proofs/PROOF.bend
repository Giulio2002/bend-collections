import Base
import ./ITERATOR_COMPONENT_PROOF.bend as IteratorComponents
import ./TREE_MAP_COMPONENT_PROOF.bend as TreeMapComponents
import ./END_TO_END.bend as End
import ./MATH_PROOF.bend as Math
import ./hash_table.bend as HashTable
import ./lru.bend as Lru

# Root gate. Checks END_TO_END.bend (and through it every proofs/<id>.bend
# entry), the math library, the hash map's and the LRU cache's refinements,
# and the partial
# indexed TreeMap component laws (its full refinement is still missing).
