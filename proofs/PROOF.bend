import Base
import ./ITERATOR_COMPONENT_PROOF.bend as IteratorComponents
import ./TREE_MAP_COMPONENT_PROOF.bend as TreeMapComponents
import ./END_TO_END.bend as End
import ./MATH_PROOF.bend as Math
import ./hash_table.bend as HashTable
import ./lru.bend as Lru
import ./doubly_linked_list.bend as Dll
import ./tree_map.bend as TreeMap

# Root gate. Checks END_TO_END.bend (and through it every proofs/<id>.bend
# entry), the math library, the refinements of the hash map, the LRU cache,
# the doubly linked list and the indexed TreeMap, and the TreeMap's component
# laws.
