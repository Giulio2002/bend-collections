import Base
import ./containers/dlist_iterator/proof.bend as IteratorComponents
import ./containers/balanced_search_tree/components.bend as TreeMapComponents
import ./END_TO_END.bend as End
import ./math/proof.bend as Math
import ./containers/hash_table/proof.bend as HashTable
import ./containers/lru/proof.bend as Lru
import ./containers/doubly_linked_list/proof.bend as Dll
import ./containers/balanced_search_tree/proof.bend as TreeMap

# Root gate. Checks END_TO_END.bend (and through it every proofs/<id>.bend
# entry), the math library, the refinements of the hash map, the LRU cache,
# the doubly linked list and the indexed TreeMap, and the TreeMap's component
# laws.
