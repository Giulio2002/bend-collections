import Base

# bend-collections-laws-containers: the proved laws of bend-collections' containers, the shared proof library and the whole-library roots (END_TO_END, PROOF).
# Importing this file checks every proof root below; see docs/*_CONTRACTS.md
# for what each clause states and what is not proved. Part of
# bend-collections-laws (laws.bend imports all three parts by name).

import ./proofs/END_TO_END.bend as ENDTOEND
import ./proofs/PROOF.bend as PROOF
import ./proofs/containers/balanced_search_tree/components.bend as ContainersBalancedSearchTreeComponents
import ./proofs/containers/balanced_search_tree/proof.bend as ContainersBalancedSearchTreeProof
import ./proofs/containers/balanced_search_tree/range.bend as ContainersBalancedSearchTreeRange
import ./proofs/containers/bitlist/proof.bend as ContainersBitlistProof
import ./proofs/containers/bitset/proof.bend as ContainersBitsetProof
import ./proofs/containers/deque/proof.bend as ContainersDequeProof
import ./proofs/containers/dlist_iterator/proof.bend as ContainersDlistIteratorProof
import ./proofs/containers/doubly_linked_list/direct_laws.bend as ContainersDoublyLinkedListDirectLaws
import ./proofs/containers/doubly_linked_list/proof.bend as ContainersDoublyLinkedListProof
import ./proofs/containers/dynamic_array/proof.bend as ContainersDynamicArrayProof
import ./proofs/containers/hash_table/proof.bend as ContainersHashTableProof
import ./proofs/containers/intrusive_doubly_linked_list/proof.bend as ContainersIntrusiveDoublyLinkedListProof
import ./proofs/containers/lru/proof.bend as ContainersLruProof
import ./proofs/containers/priority_queue/proof.bend as ContainersPriorityQueueProof
import ./proofs/containers/simple_queue/proof.bend as ContainersSimpleQueueProof
import ./proofs/containers/stack/components.bend as ContainersStackComponents
import ./proofs/lib/array2.bend as LibArray2
import ./proofs/lib/flat.bend as LibFlat
import ./proofs/lib/lemmas/proofs/public_trace.bend as LibLemmasPublicTrace
import ./proofs/lib/u32seq.bend as LibU32seq
import ./proofs/lib/vec.bend as LibVec
import ./spec/containers/balanced_search_tree/recursive.bend as SpecContainersBalancedSearchTreeRecursive
