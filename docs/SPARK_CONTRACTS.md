# SPARK formal-container contracts

The contract is part of each container's specification, as in SPARK, where it
lives in the `.ads`. `spec/containers/<pkg>.bend` holds the abstract model
and states each operation's behaviour as the postconditions of the matching
container in [SPARKlib](https://github.com/AdaCore/SPARKlib)'s formal
containers: one `<Subprogram>.<clause>` definition (a proposition on the
model) per `Post` / `Contract_Cases` clause. Its contract section opens with a
table mapping each SPARK subprogram (with its line in the `.ads`) to our
function and the clauses that state it.

`proofs/containers/<pkg>/proof.bend` proves every clause under the same
clause name, and the package's refinement theorem (`impl`) carries every
clause to the implementation. `proofs/prove.py` checks all of it. The
priority queue and the simple queue are the binary heap and the queue behind
another interface: their specs restate the underlying contract clause by
clause, and their proofs are the underlying ones.

SPARK's preconditions (index in range, not empty, room left, valid cursor)
are defensive checks here: the operation returns an error value and changes
nothing, and that is proved too (`*_outside`, `*_empty`, `*_full`,
`*_stale`, …).

| Container | SPARK container | Proved subprograms | Not applicable (no such operation in our API) |
|---|---|---|---|
| dynamic_array | Formal_Vectors | Length, Capacity, Empty_Vector, Reserve_Capacity, Clear, Element, First_Element, Last_Element, Replace_Element, Append, Delete_Last, iteration (12) | `=`, To_Vector, Assign/Copy/Move, Reference, Insert*, Prepend*, Append_Vector, Delete (index), Delete_First, Reverse_Elements, Swap, Find_Index, Reverse_Find_Index, Contains, Has_Element |
| bitlist | Formal_Vectors | Length, Capacity (limit), Empty_Vector, Clear, Element, Replace_Element, Append, Delete_Last, Last_Element, iteration, To_Vector (11) | as dynamic_array, plus Reserve_Capacity |
| stack | Formal_Vectors (top first) | Length, Empty_Vector, Prepend, Delete_First, First_Element, iteration (6) | Capacity (unbounded), Clear, indexed access, Append*, Delete_Last, Last_Element, search |
| deque | Formal_Vectors | Length, Empty_Vector, Prepend, Append, Delete_First, Delete_Last, First_Element, Last_Element, iteration (9) | Capacity, Clear, indexed access, Insert, search, Reverse, Swap |
| queue, simple_queue | Formal_Vectors (oldest first) | Length, Empty_Vector, Append, Delete_First, First_Element, iteration (6) | Capacity, Clear, indexed access, Prepend, Delete_Last, Last_Element, search |
| doubly_linked_list | Formal_Doubly_Linked_Lists | Length, Empty_List, Has_Element, Element, Replace_Element, Prepend, Append, Insert (before), Insert after, Delete, Next, Previous, iteration (13) | `=`, Is_Empty, Clear, Assign/Copy/Move, counted Insert/Delete, Delete_First/Last, First/Last(_Element), Reverse_Elements, Swap, Swap_Links, Splice, Find, Reverse_Find, Contains |
| dlist_iterator | Formal_Doubly_Linked_Lists (cursor part) | the cursor-state clauses of Has_Element, Next at the end, the Pre of Replace_Element and Delete, the cursor after Delete and Insert (6) | element-level Post clauses: the iterator walks the list's storage directly and has no sequence refinement yet (the list itself has them all) |
| hash_table | Formal_Hashed_Maps | Empty_Map, Length, Element, Contains, Include, Delete, Exclude, iteration (keys), Equivalent_Keys (9) | `=`, Capacity, Reserve_Capacity, Is_Empty, Clear, Assign/Copy/Move, cursors (First/Next/Key/Element/Has_Element), Find, Replace_Element, Insert and Replace (Include subsumes them), Default_Modulus |
| lru | Formal_Hashed_Maps + recency order | Empty_Map, Length, Capacity, Include (present / room / eviction), Element (get touches, peek does not), Contains, Delete/Exclude, Clear, iteration, expiry (10) | `=`, Is_Empty, Assign/Copy/Move, cursors, Find, Insert-fails-if-present, Replace |
| balanced_search_tree (TreeMap) | Formal_Ordered_Maps | Empty_Map, Length, Is_Empty, Clear, Element, Find, Contains, Include, Insert, Replace, Exclude, Delete, First(_Element/_Key), Last(_Element/_Key), Floor, Ceiling (16) | `=`, Assign/Copy/Move, Reference, cursors (Key/Element/Next/Previous/Has_Element by cursor: the map's iterators, related to the model by the refinement proof) |
| bitset | Formal_Ordered_Sets | Length, Capacity, Empty_Set, Contains, Include/Insert, Exclude/Delete, Union, Intersection, Difference, Symmetric_Difference, iteration (11) | `=`, Equivalent_Sets, To_Set, Assign/Copy/Move, Replace*, Delete_First/Last, set functions returning new sets, Overlap, Is_Subset, cursors, First/Last, Floor/Ceiling |
| binary_heap, priority_queue | (none in SPARKlib) closest: Formal_Ordered_Sets with multiplicity | Length, Empty_Set, Insert, First_Element (minimum), Delete_First, To_Set, ordered iteration (7) | keys, cursors and positions (Find, Floor, Ceiling, Next, Previous, Contains, Replace, Exclude of an arbitrary element, Last_Element), set algebra |

Notes:

- Model predicates (`Range_Equal`, `Range_Shifted`, `Equal_Prefix`,
  `Equal_Except`, …) are in `spec/lib/sequence.bend`, their lemmas in
  `proofs/lib/sequence.bend`; the comparator's order laws are in
  `spec/lib/order.bend`.
- The hash table's queries (Element, Contains, Length) and Empty_Map are
  stated on the value the operation returns, since its model has no step
  function; the proof instantiates them with the implementation's result.
- The list iterator has no model of its own: its spec
  (`spec/containers/dlist_iterator.bend`) maps the SPARK cursor subprograms,
  and its cursor-state clauses are proved on the implementation in
  `proofs/containers/dlist_iterator/proof.bend`.
- The LRU's key-uniqueness invariant is not re-exported, so its clauses are
  stated through the model's `find`/`drop` rather than as pointwise lookup
  frames; the TreeMap's frames (every other key unchanged, the removed key
  gone) are pointwise and use the comparator's order laws and the model's
  ordering invariant.
- Sources followed: SPARKlib (AdaCore/SPARKlib, `src/` and `src/full/`) for
  the contract shapes; the bit list also cites Lean 4's `List` lemmas and
  the ConsenSys eth2.0-dafny SSZ proofs.
