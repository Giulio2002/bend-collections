import Base
import ./doubly_linked_list.bend as DS

# ---- contract (SPARK formal containers) ----
# Each `<Subprogram>.<clause>` definition below states one Post clause of
# that SPARK subprogram, as a proposition on this model; the table names the
# clauses. proofs/containers/dlist_iterator/ proves every clause under its clause name,
# and its `impl` lemma carries them to the implementation.
#
# Contracts of the list iterator in the style of SPARK's formal doubly
# linked lists' cursor subprograms (SPARKlib
# src/spark-containers-formal-doubly_linked_lists.ads, AdaCore/SPARKlib
# master). The iterator owns a list and walks it; its state is the list, the
# next link, the last-returned link, the direction and the position index.
# What is proved here is the cursor-state part of SPARK's contracts, over
# the actual implementation (proof.bend's component laws):
#
#   SPARK subprogram (.ads line)          ours                  clauses (proof.bend)
#   Has_Element (1814)                    has_next              has_next_state (= next link present)
#   Has_Element (backward)                has_previous          has_previous_state (= position > 0)
#   Next (1614), at the end: No_Element   next                  next_exhausted (Exhausted, state unchanged)
#   Replace_Element (430), Pre Has_Element  set                 set_requires_current (NoCurrent, unchanged)
#   Delete (978), Pre Has_Element         remove                remove_requires_current (NoCurrent, unchanged)
#   Delete: cursor moves on               removed               removed_forward, removed_backward
#   Insert (523): position advances       add                   added_clears_current
#   (the container is returned intact)    finish                finish_owns
#
# Not proved: the element-level Post clauses (Next returns P.Get (Positions,
# Position + 1); Delete/Insert shift the model), because the iterator walks
# the list's storage directly and has no sequence refinement proof yet; the
# list itself (spec/containers/doubly_linked_list.bend) has all of those.
