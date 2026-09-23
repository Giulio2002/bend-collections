import Base
import ./invariants.bend as Inv
import ./map_routing.bend as R
import ./map_delete_prefix.bend as P

def NodeFacts(-V: Data, +p: Nat, +lo: Map<&2, V>, +hi: Map<&2, V>) -> Type:
  {Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) == True{} : Bool} & {Inv.nonempty(V, lo) == True{} : Bool} & {Inv.nonempty(V, hi) == True{} : Bool} & {Inv.below(V, lo, p) == True{} : Bool} & {Inv.below(V, hi, p) == True{} : Bool} & {Inv.routed(V, lo, p, False{}) == True{} : Bool} & {Inv.routed(V, hi, p, True{}) == True{} : Bool} & {Inv.critbit(V, lo) == True{} : Bool} & {Inv.critbit(V, hi) == True{} : Bool}

law node_parts:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for +e: {Inv.critbit(V, MNode{p, lo, hi}) == True{} : Bool}
  {Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) == True{} : Bool} & {Inv.nonempty(V, lo) == True{} : Bool} & {Inv.nonempty(V, hi) == True{} : Bool} & {Inv.below(V, lo, p) == True{} : Bool} & {Inv.below(V, hi, p) == True{} : Bool} & {Inv.routed(V, lo, p, False{}) == True{} : Bool} & {Inv.routed(V, hi, p, True{}) == True{} : Bool} & {Inv.critbit(V, lo) == True{} : Bool} & {Inv.critbit(V, hi) == True{} : Bool}
def node_parts(V, p, lo, hi, e):
  +e7 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}) && Inv.critbit(V, lo), Inv.critbit(V, hi), e)
  +e6 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}), Inv.critbit(V, lo), e7)
  +e5 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}), Inv.routed(V, hi, p, True{}), e6)
  +e4 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p), Inv.routed(V, lo, p, False{}), e5)
  +e3 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p), Inv.below(V, hi, p), e4)
  +e2 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi), Inv.below(V, lo, p), e3)
  +e1 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo), Inv.nonempty(V, hi), e2)
  +e0 = R.and_left(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p), Inv.nonempty(V, lo), e1)
  (e0, R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p), Inv.nonempty(V, lo), e1), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo), Inv.nonempty(V, hi), e2), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi), Inv.below(V, lo, p), e3), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p), Inv.below(V, hi, p), e4), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p), Inv.routed(V, lo, p, False{}), e5), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}), Inv.routed(V, hi, p, True{}), e6), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}), Inv.critbit(V, lo), e7), R.and_right(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}) && Inv.critbit(V, lo), Inv.critbit(V, hi), e))

law node_valid:
  for -V: Data
  for +p: Nat
  for +lo: Map<&2, V>
  for +hi: Map<&2, V>
  for e0: {Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) == True{} : Bool}
  for e1: {Inv.nonempty(V, lo) == True{} : Bool}
  for e2: {Inv.nonempty(V, hi) == True{} : Bool}
  for e3: {Inv.below(V, lo, p) == True{} : Bool}
  for e4: {Inv.below(V, hi, p) == True{} : Bool}
  for e5: {Inv.routed(V, lo, p, False{}) == True{} : Bool}
  for e6: {Inv.routed(V, hi, p, True{}) == True{} : Bool}
  for e7: {Inv.critbit(V, lo) == True{} : Bool}
  for e8: {Inv.critbit(V, hi) == True{} : Bool}
  {Inv.critbit(V, MNode{p, lo, hi}) == True{} : Bool}
def node_valid(V, p, lo, hi, e0, e1, e2, e3, e4, e5, e6, e7, e8):
  P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}) && Inv.critbit(V, lo), Inv.critbit(V, hi), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}) && Inv.routed(V, hi, p, True{}), Inv.critbit(V, lo), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p) && Inv.routed(V, lo, p, False{}), Inv.routed(V, hi, p, True{}), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p) && Inv.below(V, hi, p), Inv.routed(V, lo, p, False{}), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi) && Inv.below(V, lo, p), Inv.below(V, hi, p), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo) && Inv.nonempty(V, hi), Inv.below(V, lo, p), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p) && Inv.nonempty(V, lo), Inv.nonempty(V, hi), P.conjunction(Inv.common_prefix(V, MNode{p, lo, hi}, MNode{p, lo, hi}, p), Inv.nonempty(V, lo), e0, e1), e2), e3), e4), e5), e6), e7), e8)
