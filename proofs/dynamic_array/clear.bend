import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/dynamic_array.bend as DA
import ./layout.bend as LY
import ./state.bend as ST
import ../deque/state.bend as DST
import ../lib/array_ext.bend as AX

# The executable clear (src/dynamic_array.bend clear_at) allocates the fresh
# all-None block of the same depth, which is exactly what the parametric
# clear does, so the two agree at every state (the `good` premise is not
# needed and is kept only so the caller's shape is unchanged).

def clear_eq(~T: Data, +l: Nat, +d: Nat, n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> {DA.clear_at(~T, ST.real(T, ST.Sh{l, d, n, t})) == DA.clear(T, ST.real(T, ST.Sh{l, d, n, t})) : DA.DynArray<T>}:
  {==}
