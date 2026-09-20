import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC
import ../../src/fenwick_tree.bend as F

# `F.depth_for(n)` picks the depth of the cell array of an n-value tree: the
# smallest d <= 30 with n <= 2^d, so the capacity of the representation is
# 2^30 values and the cell array's own depth d+1 is at most 31. The fact
# proved here is that d <= 30 (hence every cell index is a representable U32
# and Base's index masking over the array is the identity). That the chosen
# depth actually holds n values is the loop's own exit test, carried as the
# explicit capacity premise of the laws about `new`.

def depth_go_le(fuel: Nat, +n: Nat, +d: Nat, +cap: Nat, done: Bool, +hd: {Nat.is_le(Nat.add(d, fuel), 30n) == True{} : Bool}) -> {Nat.is_le(F.depth_go(fuel, n, d, cap, done), 30n) == True{} : Bool}:
  match fuel done:
    case 0n _:
      %N.add_zero(d) : {Nat.is_le(_, 30n) == True{} : Bool}
      hd
    case 1n+ +f True{}:
      N.le_trans(d, Nat.add(d, 1n+f), 30n, N.le_add_right(d, 1n+f), hd)
    case 1n+ +f False{}:
      depth_go_le(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.double(cap)),
        L.subst(Nat, z => {Nat.is_le(z, 30n) == True{} : Bool}, Nat.add(d, 1n+f), 1n+Nat.add(d, f), N.add_succ(d, f), hd))

def depth_le(+n: Nat) -> {Nat.is_le(F.depth_for(n), 30n) == True{} : Bool}:
  depth_go_le(30n, n, 0n, 1n, Nat.is_le(n, 1n), N.le_refl(30n))

# The cell array's depth d+1 is below 32.
def depth_lt(+n: Nat) -> {Nat.is_lt(1n+F.depth_for(n), 32n) == True{} : Bool}:
  N.le_lt_succ(1n+F.depth_for(n), 31n, depth_le(n))
