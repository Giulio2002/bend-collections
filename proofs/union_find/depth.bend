import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC
import ../../src/union_find.bend as U

# `U.depth_for(n)` picks the depth of the arenas of an n-element structure:
# the smallest d <= 31 with n <= 2^d, so the capacity is 2^31 elements. The
# fact proved here is that the depth is always below 32, hence every slot
# index is a representable U32 and Base's index masking is the identity.
# That the chosen depth actually holds n elements is the loop's own exit
# test, carried as the explicit capacity premise of the laws about `new`.

def pow2_same(+d: Nat) -> {U.pow2(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, U.pow2(p), SC.pow2(p), pow2_same(p))

def depth_go_le(fuel: Nat, +n: Nat, +d: Nat, +cap: Nat, done: Bool, +hd: {Nat.is_le(Nat.add(d, fuel), 31n) == True{} : Bool}) -> {Nat.is_le(U.depth_go(fuel, n, d, cap, done), 31n) == True{} : Bool}:
  match fuel done:
    case 0n _:
      %N.add_zero(d) : {Nat.is_le(_, 31n) == True{} : Bool}
      hd
    case 1n+ +f True{}:
      N.le_trans(d, Nat.add(d, 1n+f), 31n, N.le_add_right(d, 1n+f), hd)
    case 1n+ +f False{}:
      depth_go_le(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.double(cap)),
        L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, Nat.add(d, 1n+f), 1n+Nat.add(d, f), N.add_succ(d, f), hd))

def depth_le(+n: Nat) -> {Nat.is_le(U.depth_for(n), 31n) == True{} : Bool}:
  depth_go_le(31n, n, 0n, 1n, Nat.is_le(n, 1n), N.le_refl(31n))

def depth_lt(+n: Nat) -> {Nat.is_lt(U.depth_for(n), 32n) == True{} : Bool}:
  N.le_lt_succ(U.depth_for(n), 31n, depth_le(n))
