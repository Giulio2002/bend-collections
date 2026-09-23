import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../../src/containers/bitset.bend as B
import ./index.bend as IX

# `B.depth_for(n)` picks the depth of the word array of an n-bit bitset: the
# smallest d <= 31 with n <= 32 * 2^d, so the capacity of the representation
# is 2^36 bits. The fact proved here is that the depth is always below 32
# (hence every word index is a representable U32 and Base's index masking is
# the identity). That the chosen depth actually holds n bits is the loop's own
# exit test, and is carried as the explicit `fits` premise of the laws about
# `new` (see proofs/bitset/state.bend): a bitset larger than the capacity
# cannot be represented, exactly as in src/dynamic_array.bend.

def pow2_same(+d: Nat) -> {B.pow2(d) == SC.pow2(d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, B.pow2(p), SC.pow2(p), pow2_same(p))

def depth_go_le(fuel: Nat, +n: Nat, +d: Nat, +cap: Nat, done: Bool, +hd: {Nat.is_le(Nat.add(d, fuel), 31n) == True{} : Bool}) -> {Nat.is_le(B.depth_go(fuel, n, d, cap, done), 31n) == True{} : Bool}:
  match fuel done:
    case 0n _:
      %N.add_zero(d) : {Nat.is_le(_, 31n) == True{} : Bool}
      hd
    case 1n+ +f True{}:
      N.le_trans(d, Nat.add(d, 1n+f), 31n, N.le_add_right(d, 1n+f), hd)
    case 1n+ +f False{}:
      depth_go_le(f, n, 1n+d, Nat.double(cap), Nat.is_le(n, Nat.mul(Nat.double(cap), 32n)),
        L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, Nat.add(d, 1n+f), 1n+Nat.add(d, f), N.add_succ(d, f), hd))

# The depth is always below 32, so every word index is a representable U32
# and Base's index masking over the word array is the identity.
def depth_le(+n: Nat) -> {Nat.is_le(B.depth_for(n), 31n) == True{} : Bool}:
  depth_go_le(31n, n, 0n, 1n, Nat.is_le(n, Nat.mul(1n, 32n)), N.le_refl(31n))

def depth_lt(+n: Nat) -> {Nat.is_lt(B.depth_for(n), 32n) == True{} : Bool}:
  N.le_lt_succ(B.depth_for(n), 31n, depth_le(n))

# re-exports so proofs/bitset/state.bend does not need proofs/bitset/index.bend
def wordix_small_alias(+i: Nat, +h: {Nat.is_lt(i, 32n) == True{} : Bool}) -> {B.wordix(i) == 0n : Nat}:
  IX.wordix_small(i, h)

def wordix_step_alias(+i: Nat, +h: {Nat.is_lt(i, 32n) == False{} : Bool}) -> {B.wordix(i) == 1n+B.wordix(Nat.sub(i, 32n)) : Nat}:
  IX.wordix_step(i, h)
