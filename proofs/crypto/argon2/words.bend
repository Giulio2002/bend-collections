import Base
import ../../../spec/lib/common.bend as C
import ../../lib/logic.bend as L
import ../../lib/u32.bend as U
import ../../math/typed/u32.bend as U32P
import ../../math/typed/width.bend as WW

# The U32 value model the Argon2 proofs use (from proofs/math/typed/u32laws.bend
# and w64sh.bend, restated here so the package does not import their
# neighbours: Bend 2.0.34 checks every imported definition, and one of them
# expands 2^13 to a unary Nat, too deep for its stack next to this package).
# Width 32 stays symbolic inside the proofs.

def v(+x: U32) -> Nat:
  U32.to_nat(x)

def vb_k(+k: Nat, +hk: {k == 32n : Nat}, +x: U32) -> {C.fits(k, v(x)) == True{} : Bool}:
  %Equal.sym(Bool, C.fits(k, v(x)), Nat.is_lt(v(x), C.pow2(k)), WW.fits_lt(k, v(x))) : {_ == True{} : Bool}
  U32P.val_lt(1n, {==}, k, hk, x)

# every U32 value fits 32 bits
def vb(+x: U32) -> {C.fits(32n, v(x)) == True{} : Bool}:
  vb_k(32n, {==}, x)

def lt_k(+k: Nat, +n: Nat, +h: {C.fits(k, n) == True{} : Bool}) -> {Nat.is_lt(n, C.pow2(k)) == True{} : Bool}:
  %WW.fits_lt(k, n) : {_ == True{} : Bool}
  h

def vo_k(+k: Nat, +hk: {k == 32n : Nat}, +n: Nat, +h: {C.fits(k, n) == True{} : Bool}) -> {v(U32.from_nat(n)) == n : Nat}:
  U.to_nat_from_nat(n, k, U32P.le_k(k, hk), lt_k(k, n, h))

# a value that fits is the value of its U32
def vo(+n: Nat, +h: {C.fits(32n, n) == True{} : Bool}) -> {v(U32.from_nat(n)) == n : Nat}:
  vo_k(32n, {==}, n, h)

def rt(+x: U32) -> {U32.from_nat(v(x)) == x : U32}:
  U32P.round_trip(x)

# the high part of a value of t + s bits has s bits
def fits_high(+t: Nat, +s: Nat, +x: Nat, +h: {C.fits(Nat.add(t, s), x) == True{} : Bool}) -> {C.fits(s, C.high(t, x)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_eq(z, 0n) == True{} : Bool}, C.high(Nat.add(t, s), x), C.high(s, C.high(t, x)), WW.high_comp(s, t, x), h)
