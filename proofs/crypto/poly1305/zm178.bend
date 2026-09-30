import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/f64bits.bend as FB
import ../../math/natural/arith.bend as NR
import ./arith.bend as A
import ./value.bend as V
import ./step.bend as ST
import ./modp.bend as MP
import ./final.bend as F

# The implementation's Poly1305 tag is the RFC 8439 tag (spec/crypto/
# poly1305.bend) for every key and message: the limb accumulator stays
# congruent to the spec's accumulator mod p block by block, and the final
# freeze and byte serialization give the spec's num_to_16_le_bytes.
# mac_correct and mac_length are the clauses of laws.bend (proof.bend fills
# the laws with them; other proofs may import this file).

# ---- bytes to limbs ----

law mask_ev:
  for +xs: List<&2, U32>
  {V.ev(P.mask(xs)) == R.le_num(xs) : Nat}

def mask_ev(xs):
  match xs:
    case Nil{}: {==}
    case x <> t: WM.cong_r(U32.to_nat(U32.and(x, 255)), C.shift(8n, V.ev(P.mask(t))), C.shift(8n, R.le_num(t)), A.csh(8n, V.ev(P.mask(t)), R.le_num(t), mask_ev(t)))

law mask_fit:
  for +xs: List<&2, U32>
  {V.fit_all(P.mask(xs), 8n) == True{} : Bool}

def mask_fit(xs):
  match xs:
    case Nil{}: {==}
    case x <> t:
      L.and_intro(C.fits(8n, V.v(U32.and(x, 255))), V.fit_all(P.mask(t), 8n),
        A.fits_subst(8n, C.low(8n, V.v(x)), V.v(U32.and(x, 255)), A.sy(V.v(U32.and(x, 255)), C.low(8n, V.v(x)), FB.andm(x, 8n, 255, {==})), WW.low_fits(8n, V.v(x))),
        mask_fit(t))

law mask_len:
  for +xs: List<&2, U32>
  {V.len(P.mask(xs)) == V.len(xs) : Nat}

def mask_len(xs):
  match xs:
    case Nil{}: {==}
    case x <> t: Equal.cong(Nat, Nat, z => 1n+z, V.len(P.mask(t)), V.len(t), mask_len(t))

law take_prefix:
  for +n: Nat
  for +xs: List<&2, U32>
  {Li.take(n, xs) == R.prefix(n, xs) : List<&2, U32>}

def take_prefix(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: Equal.cong(List<&2, U32>, List<&2, U32>, z => x <> z, Li.take(k, t), R.prefix(k, t), take_prefix(k, t))

law skip_suffix:
  for +n: Nat
  for +xs: List<&2, U32>
  {Li.skip(n, xs) == R.suffix(n, xs) : List<&2, U32>}

def skip_suffix(n, xs):
  match n xs:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: skip_suffix(k, t)

law cmask:
  for +i: Nat
  {P.clamp_mask(i) == R.clamp_mask(i) : U32}

def cmask(i):
  match i:
    case 0n: {==}
    case 1n: {==}
    case 2n: {==}
    case 3n: {==}
    case 4n: {==}
    case 5n: {==}
    case 6n: {==}
    case 7n: {==}
    case 8n: {==}
    case 9n: {==}
    case 10n: {==}
    case 11n: {==}
    case 12n: {==}
    case 13n: {==}
    case 14n: {==}
    case 15n: {==}
    case 16n+p: {==}

law clamp_eq:
  for +xs: List<&2, U32>
  for +i: Nat
  {P.clamp(xs, i) == R.clamp_from(xs, i) : List<&2, U32>}

def clamp_eq(xs, i):
  match xs:
    case Nil{}: {==}
    case x <> t:
      Equal.trans(List<&2, U32>, U32.and(x, P.clamp_mask(i)) <> P.clamp(t, 1n+i), U32.and(x, R.clamp_mask(i)) <> P.clamp(t, 1n+i), U32.and(x, R.clamp_mask(i)) <> R.clamp_from(t, 1n+i),
        Equal.cong(U32, List<&2, U32>, z => U32.and(x, z) <> P.clamp(t, 1n+i), P.clamp_mask(i), R.clamp_mask(i), cmask(i)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => U32.and(x, R.clamp_mask(i)) <> z, P.clamp(t, 1n+i), R.clamp_from(t, 1n+i), clamp_eq(t, 1n+i)))

law clamp_len:
  for +xs: List<&2, U32>
  for +i: Nat
  {V.len(P.clamp(xs, i)) == V.len(xs) : Nat}

def clamp_len(xs, i):
  match xs:
    case Nil{}: {==}
    case x <> t: Equal.cong(Nat, Nat, z => 1n+z, V.len(P.clamp(t, 1n+i)), V.len(t), clamp_len(t, 1n+i))

law fit_fit:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {V.fit_all(xs, 8n) == True{} : Bool}
  {V.fit_all(Li.fit(n, xs), 8n) == True{} : Bool}

def fit_fit(n, xs, h):
  match n:
    case 0n: {==}
    case 1n+k: L.and_intro(C.fits(8n, V.v(Li.hd0(xs))), V.fit_all(Li.fit(k, Li.tl(xs)), 8n), V.hd0_fit(xs, 8n, h), fit_fit(k, Li.tl(xs), V.tl_fit(xs, 8n, h)))

law take_all:
  for +n: Nat
  for +xs: List<&2, U32>
  for +h: {Nat.is_le(V.len(xs), n) == True{} : Bool}
  {Li.take(n, xs) == xs : List<&2, U32>}

def take_all(n, xs, h):
  match n xs:
    case 0n Nil{}: {==}
    case 0n x <> t: Empty.absurd({Li.take(0n, x <> t) == x <> t : List<&2, U32>}, L.false_true(h))
    case 1n+k Nil{}: {==}
    case 1n+k x <> t: Equal.cong(List<&2, U32>, List<&2, U32>, z => x <> z, Li.take(k, t), t, take_all(k, t, h))

# the key's r and s limbs
law r_ev:
  for +key: List<&2, U32>
  {V.ev(P.r_key(key)) == R.le_num(R.clamp(R.prefix(16n, key))) : Nat}

def r_ev(key):
  +t = Li.take(16n, key)
  +m = P.mask(P.clamp(t, 0n))
  +hl = A.le_substl(V.len(t), V.len(m), 16n, A.sy(V.len(m), V.len(t), A.tr(V.len(m), V.len(P.clamp(t, 0n)), V.len(t), mask_len(P.clamp(t, 0n)), clamp_len(t, 0n))), V.len_take(16n, key))
  A.tr(V.ev(P.r_key(key)), V.ev(Li.take(16n, m)), R.le_num(R.clamp(R.prefix(16n, key))), V.fit_ev(16n, m),
    A.tr(V.ev(Li.take(16n, m)), V.ev(m), R.le_num(R.clamp(R.prefix(16n, key))), Equal.cong(List<&2, U32>, Nat, l => V.ev(l), Li.take(16n, m), m, take_all(16n, m, hl)),
      A.tr(V.ev(m), R.le_num(P.clamp(t, 0n)), R.le_num(R.clamp(R.prefix(16n, key))), mask_ev(P.clamp(t, 0n)),
        Equal.cong(List<&2, U32>, Nat, l => R.le_num(l), P.clamp(t, 0n), R.clamp(R.prefix(16n, key)),
          Equal.trans(List<&2, U32>, P.clamp(t, 0n), R.clamp_from(t, 0n), R.clamp(R.prefix(16n, key)), clamp_eq(t, 0n), Equal.cong(List<&2, U32>, List<&2, U32>, l => R.clamp_from(l, 0n), t, R.prefix(16n, key), take_prefix(16n, key)))))))

law s_ev:
  for +key: List<&2, U32>
  {V.ev(P.s_key(key)) == R.le_num(R.prefix(16n, R.suffix(16n, key))) : Nat}

def s_ev(key):
  A.tr(V.ev(P.s_key(key)), R.le_num(Li.take(16n, Li.skip(16n, key))), R.le_num(R.prefix(16n, R.suffix(16n, key))), mask_ev(Li.take(16n, Li.skip(16n, key))),
    Equal.cong(List<&2, U32>, Nat, l => R.le_num(l), Li.take(16n, Li.skip(16n, key)), R.prefix(16n, R.suffix(16n, key)),
      Equal.trans(List<&2, U32>, Li.take(16n, Li.skip(16n, key)), R.prefix(16n, Li.skip(16n, key)), R.prefix(16n, R.suffix(16n, key)), take_prefix(16n, Li.skip(16n, key)),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => R.prefix(16n, l), Li.skip(16n, key), R.suffix(16n, key), skip_suffix(16n, key)))))


