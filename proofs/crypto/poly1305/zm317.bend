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


law app1:
  for +t: List<&2, U32>
  {V.len(List.append(&2, U32, t, [1])) == Nat.add(V.len(t), 1n) : Nat}

def app1(t):
  match t:
    case Nil{}: {==}
    case x <> u: Equal.cong(Nat, Nat, z => 1n+z, V.len(List.append(&2, U32, u, [1])), Nat.add(V.len(u), 1n), app1(u))

# p == 1 + bp
law pp_eq:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  {Nat.sub(C.shift(130n, one), 5n) == 1n+bp : Nat}

def pp_eq(one, h1, bp, h5):
  A.tr(Nat.sub(C.shift(130n, one), 5n), Nat.sub(Nat.add(1n+bp, 5n), 5n), 1n+bp, Equal.cong(Nat, Nat, z => Nat.sub(z, 5n), C.shift(130n, one), Nat.add(1n+bp, 5n), A.sy(Nat.add(1n+bp, 5n), C.shift(130n, one), h5)),
    A.tr(Nat.sub(Nat.add(1n+bp, 5n), 5n), Nat.sub(Nat.add(5n, 1n+bp), 5n), 1n+bp, Equal.cong(Nat, Nat, z => Nat.sub(z, 5n), Nat.add(1n+bp, 5n), Nat.add(5n, 1n+bp), N.add_comm(1n+bp, 5n)), N.add_sub_cancel(5n, 1n+bp)))

# ---- the accumulator ----

def load_len(+b: List<&2, U32>) -> {Nat.is_le(V.len(P.load(Li.take(16n, b))), 17n) == True{} : Bool}:
  +t = Li.take(16n, b)
  A.le_substl(V.len(List.append(&2, U32, t, [1])), V.len(P.load(t)), 17n, A.sy(V.len(P.load(t)), V.len(List.append(&2, U32, t, [1])), mask_len(List.append(&2, U32, t, [1]))),
    A.le_substl(Nat.add(V.len(t), 1n), V.len(List.append(&2, U32, t, [1])), 17n, A.sy(V.len(List.append(&2, U32, t, [1])), Nat.add(V.len(t), 1n), app1(t)),
      A.le_substl(1n+V.len(t), Nat.add(V.len(t), 1n), 17n, A.sy(Nat.add(V.len(t), 1n), 1n+V.len(t), A.tr(Nat.add(V.len(t), 1n), 1n+Nat.add(V.len(t), 0n), 1n+V.len(t), N.add_succ(V.len(t), 0n), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(V.len(t), 0n), V.len(t), N.add_zero(V.len(t))))), V.len_take(16n, b))))

law absorb_ok:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +bp: Nat
  for +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}
  for +fuel: Nat
  for +msg: List<&2, U32>
  for +r: List<&2, U32>
  for +h: List<&2, U32>
  for +a: Nat
  for +hrl: {V.len(r) == 16n : Nat}
  for +hrf: {V.fit_all(r, 8n) == True{} : Bool}
  for +hh: {ST.inv(h) == True{} : Bool}
  for +ha: {Nat.mod(V.ev(h), 1n+bp) == a : Nat}
  {Nat.mod(V.ev(P.absorb(fuel, msg, r, h)), 1n+bp) == R.absorb(R.blocks(fuel, msg), V.ev(r), a) : Nat}

law absorb_inv:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  for +fuel: Nat
  for +msg: List<&2, U32>
  for +r: List<&2, U32>
  for +h: List<&2, U32>
  for +hrl: {V.len(r) == 16n : Nat}
  for +hrf: {V.fit_all(r, 8n) == True{} : Bool}
  for +hh: {ST.inv(h) == True{} : Bool}
  {ST.inv(P.absorb(fuel, msg, r, h)) == True{} : Bool}

def absorb_inv(one, h1, fuel, msg, r, h, hrl, hrf, hh):
  match fuel msg:
    case 0n _: hh
    case 1n+k Nil{}: hh
    case 1n+k b <> Nil{}:
      +m = {[b] : List<&2, U32>}
      +c = P.load(Li.take(16n, m))
      absorb_inv(one, h1, k, Li.skip(16n, m), r, Li.block(r, h, c), hrl, hrf, ST.block_inv(one, h1, r, h, c, hh, mask_fit(List.append(&2, U32, Li.take(16n, m), [1])), hrl, hrf))
    case 1n+k b <> d <> rest:
      +m = {b <> d <> rest : List<&2, U32>}
      +c = P.load(Li.take(16n, m))
      absorb_inv(one, h1, k, Li.skip(16n, m), r, Li.block(r, h, c), hrl, hrf, ST.block_inv(one, h1, r, h, c, hh, mask_fit(List.append(&2, U32, Li.take(16n, m), [1])), hrl, hrf))

# one block: (r (a + n)) mod p == ev(block) mod p
def step_mod(+one: Nat, +h1: {one == 1n : Nat}, +bp: Nat, +h5: {Nat.add(1n+bp, 5n) == C.shift(130n, one) : Nat}, +r: List<&2, U32>, +h: List<&2, U32>, +m: List<&2, U32>, +a: Nat, +hrl: {V.len(r) == 16n : Nat}, +hrf: {V.fit_all(r, 8n) == True{} : Bool}, +hh: {ST.inv(h) == True{} : Bool}, +ha: {Nat.mod(V.ev(h), 1n+bp) == a : Nat}) -> {R.modp(Nat.mul(V.ev(r), Nat.add(a, R.le_num(List.append(&2, U32, R.prefix(16n, m), [1]))))) == Nat.mod(V.ev(Li.block(r, h, P.load(Li.take(16n, m)))), 1n+bp) : Nat}:
  +pp = {1n+bp : Nat}
  +c = P.load(Li.take(16n, m))
  +n = R.le_num(List.append(&2, U32, R.prefix(16n, m), [1]))
  +er = V.ev(r)
  +eh = V.ev(h)
  +ec = A.tr(V.ev(c), R.le_num(List.append(&2, U32, Li.take(16n, m), [1])), n, mask_ev(List.append(&2, U32, Li.take(16n, m), [1])),
    Equal.cong(List<&2, U32>, Nat, l => R.le_num(List.append(&2, U32, l, [1])), Li.take(16n, m), R.prefix(16n, m), take_prefix(16n, m)))
  +eb = ST.block_ev(one, h1, r, h, c, hh, load_len(m), mask_fit(List.append(&2, U32, Li.take(16n, m), [1])), hrl, hrf)
  +pm = ST.pm(one)
  +ep = A.tr(pm, Nat.sub(C.shift(130n, one), 5n), pp, {==}, pp_eq(one, h1, bp, h5))
  +bv = V.ev(Li.block(r, h, c))
  +k = ST.bk(r, h, c)
  +e1 = A.tr(Nat.mul(Nat.add(eh, V.ev(c)), er), Nat.add(bv, Nat.mul(k, pm)), Nat.add(Nat.mul(k, pp), bv), eb,
    A.tr(Nat.add(bv, Nat.mul(k, pm)), Nat.add(Nat.mul(k, pm), bv), Nat.add(Nat.mul(k, pp), bv), N.add_comm(bv, Nat.mul(k, pm)), WM.cong_l(Nat.mul(k, pm), Nat.mul(k, pp), bv, Equal.cong(Nat, Nat, z => Nat.mul(k, z), pm, pp, ep))))
  +e2 = A.tr(Nat.mod(Nat.mul(Nat.add(eh, V.ev(c)), er), pp), Nat.mod(Nat.add(Nat.mul(k, pp), bv), pp), Nat.mod(bv, pp), Equal.cong(Nat, Nat, z => Nat.mod(z, pp), Nat.mul(Nat.add(eh, V.ev(c)), er), Nat.add(Nat.mul(k, pp), bv), e1), NR.absorb(bp, k, bv))
  # mod(r (a + n)) == mod((eh + n) r)
  +e3 = A.tr(Nat.mod(Nat.mul(er, Nat.add(a, n)), pp), Nat.mod(Nat.mul(er, Nat.mod(Nat.add(a, n), pp)), pp), Nat.mod(Nat.mul(Nat.add(eh, V.ev(c)), er), pp),
    A.sy(Nat.mod(Nat.mul(er, Nat.mod(Nat.add(a, n), pp)), pp), Nat.mod(Nat.mul(er, Nat.add(a, n)), pp), NR.mod_mul_r(bp, er, Nat.add(a, n))),
    A.tr(Nat.mod(Nat.mul(er, Nat.mod(Nat.add(a, n), pp)), pp), Nat.mod(Nat.mul(er, Nat.mod(Nat.add(eh, n), pp)), pp), Nat.mod(Nat.mul(Nat.add(eh, V.ev(c)), er), pp),
      Equal.cong(Nat, Nat, z => Nat.mod(Nat.mul(er, z), pp), Nat.mod(Nat.add(a, n), pp), Nat.mod(Nat.add(eh, n), pp),
        A.tr(Nat.mod(Nat.add(a, n), pp), Nat.mod(Nat.add(Nat.mod(eh, pp), n), pp), Nat.mod(Nat.add(eh, n), pp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, n), pp), a, Nat.mod(eh, pp), A.sy(Nat.mod(eh, pp), a, ha)), NR.mod_add_l(bp, eh, n))),
      A.tr(Nat.mod(Nat.mul(er, Nat.mod(Nat.add(eh, n), pp)), pp), Nat.mod(Nat.mul(er, Nat.add(eh, n)), pp), Nat.mod(Nat.mul(Nat.add(eh, V.ev(c)), er), pp), NR.mod_mul_r(bp, er, Nat.add(eh, n)),
        Equal.cong(Nat, Nat, z => Nat.mod(z, pp), Nat.mul(er, Nat.add(eh, n)), Nat.mul(Nat.add(eh, V.ev(c)), er),
          A.tr(Nat.mul(er, Nat.add(eh, n)), Nat.mul(Nat.add(eh, n), er), Nat.mul(Nat.add(eh, V.ev(c)), er), NA.mul_comm(er, Nat.add(eh, n)), Equal.cong(Nat, Nat, z => Nat.mul(Nat.add(eh, z), er), n, V.ev(c), A.sy(V.ev(c), n, ec)))))))
  A.tr(R.modp(Nat.mul(er, Nat.add(a, n))), Nat.mod(Nat.mul(er, Nat.add(a, n)), pp), Nat.mod(bv, pp), MP.modp_mod(one, h1, bp, h5, Nat.mul(er, Nat.add(a, n))),
    A.tr(Nat.mod(Nat.mul(er, Nat.add(a, n)), pp), Nat.mod(Nat.mul(Nat.add(eh, V.ev(c)), er), pp), Nat.mod(bv, pp), e3, e2))

def absorb_ok(one, h1, bp, h5, fuel, msg, r, h, a, hrl, hrf, hh, ha):
  match fuel msg:
    case 0n _: ha
    case 1n+k Nil{}: ha
    case 1n+k b <> Nil{}:
      +m = {[b] : List<&2, U32>}
      +c = P.load(Li.take(16n, m))
      +h2 = Li.block(r, h, c)
      +a2 = R.modp(Nat.mul(V.ev(r), Nat.add(a, R.le_num(List.append(&2, U32, R.prefix(16n, m), [1])))))
      +hh2 = ST.block_inv(one, h1, r, h, c, hh, mask_fit(List.append(&2, U32, Li.take(16n, m), [1])), hrl, hrf)
      +ha2 = A.sy(a2, Nat.mod(V.ev(h2), 1n+bp), step_mod(one, h1, bp, h5, r, h, m, a, hrl, hrf, hh, ha))
      +ih = absorb_ok(one, h1, bp, h5, k, Li.skip(16n, m), r, h2, a2, hrl, hrf, hh2, ha2)
      A.tr(Nat.mod(V.ev(P.absorb(k, Li.skip(16n, m), r, h2)), 1n+bp), R.absorb(R.blocks(k, Li.skip(16n, m)), V.ev(r), a2), R.absorb(R.blocks(k, R.suffix(16n, m)), V.ev(r), a2), ih,
        Equal.cong(List<&2, U32>, Nat, l => R.absorb(R.blocks(k, l), V.ev(r), a2), Li.skip(16n, m), R.suffix(16n, m), skip_suffix(16n, m)))
    case 1n+k b <> d <> rest:
      +m = {b <> d <> rest : List<&2, U32>}
      +c = P.load(Li.take(16n, m))
      +h2 = Li.block(r, h, c)
      +a2 = R.modp(Nat.mul(V.ev(r), Nat.add(a, R.le_num(List.append(&2, U32, R.prefix(16n, m), [1])))))
      +hh2 = ST.block_inv(one, h1, r, h, c, hh, mask_fit(List.append(&2, U32, Li.take(16n, m), [1])), hrl, hrf)
      +ha2 = A.sy(a2, Nat.mod(V.ev(h2), 1n+bp), step_mod(one, h1, bp, h5, r, h, m, a, hrl, hrf, hh, ha))
      +ih = absorb_ok(one, h1, bp, h5, k, Li.skip(16n, m), r, h2, a2, hrl, hrf, hh2, ha2)
      A.tr(Nat.mod(V.ev(P.absorb(k, Li.skip(16n, m), r, h2)), 1n+bp), R.absorb(R.blocks(k, Li.skip(16n, m)), V.ev(r), a2), R.absorb(R.blocks(k, R.suffix(16n, m)), V.ev(r), a2), ih,
        Equal.cong(List<&2, U32>, Nat, l => R.absorb(R.blocks(k, l), V.ev(r), a2), Li.skip(16n, m), R.suffix(16n, m), skip_suffix(16n, m)))

# ---- the tag ----

def bpv(+one: Nat) -> Nat:
  Nat.sub(C.shift(130n, one), 6n)

law bp5:
  for +one: Nat
  for +h1: {one == 1n : Nat}
  {Nat.add(1n+bpv(one), 5n) == C.shift(130n, one) : Nat}

def bp5(one, h1):
  +s = C.shift(130n, one)
  +h6 = N.le_trans(6n, C.shift(3n, one), s, L.subst(Nat, z => {Nat.is_le(6n, C.shift(3n, z)) == True{} : Bool}, 1n, one, A.sy(one, 1n, h1), {==}), WW.shift_ge(127n, C.shift(3n, one)))
  A.tr(Nat.add(1n+bpv(one), 5n), Nat.add(5n, 1n+bpv(one)), s, N.add_comm(1n+bpv(one), 5n), N.sub_add(s, 6n, h6))

