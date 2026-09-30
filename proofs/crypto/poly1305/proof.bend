import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../spec/crypto/subtle.bend as SS
import ../../../src/crypto/subtle.bend as Subtle
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../lib/logic.bend as L
import ../subtle/word.bend as SW
import ../subtle/fold.bend as SF
import ./modp.bend as MP
import ./mac.bend as M
import ./api.bend as API
import ./tag2.bend as PT
import ./laws.bend as Laws
import ./poly.bend as PY

# Entry point: `bend proofs/crypto/poly1305/proof.bend` checks every clause of
# laws.bend. The work is in vals.bend (the value of the radix-2^26 limbs and
# of each limb operation, mod p), bnd.bend (27-bit limbs between blocks),
# fin.bend (the final reduction and the tag bytes), modp.bend (the spec's
# reduction) and mac.bend (the accumulator against the spec, block by
# block, and the tag); tools/generators/poly1305_hand/*.src are their
# sources (tools/generators/rw.py expands the rewrite steps).

def Laws.mac_correct(key, msg): M.mac_correct(key, msg)

def Laws.mac_length(key, msg): M.mac_length(key, msg)

def Laws.mac_aead(key, aad, ct): PT.mac_aead_correct(key, aad, ct)

def Laws.modp_mod(one, h1, x):
  Equal.trans(Nat, R.modp(x), Nat.mod(x, 1n+M.bpv(one)), Nat.mod(x, Nat.sub(C.shift(130n, one), 5n)), MP.modp_mod(one, h1, M.bpv(one), M.bp5(one, h1), x),
    Equal.cong(Nat, Nat, z => Nat.mod(x, z), 1n+M.bpv(one), Nat.sub(C.shift(130n, one), 5n), Equal.sym(Nat, Nat.sub(C.shift(130n, one), 5n), 1n+M.bpv(one), M.pp_eq(one, h1, M.bpv(one), M.bp5(one, h1)))))

def Laws.poly1305_valid(key, msg, h): API.poly1305_valid(key, msg, h)

def Laws.poly1305_invalid(key, msg, h): API.poly1305_invalid(key, msg, h)

# ---- constant-time equality (the value lemma is proofs/crypto/subtle/fold.bend's) ----

law equal_sound:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {SS.equal(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

def equal_sound(a, b, h):
  match a b:
    case Nil{} Nil{}: {==}
    case Nil{} y <> ys: Empty.absurd({Nil{} == y <> ys : List<&2, U32>}, L.false_true(h))
    case x <> xs Nil{}: Empty.absurd({x <> xs == Nil{} : List<&2, U32>}, L.false_true(h))
    case x <> xs y <> ys:
      +exy = SW.u32_sound(x, y, L.and_left(U32.is_eq(x, y), SS.equal(xs, ys), h))
      +et = equal_sound(xs, ys, L.and_right(U32.is_eq(x, y), SS.equal(xs, ys), h))
      %et : {x <> xs == y <> _ : List<&2, U32>}
      %exy : {x <> xs == _ <> xs : List<&2, U32>}
      {==}

law equal_refl:
  for +a: List<&2, U32>
  {SS.equal(a, a) == True{} : Bool}

def equal_refl(a):
  match a:
    case Nil{}: {==}
    case x <> xs:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, SW.u32_refl(x)) : {Bool.and(_, SS.equal(xs, xs)) == True{} : Bool}
      equal_refl(xs)

# ---- verify ----

def Laws.verify_accepts(key, msg, h):
  +t = R.mac(key, msg)
  +pm = P.mac(key, msg)
  Equal.trans(Bool, P.verify(key, msg, t), SS.equal(pm, t), True{},
    Equal.trans(Bool, P.verify(key, msg, t), Subtle.eq(pm, t), SS.equal(pm, t),
      Equal.cong(Bool, Bool, b => Bool.and(b, Subtle.eq(pm, t)), P.has_key(key), True{}, h),
      SF.fold4(pm, t, 0)),
    Equal.trans(Bool, SS.equal(pm, t), SS.equal(t, t), True{}, Equal.cong(List<&2, U32>, Bool, l => SS.equal(l, t), pm, t, M.mac_correct(key, msg)), equal_refl(t)))

def rej_c(+key: List<&2, U32>, +msg: List<&2, U32>, +tag: List<&2, U32>, h: {tag != R.mac(key, msg) : List<&2, U32>}, +c: Bool, +hc: {SS.equal(P.mac(key, msg), tag) == c : Bool}) -> {Bool.and(P.has_key(key), SS.equal(P.mac(key, msg), tag)) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({Bool.and(P.has_key(key), SS.equal(P.mac(key, msg), tag)) == False{} : Bool},
        h(Equal.trans(List<&2, U32>, tag, P.mac(key, msg), R.mac(key, msg), Equal.sym(List<&2, U32>, P.mac(key, msg), tag, equal_sound(P.mac(key, msg), tag, hc)), M.mac_correct(key, msg))))
    case False{}:
      Equal.trans(Bool, Bool.and(P.has_key(key), SS.equal(P.mac(key, msg), tag)), Bool.and(P.has_key(key), False{}), False{},
        Equal.cong(Bool, Bool, b => Bool.and(P.has_key(key), b), SS.equal(P.mac(key, msg), tag), False{}, hc), SW.and_false(P.has_key(key)))

def Laws.verify_rejects(key, msg, tag, h):
  Equal.trans(Bool, P.verify(key, msg, tag), Bool.and(P.has_key(key), SS.equal(P.mac(key, msg), tag)), False{},
    Equal.cong(Bool, Bool, b => Bool.and(P.has_key(key), b), Subtle.eq(P.mac(key, msg), tag), SS.equal(P.mac(key, msg), tag), SF.fold4(P.mac(key, msg), tag, 0)),
    rej_c(key, msg, tag, h, SS.equal(P.mac(key, msg), tag), {==}))

# ---- the polynomial

def Laws.absorb_poly(one, h1, bs, r):
  PY.absorb_poly(one, h1, bs, r)

def Laws.mac_poly(one, h1, key, msg):
  +r = R.le_num(R.clamp(R.prefix(16n, key)))
  +s = R.le_num(R.prefix(16n, R.suffix(16n, key)))
  +bs = R.blocks(List.length(&2, U32, msg), msg)
  Equal.cong(Nat, List<&2, U32>, z => R.le_bytes(16n, Nat.add(z, s)), R.absorb(bs, r, 0n), Nat.mod(R.poly(bs, r), Nat.sub(C.shift(130n, one), 5n)), PY.absorb_poly(one, h1, bs, r))
