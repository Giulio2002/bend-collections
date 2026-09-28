import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../spec/crypto/subtle.bend as SS
import ../../../src/crypto/subtle.bend as Subtle
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../lib/logic.bend as L
import ../subtle/word.bend as SW
import ./modp.bend as MP
import ./mac.bend as M
import ./laws.bend as Laws

# Entry point: `bend proofs/crypto/poly1305/proof.bend` checks every clause of
# laws.bend. The work is in value.bend (limb values), step.bend (one block),
# modp.bend (the spec's reduction), final.bend (freeze, tag bytes) and
# mac.bend (the accumulator against the spec, block by block).

def Laws.mac_correct(key, msg): M.mac_correct(key, msg)

def Laws.mac_length(key, msg): M.mac_length(key, msg)

def Laws.modp_mod(one, h1, x):
  Equal.trans(Nat, R.modp(x), Nat.mod(x, 1n+M.bpv(one)), Nat.mod(x, Nat.sub(C.shift(130n, one), 5n)), MP.modp_mod(one, h1, M.bpv(one), M.bp5(one, h1), x),
    Equal.cong(Nat, Nat, z => Nat.mod(x, z), 1n+M.bpv(one), Nat.sub(C.shift(130n, one), 5n), Equal.sym(Nat, Nat.sub(C.shift(130n, one), 5n), 1n+M.bpv(one), M.pp_eq(one, h1, M.bpv(one), M.bp5(one, h1)))))

def Laws.poly1305_valid(key, msg, h):
  Equal.trans(Maybe<&2, List<&2, U32>>, P.poly1305(key, msg), Some{P.mac(key, msg)}, Some{R.mac(key, msg)},
    Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => P.when(b, P.mac(key, msg)), P.has_key(key), True{}, h),
    Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, t => Some{t}, P.mac(key, msg), R.mac(key, msg), M.mac_correct(key, msg)))

def Laws.poly1305_invalid(key, msg, h):
  Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => P.when(b, P.mac(key, msg)), P.has_key(key), False{}, h)

# ---- constant-time equality (after proofs/crypto/subtle/proof.bend) ----

law step:
  for +acc: U32
  for +x: U32
  for +y: U32
  for +e: Bool
  {Bool.and(U32.is_eq(U32.or(acc, U32.xor(x, y)), 0), e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}

def step(acc, x, y, e):
  %Equal.sym(Bool, U32.is_eq(U32.or(acc, U32.xor(x, y)), 0),
    Bool.and(U32.is_eq(acc, 0), U32.is_eq(U32.xor(x, y), 0)), SW.u32_or_zero(acc, U32.xor(x, y))) :
    {Bool.and(_, e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}
  %Equal.sym(Bool, U32.is_eq(U32.xor(x, y), 0), U32.is_eq(x, y), SW.u32_xor_zero(x, y)) :
    {Bool.and(Bool.and(U32.is_eq(acc, 0), _), e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}
  SW.and_assoc(U32.is_eq(acc, 0), U32.is_eq(x, y), e)

law fold:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +acc: U32
  {Bool.and(Nat.is_eq(List.length(&2, U32, a), List.length(&2, U32, b)), U32.is_eq(Subtle.diff(a, b, acc), 0)) ==
    Bool.and(U32.is_eq(acc, 0), SS.equal(a, b)) : Bool}

def fold(a, b, acc):
  match a b:
    case Nil{} Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), True{}), U32.is_eq(acc, 0), SW.and_true(U32.is_eq(acc, 0)))
    case Nil{} y <> ys:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), False{}), False{}, SW.and_false(U32.is_eq(acc, 0)))
    case x <> xs Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), False{}), False{}, SW.and_false(U32.is_eq(acc, 0)))
    case x <> xs y <> ys:
      +acc2 = U32.or(acc, U32.xor(x, y))
      Equal.trans(Bool,
        Bool.and(Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, ys)), U32.is_eq(Subtle.diff(xs, ys, acc2), 0)),
        Bool.and(U32.is_eq(acc2, 0), SS.equal(xs, ys)),
        Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), SS.equal(xs, ys))),
        fold(xs, ys, acc2),
        step(acc, x, y, SS.equal(xs, ys)))

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
      fold(pm, t, 0)),
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
    Equal.cong(Bool, Bool, b => Bool.and(P.has_key(key), b), Subtle.eq(P.mac(key, msg), tag), SS.equal(P.mac(key, msg), tag), fold(P.mac(key, msg), tag, 0)),
    rej_c(key, msg, tag, h, SS.equal(P.mac(key, msg), tag), {==}))
