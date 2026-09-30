import Base
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/subtle.bend as Spec
import ../../lib/logic.bend as L
import ./word.bend as W
import ./laws.bend as Laws

# Gate for src/crypto/subtle.bend: `bend proofs/crypto/subtle/proof.bend`.
#
# The accumulator invariant (the shape of HACL*'s lbytes_eq proof): after
# the common prefix, "lengths agree and the accumulator is zero" is "the
# starting accumulator is zero and the lists are equal".
law step:
  for +acc: U32
  for +x: U32
  for +y: U32
  for +e: Bool
  {Bool.and(U32.is_eq(U32.or(acc, U32.xor(x, y)), 0), e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}

def step(acc, x, y, e):
  %Equal.sym(Bool, U32.is_eq(U32.or(acc, U32.xor(x, y)), 0),
    Bool.and(U32.is_eq(acc, 0), U32.is_eq(U32.xor(x, y), 0)), W.u32_or_zero(acc, U32.xor(x, y))) :
    {Bool.and(_, e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}
  %Equal.sym(Bool, U32.is_eq(U32.xor(x, y), 0), U32.is_eq(x, y), W.u32_xor_zero(x, y)) :
    {Bool.and(Bool.and(U32.is_eq(acc, 0), _), e) == Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), e)) : Bool}
  W.and_assoc(U32.is_eq(acc, 0), U32.is_eq(x, y), e)

law fold:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +acc: U32
  {Bool.and(Nat.is_eq(List.length(&2, U32, a), List.length(&2, U32, b)), U32.is_eq(Subtle.diff(a, b, acc), 0)) ==
    Bool.and(U32.is_eq(acc, 0), Spec.equal(a, b)) : Bool}

def fold(a, b, acc):
  match a b:
    case Nil{} Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), True{}), U32.is_eq(acc, 0), W.and_true(U32.is_eq(acc, 0)))
    case Nil{} y <> ys:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), False{}), False{}, W.and_false(U32.is_eq(acc, 0)))
    case x <> xs Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_eq(acc, 0), False{}), False{}, W.and_false(U32.is_eq(acc, 0)))
    case x <> xs y <> ys:
      +acc2 = U32.or(acc, U32.xor(x, y))
      Equal.trans(Bool,
        Bool.and(Nat.is_eq(List.length(&2, U32, xs), List.length(&2, U32, ys)), U32.is_eq(Subtle.diff(xs, ys, acc2), 0)),
        Bool.and(U32.is_eq(acc2, 0), Spec.equal(xs, ys)),
        Bool.and(U32.is_eq(acc, 0), Bool.and(U32.is_eq(x, y), Spec.equal(xs, ys))),
        fold(xs, ys, acc2),
        step(acc, x, y, Spec.equal(xs, ys)))

def Laws.Eq.value(a, b):
  fold(a, b, 0)

law equal_sound:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {Spec.equal(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

def equal_sound(a, b, h):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> ys:
      Empty.absurd({Nil{} == y <> ys : List<&2, U32>}, L.false_true(h))
    case x <> xs Nil{}:
      Empty.absurd({x <> xs == Nil{} : List<&2, U32>}, L.false_true(h))
    case x <> xs y <> ys:
      +exy = W.u32_sound(x, y, L.and_left(U32.is_eq(x, y), Spec.equal(xs, ys), h))
      +et = equal_sound(xs, ys, L.and_right(U32.is_eq(x, y), Spec.equal(xs, ys), h))
      %et : {x <> xs == y <> _ : List<&2, U32>}
      %exy : {x <> xs == _ <> xs : List<&2, U32>}
      {==}

def Laws.Eq.sound(a, b, h):
  equal_sound(a, b, Equal.trans(Bool, Spec.equal(a, b), Subtle.eq(a, b), True{},
    Equal.sym(Bool, Subtle.eq(a, b), Spec.equal(a, b), Laws.Eq.value(a, b)), h))

law equal_refl:
  for +a: List<&2, U32>
  {Spec.equal(a, a) == True{} : Bool}

def equal_refl(a):
  match a:
    case Nil{}:
      {==}
    case x <> xs:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, W.u32_refl(x)) : {Bool.and(_, Spec.equal(xs, xs)) == True{} : Bool}
      equal_refl(xs)

def Laws.Eq.refl(a):
  %Equal.sym(Bool, Subtle.eq(a, a), Spec.equal(a, a), Laws.Eq.value(a, a)) : {_ == True{} : Bool}
  equal_refl(a)
