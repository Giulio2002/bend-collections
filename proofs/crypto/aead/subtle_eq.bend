import Base
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/subtle.bend as SS
import ../../lib/logic.bend as L
import ../subtle/word.bend as SW

# subtle.eq is list equality (the lemmas of proofs/crypto/subtle/proof.bend,
# restated here so that file stays the subtle package's root).

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

law eq_value:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {Subtle.eq(a, b) == SS.equal(a, b) : Bool}

def eq_value(a, b):
  fold(a, b, 0)
