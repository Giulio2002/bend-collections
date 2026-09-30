import Base
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/subtle.bend as SS
import ../../lib/logic.bend as L
import ../subtle/word.bend as SW
import ../subtle/fold.bend as SF

# subtle.eq is list equality (the lemmas of proofs/crypto/subtle/proof.bend,
# restated here so that file stays the subtle package's root).

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
  SF.fold4(a, b, 0)
