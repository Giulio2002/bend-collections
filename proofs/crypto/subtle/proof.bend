import Base
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/subtle.bend as Spec
import ../../lib/logic.bend as L
import ./word.bend as W
import ./fold.bend as SF
import ./laws.bend as Laws

# Gate for src/crypto/subtle.bend: `bend proofs/crypto/subtle/proof.bend`.
#
# The accumulator invariant (the shape of HACL*'s lbytes_eq proof) is in
# fold.bend: after the common prefix, "both lists end together and the
# accumulator is zero" is "the starting accumulator is zero and the lists
# are equal", for the four-pair pass eq runs and the one-pair pass it ends
# with.
def Laws.Eq.value(a, b):
  SF.fold4(a, b, 0)

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
