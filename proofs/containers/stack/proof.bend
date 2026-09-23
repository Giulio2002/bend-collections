import Base
import ../../../src/containers/stack.bend as D
import ./spec.bend as S
import ../../lib/spec_common.bend as C
import ../../../src/containers/types/stack.bend as E
import ../../lib/nat.bend as N

# Universal one-step refinement, including cached count preservation and
# empty errors. Concrete instances in STACK_COMPONENT_PROOF.bend.
def real(~T: Data, +xs: List<&2, T>) -> D.Stack<T>:
  D.ST{xs, C.length(T, xs)}

def lift(~T: Data, r: List<&2, T> & E.Obs<T>) -> D.Stack<T> & E.Obs<T>:
  (xs, obs) = r
  (real(~T, xs), obs)

def step_correct(~T: Data, +xs: List<&2, T>, +op: E.Op<T>) -> {D.step(~T, real(~T, xs), op) == lift(~T, S.step(T, xs, op)) : D.Stack<T> & E.Obs<T>}:
  match xs op:
    case Nil{} E.Push{v}:
      {==}
    case Nil{} E.Length{}:
      {==}
    case Nil{} E.ToList{}:
      {==}
    case Nil{} E.Peek{}:
      {==}
    case Nil{} E.Pop{}:
      {==}
    case Con{+x, +tail} E.Push{v}:
      {==}
    case Con{+x, +tail} E.Length{}:
      {==}
    case Con{+x, +tail} E.ToList{}:
      {==}
    case Con{+x, +tail} E.Peek{}:
      {==}
    case Con{+x, +tail} E.Pop{}:
      Equal.cong(Nat, D.Stack<T> & E.Obs<T>, n => (D.ST{tail, n}, E.OItem{Done{x}}), Nat.sub(C.length(T, tail), 0n), C.length(T, tail), N.sub_zero(C.length(T, tail)))

def constructor(~T: Data) -> {D.new(~T) == real(~T, Nil{}) : D.Stack<T>}:
  {==}
