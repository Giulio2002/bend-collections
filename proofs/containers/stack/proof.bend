import Base
import ../../../src/containers/stack.bend as D
import ../../../spec/containers/stack.bend as S
import ../../../spec/lib/common.bend as C
import ../../../src/containers/types/stack.bend as E
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL

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

# ==== the contract of stack (stated in spec/containers/stack.bend) ====================

# ---- the implementation ----
def impl(~T: Data, +xs: List<&2, T>, +op: E.Op<T>, -Post: (D.Stack<T> & E.Obs<T>) -> Type, pf: Post(lift(~T, S.step(T, xs, op)))) -> Post(D.step(~T, real(~T, xs), op)):
  L.subst(D.Stack<T> & E.Obs<T>, Post, lift(~T, S.step(T, xs, op)), D.step(~T, real(~T, xs), op), Equal.sym(D.Stack<T> & E.Obs<T>, D.step(~T, real(~T, xs), op), lift(~T, S.step(T, xs, op)), step_correct(~T, xs, op)), pf)

# ---- Length, iteration ----
def length_result(-T: Data, +xs: List<&2, T>) -> S.Length.length_result(T, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def length_frame(-T: Data, +xs: List<&2, T>) -> S.Length.length_frame(T, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def to_list_model(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_model(T, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def to_list_frame(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_frame(T, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# ---- Empty_Vector ----
def new_empty(-T: Data) -> S.Empty_Vector.new_empty(T):
  {==}

def new_impl(~T: Data) -> {D.new(~T) == real(~T, Nil{}) : D.Stack<T>}:
  constructor(~T)

# ---- Prepend: Length + 1, Element (First) = New_Item, Range_Shifted (Old, New, First, Last'Old, 1) ----
def push_length(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_length(T, xs, v):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def push_first(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_first(T, xs, v):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def push_is(-T: Data, +xs: List<&2, T>, +v: T) -> {S.nx(T, xs, E.Push{v}) == Con{v, xs} : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def push_shifted(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_shifted(T, xs, v):
  L.subst(List<&2, T>, z => V.RangeShifted(T, xs, z, 0n, C.length(T, xs), 1n), Con{v, xs}, S.nx(T, xs, E.Push{v}), Equal.sym(List<&2, T>, S.nx(T, xs, E.Push{v}), Con{v, xs}, push_is(T, xs, v)), VL.cons_shifted(T, xs, v))

# ---- Delete_First: Length - 1, Range_Shifted (New, Old, First, Last, 1); pop returns First_Element'Old ----
def pop_length(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_length(T, h, t):
  {==}

def pop_shifted(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_shifted(T, h, t):
  VL.tail_shifted(T, h, t)

def pop_result(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_result(T, h, t):
  {==}

def pop_empty(-T: Data) -> S.Delete_First.pop_empty(T):
  {==}

# ---- First_Element: Element (Model, First); nothing changes ----
def peek_first(-T: Data, +h: T, +t: List<&2, T>) -> S.First_Element.peek_first(T, h, t):
  ({==}, {==})

def peek_frame(-T: Data, +xs: List<&2, T>) -> S.First_Element.peek_frame(T, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def peek_empty(-T: Data) -> S.First_Element.peek_empty(T):
  {==}
