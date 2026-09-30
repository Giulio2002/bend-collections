import Base
import ../../../src/containers/stack.bend as D
import ../../../spec/containers/stack.bend as S
import ../../../spec/lib/common.bend as C
import ../../../src/containers/types/stack.bend as E
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL
import ../../lib/array.bend as AR
import ../dynamic_array/layout.bend as LY
import ./chunks.bend as K

# The implementation (src/containers/stack.bend, a stack of array chunks)
# refines the list model: for every good shadow sh (proofs/containers/stack/
# chunks.bend), one step of the actual stack is one step of the model, and
# the stack it returns is again the realization of a good shadow. Concrete
# instances in components.bend.

# The model of an actual stack (proof-level: reads each chunk's array through
# AR.freeze).
def abs(~T: Data, s: D.Stack<T>) -> List<&2, T>:
  match s:
    case D.SE{}:
      Nil{}
    case D.ST{d, n, a, c, r}:
      C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, AR.freeze(Maybe<&2, T>, a)))), abs(~T, r))

def abs_real(~T: Data, +sh: K.Sh<T>) -> {abs(~T, K.real(~T, sh)) == K.model(T, sh) : List<&2, T>}:
  match sh:
    case K.SSE{}:
      {==}
    case K.SST{+d, +n, +t, +c, +r}:
      %Equal.sym(AR.Tree<Maybe<&2, T>>, AR.freeze(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t)), t, AR.freeze_thaw(Maybe<&2, T>, t)) : {C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, _))), abs(~T, K.real(~T, r))) == K.model(T, K.SST{d, n, t, c, r}) : List<&2, T>}
      %Equal.sym(List<&2, T>, abs(~T, K.real(~T, r)), K.model(T, r), abs_real(~T, r)) : {C.append(T, C.reverse(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), _) == K.model(T, K.SST{d, n, t, c, r}) : List<&2, T>}
      {==}

def view1(~T: Data, r: D.Stack<T> & E.Obs<T>) -> List<&2, T> & E.Obs<T>:
  (s, o) = r
  (abs(~T, s), o)

# An actual stack is the realization of a good shadow.
def Inv(~T: Data, s: D.Stack<T>) -> Type:
  Sigma<&1, &1, K.Sh<T>, sh => {s == K.real(~T, sh) : D.Stack<T>} & {K.good(T, sh) == True{} : Bool}>

def refine_of(~T: Data, +sh: K.Sh<T>, +op: E.Op<T>, ok: K.StepOK(~T, sh, op)) -> {view1(~T, D.step(~T, K.real(~T, sh), op)) == S.step(T, K.model(T, sh), op) : List<&2, T> & E.Obs<T>}:
  match ok:
    case Tuple{+sh2, Tuple{+o, Tuple{e, Tuple{g2, em}}}}:
      %Equal.sym(D.Stack<T> & E.Obs<T>, D.step(~T, K.real(~T, sh), op), (K.real(~T, sh2), o), e) : {view1(~T, _) == S.step(T, K.model(T, sh), op) : List<&2, T> & E.Obs<T>}
      %Equal.sym(List<&2, T>, abs(~T, K.real(~T, sh2)), K.model(T, sh2), abs_real(~T, sh2)) : {(_, o) == S.step(T, K.model(T, sh), op) : List<&2, T> & E.Obs<T>}
      em

def inv_of(~T: Data, +sh: K.Sh<T>, +op: E.Op<T>, ok: K.StepOK(~T, sh, op)) -> Inv(~T, Pair.fst(D.Stack<T>, E.Obs<T>, D.step(~T, K.real(~T, sh), op))):
  match ok:
    case Tuple{+sh2, Tuple{+o, Tuple{e, Tuple{g2, em}}}}:
      %Equal.sym(D.Stack<T> & E.Obs<T>, D.step(~T, K.real(~T, sh), op), (K.real(~T, sh2), o), e) : Inv(~T, Pair.fst(D.Stack<T>, E.Obs<T>, _))
      (sh2, ({==}, g2))

# every operation on a good stack is the model's step ...
def step_refines(~T: Data, +sh: K.Sh<T>, +op: E.Op<T>, +g: {K.good(T, sh) == True{} : Bool}) -> {view1(~T, D.step(~T, K.real(~T, sh), op)) == S.step(T, K.model(T, sh), op) : List<&2, T> & E.Obs<T>}:
  refine_of(~T, sh, op, K.step_ok(~T, sh, op, g))

# ... and leaves a good stack
def step_preserves(~T: Data, +sh: K.Sh<T>, +op: E.Op<T>, +g: {K.good(T, sh) == True{} : Bool}) -> Inv(~T, Pair.fst(D.Stack<T>, E.Obs<T>, D.step(~T, K.real(~T, sh), op))):
  inv_of(~T, sh, op, K.step_ok(~T, sh, op, g))

def constructor(~T: Data) -> {D.new(~T) == K.real(~T, K.SSE{}) : D.Stack<T>} & ({K.good(T, K.SSE{}) == True{} : Bool} & {K.model(T, K.SSE{}) == Nil{} : List<&2, T>}):
  ({==}, ({==}, {==}))

# ==== the contract of stack (stated in spec/containers/stack.bend) ====================

# ---- the implementation ----
def impl(~T: Data, +sh: K.Sh<T>, +op: E.Op<T>, +g: {K.good(T, sh) == True{} : Bool}, -Post: (List<&2, T> & E.Obs<T>) -> Type, pf: Post(S.step(T, K.model(T, sh), op))) -> Post(view1(~T, D.step(~T, K.real(~T, sh), op))):
  L.subst(List<&2, T> & E.Obs<T>, Post, S.step(T, K.model(T, sh), op), view1(~T, D.step(~T, K.real(~T, sh), op)), Equal.sym(List<&2, T> & E.Obs<T>, view1(~T, D.step(~T, K.real(~T, sh), op)), S.step(T, K.model(T, sh), op), step_refines(~T, sh, op, g)), pf)

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

def new_impl(~T: Data) -> {D.new(~T) == K.real(~T, K.SSE{}) : D.Stack<T>} & ({K.good(T, K.SSE{}) == True{} : Bool} & {K.model(T, K.SSE{}) == Nil{} : List<&2, T>}):
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
