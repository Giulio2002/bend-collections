import Base
import ../../../spec/containers/deque.bend as S
import ../../../src/containers/deque.bend as DQ
import ../../../src/containers/types/deque.bend as E
import ./state.bend as ST
import ./stepok.bend as K
import ./steps.bend as PS
import ./trace.bend as FT
import ../../lib/logic.bend as L
import ../../../spec/lib/common.bend as SC
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL

# Deque (two lists, src/containers/deque.bend): public proof entry point.
#   shadow       ST.Sh{front, back}: the deque DE{front, back, |front|,
#                |back|} (the counts are the list lengths by construction)
#   abstraction  ST.model(sh) = front ++ reverse(back), front first
#   rebalance    proofs/deque/rebalance.bend: ready_front / ready_back move
#                half of the other list over, keep the model, and leave the
#                requested end nonempty unless the deque is empty
#   operations   PS.step_ok: every public operation, errors included (pop or
#                peek on an empty deque is Fail{EmptyDeque}, deque unchanged)
#   traces       trace_from / trace_new: any finite operation list, no
#                premise on its length or on the deque's size
#
# Every law is a template in the element type; END_TO_END.bend instantiates
# them at U32 and String.

def new_abs(~T: Data) -> {ST.model(T, ST.initial(T)) == Nil{} : List<&2, T>}:
  {==}

def new_real(~T: Data) -> {DQ.new(~T) == ST.real(T, ST.initial(T)) : DQ.Deque<T>}:
  {==}

def step_ok(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> K.StepOK(~T, sh, op):
  PS.step_ok(~T, sh, op)

# a deque determines its shadow
def shadow_unique(~T: Data, +a: ST.Shadow<T>, +b: ST.Shadow<T>, +e: {ST.real(T, a) == ST.real(T, b) : DQ.Deque<T>}) -> {a == b : ST.Shadow<T>}:
  ST.real_inj(T, a, b, e)

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>) -> FT.TraceOK(~T, ops, sh0):
  FT.trace_from(~T, ops, sh0)

# arbitrary finite operation traces from the real constructor
def trace_new(~T: Data, +ops: List<&2, E.Op<T>>) -> FT.TraceOK(~T, ops, ST.initial(T)):
  FT.trace_from(~T, ops, ST.initial(T))

# ==== the contract of deque (stated in spec/containers/deque.bend) ====================

# ---- the implementation ----
def Impl(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>, Post: (List<&2, T> & E.Obs<T>) -> Type) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>} & Post((ST.model(T, sh2), o))>>

def impl_of(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, -Post: (List<&2, T> & E.Obs<T>) -> Type, k: K.StepOK(~T, sh, op), pf: Post(S.step(T, ST.model(T, sh), op))) -> Impl(~T, sh, op, Post):
  match k:
    case Tuple{sh2, Tuple{o, Tuple{e1, e2}}}:
      (sh2, (o, (e1, L.subst(List<&2, T> & E.Obs<T>, Post, S.step(T, ST.model(T, sh), op), (ST.model(T, sh2), o), Equal.sym(List<&2, T> & E.Obs<T>, (ST.model(T, sh2), o), S.step(T, ST.model(T, sh), op), e2), pf))))

def impl(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, -Post: (List<&2, T> & E.Obs<T>) -> Type, pf: Post(S.step(T, ST.model(T, sh), op))) -> Impl(~T, sh, op, Post):
  impl_of(~T, sh, op, Post, step_ok(~T, sh, op), pf)

# ---- Length, iteration ----
def length_result(-T: Data, +xs: List<&2, T>) -> S.Length.length_result(T, xs):
  {==}

def length_frame(-T: Data, +xs: List<&2, T>) -> S.Length.length_frame(T, xs):
  {==}

def to_list_model(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_model(T, xs):
  {==}

def to_list_frame(-T: Data, +xs: List<&2, T>) -> S.Iteration.to_list_frame(T, xs):
  {==}

# ---- Empty_Vector ----
def new_empty(~T: Data) -> {SC.length(T, ST.model(T, ST.initial(T))) == 0n : Nat}:
  %Equal.sym(List<&2, T>, ST.model(T, ST.initial(T)), Nil{}, new_abs(~T)) : {SC.length(T, _) == 0n : Nat}
  {==}

def new_impl(~T: Data) -> {DQ.new(~T) == ST.real(T, ST.initial(T)) : DQ.Deque<T>}:
  new_real(~T)

# ---- Prepend: Length + 1, Element (First) = New_Item, Range_Shifted (Old, New, First, Last'Old, 1) ----
def push_front_length(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_front_length(T, xs, v):
  {==}

def push_front_first(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_front_first(T, xs, v):
  {==}

def push_front_shifted(-T: Data, +xs: List<&2, T>, +v: T) -> S.Prepend.push_front_shifted(T, xs, v):
  VL.cons_shifted(T, xs, v)

# ---- Append: Length + 1, Equal_Prefix (Model'Old, Model), Element (Last'Old + 1) = New_Item ----
def push_back_length(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.push_back_length(T, xs, v):
  VL.snoc_length(T, xs, v)

def push_back_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.push_back_prefix(T, xs, v):
  VL.snoc_prefix(T, xs, v)

def push_back_element(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.push_back_element(T, xs, v):
  VL.snoc_last(T, xs, v)

# ---- Delete_First: Length - 1, Range_Shifted (New, Old, First, Last, 1); pop_front returns First_Element'Old ----
def pop_front_length(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_front_length(T, h, t):
  {==}

def pop_front_shifted(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_front_shifted(T, h, t):
  VL.tail_shifted(T, h, t)

def pop_front_result(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.pop_front_result(T, h, t):
  {==}

def pop_front_empty(-T: Data) -> S.Delete_First.pop_front_empty(T):
  {==}

# ---- Delete_Last: Length - 1, Equal_Prefix (Model, Model'Old); pop_back returns Last_Element'Old ----
def pop_back_length(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_back_length(T, h, t):
  VL.init_length(T, t, h)

def pop_back_prefix(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_back_prefix(T, h, t):
  VL.init_prefix(T, t, h)

def pop_back_result(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_back_result(T, h, t):
  %Equal.sym(Maybe<&2, T>, SC.last(T, Con{h, t}), V.last_elem(T, Con{h, t}), VL.last_is_elem(T, t, h)) : {E.OItem{S.item(T, _)} == E.OItem{S.item(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}
  {==}

def pop_back_empty(-T: Data) -> S.Delete_Last.pop_back_empty(T):
  {==}

# ---- First_Element / Last_Element: the end elements; nothing changes ----
def peek_front_first(-T: Data, +h: T, +t: List<&2, T>) -> S.First_Element.peek_front_first(T, h, t):
  ({==}, {==})

def peek_front_frame(-T: Data, +xs: List<&2, T>) -> S.First_Element.peek_front_frame(T, xs):
  {==}

def peek_front_empty(-T: Data) -> S.First_Element.peek_front_empty(T):
  {==}

def peek_back_last(-T: Data, +h: T, +t: List<&2, T>) -> S.Last_Element.peek_back_last(T, h, t):
  %Equal.sym(Maybe<&2, T>, SC.last(T, Con{h, t}), V.last_elem(T, Con{h, t}), VL.last_is_elem(T, t, h)) : {E.OItem{S.item(T, _)} == E.OItem{S.item(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}
  {==}

def peek_back_frame(-T: Data, +xs: List<&2, T>) -> S.Last_Element.peek_back_frame(T, xs):
  {==}

def peek_back_empty(-T: Data) -> S.Last_Element.peek_back_empty(T):
  {==}
