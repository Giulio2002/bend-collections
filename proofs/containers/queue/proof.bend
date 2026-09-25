import Base
import ../../../spec/containers/queue.bend as S
import ../../../src/containers/queue.bend as Q
import ../../../src/containers/types/queue.bend as E
import ./state.bend as ST
import ./steps.bend as PS
import ./trace.bend as FT
import ../../lib/logic.bend as L
import ../../../spec/lib/common.bend as SC
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL

# FIFO queue (two lists, src/containers/queue.bend): public proof entry point.
#   shadow       ST.Sh{front, back}: the queue QU{front, back, |front| +
#                |back|}
#   abstraction  ST.model(sh) = front ++ reverse(back), oldest first
#   ready        PS.ready: reversing the back into an empty front keeps the
#                model and leaves the front nonempty unless the queue is empty
#   operations   PS.step_ok: every public operation, errors included
#                (dequeue or peek on an empty queue is Fail{EmptyQueue}, queue
#                unchanged)
#   traces       trace_from / trace_new: any finite operation list, no
#                premise on its length or on the queue's size

def new_abs(~T: Data) -> {ST.model(T, ST.initial(T)) == Nil{} : List<&2, T>}:
  {==}

def new_real(~T: Data) -> {Q.new(~T) == ST.real(T, ST.initial(T)) : Q.Queue<T>}:
  {==}

def step_ok(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> PS.StepOK(~T, sh, op):
  PS.step_ok(~T, sh, op)

# a queue determines its shadow
def shadow_unique(~T: Data, +a: ST.Shadow<T>, +b: ST.Shadow<T>, +e: {ST.real(T, a) == ST.real(T, b) : Q.Queue<T>}) -> {a == b : ST.Shadow<T>}:
  ST.real_inj(T, a, b, e)

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>) -> FT.TraceOK(~T, ops, sh0):
  FT.trace_from(~T, ops, sh0)

# arbitrary finite operation traces from the real constructor
def trace_new(~T: Data, +ops: List<&2, E.Op<T>>) -> FT.TraceOK(~T, ops, ST.initial(T)):
  FT.trace_from(~T, ops, ST.initial(T))

# ==== the contract of queue (stated in spec/containers/queue.bend) ====================

# ---- the implementation ----
def Impl(~T: Data, sh: ST.Shadow<T>, op: E.Op<T>, Post: (List<&2, T> & E.Obs<T>) -> Type) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {Q.step(~T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : Q.Queue<T> & E.Obs<T>} & Post((ST.model(T, sh2), o))>>

def impl_of(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, -Post: (List<&2, T> & E.Obs<T>) -> Type, k: PS.StepOK(~T, sh, op), pf: Post(S.step(T, ST.model(T, sh), op))) -> Impl(~T, sh, op, Post):
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

def new_impl(~T: Data) -> {Q.new(~T) == ST.real(T, ST.initial(T)) : Q.Queue<T>}:
  new_real(~T)

# ---- Append: Length + 1, Equal_Prefix (Model'Old, Model), Element (Last'Old + 1) = New_Item ----
def enqueue_length(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_length(T, xs, v):
  VL.snoc_length(T, xs, v)

def enqueue_prefix(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_prefix(T, xs, v):
  VL.snoc_prefix(T, xs, v)

def enqueue_element(-T: Data, +xs: List<&2, T>, +v: T) -> S.Append.enqueue_element(T, xs, v):
  VL.snoc_last(T, xs, v)

# ---- Delete_First: Length - 1, Range_Shifted (New, Old, First, Last, 1); dequeue returns First_Element'Old ----
def dequeue_length(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_length(T, h, t):
  {==}

def dequeue_shifted(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_shifted(T, h, t):
  VL.tail_shifted(T, h, t)

def dequeue_result(-T: Data, +h: T, +t: List<&2, T>) -> S.Delete_First.dequeue_result(T, h, t):
  {==}

def dequeue_empty(-T: Data) -> S.Delete_First.dequeue_empty(T):
  {==}

# ---- First_Element: Element (Model, First); nothing changes ----
def peek_first(-T: Data, +h: T, +t: List<&2, T>) -> S.First_Element.peek_first(T, h, t):
  ({==}, {==})

def peek_frame(-T: Data, +xs: List<&2, T>) -> S.First_Element.peek_frame(T, xs):
  {==}

def peek_empty(-T: Data) -> S.First_Element.peek_empty(T):
  {==}
