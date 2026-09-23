import Base
import ./spec.bend as S
import ../../../src/containers/deque.bend as DQ
import ../../../src/containers/types/deque.bend as E
import ./state.bend as ST
import ./stepok.bend as K
import ./steps.bend as PS
import ./trace.bend as FT

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
