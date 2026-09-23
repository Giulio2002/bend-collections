import Base
import ./spec.bend as S
import ../../../src/containers/queue.bend as Q
import ../../../src/containers/types/queue.bend as E
import ./state.bend as ST
import ./steps.bend as PS
import ./trace.bend as FT

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
