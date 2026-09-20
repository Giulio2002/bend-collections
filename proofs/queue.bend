import Base
import ./lib/logic.bend as L
import ./lib/nat.bend as N
import ../spec/queue.bend as S
import ../src/queue.bend as Q
import ../src/deque.bend as DQ
import ../types/queue.bend as E
import ./deque/state.bend as DST
import ./deque/steps.bend as DPS
import ./deque/init.bend as DIN
import ./queue/steps.bend as PS
import ./queue/trace.bend as FT
import ./queue/closed.bend as CL

# Queue: public proof entry point.
#   abstraction  DST.model(sh)  (the elements, oldest first)
#   invariant    DST.good(sh)   (the deque invariant: the Some slots are
#                exactly the window [lo, lo + len) of a perfect slot tree of
#                depth <= 31)
#   shadow       a queue shadow IS a deque shadow; PS.real wraps the deque
#   operations   PS.step_ok  (enqueue = push_back, dequeue = pop_front,
#                peek = peek_front; dequeue/peek on empty -> EmptyQueue),
#                each derived from the checked deque step law
#   traces       trace_new (arbitrary op lists from Q.new)
#   closed       CL.* (the executable `*_at` specializations compute what the
#                parametric definitions compute, so every law transfers)
#
# `room` is the deque's capacity condition (depth + number of enqueues <= 31,
# i.e. at most 2^31 slots); see proofs/deque.bend.

def new_abs(-T: Data) -> {DST.model(T, DIN.initial(T)) == Nil{} : List<&2, T>}:
  DIN.new_model(T)

def new_inv(-T: Data) -> {DST.good(T, DIN.initial(T)) == True{} : Bool}:
  DIN.new_good(T)

def new_real(-T: Data) -> {Q.new(T) == PS.real(T, DIN.initial(T)) : Q.Queue<T>}:
  Equal.cong(DQ.Deque<T>, Q.Queue<T>, d => Q.QU{d}, DQ.new(T), DST.real(T, DIN.initial(T)), DIN.new_real(T))

def step_ok(-T: Data, +sh: DST.Shadow<T>, +op: E.Op<T>, +g: {DST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), PS.pushcost(T, op)), 31n) == True{} : Bool}) -> PS.StepOK(T, sh, op):
  PS.step_ok(T, sh, op, g, room)

# A runtime queue determines its shadow (it is the deque's shadow).
def shadow_unique(-T: Data, +a: DST.Shadow<T>, +b: DST.Shadow<T>, +e: {DST.real(T, a) == DST.real(T, b) : DQ.Deque<T>}) -> {a == b : DST.Shadow<T>}:
  DST.real_inj(T, a, b, e)

def trace_new(-T: Data, +ops: List<&2, E.Op<T>>, +room: {Nat.is_le(Nat.add(0n, FT.pushes(T, ops)), 31n) == True{} : Bool}) -> FT.TraceOK(T, ops, DIN.initial(T)):
  FT.trace_from(T, ops, DIN.initial(T), DIN.new_good(T), room)

def trace_new_at(~T: Data, +ops: List<&2, E.Op<T>>, +room: {Nat.is_le(Nat.add(0n, FT.pushes(T, ops)), 31n) == True{} : Bool}) -> {Q.run_at(~T, ops, PS.real(T, DIN.initial(T))) == Q.run(T, ops, PS.real(T, DIN.initial(T))) : Q.Queue<T> & List<&2, E.Obs<T>>}:
  CL.run_eq(~T, ops, DIN.initial(T), DIN.new_good(T), room)
