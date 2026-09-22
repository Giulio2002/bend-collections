import Base
import ./lib/logic.bend as L
import ./spec/queue.bend as S
import ../src/containers/queue.bend as Q
import ../src/containers/deque.bend as DQ
import ../src/containers/types/queue.bend as E
import ./deque/state.bend as DST
import ./deque/steps.bend as DPS
import ./queue/steps.bend as PS
import ./queue/trace.bend as FT

# Queue: public proof entry point.
#   abstraction  DST.model(sh)  (the elements, oldest first)
#   invariant    DST.good(sh)   (the ring deque invariant)
#   shadow       a queue shadow IS a ring deque shadow; PS.real wraps the deque
#   operations   PS.step_ok  (enqueue = push_back, dequeue = pop_front,
#                peek = peek_front; dequeue/peek on empty -> EmptyQueue,
#                unchanged), each derived from the checked deque step law
#   traces       trace_new (arbitrary op lists from Q.new)
#
# The capacity condition is the deque's (proofs/deque.bend): an enqueue onto
# a queue holding fewer than 2^q elements (q <= 31); for a trace, FT.fits. It
# bounds the peak size, not the length of a trace.

def new_abs(~T: Data) -> {DST.model(T, DST.initial(T)) == Nil{} : List<&2, T>}:
  {==}

def new_inv(~T: Data) -> {DST.good(T, DST.initial(T)) == True{} : Bool}:
  {==}

def new_real(~T: Data) -> {Q.new(~T) == PS.real(~T, DST.initial(T)) : Q.Queue<T>}:
  {==}

def step_ok(~T: Data, +sh: DST.Shadow<T>, +op: E.Op<T>, +g: {DST.good(T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {DPS.pushok(T, q, PS.dop(T, op), DST.model(T, sh)) == True{} : Bool}) -> PS.StepOK(~T, sh, op):
  PS.step_ok(~T, sh, op, g, q, hq, hp)

def trace_new(~T: Data, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hf: {FT.fits(T, q, ops, Nil{}) == True{} : Bool}) -> FT.TraceOK(~T, ops, DST.initial(T)):
  FT.trace_from(~T, ops, DST.initial(T), {==}, q, hq, hf)
