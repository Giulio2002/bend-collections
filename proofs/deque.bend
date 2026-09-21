import Base
import ./lib/logic.bend as L
import ../spec/common.bend as SC
import ../spec/deque.bend as S
import ../src/deque.bend as DQ
import ../types/deque.bend as E
import ./deque/state.bend as ST
import ./deque/stepok.bend as K
import ./deque/steps.bend as PS
import ./deque/trace.bend as FT

# Deque (ring buffer, src/deque.bend): public proof entry point.
#   abstraction  ST.model(sh) = take(rot(slots, lo), len)  (the elements,
#                front first: the first len ring positions from offset lo)
#   invariant    ST.good(sh)  (depth <= 31, so every slot index is a
#                representable U32 and the block a valid Base.Array; the slot
#                tree is perfect of that depth; lo < 2^depth; len <= 2^depth)
#   shadow       ST.S0 (never held an element: no block) | ST.Sh{d, lo, len,
#                t} (block thaw(t)); Base.Array is linear, so every law is
#                about the deque BUILT from a Data mirror tree, as for the
#                other array-backed structures
#   ring layer   proofs/deque/ring.bend: reading/writing slot wrap(lo + j) is
#                reading/writing position j of the rotation; moving lo one
#                slot right rotates by one position
#   growth       proofs/deque/grow.bend: growing a full ring copies it, in
#                order, into slots 0 .. len - 1 of a block twice as large
#   operations   PS.step_ok -- every public operation including the errors
#                (pop/peek on an empty deque: Fail{EmptyDeque}, unchanged)
#   traces       trace_from / trace_new
#
# The capacity condition of the representation is on the PEAK size only: a
# push onto a deque holding fewer than 2^q elements (q <= 31) is proven; a
# full ring of 2^d elements grows to 2^(d+1) slots, and 2^d < 2^q <= 2^31
# keeps every block within the 2^31 slots a Base.Array indexes. For a trace
# the condition is FT.fits: every push happens while the deque holds fewer
# than 2^q elements. It does not bound the length of the trace or the number
# of pushes (the drifting-window representation it replaces needed a bound
# on the lifetime number of pushes; see docs/archive).
#
# Every definition is a template in the element type; END_TO_END.bend
# instantiates the laws at U32 and String.

def new_abs(~T: Data) -> {ST.model(T, ST.initial(T)) == Nil{} : List<&2, T>}:
  {==}

def new_inv(~T: Data) -> {ST.good(T, ST.initial(T)) == True{} : Bool}:
  {==}

def new_real(~T: Data) -> {DQ.new(~T) == ST.real(T, ST.initial(T)) : DQ.Deque<T>}:
  {==}

def step_ok(~T: Data, +sh: ST.Shadow<T>, op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {PS.pushok(T, q, op, ST.model(T, sh)) == True{} : Bool}) -> K.StepOK(~T, sh, op):
  PS.step_ok(~T, sh, op, g, q, hq, hp)

# A runtime deque determines its shadow, so naming the shadow an operation
# lands on pins the abstract state.
def shadow_unique(~T: Data, +a: ST.Shadow<T>, +b: ST.Shadow<T>, +e: {ST.real(T, a) == ST.real(T, b) : DQ.Deque<T>}) -> {a == b : ST.Shadow<T>}:
  ST.real_inj(T, a, b, e)

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hf: {FT.fits(T, q, ops, ST.model(T, sh0)) == True{} : Bool}) -> FT.TraceOK(~T, ops, sh0):
  FT.trace_from(~T, ops, sh0, g0, q, hq, hf)

# Arbitrary finite operation traces from the real constructor.
def trace_new(~T: Data, +ops: List<&2, E.Op<T>>, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hf: {FT.fits(T, q, ops, Nil{}) == True{} : Bool}) -> FT.TraceOK(~T, ops, ST.initial(T)):
  FT.trace_from(~T, ops, ST.initial(T), {==}, q, hq, hf)
