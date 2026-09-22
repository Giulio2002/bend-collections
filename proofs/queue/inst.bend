import Base
import ../deque/state.bend as DST
import ../../src/containers/types/queue.bend as E
import ./steps.bend as PS
import ../deque/steps.bend as DPS
import ./trace.bend as TR

def step_ok_u32(+sh: DST.Shadow<U32>, +op: E.Op<U32>, +g: {DST.good(U32, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {DPS.pushok(U32, q, PS.dop(U32, op), DST.model(U32, sh)) == True{} : Bool}) -> PS.StepOK(~U32, sh, op):
  PS.step_ok(~U32, sh, op, g, q, hq, hp)


def trace_u32(+ops: List<&2, E.Op<U32>>, +sh0: DST.Shadow<U32>, +g0: {DST.good(U32, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hf: {TR.fits(U32, q, ops, DST.model(U32, sh0)) == True{} : Bool}) -> TR.TraceOK(~U32, ops, sh0):
  TR.trace_from(~U32, ops, sh0, g0, q, hq, hf)
