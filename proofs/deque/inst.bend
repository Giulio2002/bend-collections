import Base
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ./state.bend as ST
import ./grow.bend as G
import ./stepok.bend as K
import ./reads.bend as RD
import ./pushes.bend as PU
import ./steps.bend as SP
import ./trace.bend as TR
import ../../types/deque.bend as E

# Instantiations of the ~T templates at U32 (a template is only checked when
# it is instantiated); END_TO_END.bend instantiates the public laws.

def cp_real_u32(+d: Nat, k: Nat, +j: Nat, +lo: Nat, +td: AR.Tree<U32>, +ts: AR.Tree<U32>, +hd: {Nat.is_le(1n+d, 31n) == True{} : Bool}, +pts: {AR.perfect(U32, d, ts) == True{} : Bool}, +ptd: {AR.perfect(U32, 1n+d, td) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hjk: {Nat.is_le(Nat.add(j, k), SC.pow2(d)) == True{} : Bool}) -> {DQ.copy_go(~U32, k, j, lo, SC.pow2(d), AR.thaw(U32, td), (AR.thaw(U32, ts), ST.vat(U32, ts, DQ.wrap(Nat.add(lo, j), SC.pow2(d))))) == AR.thaw(U32, G.cpt(U32, 1n+d, k, j, lo, SC.pow2(d), td, ts)) : Array<U32>}:
  G.cp_real(~U32, d, k, j, lo, td, ts, hd, pts, ptd, hlo, hjk)

def grow_real_u32(+d: Nat, +lo: Nat, +t: AR.Tree<U32>, +v: U32, +hd: {Nat.is_le(1n+d, 31n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}) -> {DQ.grow(~U32, d, SC.pow2(d), lo, SC.pow2(d), AR.thaw(U32, t), v) == AR.thaw(U32, G.gt(U32, d, lo, t, v)) : Array<U32>}:
  G.grow_real(~U32, d, lo, t, v, hd, pf, hlo)


def peekf_ok_u32(+d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PeekFront{}):
  RD.peekf_ok(~U32, d, lo, n, t, g)

def length_ok_u32(+d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.Length{}):
  RD.length_ok(~U32, d, lo, n, t, g)

def peekb_ok_u32(+d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PeekBack{}):
  RD.peekb_ok(~U32, d, lo, n, t, g)

def popb_ok_u32(+d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PopBack{}):
  RD.popb_ok(~U32, d, lo, n, t, g)

def popf_ok_u32(+d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PopFront{}):
  RD.popf_ok(~U32, d, lo, n, t, g)

def tolist_ok_u32(+d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<U32>, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.ToList{}):
  RD.tolist_ok(~U32, d, lo, n, t, g)

def first_back_ok_u32(+v: U32) -> K.StepOK(~U32, ST.S0{}, E.PushBack{v}):
  PU.first_back_ok(~U32, v)

def first_front_ok_u32(+v: U32) -> K.StepOK(~U32, ST.S0{}, E.PushFront{v}):
  PU.first_front_ok(~U32, v)

def pb_room_ok_u32(+d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<U32>, +v: U32, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hr: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PushBack{v}):
  PU.pb_room_ok(~U32, d, lo, n, t, v, g, hr)

def pf_room_ok_u32(+d: Nat, lo: Nat, +n: Nat, +t: AR.Tree<U32>, +v: U32, +g: {ST.good(U32, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hr: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, n, t}, E.PushFront{v}):
  PU.pf_room_ok(~U32, d, lo, n, t, v, g, hr)

def pb_full_ok_u32(+d: Nat, +lo: Nat, +t: AR.Tree<U32>, +v: U32, +g: {ST.good(U32, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}, +hd1: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, SC.pow2(d), t}, E.PushBack{v}):
  PU.pb_full_ok(~U32, d, lo, t, v, g, hd1)

def pf_full_ok_u32(+d: Nat, +lo: Nat, +t: AR.Tree<U32>, +v: U32, +g: {ST.good(U32, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}, +hd1: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> K.StepOK(~U32, ST.Sh{d, lo, SC.pow2(d), t}, E.PushFront{v}):
  PU.pf_full_ok(~U32, d, lo, t, v, g, hd1)

def step_ok_u32(sh: ST.Shadow<U32>, op: E.Op<U32>, +g: {ST.good(U32, sh) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hp: {SP.pushok(U32, q, op, ST.model(U32, sh)) == True{} : Bool}) -> K.StepOK(~U32, sh, op):
  SP.step_ok(~U32, sh, op, g, q, hq, hp)

def trace_from_u32(+ops: List<&2, E.Op<U32>>, +sh0: ST.Shadow<U32>, +g0: {ST.good(U32, sh0) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hf: {TR.fits(U32, q, ops, ST.model(U32, sh0)) == True{} : Bool}) -> TR.TraceOK(~U32, ops, sh0):
  TR.trace_from(~U32, ops, sh0, g0, q, hq, hf)
