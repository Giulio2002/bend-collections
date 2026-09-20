import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../../src/queue.bend as Q
import ../../types/deque.bend as DE
import ../../types/queue.bend as E
import ../deque/state.bend as DST
import ../deque/steps.bend as DPS
import ../deque/closed.bend as DCL
import ./steps.bend as PS
import ./trace.bend as TR

# The executable specializations Q.*_at compute exactly what the parametric
# definitions compute: each of them is the deque specialization of the
# corresponding deque operation, and proofs/deque/closed.bend has already
# proved those equal.

def push_back_eq(~T: Data, +sh: DST.Shadow<T>, +v: T) -> {DQ.push_back_at(~T, DST.real(T, sh), v) == DQ.push_back(T, DST.real(T, sh), v) : DQ.Deque<T>}:
  L.pair_fst(DQ.Deque<T>, DE.Obs<T>, DQ.push_back_at(~T, DST.real(T, sh), v), DE.OUnit{}, DQ.push_back(T, DST.real(T, sh), v), DE.OUnit{},
    DCL.step_eq(~T, sh, DE.PushBack{v}))

def pop_front_eq(~T: Data, +sh: DST.Shadow<T>) -> {DQ.pop_front_at(~T, DST.real(T, sh)) == DQ.pop_front(T, DST.real(T, sh)) : DQ.Deque<T> & Result<&2, &2, DE.Error, T>}:
  match sh:
    case DST.Sh{+d, +lo, +n, +t}:
      match n:
        case 0n:
          {==}
        case 1n+ +m:
          {==}

def peek_front_eq(~T: Data, +sh: DST.Shadow<T>) -> {DQ.peek_front_at(~T, DST.real(T, sh)) == DQ.peek_front(T, DST.real(T, sh)) : DQ.Deque<T> & Result<&2, &2, DE.Error, T>}:
  match sh:
    case DST.Sh{+d, +lo, +n, +t}:
      match n:
        case 0n:
          {==}
        case 1n+ +m:
          {==}

def to_list_eq(~T: Data, +sh: DST.Shadow<T>) -> {DQ.to_list_at(~T, DST.real(T, sh)) == DQ.to_list(T, DST.real(T, sh)) : DQ.Deque<T> & List<&2, T>}:
  match sh:
    case DST.Sh{+d, +lo, +n, +t}:
      match n:
        case 0n:
          {==}
        case 1n+ +m:
          Equal.cong(Array<Maybe<&2, T>> & List<&2, T>, DQ.Deque<T> & List<&2, T>, r => DQ.tl_done(T, d, SC.pow2(d), lo, 1n+m, r),
            DQ.tl_go_at(~T, 1n+m, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))),
            DQ.tl_go(1n+m, T, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))),
            DCL.tl_go_eq(~T, 1n+m, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))))

def step_eq(~T: Data, +sh: DST.Shadow<T>, +op: E.Op<T>) -> {Q.step_at(~T, PS.real(T, sh), op) == Q.step(T, PS.real(T, sh), op) : Q.Queue<T> & E.Obs<T>}:
  match op:
    case E.Length{}:
      {==}
    case E.Enqueue{+v}:
      Equal.cong(DQ.Deque<T>, Q.Queue<T> & E.Obs<T>, z => (Q.QU{z}, E.OUnit{}),
        DQ.push_back_at(~T, DST.real(T, sh), v), DQ.push_back(T, DST.real(T, sh), v), push_back_eq(~T, sh, v))
    case E.Dequeue{}:
      Equal.cong(DQ.Deque<T> & Result<&2, &2, DE.Error, T>, Q.Queue<T> & E.Obs<T>, r => Q.obs_item(T, Q.lift(T, r)),
        DQ.pop_front_at(~T, DST.real(T, sh)), DQ.pop_front(T, DST.real(T, sh)), pop_front_eq(~T, sh))
    case E.Peek{}:
      Equal.cong(DQ.Deque<T> & Result<&2, &2, DE.Error, T>, Q.Queue<T> & E.Obs<T>, r => Q.obs_item(T, Q.lift(T, r)),
        DQ.peek_front_at(~T, DST.real(T, sh)), DQ.peek_front(T, DST.real(T, sh)), peek_front_eq(~T, sh))
    case E.ToList{}:
      Equal.cong(DQ.Deque<T> & List<&2, T>, Q.Queue<T> & E.Obs<T>, r => Q.obs_list(T, Q.lift_list(T, r)),
        DQ.to_list_at(~T, DST.real(T, sh)), DQ.to_list(T, DST.real(T, sh)), to_list_eq(~T, sh))

def run_acc_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: DST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {DST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), TR.pushes(T, ops)), 31n) == True{} : Bool}) -> {Q.run_acc_at(~T, ops, (PS.real(T, sh), acc)) == Q.run_acc(T, ops, (PS.real(T, sh), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>}:
  match ops:
    case Nil{}:
      {==}
    case Con{+op, +rest}:
      +hh = TR.budget_head(T, DPS.sh_depth(T, sh), op, rest, room)
      +sh1 = TR.so_sh(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +o = TR.so_obs(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +g1 = TR.so_good(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +r1 = TR.budget_tail(T, DPS.sh_depth(T, sh), DPS.sh_depth(T, sh1), op, rest, TR.so_depth(T, sh, op, PS.step_ok(T, sh, op, g, hh)), room)
      %Equal.sym(Q.Queue<T> & E.Obs<T>, Q.step_at(~T, PS.real(T, sh), op), Q.step(T, PS.real(T, sh), op), step_eq(~T, sh, op)) : {Q.run_acc_at(~T, rest, Q.record(T, acc, _)) == Q.run_acc(T, rest, Q.record(T, acc, Q.step(T, PS.real(T, sh), op))) : Q.Queue<T> & List<&2, E.Obs<T>>}
      %Equal.sym(Q.Queue<T> & E.Obs<T>, Q.step(T, PS.real(T, sh), op), (PS.real(T, sh1), o), TR.so_step(T, sh, op, PS.step_ok(T, sh, op, g, hh))) : {Q.run_acc_at(~T, rest, Q.record(T, acc, _)) == Q.run_acc(T, rest, Q.record(T, acc, _)) : Q.Queue<T> & List<&2, E.Obs<T>>}
      run_acc_eq(~T, rest, sh1, Con{o, acc}, g1, r1)

def run_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: DST.Shadow<T>, +g: {DST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), TR.pushes(T, ops)), 31n) == True{} : Bool}) -> {Q.run_at(~T, ops, PS.real(T, sh)) == Q.run(T, ops, PS.real(T, sh)) : Q.Queue<T> & List<&2, E.Obs<T>>}:
  Equal.cong(Q.Queue<T> & List<&2, E.Obs<T>>, Q.Queue<T> & List<&2, E.Obs<T>>, r => Q.finish(T, r), Q.run_acc_at(~T, ops, (PS.real(T, sh), Nil{})), Q.run_acc(T, ops, (PS.real(T, sh), Nil{})), run_acc_eq(~T, ops, sh, Nil{}, g, room))

def new_eq(~T: Data) -> {Q.new_at(~T) == Q.new(T) : Q.Queue<T>}:
  {==}
