import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../../types/deque.bend as E
import ./state.bend as ST
import ./steps.bend as PS
import ./trace.bend as TR

# The executable specializations DQ.*_at (template element type, so every
# Base.Array call is compiled at a closed type) compute exactly what the
# parametric definitions compute. Every universal law proved about DQ.step
# and DQ.run therefore holds of DQ.step_at and DQ.run_at at each instance.

def tl_go_eq(~T: Data, k: Nat, +lo: Nat, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> {DQ.tl_go_at(~T, k, lo, acc, r) == DQ.tl_go(k, T, lo, acc, r) : Array<Maybe<&2, T>> & List<&2, T>}:
  match k r:
    case 0n Tuple{a, x}:
      {==}
    case 1n+ +m Tuple{a, x}:
      tl_go_eq(~T, m, lo, DQ.cons_mb(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(Nat.add(lo, DQ.dec1(m)))))

def to_list_eq(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.ToList{}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.ToList{}) : DQ.Deque<T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Array<Maybe<&2, T>> & List<&2, T>, DQ.Deque<T> & E.Obs<T>, r => DQ.obs_list(T, DQ.tl_done(T, d, SC.pow2(d), lo, 1n+m, r)),
        DQ.tl_go_at(~T, 1n+m, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))),
        DQ.tl_go(1n+m, T, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))),
        tl_go_eq(~T, 1n+m, lo, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)))))

def push_back_eq(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, room: Bool, +er: {Nat.is_lt(Nat.add(lo, n), SC.pow2(d)) == room : Bool}) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushBack{v}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushBack{v}) : DQ.Deque<T> & E.Obs<T>}:
  match room:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), True{}, er) : {(DQ.pb_room_at(~T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) == (DQ.pb_room(T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), False{}, er) : {(DQ.pb_room_at(~T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) == (DQ.pb_room(T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_back_at(~T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_back_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(Nat.add(lo, n)), Some{v})}, E.OUnit{}) == (DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, Array.set(Maybe<&2, T>, DQ.grown_back(T, d, AR.thaw(Maybe<&2, T>, t)), U32.from_nat(Nat.add(lo, n)), Some{v})}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_back(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_back_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), U32.from_nat(Nat.add(lo, n)), Some{v})}, E.OUnit{}) == (DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(Nat.add(lo, n)), Some{v})}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      {==}

def push_front_eq(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushFront{v}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushFront{v}) : DQ.Deque<T> & E.Obs<T>}:
  match lo:
    case 1n+ +k:
      {==}
    case 0n:
      %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_front_at(~T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t}), ST.grown_front_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), DQ.dec1(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(DQ.dec1(SC.pow2(d))), Some{v})}, E.OUnit{}) == (DQ.DQ{1n+d, Nat.double(SC.pow2(d)), DQ.dec1(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, DQ.grown_front(T, d, AR.thaw(Maybe<&2, T>, t)), U32.from_nat(DQ.dec1(SC.pow2(d))), Some{v})}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_front(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t}), ST.grown_front_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), DQ.dec1(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t}), U32.from_nat(DQ.dec1(SC.pow2(d))), Some{v})}, E.OUnit{}) == (DQ.DQ{1n+d, Nat.double(SC.pow2(d)), DQ.dec1(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(DQ.dec1(SC.pow2(d))), Some{v})}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
      {==}

def pop_front_eq(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PopFront{}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PopFront{}) : DQ.Deque<T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      {==}

def pop_back_eq(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PopBack{}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PopBack{}) : DQ.Deque<T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      {==}

def peek_front_eq(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PeekFront{}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PeekFront{}) : DQ.Deque<T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      {==}

def peek_back_eq(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DQ.step_at(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PeekBack{}) == DQ.step(T, ST.real(T, ST.Sh{d, lo, n, t}), E.PeekBack{}) : DQ.Deque<T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      {==}

def step_eq(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>) -> {DQ.step_at(~T, ST.real(T, sh), op) == DQ.step(T, ST.real(T, sh), op) : DQ.Deque<T> & E.Obs<T>}:
  match sh op:
    case ST.Sh{+d, +lo, +n, +t} E.Length{}:
      {==}
    case ST.Sh{+d, +lo, +n, +t} E.PushFront{+v}:
      push_front_eq(~T, d, lo, n, t, v)
    case ST.Sh{+d, +lo, +n, +t} E.PushBack{+v}:
      push_back_eq(~T, d, lo, n, t, v, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), {==})
    case ST.Sh{+d, +lo, +n, +t} E.PopFront{}:
      pop_front_eq(~T, d, lo, n, t)
    case ST.Sh{+d, +lo, +n, +t} E.PopBack{}:
      pop_back_eq(~T, d, lo, n, t)
    case ST.Sh{+d, +lo, +n, +t} E.PeekFront{}:
      peek_front_eq(~T, d, lo, n, t)
    case ST.Sh{+d, +lo, +n, +t} E.PeekBack{}:
      peek_back_eq(~T, d, lo, n, t)
    case ST.Sh{+d, +lo, +n, +t} E.ToList{}:
      to_list_eq(~T, d, lo, n, t)

def run_acc_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {ST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(PS.sh_depth(T, sh), TR.pushes(T, ops)), 31n) == True{} : Bool}) -> {DQ.run_acc_at(~T, ops, (ST.real(T, sh), acc)) == DQ.run_acc(T, ops, (ST.real(T, sh), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>}:
  match ops:
    case Nil{}:
      {==}
    case Con{+op, +rest}:
      +hh = TR.budget_head(T, PS.sh_depth(T, sh), op, rest, room)
      +sh1 = TR.so_sh(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +o = TR.so_obs(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +g1 = TR.so_good(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +r1 = TR.budget_tail(T, PS.sh_depth(T, sh), PS.sh_depth(T, sh1), op, rest, TR.so_depth(T, sh, op, PS.step_ok(T, sh, op, g, hh)), room)
      %Equal.sym(DQ.Deque<T> & E.Obs<T>, DQ.step_at(~T, ST.real(T, sh), op), DQ.step(T, ST.real(T, sh), op), step_eq(~T, sh, op)) : {DQ.run_acc_at(~T, rest, DQ.record(T, acc, _)) == DQ.run_acc(T, rest, DQ.record(T, acc, DQ.step(T, ST.real(T, sh), op))) : DQ.Deque<T> & List<&2, E.Obs<T>>}
      %Equal.sym(DQ.Deque<T> & E.Obs<T>, DQ.step(T, ST.real(T, sh), op), (ST.real(T, sh1), o), TR.so_step(T, sh, op, PS.step_ok(T, sh, op, g, hh))) : {DQ.run_acc_at(~T, rest, DQ.record(T, acc, _)) == DQ.run_acc(T, rest, DQ.record(T, acc, _)) : DQ.Deque<T> & List<&2, E.Obs<T>>}
      run_acc_eq(~T, rest, sh1, Con{o, acc}, g1, r1)

def run_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +g: {ST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(PS.sh_depth(T, sh), TR.pushes(T, ops)), 31n) == True{} : Bool}) -> {DQ.run_at(~T, ops, ST.real(T, sh)) == DQ.run(T, ops, ST.real(T, sh)) : DQ.Deque<T> & List<&2, E.Obs<T>>}:
  Equal.cong(DQ.Deque<T> & List<&2, E.Obs<T>>, DQ.Deque<T> & List<&2, E.Obs<T>>, r => DQ.finish(T, r), DQ.run_acc_at(~T, ops, (ST.real(T, sh), Nil{})), DQ.run_acc(T, ops, (ST.real(T, sh), Nil{})), run_acc_eq(~T, ops, sh, Nil{}, g, room))

def new_eq(~T: Data) -> {DQ.new_at(~T) == DQ.new(T) : DQ.Deque<T>}:
  {==}
