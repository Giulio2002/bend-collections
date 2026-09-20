import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../../src/doubly_linked_list.bend as D
import ../../spec/doubly_linked_list.bend as DS
import ../../types/doubly_linked_list.bend as E
import ./steps.bend as ST

# Arbitrary finite operation traces: the real runner refines the spec runner.
# Same construction as tools/generators/trace_data.py, written by hand
# because this invariant (ST.Inv) is a proposition (a Type), not a Bool: it
# is destructured once per step instead of being re-derived.

def view(-T: Data, r: D.DList<T> & List<&2, E.Obs<T>>) -> DS.Model<T> & List<&2, E.Obs<T>>:
  match r:
    case Tuple{d, os}:
      (ST.abs(T, d), os)

def srun_obs(-T: Data, ops: List<&2, E.Op<T>>, m: DS.Model<T>) -> List<&2, E.Obs<T>>:
  Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, ops, m))

def srun_state(-T: Data, ops: List<&2, E.Op<T>>, m: DS.Model<T>) -> DS.Model<T>:
  Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, ops, m))

def next(-T: Data, d: D.DList<T>, op: E.Op<T>) -> D.DList<T>:
  Pair.fst(D.DList<T>, E.Obs<T>, D.step(T, d, op))

def obs(-T: Data, d: D.DList<T>, op: E.Op<T>) -> E.Obs<T>:
  Pair.snd(D.DList<T>, E.Obs<T>, D.step(T, d, op))

def run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +d: D.DList<T>, +acc: List<&2, E.Obs<T>>) -> {D.run_acc(T, Con{op, rest}, (d, acc)) == D.run_acc(T, rest, (next(T, d, op), Con{obs(T, d, op), acc})) : D.DList<T> & List<&2, E.Obs<T>>}:
  %Equal.sym(D.DList<T> & E.Obs<T>, D.step(T, d, op), (next(T, d, op), obs(T, d, op)), L.pair_eta(D.DList<T>, E.Obs<T>, D.step(T, d, op))) : {D.run_acc(T, rest, D.record(T, acc, _)) == D.run_acc(T, rest, (next(T, d, op), Con{obs(T, d, op), acc})) : D.DList<T> & List<&2, E.Obs<T>>}
  {==}

def spec_view(-T: Data, +d: D.DList<T>, +op: E.Op<T>, +ev: {ST.view1(T, D.step(T, d, op)) == DS.step(T, ST.abs(T, d), op) : DS.Model<T> & E.Obs<T>}) -> {(ST.abs(T, next(T, d, op)), obs(T, d, op)) == DS.step(T, ST.abs(T, d), op) : DS.Model<T> & E.Obs<T>}:
  %ev : {(ST.abs(T, next(T, d, op)), obs(T, d, op)) == _ : DS.Model<T> & E.Obs<T>}
  %Equal.sym(D.DList<T> & E.Obs<T>, D.step(T, d, op), (next(T, d, op), obs(T, d, op)), L.pair_eta(D.DList<T>, E.Obs<T>, D.step(T, d, op))) : {(ST.abs(T, next(T, d, op)), obs(T, d, op)) == ST.view1(T, _) : DS.Model<T> & E.Obs<T>}
  {==}

def spec_run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +m: DS.Model<T>, +m1: DS.Model<T>, +ob: E.Obs<T>, +e: {(m1, ob) == DS.step(T, m, op) : DS.Model<T> & E.Obs<T>}) -> {DS.run(T, Con{op, rest}, m) == (srun_state(T, rest, m1), Con{ob, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}:
  %e : {DS.cons_obs(T, Pair.snd(DS.Model<T>, E.Obs<T>, _), DS.run(T, rest, Pair.fst(DS.Model<T>, E.Obs<T>, _))) == (srun_state(T, rest, m1), Con{ob, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, rest, m1), (srun_state(T, rest, m1), srun_obs(T, rest, m1)), L.pair_eta(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, rest, m1))) : {DS.cons_obs(T, ob, _) == (srun_state(T, rest, m1), Con{ob, srun_obs(T, rest, m1)}) : DS.Model<T> & List<&2, E.Obs<T>>}
  {==}

def fin(-T: Data, ops: List<&2, E.Op<T>>, d: D.DList<T>, acc: List<&2, E.Obs<T>>) -> D.DList<T>:
  Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, D.run_acc(T, ops, (d, acc)))

def RunOK(-T: Data, ops: List<&2, E.Op<T>>, d: D.DList<T>, acc: List<&2, E.Obs<T>>) -> Type:
  {D.run_acc(T, ops, (d, acc)) == (fin(T, ops, d, acc), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.abs(T, d)), acc)) : D.DList<T> & List<&2, E.Obs<T>>} & ({ST.abs(T, fin(T, ops, d, acc)) == srun_state(T, ops, ST.abs(T, d)) : DS.Model<T>} & ST.Inv(T, fin(T, ops, d, acc)))

def run_step2(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +d: D.DList<T>, +acc: List<&2, E.Obs<T>>, +ev: {ST.view1(T, D.step(T, d, op)) == DS.step(T, ST.abs(T, d), op) : DS.Model<T> & E.Obs<T>}, r: RunOK(T, rest, next(T, d, op), Con{obs(T, d, op), acc})) -> RunOK(T, Con{op, rest}, d, acc):
  match r:
    case Tuple{+p1, Tuple{+p2, p3}}:
      +d1 = next(T, d, op)
      +ob = obs(T, d, op)
      +acc1 = {Con{ob, acc} : List<&2, E.Obs<T>>}
      +es = spec_run_cons(T, op, rest, ST.abs(T, d), ST.abs(T, d1), ob, spec_view(T, d, op, ev))
      +rc = run_cons(T, op, rest, d, acc)
      (%Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(T, Con{op, rest}, (d, acc)), D.run_acc(T, rest, (d1, acc1)), rc) : {_ == (Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, _), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, ST.abs(T, d)), acc)) : D.DList<T> & List<&2, E.Obs<T>>}
       %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, Con{op, rest}, ST.abs(T, d)), (srun_state(T, rest, ST.abs(T, d1)), Con{ob, srun_obs(T, rest, ST.abs(T, d1))}), es) : {D.run_acc(T, rest, (d1, acc1)) == (fin(T, rest, d1, acc1), List.reverse.go(&2, E.Obs<T>, Pair.snd(DS.Model<T>, List<&2, E.Obs<T>>, _), acc)) : D.DList<T> & List<&2, E.Obs<T>>}
       p1,
       (%Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(T, Con{op, rest}, (d, acc)), D.run_acc(T, rest, (d1, acc1)), rc) : {ST.abs(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, _)) == srun_state(T, Con{op, rest}, ST.abs(T, d)) : DS.Model<T>}
        %Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, Con{op, rest}, ST.abs(T, d)), (srun_state(T, rest, ST.abs(T, d1)), Con{ob, srun_obs(T, rest, ST.abs(T, d1))}), es) : {ST.abs(T, fin(T, rest, d1, acc1)) == Pair.fst(DS.Model<T>, List<&2, E.Obs<T>>, _) : DS.Model<T>}
        p2,
        L.subst(D.DList<T> & List<&2, E.Obs<T>>, z => ST.Inv(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, z)), D.run_acc(T, rest, (d1, acc1)), D.run_acc(T, Con{op, rest}, (d, acc)), Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(T, Con{op, rest}, (d, acc)), D.run_acc(T, rest, (d1, acc1)), rc), p3)))

def run_step(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +d: D.DList<T>, +acc: List<&2, E.Obs<T>>, sp: ST.StepOK(T, d, op), ih: @gg: ST.Inv(T, next(T, d, op)) -> RunOK(T, rest, next(T, d, op), Con{obs(T, d, op), acc})) -> RunOK(T, Con{op, rest}, d, acc):
  match sp:
    case Tuple{+ev, g1}:
      run_step2(T, op, rest, d, acc, ev, ih(g1))

def run_ok(-T: Data, +ops: List<&2, E.Op<T>>, +d: D.DList<T>, +acc: List<&2, E.Obs<T>>, g: ST.Inv(T, d)) -> RunOK(T, ops, d, acc):
  match ops:
    case Nil{}:
      ({==}, ({==}, g))
    case Con{+op, +rest}:
      run_step(T, op, rest, d, acc, ST.step_ok(T, d, op, g), gg => run_ok(T, rest, next(T, d, op), Con{obs(T, d, op), acc}, gg))

def trace2(-T: Data, +ops: List<&2, E.Op<T>>, +d0: D.DList<T>, r: RunOK(T, ops, d0, Nil{})) -> {view(T, D.run(T, ops, d0)) == DS.run(T, ops, ST.abs(T, d0)) : DS.Model<T> & List<&2, E.Obs<T>>}:
  match r:
    case Tuple{+p1, Tuple{+p2, p3}}:
      +m0 = ST.abs(T, d0)
      %Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(T, ops, (d0, Nil{})), (fin(T, ops, d0, Nil{}), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, m0), Nil{})), p1) : {view(T, D.finish(T, _)) == DS.run(T, ops, m0) : DS.Model<T> & List<&2, E.Obs<T>>}
      %Equal.sym(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, m0), Nil{})), srun_obs(T, ops, m0), LL.rev_rev(E.Obs<T>, srun_obs(T, ops, m0))) : {(ST.abs(T, fin(T, ops, d0, Nil{})), _) == DS.run(T, ops, m0) : DS.Model<T> & List<&2, E.Obs<T>>}
      %Equal.sym(DS.Model<T>, ST.abs(T, fin(T, ops, d0, Nil{})), srun_state(T, ops, m0), p2) : {(_, srun_obs(T, ops, m0)) == DS.run(T, ops, m0) : DS.Model<T> & List<&2, E.Obs<T>>}
      Equal.sym(DS.Model<T> & List<&2, E.Obs<T>>, DS.run(T, ops, m0), (srun_state(T, ops, m0), srun_obs(T, ops, m0)), L.pair_eta(DS.Model<T>, List<&2, E.Obs<T>>, DS.run(T, ops, m0)))

# From any state satisfying the invariant, src.run refines spec.run.
def trace_from(-T: Data, +ops: List<&2, E.Op<T>>, +d0: D.DList<T>, g0: ST.Inv(T, d0)) -> {view(T, D.run(T, ops, d0)) == DS.run(T, ops, ST.abs(T, d0)) : DS.Model<T> & List<&2, E.Obs<T>>}:
  trace2(T, ops, d0, run_ok(T, ops, d0, Nil{}, g0))

def inv2(-T: Data, +ops: List<&2, E.Op<T>>, +d0: D.DList<T>, r: RunOK(T, ops, d0, Nil{})) -> ST.Inv(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, D.run(T, ops, d0))):
  match r:
    case Tuple{+p1, Tuple{+p2, p3}}:
      L.subst(D.DList<T> & List<&2, E.Obs<T>>, z => ST.Inv(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, D.finish(T, z))), (fin(T, ops, d0, Nil{}), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.abs(T, d0)), Nil{})), D.run_acc(T, ops, (d0, Nil{})), Equal.sym(D.DList<T> & List<&2, E.Obs<T>>, D.run_acc(T, ops, (d0, Nil{})), (fin(T, ops, d0, Nil{}), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.abs(T, d0)), Nil{})), p1), p3)

def inv_from(-T: Data, +ops: List<&2, E.Op<T>>, +d0: D.DList<T>, g0: ST.Inv(T, d0)) -> ST.Inv(T, Pair.fst(D.DList<T>, List<&2, E.Obs<T>>, D.run(T, ops, d0))):
  inv2(T, ops, d0, run_ok(T, ops, d0, Nil{}, g0))
