import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ./spec.bend as S
import ../../../src/containers/deque.bend as DQ
import ../../../src/containers/types/deque.bend as E
import ./state.bend as ST
import ./stepok.bend as K
import ./steps.bend as PS

# Arbitrary finite operation traces: the real runner refines the spec
# runner. Running any list of operations on the deque of a shadow lands on
# the deque of another shadow, emits exactly the spec runner's observations,
# and the final shadow's model is the spec runner's final state. There is no
# size or length premise.

# ---- projections of a step ----

def so_sh(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> ST.Shadow<T>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> E.Obs<T>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {DQ.step(~T, ST.real(T, sh), op) == (ST.real(T, so_sh(~T, sh, op, so)), so_obs(~T, sh, op, so)) : DQ.Deque<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, s}}}:
      e

def so_spec(~T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: K.StepOK(~T, sh, op)) -> {(ST.model(T, so_sh(~T, sh, op, so)), so_obs(~T, sh, op, so)) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, s}}}:
      s

# ---- the run ----

def srun_obs(-T: Data, ops: List<&2, E.Op<T>>, m: List<&2, T>) -> List<&2, E.Obs<T>>:
  Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

def srun_state(-T: Data, ops: List<&2, E.Op<T>>, m: List<&2, T>) -> List<&2, T>:
  Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

def spec_run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +m: List<&2, T>, +m1: List<&2, T>, +o: E.Obs<T>, +e: {(m1, o) == S.step(T, m, op) : List<&2, T> & E.Obs<T>}) -> {S.run(T, Con{op, rest}, m) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}:
  %e : {S.cons_obs(T, Pair.snd(List<&2, T>, E.Obs<T>, _), S.run(T, rest, Pair.fst(List<&2, T>, E.Obs<T>, _))) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, rest, m1), (srun_state(T, rest, m1), srun_obs(T, rest, m1)), L.pair_eta(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))) : {S.cons_obs(T, o, _) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}
  {==}

def RunOK(~T: Data, ops: List<&2, E.Op<T>>, sh: ST.Shadow<T>, acc: List<&2, E.Obs<T>>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {DQ.run_acc(~T, ops, (ST.real(T, sh), acc)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>} & {ST.model(T, sh2) == srun_state(T, ops, ST.model(T, sh)) : List<&2, T>}>

def ro_sh(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> ST.Shadow<T>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> {DQ.run_acc(~T, ops, (ST.real(T, sh), acc)) == (ST.real(T, ro_sh(~T, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>}:
  match r:
    case Tuple{sh2, Tuple{e, m}}:
      e

def ro_model(~T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(~T, ops, sh, acc)) -> {ST.model(T, ro_sh(~T, ops, sh, acc, r)) == srun_state(T, ops, ST.model(T, sh)) : List<&2, T>}:
  match r:
    case Tuple{sh2, Tuple{e, m}}:
      m

def run_ok(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>) -> RunOK(~T, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, {==}))
    case Con{+op, +rest}:
      +m = ST.model(T, sh)
      +sh1 = so_sh(~T, sh, op, PS.step_ok(~T, sh, op))
      +o = so_obs(~T, sh, op, PS.step_ok(~T, sh, op))
      +m1 = ST.model(T, sh1)
      +acc1 = {Con{o, acc} : List<&2, E.Obs<T>>}
      +sh2 = ro_sh(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1))
      +es = spec_run_cons(T, op, rest, m, m1, o, so_spec(~T, sh, op, PS.step_ok(~T, sh, op)))
      -R = S.run(T, rest, m1)
      (sh2, (
        %Equal.sym(DQ.Deque<T> & E.Obs<T>, DQ.step(~T, ST.real(T, sh), op), (ST.real(T, sh1), o), so_step(~T, sh, op, PS.step_ok(~T, sh, op))) : {DQ.run_acc(~T, rest, DQ.record(~T, acc, _)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>}
        %Equal.sym(DQ.Deque<T> & List<&2, E.Obs<T>>, DQ.run_acc(~T, rest, (ST.real(T, sh1), acc1)), (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)), ro_run(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1))) : {_ == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>}
        %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, R)}), es) : {(ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, _), acc)) : DQ.Deque<T> & List<&2, E.Obs<T>>}
        {==},
        %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, R)}), es) : {ST.model(T, sh2) == Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, _) : List<&2, T>}
        ro_model(~T, rest, sh1, acc1, run_ok(~T, rest, sh1, acc1))))

def run_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>) -> {DQ.run(~T, ops, ST.real(T, sh0)) == (ST.real(T, ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}))), srun_obs(T, ops, ST.model(T, sh0))) : DQ.Deque<T> & List<&2, E.Obs<T>>}:
  +sh2 = ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}))
  +os = srun_obs(T, ops, ST.model(T, sh0))
  %Equal.sym(DQ.Deque<T> & List<&2, E.Obs<T>>, DQ.run_acc(~T, ops, (ST.real(T, sh0), Nil{})), (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, os, Nil{})), ro_run(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}))) : {DQ.finish(~T, _) == (ST.real(T, sh2), os) : DQ.Deque<T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, List.reverse.go(&2, E.Obs<T>, os, Nil{})), os, LL.rev_rev(E.Obs<T>, os)) : {(ST.real(T, sh2), _) == (ST.real(T, sh2), os) : DQ.Deque<T> & List<&2, E.Obs<T>>}
  {==}

def TraceOK(~T: Data, ops: List<&2, E.Op<T>>, sh0: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {DQ.run(~T, ops, ST.real(T, sh0)) == (ST.real(T, sh2), srun_obs(T, ops, ST.model(T, sh0))) : DQ.Deque<T> & List<&2, E.Obs<T>>} & {ST.model(T, sh2) == srun_state(T, ops, ST.model(T, sh0)) : List<&2, T>}>

def trace_from(~T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>) -> TraceOK(~T, ops, sh0):
  (ro_sh(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{})),
   (run_from(~T, ops, sh0),
    ro_model(~T, ops, sh0, Nil{}, run_ok(~T, ops, sh0, Nil{}))))
