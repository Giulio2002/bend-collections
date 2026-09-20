import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/queue.bend as S
import ../../src/deque.bend as DQ
import ../../src/queue.bend as Q
import ../../types/deque.bend as DE
import ../../types/queue.bend as E
import ../deque/state.bend as ST
import ../deque/steps.bend as DPS
import ./steps.bend as PS
import ../deque/walk.bend as W
import ../deque/trace.bend as DTR

# Arbitrary finite operation traces of the queue: the real runner refines
# the FIFO spec runner. Every step is the deque step of the corresponding
# deque operation (proofs/queue/steps.bend).
#
# The slot array is linear, so the statement is the shadow form the per-step
# laws use: running any finite list of operations on the array of a good
# shadow lands on the array of another good shadow, emits exactly the spec
# runner's observations, and the model of the final shadow is the spec
# runner's final model.
#
# `pushes(ops)` is the number of pushes in the list, and every push doubles
# the block at most once, so ONE premise -- depth + pushes(ops) <= 31 --
# discharges the capacity condition of every step of the trace. It is the
# representation's capacity condition (2^31 slots), nothing more.

def pushes(-T: Data, ops: List<&2, E.Op<T>>) -> Nat:
  match ops:
    case Nil{}:
      0n
    case Con{op, rest}:
      Nat.add(PS.pushcost(T, op), pushes(T, rest))

def budget_head(-T: Data, +d: Nat, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +h: {Nat.is_le(Nat.add(d, pushes(T, Con{op, rest})), 31n) == True{} : Bool}) -> {Nat.is_le(Nat.add(d, PS.pushcost(T, op)), 31n) == True{} : Bool}:
  N.le_trans(Nat.add(d, PS.pushcost(T, op)), Nat.add(d, Nat.add(PS.pushcost(T, op), pushes(T, rest))), 31n,
    W.add_le(d, PS.pushcost(T, op), Nat.add(PS.pushcost(T, op), pushes(T, rest)), N.le_add_right(PS.pushcost(T, op), pushes(T, rest))), h)

def budget_tail(-T: Data, +d: Nat, +d2: Nat, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +hd2: {Nat.is_le(d2, Nat.add(d, PS.pushcost(T, op))) == True{} : Bool}, +h: {Nat.is_le(Nat.add(d, pushes(T, Con{op, rest})), 31n) == True{} : Bool}) -> {Nat.is_le(Nat.add(d2, pushes(T, rest)), 31n) == True{} : Bool}:
  N.le_trans(Nat.add(d2, pushes(T, rest)), Nat.add(Nat.add(d, PS.pushcost(T, op)), pushes(T, rest)), 31n,
    DTR.add_le_l(d2, Nat.add(d, PS.pushcost(T, op)), pushes(T, rest), hd2),
    L.subst(Nat, z => {Nat.is_le(z, 31n) == True{} : Bool}, Nat.add(d, Nat.add(PS.pushcost(T, op), pushes(T, rest))), Nat.add(Nat.add(d, PS.pushcost(T, op)), pushes(T, rest)), Equal.sym(Nat, Nat.add(Nat.add(d, PS.pushcost(T, op)), pushes(T, rest)), Nat.add(d, Nat.add(PS.pushcost(T, op), pushes(T, rest))), N.add_assoc(d, PS.pushcost(T, op), pushes(T, rest))), h))

# ---- projections of a step ----

def so_sh(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> ST.Shadow<T>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> E.Obs<T>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> {Q.step(T, PS.real(T, sh), op) == (PS.real(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) : Q.Queue<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> {ST.good(T, so_sh(T, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> {(ST.model(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      s

def so_depth(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: PS.StepOK(T, sh, op)) -> {Nat.is_le(DPS.sh_depth(T, so_sh(T, sh, op, so)), Nat.add(DPS.sh_depth(T, sh), PS.pushcost(T, op))) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, Tuple{s, dd}}}}}:
      dd

# ---- the run ----

def srun_obs(-T: Data, ops: List<&2, E.Op<T>>, m: List<&2, T>) -> List<&2, E.Obs<T>>:
  Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

def srun_state(-T: Data, ops: List<&2, E.Op<T>>, m: List<&2, T>) -> List<&2, T>:
  Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

def spec_run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +m: List<&2, T>, +m1: List<&2, T>, +o: E.Obs<T>, +e: {(m1, o) == S.step(T, m, op) : List<&2, T> & E.Obs<T>}) -> {S.run(T, Con{op, rest}, m) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}:
  %e : {S.cons_obs(T, Pair.snd(List<&2, T>, E.Obs<T>, _), S.run(T, rest, Pair.fst(List<&2, T>, E.Obs<T>, _))) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, rest, m1), (srun_state(T, rest, m1), srun_obs(T, rest, m1)), L.pair_eta(List<&2, T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))) : {S.cons_obs(T, o, _) == (srun_state(T, rest, m1), Con{o, srun_obs(T, rest, m1)}) : List<&2, T> & List<&2, E.Obs<T>>}
  {==}

def RunOK(-T: Data, ops: List<&2, E.Op<T>>, sh: ST.Shadow<T>, acc: List<&2, E.Obs<T>>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {Q.run_acc(T, ops, (PS.real(T, sh), acc)) == (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>} & ({ST.good(T, sh2) == True{} : Bool} & {ST.model(T, sh2) == srun_state(T, ops, ST.model(T, sh)) : List<&2, T>})>

def ro_sh(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> ST.Shadow<T>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {Q.run_acc(T, ops, (PS.real(T, sh), acc)) == (PS.real(T, ro_sh(T, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {ST.good(T, ro_sh(T, ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {ST.model(T, ro_sh(T, ops, sh, acc, r)) == srun_state(T, ops, ST.model(T, sh)) : List<&2, T>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(-T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {ST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh), pushes(T, ops)), 31n) == True{} : Bool}) -> RunOK(T, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(T, sh)
      +hh = budget_head(T, DPS.sh_depth(T, sh), op, rest, room)
      +sh1 = so_sh(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +o = so_obs(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +g1 = so_good(T, sh, op, PS.step_ok(T, sh, op, g, hh))
      +r1 = budget_tail(T, DPS.sh_depth(T, sh), DPS.sh_depth(T, sh1), op, rest, so_depth(T, sh, op, PS.step_ok(T, sh, op, g, hh)), room)
      +m1 = ST.model(T, sh1)
      +acc1 = {Con{o, acc} : List<&2, E.Obs<T>>}
      +sh2 = ro_sh(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1, r1))
      +es = spec_run_cons(T, op, rest, m, m1, o, so_spec(T, sh, op, PS.step_ok(T, sh, op, g, hh)))
      -R = S.run(T, rest, m1)
      (sh2, (
        %Equal.sym(Q.Queue<T> & E.Obs<T>, Q.step(T, PS.real(T, sh), op), (PS.real(T, sh1), o), so_step(T, sh, op, PS.step_ok(T, sh, op, g, hh))) : {Q.run_acc(T, rest, Q.record(T, acc, _)) == (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>}
        %Equal.sym(Q.Queue<T> & List<&2, E.Obs<T>>, Q.run_acc(T, rest, (PS.real(T, sh1), acc1)), (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)), ro_run(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1, r1))) : {_ == (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>}
        %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, R)}), es) : {(PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)) == (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, _), acc)) : Q.Queue<T> & List<&2, E.Obs<T>>}
        {==},
        (ro_good(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1, r1)),
         %Equal.sym(List<&2, T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(List<&2, T>, List<&2, E.Obs<T>>, R)}), es) : {ST.model(T, sh2) == Pair.fst(List<&2, T>, List<&2, E.Obs<T>>, _) : List<&2, T>}
         ro_model(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1, r1)))))

def run_from(-T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh0), pushes(T, ops)), 31n) == True{} : Bool}) -> {Q.run(T, ops, PS.real(T, sh0)) == (PS.real(T, ro_sh(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room))), srun_obs(T, ops, ST.model(T, sh0))) : Q.Queue<T> & List<&2, E.Obs<T>>}:
  +sh2 = ro_sh(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room))
  +os = srun_obs(T, ops, ST.model(T, sh0))
  %Equal.sym(Q.Queue<T> & List<&2, E.Obs<T>>, Q.run_acc(T, ops, (PS.real(T, sh0), Nil{})), (PS.real(T, sh2), List.reverse.go(&2, E.Obs<T>, os, Nil{})), ro_run(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room))) : {Q.finish(T, _) == (PS.real(T, sh2), os) : Q.Queue<T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, List.reverse.go(&2, E.Obs<T>, os, Nil{})), os, LL.rev_rev(E.Obs<T>, os)) : {(PS.real(T, sh2), _) == (PS.real(T, sh2), os) : Q.Queue<T> & List<&2, E.Obs<T>>}
  {==}

def TraceOK(-T: Data, ops: List<&2, E.Op<T>>, sh0: ST.Shadow<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {Q.run(T, ops, PS.real(T, sh0)) == (PS.real(T, sh2), srun_obs(T, ops, ST.model(T, sh0))) : Q.Queue<T> & List<&2, E.Obs<T>>} & ({ST.good(T, sh2) == True{} : Bool} & {ST.model(T, sh2) == srun_state(T, ops, ST.model(T, sh0)) : List<&2, T>})>

def trace_from(-T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}, +room: {Nat.is_le(Nat.add(DPS.sh_depth(T, sh0), pushes(T, ops)), 31n) == True{} : Bool}) -> TraceOK(T, ops, sh0):
  (ro_sh(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room)),
   (run_from(T, ops, sh0, g0, room),
    (ro_good(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room)),
     ro_model(T, ops, sh0, Nil{}, run_ok(T, ops, sh0, Nil{}, g0, room)))))
