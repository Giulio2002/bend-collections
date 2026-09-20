import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../src/fenwick_tree.bend as F
import ../../spec/fenwick_tree.bend as S
import ../../types/fenwick_tree.bend as E
import ./state.bend as ST
import ./steps.bend as PS

# Arbitrary finite operation traces: the real runner refines the spec runner.
#
# The cell array is linear, so the statement is the same shadow form the per-step
# laws use: running any finite list of operations on the array of a good
# shadow lands on the array of another good shadow, emits exactly the spec
# runner's observations, and the model of the final shadow is the spec
# runner's final model.

def srun_obs(ops: List<&2, E.Op>, m: List<&2, U32>) -> List<&2, E.Obs>:
  Pair.snd(List<&2, U32>, List<&2, E.Obs>, S.run(ops, m))

def srun_state(ops: List<&2, E.Op>, m: List<&2, U32>) -> List<&2, U32>:
  Pair.fst(List<&2, U32>, List<&2, E.Obs>, S.run(ops, m))

def so_sh(-sh: ST.Sh, -op: E.Op, so: PS.StepOK(sh, op)) -> ST.Sh:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-sh: ST.Sh, -op: E.Op, so: PS.StepOK(sh, op)) -> E.Obs:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-sh: ST.Sh, -op: E.Op, so: PS.StepOK(sh, op)) -> {F.step(ST.real(sh), op) == (ST.real(so_sh(sh, op, so)), so_obs(sh, op, so)) : F.Fenwick & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-sh: ST.Sh, -op: E.Op, so: PS.StepOK(sh, op)) -> {ST.good(so_sh(sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-sh: ST.Sh, -op: E.Op, so: PS.StepOK(sh, op)) -> {(ST.model(so_sh(sh, op, so)), so_obs(sh, op, so)) == S.step(ST.model(sh), op) : List<&2, U32> & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      s

def spec_run_cons(+op: E.Op, +rest: List<&2, E.Op>, +m: List<&2, U32>, +m1: List<&2, U32>, +o: E.Obs, +e: {(m1, o) == S.step(m, op) : List<&2, U32> & E.Obs}) -> {S.run(Con{op, rest}, m) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, U32> & List<&2, E.Obs>}:
  %e : {S.cons_obs(Pair.snd(List<&2, U32>, E.Obs, _), S.run(rest, Pair.fst(List<&2, U32>, E.Obs, _))) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, U32> & List<&2, E.Obs>}
  %Equal.sym(List<&2, U32> & List<&2, E.Obs>, S.run(rest, m1), (srun_state(rest, m1), srun_obs(rest, m1)), L.pair_eta(List<&2, U32>, List<&2, E.Obs>, S.run(rest, m1))) : {S.cons_obs(o, _) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, U32> & List<&2, E.Obs>}
  {==}

def RunOK(ops: List<&2, E.Op>, sh: ST.Sh, acc: List<&2, E.Obs>) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {F.run_acc(ops, (ST.real(sh), acc)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : F.Fenwick & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh)) : List<&2, U32>})>

def ro_sh(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> ST.Sh:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {F.run_acc(ops, (ST.real(sh), acc)) == (ST.real(ro_sh(ops, sh, acc, r)), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : F.Fenwick & List<&2, E.Obs>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.good(ro_sh(ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.model(ro_sh(ops, sh, acc, r)) == srun_state(ops, ST.model(sh)) : List<&2, U32>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(+ops: List<&2, E.Op>, +sh: ST.Sh, +acc: List<&2, E.Obs>, +g: {ST.good(sh) == True{} : Bool}) -> RunOK(ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(sh)
      +sh1 = so_sh(sh, op, PS.step_ok(sh, op, g))
      +o = so_obs(sh, op, PS.step_ok(sh, op, g))
      +g1 = so_good(sh, op, PS.step_ok(sh, op, g))
      +m1 = ST.model(sh1)
      +acc1 = {Con{o, acc} : List<&2, E.Obs>}
      +sh2 = ro_sh(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1))
      +es = spec_run_cons(op, rest, m, m1, o, so_spec(sh, op, PS.step_ok(sh, op, g)))
      -R = S.run(rest, m1)
      (sh2, (
        %Equal.sym(F.Fenwick & E.Obs, F.step(ST.real(sh), op), (ST.real(sh1), o), so_step(sh, op, PS.step_ok(sh, op, g))) : {F.run_acc(rest, F.record(acc, _)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : F.Fenwick & List<&2, E.Obs>}
        %Equal.sym(F.Fenwick & List<&2, E.Obs>, F.run_acc(rest, (ST.real(sh1), acc1)), (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)), ro_run(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1))) : {_ == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : F.Fenwick & List<&2, E.Obs>}
        %Equal.sym(List<&2, U32> & List<&2, E.Obs>, S.run(Con{op, rest}, m), (Pair.fst(List<&2, U32>, List<&2, E.Obs>, R), Con{o, Pair.snd(List<&2, U32>, List<&2, E.Obs>, R)}), es) : {(ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, Pair.snd(List<&2, U32>, List<&2, E.Obs>, _), acc)) : F.Fenwick & List<&2, E.Obs>}
        {==},
        (ro_good(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1)),
         %Equal.sym(List<&2, U32> & List<&2, E.Obs>, S.run(Con{op, rest}, m), (Pair.fst(List<&2, U32>, List<&2, E.Obs>, R), Con{o, Pair.snd(List<&2, U32>, List<&2, E.Obs>, R)}), es) : {ST.model(sh2) == Pair.fst(List<&2, U32>, List<&2, E.Obs>, _) : List<&2, U32>}
         ro_model(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1)))))

# The finished run: B.run reverses the accumulator, which is the spec's own
# observation list.
def run_from(+ops: List<&2, E.Op>, +sh0: ST.Sh, +g0: {ST.good(sh0) == True{} : Bool}) -> {F.run(ops, ST.real(sh0)) == (ST.real(ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))), srun_obs(ops, ST.model(sh0))) : F.Fenwick & List<&2, E.Obs>}:
  +sh2 = ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))
  +os = srun_obs(ops, ST.model(sh0))
  %Equal.sym(F.Fenwick & List<&2, E.Obs>, F.run_acc(ops, (ST.real(sh0), Nil{})), (ST.real(sh2), List.reverse.go(&2, E.Obs, os, Nil{})), ro_run(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))) : {F.finish(_) == (ST.real(sh2), os) : F.Fenwick & List<&2, E.Obs>}
  %Equal.sym(List<&2, E.Obs>, List.reverse(&2, E.Obs, List.reverse.go(&2, E.Obs, os, Nil{})), os, LL.rev_rev(E.Obs, os)) : {(ST.real(sh2), _) == (ST.real(sh2), os) : F.Fenwick & List<&2, E.Obs>}
  {==}

def TraceOK(ops: List<&2, E.Op>, sh0: ST.Sh) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {F.run(ops, ST.real(sh0)) == (ST.real(sh2), srun_obs(ops, ST.model(sh0))) : F.Fenwick & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh0)) : List<&2, U32>})>

def trace_from(+ops: List<&2, E.Op>, +sh0: ST.Sh, +g0: {ST.good(sh0) == True{} : Bool}) -> TraceOK(ops, sh0):
  (ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)),
   (run_from(ops, sh0, g0),
    (ro_good(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)),
     ro_model(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)))))
