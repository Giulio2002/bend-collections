import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../spec/common.bend as SC
import ../../src/containers/bitset.bend as B
import ../spec/bitset.bend as S
import ../../src/containers/types/bitset.bend as E
import ./state.bend as ST
import ./steps.bend as BS

# Arbitrary finite operation traces: the real runner refines the spec runner.
#
# Base.Array is linear, so the statement is the same shadow form the per-step
# laws use: running any finite list of operations on the array of a good
# shadow lands on the array of another good shadow, emits exactly the spec
# runner's observations, and the model of the final shadow is the spec
# runner's final model.

def srun_obs(ops: List<&2, E.Op>, m: List<&2, Bool>) -> List<&2, E.Obs>:
  Pair.snd(List<&2, Bool>, List<&2, E.Obs>, S.run(ops, m))

def srun_state(ops: List<&2, E.Op>, m: List<&2, Bool>) -> List<&2, Bool>:
  Pair.fst(List<&2, Bool>, List<&2, E.Obs>, S.run(ops, m))

def so_sh(-sh: ST.Sh, -op: E.Op, so: BS.StepOK(sh, op)) -> ST.Sh:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-sh: ST.Sh, -op: E.Op, so: BS.StepOK(sh, op)) -> E.Obs:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-sh: ST.Sh, -op: E.Op, so: BS.StepOK(sh, op)) -> {B.step(ST.real(sh), op) == (ST.real(so_sh(sh, op, so)), so_obs(sh, op, so)) : B.Bitset & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-sh: ST.Sh, -op: E.Op, so: BS.StepOK(sh, op)) -> {ST.good(so_sh(sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-sh: ST.Sh, -op: E.Op, so: BS.StepOK(sh, op)) -> {(ST.model(so_sh(sh, op, so)), so_obs(sh, op, so)) == S.step(ST.model(sh), op) : List<&2, Bool> & E.Obs}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      s

def spec_run_cons(+op: E.Op, +rest: List<&2, E.Op>, +m: List<&2, Bool>, +m1: List<&2, Bool>, +o: E.Obs, +e: {(m1, o) == S.step(m, op) : List<&2, Bool> & E.Obs}) -> {S.run(Con{op, rest}, m) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, Bool> & List<&2, E.Obs>}:
  %e : {S.cons_obs(Pair.snd(List<&2, Bool>, E.Obs, _), S.run(rest, Pair.fst(List<&2, Bool>, E.Obs, _))) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, Bool> & List<&2, E.Obs>}
  %Equal.sym(List<&2, Bool> & List<&2, E.Obs>, S.run(rest, m1), (srun_state(rest, m1), srun_obs(rest, m1)), L.pair_eta(List<&2, Bool>, List<&2, E.Obs>, S.run(rest, m1))) : {S.cons_obs(o, _) == (srun_state(rest, m1), Con{o, srun_obs(rest, m1)}) : List<&2, Bool> & List<&2, E.Obs>}
  {==}

def RunOK(ops: List<&2, E.Op>, sh: ST.Sh, acc: List<&2, E.Obs>) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {B.run_acc(ops, (ST.real(sh), acc)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : B.Bitset & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh)) : List<&2, Bool>})>

def ro_sh(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> ST.Sh:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {B.run_acc(ops, (ST.real(sh), acc)) == (ST.real(ro_sh(ops, sh, acc, r)), List.reverse.go(&2, E.Obs, srun_obs(ops, ST.model(sh)), acc)) : B.Bitset & List<&2, E.Obs>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.good(ro_sh(ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(-ops: List<&2, E.Op>, -sh: ST.Sh, -acc: List<&2, E.Obs>, r: RunOK(ops, sh, acc)) -> {ST.model(ro_sh(ops, sh, acc, r)) == srun_state(ops, ST.model(sh)) : List<&2, Bool>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(+ops: List<&2, E.Op>, +sh: ST.Sh, +acc: List<&2, E.Obs>, +g: {ST.good(sh) == True{} : Bool}) -> RunOK(ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(sh)
      +sh1 = so_sh(sh, op, BS.step_ok(sh, op, g))
      +o = so_obs(sh, op, BS.step_ok(sh, op, g))
      +g1 = so_good(sh, op, BS.step_ok(sh, op, g))
      +m1 = ST.model(sh1)
      +acc1 = {Con{o, acc} : List<&2, E.Obs>}
      +sh2 = ro_sh(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1))
      +es = spec_run_cons(op, rest, m, m1, o, so_spec(sh, op, BS.step_ok(sh, op, g)))
      -R = S.run(rest, m1)
      (sh2, (
        %Equal.sym(B.Bitset & E.Obs, B.step(ST.real(sh), op), (ST.real(sh1), o), so_step(sh, op, BS.step_ok(sh, op, g))) : {B.run_acc(rest, B.record(acc, _)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : B.Bitset & List<&2, E.Obs>}
        %Equal.sym(B.Bitset & List<&2, E.Obs>, B.run_acc(rest, (ST.real(sh1), acc1)), (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)), ro_run(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1))) : {_ == (ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(Con{op, rest}, m), acc)) : B.Bitset & List<&2, E.Obs>}
        %Equal.sym(List<&2, Bool> & List<&2, E.Obs>, S.run(Con{op, rest}, m), (Pair.fst(List<&2, Bool>, List<&2, E.Obs>, R), Con{o, Pair.snd(List<&2, Bool>, List<&2, E.Obs>, R)}), es) : {(ST.real(sh2), List.reverse.go(&2, E.Obs, srun_obs(rest, m1), acc1)) == (ST.real(sh2), List.reverse.go(&2, E.Obs, Pair.snd(List<&2, Bool>, List<&2, E.Obs>, _), acc)) : B.Bitset & List<&2, E.Obs>}
        {==},
        (ro_good(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1)),
         %Equal.sym(List<&2, Bool> & List<&2, E.Obs>, S.run(Con{op, rest}, m), (Pair.fst(List<&2, Bool>, List<&2, E.Obs>, R), Con{o, Pair.snd(List<&2, Bool>, List<&2, E.Obs>, R)}), es) : {ST.model(sh2) == Pair.fst(List<&2, Bool>, List<&2, E.Obs>, _) : List<&2, Bool>}
         ro_model(rest, sh1, acc1, run_ok(rest, sh1, acc1, g1)))))

# The finished run: B.run reverses the accumulator, which is the spec's own
# observation list.
def run_from(+ops: List<&2, E.Op>, +sh0: ST.Sh, +g0: {ST.good(sh0) == True{} : Bool}) -> {B.run(ops, ST.real(sh0)) == (ST.real(ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))), srun_obs(ops, ST.model(sh0))) : B.Bitset & List<&2, E.Obs>}:
  +sh2 = ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))
  +os = srun_obs(ops, ST.model(sh0))
  %Equal.sym(B.Bitset & List<&2, E.Obs>, B.run_acc(ops, (ST.real(sh0), Nil{})), (ST.real(sh2), List.reverse.go(&2, E.Obs, os, Nil{})), ro_run(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0))) : {B.finish(_) == (ST.real(sh2), os) : B.Bitset & List<&2, E.Obs>}
  %Equal.sym(List<&2, E.Obs>, List.reverse(&2, E.Obs, List.reverse.go(&2, E.Obs, os, Nil{})), os, LL.rev_rev(E.Obs, os)) : {(ST.real(sh2), _) == (ST.real(sh2), os) : B.Bitset & List<&2, E.Obs>}
  {==}

def TraceOK(ops: List<&2, E.Op>, sh0: ST.Sh) -> Type:
  Sigma<&1, &1, ST.Sh, sh2 => {B.run(ops, ST.real(sh0)) == (ST.real(sh2), srun_obs(ops, ST.model(sh0))) : B.Bitset & List<&2, E.Obs>} & ({ST.good(sh2) == True{} : Bool} & {ST.model(sh2) == srun_state(ops, ST.model(sh0)) : List<&2, Bool>})>

def trace_from(+ops: List<&2, E.Op>, +sh0: ST.Sh, +g0: {ST.good(sh0) == True{} : Bool}) -> TraceOK(ops, sh0):
  (ro_sh(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)),
   (run_from(ops, sh0, g0),
    (ro_good(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)),
     ro_model(ops, sh0, Nil{}, run_ok(ops, sh0, Nil{}, g0)))))

# ---- from the constructor ----

def initial(+n: Nat) -> ST.Sh:
  {ST.Sh{n, B.depth_for(n), A.trep(B.Wd, B.depth_for(n), B.W{0})} : ST.Sh}

def new_real(+n: Nat) -> {B.new(n) == ST.real(initial(n)) : B.Bitset}:
  ST.new_form(n)

def new_good(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {ST.good(initial(n)) == True{} : Bool}:
  ST.new_rep(n, h)

def new_model(+n: Nat, +h: {Nat.is_le(n, Nat.mul(SC.pow2(B.depth_for(n)), 32n)) == True{} : Bool}) -> {ST.model(initial(n)) == S.new(n) : List<&2, Bool>}:
  ST.new_abs(n, h)
