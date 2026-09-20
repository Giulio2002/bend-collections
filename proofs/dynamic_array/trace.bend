import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/dynamic_array.bend as S
import ../../src/dynamic_array.bend as DA
import ../../types/dynamic_array.bend as E
import ./layout.bend as LY
import ./state.bend as ST
import ./steps.bend as SP

# Arbitrary finite operation traces through DA.run.

def so_sh(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: SP.StepOK(T, sh, op)) -> ST.Shadow<T>:
  match so:
    case Tuple{sh2, r}:
      sh2

def so_obs(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: SP.StepOK(T, sh, op)) -> E.Obs<T>:
  match so:
    case Tuple{sh2, Tuple{o, r}}:
      o

def so_step(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: SP.StepOK(T, sh, op)) -> {DA.step(T, ST.real(T, sh), op) == (ST.real(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) : DA.DynArray<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, r}}}:
      e

def so_good(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: SP.StepOK(T, sh, op)) -> {ST.good(T, so_sh(T, sh, op, so)) == True{} : Bool}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      g

def so_spec(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, so: SP.StepOK(T, sh, op)) -> {(ST.model(T, so_sh(T, sh, op, so)), so_obs(T, sh, op, so)) == S.step(T, ST.model(T, sh), op) : S.Model<T> & E.Obs<T>}:
  match so:
    case Tuple{sh2, Tuple{o, Tuple{e, Tuple{g, s}}}}:
      s

def spec_run_cons(-T: Data, +op: E.Op<T>, +rest: List<&2, E.Op<T>>, +m: S.Model<T>, +m1: S.Model<T>, +o: E.Obs<T>, +e: {(m1, o) == S.step(T, m, op) : S.Model<T> & E.Obs<T>}) -> {S.run(T, Con{op, rest}, m) == (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1)), Con{o, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))}) : S.Model<T> & List<&2, E.Obs<T>>}:
  %e : {S.cons_obs(T, Pair.snd(S.Model<T>, E.Obs<T>, _), S.run(T, rest, Pair.fst(S.Model<T>, E.Obs<T>, _))) == (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1)), Con{o, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))}) : S.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(S.Model<T> & List<&2, E.Obs<T>>, S.run(T, rest, m1), (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1)), Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))), L.pair_eta(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))) : {S.cons_obs(T, o, _) == (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1)), Con{o, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, rest, m1))}) : S.Model<T> & List<&2, E.Obs<T>>}
  {==}

def srun_obs(-T: Data, ops: List<&2, E.Op<T>>, m: S.Model<T>) -> List<&2, E.Obs<T>>:
  Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

def srun_state(-T: Data, ops: List<&2, E.Op<T>>, m: S.Model<T>) -> S.Model<T>:
  Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, ops, m))

# Running ops from the array of a good shadow, with any accumulator.
def RunOK(-T: Data, ops: List<&2, E.Op<T>>, sh: ST.Shadow<T>, acc: List<&2, E.Obs<T>>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => {DA.run_acc(T, ops, (ST.real(T, sh), acc)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : DA.DynArray<T> & List<&2, E.Obs<T>>} & ({ST.good(T, sh2) == True{} : Bool} & {ST.model(T, sh2) == srun_state(T, ops, ST.model(T, sh)) : S.Model<T>})>

def ro_sh(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> ST.Shadow<T>:
  match r:
    case Tuple{sh2, x}:
      sh2

def ro_run(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {DA.run_acc(T, ops, (ST.real(T, sh), acc)) == (ST.real(T, ro_sh(T, ops, sh, acc, r)), List.reverse.go(&2, E.Obs<T>, srun_obs(T, ops, ST.model(T, sh)), acc)) : DA.DynArray<T> & List<&2, E.Obs<T>>}:
  match r:
    case Tuple{sh2, Tuple{e, x}}:
      e

def ro_good(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {ST.good(T, ro_sh(T, ops, sh, acc, r)) == True{} : Bool}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      g

def ro_model(-T: Data, -ops: List<&2, E.Op<T>>, -sh: ST.Shadow<T>, -acc: List<&2, E.Obs<T>>, r: RunOK(T, ops, sh, acc)) -> {ST.model(T, ro_sh(T, ops, sh, acc, r)) == srun_state(T, ops, ST.model(T, sh)) : S.Model<T>}:
  match r:
    case Tuple{sh2, Tuple{e, Tuple{g, m}}}:
      m

def run_ok(-T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {ST.good(T, sh) == True{} : Bool}) -> RunOK(T, ops, sh, acc):
  match ops:
    case Nil{}:
      (sh, ({==}, (g, {==})))
    case Con{+op, +rest}:
      +m = ST.model(T, sh)
      +sh1 = so_sh(T, sh, op, SP.step_ok(T, sh, op, g))
      +o = so_obs(T, sh, op, SP.step_ok(T, sh, op, g))
      +g1 = so_good(T, sh, op, SP.step_ok(T, sh, op, g))
      +m1 = ST.model(T, sh1)
      +acc1 = {Con{o, acc} : List<&2, E.Obs<T>>}
      +sh2 = ro_sh(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1))
      +es = spec_run_cons(T, op, rest, m, m1, o, so_spec(T, sh, op, SP.step_ok(T, sh, op, g)))
      -R = S.run(T, rest, m1)
      (sh2, (
        %Equal.sym(DA.DynArray<T> & E.Obs<T>, DA.step(T, ST.real(T, sh), op), (ST.real(T, sh1), o), so_step(T, sh, op, SP.step_ok(T, sh, op, g))) : {DA.run_acc(T, rest, DA.record(T, acc, _)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : DA.DynArray<T> & List<&2, E.Obs<T>>}
        %Equal.sym(DA.DynArray<T> & List<&2, E.Obs<T>>, DA.run_acc(T, rest, (ST.real(T, sh1), acc1)), (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)), ro_run(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1))) : {_ == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, Con{op, rest}, m), acc)) : DA.DynArray<T> & List<&2, E.Obs<T>>}
        %Equal.sym(S.Model<T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, R)}), es) : {(ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, srun_obs(T, rest, m1), acc1)) == (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, _), acc)) : DA.DynArray<T> & List<&2, E.Obs<T>>}
        {==},
        (ro_good(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1)),
         %Equal.sym(S.Model<T> & List<&2, E.Obs<T>>, S.run(T, Con{op, rest}, m), (Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, R), Con{o, Pair.snd(S.Model<T>, List<&2, E.Obs<T>>, R)}), es) : {ST.model(T, sh2) == Pair.fst(S.Model<T>, List<&2, E.Obs<T>>, _) : S.Model<T>}
         ro_model(T, rest, sh1, acc1, run_ok(T, rest, sh1, acc1, g1)))))

# ---- from the constructors ----

def initial(-T: Data) -> ST.Shadow<T>:
  ST.Sh{31n, 0n, 0n, AR.TLeaf{None{}}}

def new_real(-T: Data) -> {DA.new(T) == ST.real(T, initial(T)) : DA.DynArray<T>}:
  {==}

def new_good(-T: Data) -> {ST.good(T, initial(T)) == True{} : Bool}:
  {==}

def new_model(-T: Data) -> {ST.model(T, initial(T)) == S.new(T) : S.Model<T>}:
  {==}

def limited(-T: Data, +k: Nat) -> ST.Shadow<T>:
  ST.Sh{DA.clamp_limit(k, Nat.is_lt(k, 31n)), 0n, 0n, AR.TLeaf{None{}}}

def clamp_case(+k: Nat, +b: Bool, +eb: {Nat.is_lt(k, 31n) == b : Bool}) -> {Nat.is_le(DA.clamp_limit(k, b), 31n) == True{} : Bool} & {DA.clamp_limit(k, b) == Nat.min(k, 31n) : Nat}:
  match b:
    case True{}:
      (N.lt_le(k, 31n, eb),
       %Equal.sym(Bool, Nat.is_lt(k, 31n), True{}, eb) : {k == Bool.pick(Nat, _, k, 31n) : Nat}
       {==})
    case False{}:
      ({==},
       %Equal.sym(Bool, Nat.is_lt(k, 31n), False{}, eb) : {31n == Bool.pick(Nat, _, k, 31n) : Nat}
       {==})
