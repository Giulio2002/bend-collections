import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ./spec.bend as S
import ../../../src/containers/dynamic_array.bend as DA
import ../../../src/containers/types/dynamic_array.bend as E
import ./state.bend as ST
import ./steps.bend as SP
import ./trace.bend as TR
import ./closed.bend as CL
import ./owned_instances.bend as OWN
import ./owned_swap.bend as OS

# Dynamic array: public proof entry point.
#   abstraction  ST.abs   (Base.Array slots -> item sequence, via AR.freeze)
#   invariant    ST.Inv   (the array realizes a shadow satisfying ST.good)
#   operations   SP.step_ok (every operation, errors included)
#   traces       trace_new / trace_with_limit (arbitrary finite op lists)
# The element type T is an arbitrary Data type (parametric; no template).

def view(-T: Data, r: DA.DynArray<&2, T> & List<&2, E.Obs<T>>) -> S.Model<T> & List<&2, E.Obs<T>>:
  match r:
    case Tuple{da, os}:
      (ST.abs(T, da), os)

def view1(-T: Data, r: DA.DynArray<&2, T> & E.Obs<T>) -> S.Model<T> & E.Obs<T>:
  match r:
    case Tuple{da, o}:
      (ST.abs(T, da), o)

# ---- initialization ----

def new_inv(-T: Data) -> ST.Inv(T, DA.new(T)):
  (TR.initial(T), ({==}, TR.new_good(T)))

def new_abs(-T: Data) -> {ST.abs(T, DA.new(T)) == S.new(T) : S.Model<T>}:
  {==}

def limit_good(-T: Data, +k: Nat) -> {ST.good(T, TR.limited(T, k)) == True{} : Bool}:
  ST.good_intro(T, DA.clamp_limit(k, Nat.is_lt(k, 31n)), 0n, 0n, AR.TLeaf{None{}}, Pair.fst({Nat.is_le(DA.clamp_limit(k, Nat.is_lt(k, 31n)), 31n) == True{} : Bool}, {DA.clamp_limit(k, Nat.is_lt(k, 31n)) == Nat.min(k, 31n) : Nat}, TR.clamp_case(k, Nat.is_lt(k, 31n), {==})), N.zero_le(DA.clamp_limit(k, Nat.is_lt(k, 31n))), {==}, {==})

def with_limit_inv(-T: Data, +k: Nat) -> ST.Inv(T, DA.with_limit(T, k)):
  (TR.limited(T, k), ({==}, limit_good(T, k)))

def with_limit_abs(-T: Data, +k: Nat) -> {ST.abs(T, DA.with_limit(T, k)) == S.with_limit(T, k) : S.Model<T>}:
  %Equal.sym(Nat, DA.clamp_limit(k, Nat.is_lt(k, 31n)), Nat.min(k, 31n), Pair.snd({Nat.is_le(DA.clamp_limit(k, Nat.is_lt(k, 31n)), 31n) == True{} : Bool}, {DA.clamp_limit(k, Nat.is_lt(k, 31n)) == Nat.min(k, 31n) : Nat}, TR.clamp_case(k, Nat.is_lt(k, 31n), {==}))) : {S.M{_, 0n, Nil{}} == S.M{Nat.min(k, 31n), 0n, Nil{}} : S.Model<T>}
  {==}

# ---- every operation (errors included), on every reachable representation ----

def step_refines(-T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> {view1(T, DA.step(T, ST.real(T, sh), op)) == S.step(T, ST.abs(T, ST.real(T, sh)), op) : S.Model<T> & E.Obs<T>}:
  +sh2 = TR.so_sh(T, sh, op, SP.step_ok(T, sh, op, g))
  +o = TR.so_obs(T, sh, op, SP.step_ok(T, sh, op, g))
  %Equal.sym(DA.DynArray<&2, T> & E.Obs<T>, DA.step(T, ST.real(T, sh), op), (ST.real(T, sh2), o), TR.so_step(T, sh, op, SP.step_ok(T, sh, op, g))) : {view1(T, _) == S.step(T, ST.abs(T, ST.real(T, sh)), op) : S.Model<T> & E.Obs<T>}
  %Equal.sym(S.Model<T>, ST.abs(T, ST.real(T, sh2)), ST.model(T, sh2), ST.abs_real(T, sh2)) : {(_, o) == S.step(T, ST.abs(T, ST.real(T, sh)), op) : S.Model<T> & E.Obs<T>}
  %Equal.sym(S.Model<T>, ST.abs(T, ST.real(T, sh)), ST.model(T, sh), ST.abs_real(T, sh)) : {(ST.model(T, sh2), o) == S.step(T, _, op) : S.Model<T> & E.Obs<T>}
  TR.so_spec(T, sh, op, SP.step_ok(T, sh, op, g))

def step_preserves(-T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, E.Obs<T>, DA.step(T, ST.real(T, sh), op))):
  +sh2 = TR.so_sh(T, sh, op, SP.step_ok(T, sh, op, g))
  (sh2, (Equal.cong(DA.DynArray<&2, T> & E.Obs<T>, DA.DynArray<&2, T>, r => Pair.fst(DA.DynArray<&2, T>, E.Obs<T>, r), DA.step(T, ST.real(T, sh), op), (ST.real(T, sh2), TR.so_obs(T, sh, op, SP.step_ok(T, sh, op, g))), TR.so_step(T, sh, op, SP.step_ok(T, sh, op, g))), TR.so_good(T, sh, op, SP.step_ok(T, sh, op, g))))

# ---- arbitrary finite traces from a constructor ----

def run_from(-T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}) -> {DA.run(T, ops, ST.real(T, sh0)) == (ST.real(T, TR.ro_sh(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))), TR.srun_obs(T, ops, ST.model(T, sh0))) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}:
  +sh2 = TR.ro_sh(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))
  +os = TR.srun_obs(T, ops, ST.model(T, sh0))
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run_acc(T, ops, (ST.real(T, sh0), Nil{})), (ST.real(T, sh2), List.reverse.go(&2, E.Obs<T>, os, Nil{})), TR.ro_run(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))) : {DA.finish(T, _) == (ST.real(T, sh2), os) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}
  %Equal.sym(List<&2, E.Obs<T>>, List.reverse(&2, E.Obs<T>, List.reverse.go(&2, E.Obs<T>, os, Nil{})), os, LL.rev_rev(E.Obs<T>, os)) : {(ST.real(T, sh2), _) == (ST.real(T, sh2), os) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}
  {==}

def trace_from(-T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}) -> {view(T, DA.run(T, ops, ST.real(T, sh0))) == S.run(T, ops, ST.model(T, sh0)) : S.Model<T> & List<&2, E.Obs<T>>}:
  +sh2 = TR.ro_sh(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))
  +os = TR.srun_obs(T, ops, ST.model(T, sh0))
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run(T, ops, ST.real(T, sh0)), (ST.real(T, sh2), os), run_from(T, ops, sh0, g0)) : {view(T, _) == S.run(T, ops, ST.model(T, sh0)) : S.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(S.Model<T>, ST.abs(T, ST.real(T, sh2)), ST.model(T, sh2), ST.abs_real(T, sh2)) : {(_, os) == S.run(T, ops, ST.model(T, sh0)) : S.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(S.Model<T>, ST.model(T, sh2), TR.srun_state(T, ops, ST.model(T, sh0)), TR.ro_model(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))) : {(_, os) == S.run(T, ops, ST.model(T, sh0)) : S.Model<T> & List<&2, E.Obs<T>>}
  Equal.sym(S.Model<T> & List<&2, E.Obs<T>>, S.run(T, ops, ST.model(T, sh0)), (TR.srun_state(T, ops, ST.model(T, sh0)), os), L.pair_eta(S.Model<T>, List<&2, E.Obs<T>>, S.run(T, ops, ST.model(T, sh0))))

def inv_from(-T: Data, +ops: List<&2, E.Op<T>>, +sh0: ST.Shadow<T>, +g0: {ST.good(T, sh0) == True{} : Bool}) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run(T, ops, ST.real(T, sh0)))):
  +sh2 = TR.ro_sh(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))
  (sh2, (Equal.cong(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.DynArray<&2, T>, r => Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, r), DA.run(T, ops, ST.real(T, sh0)), (ST.real(T, sh2), TR.srun_obs(T, ops, ST.model(T, sh0))), run_from(T, ops, sh0, g0)), TR.ro_good(T, ops, sh0, Nil{}, TR.run_ok(T, ops, sh0, Nil{}, g0))))

# Public trace laws: every finite op list run from DA.new / DA.with_limit
# through the actual DA.run equals the specification run, and the final
# array satisfies the invariant.
def trace_new(-T: Data, +ops: List<&2, E.Op<T>>) -> {view(T, DA.run(T, ops, DA.new(T))) == S.run(T, ops, S.new(T)) : S.Model<T> & List<&2, E.Obs<T>>}:
  trace_from(T, ops, TR.initial(T), TR.new_good(T))

def trace_new_inv(-T: Data, +ops: List<&2, E.Op<T>>) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run(T, ops, DA.new(T)))):
  inv_from(T, ops, TR.initial(T), TR.new_good(T))

def trace_with_limit(-T: Data, +k: Nat, +ops: List<&2, E.Op<T>>) -> {view(T, DA.run(T, ops, DA.with_limit(T, k))) == S.run(T, ops, S.with_limit(T, k)) : S.Model<T> & List<&2, E.Obs<T>>}:
  %with_limit_abs(T, k) : {view(T, DA.run(T, ops, DA.with_limit(T, k))) == S.run(T, ops, _) : S.Model<T> & List<&2, E.Obs<T>>}
  trace_from(T, ops, TR.limited(T, k), limit_good(T, k))

def trace_with_limit_inv(-T: Data, +k: Nat, +ops: List<&2, E.Op<T>>) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run(T, ops, DA.with_limit(T, k)))):
  inv_from(T, ops, TR.limited(T, k), limit_good(T, k))

# ---- the executable specializations (closed element type) ----
#
# DA.*_at is what tests and benchmarks run (see src/dynamic_array.bend for
# why a closed element type is required by the native backend). CL.*_eq
# proves each specialization equal to the parametric definition, so every
# law above holds verbatim of the executed code.

def new_at_abs(~T: Data) -> {ST.abs(T, DA.new_at(~T)) == S.new(T) : S.Model<T>}:
  %Equal.sym(DA.DynArray<&2, T>, DA.new_at(~T), DA.new(T), CL.new_eq(~T)) : {ST.abs(T, _) == S.new(T) : S.Model<T>}
  new_abs(T)

def new_at_inv(~T: Data) -> ST.Inv(T, DA.new_at(~T)):
  %Equal.sym(DA.DynArray<&2, T>, DA.new_at(~T), DA.new(T), CL.new_eq(~T)) : ST.Inv(T, _)
  new_inv(T)

def with_limit_at_abs(~T: Data, +k: Nat) -> {ST.abs(T, DA.with_limit_at(~T, k)) == S.with_limit(T, k) : S.Model<T>}:
  %Equal.sym(DA.DynArray<&2, T>, DA.with_limit_at(~T, k), DA.with_limit(T, k), CL.with_limit_eq(~T, k)) : {ST.abs(T, _) == S.with_limit(T, k) : S.Model<T>}
  with_limit_abs(T, k)

def step_at_refines(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> {view1(T, DA.step_at(~T, ST.real(T, sh), op)) == S.step(T, ST.abs(T, ST.real(T, sh)), op) : S.Model<T> & E.Obs<T>}:
  %Equal.sym(DA.DynArray<&2, T> & E.Obs<T>, DA.step_at(~T, ST.real(T, sh), op), DA.step(T, ST.real(T, sh), op), CL.step_eq(~T, sh, op, g)) : {view1(T, _) == S.step(T, ST.abs(T, ST.real(T, sh)), op) : S.Model<T> & E.Obs<T>}
  step_refines(T, sh, op, g)

def step_at_preserves(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, E.Obs<T>, DA.step_at(~T, ST.real(T, sh), op))):
  %Equal.sym(DA.DynArray<&2, T> & E.Obs<T>, DA.step_at(~T, ST.real(T, sh), op), DA.step(T, ST.real(T, sh), op), CL.step_eq(~T, sh, op, g)) : ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, E.Obs<T>, _))
  step_preserves(T, sh, op, g)

def trace_new_at(~T: Data, +ops: List<&2, E.Op<T>>) -> {view(T, DA.run_at(~T, ops, DA.new_at(~T))) == S.run(T, ops, S.new(T)) : S.Model<T> & List<&2, E.Obs<T>>}:
  %Equal.sym(DA.DynArray<&2, T>, DA.new_at(~T), DA.new(T), CL.new_eq(~T)) : {view(T, DA.run_at(~T, ops, _)) == S.run(T, ops, S.new(T)) : S.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run_at(~T, ops, ST.real(T, TR.initial(T))), DA.run(T, ops, ST.real(T, TR.initial(T))), CL.run_eq(~T, ops, TR.initial(T), TR.new_good(T))) : {view(T, _) == S.run(T, ops, S.new(T)) : S.Model<T> & List<&2, E.Obs<T>>}
  trace_new(T, ops)

def trace_new_at_inv(~T: Data, +ops: List<&2, E.Op<T>>) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run_at(~T, ops, DA.new_at(~T)))):
  %Equal.sym(DA.DynArray<&2, T>, DA.new_at(~T), DA.new(T), CL.new_eq(~T)) : ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run_at(~T, ops, _)))
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run_at(~T, ops, ST.real(T, TR.initial(T))), DA.run(T, ops, ST.real(T, TR.initial(T))), CL.run_eq(~T, ops, TR.initial(T), TR.new_good(T))) : ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, _))
  trace_new_inv(T, ops)

def trace_with_limit_at(~T: Data, +k: Nat, +ops: List<&2, E.Op<T>>) -> {view(T, DA.run_at(~T, ops, DA.with_limit_at(~T, k))) == S.run(T, ops, S.with_limit(T, k)) : S.Model<T> & List<&2, E.Obs<T>>}:
  %Equal.sym(DA.DynArray<&2, T>, DA.with_limit_at(~T, k), DA.with_limit(T, k), CL.with_limit_eq(~T, k)) : {view(T, DA.run_at(~T, ops, _)) == S.run(T, ops, S.with_limit(T, k)) : S.Model<T> & List<&2, E.Obs<T>>}
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run_at(~T, ops, ST.real(T, TR.limited(T, k))), DA.run(T, ops, ST.real(T, TR.limited(T, k))), CL.run_eq(~T, ops, TR.limited(T, k), limit_good(T, k))) : {view(T, _) == S.run(T, ops, S.with_limit(T, k)) : S.Model<T> & List<&2, E.Obs<T>>}
  trace_with_limit(T, k, ops)

def trace_with_limit_at_inv(~T: Data, +k: Nat, +ops: List<&2, E.Op<T>>) -> ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run_at(~T, ops, DA.with_limit_at(~T, k)))):
  %Equal.sym(DA.DynArray<&2, T>, DA.with_limit_at(~T, k), DA.with_limit(T, k), CL.with_limit_eq(~T, k)) : ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, DA.run_at(~T, ops, _)))
  %Equal.sym(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.run_at(~T, ops, ST.real(T, TR.limited(T, k))), DA.run(T, ops, ST.real(T, TR.limited(T, k))), CL.run_eq(~T, ops, TR.limited(T, k), limit_good(T, k))) : ST.Inv(T, Pair.fst(DA.DynArray<&2, T>, List<&2, E.Obs<T>>, _))
  trace_with_limit_inv(T, k, ops)
