import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../../spec/containers/dynamic_array.bend as S
import ../../../src/containers/dynamic_array.bend as DA
import ../../../src/containers/types/dynamic_array.bend as E
import ./state.bend as ST
import ./steps.bend as SP
import ./trace.bend as TR
import ./closed.bend as CL
import ./owned_instances.bend as OWN
import ./owned_swap.bend as OS
import ../../../spec/lib/common.bend as SC
import ../../../spec/lib/sequence.bend as V
import ../../lib/sequence.bend as VL

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

# ==== the contract of dynamic_array (stated in spec/containers/dynamic_array.bend) ====================

# ---- the implementation ----
# every Post below is a property of S.step; it holds of DA.step read back
# through the abstraction (view1), on every good array
def impl(-T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}, -Post: (S.Model<T> & E.Obs<T>) -> Type, pf: Post(S.step(T, ST.abs(T, ST.real(T, sh)), op))) -> Post(view1(T, DA.step(T, ST.real(T, sh), op))):
  L.subst(S.Model<T> & E.Obs<T>, Post, S.step(T, ST.abs(T, ST.real(T, sh)), op), view1(T, DA.step(T, ST.real(T, sh), op)), Equal.sym(S.Model<T> & E.Obs<T>, view1(T, DA.step(T, ST.real(T, sh), op)), S.step(T, ST.abs(T, ST.real(T, sh)), op), step_refines(T, sh, op, g)), pf)

# ---- Length, Capacity, iteration: the value, and nothing changes ----
def length_result(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Length.length_result(T, l, d, xs):
  {==}

def length_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Length.length_frame(T, l, d, xs):
  {==}

def capacity_result(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Capacity.capacity_result(T, l, d, xs):
  {==}

def capacity_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Capacity.capacity_frame(T, l, d, xs):
  {==}

def to_list_model(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Iteration.to_list_model(T, l, d, xs):
  {==}

def to_list_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Iteration.to_list_frame(T, l, d, xs):
  {==}

# ---- Empty_Vector: Length 0 (the default capacity is 2^0) ----
def new_empty(-T: Data) -> S.Empty_Vector.new_empty(T):
  {==}

def new_capacity(-T: Data) -> S.Empty_Vector.new_capacity(T):
  {==}

def new_impl(-T: Data) -> {ST.abs(T, DA.new(T)) == S.new(T) : S.Model<T>}:
  new_abs(T)

def with_limit_empty(-T: Data, +k: Nat) -> S.Empty_Vector.with_limit_empty(T, k):
  {==}

def with_limit_impl(-T: Data, +k: Nat) -> {ST.abs(T, DA.with_limit(T, k)) == S.with_limit(T, k) : S.Model<T>}:
  with_limit_abs(T, k)

# ---- Reserve_Capacity: M.Equal (Model, Model'Old) ----
def re_c(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +n: Nat, +c1: Bool, +h1: {Nat.is_le(n, SC.pow2(d)) == c1 : Bool}, +c2: Bool, +h2: {Nat.is_le(n, SC.pow2(l)) == c2 : Bool}) -> {S.items(T, S.nx(T, S.M{l, d, xs}, E.Reserve{n})) == xs : List<&2, T>}:
  match c1 c2:
    case True{} _:
      %Equal.sym(Bool, Nat.is_le(n, SC.pow2(d)), True{}, h1) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(n, SC.pow2(l)), (S.M{l, S.fit(n, d, n), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == xs : List<&2, T>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_le(n, SC.pow2(d)), False{}, h1) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(n, SC.pow2(l)), (S.M{l, S.fit(n, d, n), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == xs : List<&2, T>}
      %Equal.sym(Bool, Nat.is_le(n, SC.pow2(l)), True{}, h2) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, False{}, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, S.fit(n, d, n), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == xs : List<&2, T>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_le(n, SC.pow2(d)), False{}, h1) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(n, SC.pow2(l)), (S.M{l, S.fit(n, d, n), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == xs : List<&2, T>}
      %Equal.sym(Bool, Nat.is_le(n, SC.pow2(l)), False{}, h2) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, False{}, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, S.fit(n, d, n), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == xs : List<&2, T>}
      {==}

def reserve_equal(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +n: Nat) -> S.Reserve_Capacity.reserve_equal(T, l, d, xs, n):
  re_c(T, l, d, xs, n, Nat.is_le(n, SC.pow2(d)), {==}, Nat.is_le(n, SC.pow2(l)), {==})

# ---- Clear: Length 0 (the capacity is kept) ----
def clear_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Clear.clear_length(T, l, d, xs):
  {==}

def clear_capacity(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Clear.clear_capacity(T, l, d, xs):
  {==}

# ---- Element / First_Element / Last_Element ----
def get_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {SC.nth(T, xs, i) == Some{v} : Maybe<&2, T>}) -> S.Element.get_element(T, l, d, xs, i, v, h):
  %Equal.sym(Maybe<&2, T>, SC.nth(T, xs, i), Some{v}, h) : {E.OItem{S.item_result(T, _)} == E.OItem{Done{v}} : E.Obs<T>}
  {==}

def get_frame(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat) -> S.Element.get_frame(T, l, d, xs, i):
  {==}

def get_outside(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +h: {Nat.is_le(SC.length(T, xs), i) == True{} : Bool}) -> S.Element.get_outside(T, l, d, xs, i, h):
  %Equal.sym(Maybe<&2, T>, SC.nth(T, xs, i), None{}, LL.nth_none(T, xs, i, h)) : {E.OItem{S.item_result(T, _)} == E.OItem{Fail{E.IndexOutOfRange{}}} : E.Obs<T>}
  {==}

def first_element(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> S.First_Element.first_element(T, l, d, h, t):
  {==}

def last_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>) -> S.Last_Element.last_element(T, l, d, xs):
  {==}

# ---- Replace_Element: Length kept, Element (Index) = New_Item, Equal_Except elsewhere ----
def set_step(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {S.step(T, S.M{l, d, xs}, E.Set{i, v}) == (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model<T> & E.Obs<T>}:
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(T, xs)), True{}, h) : {Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) == (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{Done{Unit{}}}) : S.Model<T> & E.Obs<T>}
  {==}

def set_items(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {S.items(T, S.nx(T, S.M{l, d, xs}, E.Set{i, v})) == SC.update(T, xs, i, v) : List<&2, T>}:
  %Equal.sym(S.Model<T> & E.Obs<T>, S.step(T, S.M{l, d, xs}, E.Set{i, v}), (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{Done{Unit{}}}), set_step(T, l, d, xs, i, v, h)) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, _)) == SC.update(T, xs, i, v) : List<&2, T>}
  {==}

def set_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> S.Replace_Element.set_length(T, l, d, xs, i, v, h):
  %Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Set{i, v})), SC.update(T, xs, i, v), set_items(T, l, d, xs, i, v, h)) : {SC.length(T, _) == SC.length(T, xs) : Nat}
  VL.update_length(T, xs, i, v)

def set_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> S.Replace_Element.set_element(T, l, d, xs, i, v, h):
  %Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Set{i, v})), SC.update(T, xs, i, v), set_items(T, l, d, xs, i, v, h)) : {SC.nth(T, _, i) == Some{v} : Maybe<&2, T>}
  VL.update_at(T, xs, i, v, h)

def set_except(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> S.Replace_Element.set_except(T, l, d, xs, i, v, h):
  L.subst(List<&2, T>, z => V.EqualExcept(T, xs, z, i), SC.update(T, xs, i, v), S.items(T, S.nx(T, S.M{l, d, xs}, E.Set{i, v})), Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Set{i, v})), SC.update(T, xs, i, v), set_items(T, l, d, xs, i, v, h)), VL.update_except(T, xs, i, v))

def set_outside(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == False{} : Bool}) -> S.Replace_Element.set_outside(T, l, d, xs, i, v, h):
  %Equal.sym(Bool, Nat.is_lt(i, SC.length(T, xs)), False{}, h) : {Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) == (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) : S.Model<T> & E.Obs<T>}
  {==}

def pi_c(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +c1: Bool, +h1: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == c1 : Bool}, +c2: Bool, +h2: {Nat.is_lt(d, l) == c2 : Bool}, +hr: {Bool.or(c1, c2) == True{} : Bool}) -> {S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})) == SC.snoc(T, xs, v) : List<&2, T>}:
  match c1 c2:
    case True{} _:
      %Equal.sym(Bool, Nat.is_lt(SC.length(T, xs), SC.pow2(d)), True{}, h1) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == SC.snoc(T, xs, v) : List<&2, T>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_lt(SC.length(T, xs), SC.pow2(d)), False{}, h1) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == SC.snoc(T, xs, v) : List<&2, T>}
      %Equal.sym(Bool, Nat.is_lt(d, l), True{}, h2) : {S.items(T, Pair.fst(S.Model<T>, E.Obs<T>, Bool.pick(S.Model<T> & E.Obs<T>, False{}, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))))) == SC.snoc(T, xs, v) : List<&2, T>}
      {==}
    case False{} False{}:
      Empty.absurd({S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})) == SC.snoc(T, xs, v) : List<&2, T>}, L.false_true(hr))

def push_items(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {S.room(T, l, d, xs) == True{} : Bool}) -> {S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})) == SC.snoc(T, xs, v) : List<&2, T>}:
  pi_c(T, l, d, xs, v, Nat.is_lt(SC.length(T, xs), SC.pow2(d)), {==}, Nat.is_lt(d, l), {==}, hr)

def push_length(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {S.room(T, l, d, xs) == True{} : Bool}) -> S.Append.push_length(T, l, d, xs, v, hr):
  %Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})), SC.snoc(T, xs, v), push_items(T, l, d, xs, v, hr)) : {SC.length(T, _) == 1n+SC.length(T, xs) : Nat}
  VL.snoc_length(T, xs, v)

def push_prefix(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {S.room(T, l, d, xs) == True{} : Bool}) -> S.Append.push_prefix(T, l, d, xs, v, hr):
  L.subst(List<&2, T>, z => V.EqualPrefix(T, xs, z), SC.snoc(T, xs, v), S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})), Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})), SC.snoc(T, xs, v), push_items(T, l, d, xs, v, hr)), VL.snoc_prefix(T, xs, v))

def push_element(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +hr: {S.room(T, l, d, xs) == True{} : Bool}) -> S.Append.push_element(T, l, d, xs, v, hr):
  %Equal.sym(List<&2, T>, S.items(T, S.nx(T, S.M{l, d, xs}, E.Push{v})), SC.snoc(T, xs, v), push_items(T, l, d, xs, v, hr)) : {SC.nth(T, _, SC.length(T, xs)) == Some{v} : Maybe<&2, T>}
  VL.snoc_last(T, xs, v)

def push_full(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +v: T, +h1: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == False{} : Bool}, +h2: {Nat.is_lt(d, l) == False{} : Bool}) -> S.Append.push_full(T, l, d, xs, v, h1, h2):
  %Equal.sym(Bool, Nat.is_lt(SC.length(T, xs), SC.pow2(d)), False{}, h1) : {Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) == (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) : S.Model<T> & E.Obs<T>}
  %Equal.sym(Bool, Nat.is_lt(d, l), False{}, h2) : {Bool.pick(S.Model<T> & E.Obs<T>, False{}, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) == (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) : S.Model<T> & E.Obs<T>}
  {==}

# ---- Delete_Last: Length - 1, Equal_Prefix (Model, Model'Old); pop returns Last_Element'Old ----
def pop_length(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_length(T, l, d, h, t):
  VL.init_length(T, t, h)

def pop_prefix(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_prefix(T, l, d, h, t):
  VL.init_prefix(T, t, h)

def pop_result(-T: Data, +l: Nat, +d: Nat, +h: T, +t: List<&2, T>) -> S.Delete_Last.pop_result(T, l, d, h, t):
  %Equal.sym(Maybe<&2, T>, SC.last(T, Con{h, t}), V.last_elem(T, Con{h, t}), VL.last_is_elem(T, t, h)) : {E.OItem{S.item_result(T, _)} == E.OItem{S.item_result(T, V.last_elem(T, Con{h, t}))} : E.Obs<T>}
  {==}

def pop_empty(-T: Data, +l: Nat, +d: Nat) -> S.Delete_Last.pop_empty(T, l, d):
  {==}
