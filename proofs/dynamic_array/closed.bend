import Base
import ../../src/pow2.bend as P2
import ../lib/pow2t.bend as PT
import ./clear.bend as CLR
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
import ./growth.bend as GR
import ./trace.bend as TR

# The executable specializations DA.*_at (template element type, so every
# Base.Array call is compiled at a closed type) compute exactly what the
# parametric definitions compute. Every universal law proved about DA.step
# and DA.run therefore holds of DA.step_at and DA.run_at at each instance.

# ---- the growth loop ----

def gstep_at_case(~T: Data, +k: Nat, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +b: Bool, +eb: {Nat.is_le(k, SC.pow2(d)) == b : Bool}) -> {DA.grow_step_at(~T, k, ST.real(T, ST.Sh{l, d, n, t})) == ST.real(T, GR.sgstep(T, k, ST.Sh{l, d, n, t})) : DA.DynArray<&2, T>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, eb) : {DA.grow_if_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), _) == ST.real(T, Bool.pick(ST.Shadow<T>, Nat.is_le(k, SC.pow2(d)), ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, eb) : {DA.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)} == ST.real(T, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {DA.grow_if_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), _) == ST.real(T, Bool.pick(ST.Shadow<T>, Nat.is_le(k, SC.pow2(d)), ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, eb) : {DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), n, DA.grown_at(~T, d, AR.thaw(Maybe<&2, T>, t))} == ST.real(T, Bool.pick(ST.Shadow<T>, _, ST.Sh{l, d, n, t}, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}})) : DA.DynArray<&2, T>}
      %Equal.sym(Array<Maybe<&2, T>>, DA.grown_at(~T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_eq(T, d, t)) : {DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), n, _} == ST.real(T, ST.Sh{l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}}) : DA.DynArray<&2, T>}
      {==}

def grow_until_at_real(~T: Data, +f: Nat, +k: Nat, +sh: ST.Shadow<T>) -> {DA.grow_until_at(~T, f, k, ST.real(T, sh)) == ST.real(T, GR.sgrow(T, f, k, sh)) : DA.DynArray<&2, T>}:
  match f sh:
    case 0n _:
      {==}
    case 1n+g ST.Sh{+l, +d, +n, +t}:
      %Equal.sym(DA.DynArray<&2, T>, DA.grow_step_at(~T, k, ST.real(T, ST.Sh{l, d, n, t})), ST.real(T, GR.sgstep(T, k, ST.Sh{l, d, n, t})), gstep_at_case(~T, k, l, d, n, t, Nat.is_le(k, SC.pow2(d)), {==})) : {DA.grow_until_at(~T, g, k, _) == ST.real(T, GR.sgrow(T, g, k, GR.sgstep(T, k, ST.Sh{l, d, n, t}))) : DA.DynArray<&2, T>}
      grow_until_at_real(~T, g, k, GR.sgstep(T, k, ST.Sh{l, d, n, t}))

def grow_until_eq(~T: Data, +f: Nat, +k: Nat, +sh: ST.Shadow<T>) -> {DA.grow_until_at(~T, f, k, ST.real(T, sh)) == DA.grow_until(T, f, k, ST.real(T, sh)) : DA.DynArray<&2, T>}:
  %Equal.sym(DA.DynArray<&2, T>, DA.grow_until(T, f, k, ST.real(T, sh)), ST.real(T, GR.sgrow(T, f, k, sh)), GR.grow_until_real(T, f, k, sh)) : {DA.grow_until_at(~T, f, k, ST.real(T, sh)) == _ : DA.DynArray<&2, T>}
  grow_until_at_real(~T, f, k, sh)

# ---- the flattening walk ----

def get_eq_case(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.Get{i}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.Get{i}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {DA.obs_item(T, DA.get_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) == DA.obs_item(T, DA.get_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {DA.obs_item(T, DA.get_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) == DA.obs_item(T, DA.get_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}

def set_eq_case(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +v: T, +b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.Set{i, v}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.Set{i, v}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {DA.obs_unit(T, DA.set_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) == DA.obs_unit(T, DA.set_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {DA.obs_unit(T, DA.set_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) == DA.obs_unit(T, DA.set_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}

def push_eq_case(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +room: Bool, +er: {Nat.is_lt(n, SC.pow2(d)) == room : Bool}, +grow: Bool, +eg: {Nat.is_lt(d, l) == grow : Bool}) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.Push{v}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.Push{v}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match room grow:
    case True{} _:
      %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), True{}, er) : {DA.obs_unit(T, DA.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, er) : {DA.obs_unit(T, DA.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Bool, Nat.is_lt(d, l), True{}, eg) : {DA.obs_unit(T, DA.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) == DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Array<Maybe<&2, T>>, DA.grown_at(~T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_eq(T, d, t)) : {(DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(n), Some{v})}, E.OUnit{Done{Unit{}}}) == (DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)), U32.from_nat(n), Some{v})}, E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Array<Maybe<&2, T>>, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), ST.grown_eq(T, d, t)) : {(DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), U32.from_nat(n), Some{v})}, E.OUnit{Done{Unit{}}}) == (DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(n), Some{v})}, E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, er) : {DA.obs_unit(T, DA.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Bool, Nat.is_lt(d, l), False{}, eg) : {DA.obs_unit(T, DA.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) == DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}

def pop_eq_case(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.Pop{}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.Pop{}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      {==}

def tl_go_eq(~T: Data, k: Nat, acc: List<&2, T>, r: Array<Maybe<&2, T>> & Maybe<&2, T>) -> {DA.tl_go_at(~T, k, acc, r) == DA.tl_go(k, T, acc, r) : Array<Maybe<&2, T>> & List<&2, T>}:
  match k r:
    case 0n Tuple{a, x}:
      {==}
    case 1n+ +m Tuple{a, x}:
      tl_go_eq(~T, m, DA.cons_some(T, x, acc), Array.get(Maybe<&2, T>, a, U32.from_nat(DA.dec1(m))))

def to_list_eq(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.ToList{}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.ToList{}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      Equal.cong(Array<Maybe<&2, T>> & List<&2, T>, DA.DynArray<&2, T> & E.Obs<T>, r => DA.obs_list(T, DA.tl_done(T, l, d, SC.pow2(d), 1n+m, r)),
        DA.tl_go_at(~T, 1n+m, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m))),
        DA.tl_go(1n+m, T, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m))),
        tl_go_eq(~T, 1n+m, Nil{}, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m))))

def reserve_eq_case(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +k: Nat, +fits: Bool, +ef: {Nat.is_le(k, SC.pow2(d)) == fits : Bool}, +feas: Bool, +ep: {Nat.is_le(k, DA.pow2(l)) == feas : Bool}) -> {DA.step_at(~T, ST.real(T, ST.Sh{l, d, n, t}), E.Reserve{k}) == DA.step(T, ST.real(T, ST.Sh{l, d, n, t}), E.Reserve{k}) : DA.DynArray<&2, T> & E.Obs<T>}:
  match fits feas:
    case True{} _:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, ef) : {DA.obs_unit(T, DA.reserve_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {DA.obs_unit(T, DA.reserve_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.trans(Nat, DA.pow2(l), SC.pow2(l), P2.pow2t(l), ST.pow2_src(l), Equal.sym(Nat, P2.pow2t(l), SC.pow2(l), PT.same(l))) : {DA.obs_unit(T, DA.reserve_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, Nat.is_le(k, _))) == DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, Nat.is_le(k, DA.pow2(l)))) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Bool, Nat.is_le(k, DA.pow2(l)), True{}, ep) : {DA.obs_unit(T, DA.reserve_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(DA.DynArray<&2, T>, DA.grow_until_at(~T, Nat.sub(l, d), k, ST.real(T, ST.Sh{l, d, n, t})), DA.grow_until(T, Nat.sub(l, d), k, ST.real(T, ST.Sh{l, d, n, t})), grow_until_eq(~T, Nat.sub(l, d), k, ST.Sh{l, d, n, t})) : {(_, E.OUnit{Done{Unit{}}}) == (DA.grow_until(T, Nat.sub(l, d), k, DA.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {DA.obs_unit(T, DA.reserve_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.trans(Nat, DA.pow2(l), SC.pow2(l), P2.pow2t(l), ST.pow2_src(l), Equal.sym(Nat, P2.pow2t(l), SC.pow2(l), PT.same(l))) : {DA.obs_unit(T, DA.reserve_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, Nat.is_le(k, _))) == DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, Nat.is_le(k, DA.pow2(l)))) : DA.DynArray<&2, T> & E.Obs<T>}
      %Equal.sym(Bool, Nat.is_le(k, DA.pow2(l)), False{}, ep) : {DA.obs_unit(T, DA.reserve_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) : DA.DynArray<&2, T> & E.Obs<T>}
      {==}

def step_eq(~T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> {DA.step_at(~T, ST.real(T, sh), op) == DA.step(T, ST.real(T, sh), op) : DA.DynArray<&2, T> & E.Obs<T>}:
  match sh op:
    case ST.Sh{+l, +d, +n, +t} E.Length{}:
      {==}
    case ST.Sh{+l, +d, +n, +t} E.Capacity{}:
      {==}
    case ST.Sh{+l, +d, +n, +t} E.Get{+i}:
      get_eq_case(~T, l, d, n, t, i, Nat.is_lt(i, n), {==})
    case ST.Sh{+l, +d, +n, +t} E.Set{+i, +v}:
      set_eq_case(~T, l, d, n, t, i, v, Nat.is_lt(i, n), {==})
    case ST.Sh{+l, +d, +n, +t} E.Push{+v}:
      push_eq_case(~T, l, d, n, t, v, Nat.is_lt(n, SC.pow2(d)), {==}, Nat.is_lt(d, l), {==})
    case ST.Sh{+l, +d, +n, +t} E.Pop{}:
      pop_eq_case(~T, l, d, n, t)
    case ST.Sh{+l, +d, +n, +t} E.Reserve{+k}:
      reserve_eq_case(~T, l, d, n, t, k, Nat.is_le(k, SC.pow2(d)), {==}, Nat.is_le(k, DA.pow2(l)), {==})
    case ST.Sh{+l, +d, +n, +t} E.Clear{}:
      Equal.cong(DA.DynArray<&2, T>, DA.DynArray<&2, T> & E.Obs<T>, z => (z, E.OUnit{Done{Unit{}}}), DA.clear_at(~T, ST.real(T, ST.Sh{l, d, n, t})), DA.clear(T, ST.real(T, ST.Sh{l, d, n, t})), CLR.clear_eq(~T, l, d, n, t, g))
    case ST.Sh{+l, +d, +n, +t} E.ToList{}:
      to_list_eq(~T, l, d, n, t)

# ---- whole traces ----

def run_acc_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +acc: List<&2, E.Obs<T>>, +g: {ST.good(T, sh) == True{} : Bool}) -> {DA.run_acc_at(~T, ops, (ST.real(T, sh), acc)) == DA.run_acc(T, ops, (ST.real(T, sh), acc)) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}:
  match ops:
    case Nil{}:
      {==}
    case Con{+op, +rest}:
      +sh1 = TR.so_sh(T, sh, op, SP.step_ok(T, sh, op, g))
      +o = TR.so_obs(T, sh, op, SP.step_ok(T, sh, op, g))
      +g1 = TR.so_good(T, sh, op, SP.step_ok(T, sh, op, g))
      %Equal.sym(DA.DynArray<&2, T> & E.Obs<T>, DA.step_at(~T, ST.real(T, sh), op), DA.step(T, ST.real(T, sh), op), step_eq(~T, sh, op, g)) : {DA.run_acc_at(~T, rest, DA.record(T, acc, _)) == DA.run_acc(T, rest, DA.record(T, acc, DA.step(T, ST.real(T, sh), op))) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}
      %Equal.sym(DA.DynArray<&2, T> & E.Obs<T>, DA.step(T, ST.real(T, sh), op), (ST.real(T, sh1), o), TR.so_step(T, sh, op, SP.step_ok(T, sh, op, g))) : {DA.run_acc_at(~T, rest, DA.record(T, acc, _)) == DA.run_acc(T, rest, DA.record(T, acc, _)) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}
      run_acc_eq(~T, rest, sh1, Con{o, acc}, g1)

def run_eq(~T: Data, +ops: List<&2, E.Op<T>>, +sh: ST.Shadow<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> {DA.run_at(~T, ops, ST.real(T, sh)) == DA.run(T, ops, ST.real(T, sh)) : DA.DynArray<&2, T> & List<&2, E.Obs<T>>}:
  Equal.cong(DA.DynArray<&2, T> & List<&2, E.Obs<T>>, DA.DynArray<&2, T> & List<&2, E.Obs<T>>, r => DA.finish(T, r), DA.run_acc_at(~T, ops, (ST.real(T, sh), Nil{})), DA.run_acc(T, ops, (ST.real(T, sh), Nil{})), run_acc_eq(~T, ops, sh, Nil{}, g))

# ---- the constructors ----

def new_eq(~T: Data) -> {DA.new_at(~T) == DA.new(T) : DA.DynArray<&2, T>}:
  {==}

def with_limit_eq(~T: Data, +k: Nat) -> {DA.with_limit_at(~T, k) == DA.with_limit(T, k) : DA.DynArray<&2, T>}:
  {==}
