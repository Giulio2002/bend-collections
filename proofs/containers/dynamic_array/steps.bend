import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/dynamic_array.bend as DA
import ../../../src/containers/types/dynamic_array.bend as E
import ./layout.bend as LY
import ./state.bend as ST
import ./growth.bend as GR
import ./walk.bend as W

# One actual public operation on a good shadow's array yields the array of a
# new good shadow, and (abstract state, observation) equals the spec step.
def StepOK(-T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {DA.step(T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DA.DynArray<&2, T> & E.Obs<T>} & ({ST.good(T, sh2) == True{} : Bool} & {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : S.Model<T> & E.Obs<T>})>>

def length_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Length{}):
  +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
  (ST.Sh{l, d, n, t}, (E.ONat{n}, ({==}, (g,
    %Equal.sym(Nat, SC.length(T, xs), n, LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g))) : {(S.M{l, d, xs}, E.ONat{n}) == (S.M{l, d, xs}, E.ONat{_}) : S.Model<T> & E.Obs<T>}
    {==}))))

def capacity_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Capacity{}):
  +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
  (ST.Sh{l, d, n, t}, (E.ONat{SC.pow2(d)}, ({==}, (g,
    {==}))))

# ---- facts shared by indexed operations ----

def n_le_cap(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_le(n, k) == True{} : Bool}, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, ST.g_perfect(T, l, d, n, t, g)), LY.lay_le(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g)))

def idx_lt(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(U32.from_nat(i)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, U.to_nat_from_nat(i, d, ST.le32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), hi)), hi)

def idx_slot(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +x: Maybe<&2, T>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), i) == Some{x} : Maybe<&2, Maybe<&2, T>>}) -> {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), U32.to_nat(U32.from_nat(i))) == Some{x} : Maybe<&2, Maybe<&2, T>>}:
  L.subst(Nat, k => {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), k) == Some{x} : Maybe<&2, Maybe<&2, T>>}, i, U32.to_nat(U32.from_nat(i)), Equal.sym(Nat, U32.to_nat(U32.from_nat(i)), i, U.to_nat_from_nat(i, d, ST.le32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), hi)), hx)

# ---- get ----

def get_case(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Get{i}):
  match b:
    case True{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      +x = SC.nth(T, xs, i)
      +hi = N.lt_le_trans(i, n, SC.pow2(d), eb, n_le_cap(T, l, d, n, t, g))
      (ST.Sh{l, d, n, t}, (E.OItem{S.item_result(T, x)}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {DA.obs_item(T, DA.get_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OItem{S.item_result(T, x)}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i)), (AR.thaw(Maybe<&2, T>, t), x), AR.get(Maybe<&2, T>, d, t, U32.from_nat(i), x, ST.lt32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), idx_lt(T, l, d, n, t, i, g, hi), idx_slot(T, l, d, n, t, i, x, g, hi, LY.lay_nth(T, ss, n, i, ST.g_lay(T, l, d, n, t, g), eb)), ST.g_perfect(T, l, d, n, t, g))) : {DA.obs_item(T, DA.get_found(T, l, d, SC.pow2(d), n, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OItem{S.item_result(T, x)}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DA.slot_result(T, x), S.item_result(T, x), ST.slot_item(T, x)) : {(DA.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)}, E.OItem{_}) == (ST.real(T, ST.Sh{l, d, n, t}), E.OItem{S.item_result(T, x)}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==}, (g, {==}))))
    case False{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      (ST.Sh{l, d, n, t}, (E.OItem{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {DA.obs_item(T, DA.get_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OItem{Fail{E.IndexOutOfRange{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==}, (g,
        %Equal.sym(Maybe<&2, T>, SC.nth(T, xs, i), None{}, LL.nth_none(T, xs, i, L.subst(Nat, k => {Nat.is_le(k, i) == True{} : Bool}, n, SC.length(T, xs), Equal.sym(Nat, SC.length(T, xs), n, LY.lay_len(T, ss, n, ST.g_lay(T, l, d, n, t, g))), N.not_lt_le(i, n, eb)))) : {(S.M{l, d, xs}, E.OItem{Fail{E.IndexOutOfRange{}}}) == (S.M{l, d, xs}, E.OItem{S.item_result(T, _)}) : S.Model<T> & E.Obs<T>}
        {==}))))

def get_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Get{i}):
  get_case(T, l, d, n, t, i, g, Nat.is_lt(i, n), {==})

# ---- writes through Base.Array.set / swap at a checked Nat index ----

def set_arr(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +w: Maybe<&2, T>, +x: Maybe<&2, T>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), i) == Some{x} : Maybe<&2, Maybe<&2, T>>}) -> {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), w) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, w)) : Array<Maybe<&2, T>>}:
  L.subst(Nat, k => {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), w) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, k, w)) : Array<Maybe<&2, T>>}, U32.to_nat(U32.from_nat(i)), i, U.to_nat_from_nat(i, d, ST.le32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), hi),
    AR.set(Maybe<&2, T>, d, t, U32.from_nat(i), w, x, ST.lt32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), idx_lt(T, l, d, n, t, i, g, hi), idx_slot(T, l, d, n, t, i, x, g, hi, hx), ST.g_perfect(T, l, d, n, t, g)))

def swap_arr(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +w: Maybe<&2, T>, +x: Maybe<&2, T>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), i) == Some{x} : Maybe<&2, Maybe<&2, T>>}) -> {Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), w) == (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, w)), x) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  L.subst(Nat, k => {Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), w) == (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, k, w)), x) : Array<Maybe<&2, T>> & Maybe<&2, T>}, U32.to_nat(U32.from_nat(i)), i, U.to_nat_from_nat(i, d, ST.le32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), hi),
    AR.swap(Maybe<&2, T>, d, t, U32.from_nat(i), w, x, ST.lt32(d, l, ST.g_depth(T, l, d, n, t, g), ST.g_limit(T, l, d, n, t, g)), idx_lt(T, l, d, n, t, i, g, hi), idx_slot(T, l, d, n, t, i, x, g, hi, hx), ST.g_perfect(T, l, d, n, t, g)))

# slots of an updated tree (index below the capacity).
def upd_slots(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +w: Maybe<&2, T>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {AR.slots(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, w)) == SC.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), i, w) : List<&2, Maybe<&2, T>>}:
  AR.upd_slots(Maybe<&2, T>, d, t, i, w, hi, ST.g_perfect(T, l, d, n, t, g))

# ---- set ----

def set_case(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +b: Bool, +eb: {Nat.is_lt(i, n) == b : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Set{i, v}):
  match b:
    case True{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      +hi = N.lt_le_trans(i, n, SC.pow2(d), eb, n_le_cap(T, l, d, n, t, g))
      +t2 = AR.upd(Maybe<&2, T>, d, t, i, Some{v})
      +hs = upd_slots(T, l, d, n, t, i, Some{v}, g, hi)
      +hlay = ST.g_lay(T, l, d, n, t, g)
      +hlen = LY.lay_len(T, ss, n, hlay)
      (ST.Sh{l, d, n, t2}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {DA.obs_unit(T, DA.set_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) == (ST.real(T, ST.Sh{l, d, n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), Some{v}), AR.thaw(Maybe<&2, T>, t2), set_arr(T, l, d, n, t, i, Some{v}, SC.nth(T, xs, i), g, hi, LY.lay_nth(T, ss, n, i, hlay, eb))) : {(DA.DA{l, d, SC.pow2(d), n, _}, E.OUnit{Done{Unit{}}}) == (ST.real(T, ST.Sh{l, d, n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (ST.good_intro(T, l, d, n, t2, ST.g_limit(T, l, d, n, t, g), ST.g_depth(T, l, d, n, t, g), AR.upd_perfect(Maybe<&2, T>, d, t, i, Some{v}, ST.g_perfect(T, l, d, n, t, g)),
           L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, i, Some{v}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, i, Some{v}), hs), LY.lay_set(T, ss, n, i, v, hlay, eb))),
         %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, i, Some{v}), hs) : {(S.M{l, d, LY.somes(T, _)}, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Set{i, v}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, i, Some{v})), SC.update(T, xs, i, v), LY.somes_set(T, ss, n, i, v, hlay, eb)) : {(S.M{l, d, _}, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Set{i, v}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Nat, SC.length(T, xs), n, hlen) : {(S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(i, _), (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(i, n), True{}, eb) : {(S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))
    case False{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      +hlen = LY.lay_len(T, ss, n, ST.g_lay(T, l, d, n, t, g))
      (ST.Sh{l, d, n, t}, (E.OUnit{Fail{E.IndexOutOfRange{}}}, (
        %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {DA.obs_unit(T, DA.set_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Fail{E.IndexOutOfRange{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(T, xs), n, hlen) : {(S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(i, _), (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(i, n), False{}, eb) : {(S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.update(T, xs, i, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.IndexOutOfRange{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))

def set_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +i: Nat, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Set{i, v}):
  set_case(T, l, d, n, t, i, v, g, Nat.is_lt(i, n), {==})

# ---- push ----

def len_slots(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(n, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t))) == True{} : Bool}:
  L.subst(Nat, k => {Nat.is_lt(n, k) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), Equal.sym(Nat, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, ST.g_perfect(T, l, d, n, t, g))), hn)

def pi_arr(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(n), Some{v}) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, n, Some{v})) : Array<Maybe<&2, T>>}:
  set_arr(T, l, d, n, t, n, Some{v}, None{}, g, hn, LY.push_free(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g), len_slots(T, l, d, n, t, g, hn)))

def pi_good(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> {ST.good(T, ST.Sh{l, d, 1n+n, AR.upd(Maybe<&2, T>, d, t, n, Some{v})}) == True{} : Bool}:
  +ss = AR.slots(Maybe<&2, T>, t)
  +t2 = AR.upd(Maybe<&2, T>, d, t, n, Some{v})
  ST.good_intro(T, l, d, 1n+n, t2, ST.g_limit(T, l, d, n, t, g), ST.g_depth(T, l, d, n, t, g), AR.upd_perfect(Maybe<&2, T>, d, t, n, Some{v}, ST.g_perfect(T, l, d, n, t, g)),
    L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, 1n+n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, n, Some{v}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, n, Some{v}), upd_slots(T, l, d, n, t, n, Some{v}, g, hn)), LY.lay_push(T, ss, n, v, ST.g_lay(T, l, d, n, t, g), len_slots(T, l, d, n, t, g, hn))))

def pi_model(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +hn: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> {LY.somes(T, AR.slots(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, n, Some{v}))) == SC.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), v) : List<&2, T>}:
  +ss = AR.slots(Maybe<&2, T>, t)
  Equal.trans(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, n, Some{v}))), LY.somes(T, SC.update(Maybe<&2, T>, ss, n, Some{v})), SC.snoc(T, LY.somes(T, ss), v),
    Equal.cong(List<&2, Maybe<&2, T>>, List<&2, T>, ys => LY.somes(T, ys), AR.slots(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, n, Some{v})), SC.update(Maybe<&2, T>, ss, n, Some{v}), upd_slots(T, l, d, n, t, n, Some{v}, g, hn)),
    LY.somes_push(T, ss, n, v, ST.g_lay(T, l, d, n, t, g), len_slots(T, l, d, n, t, g, hn)))

def room_nat(+n: Nat, +d: Nat, +b: Bool, +e: {Nat.is_lt(n, SC.pow2(d)) == b : Bool}) -> {Nat.is_lt(n, SC.pow2(d)) == b : Bool}:
  e

def push_case(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +room: Bool, +er: {Nat.is_lt(n, SC.pow2(d)) == room : Bool}, +grow: Bool, +eg: {Nat.is_lt(d, l) == grow : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Push{v}):
  match room grow:
    case True{} _:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      +hn = room_nat(n, d, True{}, er)
      +t2 = AR.upd(Maybe<&2, T>, d, t, n, Some{v})
      (ST.Sh{l, d, 1n+n, t2}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), True{}, er) : {DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == (ST.real(T, ST.Sh{l, d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, t2), pi_arr(T, l, d, n, t, v, g, hn)) : {(DA.DA{l, d, SC.pow2(d), 1n+n, _}, E.OUnit{Done{Unit{}}}) == (ST.real(T, ST.Sh{l, d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (pi_good(T, l, d, n, t, v, g, hn),
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t2)), SC.snoc(T, xs, v), pi_model(T, l, d, n, t, v, g, hn)) : {(S.M{l, d, _}, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Push{v}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Nat, SC.length(T, xs), n, LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g))) : {(S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(_, SC.pow2(d)), (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), True{}, hn) : {(S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         {==}))))
    case False{} True{}:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      +nf = room_nat(n, d, False{}, er)
      +t1 = {AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})} : AR.Tree<Maybe<&2, T>>}
      +g1 = GR.grow_good(T, l, d, n, t, g, eg)
      +hn = N.le_lt_trans(n, SC.pow2(d), SC.pow2(1n+d), n_le_cap(T, l, d, n, t, g), N.pow2_lt_succ(d))
      +t2 = AR.upd(Maybe<&2, T>, 1n+d, t1, n, Some{v})
      (ST.Sh{l, 1n+d, 1n+n, t2}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, er) : {DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == (ST.real(T, ST.Sh{l, 1n+d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_lt(d, l), True{}, eg) : {DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) == (ST.real(T, ST.Sh{l, 1n+d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, DA.grown(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, t1), ST.grown_eq(T, d, t)) : {(DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(n), Some{v})}, E.OUnit{Done{Unit{}}}) == (ST.real(T, ST.Sh{l, 1n+d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t1), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, t2), pi_arr(T, l, 1n+d, n, t1, v, g1, hn)) : {(DA.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, _}, E.OUnit{Done{Unit{}}}) == (ST.real(T, ST.Sh{l, 1n+d, 1n+n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (pi_good(T, l, 1n+d, n, t1, v, g1, hn),
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t2)), SC.snoc(T, LY.somes(T, AR.slots(Maybe<&2, T>, t1)), v), pi_model(T, l, 1n+d, n, t1, v, g1, hn)) : {(S.M{l, 1n+d, _}, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Push{v}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, t1)), xs, GR.grow_model(T, d, t)) : {(S.M{l, 1n+d, SC.snoc(T, _, v)}, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Push{v}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Nat, SC.length(T, xs), n, LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g))) : {(S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(_, SC.pow2(d)), (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, nf) : {(S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(d, l), True{}, eg) : {(S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))
    case False{} False{}:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      +nf = room_nat(n, d, False{}, er)
      (ST.Sh{l, d, n, t}, (E.OUnit{Fail{E.CapacityExceeded{}}}, (
        %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, er) : {DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l))) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Fail{E.CapacityExceeded{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_lt(d, l), False{}, eg) : {DA.obs_unit(T, DA.push_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Fail{E.CapacityExceeded{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (g,
         %Equal.sym(Nat, SC.length(T, xs), n, LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, ST.g_lay(T, l, d, n, t, g))) : {(S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(_, SC.pow2(d)), (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, nf) : {(S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_lt(d, l), (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_lt(d, l), False{}, eg) : {(S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, 1n+d, SC.snoc(T, xs, v)}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))

def push_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Push{v}):
  push_case(T, l, d, n, t, v, g, Nat.is_lt(n, SC.pow2(d)), {==}, Nat.is_lt(d, l), {==})

# ---- pop ----

def pop_spec(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +m: Nat, +h: {SC.length(T, xs) == 1n+m : Nat}) -> {S.pop(T, l, d, xs) == (S.M{l, d, SC.init(T, xs)}, E.OItem{S.item_result(T, SC.nth(T, xs, m))}) : S.Model<T> & E.Obs<T>}:
  match xs:
    case Nil{}:
      Empty.absurd({S.pop(T, l, d, Nil{}) == (S.M{l, d, Nil{}}, E.OItem{S.item_result(T, None{})}) : S.Model<T> & E.Obs<T>}, N.zero_succ(m, h))
    case Con{+x, +r}:
      %Equal.sym(Maybe<&2, T>, SC.nth(T, Con{x, r}, m), SC.last(T, Con{x, r}), LY.nth_last(T, Con{x, r}, m, h)) : {(S.M{l, d, SC.init(T, Con{x, r})}, E.OItem{S.item_result(T, SC.last(T, Con{x, r}))}) == (S.M{l, d, SC.init(T, Con{x, r})}, E.OItem{S.item_result(T, _)}) : S.Model<T> & E.Obs<T>}
      {==}

def pop_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Pop{}):
  match n:
    case 0n:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      (ST.Sh{l, d, 0n, t}, (E.OItem{Fail{E.EmptyArray{}}}, ({==}, (g,
        %Equal.sym(List<&2, T>, xs, Nil{}, LL.length_zero_nil(T, xs, LY.lay_len(T, AR.slots(Maybe<&2, T>, t), 0n, ST.g_lay(T, l, d, 0n, t, g)))) : {(S.M{l, d, _}, E.OItem{Fail{E.EmptyArray{}}}) == S.pop(T, l, d, _) : S.Model<T> & E.Obs<T>}
        {==}))))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      +x = SC.nth(T, xs, m)
      +hlay = ST.g_lay(T, l, d, 1n+m, t, g)
      +hm = N.lt_succ(m)
      +hi = N.lt_le_trans(m, 1n+m, SC.pow2(d), hm, n_le_cap(T, l, d, 1n+m, t, g))
      +t2 = AR.upd(Maybe<&2, T>, d, t, m, None{})
      +hs = upd_slots(T, l, d, 1n+m, t, m, None{}, g, hi)
      (ST.Sh{l, d, m, t2}, (E.OItem{S.item_result(T, x)}, (
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m), None{}), (AR.thaw(Maybe<&2, T>, t2), x), swap_arr(T, l, d, 1n+m, t, m, None{}, x, g, hi, LY.lay_nth(T, ss, 1n+m, m, hlay, hm))) : {DA.obs_item(T, DA.pop_found(T, l, d, SC.pow2(d), m, _)) == (ST.real(T, ST.Sh{l, d, m, t2}), E.OItem{S.item_result(T, x)}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DA.slot_result(T, x), S.item_result(T, x), ST.slot_item(T, x)) : {(DA.DA{l, d, SC.pow2(d), m, AR.thaw(Maybe<&2, T>, t2)}, E.OItem{_}) == (ST.real(T, ST.Sh{l, d, m, t2}), E.OItem{S.item_result(T, x)}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (ST.good_intro(T, l, d, m, t2, ST.g_limit(T, l, d, 1n+m, t, g), ST.g_depth(T, l, d, 1n+m, t, g), AR.upd_perfect(Maybe<&2, T>, d, t, m, None{}, ST.g_perfect(T, l, d, 1n+m, t, g)),
           L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, m) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, m, None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, m, None{}), hs), LY.lay_pop(T, ss, m, hlay))),
         %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, m, None{}), hs) : {(S.M{l, d, LY.somes(T, _)}, E.OItem{S.item_result(T, x)}) == S.pop(T, l, d, xs) : S.Model<T> & E.Obs<T>}
         %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, m, None{})), SC.init(T, xs), LY.somes_pop(T, ss, m, hlay)) : {(S.M{l, d, _}, E.OItem{S.item_result(T, x)}) == S.pop(T, l, d, xs) : S.Model<T> & E.Obs<T>}
         Equal.sym(S.Model<T> & E.Obs<T>, S.pop(T, l, d, xs), (S.M{l, d, SC.init(T, xs)}, E.OItem{S.item_result(T, x)}), pop_spec(T, l, d, xs, m, LY.lay_len(T, ss, 1n+m, hlay)))))))

# ---- clear ----

def clear_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Clear{}):
  +t2 = AR.trep(Maybe<&2, T>, d, None{})
  (ST.Sh{l, d, 0n, t2}, (E.OUnit{Done{Unit{}}}, (
    %Equal.sym(Array<Maybe<&2, T>>, DA.empty_slots(T, d), AR.thaw(Maybe<&2, T>, t2), ST.empty_eq(T, d)) : {(DA.DA{l, d, SC.pow2(d), 0n, _}, E.OUnit{Done{Unit{}}}) == (ST.real(T, ST.Sh{l, d, 0n, t2}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
    {==},
    (ST.good_intro(T, l, d, 0n, t2, ST.g_limit(T, l, d, n, t, g), ST.g_depth(T, l, d, n, t, g), AR.trep_perfect(Maybe<&2, T>, d, None{}),
       L.subst(List<&2, Maybe<&2, T>>, ys => {LY.lay(T, ys, 0n) == True{} : Bool}, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})), LY.lay_rep(T, SC.pow2(d)))),
     %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), AR.trep_slots(Maybe<&2, T>, d, None{})) : {(S.M{l, d, LY.somes(T, _)}, E.OUnit{Done{Unit{}}}) == (S.M{l, d, Nil{}}, E.OUnit{S.ok_unit()}) : S.Model<T> & E.Obs<T>}
     %Equal.sym(List<&2, T>, LY.somes(T, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), Nil{}, LY.somes_rep(T, SC.pow2(d))) : {(S.M{l, d, _}, E.OUnit{Done{Unit{}}}) == (S.M{l, d, Nil{}}, E.OUnit{S.ok_unit()}) : S.Model<T> & E.Obs<T>}
     {==}))))

# ---- to_list ----

def to_list_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.ToList{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      (ST.Sh{l, d, 0n, t}, (E.OList{xs}, (
        %Equal.sym(List<&2, T>, xs, Nil{}, LL.length_zero_nil(T, xs, LY.lay_len(T, ss, 0n, ST.g_lay(T, l, d, 0n, t, g)))) : {(DA.DA{l, d, SC.pow2(d), 0n, AR.thaw(Maybe<&2, T>, t)}, E.OList{Nil{}}) == (ST.real(T, ST.Sh{l, d, 0n, t}), E.OList{_}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==}, (g, {==}))))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +xs = LY.somes(T, ss)
      +hlay = ST.g_lay(T, l, d, 1n+m, t, g)
      +hd = ST.g_depth(T, l, d, 1n+m, t, g)
      +hl = ST.g_limit(T, l, d, 1n+m, t, g)
      +pf = ST.g_perfect(T, l, d, 1n+m, t, g)
      +hm = N.succ_le_lt(m, SC.pow2(d), n_le_cap(T, l, d, 1n+m, t, g))
      (ST.Sh{l, d, 1n+m, t}, (E.OList{xs}, (
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(m)), (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, m)), W.get_slot(T, l, d, t, m, hd, hl, hm, pf)) : {DA.obs_list(T, DA.tl_done(T, l, d, SC.pow2(d), 1n+m, DA.tl_go(1n+m, T, Nil{}, _))) == (ST.real(T, ST.Sh{l, d, 1n+m, t}), E.OList{xs}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>> & List<&2, T>, DA.tl_go(1n+m, T, Nil{}, (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, m))), (AR.thaw(Maybe<&2, T>, t), W.tvals(1n+m, T, ss, Nil{})), W.tl_thaw(1n+m, T, l, d, t, Nil{}, hd, hl, hm, pf)) : {DA.obs_list(T, DA.tl_done(T, l, d, SC.pow2(d), 1n+m, _)) == (ST.real(T, ST.Sh{l, d, 1n+m, t}), E.OList{xs}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, W.tvals(1n+m, T, ss, Nil{}), xs, W.tvals_model(T, ss, 1n+m, hlay)) : {(DA.DA{l, d, SC.pow2(d), 1n+m, AR.thaw(Maybe<&2, T>, t)}, E.OList{_}) == (ST.real(T, ST.Sh{l, d, 1n+m, t}), E.OList{xs}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==}, (g, {==}))))

# ---- reserve ----

def feasible_fuel(+l: Nat, +d: Nat, +k: Nat, +hdl: {Nat.is_le(d, l) == True{} : Bool}, +hp: {Nat.is_le(k, SC.pow2(l)) == True{} : Bool}) -> {Nat.is_le(k, SC.pow2(Nat.add(d, Nat.sub(l, d)))) == True{} : Bool}:
  L.subst(Nat, x => {Nat.is_le(k, SC.pow2(x)) == True{} : Bool}, l, Nat.add(d, Nat.sub(l, d)), Equal.sym(Nat, Nat.add(d, Nat.sub(l, d)), l, N.sub_add(l, d, hdl)), hp)

def spec_fuel(+d: Nat, +k: Nat) -> {Nat.is_le(k, SC.pow2(Nat.add(d, k))) == True{} : Bool}:
  N.lt_le(k, SC.pow2(Nat.add(d, k)), N.lt_le_trans(k, SC.pow2(k), SC.pow2(Nat.add(d, k)), GR.pow2_gt(k), N.pow2_mono(k, Nat.add(d, k), L.subst(Nat, x => {Nat.is_le(k, x) == True{} : Bool}, Nat.add(k, d), Nat.add(d, k), N.add_comm(k, d), N.le_add_right(k, d)))))

def reserve_case(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +k: Nat, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}, +fits: Bool, +ef: {Nat.is_le(k, SC.pow2(d)) == fits : Bool}, +feas: Bool, +ep: {Nat.is_le(k, DA.pow2(l)) == feas : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Reserve{k}):
  match fits feas:
    case True{} _:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      (ST.Sh{l, d, n, t}, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, ef) : {DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (g,
         %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), True{}, ef) : {(S.M{l, d, xs}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(k, SC.pow2(l)), (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         {==}))))
    case False{} True{}:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      +f = Nat.sub(l, d)
      +sh2 = GR.sgrow(T, f, k, ST.Sh{l, d, n, t})
      +hdl = ST.g_depth(T, l, d, n, t, g)
      +hp = GR.fits_nat(k, l, True{}, ep)
      -mP = {ST.model(T, sh2) == S.M{l, S.fit(f, d, k), xs} : S.Model<T>}
      -gP = {ST.good(T, sh2) == True{} : Bool}
      +hf = L.subst(Nat, x => {Nat.is_le(x, l) == True{} : Bool}, l, Nat.add(d, f), Equal.sym(Nat, Nat.add(d, f), l, N.sub_add(l, d, hdl)), N.le_refl(l))
      (sh2, (E.OUnit{Done{Unit{}}}, (
        %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == (ST.real(T, sh2), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_le(k, DA.pow2(l)), True{}, ep) : {DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == (ST.real(T, sh2), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(DA.DynArray<&2, T>, DA.grow_until(T, f, k, ST.real(T, ST.Sh{l, d, n, t})), ST.real(T, sh2), GR.grow_until_real(T, f, k, ST.Sh{l, d, n, t})) : {(_, E.OUnit{Done{Unit{}}}) == (ST.real(T, sh2), E.OUnit{Done{Unit{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (Pair.snd(mP, gP, GR.sgrow_props(T, f, k, l, d, n, t, g, hf, Nat.is_le(k, SC.pow2(d)), {==})),
         %Equal.sym(S.Model<T>, ST.model(T, sh2), S.M{l, S.fit(f, d, k), xs}, Pair.fst(mP, gP, GR.sgrow_props(T, f, k, l, d, n, t, g, hf, Nat.is_le(k, SC.pow2(d)), {==}))) : {(_, E.OUnit{Done{Unit{}}}) == S.step(T, S.M{l, d, xs}, E.Reserve{k}) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Nat, S.fit(f, d, k), S.fit(k, d, k), GR.fe_case(f, k, d, k, feasible_fuel(l, d, k, hdl, hp), spec_fuel(d, k), Nat.is_le(k, SC.pow2(d)), {==})) : {(S.M{l, _, xs}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(k, SC.pow2(d)), (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(k, SC.pow2(l)), (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {(S.M{l, S.fit(k, d, k), xs}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(k, SC.pow2(l)), (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_le(k, SC.pow2(l)), True{}, hp) : {(S.M{l, S.fit(k, d, k), xs}, E.OUnit{Done{Unit{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))
    case False{} False{}:
      +xs = LY.somes(T, AR.slots(Maybe<&2, T>, t))
      (ST.Sh{l, d, n, t}, (E.OUnit{Fail{E.CapacityExceeded{}}}, (
        %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {DA.obs_unit(T, DA.reserve_checked(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Fail{E.CapacityExceeded{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        %Equal.sym(Bool, Nat.is_le(k, DA.pow2(l)), False{}, ep) : {DA.obs_unit(T, DA.reserve_room(T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), k, _)) == (ST.real(T, ST.Sh{l, d, n, t}), E.OUnit{Fail{E.CapacityExceeded{}}}) : DA.DynArray<&2, T> & E.Obs<T>}
        {==},
        (g,
         %Equal.sym(Bool, Nat.is_le(k, SC.pow2(d)), False{}, ef) : {(S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, d, xs}, E.OUnit{S.ok_unit()}), Bool.pick(S.Model<T> & E.Obs<T>, Nat.is_le(k, SC.pow2(l)), (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}))) : S.Model<T> & E.Obs<T>}
         %Equal.sym(Bool, Nat.is_le(k, SC.pow2(l)), False{}, GR.fits_nat(k, l, False{}, ep)) : {(S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}}) == Bool.pick(S.Model<T> & E.Obs<T>, _, (S.M{l, S.fit(k, d, k), xs}, E.OUnit{S.ok_unit()}), (S.M{l, d, xs}, E.OUnit{Fail{E.CapacityExceeded{}}})) : S.Model<T> & E.Obs<T>}
         {==}))))

def reserve_ok(-T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +k: Nat, +g: {ST.good(T, ST.Sh{l, d, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{l, d, n, t}, E.Reserve{k}):
  reserve_case(T, l, d, n, t, k, g, Nat.is_le(k, SC.pow2(d)), {==}, Nat.is_le(k, DA.pow2(l)), {==})

# ---- every operation ----

def step_ok(-T: Data, +sh: ST.Shadow<T>, +op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}) -> StepOK(T, sh, op):
  match sh op:
    case ST.Sh{+l, +d, +n, +t} E.Length{}:
      length_ok(T, l, d, n, t, g)
    case ST.Sh{+l, +d, +n, +t} E.Capacity{}:
      capacity_ok(T, l, d, n, t, g)
    case ST.Sh{+l, +d, +n, +t} E.Get{+i}:
      get_ok(T, l, d, n, t, i, g)
    case ST.Sh{+l, +d, +n, +t} E.Set{+i, +v}:
      set_ok(T, l, d, n, t, i, v, g)
    case ST.Sh{+l, +d, +n, +t} E.Push{+v}:
      push_ok(T, l, d, n, t, v, g)
    case ST.Sh{+l, +d, +n, +t} E.Pop{}:
      pop_ok(T, l, d, n, t, g)
    case ST.Sh{+l, +d, +n, +t} E.Reserve{+k}:
      reserve_ok(T, l, d, n, t, k, g)
    case ST.Sh{+l, +d, +n, +t} E.Clear{}:
      clear_ok(T, l, d, n, t, g)
    case ST.Sh{+l, +d, +n, +t} E.ToList{}:
      to_list_ok(T, l, d, n, t, g)
