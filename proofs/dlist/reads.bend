import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../binary_heap/u32idx.bend as IX
import ../graph/shift.bend as SH
import ../graph/ashift.bend as AS2
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./core.bend as K
import ./alive.bend as AL

# length and get, and the handle validation every handle operation shares.

def ln_obs(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +n: Nat) -> DS.Model<T> & E.Obs<T>:
  (ST.model(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), E.ONat{n})

def length_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Length{}):
  +xs = AR.slots(Maybe<&2, T>, tv)
  K.mk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Length{}, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.ONat{SC.length(Nat, ord)}, {==}, h,
    Equal.cong(Nat, DS.Model<T> & E.Obs<T>, n => ln_obs(~T, tag, fresh, depth, tv, tp, tn, ord, n), SC.length(Nat, ord), SC.length(E.Item<T>, ST.items(T, xs, ord)), Equal.sym(Nat, SC.length(E.Item<T>, ST.items(T, xs, ord)), SC.length(Nat, ord), AL.items_len(T, xs, ord, AL.g_alive(~T, tag, fresh, depth, tv, tp, tn, ord, h)))),
    K.same_fresh(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Length{}))

# ---- validating a handle ----

def fresh_nat(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(fresh)) == fresh : Nat}:
  IX.nat_round(fresh, 1n+depth, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.le_lt_trans(fresh, SC.pow2(depth), SC.pow2(1n+depth), F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.pow2_lt_succ(depth)))

# The runtime's `i < fresh` test, on naturals.
def ok_nat(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> {U32.is_lt(i, U32.from_nat(fresh)) == Nat.is_lt(U32.to_nat(i), fresh) : Bool}:
  Equal.trans(Bool, U32.is_lt(i, U32.from_nat(fresh)), Nat.is_lt(U32.to_nat(i), U32.to_nat(U32.from_nat(fresh))), Nat.is_lt(U32.to_nat(i), fresh),
    U.is_lt_nat(i, U32.from_nat(fresh)),
    Equal.cong(Nat, Bool, z => Nat.is_lt(U32.to_nat(i), z), U32.to_nat(U32.from_nat(fresh)), fresh, fresh_nat(~T, tag, fresh, depth, tv, tp, tn, ord, h)))

def hi_of(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(i), SC.pow2(depth)) == True{} : Bool}:
  N.lt_le_trans(U32.to_nat(i), fresh, SC.pow2(depth), hi, F.g_fresh(~T, tag, fresh, depth, tv, tp, tn, ord, h))

# the value slot of an issued handle
def xv(~T: Data, +tv: AR.Tree<Maybe<&2, T>>, +i: U32) -> Maybe<&2, T>:
  L.some_value(Maybe<&2, T>, SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), U32.to_nat(i)), None{})

def read_v(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i) == (AR.thaw(Maybe<&2, T>, tv), xv(~T, tv, i)) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  AR.get(Maybe<&2, T>, depth, tv, i, xv(~T, tv, i), N.le_lt_trans(depth, 31n, 32n, F.g_depth(~T, tag, fresh, depth, tv, tp, tn, ord, h), N.lt_succ(31n)), hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi), AS2.tsat(Maybe<&2, T>, depth, tv, U32.to_nat(i), None{}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)), F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h))

def vat_xv(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {ST.vat(T, AR.slots(Maybe<&2, T>, tv), U32.to_nat(i)) == xv(~T, tv, i) : Maybe<&2, T>}:
  Equal.cong(Maybe<&2, Maybe<&2, T>>, Maybe<&2, T>, m => ST.flat(T, m), SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, tv), U32.to_nat(i)), Some{xv(~T, tv, i)}, AS2.tsat(Maybe<&2, T>, depth, tv, U32.to_nat(i), None{}, F.g_tv(~T, tag, fresh, depth, tv, tp, tn, ord, h), hi_of(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)))

# The model's lookup of an issued handle is its value slot.
def getv_xv(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}) -> {DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i) == xv(~T, tv, i) : Maybe<&2, T>}:
  Equal.trans(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), ST.vat(T, AR.slots(Maybe<&2, T>, tv), U32.to_nat(i)), xv(~T, tv, i), K.getv_live(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi), vat_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi))

def getv_ok_false(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == False{} : Bool}) -> {DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i) == None{} : Maybe<&2, T>}:
  K.getv_dead(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, N.not_lt_le(U32.to_nat(i), fresh, Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), fresh), U32.is_lt(i, U32.from_nat(fresh)), False{}, Equal.sym(Bool, U32.is_lt(i, U32.from_nat(fresh)), Nat.is_lt(U32.to_nat(i), fresh), ok_nat(~T, tag, fresh, depth, tv, tp, tn, ord, i, h)), eok)))

def hi_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(i), fresh) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), fresh), U32.is_lt(i, U32.from_nat(fresh)), True{}, Equal.sym(Bool, U32.is_lt(i, U32.from_nat(fresh)), Nat.is_lt(U32.to_nat(i), fresh), ok_nat(~T, tag, fresh, depth, tv, tp, tn, ord, i, h)), eok)

# ---- get ----

def value_eq(~T: Data, m: Maybe<&2, T>) -> {D.value_of(~T, m) == DS.value(T, True{}, m) : Result<&2, &2, E.Error, T>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def gfin(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +r: Result<&2, &2, E.Error, T>) -> D.DList<T> & Result<&2, &2, E.Error, T>:
  (ST.real(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}), r)

def get_eq(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}, ok: Bool, +eok: {U32.is_lt(i, U32.from_nat(fresh)) == ok : Bool}, same: Bool) -> {D.get_checked(~T, ok, tag, U32.from_nat(fresh), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, same) == gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, same, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))) : D.DList<T> & Result<&2, &2, E.Error, T>}:
  match ok same:
    case True{} False{}:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      Equal.cong(Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, T>, m => gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, True{}, m)), None{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), None{}, getv_ok_false(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)))
    case True{} True{}:
      +hi = hi_ok(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, eok)
      Equal.trans(D.DList<T> & Result<&2, &2, E.Error, T>, D.get_fin(~T, tag, U32.from_nat(fresh), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i)), gfin(~T, tag, fresh, depth, tv, tp, tn, ord, D.value_of(~T, xv(~T, tv, i))), gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, True{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))),
        Equal.cong(Array<Maybe<&2, T>> & Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, T>, r => D.get_fin(~T, tag, U32.from_nat(fresh), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(U32, tp), AR.thaw(U32, tn), r), Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, tv), i), (AR.thaw(Maybe<&2, T>, tv), xv(~T, tv, i)), read_v(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)),
        Equal.trans(D.DList<T> & Result<&2, &2, E.Error, T>, gfin(~T, tag, fresh, depth, tv, tp, tn, ord, D.value_of(~T, xv(~T, tv, i))), gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, True{}, xv(~T, tv, i))), gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, True{}, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))),
          Equal.cong(Result<&2, &2, E.Error, T>, D.DList<T> & Result<&2, &2, E.Error, T>, z => gfin(~T, tag, fresh, depth, tv, tp, tn, ord, z), D.value_of(~T, xv(~T, tv, i)), DS.value(T, True{}, xv(~T, tv, i)), value_eq(~T, xv(~T, tv, i))),
          Equal.cong(Maybe<&2, T>, D.DList<T> & Result<&2, &2, E.Error, T>, m => gfin(~T, tag, fresh, depth, tv, tp, tn, ord, DS.value(T, True{}, m)), xv(~T, tv, i), DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), Equal.sym(Maybe<&2, T>, DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i), xv(~T, tv, i), getv_xv(~T, tag, fresh, depth, tv, tp, tn, ord, i, h, hi)))))

def vobs(~T: Data, r: D.DList<T> & Result<&2, &2, E.Error, T>) -> D.DList<T> & E.Obs<T>:
  D.obs_val(~T, r)

def get_ok(~T: Data, +tag: U32, +fresh: Nat, +depth: Nat, +tv: AR.Tree<Maybe<&2, T>>, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +ord: List<&2, Nat>, +l: U32, +i: U32, +h: {ST.good(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Get{E.H{l, i}}):
  +r = DS.value(T, U32.is_eq(l, tag), DS.getv(T, ST.items(T, AR.slots(Maybe<&2, T>, tv), ord), i))
  K.mk(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Get{E.H{l, i}}, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.OVal{r},
    Equal.cong(D.DList<T> & Result<&2, &2, E.Error, T>, D.DList<T> & E.Obs<T>, z => vobs(~T, z), D.get_checked(~T, U32.is_lt(i, U32.from_nat(fresh)), tag, U32.from_nat(fresh), SC.length(Nat, ord), ST.hd(ord), ST.lst(ord), depth, U.pow2u(depth), AR.thaw(Maybe<&2, T>, tv), AR.thaw(U32, tp), AR.thaw(U32, tn), i, U32.is_eq(l, tag)), gfin(~T, tag, fresh, depth, tv, tp, tn, ord, r),
      get_eq(~T, tag, fresh, depth, tv, tp, tn, ord, l, i, h, U32.is_lt(i, U32.from_nat(fresh)), {==}, U32.is_eq(l, tag))),
    h, {==}, K.same_fresh(~T, ST.Sh{tag, fresh, depth, tv, tp, tn, ord}, E.Get{E.H{l, i}}))
