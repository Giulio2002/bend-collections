import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as DE
import ../dynamic_array/layout.bend as LY
import ../dynamic_array/state.bend as DAS
import ./mk.bend as MK
import ./da.bend as DA

# The dynamic array operations over canonical blocks of item lists.


def somes_mk(-T: Data, +d: Nat, +xs: List<&2, T>, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {LY.somes(T, AR.slots(Maybe<&2, T>, MK.mk(T, d, xs))) == xs : List<&2, T>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, MK.mk(T, d, xs)), MK.fill(T, SC.pow2(d), xs), MK.mk_slots(T, d, xs)) : {LY.somes(T, _) == xs : List<&2, T>}
  MK.fill_somes(T, SC.pow2(d), xs, hc)

def good_mk(-T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {DAS.good(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}) == True{} : Bool}:
  +hlay = L.subst(List<&2, Maybe<&2, T>>, z => {LY.lay(T, z, SC.length(T, xs)) == True{} : Bool}, MK.fill(T, SC.pow2(d), xs), AR.slots(Maybe<&2, T>, MK.mk(T, d, xs)), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, MK.mk(T, d, xs)), MK.fill(T, SC.pow2(d), xs), MK.mk_slots(T, d, xs)), MK.fill_lay(T, SC.pow2(d), xs, hc))
  DAS.good_intro(T, l, d, SC.length(T, xs), MK.mk(T, d, xs), hl, hd, MK.mk_perfect(T, d, xs), hlay)


def blk_get(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat) -> {D.get_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), DA.item(T, SC.nth(T, xs, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  %somes_mk(T, d, xs, hc) : {D.get_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), DA.item(T, SC.nth(T, _, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  DA.da_get(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), i)

def len_upd(-T: Data, +xs: List<&2, T>, +i: Nat, +v: T) -> {SC.length(T, SC.update(T, xs, i, v)) == SC.length(T, xs) : Nat}:
  LL.length_update(T, xs, i, v)

def blk_set(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, SC.update(T, xs, i, v)), MK.mk(T, d, SC.update(T, xs, i, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  +hi = L.subst(List<&2, T>, z => {Nat.is_lt(i, SC.length(T, z)) == True{} : Bool}, xs, LY.somes(T, AR.slots(Maybe<&2, T>, MK.mk(T, d, xs))), Equal.sym(List<&2, T>, LY.somes(T, AR.slots(Maybe<&2, T>, MK.mk(T, d, xs))), xs, somes_mk(T, d, xs, hc)), h)
  %Equal.sym(Nat, SC.length(T, SC.update(T, xs, i, v)), SC.length(T, xs), len_upd(T, xs, i, v)) : {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, _, MK.mk(T, d, SC.update(T, xs, i, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %MK.mk_set(T, d, xs, i, v, h, hc) : {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), _}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  DA.da_set(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), i, v, h)

def blk_set_out(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == False{} : Bool}) -> {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  DA.da_set_out(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), i, v, h)

def blk_swap(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, SC.update(T, xs, i, v)), MK.mk(T, d, SC.update(T, xs, i, v))}), DA.item(T, SC.nth(T, xs, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  %Equal.sym(Nat, SC.length(T, SC.update(T, xs, i, v)), SC.length(T, xs), len_upd(T, xs, i, v)) : {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, _, MK.mk(T, d, SC.update(T, xs, i, v))}), DA.item(T, SC.nth(T, xs, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  %MK.mk_set(T, d, xs, i, v, h, hc) : {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), _}), DA.item(T, SC.nth(T, xs, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  %somes_mk(T, d, xs, hc) : {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), AR.upd(Maybe<&2, T>, d, MK.mk(T, d, xs), i, Some{v})}), DA.item(T, SC.nth(T, _, i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  DA.da_swap(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), i, v, h)

def blk_swap_out(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == False{} : Bool}) -> {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), i, v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  DA.da_swap_out(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), i, v, h)

def len_snoc(-T: Data, +xs: List<&2, T>, +v: T) -> {SC.length(T, SC.snoc(T, xs, v)) == 1n+SC.length(T, xs) : Nat}:
  LL.length_snoc(T, xs, v)

def blk_push_room(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, SC.snoc(T, xs, v)), MK.mk(T, d, SC.snoc(T, xs, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Nat, SC.length(T, SC.snoc(T, xs, v)), 1n+SC.length(T, xs), len_snoc(T, xs, v)) : {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, d, _, MK.mk(T, d, SC.snoc(T, xs, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %MK.mk_push(T, d, xs, v, hn) : {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, d, 1n+SC.length(T, xs), _}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  DA.da_push_room(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), v, hn)

def blk_push_grow(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == False{} : Bool}, +hdl: {Nat.is_lt(d, l) == True{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, 1n+d, SC.length(T, SC.snoc(T, xs, v)), MK.mk(T, 1n+d, SC.snoc(T, xs, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  +hn1 = N.le_lt_trans(SC.length(T, xs), SC.pow2(d), SC.pow2(1n+d), hc, N.pow2_lt_succ(d))
  %Equal.sym(Nat, SC.length(T, SC.snoc(T, xs, v)), 1n+SC.length(T, xs), len_snoc(T, xs, v)) : {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, 1n+d, _, MK.mk(T, 1n+d, SC.snoc(T, xs, v))}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %MK.mk_push(T, 1n+d, xs, v, hn1) : {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+SC.length(T, xs), _}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %MK.mk_grow(T, d, xs, hc) : {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+SC.length(T, xs), AR.upd(Maybe<&2, T>, 1n+d, _, SC.length(T, xs), Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  DA.da_push_grow(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), v, hn, hdl)

def blk_push_full(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == False{} : Bool}, +hdl: {Nat.is_lt(d, l) == False{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), v) == (DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)}), Fail{DE.CapacityExceeded{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  DA.da_push_full(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc), v, hn, hdl)

def blk_clear(~T: Data, +l: Nat, +d: Nat, +xs: List<&2, T>, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +hd: {Nat.is_le(d, l) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {D.clear_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)})) == DAS.real(T, DAS.Sh{l, d, 0n, MK.mk(T, d, Nil{})}) : D.DynArray<&2, T>}:
  %MK.mk_empty(T, d) : {D.clear_at(~T, DAS.real(T, DAS.Sh{l, d, SC.length(T, xs), MK.mk(T, d, xs)})) == DAS.real(T, DAS.Sh{l, d, 0n, _}) : D.DynArray<&2, T>}
  DA.da_clear(~T, l, d, SC.length(T, xs), MK.mk(T, d, xs), good_mk(T, l, d, xs, hl, hd, hc))
