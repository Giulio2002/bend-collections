import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../../src/containers/dynamic_array.bend as D
import ../../src/containers/types/dynamic_array.bend as DE
import ../dynamic_array/layout.bend as LY
import ../dynamic_array/state.bend as DAS
import ../dynamic_array/steps.bend as DST
import ../dynamic_array/growth.bend as DGR

# The dynamic array operations the TreeMap calls, over a good array shadow:
# the result is the realization of the updated shadow.


def item(-T: Data, m: Maybe<&2, T>) -> Result<&2, &2, DE.Error, T>:
  match m:
    case None{}:
      Fail{DE.IndexOutOfRange{}}
    case Some{x}:
      Done{x}

def gf(~T: Data, +l: Nat, +d: Nat, +c: Nat, +n: Nat, -arr: Array<Maybe<&2, T>>, +x: Maybe<&2, T>) -> {D.get_found_at(~T, l, d, c, n, (arr, x)) == (D.DA{l, d, c, n, arr}, item(T, x)) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  match x:
    case None{}:
      {==}
    case Some{v}:
      {==}

def n_len(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}) -> {SC.length(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))) == n : Nat}:
  LY.lay_len(T, AR.slots(Maybe<&2, T>, t), n, DAS.g_lay(T, l, d, n, t, g))

def nth_hi(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +h: {Nat.is_lt(i, n) == False{} : Bool}) -> {SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i) == None{} : Maybe<&2, T>}:
  LL.nth_none(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i, L.subst(Nat, z => {Nat.is_le(z, i) == True{} : Bool}, n, SC.length(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), Equal.sym(Nat, SC.length(T, LY.somes(T, AR.slots(Maybe<&2, T>, t))), n, n_len(~T, l, d, n, t, g)), N.not_lt_le(i, n, h)))

def lt_cap(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(i, n, SC.pow2(d), h, DST.n_le_cap(T, l, d, n, t, g))

def slot_at(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), i) == Some{SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i)} : Maybe<&2, Maybe<&2, T>>}:
  LY.lay_nth(T, AR.slots(Maybe<&2, T>, t), n, i, DAS.g_lay(T, l, d, n, t, g), h)

def get_c(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +b: Bool, +hb: {Nat.is_lt(i, n) == b : Bool}) -> {D.get_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, b) == (DAS.real(T, DAS.Sh{l, d, n, t}), item(T, SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  match b:
    case False{}:
      %Equal.sym(Maybe<&2, T>, SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i), None{}, nth_hi(~T, l, d, n, t, g, i, hb)) : {(D.DA{l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t)}, Fail{DE.IndexOutOfRange{}}) == (DAS.real(T, DAS.Sh{l, d, n, t}), item(T, _)) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
      {==}
    case True{}:
      +x = SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i)
      +e = AR.get(Maybe<&2, T>, d, t, U32.from_nat(i), x, DAS.lt32(d, l, DAS.g_depth(T, l, d, n, t, g), DAS.g_limit(T, l, d, n, t, g)), DST.idx_lt(T, l, d, n, t, i, g, lt_cap(~T, l, d, n, t, g, i, hb)), DST.idx_slot(T, l, d, n, t, i, x, g, lt_cap(~T, l, d, n, t, g, i, hb), slot_at(~T, l, d, n, t, g, i, hb)), DAS.g_perfect(T, l, d, n, t, g))
      %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i)), (AR.thaw(Maybe<&2, T>, t), x), e) : {D.get_found_at(~T, l, d, SC.pow2(d), n, _) == (DAS.real(T, DAS.Sh{l, d, n, t}), item(T, x)) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
      gf(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), x)

# get: the item at i, or out of range
def da_get(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat) -> {D.get_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), i) == (DAS.real(T, DAS.Sh{l, d, n, t}), item(T, SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  get_c(~T, l, d, n, t, g, i, Nat.is_lt(i, n), {==})

# set: the item at i replaced (i < n)
def da_set(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), i, v) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  +e = DST.set_arr(T, l, d, n, t, i, Some{v}, SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i), g, lt_cap(~T, l, d, n, t, g, i, h), slot_at(~T, l, d, n, t, g, i, h))
  %Equal.sym(Bool, Nat.is_lt(i, n), True{}, h) : {D.set_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), Some{v}), AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, Some{v})), e) : {(D.DA{l, d, SC.pow2(d), n, _}, Done{Unit{}}) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  {==}

def da_set_out(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, n) == False{} : Bool}) -> {D.set_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), i, v) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(i, n), False{}, h) : {D.set_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  {==}

# swap: the item at i replaced, the old one returned (i < n)
def da_swap(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), i, v) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), item(T, SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i))) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  +x = SC.nth(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), i)
  +e = DST.swap_arr(T, l, d, n, t, i, Some{v}, x, g, lt_cap(~T, l, d, n, t, g, i, h), slot_at(~T, l, d, n, t, g, i, h))
  %Equal.sym(Bool, Nat.is_lt(i, n), True{}, h) : {D.swap_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), item(T, x)) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(i), Some{v}), (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, Some{v})), x), e) : {D.get_found_at(~T, l, d, SC.pow2(d), n, _) == (DAS.real(T, DAS.Sh{l, d, n, AR.upd(Maybe<&2, T>, d, t, i, Some{v})}), item(T, x)) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  gf(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, i, Some{v})), x)

def da_swap_out(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +i: Nat, +v: T, +h: {Nat.is_lt(i, n) == False{} : Bool}) -> {D.swap_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), i, v) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}:
  %Equal.sym(Bool, Nat.is_lt(i, n), False{}, h) : {D.swap_checked_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), i, v, _) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.IndexOutOfRange{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, T>}
  {==}

def da_len(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}) -> {D.length(T, DAS.real(T, DAS.Sh{l, d, n, t})) == (DAS.real(T, DAS.Sh{l, d, n, t}), n) : D.DynArray<&2, T> & Nat}:
  {==}

def da_clear(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>) -> {D.clear_at(~T, DAS.real(T, DAS.Sh{l, d, n, t})) == DAS.real(T, DAS.Sh{l, d, 0n, AR.trep(Maybe<&2, T>, d, None{})}) : D.DynArray<&2, T>}:
  %Equal.sym(Array<Maybe<&2, T>>, Array.new(Maybe<&2, T>, d, None{}), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), AR.new(Maybe<&2, T>, d, None{})) : {D.DA{l, d, SC.pow2(d), 0n, _} == DAS.real(T, DAS.Sh{l, d, 0n, AR.trep(Maybe<&2, T>, d, None{})}) : D.DynArray<&2, T>}
  {==}

# push, with room in the block
def da_push_room(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), v) == (DAS.real(T, DAS.Sh{l, d, 1n+n, AR.upd(Maybe<&2, T>, d, t, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), True{}, hn) : {D.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l)) == (DAS.real(T, DAS.Sh{l, d, 1n+n, AR.upd(Maybe<&2, T>, d, t, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, n, Some{v})), DST.pi_arr(T, l, d, n, t, v, g, hn)) : {(D.DA{l, d, SC.pow2(d), 1n+n, _}, Done{Unit{}}) == (DAS.real(T, DAS.Sh{l, d, 1n+n, AR.upd(Maybe<&2, T>, d, t, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  {==}


# push into a full block below the limit: the block doubles
def da_push_grow(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(n, SC.pow2(d)) == False{} : Bool}, +hd: {Nat.is_lt(d, l) == True{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), v) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+n, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  +g1 = DGR.grow_good(T, l, d, n, t, g, hd)
  +hn1 = N.le_lt_trans(n, SC.pow2(d), SC.pow2(1n+d), DST.n_le_cap(T, l, d, n, t, g), N.pow2_lt_succ(d))
  %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, hn) : {D.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l)) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+n, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Bool, Nat.is_lt(d, l), True{}, hd) : {D.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+n, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, T>>, Array.new(Maybe<&2, T>, d, None{}), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, d, None{})), AR.new(Maybe<&2, T>, d, None{})) : {(D.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, Array.set(Maybe<&2, T>, ANode{AR.thaw(Maybe<&2, T>, t), _}, U32.from_nat(n), Some{v})}, Done{Unit{}}) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+n, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}), U32.from_nat(n), Some{v}), AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})), DST.pi_arr(T, l, 1n+d, n, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, v, g1, hn1)) : {(D.DA{l, 1n+d, Nat.double(SC.pow2(d)), 1n+n, _}, Done{Unit{}}) == (DAS.real(T, DAS.Sh{l, 1n+d, 1n+n, AR.upd(Maybe<&2, T>, 1n+d, AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})}, n, Some{v})}), Done{Unit{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  {==}

# push into a full block at the limit: rejected
def da_push_full(~T: Data, +l: Nat, +d: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {DAS.good(T, DAS.Sh{l, d, n, t}) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(n, SC.pow2(d)) == False{} : Bool}, +hd: {Nat.is_lt(d, l) == False{} : Bool}) -> {D.push_at(~T, DAS.real(T, DAS.Sh{l, d, n, t}), v) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.CapacityExceeded{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}:
  %Equal.sym(Bool, Nat.is_lt(n, SC.pow2(d)), False{}, hn) : {D.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, _, Nat.is_lt(d, l)) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.CapacityExceeded{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  %Equal.sym(Bool, Nat.is_lt(d, l), False{}, hd) : {D.push_room_at(~T, l, d, SC.pow2(d), n, AR.thaw(Maybe<&2, T>, t), v, False{}, _) == (DAS.real(T, DAS.Sh{l, d, n, t}), Fail{DE.CapacityExceeded{}}) : D.DynArray<&2, T> & Result<&2, &2, DE.Error, Unit>}
  {==}
