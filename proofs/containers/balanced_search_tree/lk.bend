import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ./bk.bend as BK

# An array of two halves, each the block (bk.bend) of a list with a default:
# Array.get and Array.set at a slot of the low half (index j) or of the high
# half (index 2^e + j) read and write that half's list, for blocks of depth
# e with 1 + e < 32. The TreeMap's links array is such an array.


# ---- the mirror tree of a write, by half ----

def upd_lo(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.pow2(e)) == True{} : Bool}) -> {AR.upd(T, 1n+e, AR.TNode{a, b}, j, v) == AR.TNode{AR.upd(T, e, a, j, v), b} : AR.Tree<T>}:
  %Equal.sym(Bool, Nat.is_lt(j, SC.pow2(e)), True{}, hj) : {AR.tupd(T, 1n+e, AR.TNode{a, b}, j, v, _) == AR.TNode{AR.upd(T, e, a, j, v), b} : AR.Tree<T>}
  {==}

def upd_hi(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +j: Nat, +v: T) -> {AR.upd(T, 1n+e, AR.TNode{a, b}, Nat.add(SC.pow2(e), j), v) == AR.TNode{a, AR.upd(T, e, b, j, v)} : AR.Tree<T>}:
  %Equal.sym(Bool, Nat.is_lt(Nat.add(SC.pow2(e), j), SC.pow2(e)), False{}, N.le_not_lt(Nat.add(SC.pow2(e), j), SC.pow2(e), N.le_add_right(SC.pow2(e), j))) : {AR.tupd(T, 1n+e, AR.TNode{a, b}, Nat.add(SC.pow2(e), j), v, _) == AR.TNode{a, AR.upd(T, e, b, j, v)} : AR.Tree<T>}
  %Equal.sym(Nat, Nat.sub(Nat.add(SC.pow2(e), j), SC.pow2(e)), j, N.add_sub_cancel(SC.pow2(e), j)) : {AR.TNode{a, AR.tupd(T, e, b, _, v, AR.ndec(e, _))} == AR.TNode{a, AR.upd(T, e, b, j, v)} : AR.Tree<T>}
  {==}

# ---- indices ----

def lt_lo(+e: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(e)) == True{} : Bool}) -> {Nat.is_lt(j, SC.pow2(1n+e)) == True{} : Bool}:
  N.lt_trans(j, SC.pow2(e), SC.pow2(1n+e), hj, N.pow2_lt_succ(e))

def lt_hi(+e: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(e)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(SC.pow2(e), j), SC.pow2(1n+e)) == True{} : Bool}:
  %Equal.sym(Nat, SC.pow2(1n+e), Nat.add(SC.pow2(e), SC.pow2(e)), BK.dbl(e)) : {Nat.is_lt(Nat.add(SC.pow2(e), j), _) == True{} : Bool}
  N.lt_add_left(j, SC.pow2(e), SC.pow2(e), hj)

def le33(+e: Nat, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}) -> {Nat.is_le(1n+e, 32n) == True{} : Bool}:
  N.lt_le(1n+e, 32n, he)

def slot_lo(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +j: Nat, +x: T, +pa: {AR.perfect(T, e, a) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(e)) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, a), j) == Some{x} : Maybe<&2, T>}) -> {SC.nth(T, AR.slots(T, AR.TNode{a, b}), j) == Some{x} : Maybe<&2, T>}:
  Equal.trans(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, a), AR.slots(T, b)), j), SC.nth(T, AR.slots(T, a), j), Some{x}, LL.nth_append_left(T, AR.slots(T, a), AR.slots(T, b), j, AR.len_lt(T, e, a, j, pa, hj)), hx)

def slot_hi(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +j: Nat, +x: T, +pa: {AR.perfect(T, e, a) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, b), j) == Some{x} : Maybe<&2, T>}) -> {SC.nth(T, AR.slots(T, AR.TNode{a, b}), Nat.add(SC.pow2(e), j)) == Some{x} : Maybe<&2, T>}:
  +e1 = AR.right_nth(T, e, a, b, Nat.add(SC.pow2(e), j), pa, N.le_add_right(SC.pow2(e), j))
  +e2 = L.subst(Nat, z => {SC.nth(T, SC.append(T, AR.slots(T, a), AR.slots(T, b)), Nat.add(SC.pow2(e), j)) == SC.nth(T, AR.slots(T, b), z) : Maybe<&2, T>}, Nat.sub(Nat.add(SC.pow2(e), j), SC.pow2(e)), j, N.add_sub_cancel(SC.pow2(e), j), e1)
  Equal.trans(Maybe<&2, T>, SC.nth(T, SC.append(T, AR.slots(T, a), AR.slots(T, b)), Nat.add(SC.pow2(e), j)), SC.nth(T, AR.slots(T, b), j), Some{x}, e2, hx)

# ---- Array.get / Array.set on the two-half array of perfect trees ----

# an index k below 2^(1+e) whose slot holds x
def get_at(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +pa: {AR.perfect(T, e, a) == True{} : Bool}, +pb: {AR.perfect(T, e, b) == True{} : Bool}, +k: Nat, +x: T, +hk: {Nat.is_lt(k, SC.pow2(1n+e)) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, AR.TNode{a, b}), k) == Some{x} : Maybe<&2, T>}) -> {Array.get(T, AR.thaw(T, AR.TNode{a, b}), U32.from_nat(k)) == (AR.thaw(T, AR.TNode{a, b}), x) : Array<T> & T}:
  +eu = U.to_nat_from_nat(k, 1n+e, le33(e, he), hk)
  +hxu = L.subst(Nat, z => {SC.nth(T, AR.slots(T, AR.TNode{a, b}), z) == Some{x} : Maybe<&2, T>}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hx)
  +hku = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+e)) == True{} : Bool}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hk)
  AR.get(T, 1n+e, AR.TNode{a, b}, U32.from_nat(k), x, he, hku, hxu, L.and_intro(AR.perfect(T, e, a), AR.perfect(T, e, b), pa, pb))

def set_at(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +pa: {AR.perfect(T, e, a) == True{} : Bool}, +pb: {AR.perfect(T, e, b) == True{} : Bool}, +k: Nat, +v: T, +x: T, +hk: {Nat.is_lt(k, SC.pow2(1n+e)) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, AR.TNode{a, b}), k) == Some{x} : Maybe<&2, T>}) -> {Array.set(T, AR.thaw(T, AR.TNode{a, b}), U32.from_nat(k), v) == AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{a, b}, k, v)) : Array<T>}:
  +eu = U.to_nat_from_nat(k, 1n+e, le33(e, he), hk)
  +hxu = L.subst(Nat, z => {SC.nth(T, AR.slots(T, AR.TNode{a, b}), z) == Some{x} : Maybe<&2, T>}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hx)
  +hku = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+e)) == True{} : Bool}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hk)
  L.subst(Nat, z => {Array.set(T, AR.thaw(T, AR.TNode{a, b}), U32.from_nat(k), v) == AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{a, b}, z, v)) : Array<T>}, U32.to_nat(U32.from_nat(k)), k, eu, AR.set(T, 1n+e, AR.TNode{a, b}, U32.from_nat(k), v, x, he, hku, hxu, L.and_intro(AR.perfect(T, e, a), AR.perfect(T, e, b), pa, pb)))

def swap_at(-T: Data, +e: Nat, +a: AR.Tree<T>, +b: AR.Tree<T>, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +pa: {AR.perfect(T, e, a) == True{} : Bool}, +pb: {AR.perfect(T, e, b) == True{} : Bool}, +k: Nat, +v: T, +x: T, +hk: {Nat.is_lt(k, SC.pow2(1n+e)) == True{} : Bool}, +hx: {SC.nth(T, AR.slots(T, AR.TNode{a, b}), k) == Some{x} : Maybe<&2, T>}) -> {Array.swap(T, AR.thaw(T, AR.TNode{a, b}), U32.from_nat(k), v) == (AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{a, b}, k, v)), x) : Array<T> & T}:
  +eu = U.to_nat_from_nat(k, 1n+e, le33(e, he), hk)
  +hxu = L.subst(Nat, z => {SC.nth(T, AR.slots(T, AR.TNode{a, b}), z) == Some{x} : Maybe<&2, T>}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hx)
  +hku = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+e)) == True{} : Bool}, k, U32.to_nat(U32.from_nat(k)), Equal.sym(Nat, U32.to_nat(U32.from_nat(k)), k, eu), hk)
  L.subst(Nat, z => {Array.swap(T, AR.thaw(T, AR.TNode{a, b}), U32.from_nat(k), v) == (AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{a, b}, z, v)), x) : Array<T> & T}, U32.to_nat(U32.from_nat(k)), k, eu, AR.swap(T, 1n+e, AR.TNode{a, b}, U32.from_nat(k), v, x, he, hku, hxu, L.and_intro(AR.perfect(T, e, a), AR.perfect(T, e, b), pa, pb)))

# ---- the item at an index of a list ----

def at(-T: Data, xs: List<&2, T>, +j: Nat, +dv: T) -> T:
  match xs j:
    case Nil{} _:
      dv
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      at(T, t, p, dv)

def nth_at(-T: Data, +xs: List<&2, T>, +j: Nat, +dv: T, +h: {Nat.is_lt(j, SC.length(T, xs)) == True{} : Bool}) -> {SC.nth(T, xs, j) == Some{at(T, xs, j, dv)} : Maybe<&2, T>}:
  match xs j:
    case Nil{} _:
      Empty.absurd({SC.nth(T, Nil{}, j) == Some{dv} : Maybe<&2, T>}, N.lt_zero_absurd(j, h))
    case Con{x, r} 0n:
      {==}
    case Con{x, +r} 1n+q:
      nth_at(T, r, q, dv, h)

# a slot of a block below the list's length holds the list's item
def bslot(-T: Data, +e: Nat, +fl: List<&2, T>, +dv: T, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +j: Nat, +x: T, +hx: {SC.nth(T, fl, j) == Some{x} : Maybe<&2, T>}) -> {SC.nth(T, AR.slots(T, BK.bk(T, e, fl, dv)), j) == Some{x} : Maybe<&2, T>}:
  %Equal.sym(List<&2, T>, AR.slots(T, BK.bk(T, e, fl, dv)), BK.fillv(T, SC.pow2(e), fl, dv), BK.bk_slots(T, e, fl, dv)) : {SC.nth(T, _, j) == Some{x} : Maybe<&2, T>}
  Equal.trans(Maybe<&2, T>, SC.nth(T, BK.fillv(T, SC.pow2(e), fl, dv), j), SC.nth(T, fl, j), Some{x}, BK.fill_nth(T, SC.pow2(e), fl, dv, j, LL.nth_lt_length(T, fl, j, x, hx), hf), hx)

# the slot at the list's length holds the default
def bslot_len(-T: Data, +e: Nat, +fl: List<&2, T>, +dv: T, +hn: {Nat.is_lt(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}) -> {SC.nth(T, AR.slots(T, BK.bk(T, e, fl, dv)), SC.length(T, fl)) == Some{dv} : Maybe<&2, T>}:
  %Equal.sym(List<&2, T>, AR.slots(T, BK.bk(T, e, fl, dv)), BK.fillv(T, SC.pow2(e), fl, dv), BK.bk_slots(T, e, fl, dv)) : {SC.nth(T, _, SC.length(T, fl)) == Some{dv} : Maybe<&2, T>}
  BK.fill_at_len(T, SC.pow2(e), fl, dv, hn)

def jlt(-T: Data, +e: Nat, +fl: List<&2, T>, +j: Nat, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.length(T, fl)) == True{} : Bool}) -> {Nat.is_lt(j, SC.pow2(e)) == True{} : Bool}:
  N.lt_le_trans(j, SC.length(T, fl), SC.pow2(e), hj, hf)

# ---- reads ----

def get_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j: Nat, +x: T, +hx: {SC.nth(T, fl, j) == Some{x} : Maybe<&2, T>}) -> {Array.get(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j)) == (AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), x) : Array<T> & T}:
  +hj = jlt(T, e, fl, j, hf, LL.nth_lt_length(T, fl, j, x, hx))
  get_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), j, x, lt_lo(e, j, hj), slot_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, x, BK.bk_perfect(T, e, fl, dv), hj, bslot(T, e, fl, dv, hf, j, x, hx)))

def get_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j: Nat, +x: T, +hx: {SC.nth(T, gl, j) == Some{x} : Maybe<&2, T>}) -> {Array.get(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j))) == (AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), x) : Array<T> & T}:
  +hj = jlt(T, e, gl, j, hg, LL.nth_lt_length(T, gl, j, x, hx))
  get_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), Nat.add(SC.pow2(e), j), x, lt_hi(e, j, hj), slot_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, x, BK.bk_perfect(T, e, fl, dv), bslot(T, e, gl, dv, hg, j, x, hx)))

# ---- writes below the length ----

def set_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.length(T, fl)) == True{} : Bool}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j), v) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.update(T, fl, j, v), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  +hjp = jlt(T, e, fl, j, hf, hj)
  +x = at(T, fl, j, dv)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), j, v, x, lt_lo(e, j, hjp), slot_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, x, BK.bk_perfect(T, e, fl, dv), hjp, bslot(T, e, fl, dv, hf, j, x, nth_at(T, fl, j, dv, hj))))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v), AR.TNode{AR.upd(T, e, BK.bk(T, e, fl, dv), j, v), BK.bk(T, e, gl, dv)}, AR.TNode{BK.bk(T, e, SC.update(T, fl, j, v), dv), BK.bk(T, e, gl, dv)}, upd_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, v, hjp), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{z, BK.bk(T, e, gl, dv)}, AR.upd(T, e, BK.bk(T, e, fl, dv), j, v), BK.bk(T, e, SC.update(T, fl, j, v), dv), BK.bk_set(T, e, fl, dv, j, v, hj, hf)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j), v), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v)), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.update(T, fl, j, v), dv), BK.bk(T, e, gl, dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v), AR.TNode{BK.bk(T, e, SC.update(T, fl, j, v), dv), BK.bk(T, e, gl, dv)}, e2))

def set_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.length(T, gl)) == True{} : Bool}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j)), v) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, gl, j, v), dv)}) : Array<T>}:
  +hjp = jlt(T, e, gl, j, hg, hj)
  +x = at(T, gl, j, dv)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), Nat.add(SC.pow2(e), j), v, x, lt_hi(e, j, hjp), slot_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, x, BK.bk_perfect(T, e, fl, dv), bslot(T, e, gl, dv, hg, j, x, nth_at(T, gl, j, dv, hj))))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v), AR.TNode{BK.bk(T, e, fl, dv), AR.upd(T, e, BK.bk(T, e, gl, dv), j, v)}, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, gl, j, v), dv)}, upd_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, v), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{BK.bk(T, e, fl, dv), z}, AR.upd(T, e, BK.bk(T, e, gl, dv), j, v), BK.bk(T, e, SC.update(T, gl, j, v), dv), BK.bk_set(T, e, gl, dv, j, v, hj, hg)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j)), v), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v)), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, gl, j, v), dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v), AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, gl, j, v), dv)}, e2))

# ---- a write at the length: an append ----

def push_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(SC.length(T, fl)), v) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  +j = SC.length(T, fl)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), j, v, dv, lt_lo(e, j, hn), slot_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, dv, BK.bk_perfect(T, e, fl, dv), hn, bslot_len(T, e, fl, dv, hn)))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v), AR.TNode{AR.upd(T, e, BK.bk(T, e, fl, dv), j, v), BK.bk(T, e, gl, dv)}, AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v), dv), BK.bk(T, e, gl, dv)}, upd_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, v, hn), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{z, BK.bk(T, e, gl, dv)}, AR.upd(T, e, BK.bk(T, e, fl, dv), j, v), BK.bk(T, e, SC.snoc(T, fl, v), dv), BK.bk_push(T, e, fl, dv, v, hn)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j), v), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v)), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v), dv), BK.bk(T, e, gl, dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, j, v), AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v), dv), BK.bk(T, e, gl, dv)}, e2))

def push_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +v: T, +hn: {Nat.is_lt(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), SC.length(T, gl))), v) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v), dv)}) : Array<T>}:
  +j = SC.length(T, gl)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), Nat.add(SC.pow2(e), j), v, dv, lt_hi(e, j, hn), slot_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, dv, BK.bk_perfect(T, e, fl, dv), bslot_len(T, e, gl, dv, hn)))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v), AR.TNode{BK.bk(T, e, fl, dv), AR.upd(T, e, BK.bk(T, e, gl, dv), j, v)}, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v), dv)}, upd_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), j, v), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{BK.bk(T, e, fl, dv), z}, AR.upd(T, e, BK.bk(T, e, gl, dv), j, v), BK.bk(T, e, SC.snoc(T, gl, v), dv), BK.bk_push(T, e, gl, dv, v, hn)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j)), v), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v)), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v), dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), j), v), AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v), dv)}, e2))

# ---- the last slot reset to the default: a pop ----

def mlt(-T: Data, +fl: List<&2, T>, +m: Nat, +hm: {SC.length(T, fl) == 1n+m : Nat}) -> {Nat.is_lt(m, SC.length(T, fl)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(m, z) == True{} : Bool}, 1n+m, SC.length(T, fl), Equal.sym(Nat, SC.length(T, fl), 1n+m, hm), N.lt_succ(m))

def pop_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +m: Nat, +hm: {SC.length(T, fl) == 1n+m : Nat}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(m), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.init(T, fl), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  +hj = mlt(T, fl, m, hm)
  +hjp = jlt(T, e, fl, m, hf, hj)
  +x = at(T, fl, m, dv)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), m, dv, x, lt_lo(e, m, hjp), slot_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), m, x, BK.bk_perfect(T, e, fl, dv), hjp, bslot(T, e, fl, dv, hf, m, x, nth_at(T, fl, m, dv, hj))))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, m, dv), AR.TNode{AR.upd(T, e, BK.bk(T, e, fl, dv), m, dv), BK.bk(T, e, gl, dv)}, AR.TNode{BK.bk(T, e, SC.init(T, fl), dv), BK.bk(T, e, gl, dv)}, upd_lo(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), m, dv, hjp), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{z, BK.bk(T, e, gl, dv)}, AR.upd(T, e, BK.bk(T, e, fl, dv), m, dv), BK.bk(T, e, SC.init(T, fl), dv), BK.bk_pop(T, e, fl, dv, m, hm, hf)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(m), dv), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, m, dv)), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.init(T, fl), dv), BK.bk(T, e, gl, dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, m, dv), AR.TNode{BK.bk(T, e, SC.init(T, fl), dv), BK.bk(T, e, gl, dv)}, e2))

def pop_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +m: Nat, +hm: {SC.length(T, gl) == 1n+m : Nat}) -> {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), m)), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, gl), dv)}) : Array<T>}:
  +hj = mlt(T, gl, m, hm)
  +hjp = jlt(T, e, gl, m, hg, hj)
  +x = at(T, gl, m, dv)
  +e1 = set_at(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), he, BK.bk_perfect(T, e, fl, dv), BK.bk_perfect(T, e, gl, dv), Nat.add(SC.pow2(e), m), dv, x, lt_hi(e, m, hjp), slot_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), m, x, BK.bk_perfect(T, e, fl, dv), bslot(T, e, gl, dv, hg, m, x, nth_at(T, gl, m, dv, hj))))
  +e2 = Equal.trans(AR.Tree<T>, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), m), dv), AR.TNode{BK.bk(T, e, fl, dv), AR.upd(T, e, BK.bk(T, e, gl, dv), m, dv)}, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, gl), dv)}, upd_hi(T, e, BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv), m, dv), Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{BK.bk(T, e, fl, dv), z}, AR.upd(T, e, BK.bk(T, e, gl, dv), m, dv), BK.bk(T, e, SC.init(T, gl), dv), BK.bk_pop(T, e, gl, dv, m, hm, hg)))
  Equal.trans(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), m)), dv), AR.thaw(T, AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), m), dv)), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, gl), dv)}), e1, Equal.cong(AR.Tree<T>, Array<T>, z => AR.thaw(T, z), AR.upd(T, 1n+e, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}, Nat.add(SC.pow2(e), m), dv), AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, gl), dv)}, e2))

# ---- each half doubled with a default half ----

def grow(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}) -> {ANode{ANode{AR.thaw(T, BK.bk(T, e, fl, dv)), Array.new(T, e, dv)}, ANode{AR.thaw(T, BK.bk(T, e, gl, dv)), Array.new(T, e, dv)}} == AR.thaw(T, AR.TNode{BK.bk(T, 1n+e, fl, dv), BK.bk(T, 1n+e, gl, dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.new(T, e, dv), AR.thaw(T, AR.trep(T, e, dv)), AR.new(T, e, dv)) : {ANode{ANode{AR.thaw(T, BK.bk(T, e, fl, dv)), _}, ANode{AR.thaw(T, BK.bk(T, e, gl, dv)), _}} == AR.thaw(T, AR.TNode{BK.bk(T, 1n+e, fl, dv), BK.bk(T, 1n+e, gl, dv)}) : Array<T>}
  %BK.bk_grow(T, e, fl, dv, hf) : {AR.thaw(T, AR.TNode{AR.TNode{BK.bk(T, e, fl, dv), AR.trep(T, e, dv)}, AR.TNode{BK.bk(T, e, gl, dv), AR.trep(T, e, dv)}}) == AR.thaw(T, AR.TNode{_, BK.bk(T, 1n+e, gl, dv)}) : Array<T>}
  %BK.bk_grow(T, e, gl, dv, hg) : {AR.thaw(T, AR.TNode{AR.TNode{BK.bk(T, e, fl, dv), AR.trep(T, e, dv)}, AR.TNode{BK.bk(T, e, gl, dv), AR.trep(T, e, dv)}}) == AR.thaw(T, AR.TNode{AR.TNode{BK.bk(T, e, fl, dv), AR.trep(T, e, dv)}, _}) : Array<T>}
  {==}

# ---- two writes in one half ----

def cap_upd(-T: Data, +k: Nat, +fl: List<&2, T>, +j: Nat, +v: T, +h: {Nat.is_le(SC.length(T, fl), k) == True{} : Bool}) -> {Nat.is_le(SC.length(T, SC.update(T, fl, j, v)), k) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, SC.length(T, fl), SC.length(T, SC.update(T, fl, j, v)), Equal.sym(Nat, SC.length(T, SC.update(T, fl, j, v)), SC.length(T, fl), LL.length_update(T, fl, j, v)), h)

def lt_upd(-T: Data, +i: Nat, +fl: List<&2, T>, +j: Nat, +v: T, +h: {Nat.is_lt(i, SC.length(T, fl)) == True{} : Bool}) -> {Nat.is_lt(i, SC.length(T, SC.update(T, fl, j, v))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.length(T, fl), SC.length(T, SC.update(T, fl, j, v)), Equal.sym(Nat, SC.length(T, SC.update(T, fl, j, v)), SC.length(T, fl), LL.length_update(T, fl, j, v)), h)

def set2_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j0: Nat, +v0: T, +j1: Nat, +v1: T, +h0: {Nat.is_lt(j0, SC.length(T, fl)) == True{} : Bool}, +h1: {Nat.is_lt(j1, SC.length(T, fl)) == True{} : Bool}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j0), v0), U32.from_nat(j1), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.update(T, SC.update(T, fl, j0, v0), j1, v1), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(j0), v0), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.update(T, fl, j0, v0), dv), BK.bk(T, e, gl, dv)}), set_lo(T, e, fl, gl, dv, he, hf, hg, j0, v0, h0)) : {Array.set(T, _, U32.from_nat(j1), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.update(T, SC.update(T, fl, j0, v0), j1, v1), dv), BK.bk(T, e, gl, dv)}) : Array<T>}
  set_lo(T, e, SC.update(T, fl, j0, v0), gl, dv, he, cap_upd(T, SC.pow2(e), fl, j0, v0, hf), hg, j1, v1, lt_upd(T, j1, fl, j0, v0, h1))

def set2_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +j0: Nat, +v0: T, +j1: Nat, +v1: T, +h0: {Nat.is_lt(j0, SC.length(T, gl)) == True{} : Bool}, +h1: {Nat.is_lt(j1, SC.length(T, gl)) == True{} : Bool}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j0)), v0), U32.from_nat(Nat.add(SC.pow2(e), j1)), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, SC.update(T, gl, j0, v0), j1, v1), dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), j0)), v0), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, gl, j0, v0), dv)}), set_hi(T, e, fl, gl, dv, he, hf, hg, j0, v0, h0)) : {Array.set(T, _, U32.from_nat(Nat.add(SC.pow2(e), j1)), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.update(T, SC.update(T, gl, j0, v0), j1, v1), dv)}) : Array<T>}
  set_hi(T, e, fl, SC.update(T, gl, j0, v0), dv, he, hf, cap_upd(T, SC.pow2(e), gl, j0, v0, hg), j1, v1, lt_upd(T, j1, gl, j0, v0, h1))

# ---- two appends in one half ----


def ln0(-T: Data, +k: Nat, +xl: List<&2, T>, +hn: {Nat.is_lt(1n+SC.length(T, xl), k) == True{} : Bool}) -> {Nat.is_lt(SC.length(T, xl), k) == True{} : Bool}:
  N.lt_trans(SC.length(T, xl), 1n+SC.length(T, xl), k, N.lt_succ(SC.length(T, xl)), hn)

def ln1(-T: Data, +k: Nat, +xl: List<&2, T>, +v: T, +hn: {Nat.is_lt(1n+SC.length(T, xl), k) == True{} : Bool}) -> {Nat.is_lt(SC.length(T, SC.snoc(T, xl, v)), k) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, k) == True{} : Bool}, 1n+SC.length(T, xl), SC.length(T, SC.snoc(T, xl, v)), Equal.sym(Nat, SC.length(T, SC.snoc(T, xl, v)), 1n+SC.length(T, xl), LL.length_snoc(T, xl, v)), hn)

def push2_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +v0: T, +v1: T, +hn: {Nat.is_lt(1n+SC.length(T, fl), SC.pow2(e)) == True{} : Bool}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(SC.length(T, fl)), v0), U32.from_nat(1n+SC.length(T, fl)), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, SC.snoc(T, fl, v0), v1), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(SC.length(T, fl)), v0), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v0), dv), BK.bk(T, e, gl, dv)}), push_lo(T, e, fl, gl, dv, he, hf, hg, v0, ln0(T, SC.pow2(e), fl, hn))) : {Array.set(T, _, U32.from_nat(1n+SC.length(T, fl)), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, SC.snoc(T, fl, v0), v1), dv), BK.bk(T, e, gl, dv)}) : Array<T>}
  %LL.length_snoc(T, fl, v0) : {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, fl, v0), dv), BK.bk(T, e, gl, dv)}), U32.from_nat(_), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.snoc(T, SC.snoc(T, fl, v0), v1), dv), BK.bk(T, e, gl, dv)}) : Array<T>}
  push_lo(T, e, SC.snoc(T, fl, v0), gl, dv, he, N.lt_le(SC.length(T, SC.snoc(T, fl, v0)), SC.pow2(e), ln1(T, SC.pow2(e), fl, v0, hn)), hg, v1, ln1(T, SC.pow2(e), fl, v0, hn))

def push2_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +v0: T, +v1: T, +hn: {Nat.is_lt(1n+SC.length(T, gl), SC.pow2(e)) == True{} : Bool}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), SC.length(T, gl))), v0), U32.from_nat(Nat.add(SC.pow2(e), 1n+SC.length(T, gl))), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, SC.snoc(T, gl, v0), v1), dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), SC.length(T, gl))), v0), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v0), dv)}), push_hi(T, e, fl, gl, dv, he, hf, hg, v0, ln0(T, SC.pow2(e), gl, hn))) : {Array.set(T, _, U32.from_nat(Nat.add(SC.pow2(e), 1n+SC.length(T, gl))), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, SC.snoc(T, gl, v0), v1), dv)}) : Array<T>}
  %LL.length_snoc(T, gl, v0) : {Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, gl, v0), dv)}), U32.from_nat(Nat.add(SC.pow2(e), _)), v1) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.snoc(T, SC.snoc(T, gl, v0), v1), dv)}) : Array<T>}
  push_hi(T, e, fl, SC.snoc(T, gl, v0), dv, he, hf, N.lt_le(SC.length(T, SC.snoc(T, gl, v0)), SC.pow2(e), ln1(T, SC.pow2(e), gl, v0, hn)), v1, ln1(T, SC.pow2(e), gl, v0, hn))

# ---- the last two slots of a half reset: two pops ----

def len_init(-A: Data, +xs: List<&2, A>, +m: Nat, +h: {SC.length(A, xs) == 1n+m : Nat}) -> {SC.length(A, SC.init(A, xs)) == m : Nat}:
  match xs m:
    case Nil{} _:
      Empty.absurd({SC.length(A, SC.init(A, Nil{})) == m : Nat}, N.zero_succ(m, h))
    case Con{x, Nil{}} 0n:
      {==}
    case Con{x, Nil{}} 1n+q:
      Empty.absurd({SC.length(A, SC.init(A, Con{x, Nil{}})) == 1n+q : Nat}, N.zero_succ(q, N.succ_inj(0n, 1n+q, h)))
    case Con{x, Con{y, t}} 0n:
      Empty.absurd({SC.length(A, SC.init(A, Con{x, Con{y, t}})) == 0n : Nat}, N.succ_zero(SC.length(A, t), N.succ_inj(1n+SC.length(A, t), 0n, h)))
    case Con{x, Con{+y, +t}} 1n+q:
      N.succ_cong(SC.length(A, SC.init(A, Con{y, t})), q, len_init(A, Con{y, t}, q, N.succ_inj(1n+SC.length(A, t), 1n+q, h)))

def cap_init(-T: Data, +k: Nat, +xl: List<&2, T>, +m: Nat, +hm: {SC.length(T, xl) == 1n+m : Nat}, +h: {Nat.is_le(SC.length(T, xl), k) == True{} : Bool}) -> {Nat.is_le(SC.length(T, SC.init(T, xl)), k) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(T, SC.init(T, xl)), m, len_init(T, xl, m, hm)) : {Nat.is_le(_, k) == True{} : Bool}
  N.le_trans(m, 1n+m, k, N.le_succ(m), L.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, SC.length(T, xl), 1n+m, hm, h))

def pop2_lo(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +m: Nat, +hm: {SC.length(T, fl) == 1n+(1n+m) : Nat}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(1n+m), dv), U32.from_nat(m), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.init(T, SC.init(T, fl)), dv), BK.bk(T, e, gl, dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(1n+m), dv), AR.thaw(T, AR.TNode{BK.bk(T, e, SC.init(T, fl), dv), BK.bk(T, e, gl, dv)}), pop_lo(T, e, fl, gl, dv, he, hf, hg, 1n+m, hm)) : {Array.set(T, _, U32.from_nat(m), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, SC.init(T, SC.init(T, fl)), dv), BK.bk(T, e, gl, dv)}) : Array<T>}
  pop_lo(T, e, SC.init(T, fl), gl, dv, he, cap_init(T, SC.pow2(e), fl, 1n+m, hm, hf), hg, m, len_init(T, fl, 1n+m, hm))

def pop2_hi(-T: Data, +e: Nat, +fl: List<&2, T>, +gl: List<&2, T>, +dv: T, +he: {Nat.is_lt(1n+e, 32n) == True{} : Bool}, +hf: {Nat.is_le(SC.length(T, fl), SC.pow2(e)) == True{} : Bool}, +hg: {Nat.is_le(SC.length(T, gl), SC.pow2(e)) == True{} : Bool}, +m: Nat, +hm: {SC.length(T, gl) == 1n+(1n+m) : Nat}) -> {Array.set(T, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), 1n+m)), dv), U32.from_nat(Nat.add(SC.pow2(e), m)), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, SC.init(T, gl)), dv)}) : Array<T>}:
  %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, gl, dv)}), U32.from_nat(Nat.add(SC.pow2(e), 1n+m)), dv), AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, gl), dv)}), pop_hi(T, e, fl, gl, dv, he, hf, hg, 1n+m, hm)) : {Array.set(T, _, U32.from_nat(Nat.add(SC.pow2(e), m)), dv) == AR.thaw(T, AR.TNode{BK.bk(T, e, fl, dv), BK.bk(T, e, SC.init(T, SC.init(T, gl)), dv)}) : Array<T>}
  pop_hi(T, e, fl, SC.init(T, gl), dv, he, hf, cap_init(T, SC.pow2(e), gl, 1n+m, hm, hg), m, len_init(T, gl, 1n+m, hm))
