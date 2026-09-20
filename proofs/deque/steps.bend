import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/deque.bend as S
import ../../src/deque.bend as DQ
import ../../types/deque.bend as E
import ../dynamic_array/layout.bend as LY
import ./layout.bend as WN
import ./state.bend as ST
import ./walk.bend as W

# One actual public operation on a good shadow's array yields the array of a
# new good shadow, and (abstract state, observation) equals the spec step.
#
# The fourth component bounds the new depth: a push doubles the block at most
# once, every other operation leaves the depth alone. That is what lets the
# trace law carry a single capacity premise for a whole operation list.

def sh_depth(-T: Data, sh: ST.Shadow<T>) -> Nat:
  match sh:
    case ST.Sh{+d, lo, n, t}:
      d

def pushcost(-T: Data, op: E.Op<T>) -> Nat:
  match op:
    case E.Length{}:
      0n
    case E.PushFront{x}:
      1n
    case E.PushBack{x}:
      1n
    case E.PopFront{}:
      0n
    case E.PopBack{}:
      0n
    case E.PeekFront{}:
      0n
    case E.PeekBack{}:
      0n
    case E.ToList{}:
      0n

def StepOK(-T: Data, sh: ST.Shadow<T>, op: E.Op<T>) -> Type:
  Sigma<&1, &1, ST.Shadow<T>, sh2 => Sigma<&1, &1, E.Obs<T>, o => {DQ.step(T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>} & ({ST.good(T, sh2) == True{} : Bool} & ({(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>} & {Nat.is_le(sh_depth(T, sh2), Nat.add(sh_depth(T, sh), pushcost(T, op))) == True{} : Bool}))>>

def mk(-T: Data, -sh: ST.Shadow<T>, -op: E.Op<T>, sh2: ST.Shadow<T>, o: E.Obs<T>, e1: {DQ.step(T, ST.real(T, sh), op) == (ST.real(T, sh2), o) : DQ.Deque<T> & E.Obs<T>}, e2: {ST.good(T, sh2) == True{} : Bool}, e3: {(ST.model(T, sh2), o) == S.step(T, ST.model(T, sh), op) : List<&2, T> & E.Obs<T>}, e4: {Nat.is_le(sh_depth(T, sh2), Nat.add(sh_depth(T, sh), pushcost(T, op))) == True{} : Bool}) -> StepOK(T, sh, op):
  (sh2, (o, (e1, (e2, (e3, e4)))))

# ---- small arithmetic and list facts ----

def item_eq(-T: Data, +m: Maybe<&2, T>) -> {DQ.item(T, m) == S.item(T, m) : Result<&2, &2, E.Error, T>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def nth0_head(-T: Data, +ys: List<&2, T>) -> {SC.nth(T, ys, 0n) == SC.head(T, ys) : Maybe<&2, T>}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, r}:
      {==}

def le_same(+d: Nat) -> {Nat.is_le(d, Nat.add(d, 0n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(d, _) == True{} : Bool}
  N.le_refl(d)

def le_succ_add(+d: Nat) -> {Nat.is_le(1n+d, Nat.add(d, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 1n), 1n+Nat.add(d, 0n), N.add_succ(d, 0n)) : {Nat.is_le(1n+d, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(1n+d, 1n+_) == True{} : Bool}
  N.le_refl(1n+d)

def dec1_lt(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(DQ.dec1(x), x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p:
      N.lt_succ(p)

def succ_dec1(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {x == 1n+DQ.dec1(x) : Nat}:
  match x:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, L.false_true(h))
    case 1n+p:
      {==}

# ---- indexed access on a good shadow ----

def cap_len(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> {SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)) == SC.pow2(d) : Nat}:
  AR.slots_length(Maybe<&2, T>, d, t, ST.g_perfect(T, d, lo, n, t, g))

def win_cap(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> {Nat.is_le(Nat.add(lo, n), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(Nat.add(lo, n), z) == True{} : Bool}, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), SC.pow2(d), cap_len(T, d, lo, n, t, g), WN.win_le(T, AR.slots(Maybe<&2, T>, t), lo, n, ST.g_win(T, d, lo, n, t, g)))

def idx_lt(+d: Nat, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(U32.from_nat(j)), SC.pow2(d)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, U.to_nat_from_nat(j, d, ST.le32(d, hd), hj)), hj)

def idx_slot(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), U32.to_nat(U32.from_nat(j))) == Some{W.slot(T, AR.slots(Maybe<&2, T>, t), j)} : Maybe<&2, Maybe<&2, T>>}:
  L.subst(Nat, z => {SC.nth(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), z) == Some{W.slot(T, AR.slots(Maybe<&2, T>, t), j)} : Maybe<&2, Maybe<&2, T>>}, j, U32.to_nat(U32.from_nat(j)), Equal.sym(Nat, U32.to_nat(U32.from_nat(j)), j, U.to_nat_from_nat(j, d, ST.le32(d, hd), hj)),
    W.nth_slot(T, AR.slots(Maybe<&2, T>, t), j, L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), Equal.sym(Nat, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, pf)), hj)))

def set_arr(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +w: Maybe<&2, T>, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j), w) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, j, w)) : Array<Maybe<&2, T>>}:
  L.subst(Nat, z => {Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j), w) == AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, z, w)) : Array<Maybe<&2, T>>}, U32.to_nat(U32.from_nat(j)), j, U.to_nat_from_nat(j, d, ST.le32(d, hd), hj),
    AR.set(Maybe<&2, T>, d, t, U32.from_nat(j), w, W.slot(T, AR.slots(Maybe<&2, T>, t), j), ST.lt32(d, hd), idx_lt(d, j, hd, hj), idx_slot(T, d, t, j, hd, hj, pf), pf))

def swap_arr(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +w: Maybe<&2, T>, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j), w) == (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, j, w)), W.slot(T, AR.slots(Maybe<&2, T>, t), j)) : Array<Maybe<&2, T>> & Maybe<&2, T>}:
  L.subst(Nat, z => {Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j), w) == (AR.thaw(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, z, w)), W.slot(T, AR.slots(Maybe<&2, T>, t), j)) : Array<Maybe<&2, T>> & Maybe<&2, T>}, U32.to_nat(U32.from_nat(j)), j, U.to_nat_from_nat(j, d, ST.le32(d, hd), hj),
    AR.swap(Maybe<&2, T>, d, t, U32.from_nat(j), w, W.slot(T, AR.slots(Maybe<&2, T>, t), j), ST.lt32(d, hd), idx_lt(d, j, hd, hj), idx_slot(T, d, t, j, hd, hj, pf), pf))

def upd_slots(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +w: Maybe<&2, T>, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {AR.slots(Maybe<&2, T>, AR.upd(Maybe<&2, T>, d, t, j, w)) == SC.update(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t), j, w) : List<&2, Maybe<&2, T>>}:
  AR.upd_slots(Maybe<&2, T>, d, t, j, w, hj, pf)

# ---- length ----

def length_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.Length{}):
  +ys = LY.somes(T, AR.slots(Maybe<&2, T>, t))
  mk(T, ST.Sh{d, lo, n, t}, E.Length{}, ST.Sh{d, lo, n, t}, E.ONat{n},
    {==},
    g,
    %Equal.sym(Nat, SC.length(T, ys), n, WN.win_len(T, AR.slots(Maybe<&2, T>, t), lo, n, ST.g_win(T, d, lo, n, t, g))) : {(ys, E.ONat{n}) == (ys, E.ONat{_}) : List<&2, T> & E.Obs<T>}
    {==},
    le_same(d))

# ---- peek_front / peek_back ----

def front_slot(-T: Data, +xs: List<&2, Maybe<&2, T>>, +lo: Nat, +m: Nat, +h: {WN.win(T, xs, lo, 1n+m) == True{} : Bool}) -> {W.slot(T, xs, lo) == SC.nth(T, LY.somes(T, xs), 0n) : Maybe<&2, T>}:
  %N.add_zero(lo) : {W.slot(T, xs, _) == SC.nth(T, LY.somes(T, xs), 0n) : Maybe<&2, T>}
  W.slot_nth(T, xs, lo, 1n+m, 0n, h, {==})

def empty_model(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, 0n, t}) == True{} : Bool}) -> {LY.somes(T, AR.slots(Maybe<&2, T>, t)) == Nil{} : List<&2, T>}:
  LL.length_zero_nil(T, LY.somes(T, AR.slots(Maybe<&2, T>, t)), WN.win_len(T, AR.slots(Maybe<&2, T>, t), lo, 0n, ST.g_win(T, d, lo, 0n, t, g)))

def lom_lt(-T: Data, +d: Nat, +lo: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, 1n+m, t}) == True{} : Bool}) -> {Nat.is_lt(Nat.add(lo, m), SC.pow2(d)) == True{} : Bool}:
  N.succ_le_lt(Nat.add(lo, m), SC.pow2(d),
    L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(lo, 1n+m), 1n+Nat.add(lo, m), N.add_succ(lo, m), win_cap(T, d, lo, 1n+m, t, g)))

def lo_lt(-T: Data, +d: Nat, +lo: Nat, +m: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, 1n+m, t}) == True{} : Bool}) -> {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}:
  N.le_lt_trans(lo, Nat.add(lo, m), SC.pow2(d), N.le_add_right(lo, m), lom_lt(T, d, lo, m, t, g))

def peek_front_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PeekFront{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      mk(T, ST.Sh{d, lo, 0n, t}, E.PeekFront{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}},
        {==},
        g,
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(LY.somes(T, ss), E.OItem{Fail{E.EmptyDeque{}}}) == (LY.somes(T, ss), E.OItem{S.item(T, SC.head(T, _))}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +x = SC.nth(T, ys, 0n)
      mk(T, ST.Sh{d, lo, 1n+m, t}, E.PeekFront{}, ST.Sh{d, lo, 1n+m, t}, E.OItem{S.item(T, x)},
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(lo)), (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, lo)), W.get_slot(T, d, t, lo, ST.g_depth(T, d, lo, 1n+m, t, g), lo_lt(T, d, lo, m, t, g), ST.g_perfect(T, d, lo, 1n+m, t, g))) : {DQ.obs_item(T, DQ.peek_fin(T, d, SC.pow2(d), lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, W.slot(T, ss, lo), x, front_slot(T, ss, lo, m, ST.g_win(T, d, lo, 1n+m, t, g))) : {DQ.obs_item(T, DQ.peek_fin(T, d, SC.pow2(d), lo, 1n+m, (AR.thaw(Maybe<&2, T>, t), _))) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DQ.item(T, x), S.item(T, x), item_eq(T, x)) : {(DQ.DQ{d, SC.pow2(d), lo, 1n+m, AR.thaw(Maybe<&2, T>, t)}, E.OItem{_}) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g,
        %nth0_head(T, ys) : {(ys, E.OItem{S.item(T, x)}) == (ys, E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))

def peek_back_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PeekBack{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      mk(T, ST.Sh{d, lo, 0n, t}, E.PeekBack{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}},
        {==},
        g,
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(LY.somes(T, ss), E.OItem{Fail{E.EmptyDeque{}}}) == (LY.somes(T, ss), E.OItem{S.item(T, SC.last(T, _))}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +x = SC.nth(T, ys, m)
      mk(T, ST.Sh{d, lo, 1n+m, t}, E.PeekBack{}, ST.Sh{d, lo, 1n+m, t}, E.OItem{S.item(T, x)},
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m))), (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, Nat.add(lo, m))), W.get_slot(T, d, t, Nat.add(lo, m), ST.g_depth(T, d, lo, 1n+m, t, g), lom_lt(T, d, lo, m, t, g), ST.g_perfect(T, d, lo, 1n+m, t, g))) : {DQ.obs_item(T, DQ.peek_fin(T, d, SC.pow2(d), lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, W.slot(T, ss, Nat.add(lo, m)), x, W.slot_nth(T, ss, lo, 1n+m, m, ST.g_win(T, d, lo, 1n+m, t, g), N.lt_succ(m))) : {DQ.obs_item(T, DQ.peek_fin(T, d, SC.pow2(d), lo, 1n+m, (AR.thaw(Maybe<&2, T>, t), _))) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DQ.item(T, x), S.item(T, x), item_eq(T, x)) : {(DQ.DQ{d, SC.pow2(d), lo, 1n+m, AR.thaw(Maybe<&2, T>, t)}, E.OItem{_}) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g,
        %LY.nth_last(T, ys, m, WN.win_len(T, ss, lo, 1n+m, ST.g_win(T, d, lo, 1n+m, t, g))) : {(ys, E.OItem{S.item(T, x)}) == (ys, E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))

# ---- pop_front / pop_back ----

def pf_spec(-T: Data, +ys: List<&2, T>, +m: Nat, +h: {SC.length(T, ys) == 1n+m : Nat}) -> {S.pop_front(T, ys) == (SC.tail(T, ys), E.OItem{S.item(T, SC.nth(T, ys, 0n))}) : List<&2, T> & E.Obs<T>}:
  match ys:
    case Nil{}:
      Empty.absurd({S.pop_front(T, Nil{}) == (Nil{}, E.OItem{S.item(T, None{})}) : List<&2, T> & E.Obs<T>}, N.zero_succ(m, h))
    case Con{y, r}:
      {==}

def pb_spec(-T: Data, +ys: List<&2, T>, +m: Nat, +h: {SC.length(T, ys) == 1n+m : Nat}) -> {S.pop_back(T, ys) == (SC.init(T, ys), E.OItem{S.item(T, SC.nth(T, ys, m))}) : List<&2, T> & E.Obs<T>}:
  match ys:
    case Nil{}:
      Empty.absurd({S.pop_back(T, Nil{}) == (Nil{}, E.OItem{S.item(T, None{})}) : List<&2, T> & E.Obs<T>}, N.zero_succ(m, h))
    case Con{+y, +r}:
      %Equal.sym(Maybe<&2, T>, SC.nth(T, Con{y, r}, m), SC.last(T, Con{y, r}), LY.nth_last(T, Con{y, r}, m, h)) : {(SC.init(T, Con{y, r}), E.OItem{S.item(T, SC.last(T, Con{y, r}))}) == (SC.init(T, Con{y, r}), E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
      {==}

def pop_front_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PopFront{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      mk(T, ST.Sh{d, lo, 0n, t}, E.PopFront{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}},
        {==},
        g,
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(LY.somes(T, ss), E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_front(T, _) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_front(T, Nil{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +x = SC.nth(T, ys, 0n)
      +hw = ST.g_win(T, d, lo, 1n+m, t, g)
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = lo_lt(T, d, lo, m, t, g)
      +t2 = AR.upd(Maybe<&2, T>, d, t, lo, None{})
      +hs = upd_slots(T, d, t, lo, None{}, hlo, pf)
      mk(T, ST.Sh{d, lo, 1n+m, t}, E.PopFront{}, ST.Sh{d, 1n+lo, m, t2}, E.OItem{S.item(T, x)},
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(lo), None{}), (AR.thaw(Maybe<&2, T>, t2), W.slot(T, ss, lo)), swap_arr(T, d, t, lo, None{}, hd, hlo, pf)) : {DQ.obs_item(T, DQ.pop_f_fin(T, d, SC.pow2(d), lo, m, _)) == (ST.real(T, ST.Sh{d, 1n+lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, W.slot(T, ss, lo), x, front_slot(T, ss, lo, m, hw)) : {DQ.obs_item(T, DQ.pop_f_fin(T, d, SC.pow2(d), lo, m, (AR.thaw(Maybe<&2, T>, t2), _))) == (ST.real(T, ST.Sh{d, 1n+lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DQ.item(T, x), S.item(T, x), item_eq(T, x)) : {(DQ.DQ{d, SC.pow2(d), 1n+lo, m, AR.thaw(Maybe<&2, T>, t2)}, E.OItem{_}) == (ST.real(T, ST.Sh{d, 1n+lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, 1n+lo, m, t2, hd, AR.upd_perfect(Maybe<&2, T>, d, t, lo, None{}, pf),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, 1n+lo, m) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, lo, None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, lo, None{}), hs), WN.win_pop_front(T, ss, lo, m, hw))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, lo, None{}), hs) : {(LY.somes(T, _), E.OItem{S.item(T, x)}) == S.pop_front(T, ys) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, lo, None{})), SC.tail(T, ys), WN.somes_pop_front(T, ss, lo, m, hw)) : {(_, E.OItem{S.item(T, x)}) == S.pop_front(T, ys) : List<&2, T> & E.Obs<T>}
        Equal.sym(List<&2, T> & E.Obs<T>, S.pop_front(T, ys), (SC.tail(T, ys), E.OItem{S.item(T, x)}), pf_spec(T, ys, m, WN.win_len(T, ss, lo, 1n+m, hw))),
        le_same(d))

def pop_back_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PopBack{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      mk(T, ST.Sh{d, lo, 0n, t}, E.PopBack{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}},
        {==},
        g,
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(LY.somes(T, ss), E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_back(T, _) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_back(T, Nil{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +x = SC.nth(T, ys, m)
      +hw = ST.g_win(T, d, lo, 1n+m, t, g)
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hj = lom_lt(T, d, lo, m, t, g)
      +t2 = AR.upd(Maybe<&2, T>, d, t, Nat.add(lo, m), None{})
      +hs = upd_slots(T, d, t, Nat.add(lo, m), None{}, hj, pf)
      mk(T, ST.Sh{d, lo, 1n+m, t}, E.PopBack{}, ST.Sh{d, lo, m, t2}, E.OItem{S.item(T, x)},
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.swap(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m)), None{}), (AR.thaw(Maybe<&2, T>, t2), W.slot(T, ss, Nat.add(lo, m))), swap_arr(T, d, t, Nat.add(lo, m), None{}, hd, hj, pf)) : {DQ.obs_item(T, DQ.pop_b_fin(T, d, SC.pow2(d), lo, m, _)) == (ST.real(T, ST.Sh{d, lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, W.slot(T, ss, Nat.add(lo, m)), x, W.slot_nth(T, ss, lo, 1n+m, m, hw, N.lt_succ(m))) : {DQ.obs_item(T, DQ.pop_b_fin(T, d, SC.pow2(d), lo, m, (AR.thaw(Maybe<&2, T>, t2), _))) == (ST.real(T, ST.Sh{d, lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Result<&2, &2, E.Error, T>, DQ.item(T, x), S.item(T, x), item_eq(T, x)) : {(DQ.DQ{d, SC.pow2(d), lo, m, AR.thaw(Maybe<&2, T>, t2)}, E.OItem{_}) == (ST.real(T, ST.Sh{d, lo, m, t2}), E.OItem{S.item(T, x)}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, lo, m, t2, hd, AR.upd_perfect(Maybe<&2, T>, d, t, Nat.add(lo, m), None{}, pf),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, lo, m) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, Nat.add(lo, m), None{}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, Nat.add(lo, m), None{}), hs), WN.win_pop_back(T, ss, lo, m, hw))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, Nat.add(lo, m), None{}), hs) : {(LY.somes(T, _), E.OItem{S.item(T, x)}) == S.pop_back(T, ys) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, Nat.add(lo, m), None{})), SC.init(T, ys), WN.somes_pop_back(T, ss, lo, m, hw)) : {(_, E.OItem{S.item(T, x)}) == S.pop_back(T, ys) : List<&2, T> & E.Obs<T>}
        Equal.sym(List<&2, T> & E.Obs<T>, S.pop_back(T, ys), (SC.init(T, ys), E.OItem{S.item(T, x)}), pb_spec(T, ys, m, WN.win_len(T, ss, lo, 1n+m, hw))),
        le_same(d))

# ---- push_back ----

def le_add1(+d: Nat) -> {Nat.is_le(d, Nat.add(d, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(d, 1n), 1n+Nat.add(d, 0n), N.add_succ(d, 0n)) : {Nat.is_le(d, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, 0n), d, N.add_zero(d)) : {Nat.is_le(d, 1n+_) == True{} : Bool}
  N.le_succ(d)

def len_bound(-T: Data, +d: Nat, +t: AR.Tree<Maybe<&2, T>>, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {AR.perfect(Maybe<&2, T>, d, t) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(d), SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), Equal.sym(Nat, SC.length(Maybe<&2, T>, AR.slots(Maybe<&2, T>, t)), SC.pow2(d), AR.slots_length(Maybe<&2, T>, d, t, pf)), hj)

def push_back_case(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +room: {Nat.is_le(1n+d, 31n) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(Nat.add(lo, n), SC.pow2(d)) == b : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PushBack{v}):
  match b:
    case True{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +hw = ST.g_win(T, d, lo, n, t, g)
      +hd = ST.g_depth(T, d, lo, n, t, g)
      +pf = ST.g_perfect(T, d, lo, n, t, g)
      +j = Nat.add(lo, n)
      +t2 = AR.upd(Maybe<&2, T>, d, t, j, Some{v})
      +hs = upd_slots(T, d, t, j, Some{v}, eb, pf)
      +hn = len_bound(T, d, t, j, eb, pf)
      mk(T, ST.Sh{d, lo, n, t}, E.PushBack{v}, ST.Sh{d, lo, 1n+n, t2}, E.OUnit{},
        %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), True{}, eb) : {(DQ.pb_room(T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) == (ST.real(T, ST.Sh{d, lo, 1n+n, t2}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(j), Some{v}), AR.thaw(Maybe<&2, T>, t2), set_arr(T, d, t, j, Some{v}, hd, eb, pf)) : {(DQ.DQ{d, SC.pow2(d), lo, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{d, lo, 1n+n, t2}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, lo, 1n+n, t2, hd, AR.upd_perfect(Maybe<&2, T>, d, t, j, Some{v}, pf),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, lo, 1n+n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, j, Some{v}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, j, Some{v}), hs), WN.win_push_back(T, ss, lo, n, v, hw, hn))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, j, Some{v}), hs) : {(LY.somes(T, _), E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, j, Some{v})), SC.snoc(T, ys, v), WN.somes_push_back(T, ss, lo, n, v, hw, hn)) : {(_, E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_add1(d))
    case False{}:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +hw = ST.g_win(T, d, lo, n, t, g)
      +hd = ST.g_depth(T, d, lo, n, t, g)
      +pf = ST.g_perfect(T, d, lo, n, t, g)
      +j = Nat.add(lo, n)
      +t2 = {AR.TNode{t, AR.trep(Maybe<&2, T>, d, None{})} : AR.Tree<Maybe<&2, T>>}
      +pf2 = ST.node_perfect(T, d, t, AR.trep(Maybe<&2, T>, d, None{}), pf, AR.trep_perfect(Maybe<&2, T>, d, None{}))
      +ss2 = AR.slots(Maybe<&2, T>, t2)
      +hj2 = N.le_lt_trans(j, SC.pow2(d), SC.pow2(1n+d), win_cap(T, d, lo, n, t, g), N.pow2_lt_succ(d))
      +t3 = AR.upd(Maybe<&2, T>, 1n+d, t2, j, Some{v})
      +hs = upd_slots(T, 1n+d, t2, j, Some{v}, hj2, pf2)
      +hw2 = L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, lo, n) == True{} : Bool}, SC.append(Maybe<&2, T>, ss, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), ss2, Equal.sym(List<&2, Maybe<&2, T>>, ss2, SC.append(Maybe<&2, T>, ss, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), ST.slots_back(T, d, t)), WN.win_grow_back(T, ss, lo, n, SC.pow2(d), hw))
      +hn2 = len_bound(T, 1n+d, t2, j, hj2, pf2)
      mk(T, ST.Sh{d, lo, n, t}, E.PushBack{v}, ST.Sh{1n+d, lo, 1n+n, t3}, E.OUnit{},
        %Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), False{}, eb) : {(DQ.pb_room(T, d, SC.pow2(d), lo, n, AR.thaw(Maybe<&2, T>, t), v, _), E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lo, 1n+n, t3}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_back(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, t2), ST.grown_back_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(j), Some{v})}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lo, 1n+n, t3}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t2), U32.from_nat(j), Some{v}), AR.thaw(Maybe<&2, T>, t3), set_arr(T, 1n+d, t2, j, Some{v}, room, hj2, pf2)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), lo, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lo, 1n+n, t3}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, 1n+d, lo, 1n+n, t3, room, AR.upd_perfect(Maybe<&2, T>, 1n+d, t2, j, Some{v}, pf2),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, lo, 1n+n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss2, j, Some{v}), AR.slots(Maybe<&2, T>, t3), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t3), SC.update(Maybe<&2, T>, ss2, j, Some{v}), hs), WN.win_push_back(T, ss2, lo, n, v, hw2, hn2))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t3), SC.update(Maybe<&2, T>, ss2, j, Some{v}), hs) : {(LY.somes(T, _), E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss2, j, Some{v})), SC.snoc(T, LY.somes(T, ss2), v), WN.somes_push_back(T, ss2, lo, n, v, hw2, hn2)) : {(_, E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, Maybe<&2, T>>, ss2, SC.append(Maybe<&2, T>, ss, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{})), ST.slots_back(T, d, t)) : {(SC.snoc(T, LY.somes(T, _), v), E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.append(Maybe<&2, T>, ss, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}))), ys, LY.somes_grow(T, ss, SC.pow2(d))) : {(SC.snoc(T, _, v), E.OUnit{}) == (SC.snoc(T, ys, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_succ_add(d))

def push_back_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +room: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PushBack{v}):
  push_back_case(T, d, lo, n, t, v, g, room, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), {==})

# ---- push_front ----

def push_front_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +room: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.PushFront{v}):
  match lo:
    case 1n+ +k:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +hw = ST.g_win(T, d, 1n+k, n, t, g)
      +hd = ST.g_depth(T, d, 1n+k, n, t, g)
      +pf = ST.g_perfect(T, d, 1n+k, n, t, g)
      +hk = N.lt_le_trans(k, SC.pow2(d), SC.pow2(d), N.succ_le_lt(k, SC.pow2(d), N.le_trans(1n+k, Nat.add(1n+k, n), SC.pow2(d), N.le_add_right(1n+k, n), win_cap(T, d, 1n+k, n, t, g))), N.le_refl(SC.pow2(d)))
      +t2 = AR.upd(Maybe<&2, T>, d, t, k, Some{v})
      +hs = upd_slots(T, d, t, k, Some{v}, hk, pf)
      mk(T, ST.Sh{d, 1n+k, n, t}, E.PushFront{v}, ST.Sh{d, k, 1n+n, t2}, E.OUnit{},
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(k), Some{v}), AR.thaw(Maybe<&2, T>, t2), set_arr(T, d, t, k, Some{v}, hd, hk, pf)) : {(DQ.DQ{d, SC.pow2(d), k, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{d, k, 1n+n, t2}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, k, 1n+n, t2, hd, AR.upd_perfect(Maybe<&2, T>, d, t, k, Some{v}, pf),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, k, 1n+n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss, k, Some{v}), AR.slots(Maybe<&2, T>, t2), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, k, Some{v}), hs), WN.win_push_front(T, ss, k, n, v, hw))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t2), SC.update(Maybe<&2, T>, ss, k, Some{v}), hs) : {(LY.somes(T, _), E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss, k, Some{v})), Con{v, ys}, WN.somes_push_front(T, ss, k, n, v, hw)) : {(_, E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_add1(d))
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +hw = ST.g_win(T, d, 0n, n, t, g)
      +hd = ST.g_depth(T, d, 0n, n, t, g)
      +pf = ST.g_perfect(T, d, 0n, n, t, g)
      +t2 = {AR.TNode{AR.trep(Maybe<&2, T>, d, None{}), t} : AR.Tree<Maybe<&2, T>>}
      +pf2 = ST.node_perfect(T, d, AR.trep(Maybe<&2, T>, d, None{}), t, AR.trep_perfect(Maybe<&2, T>, d, None{}), pf)
      +ss2 = AR.slots(Maybe<&2, T>, t2)
      +j = DQ.dec1(SC.pow2(d))
      +hj = N.lt_le_trans(j, SC.pow2(d), SC.pow2(1n+d), dec1_lt(SC.pow2(d), N.pow2_pos(d)), N.lt_le(SC.pow2(d), SC.pow2(1n+d), N.pow2_lt_succ(d)))
      +t3 = AR.upd(Maybe<&2, T>, 1n+d, t2, j, Some{v})
      +hs = upd_slots(T, 1n+d, t2, j, Some{v}, hj, pf2)
      +hpad = L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, SC.pow2(d), n) == True{} : Bool}, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), ss), ss2, Equal.sym(List<&2, Maybe<&2, T>>, ss2, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), ss), ST.slots_front(T, d, t)), WN.win_pad_front(T, ss, n, SC.pow2(d), hw))
      +hw2 = L.subst(Nat, z => {WN.win(T, ss2, z, n) == True{} : Bool}, SC.pow2(d), 1n+j, succ_dec1(SC.pow2(d), N.pow2_pos(d)), hpad)
      mk(T, ST.Sh{d, 0n, n, t}, E.PushFront{v}, ST.Sh{1n+d, j, 1n+n, t3}, E.OUnit{},
        %Equal.sym(Array<Maybe<&2, T>>, DQ.grown_front(T, d, AR.thaw(Maybe<&2, T>, t)), AR.thaw(Maybe<&2, T>, t2), ST.grown_front_eq(T, d, t)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), j, 1n+n, Array.set(Maybe<&2, T>, _, U32.from_nat(j), Some{v})}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, j, 1n+n, t3}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>>, Array.set(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t2), U32.from_nat(j), Some{v}), AR.thaw(Maybe<&2, T>, t3), set_arr(T, 1n+d, t2, j, Some{v}, room, hj, pf2)) : {(DQ.DQ{1n+d, Nat.double(SC.pow2(d)), j, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, j, 1n+n, t3}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, 1n+d, j, 1n+n, t3, room, AR.upd_perfect(Maybe<&2, T>, 1n+d, t2, j, Some{v}, pf2),
          L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, j, 1n+n) == True{} : Bool}, SC.update(Maybe<&2, T>, ss2, j, Some{v}), AR.slots(Maybe<&2, T>, t3), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t3), SC.update(Maybe<&2, T>, ss2, j, Some{v}), hs), WN.win_push_front(T, ss2, j, n, v, hw2))),
        %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, t3), SC.update(Maybe<&2, T>, ss2, j, Some{v}), hs) : {(LY.somes(T, _), E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.update(Maybe<&2, T>, ss2, j, Some{v})), Con{v, LY.somes(T, ss2)}, WN.somes_push_front(T, ss2, j, n, v, hw2)) : {(_, E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, Maybe<&2, T>>, ss2, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), ss), ST.slots_front(T, d, t)) : {(Con{v, LY.somes(T, _)}, E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, LY.somes(T, SC.append(Maybe<&2, T>, SC.replicate(Maybe<&2, T>, SC.pow2(d), None{}), ss)), ys, WN.somes_pad_front(T, ss, SC.pow2(d))) : {(Con{v, _}, E.OUnit{}) == (Con{v, ys}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
        {==},
        le_succ_add(d))

# ---- to_list ----

def to_list_ok(-T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<Maybe<&2, T>>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> StepOK(T, ST.Sh{d, lo, n, t}, E.ToList{}):
  match n:
    case 0n:
      +ss = AR.slots(Maybe<&2, T>, t)
      mk(T, ST.Sh{d, lo, 0n, t}, E.ToList{}, ST.Sh{d, lo, 0n, t}, E.OList{Nil{}},
        {==},
        g,
        %Equal.sym(List<&2, T>, LY.somes(T, ss), Nil{}, empty_model(T, d, lo, t, g)) : {(LY.somes(T, ss), E.OList{Nil{}}) == (LY.somes(T, ss), E.OList{_}) : List<&2, T> & E.Obs<T>}
        {==},
        le_same(d))
    case 1n+ +m:
      +ss = AR.slots(Maybe<&2, T>, t)
      +ys = LY.somes(T, ss)
      +hw = ST.g_win(T, d, lo, 1n+m, t, g)
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hj = lom_lt(T, d, lo, m, t, g)
      mk(T, ST.Sh{d, lo, 1n+m, t}, E.ToList{}, ST.Sh{d, lo, 1n+m, t}, E.OList{ys},
        %Equal.sym(Array<Maybe<&2, T>> & Maybe<&2, T>, Array.get(Maybe<&2, T>, AR.thaw(Maybe<&2, T>, t), U32.from_nat(Nat.add(lo, m))), (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, Nat.add(lo, m))), W.get_slot(T, d, t, Nat.add(lo, m), hd, hj, pf)) : {DQ.obs_list(T, DQ.tl_done(T, d, SC.pow2(d), lo, 1n+m, DQ.tl_go(1n+m, T, lo, Nil{}, _))) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{ys}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<Maybe<&2, T>> & List<&2, T>, DQ.tl_go(1n+m, T, lo, Nil{}, (AR.thaw(Maybe<&2, T>, t), W.slot(T, ss, Nat.add(lo, m)))), (AR.thaw(Maybe<&2, T>, t), W.tvals(1n+m, T, ss, lo, Nil{})), W.tl_thaw(1n+m, T, d, t, lo, Nil{}, hd, hj, pf)) : {DQ.obs_list(T, DQ.tl_done(T, d, SC.pow2(d), lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{ys}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, W.tvals(1n+m, T, ss, lo, Nil{}), ys, W.tvals_model(T, ss, lo, 1n+m, hw)) : {(DQ.DQ{d, SC.pow2(d), lo, 1n+m, AR.thaw(Maybe<&2, T>, t)}, E.OList{_}) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{ys}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g,
        {==},
        le_same(d))

# ---- every operation ----
#
# `room` is the capacity condition of the representation for this step: a
# push doubles the block at most once, so the depth after it is still below
# 32 and every slot index stays a representable U32. It is the only premise
# besides the invariant, and it is discharged for a whole operation list by
# proofs/deque/trace.bend.

def step_ok(-T: Data, +sh: ST.Shadow<T>, op: E.Op<T>, +g: {ST.good(T, sh) == True{} : Bool}, +room: {Nat.is_le(Nat.add(sh_depth(T, sh), pushcost(T, op)), 31n) == True{} : Bool}) -> StepOK(T, sh, op):
  match sh op:
    case ST.Sh{+d, +lo, +n, +t} E.Length{}:
      length_ok(T, d, lo, n, t, g)
    case ST.Sh{+d, +lo, +n, +t} E.PushFront{+v}:
      push_front_ok(T, d, lo, n, t, v, g, N.le_trans(1n+d, Nat.add(d, 1n), 31n, le_succ_add(d), room))
    case ST.Sh{+d, +lo, +n, +t} E.PushBack{+v}:
      push_back_ok(T, d, lo, n, t, v, g, N.le_trans(1n+d, Nat.add(d, 1n), 31n, le_succ_add(d), room))
    case ST.Sh{+d, +lo, +n, +t} E.PopFront{}:
      pop_front_ok(T, d, lo, n, t, g)
    case ST.Sh{+d, +lo, +n, +t} E.PopBack{}:
      pop_back_ok(T, d, lo, n, t, g)
    case ST.Sh{+d, +lo, +n, +t} E.PeekFront{}:
      peek_front_ok(T, d, lo, n, t, g)
    case ST.Sh{+d, +lo, +n, +t} E.PeekBack{}:
      peek_back_ok(T, d, lo, n, t, g)
    case ST.Sh{+d, +lo, +n, +t} E.ToList{}:
      to_list_ok(T, d, lo, n, t, g)
