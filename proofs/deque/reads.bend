import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../spec/deque.bend as S
import ../../src/deque.bend as DQ
import ../../types/deque.bend as E
import ./ring.bend as R
import ./state.bend as ST
import ./stepok.bend as K

# length, peek_front, peek_back, pop_front, pop_back and to_list on a good
# ring Sh{d, lo, n, t}: each is the spec step on take(rot(slots, lo), n).

def rr(-T: Data, +t: AR.Tree<T>, +lo: Nat) -> List<&2, T>:
  R.rot(T, AR.slots(T, t), lo)

def length_ok(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.Length{}):
  K.mk(~T, ST.Sh{d, lo, n, t}, E.Length{}, ST.Sh{d, lo, n, t}, E.ONat{n}, {==}, g,
    Equal.cong(Nat, List<&2, T> & E.Obs<T>, z => (ST.model(T, ST.Sh{d, lo, n, t}), E.ONat{z}), n, SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), Equal.sym(Nat, SC.length(T, ST.model(T, ST.Sh{d, lo, n, t})), n, K.mlen(T, d, lo, n, t, g))))

# the spec step on an empty model
def empty_model(-T: Data, +t: AR.Tree<T>, +lo: Nat) -> {SC.take(T, rr(T, t, lo), 0n) == Nil{} : List<&2, T>}:
  LL.sc_take_zero(T, rr(T, t, lo))

def peekf_ok(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PeekFront{}):
  match n:
    case 0n:
      K.mk(~T, ST.Sh{d, lo, 0n, t}, E.PeekFront{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, g,
        %Equal.sym(List<&2, T>, SC.take(T, rr(T, t, lo), 0n), Nil{}, empty_model(T, t, lo)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == (_, E.OItem{S.item(T, SC.head(T, _))}) : List<&2, T> & E.Obs<T>}
        {==})
    case 1n+ +m:
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = ST.g_lo(T, d, lo, 1n+m, t, g)
      +x = ST.vat(T, t, lo)
      K.mk(~T, ST.Sh{d, lo, 1n+m, t}, E.PeekFront{}, ST.Sh{d, lo, 1n+m, t}, E.OItem{Done{x}},
        %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(lo)), (AR.thaw(T, t), x), ST.get_at(T, d, t, lo, hd, pf, hlo)) : {DQ.obs_item(~T, DQ.peek_fin(~T, d, SC.pow2(d), lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{Done{x}}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g,
        %Equal.sym(Maybe<&2, T>, SC.head(T, SC.take(T, rr(T, t, lo), 1n+m)), Some{x}, K.head_take(T, rr(T, t, lo), m, x, K.r0(T, d, lo, 1n+m, t, g))) : {(SC.take(T, rr(T, t, lo), 1n+m), E.OItem{Done{x}}) == (SC.take(T, rr(T, t, lo), 1n+m), E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
        {==})

# the slot of ring position m < 2^d
def wm_lt(+d: Nat, +lo: Nat, +m: Nat, +hlo: {Nat.is_lt(lo, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(m, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(DQ.wrap(Nat.add(lo, m), SC.pow2(d)), SC.pow2(d)) == True{} : Bool}:
  R.wrap_lt(Nat.add(lo, m), SC.pow2(d), R.two_lt(lo, m, SC.pow2(d), hlo, hm))

# the last of the first 1 + m ring positions
def last_ring(-T: Data, +d: Nat, +lo: Nat, +m: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, 1n+m, t}) == True{} : Bool}) -> {SC.last(T, SC.take(T, rr(T, t, lo), 1n+m)) == Some{ST.vat(T, t, DQ.wrap(Nat.add(lo, m), SC.pow2(d)))} : Maybe<&2, T>}:
  +r = rr(T, t, lo)
  +hn = ST.g_n(T, d, lo, 1n+m, t, g)
  +hl = L.subst(Nat, z => {Nat.is_le(1n+m, z) == True{} : Bool}, SC.pow2(d), SC.length(T, r), Equal.sym(Nat, SC.length(T, r), SC.pow2(d), K.rlen(T, d, lo, 1n+m, t, g)), hn)
  +e1 = R.last_nth(T, m, SC.take(T, r, 1n+m), LL.sc_length_take(T, r, 1n+m, hl))
  +e2 = LL.sc_nth_take(T, r, 1n+m, m, N.lt_succ(m))
  +e3 = K.rat(T, d, lo, 1n+m, t, m, g, N.succ_le_lt(m, SC.pow2(d), hn))
  Equal.trans(Maybe<&2, T>, SC.last(T, SC.take(T, r, 1n+m)), SC.nth(T, SC.take(T, r, 1n+m), m), Some{ST.vat(T, t, DQ.wrap(Nat.add(lo, m), SC.pow2(d)))}, e1, Equal.trans(Maybe<&2, T>, SC.nth(T, SC.take(T, r, 1n+m), m), SC.nth(T, r, m), Some{ST.vat(T, t, DQ.wrap(Nat.add(lo, m), SC.pow2(d)))}, e2, e3))

def peekb_ok(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PeekBack{}):
  match n:
    case 0n:
      K.mk(~T, ST.Sh{d, lo, 0n, t}, E.PeekBack{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, g,
        %Equal.sym(List<&2, T>, SC.take(T, rr(T, t, lo), 0n), Nil{}, empty_model(T, t, lo)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == (_, E.OItem{S.item(T, SC.last(T, _))}) : List<&2, T> & E.Obs<T>}
        {==})
    case 1n+ +m:
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = ST.g_lo(T, d, lo, 1n+m, t, g)
      +w = DQ.wrap(Nat.add(lo, m), SC.pow2(d))
      +hw = wm_lt(d, lo, m, hlo, N.le_trans(m, 1n+m, SC.pow2(d), N.le_succ(m), ST.g_n(T, d, lo, 1n+m, t, g)))
      +x = ST.vat(T, t, w)
      K.mk(~T, ST.Sh{d, lo, 1n+m, t}, E.PeekBack{}, ST.Sh{d, lo, 1n+m, t}, E.OItem{Done{x}},
        %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(w)), (AR.thaw(T, t), x), ST.get_at(T, d, t, w, hd, pf, hw)) : {DQ.obs_item(~T, DQ.peek_fin(~T, d, SC.pow2(d), lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OItem{Done{x}}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g,
        %Equal.sym(Maybe<&2, T>, SC.last(T, SC.take(T, rr(T, t, lo), 1n+m)), Some{x}, last_ring(T, d, lo, m, t, g)) : {(SC.take(T, rr(T, t, lo), 1n+m), E.OItem{Done{x}}) == (SC.take(T, rr(T, t, lo), 1n+m), E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
        {==})

def len_tail(-T: Data, +r: List<&2, T>, +x: T, +e: {SC.nth(T, r, 0n) == Some{x} : Maybe<&2, T>}) -> {SC.length(T, r) == 1n+SC.length(T, SC.tail(T, r)) : Nat}:
  match r:
    case Nil{}:
      Empty.absurd({SC.length(T, Nil{}) == 1n+SC.length(T, SC.tail(T, Nil{})) : Nat}, L.none_some(T, x, e))
    case Con{y, t0}:
      {==}

def popb_ok(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PopBack{}):
  match n:
    case 0n:
      K.mk(~T, ST.Sh{d, lo, 0n, t}, E.PopBack{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, g,
        %Equal.sym(List<&2, T>, SC.take(T, rr(T, t, lo), 0n), Nil{}, empty_model(T, t, lo)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_back(T, _) : List<&2, T> & E.Obs<T>}
        {==})
    case 1n+ +m:
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = ST.g_lo(T, d, lo, 1n+m, t, g)
      +hn = ST.g_n(T, d, lo, 1n+m, t, g)
      +hm = N.le_trans(m, 1n+m, SC.pow2(d), N.le_succ(m), hn)
      +w = DQ.wrap(Nat.add(lo, m), SC.pow2(d))
      +x = ST.vat(T, t, w)
      +r = rr(T, t, lo)
      +hl = L.subst(Nat, z => {Nat.is_le(1n+m, z) == True{} : Bool}, SC.pow2(d), SC.length(T, r), Equal.sym(Nat, SC.length(T, r), SC.pow2(d), K.rlen(T, d, lo, 1n+m, t, g)), hn)
      K.mk(~T, ST.Sh{d, lo, 1n+m, t}, E.PopBack{}, ST.Sh{d, lo, m, t}, E.OItem{Done{x}},
        %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(w)), (AR.thaw(T, t), x), ST.get_at(T, d, t, w, hd, pf, wm_lt(d, lo, m, hlo, hm))) : {DQ.obs_item(~T, DQ.popb_fin(~T, d, SC.pow2(d), lo, m, _)) == (ST.real(T, ST.Sh{d, lo, m, t}), E.OItem{Done{x}}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, lo, m, t, hd, pf, hlo, hm),
        %Equal.sym(List<&2, T> & E.Obs<T>, S.pop_back(T, SC.take(T, r, 1n+m)), (SC.init(T, SC.take(T, r, 1n+m)), E.OItem{S.item(T, SC.last(T, SC.take(T, r, 1n+m)))}), K.pb_spec(T, SC.take(T, r, 1n+m), m, LL.sc_length_take(T, r, 1n+m, hl))) : {(SC.take(T, r, m), E.OItem{Done{x}}) == _ : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, SC.init(T, SC.take(T, r, 1n+m)), SC.take(T, r, m), R.init_take(T, m, r, hl)) : {(SC.take(T, r, m), E.OItem{Done{x}}) == (_, E.OItem{S.item(T, SC.last(T, SC.take(T, r, 1n+m)))}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(Maybe<&2, T>, SC.last(T, SC.take(T, r, 1n+m)), Some{x}, last_ring(T, d, lo, m, t, g)) : {(SC.take(T, r, m), E.OItem{Done{x}}) == (SC.take(T, r, m), E.OItem{S.item(T, _)}) : List<&2, T> & E.Obs<T>}
        {==})

def succ_2c(+lo: Nat, +c: Nat, +hlo: {Nat.is_lt(lo, c) == True{} : Bool}, +hc: {Nat.is_le(1n, c) == True{} : Bool}) -> {Nat.is_lt(1n+lo, Nat.add(c, c)) == True{} : Bool}:
  +e = Equal.trans(Nat, Nat.add(lo, 1n), 1n+Nat.add(lo, 0n), 1n+lo, N.add_succ(lo, 0n), N.succ_cong(Nat.add(lo, 0n), lo, N.add_zero(lo)))
  L.subst(Nat, z => {Nat.is_lt(z, Nat.add(c, c)) == True{} : Bool}, Nat.add(lo, 1n), 1n+lo, e, R.two_lt(lo, 1n, c, hlo, hc))

def popf_ok(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PopFront{}):
  match n:
    case 0n:
      K.mk(~T, ST.Sh{d, lo, 0n, t}, E.PopFront{}, ST.Sh{d, lo, 0n, t}, E.OItem{Fail{E.EmptyDeque{}}}, {==}, g,
        %Equal.sym(List<&2, T>, SC.take(T, rr(T, t, lo), 0n), Nil{}, empty_model(T, t, lo)) : {(_, E.OItem{Fail{E.EmptyDeque{}}}) == S.pop_front(T, _) : List<&2, T> & E.Obs<T>}
        {==})
    case 1n+ +m:
      +c = SC.pow2(d)
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = ST.g_lo(T, d, lo, 1n+m, t, g)
      +hn = ST.g_n(T, d, lo, 1n+m, t, g)
      +hm = N.le_trans(m, 1n+m, c, N.le_succ(m), hn)
      +x = ST.vat(T, t, lo)
      +s = AR.slots(T, t)
      +r = rr(T, t, lo)
      +w1 = DQ.wrap(1n+lo, c)
      +el = ST.g_len(T, d, lo, 1n+m, t, g)
      +hlo2 = L.subst(Nat, z => {Nat.is_lt(lo, z) == True{} : Bool}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hlo)
      +ers = L.subst(Nat, z => {R.rot(T, s, DQ.wrap(1n+lo, z)) == SC.snoc(T, SC.tail(T, r), x) : List<&2, T>}, SC.length(T, s), c, el, R.rot_step(T, s, lo, x, ST.slot_val(T, d, t, lo, pf, hlo), hlo2))
      +er0 = K.r0(T, d, lo, 1n+m, t, g)
      +elt = Equal.trans(Nat, 1n+SC.length(T, SC.tail(T, r)), SC.length(T, r), c, Equal.sym(Nat, SC.length(T, r), 1n+SC.length(T, SC.tail(T, r)), len_tail(T, r, x, er0)), K.rlen(T, d, lo, 1n+m, t, g))
      +hmt = L.subst(Nat, z => {Nat.is_le(1n+m, z) == True{} : Bool}, c, 1n+SC.length(T, SC.tail(T, r)), Equal.sym(Nat, 1n+SC.length(T, SC.tail(T, r)), c, elt), hn)
      +e0 = Equal.trans(Maybe<&2, T>, SC.nth(T, SC.take(T, r, 1n+m), 0n), SC.nth(T, r, 0n), Some{x}, LL.sc_nth_take(T, r, 1n+m, 0n, {==}), er0)
      K.mk(~T, ST.Sh{d, lo, 1n+m, t}, E.PopFront{}, ST.Sh{d, w1, m, t}, E.OItem{Done{x}},
        %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(lo)), (AR.thaw(T, t), x), ST.get_at(T, d, t, lo, hd, pf, hlo)) : {DQ.obs_item(~T, DQ.popf_fin(~T, d, c, lo, m, _)) == (ST.real(T, ST.Sh{d, w1, m, t}), E.OItem{Done{x}}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        ST.good_intro(T, d, w1, m, t, hd, pf, R.wrap_lt(1n+lo, c, succ_2c(lo, c, hlo, N.pow2_pos(d))), hm),
        %Equal.sym(List<&2, T> & E.Obs<T>, S.pop_front(T, SC.take(T, r, 1n+m)), (SC.tail(T, SC.take(T, r, 1n+m)), E.OItem{Done{x}}), K.pf_spec(T, SC.take(T, r, 1n+m), x, e0)) : {(SC.take(T, R.rot(T, s, w1), m), E.OItem{Done{x}}) == _ : List<&2, T> & E.Obs<T>}
        %R.take_tail(T, r, m) : {(SC.take(T, R.rot(T, s, w1), m), E.OItem{Done{x}}) == (_, E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, R.rot(T, s, w1), SC.snoc(T, SC.tail(T, r), x), ers) : {(SC.take(T, _, m), E.OItem{Done{x}}) == (SC.take(T, SC.tail(T, r), m), E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, SC.take(T, SC.snoc(T, SC.tail(T, r), x), m), SC.take(T, SC.tail(T, r), m), R.take_snoc_le(T, SC.tail(T, r), x, m, hmt)) : {(_, E.OItem{Done{x}}) == (SC.take(T, SC.tail(T, r), m), E.OItem{Done{x}}) : List<&2, T> & E.Obs<T>}
        {==})

# ---- to_list: the backward read walk ----

def tl_ok(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, k: Nat, +acc: List<&2, T>, +hk: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}) -> {DQ.tl_go(~T, k, lo, SC.pow2(d), acc, (AR.thaw(T, t), ST.vat(T, t, DQ.wrap(Nat.add(lo, k), SC.pow2(d))))) == (AR.thaw(T, t), SC.append(T, SC.take(T, rr(T, t, lo), 1n+k), acc)) : Array<T> & List<&2, T>}:
  match k:
    case 0n:
      +x0 = ST.vat(T, t, DQ.wrap(Nat.add(lo, 0n), SC.pow2(d)))
      +r = rr(T, t, lo)
      %Equal.sym(List<&2, T>, r, Con{x0, SC.tail(T, r)}, R.cons_head(T, r, x0, K.rat(T, d, lo, n, t, 0n, g, hk))) : {(AR.thaw(T, t), Con{x0, acc}) == (AR.thaw(T, t), SC.append(T, SC.take(T, _, 1n), acc)) : Array<T> & List<&2, T>}
      %Equal.sym(List<&2, T>, SC.take(T, SC.tail(T, r), 0n), Nil{}, LL.sc_take_zero(T, SC.tail(T, r))) : {(AR.thaw(T, t), Con{x0, acc}) == (AR.thaw(T, t), SC.append(T, Con{x0, _}, acc)) : Array<T> & List<&2, T>}
      {==}
    case 1n+ +p:
      +c = SC.pow2(d)
      +r = rr(T, t, lo)
      +x = ST.vat(T, t, DQ.wrap(Nat.add(lo, 1n+p), c))
      +hd = ST.g_depth(T, d, lo, n, t, g)
      +pf = ST.g_perfect(T, d, lo, n, t, g)
      +hlo = ST.g_lo(T, d, lo, n, t, g)
      +hp = N.lt_trans(p, 1n+p, c, N.lt_succ(p), hk)
      +wp = DQ.wrap(Nat.add(lo, p), c)
      %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(wp)), (AR.thaw(T, t), ST.vat(T, t, wp)), ST.get_at(T, d, t, wp, hd, pf, wm_lt(d, lo, p, hlo, N.lt_le(p, c, hp)))) : {DQ.tl_go(~T, p, lo, c, Con{x, acc}, _) == (AR.thaw(T, t), SC.append(T, SC.take(T, r, 2n+p), acc)) : Array<T> & List<&2, T>}
      %Equal.sym(List<&2, T>, SC.take(T, r, 2n+p), SC.snoc(T, SC.take(T, r, 1n+p), x), R.take_succ_snoc(T, r, 1n+p, x, K.rat(T, d, lo, n, t, 1n+p, g, hk))) : {DQ.tl_go(~T, p, lo, c, Con{x, acc}, (AR.thaw(T, t), ST.vat(T, t, wp))) == (AR.thaw(T, t), SC.append(T, _, acc)) : Array<T> & List<&2, T>}
      %Equal.sym(List<&2, T>, SC.append(T, SC.snoc(T, SC.take(T, r, 1n+p), x), acc), SC.append(T, SC.take(T, r, 1n+p), Con{x, acc}), LL.snoc_append_cons(T, SC.take(T, r, 1n+p), x, acc)) : {DQ.tl_go(~T, p, lo, c, Con{x, acc}, (AR.thaw(T, t), ST.vat(T, t, wp))) == (AR.thaw(T, t), _) : Array<T> & List<&2, T>}
      tl_ok(~T, d, lo, n, t, g, p, Con{x, acc}, hp)

def tolist_ok(~T: Data, +d: Nat, +lo: Nat, n: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.ToList{}):
  match n:
    case 0n:
      K.mk(~T, ST.Sh{d, lo, 0n, t}, E.ToList{}, ST.Sh{d, lo, 0n, t}, E.OList{Nil{}}, {==}, g,
        %Equal.sym(List<&2, T>, SC.take(T, rr(T, t, lo), 0n), Nil{}, empty_model(T, t, lo)) : {(_, E.OList{Nil{}}) == (_, E.OList{_}) : List<&2, T> & E.Obs<T>}
        {==})
    case 1n+ +m:
      +c = SC.pow2(d)
      +hd = ST.g_depth(T, d, lo, 1n+m, t, g)
      +pf = ST.g_perfect(T, d, lo, 1n+m, t, g)
      +hlo = ST.g_lo(T, d, lo, 1n+m, t, g)
      +hn = ST.g_n(T, d, lo, 1n+m, t, g)
      +hmc = N.succ_le_lt(m, c, hn)
      +wm = DQ.wrap(Nat.add(lo, m), c)
      +xs = SC.take(T, rr(T, t, lo), 1n+m)
      K.mk(~T, ST.Sh{d, lo, 1n+m, t}, E.ToList{}, ST.Sh{d, lo, 1n+m, t}, E.OList{xs},
        %Equal.sym(Array<T> & T, Array.get(T, AR.thaw(T, t), U32.from_nat(wm)), (AR.thaw(T, t), ST.vat(T, t, wm)), ST.get_at(T, d, t, wm, hd, pf, wm_lt(d, lo, m, hlo, N.lt_le(m, c, hmc)))) : {DQ.obs_list(~T, DQ.tl_fin(~T, d, c, lo, 1n+m, DQ.tl_go(~T, m, lo, c, Nil{}, _))) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{xs}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(Array<T> & List<&2, T>, DQ.tl_go(~T, m, lo, c, Nil{}, (AR.thaw(T, t), ST.vat(T, t, wm))), (AR.thaw(T, t), SC.append(T, xs, Nil{})), tl_ok(~T, d, lo, 1n+m, t, g, m, Nil{}, hmc)) : {DQ.obs_list(~T, DQ.tl_fin(~T, d, c, lo, 1n+m, _)) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{xs}) : DQ.Deque<T> & E.Obs<T>}
        %Equal.sym(List<&2, T>, SC.append(T, xs, Nil{}), xs, LL.append_nil(T, xs)) : {(ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{_}) == (ST.real(T, ST.Sh{d, lo, 1n+m, t}), E.OList{xs}) : DQ.Deque<T> & E.Obs<T>}
        {==},
        g, {==})
