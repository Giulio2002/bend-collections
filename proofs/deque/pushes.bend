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
import ./grow.bend as G
import ./stepok.bend as K
import ./reads.bend as RD

# push_back and push_front: into free room (one slot written), onto a full
# ring (grow: the ring is copied into slots 0 .. 2^d - 1 of a block of
# 2^(d+1) slots, then the slot is written), and the first push onto the
# empty deque (the block of one slot is allocated with the element).

# ---- the list facts of a front insertion ----

# Writing v at slot lo' and moving the offset there, where lo' is the slot
# just before lo (wrap(1 + lo') = lo), puts v in front of the ring read from
# lo; with fewer than c elements the old elements follow unchanged.
def pf_model(-T: Data, +s: List<&2, T>, +lo: Nat, +lp: Nat, +n: Nat, +v: T, +x: T, +hlp: {Nat.is_lt(lp, SC.length(T, s)) == True{} : Bool}, +hw: {DQ.wrap(1n+lp, SC.length(T, s)) == lo : Nat}, +hn: {Nat.is_lt(n, SC.length(T, s)) == True{} : Bool}, +ex: {SC.nth(T, s, lp) == Some{x} : Maybe<&2, T>}) -> {SC.take(T, R.rot(T, SC.update(T, s, lp, v), lp), 1n+n) == Con{v, SC.take(T, R.rot(T, s, lo), n)} : List<&2, T>}:
  +c = SC.length(T, s)
  +rp = R.rot(T, s, lp)
  +h0 = N.le_lt_trans(0n, lp, c, N.zero_le(lp), hlp)
  +ew = K.wrap_lo(lp, c, hlp)
  +eu = L.subst(Nat, z => {R.rot(T, SC.update(T, s, z, v), lp) == SC.update(T, rp, 0n, v) : List<&2, T>}, DQ.wrap(Nat.add(lp, 0n), c), lp, ew, R.rot_update(T, s, lp, 0n, v, hlp, h0))
  +en0 = Equal.trans(Maybe<&2, T>, SC.nth(T, rp, 0n), SC.nth(T, s, DQ.wrap(Nat.add(lp, 0n), c)), Some{x}, R.rot_nth(T, s, lp, 0n, hlp, h0), L.subst(Nat, z => {SC.nth(T, s, z) == Some{x} : Maybe<&2, T>}, lp, DQ.wrap(Nat.add(lp, 0n), c), Equal.sym(Nat, DQ.wrap(Nat.add(lp, 0n), c), lp, ew), ex))
  +ech = R.cons_head(T, rp, x, en0)
  +est = L.subst(Nat, z => {R.rot(T, s, z) == SC.snoc(T, SC.tail(T, rp), x) : List<&2, T>}, DQ.wrap(1n+lp, c), lo, hw, R.rot_step(T, s, lp, x, ex, hlp))
  +elt = Equal.trans(Nat, 1n+SC.length(T, SC.tail(T, rp)), SC.length(T, rp), c, Equal.sym(Nat, SC.length(T, rp), 1n+SC.length(T, SC.tail(T, rp)), RD.len_tail(T, rp, x, en0)), R.rot_len(T, s, lp, N.lt_le(lp, c, hlp)))
  +hnt = L.subst(Nat, z => {Nat.is_le(1n+n, z) == True{} : Bool}, c, 1n+SC.length(T, SC.tail(T, rp)), Equal.sym(Nat, 1n+SC.length(T, SC.tail(T, rp)), c, elt), N.lt_succ_le_succ(n, c, hn))
  %Equal.sym(List<&2, T>, R.rot(T, SC.update(T, s, lp, v), lp), SC.update(T, rp, 0n, v), eu) : {SC.take(T, _, 1n+n) == Con{v, SC.take(T, R.rot(T, s, lo), n)} : List<&2, T>}
  %Equal.sym(List<&2, T>, rp, Con{x, SC.tail(T, rp)}, ech) : {SC.take(T, SC.update(T, _, 0n, v), 1n+n) == Con{v, SC.take(T, R.rot(T, s, lo), n)} : List<&2, T>}
  %Equal.sym(List<&2, T>, R.rot(T, s, lo), SC.snoc(T, SC.tail(T, rp), x), est) : {Con{v, SC.take(T, SC.tail(T, rp), n)} == Con{v, SC.take(T, _, n)} : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.take(T, SC.snoc(T, SC.tail(T, rp), x), n), SC.take(T, SC.tail(T, rp), n), R.take_snoc_le(T, SC.tail(T, rp), x, n, hnt)) : {Con{v, SC.take(T, SC.tail(T, rp), n)} == Con{v, _} : List<&2, T>}
  {==}

# ---- the first push onto the empty deque ----

def first_back_ok(~T: Data, +v: T) -> K.StepOK(~T, ST.S0{}, E.PushBack{v}):
  K.mk(~T, ST.S0{}, E.PushBack{v}, ST.Sh{0n, 0n, 1n, AR.trep(T, 0n, v)}, E.OUnit{},
    %Equal.sym(Array<T>, Array.new(T, 0n, v), AR.thaw(T, AR.trep(T, 0n, v)), AR.new(T, 0n, v)) : {(DQ.DQ{0n, 1n, 0n, 1n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{0n, 0n, 1n, AR.trep(T, 0n, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    {==}, {==})

def first_front_ok(~T: Data, +v: T) -> K.StepOK(~T, ST.S0{}, E.PushFront{v}):
  K.mk(~T, ST.S0{}, E.PushFront{v}, ST.Sh{0n, 0n, 1n, AR.trep(T, 0n, v)}, E.OUnit{},
    %Equal.sym(Array<T>, Array.new(T, 0n, v), AR.thaw(T, AR.trep(T, 0n, v)), AR.new(T, 0n, v)) : {(DQ.DQ{0n, 1n, 0n, 1n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{0n, 0n, 1n, AR.trep(T, 0n, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    {==}, {==})

# ---- small facts ----

def dec1_lt(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_lt(DQ.dec1(x), x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(DQ.dec1(0n), 0n) == True{} : Bool}, L.false_true(h))
    case 1n+ +p:
      N.lt_succ(p)

def succ_dec1(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {1n+DQ.dec1(x) == x : Nat}:
  match x:
    case 0n:
      Empty.absurd({1n+DQ.dec1(0n) == 0n : Nat}, L.false_true(h))
    case 1n+p:
      {==}

def wrap_self(+c: Nat) -> {DQ.wrap(c, c) == 0n : Nat}:
  Equal.trans(Nat, DQ.wrap(c, c), Nat.sub(c, c), 0n, R.wrap_big(c, c, N.lt_irrefl(c)), N.sub_self(c))

# wrap(1 + dec1(c), c) = 0: the slot before slot 0 is slot c - 1
def wrap_dec1(+c: Nat, +h: {Nat.is_le(1n, c) == True{} : Bool}) -> {DQ.wrap(1n+DQ.dec1(c), c) == 0n : Nat}:
  L.subst(Nat, z => {DQ.wrap(z, c) == 0n : Nat}, c, 1n+DQ.dec1(c), Equal.sym(Nat, 1n+DQ.dec1(c), c, succ_dec1(c, h)), wrap_self(c))

def lt_double(+c: Nat, +h: {Nat.is_le(1n, c) == True{} : Bool}) -> {Nat.is_lt(c, Nat.double(c)) == True{} : Bool}:
  N.lt_le_trans(c, 1n+c, Nat.double(c), N.lt_succ(c), N.double_succ_le(c, h))

def one_le_double(+c: Nat, +h: {Nat.is_le(1n, c) == True{} : Bool}) -> {Nat.is_le(1n, Nat.double(c)) == True{} : Bool}:
  N.le_trans(1n, c, Nat.double(c), h, N.double_self_le(c))

def zero_lt_pow2(+d: Nat) -> {Nat.is_lt(0n, SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(0n, 1n, SC.pow2(d), {==}, N.pow2_pos(d))

# ---- push into free room ----

def pb_room_ok(~T: Data, +d: Nat, +lo: Nat, +n: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hr: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PushBack{v}):
  +c = SC.pow2(d)
  +hd = ST.g_depth(T, d, lo, n, t, g)
  +pf = ST.g_perfect(T, d, lo, n, t, g)
  +hlo = ST.g_lo(T, d, lo, n, t, g)
  +s = AR.slots(T, t)
  +r = RD.rr(T, t, lo)
  +w = DQ.wrap(Nat.add(lo, n), c)
  +hw = RD.wm_lt(d, lo, n, hlo, N.lt_le(n, c, hr))
  +el = ST.g_len(T, d, lo, n, t, g)
  +hlo2 = L.subst(Nat, z => {Nat.is_lt(lo, z) == True{} : Bool}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hlo)
  +hn2 = L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hr)
  +eru = L.subst(Nat, z => {R.rot(T, SC.update(T, s, DQ.wrap(Nat.add(lo, n), z), v), lo) == SC.update(T, r, n, v) : List<&2, T>}, SC.length(T, s), c, el, R.rot_update(T, s, lo, n, v, hlo2, hn2))
  +hnr = L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, c, SC.length(T, r), Equal.sym(Nat, SC.length(T, r), c, K.rlen(T, d, lo, n, t, g)), hr)
  K.mk(~T, ST.Sh{d, lo, n, t}, E.PushBack{v}, ST.Sh{d, lo, 1n+n, AR.upd(T, d, t, w, v)}, E.OUnit{},
    %Equal.sym(Bool, Nat.is_lt(n, c), True{}, hr) : {(DQ.pb_room(~T, d, c, lo, n, AR.thaw(T, t), v, _), E.OUnit{}) == (ST.real(T, ST.Sh{d, lo, 1n+n, AR.upd(T, d, t, w, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, t), U32.from_nat(w), v), AR.thaw(T, AR.upd(T, d, t, w, v)), ST.set_at(T, d, t, w, v, hd, pf, hw)) : {(DQ.DQ{d, c, lo, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{d, lo, 1n+n, AR.upd(T, d, t, w, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    ST.good_intro(T, d, lo, 1n+n, AR.upd(T, d, t, w, v), hd, AR.upd_perfect(T, d, t, w, v, pf), hlo, N.lt_succ_le_succ(n, c, hr)),
    %Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, d, t, w, v)), SC.update(T, s, w, v), AR.upd_slots(T, d, t, w, v, hw, pf)) : {(SC.take(T, R.rot(T, _, lo), 1n+n), E.OUnit{}) == (SC.snoc(T, SC.take(T, r, n), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, R.rot(T, SC.update(T, s, w, v), lo), SC.update(T, r, n, v), eru) : {(SC.take(T, _, 1n+n), E.OUnit{}) == (SC.snoc(T, SC.take(T, r, n), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, SC.update(T, r, n, v), 1n+n), SC.snoc(T, SC.take(T, r, n), v), R.take_update_at(T, r, n, v, hnr)) : {(_, E.OUnit{}) == (SC.snoc(T, SC.take(T, r, n), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    {==})

def pf_room_core(~T: Data, +d: Nat, +lo: Nat, +lp: Nat, +n: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hr: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}, +hlp: {Nat.is_lt(lp, SC.pow2(d)) == True{} : Bool}, +hw: {DQ.wrap(1n+lp, SC.pow2(d)) == lo : Nat}, +es: {DQ.step(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushFront{v}) == (DQ.DQ{d, SC.pow2(d), lp, 1n+n, Array.set(T, AR.thaw(T, t), U32.from_nat(lp), v)}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PushFront{v}):
  +c = SC.pow2(d)
  +hd = ST.g_depth(T, d, lo, n, t, g)
  +pf = ST.g_perfect(T, d, lo, n, t, g)
  +s = AR.slots(T, t)
  +el = ST.g_len(T, d, lo, n, t, g)
  +x = ST.vat(T, t, lp)
  +hlp2 = L.subst(Nat, z => {Nat.is_lt(lp, z) == True{} : Bool}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hlp)
  +hn2 = L.subst(Nat, z => {Nat.is_lt(n, z) == True{} : Bool}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hr)
  +hw2 = L.subst(Nat, z => {DQ.wrap(1n+lp, z) == lo : Nat}, c, SC.length(T, s), Equal.sym(Nat, SC.length(T, s), c, el), hw)
  +em = pf_model(T, s, lo, lp, n, v, x, hlp2, hw2, hn2, ST.slot_val(T, d, t, lp, pf, hlp))
  K.mk(~T, ST.Sh{d, lo, n, t}, E.PushFront{v}, ST.Sh{d, lp, 1n+n, AR.upd(T, d, t, lp, v)}, E.OUnit{},
    %Equal.sym(DQ.Deque<T> & E.Obs<T>, DQ.step(~T, ST.real(T, ST.Sh{d, lo, n, t}), E.PushFront{v}), (DQ.DQ{d, c, lp, 1n+n, Array.set(T, AR.thaw(T, t), U32.from_nat(lp), v)}, E.OUnit{}), es) : {_ == (ST.real(T, ST.Sh{d, lp, 1n+n, AR.upd(T, d, t, lp, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, t), U32.from_nat(lp), v), AR.thaw(T, AR.upd(T, d, t, lp, v)), ST.set_at(T, d, t, lp, v, hd, pf, hlp)) : {(DQ.DQ{d, c, lp, 1n+n, _}, E.OUnit{}) == (ST.real(T, ST.Sh{d, lp, 1n+n, AR.upd(T, d, t, lp, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    ST.good_intro(T, d, lp, 1n+n, AR.upd(T, d, t, lp, v), hd, AR.upd_perfect(T, d, t, lp, v, pf), hlp, N.lt_succ_le_succ(n, c, hr)),
    %Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, d, t, lp, v)), SC.update(T, s, lp, v), AR.upd_slots(T, d, t, lp, v, hlp, pf)) : {(SC.take(T, R.rot(T, _, lp), 1n+n), E.OUnit{}) == (Con{v, SC.take(T, RD.rr(T, t, lo), n)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, R.rot(T, SC.update(T, s, lp, v), lp), 1n+n), Con{v, SC.take(T, R.rot(T, s, lo), n)}, em) : {(_, E.OUnit{}) == (Con{v, SC.take(T, RD.rr(T, t, lo), n)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    {==})

def pf_room_ok(~T: Data, +d: Nat, lo: Nat, +n: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, n, t}) == True{} : Bool}, +hr: {Nat.is_lt(n, SC.pow2(d)) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, n, t}, E.PushFront{v}):
  match lo:
    case 0n:
      +c = SC.pow2(d)
      +hc = N.pow2_pos(d)
      pf_room_core(~T, d, 0n, DQ.dec1(c), n, t, v, g, hr, dec1_lt(c, hc), wrap_dec1(c, hc),
        %Equal.sym(Bool, Nat.is_lt(n, c), True{}, hr) : {(DQ.pf_room(~T, d, c, 0n, n, AR.thaw(T, t), v, _), E.OUnit{}) == (DQ.DQ{d, c, DQ.dec1(c), 1n+n, Array.set(T, AR.thaw(T, t), U32.from_nat(DQ.dec1(c)), v)}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==})
    case 1n+ +k:
      +c = SC.pow2(d)
      +hlo = ST.g_lo(T, d, 1n+k, n, t, g)
      pf_room_core(~T, d, 1n+k, k, n, t, v, g, hr, N.lt_trans(k, 1n+k, c, N.lt_succ(k), hlo), R.wrap_small(1n+k, c, hlo),
        %Equal.sym(Bool, Nat.is_lt(n, c), True{}, hr) : {(DQ.pf_room(~T, d, c, 1n+k, n, AR.thaw(T, t), v, _), E.OUnit{}) == (DQ.DQ{d, c, k, 1n+n, Array.set(T, AR.thaw(T, t), U32.from_nat(k), v)}, E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
        {==})

# ---- push onto a full ring (n = 2^d): grow, then write ----

def gfacts_len(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T) -> {SC.length(T, AR.slots(T, G.gt(T, d, lo, t, v))) == Nat.double(SC.pow2(d)) : Nat}:
  AR.slots_length(T, 1n+d, G.gt(T, d, lo, t, v), G.gt_perfect(T, d, lo, t, v))

# take(slots of the grown block, c) is the old ring
def gt_take(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}) -> {SC.take(T, AR.slots(T, G.gt(T, d, lo, t, v)), SC.pow2(d)) == RD.rr(T, t, lo) : List<&2, T>}:
  +c = SC.pow2(d)
  +r = RD.rr(T, t, lo)
  +er = K.rlen(T, d, lo, c, t, g)
  %Equal.sym(List<&2, T>, AR.slots(T, G.gt(T, d, lo, t, v)), SC.append(T, r, SC.replicate(T, c, v)), G.gt_slots(T, d, lo, t, v, ST.g_perfect(T, d, lo, c, t, g), ST.g_lo(T, d, lo, c, t, g))) : {SC.take(T, _, c) == r : List<&2, T>}
  %Equal.sym(List<&2, T>, SC.take(T, SC.append(T, r, SC.replicate(T, c, v)), c), SC.take(T, r, c), LL.sc_take_append_left(T, r, SC.replicate(T, c, v), c, N.eq_le(c, SC.length(T, r), Equal.sym(Nat, SC.length(T, r), c, er)))) : {_ == r : List<&2, T>}
  L.subst(Nat, z => {SC.take(T, r, z) == r : List<&2, T>}, SC.length(T, r), c, er, R.take_len(T, r))

def model_full(-T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +g: {ST.good(T, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}) -> {SC.take(T, RD.rr(T, t, lo), SC.pow2(d)) == RD.rr(T, t, lo) : List<&2, T>}:
  L.subst(Nat, z => {SC.take(T, RD.rr(T, t, lo), z) == RD.rr(T, t, lo) : List<&2, T>}, SC.length(T, RD.rr(T, t, lo)), SC.pow2(d), K.rlen(T, d, lo, SC.pow2(d), t, g), R.take_len(T, RD.rr(T, t, lo)))

def pb_full_ok(~T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}, +hd1: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, SC.pow2(d), t}, E.PushBack{v}):
  +c = SC.pow2(d)
  +pf = ST.g_perfect(T, d, lo, c, t, g)
  +hlo = ST.g_lo(T, d, lo, c, t, g)
  +hc = N.pow2_pos(d)
  +gt = G.gt(T, d, lo, t, v)
  +pg = G.gt_perfect(T, d, lo, t, v)
  +hcc = lt_double(c, hc)
  +gs = AR.slots(T, gt)
  +r = RD.rr(T, t, lo)
  +hcg = L.subst(Nat, z => {Nat.is_lt(c, z) == True{} : Bool}, Nat.double(c), SC.length(T, gs), Equal.sym(Nat, SC.length(T, gs), Nat.double(c), gfacts_len(T, d, lo, t, v)), hcc)
  K.mk(~T, ST.Sh{d, lo, c, t}, E.PushBack{v}, ST.Sh{1n+d, 0n, 1n+c, AR.upd(T, 1n+d, gt, c, v)}, E.OUnit{},
    %Equal.sym(Bool, Nat.is_lt(c, c), False{}, N.lt_irrefl(c)) : {(DQ.pb_room(~T, d, c, lo, c, AR.thaw(T, t), v, _), E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, 0n, 1n+c, AR.upd(T, 1n+d, gt, c, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, DQ.grow(~T, d, c, lo, c, AR.thaw(T, t), v), AR.thaw(T, gt), G.grow_real(~T, d, lo, t, v, hd1, pf, hlo)) : {(DQ.DQ{1n+d, Nat.double(c), 0n, 1n+c, Array.set(T, _, U32.from_nat(c), v)}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, 0n, 1n+c, AR.upd(T, 1n+d, gt, c, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, gt), U32.from_nat(c), v), AR.thaw(T, AR.upd(T, 1n+d, gt, c, v)), ST.set_at(T, 1n+d, gt, c, v, hd1, pg, hcc)) : {(DQ.DQ{1n+d, Nat.double(c), 0n, 1n+c, _}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, 0n, 1n+c, AR.upd(T, 1n+d, gt, c, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    ST.good_intro(T, 1n+d, 0n, 1n+c, AR.upd(T, 1n+d, gt, c, v), hd1, AR.upd_perfect(T, 1n+d, gt, c, v, pg), zero_lt_pow2(1n+d), N.double_succ_le(c, hc)),
    %Equal.sym(List<&2, T>, R.rot(T, AR.slots(T, AR.upd(T, 1n+d, gt, c, v)), 0n), AR.slots(T, AR.upd(T, 1n+d, gt, c, v)), R.rot_zero(T, AR.slots(T, AR.upd(T, 1n+d, gt, c, v)))) : {(SC.take(T, _, 1n+c), E.OUnit{}) == (SC.snoc(T, SC.take(T, r, c), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, 1n+d, gt, c, v)), SC.update(T, gs, c, v), AR.upd_slots(T, 1n+d, gt, c, v, hcc, pg)) : {(SC.take(T, _, 1n+c), E.OUnit{}) == (SC.snoc(T, SC.take(T, r, c), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, SC.update(T, gs, c, v), 1n+c), SC.snoc(T, SC.take(T, gs, c), v), R.take_update_at(T, gs, c, v, hcg)) : {(_, E.OUnit{}) == (SC.snoc(T, SC.take(T, r, c), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, gs, c), r, gt_take(T, d, lo, t, v, g)) : {(SC.snoc(T, _, v), E.OUnit{}) == (SC.snoc(T, SC.take(T, r, c), v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, r, c), r, model_full(T, d, lo, t, g)) : {(SC.snoc(T, r, v), E.OUnit{}) == (SC.snoc(T, _, v), E.OUnit{}) : List<&2, T> & E.Obs<T>}
    {==})

def pf_full_ok(~T: Data, +d: Nat, +lo: Nat, +t: AR.Tree<T>, +v: T, +g: {ST.good(T, ST.Sh{d, lo, SC.pow2(d), t}) == True{} : Bool}, +hd1: {Nat.is_le(1n+d, 31n) == True{} : Bool}) -> K.StepOK(~T, ST.Sh{d, lo, SC.pow2(d), t}, E.PushFront{v}):
  +c = SC.pow2(d)
  +cc = Nat.double(c)
  +pf = ST.g_perfect(T, d, lo, c, t, g)
  +hlo = ST.g_lo(T, d, lo, c, t, g)
  +hc = N.pow2_pos(d)
  +hcc1 = one_le_double(c, hc)
  +gt = G.gt(T, d, lo, t, v)
  +pg = G.gt_perfect(T, d, lo, t, v)
  +lp = DQ.dec1(cc)
  +hlp = dec1_lt(cc, hcc1)
  +gs = AR.slots(T, gt)
  +r = RD.rr(T, t, lo)
  +egl = gfacts_len(T, d, lo, t, v)
  +hlp2 = L.subst(Nat, z => {Nat.is_lt(lp, z) == True{} : Bool}, cc, SC.length(T, gs), Equal.sym(Nat, SC.length(T, gs), cc, egl), hlp)
  +hw2 = L.subst(Nat, z => {DQ.wrap(1n+lp, z) == 0n : Nat}, cc, SC.length(T, gs), Equal.sym(Nat, SC.length(T, gs), cc, egl), wrap_dec1(cc, hcc1))
  +hcg = L.subst(Nat, z => {Nat.is_lt(c, z) == True{} : Bool}, cc, SC.length(T, gs), Equal.sym(Nat, SC.length(T, gs), cc, egl), lt_double(c, hc))
  +em = pf_model(T, gs, 0n, lp, c, v, ST.vat(T, gt, lp), hlp2, hw2, hcg, ST.slot_val(T, 1n+d, gt, lp, pg, hlp))
  K.mk(~T, ST.Sh{d, lo, c, t}, E.PushFront{v}, ST.Sh{1n+d, lp, 1n+c, AR.upd(T, 1n+d, gt, lp, v)}, E.OUnit{},
    %Equal.sym(Bool, Nat.is_lt(c, c), False{}, N.lt_irrefl(c)) : {(DQ.pf_room(~T, d, c, lo, c, AR.thaw(T, t), v, _), E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lp, 1n+c, AR.upd(T, 1n+d, gt, lp, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, DQ.grow(~T, d, c, lo, c, AR.thaw(T, t), v), AR.thaw(T, gt), G.grow_real(~T, d, lo, t, v, hd1, pf, hlo)) : {(DQ.DQ{1n+d, cc, lp, 1n+c, Array.set(T, _, U32.from_nat(lp), v)}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lp, 1n+c, AR.upd(T, 1n+d, gt, lp, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    %Equal.sym(Array<T>, Array.set(T, AR.thaw(T, gt), U32.from_nat(lp), v), AR.thaw(T, AR.upd(T, 1n+d, gt, lp, v)), ST.set_at(T, 1n+d, gt, lp, v, hd1, pg, hlp)) : {(DQ.DQ{1n+d, cc, lp, 1n+c, _}, E.OUnit{}) == (ST.real(T, ST.Sh{1n+d, lp, 1n+c, AR.upd(T, 1n+d, gt, lp, v)}), E.OUnit{}) : DQ.Deque<T> & E.Obs<T>}
    {==},
    ST.good_intro(T, 1n+d, lp, 1n+c, AR.upd(T, 1n+d, gt, lp, v), hd1, AR.upd_perfect(T, 1n+d, gt, lp, v, pg), hlp, N.double_succ_le(c, hc)),
    %Equal.sym(List<&2, T>, AR.slots(T, AR.upd(T, 1n+d, gt, lp, v)), SC.update(T, gs, lp, v), AR.upd_slots(T, 1n+d, gt, lp, v, hlp, pg)) : {(SC.take(T, R.rot(T, _, lp), 1n+c), E.OUnit{}) == (Con{v, SC.take(T, r, c)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, R.rot(T, SC.update(T, gs, lp, v), lp), 1n+c), Con{v, SC.take(T, R.rot(T, gs, 0n), c)}, em) : {(_, E.OUnit{}) == (Con{v, SC.take(T, r, c)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, R.rot(T, gs, 0n), gs, R.rot_zero(T, gs)) : {(Con{v, SC.take(T, _, c)}, E.OUnit{}) == (Con{v, SC.take(T, r, c)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, gs, c), r, gt_take(T, d, lo, t, v, g)) : {(Con{v, _}, E.OUnit{}) == (Con{v, SC.take(T, r, c)}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    %Equal.sym(List<&2, T>, SC.take(T, r, c), r, model_full(T, d, lo, t, g)) : {(Con{v, r}, E.OUnit{}) == (Con{v, _}, E.OUnit{}) : List<&2, T> & E.Obs<T>}
    {==})
