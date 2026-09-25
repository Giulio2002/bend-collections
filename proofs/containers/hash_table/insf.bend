import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/lib/common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./words.bend as WR
import ./buckets.bend as B
import ./state.bend as ST
import ./insm.bend as IM
import ../../lib/nat_list.bend as NL
import ../../lib/words32.bend as W32

# The free list across an insertion: its slots stay unused when the new
# bucket takes a slot not on it, and forgetting visited slots keeps it valid.


def mem_ne_c(+a: Nat, +t: Nat, +seen: List<&2, Nat>, +ha: {NL.memn(a, seen) == True{} : Bool}, +ht: {Bool.not(NL.memn(t, seen)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(a, t) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +h2 = L.subst(Nat, z => {NL.memn(z, seen) == True{} : Bool}, a, t, N.eq_from_is_eq(a, t, hc), ha)
      Empty.absurd({True{} == False{} : Bool}, L.false_true(L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, NL.memn(t, seen), True{}, h2, ht)))

# a slot on the list and a slot not on it differ
def mem_ne(+a: Nat, +t: Nat, +seen: List<&2, Nat>, +ha: {NL.memn(a, seen) == True{} : Bool}, +ht: {Bool.not(NL.memn(t, seen)) == True{} : Bool}) -> {Nat.is_eq(a, t) == False{} : Bool}:
  mem_ne_c(a, t, seen, ha, ht, Nat.is_eq(a, t), {==})

def mem_cons(+a: Nat, +t: Nat, +seen: List<&2, Nat>, +ha: {NL.memn(a, seen) == True{} : Bool}) -> {NL.memn(a, Con{t, seen}) == True{} : Bool}:
  L.subst(Bool, b => {Bool.or(Nat.is_eq(t, a), b) == True{} : Bool}, True{}, NL.memn(a, seen), Equal.sym(Bool, NL.memn(a, seen), True{}, ha), WR.or_true(Nat.is_eq(t, a)))

# THEOREM: filling bucket e with a slot the list has visited keeps the list valid
def fl_tr(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +nb: Nat, +nxl: List<&2, U32>, +cnt: Nat, +f: U32, +fr: Nat, +seen: List<&2, Nat>, +hm: {NL.memn(UD.v(H.slot(L)), seen) == True{} : Bool}, +h: {ST.fl_ok(bs, nb, nxl, cnt, f, fr, seen) == True{} : Bool}) -> {ST.fl_ok(IM.bupd(bs, e, B.BF{w, L, key}), nb, nxl, cnt, f, fr, seen) == True{} : Bool}:
  match cnt:
    case 0n:
      h
    case 1n+p:
      +x1 = Bool.not(U32.is_eq(f, 0))
      +x2 = Bool.and(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))), ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}))
      +y = Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen))))
      +z = Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))
      +a1 = L.and_left(x1, x2, h)
      +a2 = L.and_left(y, ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}), L.and_right(x1, x2, h))
      +a5 = L.and_right(y, ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}), L.and_right(x1, x2, h))
      +lt = L.and_left(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2)
      +ns = L.and_left(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2))
      +nm = L.and_right(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2))
      +ns2 = IM.noslot_up(bs, e, he, w, L, key, UD.v(H.slot(f)), mem_ne(UD.v(H.slot(L)), UD.v(H.slot(f)), seen, hm, nm), nb, ns)
      +r5 = fl_tr(bs, e, he, w, L, key, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}, mem_cons(UD.v(H.slot(L)), UD.v(H.slot(f)), seen, hm), a5)
      L.and_intro(x1, Bool.and(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(IM.bupd(bs, e, B.BF{w, L, key}), UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))), ST.fl_ok(IM.bupd(bs, e, B.BF{w, L, key}), nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen})), a1, L.and_intro(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(IM.bupd(bs, e, B.BF{w, L, key}), UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))), ST.fl_ok(IM.bupd(bs, e, B.BF{w, L, key}), nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}), L.and_intro(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(IM.bupd(bs, e, B.BF{w, L, key}), UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen))), lt, L.and_intro(ST.noslot(IM.bupd(bs, e, B.BF{w, L, key}), UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), ns2, nm)), r5))

# ---- forgetting visited slots ----

def subl(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(NL.memn(x, ys), subl(t, ys))

def ms_c(+t: Nat, +x: Nat, +r: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {NL.memn(x, ys) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(x, t) == c : Bool}, +hm: {Bool.or(c, NL.memn(t, r)) == True{} : Bool}, rec: @hr: {NL.memn(t, r) == True{} : Bool} -> {NL.memn(t, ys) == True{} : Bool}) -> {NL.memn(t, ys) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {NL.memn(z, ys) == True{} : Bool}, x, t, N.eq_from_is_eq(x, t, hc), hx)
    case False{}:
      rec(hm)

def memn_sub(+t: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hs: {subl(xs, ys) == True{} : Bool}, +hm: {NL.memn(t, xs) == True{} : Bool}) -> {NL.memn(t, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({NL.memn(t, ys) == True{} : Bool}, L.false_true(hm))
    case Con{+x, r}:
      ms_c(t, x, r, ys, L.and_left(NL.memn(x, ys), subl(r, ys), hs), Nat.is_eq(x, t), {==}, hm, hr => memn_sub(t, r, ys, L.and_right(NL.memn(x, ys), subl(r, ys), hs), hr))

def nm_c(+t: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hs: {subl(xs, ys) == True{} : Bool}, +h: {Bool.not(NL.memn(t, ys)) == True{} : Bool}, +c: Bool, +hc: {NL.memn(t, xs) == c : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, L.false_true(L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, NL.memn(t, ys), True{}, memn_sub(t, xs, ys, hs, hc), h)))

def subl_cons(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +y: Nat, +h: {subl(xs, ys) == True{} : Bool}) -> {subl(xs, Con{y, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, r}:
      L.and_intro(NL.memn(x, Con{y, ys}), subl(r, Con{y, ys}), mem_cons(x, y, ys, L.and_left(NL.memn(x, ys), subl(r, ys), h)), subl_cons(r, ys, y, L.and_right(NL.memn(x, ys), subl(r, ys), h)))

def subl_both(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +t: Nat, +h: {subl(xs, ys) == True{} : Bool}) -> {subl(Con{t, xs}, Con{t, ys}) == True{} : Bool}:
  L.and_intro(NL.memn(t, Con{t, ys}), subl(xs, Con{t, ys}), L.subst(Bool, b => {Bool.or(b, NL.memn(t, ys)) == True{} : Bool}, True{}, Nat.is_eq(t, t), Equal.sym(Bool, Nat.is_eq(t, t), True{}, N.is_eq_refl(t)), {==}), subl_cons(xs, ys, t, h))

# THEOREM: a valid list stays valid when fewer slots count as visited
def fl_weak(+bs: List<&2, B.Bk>, +nb: Nat, +nxl: List<&2, U32>, +cnt: Nat, +f: U32, +fr: Nat, +seen: List<&2, Nat>, +seen2: List<&2, Nat>, +hs: {subl(seen2, seen) == True{} : Bool}, +h: {ST.fl_ok(bs, nb, nxl, cnt, f, fr, seen) == True{} : Bool}) -> {ST.fl_ok(bs, nb, nxl, cnt, f, fr, seen2) == True{} : Bool}:
  match cnt:
    case 0n:
      h
    case 1n+p:
      +x1 = Bool.not(U32.is_eq(f, 0))
      +x2 = Bool.and(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))), ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}))
      +y = Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen))))
      +z = Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)))
      +a2 = L.and_left(y, ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}), L.and_right(x1, x2, h))
      +a5 = L.and_right(y, ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}), L.and_right(x1, x2, h))
      +nm = L.and_right(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2))
      +nm2 = nm_c(UD.v(H.slot(f)), seen2, seen, hs, nm, NL.memn(UD.v(H.slot(f)), seen2), {==})
      L.and_intro(x1, Bool.and(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen2)))), ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen2})), L.and_left(x1, x2, h), L.and_intro(Bool.and(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen2)))), ST.fl_ok(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen2}), L.and_intro(Nat.is_lt(UD.v(H.slot(f)), fr), Bool.and(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen2))), L.and_left(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2), L.and_intro(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen2)), L.and_left(ST.noslot(bs, UD.v(H.slot(f)), nb), Bool.not(NL.memn(UD.v(H.slot(f)), seen)), L.and_right(Nat.is_lt(UD.v(H.slot(f)), fr), z, a2)), nm2)), fl_weak(bs, nb, nxl, p, W32.nth0(nxl, UD.v(H.slot(f))), fr, Con{UD.v(H.slot(f)), seen}, Con{UD.v(H.slot(f)), seen2}, subl_both(seen2, seen, UD.v(H.slot(f)), hs), a5)))

# ---- the list's length ----

# an empty list (link 0) has no links
def cnt_zero(+bs: List<&2, B.Bk>, +nb: Nat, +nxl: List<&2, U32>, +cnt: Nat, +fr: Nat, +seen: List<&2, Nat>, +h: {ST.fl_ok(bs, nb, nxl, cnt, 0, fr, seen) == True{} : Bool}) -> {cnt == 0n : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, L.false_true(h))

# a list that is not empty has a first link
def cnt_pos(+bs: List<&2, B.Bk>, +nb: Nat, +nxl: List<&2, U32>, +cnt: Nat, +f: U32, +fr: Nat, +seen: List<&2, Nat>, +hf: {U32.is_eq(f, 0) == False{} : Bool}, +h: {ST.fl_ok(bs, nb, nxl, cnt, f, fr, seen) == True{} : Bool}) -> Sigma<&1, &1, Nat, p => {cnt == 1n+p : Nat}>:
  match cnt:
    case 0n:
      Empty.absurd(Sigma<&1, &1, Nat, p => {0n == 1n+p : Nat}>, L.false_true(Equal.trans(Bool, False{}, U32.is_eq(f, 0), True{}, Equal.sym(Bool, U32.is_eq(f, 0), False{}, hf), h)))
    case 1n+p:
      (p, {==})

# with n <= fr and fr - n = 0: fr = n
def sub_zero_eq(+fr: Nat, +n: Nat, +hle: {Nat.is_le(n, fr) == True{} : Bool}, +h: {Nat.sub(fr, n) == 0n : Nat}) -> {fr == n : Nat}:
  Equal.trans(Nat, fr, Nat.add(n, Nat.sub(fr, n)), n, Equal.sym(Nat, Nat.add(n, Nat.sub(fr, n)), fr, N.sub_add(fr, n, hle)), Equal.trans(Nat, Nat.add(n, Nat.sub(fr, n)), Nat.add(n, 0n), n, Equal.cong(Nat, Nat, z => Nat.add(n, z), Nat.sub(fr, n), 0n, h), N.add_zero(n)))

# with n <= fr and fr - n = p + 1: n + 1 <= fr and fr - (n + 1) = p
def sub_step(+fr: Nat, +n: Nat, +p: Nat, +hle: {Nat.is_le(n, fr) == True{} : Bool}, +h: {Nat.sub(fr, n) == 1n+p : Nat}) -> {Nat.sub(fr, 1n+n) == p : Nat} & {Nat.is_le(1n+n, fr) == True{} : Bool}:
  +efr = Equal.trans(Nat, fr, Nat.add(n, Nat.sub(fr, n)), Nat.add(n, 1n+p), Equal.sym(Nat, Nat.add(n, Nat.sub(fr, n)), fr, N.sub_add(fr, n, hle)), Equal.cong(Nat, Nat, z => Nat.add(n, z), Nat.sub(fr, n), 1n+p, h))
  +efr2 = Equal.trans(Nat, fr, Nat.add(n, 1n+p), 1n+Nat.add(n, p), efr, N.add_succ(n, p))
  +es = L.subst(Nat, z => {Nat.sub(z, 1n+n) == p : Nat}, 1n+Nat.add(n, p), fr, Equal.sym(Nat, fr, 1n+Nat.add(n, p), efr2), N.add_sub_cancel(n, p))
  +el = L.subst(Nat, z => {Nat.is_le(1n+n, z) == True{} : Bool}, 1n+Nat.add(n, p), fr, Equal.sym(Nat, fr, 1n+Nat.add(n, p), efr2), N.le_add_right(n, p))
  (es, el)

# ---- a fresh slot is used by no bucket ----

def ns_live_b(+lv: List<&2, Bool>, +fr: Nat, +b: B.Bk, +h: {B.live_b(lv, fr, b) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), fr))) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, k}:
      IM.not_f(Nat.is_eq(UD.v(H.slot(l)), fr), N.is_eq_lt(UD.v(H.slot(l)), fr, L.and_right(B.nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), fr), h)))

# THEOREM: every bucket's slot is below fresh, so fresh is unused
def noslot_live(+bs: List<&2, B.Bk>, +lv: List<&2, Bool>, +fr: Nat, +n: Nat, +hl: {B.all_lt(B.PLive{bs, lv, fr}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {ST.noslot(bs, fr, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hm)
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), fr))), ST.noslot(bs, fr, j), ns_live_b(lv, fr, B.at(bs, j), B.all_inst(B.PLive{bs, lv, fr}, n, hl, j, hj)), noslot_live(bs, lv, fr, n, hl, j, N.lt_le(j, n, hj)))
