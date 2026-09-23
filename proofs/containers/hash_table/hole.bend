import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/math/hash.bend as HS
import ./buckets.bend as B
import ./modn.bend as M
import ./cyc.bend as CY
import ./probe_all.bend as PA
import ./insm.bend as IM
import ./insert.bend as IS
import ./ring.bend as RG
import ./rehash.bend as RH

# Backward-shift deletion at the bucket level. While the gap left by the
# removed bucket travels forward, every full bucket's path is full except
# possibly at the gap h, and only buckets at least dk past h have paths
# through h. When the scan meets an empty bucket, no path goes through the
# gap, so the clusters are whole again.


def hb_lt(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +b: B.Bk) -> {Nat.is_lt(B.hb(CY.msk(K), b), 1n+bp) == True{} : Bool}:
  match b:
    case B.BE{}:
      N.succ_le_lt(0n, 1n+bp, N.zero_le(bp))
    case B.BF{+w, l, k}:
      L.subst(Nat, z => {Nat.is_lt(UD.v(HS.bucket(w, CY.msk(K))), z) == True{} : Bool}, SC.pow2(K), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(K), hN), PA.home_lt(w, K))

# ---- paths full except at h ----

def ox_c(+bs: List<&2, B.Bk>, +n: Nat, +a: Nat, +h: Nat, +q: Nat, +hp: {Bool.and(Bool.or(Nat.is_eq(h, M.pos(n, a, q)), B.occ(B.at(bs, M.pos(n, a, q)))), B.opx(bs, n, a, q, h)) == True{} : Bool}, +t: Nat, +ht: {Nat.is_lt(t, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(t, q) == c : Bool}, rec: @hlt: {Nat.is_lt(t, q) == True{} : Bool} -> {Bool.or(Nat.is_eq(h, M.pos(n, a, t)), B.occ(B.at(bs, M.pos(n, a, t)))) == True{} : Bool}) -> {Bool.or(Nat.is_eq(h, M.pos(n, a, t)), B.occ(B.at(bs, M.pos(n, a, t)))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.or(Nat.is_eq(h, M.pos(n, a, z)), B.occ(B.at(bs, M.pos(n, a, z)))) == True{} : Bool}, q, t, Equal.sym(Nat, t, q, N.eq_from_is_eq(t, q, hc)), L.and_left(Bool.or(Nat.is_eq(h, M.pos(n, a, q)), B.occ(B.at(bs, M.pos(n, a, q)))), B.opx(bs, n, a, q, h), hp))
    case False{}:
      rec(N.lt_or_eq(t, q, N.lt_succ_le(t, q, ht), hc))

def opx_inst(+bs: List<&2, B.Bk>, +n: Nat, +a: Nat, +m: Nat, +h: Nat, +hp: {B.opx(bs, n, a, m, h) == True{} : Bool}, +t: Nat, +ht: {Nat.is_lt(t, m) == True{} : Bool}) -> {Bool.or(Nat.is_eq(h, M.pos(n, a, t)), B.occ(B.at(bs, M.pos(n, a, t)))) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Bool.or(Nat.is_eq(h, M.pos(n, a, t)), B.occ(B.at(bs, M.pos(n, a, t)))) == True{} : Bool}, N.lt_zero_absurd(t, ht))
    case 1n+q:
      ox_c(bs, n, a, h, q, hp, t, ht, Nat.is_eq(t, q), {==}, hlt => opx_inst(bs, n, a, q, h, L.and_right(Bool.or(Nat.is_eq(h, M.pos(n, a, q)), B.occ(B.at(bs, M.pos(n, a, q)))), B.opx(bs, n, a, q, h), hp), t, hlt))

def opx_pre(+bs: List<&2, B.Bk>, +n: Nat, +a: Nat, +m: Nat, +h: Nat, +hp: {B.opx(bs, n, a, m, h) == True{} : Bool}, +m2: Nat, +hm: {Nat.is_le(m2, m) == True{} : Bool}) -> {B.opx(bs, n, a, m2, h) == True{} : Bool}:
  match m2:
    case 0n:
      {==}
    case 1n+s:
      +hs = N.succ_le_lt(s, m, hm)
      L.and_intro(Bool.or(Nat.is_eq(h, M.pos(n, a, s)), B.occ(B.at(bs, M.pos(n, a, s)))), B.opx(bs, n, a, s, h), opx_inst(bs, n, a, m, h, hp, s, hs), opx_pre(bs, n, a, m, h, hp, s, N.lt_le(s, m, hs)))

def or_f(+x: Bool, +y: Bool, +h: {Bool.or(x, y) == True{} : Bool}, +hx: {x == False{} : Bool}) -> {y == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, y) == True{} : Bool}, x, False{}, hx, h)

# a path that does not reach h is full
def occ_of_opx(+bs: List<&2, B.Bk>, +bp: Nat, +a: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +h: Nat, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}, +hp: {B.opx(bs, 1n+bp, a, m, h) == True{} : Bool}, +hn: {Nat.is_lt(M.dist(1n+bp, a, h), m) == False{} : Bool}) -> {B.occpath(bs, 1n+bp, a, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+s:
      +d = M.dist(1n+bp, a, h)
      +hd = N.not_lt_le(d, 1n+s, hn)
      +hsd = N.lt_le_trans(s, 1n+s, d, N.lt_succ(s), hd)
      +hne = N.is_eq_sym_false(M.pos(1n+bp, a, s), h, RG.pos_ne(bp, a, s, h, ha, N.lt_le_trans(s, 1n+s, 1n+bp, N.lt_succ(s), hm), N.is_eq_lt(s, d, hsd)))
      +x = Bool.or(Nat.is_eq(h, M.pos(1n+bp, a, s)), B.occ(B.at(bs, M.pos(1n+bp, a, s))))
      L.and_intro(B.occ(B.at(bs, M.pos(1n+bp, a, s))), B.occpath(bs, 1n+bp, a, s), or_f(Nat.is_eq(h, M.pos(1n+bp, a, s)), B.occ(B.at(bs, M.pos(1n+bp, a, s))), L.and_left(x, B.opx(bs, 1n+bp, a, s, h), hp), hne), occ_of_opx(bs, bp, a, ha, h, s, N.lt_le(s, 1n+bp, N.lt_le_trans(s, 1n+s, 1n+bp, N.lt_succ(s), hm)), L.and_right(x, B.opx(bs, 1n+bp, a, s, h), hp), N.le_not_lt(d, s, N.lt_le(s, d, hsd))))

def ooc_bit(+bs: List<&2, B.Bk>, +i: Nat, +p: Nat, +ho: {B.occ(B.at(bs, p)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, p) == c : Bool}) -> {Bool.or(c, B.occ(B.at(IM.bupd(bs, i, B.BE{}), p))) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      L.subst(B.Bk, y => {Bool.or(False{}, B.occ(y)) == True{} : Bool}, B.at(bs, p), B.at(IM.bupd(bs, i, B.BE{}), p), Equal.sym(B.Bk, B.at(IM.bupd(bs, i, B.BE{}), p), B.at(bs, p), IM.at_bupd_other(bs, i, B.BE{}, p, hc)), ho)

# emptying bucket i leaves every full path full except at i
def opx_of_occ(+bs: List<&2, B.Bk>, +i: Nat, +n: Nat, +a: Nat, +m: Nat, +hp: {B.occpath(bs, n, a, m) == True{} : Bool}) -> {B.opx(IM.bupd(bs, i, B.BE{}), n, a, m, i) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+s:
      +p = M.pos(n, a, s)
      L.and_intro(Bool.or(Nat.is_eq(i, p), B.occ(B.at(IM.bupd(bs, i, B.BE{}), p))), B.opx(IM.bupd(bs, i, B.BE{}), n, a, s, i), L.subst(Bool, c => {Bool.or(c, B.occ(B.at(IM.bupd(bs, i, B.BE{}), p))) == True{} : Bool}, Nat.is_eq(i, p), Nat.is_eq(i, p), {==}, ooc_bit(bs, i, p, L.and_left(B.occ(B.at(bs, p)), B.occpath(bs, n, a, s), hp), Nat.is_eq(i, p), {==})), opx_of_occ(bs, i, n, a, s, L.and_right(B.occ(B.at(bs, p)), B.occpath(bs, n, a, s), hp)))

# ---- moving bucket k into the gap h ----


def hlen2(+V: List<&2, B.Bk>, +h: Nat, +k: Nat, +b: B.Bk, +hbo: {B.occ(b) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}) -> {Nat.is_lt(h, SC.length(B.Bk, IM.bupd(V, k, B.BE{}))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(h, z) == True{} : Bool}, SC.length(B.Bk, V), SC.length(B.Bk, IM.bupd(V, k, B.BE{})), Equal.sym(Nat, SC.length(B.Bk, IM.bupd(V, k, B.BE{})), SC.length(B.Bk, V), RG.len_bupd(V, k, B.BE{})), hlen)

def mv_h2(+V: List<&2, B.Bk>, +h: Nat, +k: Nat, +b: B.Bk, +hbo: {B.occ(b) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +p: Nat, +c: Bool, +hc: {Nat.is_eq(h, p) == c : Bool}, +hold: {Bool.or(c, B.occ(B.at(V, p))) == True{} : Bool}, +hck: {Nat.is_eq(k, p) == False{} : Bool}) -> {Bool.or(False{}, B.occ(B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, b, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), b, IM.at_bu_eq(IM.bupd(V, k, B.BE{}), h, b, hlen2(V, h, k, b, hbo, hlen), p, hc)), hbo)
    case False{}:
      L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, B.at(V, p), B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), B.at(V, p), Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), B.at(IM.bupd(V, k, B.BE{}), p), B.at(V, p), IM.at_bupd_other(IM.bupd(V, k, B.BE{}), h, b, p, hc), IM.at_bupd_other(V, k, B.BE{}, p, hck))), hold)

def mv_h(+V: List<&2, B.Bk>, +h: Nat, +k: Nat, +b: B.Bk, +hbo: {B.occ(b) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +p: Nat, +c: Bool, +hc: {Nat.is_eq(h, p) == c : Bool}, +hold: {Bool.or(c, B.occ(B.at(V, p))) == True{} : Bool}, +ck: Bool, +hck: {Nat.is_eq(k, p) == ck : Bool}) -> {Bool.or(ck, B.occ(B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p))) == True{} : Bool}:
  match ck:
    case True{}:
      {==}
    case False{}:
      mv_h2(V, h, k, b, hbo, hlen, p, c, hc, hold, hck)

# THEOREM: after the move, paths are full except at the new gap k
def opx_move(+V: List<&2, B.Bk>, +h: Nat, +k: Nat, +b: B.Bk, +hbo: {B.occ(b) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +n: Nat, +a: Nat, +m: Nat, +hp: {B.opx(V, n, a, m, h) == True{} : Bool}) -> {B.opx(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, a, m, k) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+s:
      +p = M.pos(n, a, s)
      +x = Bool.or(Nat.is_eq(h, p), B.occ(B.at(V, p)))
      L.and_intro(Bool.or(Nat.is_eq(k, p), B.occ(B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p))), B.opx(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, a, s, k), mv_h(V, h, k, b, hbo, hlen, p, Nat.is_eq(h, p), {==}, L.and_left(x, B.opx(V, n, a, s, h), hp), Nat.is_eq(k, p), {==}), opx_move(V, h, k, b, hbo, hlen, n, a, s, L.and_right(x, B.opx(V, n, a, s, h), hp)))

# ---- more ring facts ----

# a path from a through h to j: its length splits at h
def dist_split2(+bp: Nat, +a: Nat, +h: Nat, +j: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hlt: {Nat.is_lt(M.dist(1n+bp, a, h), M.dist(1n+bp, a, j)) == True{} : Bool}) -> {Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)) == M.dist(1n+bp, a, j) : Nat}:
  +x = M.dist(1n+bp, a, h)
  +m = M.dist(1n+bp, a, j)
  +r = Nat.sub(m, x)
  +exr = N.sub_add(m, x, N.lt_le(x, m, hlt))
  +hr = N.le_lt_trans(r, m, 1n+bp, L.subst(Nat, z => {Nat.is_le(r, z) == True{} : Bool}, Nat.add(r, x), m, Equal.trans(Nat, Nat.add(r, x), Nat.add(x, r), m, N.add_comm(r, x), exr), N.le_add_right(r, x)), M.dist_lt(bp, a, j))
  +pj = Equal.trans(Nat, M.pos(1n+bp, h, r), M.pos(1n+bp, M.pos(1n+bp, a, x), r), j, Equal.cong(Nat, Nat, z => M.pos(1n+bp, z, r), h, M.pos(1n+bp, a, x), Equal.sym(Nat, M.pos(1n+bp, a, x), h, M.pos_dist(bp, a, h, ha, hh))), Equal.trans(Nat, M.pos(1n+bp, M.pos(1n+bp, a, x), r), M.pos(1n+bp, a, Nat.add(x, r)), j, RG.pos_add(bp, a, x, r), Equal.trans(Nat, M.pos(1n+bp, a, Nat.add(x, r)), M.pos(1n+bp, a, m), j, Equal.cong(Nat, Nat, z => M.pos(1n+bp, a, z), Nat.add(x, r), m, exr), M.pos_dist(bp, a, j, ha, hj))))
  +dr = Equal.trans(Nat, M.dist(1n+bp, h, j), M.dist(1n+bp, h, M.pos(1n+bp, h, r)), r, Equal.cong(Nat, Nat, z => M.dist(1n+bp, h, z), j, M.pos(1n+bp, h, r), Equal.sym(Nat, M.pos(1n+bp, h, r), j, pj)), M.dist_pos(bp, h, r, hh, hr))
  Equal.trans(Nat, Nat.add(x, M.dist(1n+bp, h, j)), Nat.add(x, r), m, Equal.cong(Nat, Nat, z => Nat.add(x, z), M.dist(1n+bp, h, j), r, dr), exr)

def dp_c(+bp: Nat, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hne: {Nat.is_eq(i, j) == False{} : Bool}, +d: Nat, +hd: {M.dist(1n+bp, i, j) == d : Nat}) -> {Nat.is_le(1n, d) == True{} : Bool}:
  match d:
    case 0n:
      +e = RG.eq_of_dist0(bp, i, j, hi, hj, hd)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(i, j), False{}, Equal.sym(Bool, Nat.is_eq(i, j), True{}, IS.eq_is_eq(i, j, e)), hne)))
    case 1n+p:
      N.zero_le(p)

# distinct buckets are at least one step apart
def dist_pos1(+bp: Nat, +i: Nat, +j: Nat, +hi: {Nat.is_lt(i, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hne: {Nat.is_eq(i, j) == False{} : Bool}) -> {Nat.is_le(1n, M.dist(1n+bp, i, j)) == True{} : Bool}:
  dp_c(bp, i, j, hi, hj, hne, M.dist(1n+bp, i, j), {==})

# ---- the hole invariant: start ----


def h0_o(+O: List<&2, B.Bk>, +K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +i: Nat, +hi: {Nat.is_lt(i, 1n+bp) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hij: {Nat.is_eq(i, j) == False{} : Bool}, +x: B.Bk, +hx: {B.implies(B.occ(x), B.occpath(O, 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j))) == True{} : Bool}, +o: Bool, +ho: {B.occ(x) == o : Bool}) -> {B.implies(o, Bool.and(B.opx(IM.bupd(O, i, B.BE{}), 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j), i), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), x), i), M.dist(1n+bp, B.hb(CY.msk(K), x), j)), Nat.is_le(1n, M.dist(1n+bp, i, j))))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      +op = B.imp_elim(B.occ(x), B.occpath(O, 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j)), hx, ho)
      L.and_intro(B.opx(IM.bupd(O, i, B.BE{}), 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j), i), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), x), i), M.dist(1n+bp, B.hb(CY.msk(K), x), j)), Nat.is_le(1n, M.dist(1n+bp, i, j))), opx_of_occ(O, i, 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j), op), RH.imp_true(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), x), i), M.dist(1n+bp, B.hb(CY.msk(K), x), j)), Nat.is_le(1n, M.dist(1n+bp, i, j)), dist_pos1(bp, i, j, hi, hj, hij)))


def h0_i(+O: List<&2, B.Bk>, +K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +i: Nat, +hi: {Nat.is_lt(i, 1n+bp) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +cl: {B.cluster(O, 1n+bp, CY.msk(K)) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, j) == c : Bool}) -> {B.eval(B.PHole{IM.bupd(O, i, B.BE{}), 1n+bp, CY.msk(K), i, 1n}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(IM.bupd(O, i, B.BE{}), 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), j), i), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), i), M.dist(1n+bp, B.hb(CY.msk(K), y), j)), Nat.is_le(1n, M.dist(1n+bp, i, j))))) == True{} : Bool}, B.BE{}, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), B.BE{}, IM.at_bu_eq(O, i, B.BE{}, hlen, j, hc)), {==})
    case False{}:
      +x = B.at(O, j)
      L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(IM.bupd(O, i, B.BE{}), 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), j), i), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), i), M.dist(1n+bp, B.hb(CY.msk(K), y), j)), Nat.is_le(1n, M.dist(1n+bp, i, j))))) == True{} : Bool}, x, B.at(IM.bupd(O, i, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(O, i, B.BE{}), j), x, IM.at_bupd_other(O, i, B.BE{}, j, hc)), L.subst(Bool, o => {B.implies(o, Bool.and(B.opx(IM.bupd(O, i, B.BE{}), 1n+bp, B.hb(CY.msk(K), x), M.dist(1n+bp, B.hb(CY.msk(K), x), j), i), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), x), i), M.dist(1n+bp, B.hb(CY.msk(K), x), j)), Nat.is_le(1n, M.dist(1n+bp, i, j))))) == True{} : Bool}, B.occ(x), B.occ(x), {==}, h0_o(O, K, bp, hN, i, hi, j, hj, hc, x, B.all_inst(B.PClus{O, 1n+bp, CY.msk(K)}, 1n+bp, cl, j, hj), B.occ(x), {==})))

# THEOREM: emptying a bucket of a clustered table starts the invariant
def hole_init(+O: List<&2, B.Bk>, +K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +i: Nat, +hi: {Nat.is_lt(i, 1n+bp) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, O)) == True{} : Bool}, +cl: {B.cluster(O, 1n+bp, CY.msk(K)) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PHole{IM.bupd(O, i, B.BE{}), 1n+bp, CY.msk(K), i, 1n}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, 1n+bp, hm)
      L.and_intro(B.eval(B.PHole{IM.bupd(O, i, B.BE{}), 1n+bp, CY.msk(K), i, 1n}, q), B.all_lt(B.PHole{IM.bupd(O, i, B.BE{}), 1n+bp, CY.msk(K), i, 1n}, q), h0_i(O, K, bp, hN, i, hi, hlen, cl, q, hq, Nat.is_eq(i, q), {==}), hole_init(O, K, bp, hN, i, hi, hlen, cl, q, N.lt_le(q, 1n+bp, hq)))

# ---- the scan position ----


def dist_k(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}) -> {M.dist(1n+bp, h, M.pos(1n+bp, h, dk)) == dk : Nat}:
  M.dist_pos(bp, h, dk, hh, hdn)

def hk_c(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(h, M.pos(1n+bp, h, dk)) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e = Equal.trans(Nat, 0n, M.dist(1n+bp, h, h), dk, Equal.sym(Nat, M.dist(1n+bp, h, h), 0n, RG.dist_self(bp, h, hh)), Equal.trans(Nat, M.dist(1n+bp, h, h), M.dist(1n+bp, h, M.pos(1n+bp, h, dk)), dk, Equal.cong(Nat, Nat, z => M.dist(1n+bp, h, z), h, M.pos(1n+bp, h, dk), N.eq_from_is_eq(h, M.pos(1n+bp, h, dk), hc)), dist_k(K, bp, hN, V, h, hh, dk, hd1, hdn)))
      Empty.absurd({True{} == False{} : Bool}, L.false_true(L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, dk, 0n, Equal.sym(Nat, 0n, dk, e), hd1)))

# the scan position is not the gap
def h_ne_k(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}) -> {Nat.is_eq(h, M.pos(1n+bp, h, dk)) == False{} : Bool}:
  hk_c(K, bp, hN, V, h, hh, dk, hd1, hdn, Nat.is_eq(h, M.pos(1n+bp, h, dk)), {==})

# ---- end: the scan met an empty bucket ----

def e_bad(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hz: {B.occ(B.at(V, M.pos(1n+bp, h, dk))) == False{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hoj: {B.occ(B.at(V, j)) == True{} : Bool}, +hop: {B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h) == True{} : Bool}, +hlt: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == True{} : Bool}, +hge: {Nat.is_le(dk, M.dist(1n+bp, h, j)) == True{} : Bool}, +c3: Bool, +hc3: {Nat.is_eq(dk, M.dist(1n+bp, h, j)) == c3 : Bool}) -> Empty:
  match c3:
    case True{}:
      +ejk = Equal.trans(Nat, j, M.pos(1n+bp, h, M.dist(1n+bp, h, j)), M.pos(1n+bp, h, dk), Equal.sym(Nat, M.pos(1n+bp, h, M.dist(1n+bp, h, j)), j, M.pos_dist(bp, h, j, hh, hj)), Equal.cong(Nat, Nat, z => M.pos(1n+bp, h, z), M.dist(1n+bp, h, j), dk, Equal.sym(Nat, dk, M.dist(1n+bp, h, j), N.eq_from_is_eq(dk, M.dist(1n+bp, h, j), hc3))))
      L.true_false(Equal.trans(Bool, True{}, B.occ(B.at(V, M.pos(1n+bp, h, dk))), False{}, L.subst(Nat, z => {True{} == B.occ(B.at(V, z)) : Bool}, j, M.pos(1n+bp, h, dk), ejk, Equal.sym(Bool, B.occ(B.at(V, j)), True{}, hoj)), hz))
    case False{}:
      +a = B.hb(CY.msk(K), B.at(V, j))
      +ha = hb_lt(K, bp, hN, B.at(V, j))
      +x = M.dist(1n+bp, a, h)
      +ds = dist_split2(bp, a, h, j, ha, hh, hj, hlt)
      +hlt2 = N.lt_or_eq(dk, M.dist(1n+bp, h, j), hge, hc3)
      +ht = L.subst(Nat, z => {Nat.is_lt(Nat.add(x, dk), z) == True{} : Bool}, Nat.add(x, M.dist(1n+bp, h, j)), M.dist(1n+bp, a, j), ds, N.lt_add_left(dk, M.dist(1n+bp, h, j), x, hlt2))
      +pt = Equal.trans(Nat, M.pos(1n+bp, a, Nat.add(x, dk)), M.pos(1n+bp, M.pos(1n+bp, a, x), dk), M.pos(1n+bp, h, dk), Equal.sym(Nat, M.pos(1n+bp, M.pos(1n+bp, a, x), dk), M.pos(1n+bp, a, Nat.add(x, dk)), RG.pos_add(bp, a, x, dk)), Equal.cong(Nat, Nat, z => M.pos(1n+bp, z, dk), M.pos(1n+bp, a, x), h, M.pos_dist(bp, a, h, ha, hh)))
      +oi = L.subst(Nat, z => {Bool.or(Nat.is_eq(h, z), B.occ(B.at(V, z))) == True{} : Bool}, M.pos(1n+bp, a, Nat.add(x, dk)), M.pos(1n+bp, h, dk), pt, opx_inst(V, 1n+bp, a, M.dist(1n+bp, a, j), h, hop, Nat.add(x, dk), ht))
      L.true_false(Equal.trans(Bool, True{}, B.occ(B.at(V, M.pos(1n+bp, h, dk))), False{}, Equal.sym(Bool, B.occ(B.at(V, M.pos(1n+bp, h, dk))), True{}, or_f(Nat.is_eq(h, M.pos(1n+bp, h, dk)), B.occ(B.at(V, M.pos(1n+bp, h, dk))), oi, h_ne_k(K, bp, hN, V, h, hh, dk, hd1, hdn))), hz))


def e_c(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hz: {B.occ(B.at(V, M.pos(1n+bp, h, dk))) == False{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hoj: {B.occ(B.at(V, j)) == True{} : Bool}, +hop: {B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h) == True{} : Bool}, +himp: {B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))) == True{} : Bool}, +c2: Bool, +hc2: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == c2 : Bool}) -> {B.occpath(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == True{} : Bool}:
  match c2:
    case False{}:
      occ_of_opx(V, bp, B.hb(CY.msk(K), B.at(V, j)), hb_lt(K, bp, hN, B.at(V, j)), h, M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), N.lt_le(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), 1n+bp, M.dist_lt(bp, B.hb(CY.msk(K), B.at(V, j)), j)), hop, hc2)
    case True{}:
      Empty.absurd({B.occpath(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == True{} : Bool}, e_bad(K, bp, hN, V, h, hh, dk, hd1, hdn, hz, j, hj, hoj, hop, hc2, B.imp_elim(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j)), himp, hc2), Nat.is_eq(dk, M.dist(1n+bp, h, j)), {==}))

def e_o(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hz: {B.occ(B.at(V, M.pos(1n+bp, h, dk))) == False{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +h0: {B.eval(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, j) == True{} : Bool}, +o: Bool, +ho: {B.occ(B.at(V, j)) == o : Bool}) -> {B.implies(o, B.occpath(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      +hx = B.imp_elim(B.occ(B.at(V, j)), Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j)))), h0, ho)
      e_c(K, bp, hN, V, h, hh, dk, hd1, hdn, hz, j, hj, ho, L.and_left(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))), hx), L.and_right(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))), hx), Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), {==})

def hole_end_m(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hz: {B.occ(B.at(V, M.pos(1n+bp, h, dk))) == False{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PClus{V, 1n+bp, CY.msk(K)}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, 1n+bp, hm)
      L.and_intro(B.eval(B.PClus{V, 1n+bp, CY.msk(K)}, j), B.all_lt(B.PClus{V, 1n+bp, CY.msk(K)}, j), L.subst(Bool, o => {B.implies(o, B.occpath(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j))) == True{} : Bool}, B.occ(B.at(V, j)), B.occ(B.at(V, j)), {==}, e_o(K, bp, hN, V, h, hh, dk, hd1, hdn, hz, j, hj, B.all_inst(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp, hv, j, hj), B.occ(B.at(V, j)), {==})), hole_end_m(K, bp, hN, V, h, hh, dk, hd1, hdn, hz, hv, j, N.lt_le(j, 1n+bp, hj)))

# THEOREM: when the scan meets an empty bucket, the clusters are whole
def hole_end(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hz: {B.occ(B.at(V, M.pos(1n+bp, h, dk))) == False{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}) -> {B.cluster(V, 1n+bp, CY.msk(K)) == True{} : Bool}:
  hole_end_m(K, bp, hN, V, h, hh, dk, hd1, hdn, hz, hv, 1n+bp, N.le_refl(1n+bp))

# ---- skip: the scanned bucket's path does not reach the gap ----


def s_ne(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hskip: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, M.pos(1n+bp, h, dk))), M.pos(1n+bp, h, dk)), dk) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hc2: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == True{} : Bool}, +c3: Bool, +hc3: {Nat.is_eq(dk, M.dist(1n+bp, h, j)) == c3 : Bool}) -> {c3 == False{} : Bool}:
  match c3:
    case False{}:
      {==}
    case True{}:
      +edj = N.eq_from_is_eq(dk, M.dist(1n+bp, h, j), hc3)
      +ejk = Equal.trans(Nat, M.pos(1n+bp, h, dk), M.pos(1n+bp, h, M.dist(1n+bp, h, j)), j, Equal.cong(Nat, Nat, z => M.pos(1n+bp, h, z), dk, M.dist(1n+bp, h, j), edj), M.pos_dist(bp, h, j, hh, hj))
      +hs2 = L.subst(Nat, z => {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, z)), z), dk) == True{} : Bool}, M.pos(1n+bp, h, dk), j, ejk, hskip)
      +ds = dist_split2(bp, B.hb(CY.msk(K), B.at(V, j)), h, j, hb_lt(K, bp, hN, B.at(V, j)), hh, hj, hc2)
      +le = L.subst(Nat, z => {Nat.is_le(z, M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == True{} : Bool}, M.dist(1n+bp, h, j), dk, Equal.sym(Nat, dk, M.dist(1n+bp, h, j), edj), L.subst(Nat, z => {Nat.is_le(M.dist(1n+bp, h, j), z) == True{} : Bool}, Nat.add(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, h, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), ds, L.subst(Nat, z => {Nat.is_le(M.dist(1n+bp, h, j), z) == True{} : Bool}, Nat.add(M.dist(1n+bp, h, j), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h)), Nat.add(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, h, j)), N.add_comm(M.dist(1n+bp, h, j), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h)), N.le_add_right(M.dist(1n+bp, h, j), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h)))))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), False{}, Equal.sym(Bool, Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), True{}, le), N.lt_not_le(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), dk, hs2))))


def s_imp(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hskip: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, M.pos(1n+bp, h, dk))), M.pos(1n+bp, h, dk)), dk) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +himp: {B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))) == True{} : Bool}, +c2: Bool, +hc2: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)) == c2 : Bool}) -> {B.implies(c2, Nat.is_le(1n+dk, M.dist(1n+bp, h, j))) == True{} : Bool}:
  match c2:
    case False{}:
      {==}
    case True{}:
      +le1 = B.imp_elim(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j)), himp, hc2)
      N.lt_succ_le_succ(dk, M.dist(1n+bp, h, j), N.lt_or_eq(dk, M.dist(1n+bp, h, j), le1, s_ne(K, bp, hN, V, h, hh, dk, hd1, hdn, hskip, j, hj, hc2, Nat.is_eq(dk, M.dist(1n+bp, h, j)), {==})))
def sk_o(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hskip: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, M.pos(1n+bp, h, dk))), M.pos(1n+bp, h, dk)), dk) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +h0: {B.eval(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, j) == True{} : Bool}, +o: Bool, +ho: {B.occ(B.at(V, j)) == o : Bool}) -> {B.implies(o, Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n+dk, M.dist(1n+bp, h, j))))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      +hx = B.imp_elim(B.occ(B.at(V, j)), Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j)))), h0, ho)
      L.and_intro(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n+dk, M.dist(1n+bp, h, j))), L.and_left(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))), hx), s_imp(K, bp, hN, V, h, hh, dk, hd1, hdn, hskip, j, hj, L.and_right(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))), hx), Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), {==}))

def hole_skip_m(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hskip: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, M.pos(1n+bp, h, dk))), M.pos(1n+bp, h, dk)), dk) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, 1n+dk}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, 1n+bp, hm)
      L.and_intro(B.eval(B.PHole{V, 1n+bp, CY.msk(K), h, 1n+dk}, j), B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, 1n+dk}, j), L.subst(Bool, o => {B.implies(o, Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n+dk, M.dist(1n+bp, h, j))))) == True{} : Bool}, B.occ(B.at(V, j)), B.occ(B.at(V, j)), {==}, sk_o(K, bp, hN, V, h, hh, dk, hd1, hdn, hskip, j, hj, B.all_inst(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp, hv, j, hj), B.occ(B.at(V, j)), {==})), hole_skip_m(K, bp, hN, V, h, hh, dk, hd1, hdn, hskip, hv, j, N.lt_le(j, 1n+bp, hj)))

# THEOREM: skipping a bucket whose path starts after the gap keeps the invariant one step further
def hole_skip(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +hskip: {Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, M.pos(1n+bp, h, dk))), M.pos(1n+bp, h, dk)), dk) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, 1n+dk}, 1n+bp) == True{} : Bool}:
  hole_skip_m(K, bp, hN, V, h, hh, dk, hd1, hdn, hskip, hv, 1n+bp, N.le_refl(1n+bp))

# ---- move: the scanned bucket's path reaches the gap ----


def hkk(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}) -> {Nat.is_lt(M.pos(1n+bp, h, dk), 1n+bp) == True{} : Bool}:
  M.pos_lt(bp, h, dk)

def m_at_h(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}) -> {B.eval(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, h) == True{} : Bool}:
  +hk0 = L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), M.pos(1n+bp, h, dk)), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), h), M.dist(1n+bp, B.hb(CY.msk(K), y), M.pos(1n+bp, h, dk))), Nat.is_le(dk, M.dist(1n+bp, h, M.pos(1n+bp, h, dk)))))) == True{} : Bool}, B.at(V, M.pos(1n+bp, h, dk)), b, hbk, B.all_inst(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp, hv, M.pos(1n+bp, h, dk), hkk(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv)))
  +hx = B.imp_elim(B.occ(b), Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))), Nat.is_le(dk, M.dist(1n+bp, h, M.pos(1n+bp, h, dk))))), hk0, hbo)
  +hop = L.and_left(B.opx(V, 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))), Nat.is_le(dk, M.dist(1n+bp, h, M.pos(1n+bp, h, dk)))), hx)
  +hle = L.subst(Nat, z => {Nat.is_le(z, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, dk, M.dist(1n+bp, h, M.pos(1n+bp, h, dk)), Equal.sym(Nat, M.dist(1n+bp, h, M.pos(1n+bp, h, dk)), dk, dist_k(K, bp, hN, V, h, hh, dk, hd1, hdn)), hmv)
  +ds = RG.dist_split(bp, B.hb(CY.msk(K), b), h, M.pos(1n+bp, h, dk), hb_lt(K, bp, hN, b), hh, hkk(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv), hle)
  +hl2 = L.subst(Nat, z => {Nat.is_le(M.dist(1n+bp, B.hb(CY.msk(K), b), h), z) == True{} : Bool}, Nat.add(M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.dist(1n+bp, h, M.pos(1n+bp, h, dk))), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), ds, N.le_add_right(M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.dist(1n+bp, h, M.pos(1n+bp, h, dk))))
  +op2 = opx_move(V, h, M.pos(1n+bp, h, dk), b, hbo, hlen, 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), h), opx_pre(V, 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), h, hop, M.dist(1n+bp, B.hb(CY.msk(K), b), h), hl2))
  +le1 = dist_pos1(bp, M.pos(1n+bp, h, dk), h, hkk(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv), hh, N.is_eq_sym_false(h, M.pos(1n+bp, h, dk), h_ne_k(K, bp, hN, V, h, hh, dk, hd1, hdn)))
  +r = RH.imp_true(B.occ(b), Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), b), h)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), h)))), L.and_intro(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), b), M.dist(1n+bp, B.hb(CY.msk(K), b), h), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), b), h)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), h))), op2, RH.imp_true(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), b), h)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), h)), le1)))
  L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), h), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), y), h)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), h))))) == True{} : Bool}, b, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), h), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), h), b, IM.at_bupd_same(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b, hlen2(V, h, M.pos(1n+bp, h, dk), b, hbo, hlen))), r)

def m_o(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hkj: {Nat.is_eq(M.pos(1n+bp, h, dk), j) == False{} : Bool}, +h0: {B.eval(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, j) == True{} : Bool}, +o: Bool, +ho: {B.occ(B.at(V, j)) == o : Bool}) -> {B.implies(o, Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j))))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      +hx = B.imp_elim(B.occ(B.at(V, j)), Bool.and(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j)))), h0, ho)
      L.and_intro(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j))), opx_move(V, h, M.pos(1n+bp, h, dk), b, hbo, hlen, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), L.and_left(B.opx(V, 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), h), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), h), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(dk, M.dist(1n+bp, h, j))), hx)), RH.imp_true(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j)), dist_pos1(bp, M.pos(1n+bp, h, dk), j, hkk(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv), hj, hkj)))

def m_k(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hc: {Nat.is_eq(h, j) == False{} : Bool}, +ck: Bool, +hck: {Nat.is_eq(M.pos(1n+bp, h, dk), j) == ck : Bool}) -> {B.eval(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, j) == True{} : Bool}:
  match ck:
    case True{}:
      L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), j), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), y), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j))))) == True{} : Bool}, B.BE{}, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), B.BE{}, Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), B.at(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), j), B.BE{}, IM.at_bupd_other(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b, j, hc), IM.at_bu_eq(V, M.pos(1n+bp, h, dk), B.BE{}, hlk, j, hck))), {==})
    case False{}:
      L.subst(B.Bk, y => {B.implies(B.occ(y), Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), y), M.dist(1n+bp, B.hb(CY.msk(K), y), j), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), y), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), y), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j))))) == True{} : Bool}, B.at(V, j), B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), B.at(V, j), Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), j), B.at(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), j), B.at(V, j), IM.at_bupd_other(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b, j, hc), IM.at_bupd_other(V, M.pos(1n+bp, h, dk), B.BE{}, j, hck))), L.subst(Bool, o => {B.implies(o, Bool.and(B.opx(IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j), M.pos(1n+bp, h, dk)), B.implies(Nat.is_lt(M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), M.pos(1n+bp, h, dk)), M.dist(1n+bp, B.hb(CY.msk(K), B.at(V, j)), j)), Nat.is_le(1n, M.dist(1n+bp, M.pos(1n+bp, h, dk), j))))) == True{} : Bool}, B.occ(B.at(V, j)), B.occ(B.at(V, j)), {==}, m_o(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv, j, hj, hck, B.all_inst(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp, hv, j, hj), B.occ(B.at(V, j)), {==})))

def m_i(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(h, j) == c : Bool}) -> {B.eval(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {B.eval(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, z) == True{} : Bool}, h, j, N.eq_from_is_eq(h, j, hc), m_at_h(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv))
    case False{}:
      m_k(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv, j, hj, hc, Nat.is_eq(M.pos(1n+bp, h, dk), j), {==})

def hole_move_m(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, 1n+bp, hm)
      L.and_intro(B.eval(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, j), B.all_lt(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, j), m_i(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv, j, hj, Nat.is_eq(h, j), {==}), hole_move_m(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv, j, N.lt_le(j, 1n+bp, hj)))

# THEOREM: moving the scanned bucket into the gap moves the gap to it
def hole_move(+K: Nat, +bp: Nat, +hN: {1n+bp == SC.pow2(K) : Nat}, +V: List<&2, B.Bk>, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +dk: Nat, +hd1: {Nat.is_le(1n, dk) == True{} : Bool}, +hdn: {Nat.is_lt(dk, 1n+bp) == True{} : Bool}, +b: B.Bk, +hbk: {B.at(V, M.pos(1n+bp, h, dk)) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hmv: {Nat.is_le(dk, M.dist(1n+bp, B.hb(CY.msk(K), b), M.pos(1n+bp, h, dk))) == True{} : Bool}, +hlen: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(M.pos(1n+bp, h, dk), SC.length(B.Bk, V)) == True{} : Bool}, +hv: {B.all_lt(B.PHole{V, 1n+bp, CY.msk(K), h, dk}, 1n+bp) == True{} : Bool}) -> {B.all_lt(B.PHole{IM.bupd(IM.bupd(V, M.pos(1n+bp, h, dk), B.BE{}), h, b), 1n+bp, CY.msk(K), M.pos(1n+bp, h, dk), 1n}, 1n+bp) == True{} : Bool}:
  hole_move_m(K, bp, hN, V, h, hh, dk, hd1, hdn, b, hbk, hbo, hmv, hlen, hlk, hv, 1n+bp, N.le_refl(1n+bp))
