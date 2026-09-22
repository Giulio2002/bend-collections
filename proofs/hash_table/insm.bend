import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./buckets.bend as B
import ./modn.bend as M
import ./inv.bend as IV
import ../lib/u32alg.bend as A
import ./keys.bend as K2
import ./state.bend as ST
import ./tools.bend as T
import ./setv.bend as SV
import ./lookup.bend as LK
import ./speclem.bend as SL
import ./size.bend as SZ

# Inserting a full bucket into an empty one, at the bucket level.

def bupd(bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk) -> List<&2, B.Bk>:
  match bs e:
    case Nil{} _:
      Nil{}
    case Con{c, t} 0n:
      Con{b, t}
    case Con{c, t} 1n+p:
      Con{c, bupd(t, p, b)}

def at_bupd_same(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +h: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}) -> {B.at(bupd(bs, e, b), e) == b : B.Bk}:
  match bs e:
    case Nil{} _:
      Empty.absurd({B.at(bupd(Nil{}, e, b), e) == b : B.Bk}, N.lt_zero_absurd(e, h))
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+p:
      at_bupd_same(t, p, b, h)

def at_bupd_other(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +j: Nat, +h: {Nat.is_eq(e, j) == False{} : Bool}) -> {B.at(bupd(bs, e, b), j) == B.at(bs, j) : B.Bk}:
  match bs e j:
    case Nil{} _ _:
      {==}
    case Con{c, t} 0n 0n:
      Empty.absurd({B.at(bupd(Con{c, t}, 0n, b), 0n) == B.at(Con{c, t}, 0n) : B.Bk}, L.true_false(h))
    case Con{c, t} 0n 1n+q:
      {==}
    case Con{c, t} 1n+p 0n:
      {==}
    case Con{c, t} 1n+p 1n+q:
      at_bupd_other(t, p, b, q, h)

# ---- occupancy only grows ----

def occ_up_c(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +x: Nat, +h: {B.occ(B.at(bs, x)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, x) == c : Bool}) -> {B.occ(B.at(bupd(bs, e, b), x)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {B.occ(B.at(bupd(bs, e, b), z)) == True{} : Bool}, e, x, N.eq_from_is_eq(e, x, hc), L.subst(B.Bk, bb => {B.occ(bb) == True{} : Bool}, b, B.at(bupd(bs, e, b), e), Equal.sym(B.Bk, B.at(bupd(bs, e, b), e), b, at_bupd_same(bs, e, b, he)), hb))
    case False{}:
      L.subst(B.Bk, bb => {B.occ(bb) == True{} : Bool}, B.at(bs, x), B.at(bupd(bs, e, b), x), Equal.sym(B.Bk, B.at(bupd(bs, e, b), x), B.at(bs, x), at_bupd_other(bs, e, b, x, hc)), h)

def occ_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +x: Nat, +h: {B.occ(B.at(bs, x)) == True{} : Bool}) -> {B.occ(B.at(bupd(bs, e, b), x)) == True{} : Bool}:
  occ_up_c(bs, e, b, hb, he, x, h, Nat.is_eq(e, x), {==})

def occpath_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +h: Nat, +m: Nat, +hp: {B.occpath(bs, n, h, m) == True{} : Bool}) -> {B.occpath(bupd(bs, e, b), n, h, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+s:
      L.and_intro(B.occ(B.at(bupd(bs, e, b), M.pos(n, h, s))), B.occpath(bupd(bs, e, b), n, h, s), occ_up(bs, e, b, hb, he, M.pos(n, h, s), L.and_left(B.occ(B.at(bs, M.pos(n, h, s))), B.occpath(bs, n, h, s), hp)), occpath_up(bs, e, b, hb, he, n, h, s, L.and_right(B.occ(B.at(bs, M.pos(n, h, s))), B.occpath(bs, n, h, s), hp)))

def at_bu_eq(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +j: Nat, +hc: {Nat.is_eq(e, j) == True{} : Bool}) -> {B.at(bupd(bs, e, b), j) == b : B.Bk}:
  L.subst(Nat, z => {B.at(bupd(bs, e, b), z) == b : B.Bk}, e, j, N.eq_from_is_eq(e, j, hc), at_bupd_same(bs, e, b, he))

# ---- the cluster property ----

def imp_occ(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +h: Nat, +m: Nat, +a: Bool, +hi: {B.implies(a, B.occpath(bs, n, h, m)) == True{} : Bool}) -> {B.implies(a, B.occpath(bupd(bs, e, b), n, h, m)) == True{} : Bool}:
  match a:
    case True{}:
      occpath_up(bs, e, b, hb, he, n, h, m, hi)
    case False{}:
      {==}

def clus_i(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +mask: U32, +hp: {B.occpath(bs, n, B.hb(mask, b), M.dist(n, B.hb(mask, b), e)) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {B.eval(B.PClus{bupd(bs, e, b), n, mask}, j) == True{} : Bool}:
  match c:
    case True{}:
      +hp1 = L.subst(Bool, a => {B.implies(a, B.occpath(bs, n, B.hb(mask, b), M.dist(n, B.hb(mask, b), e))) == True{} : Bool}, True{}, B.occ(b), Equal.sym(Bool, B.occ(b), True{}, hb), hp)
      +p0 = L.subst(B.Bk, x => {B.implies(B.occ(x), B.occpath(bupd(bs, e, b), n, B.hb(mask, x), M.dist(n, B.hb(mask, x), e))) == True{} : Bool}, b, B.at(bupd(bs, e, b), e), Equal.sym(B.Bk, B.at(bupd(bs, e, b), e), b, at_bupd_same(bs, e, b, he)), imp_occ(bs, e, b, hb, he, n, B.hb(mask, b), M.dist(n, B.hb(mask, b), e), B.occ(b), hp1))
      L.subst(Nat, z => {B.eval(B.PClus{bupd(bs, e, b), n, mask}, z) == True{} : Bool}, e, j, N.eq_from_is_eq(e, j, hc), p0)
    case False{}:
      +old = B.all_inst(B.PClus{bs, n, mask}, n, cl, j, hj)
      L.subst(B.Bk, x => {B.implies(B.occ(x), B.occpath(bupd(bs, e, b), n, B.hb(mask, x), M.dist(n, B.hb(mask, x), j))) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, hc)), imp_occ(bs, e, b, hb, he, n, B.hb(mask, B.at(bs, j)), M.dist(n, B.hb(mask, B.at(bs, j)), j), B.occ(B.at(bs, j)), old))

def clus_m(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +mask: U32, +hp: {B.occpath(bs, n, B.hb(mask, b), M.dist(n, B.hb(mask, b), e)) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PClus{bupd(bs, e, b), n, mask}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.eval(B.PClus{bupd(bs, e, b), n, mask}, q), B.all_lt(B.PClus{bupd(bs, e, b), n, mask}, q), clus_i(bs, e, b, hb, he, n, mask, hp, cl, q, hq, Nat.is_eq(e, q), {==}), clus_m(bs, e, b, hb, he, n, mask, hp, cl, q, N.lt_le(q, n, hq)))

# THEOREM: filling the empty bucket e that ends b's probe keeps the clusters
def clus_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +mask: U32, +hp: {B.occpath(bs, n, B.hb(mask, b), M.dist(n, B.hb(mask, b), e)) == True{} : Bool}, +cl: {B.cluster(bs, n, mask) == True{} : Bool}) -> {B.cluster(bupd(bs, e, b), n, mask) == True{} : Bool}:
  clus_m(bs, e, b, hb, he, n, mask, hp, cl, n, N.le_refl(n))

# ---- well-formed buckets ----

def well_i(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +sd: Nat, +hwb: {B.wb(sd, b) == True{} : Bool}, +n: Nat, +hw: {B.all_lt(B.PWell{bs, sd}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {B.eval(B.PWell{bupd(bs, e, b), sd}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, x => {B.wb(sd, x) == True{} : Bool}, b, B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), b, at_bu_eq(bs, e, b, he, j, hc)), hwb)
    case False{}:
      L.subst(B.Bk, x => {B.wb(sd, x) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, hc)), B.all_inst(B.PWell{bs, sd}, n, hw, j, hj))

def well_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +sd: Nat, +hwb: {B.wb(sd, b) == True{} : Bool}, +n: Nat, +hw: {B.all_lt(B.PWell{bs, sd}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PWell{bupd(bs, e, b), sd}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.eval(B.PWell{bupd(bs, e, b), sd}, q), B.all_lt(B.PWell{bupd(bs, e, b), sd}, q), well_i(bs, e, b, he, sd, hwb, n, hw, q, hq, Nat.is_eq(e, q), {==}), well_up(bs, e, b, he, sd, hwb, n, hw, q, N.lt_le(q, n, hq)))

# ---- occupancy count ----

def occn_lo(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +m: Nat, +hm: {Nat.is_le(m, e) == True{} : Bool}) -> {IV.occn(bupd(bs, e, b), m) == IV.occn(bs, m) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, e, hm)
      +ne = N.is_eq_sym_false(q, e, N.is_eq_lt(q, e, hq))
      Equal.trans(Nat, Nat.add(IV.bitv(B.occ(B.at(bupd(bs, e, b), q))), IV.occn(bupd(bs, e, b), q)), Nat.add(IV.bitv(B.occ(B.at(bs, q))), IV.occn(bupd(bs, e, b), q)), Nat.add(IV.bitv(B.occ(B.at(bs, q))), IV.occn(bs, q)),
        Equal.cong(B.Bk, Nat, x => Nat.add(IV.bitv(B.occ(x)), IV.occn(bupd(bs, e, b), q)), B.at(bupd(bs, e, b), q), B.at(bs, q), at_bupd_other(bs, e, b, q, ne)),
        Equal.cong(Nat, Nat, z => Nat.add(IV.bitv(B.occ(B.at(bs, q))), z), IV.occn(bupd(bs, e, b), q), IV.occn(bs, q), occn_lo(bs, e, b, q, N.lt_le(q, e, hq))))

def occn_at(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}) -> {IV.occn(bupd(bs, e, b), 1n+e) == 1n+IV.occn(bs, 1n+e) : Nat}:
  +lo = occn_lo(bs, e, b, e, N.le_refl(e))
  +a1 = Equal.cong(B.Bk, Nat, x => Nat.add(IV.bitv(B.occ(x)), IV.occn(bupd(bs, e, b), e)), B.at(bupd(bs, e, b), e), b, at_bupd_same(bs, e, b, he))
  +a2 = Equal.cong(Bool, Nat, o => Nat.add(IV.bitv(o), IV.occn(bupd(bs, e, b), e)), B.occ(b), True{}, hb)
  +a3 = Equal.cong(B.Bk, Nat, x => 1n+Nat.add(IV.bitv(B.occ(x)), IV.occn(bs, e)), B.BE{}, B.at(bs, e), Equal.sym(B.Bk, B.at(bs, e), B.BE{}, hz))
  Equal.trans(Nat, IV.occn(bupd(bs, e, b), 1n+e), Nat.add(IV.bitv(B.occ(b)), IV.occn(bupd(bs, e, b), e)), 1n+IV.occn(bs, 1n+e), a1,
    Equal.trans(Nat, Nat.add(IV.bitv(B.occ(b)), IV.occn(bupd(bs, e, b), e)), 1n+IV.occn(bupd(bs, e, b), e), 1n+IV.occn(bs, 1n+e), a2,
      Equal.trans(Nat, 1n+IV.occn(bupd(bs, e, b), e), 1n+IV.occn(bs, e), 1n+IV.occn(bs, 1n+e), Equal.cong(Nat, Nat, z => 1n+z, IV.occn(bupd(bs, e, b), e), IV.occn(bs, e), lo), a3)))

def occn_hi_s(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +q: Nat, +ne: {Nat.is_eq(e, 1n+q) == False{} : Bool}, +ih: {IV.occn(bupd(bs, e, b), 1n+q) == 1n+IV.occn(bs, 1n+q) : Nat}) -> {IV.occn(bupd(bs, e, b), 2n+q) == 1n+IV.occn(bs, 2n+q) : Nat}:
  +x = IV.bitv(B.occ(B.at(bs, 1n+q)))
  Equal.trans(Nat, Nat.add(IV.bitv(B.occ(B.at(bupd(bs, e, b), 1n+q))), IV.occn(bupd(bs, e, b), 1n+q)), Nat.add(x, IV.occn(bupd(bs, e, b), 1n+q)), 1n+IV.occn(bs, 2n+q),
    Equal.cong(B.Bk, Nat, y => Nat.add(IV.bitv(B.occ(y)), IV.occn(bupd(bs, e, b), 1n+q)), B.at(bupd(bs, e, b), 1n+q), B.at(bs, 1n+q), at_bupd_other(bs, e, b, 1n+q, ne)),
    Equal.trans(Nat, Nat.add(x, IV.occn(bupd(bs, e, b), 1n+q)), Nat.add(x, 1n+IV.occn(bs, 1n+q)), 1n+IV.occn(bs, 2n+q), Equal.cong(Nat, Nat, z => Nat.add(x, z), IV.occn(bupd(bs, e, b), 1n+q), 1n+IV.occn(bs, 1n+q), ih), N.add_succ(x, IV.occn(bs, 1n+q))))

def occn_hi_c(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +p: Nat, +hq: {Nat.is_le(e, 1n+p) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, 1n+p) == c : Bool}, rec: @hep: {Nat.is_le(e, p) == True{} : Bool} -> {IV.occn(bupd(bs, e, b), 1n+p) == 1n+IV.occn(bs, 1n+p) : Nat}) -> {IV.occn(bupd(bs, e, b), 2n+p) == 1n+IV.occn(bs, 2n+p) : Nat}:
  match c:
    case True{}:
      L.subst(Nat, z => {IV.occn(bupd(bs, e, b), 1n+z) == 1n+IV.occn(bs, 1n+z) : Nat}, e, 1n+p, N.eq_from_is_eq(e, 1n+p, hc), occn_at(bs, e, b, hb, he, hz))
    case False{}:
      occn_hi_s(bs, e, b, p, hc, rec(N.lt_succ_le(e, p, N.lt_or_eq(e, 1n+p, hq, hc))))

def occn_hi(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +q: Nat, +hq: {Nat.is_le(e, q) == True{} : Bool}) -> {IV.occn(bupd(bs, e, b), 1n+q) == 1n+IV.occn(bs, 1n+q) : Nat}:
  match q:
    case 0n:
      L.subst(Nat, z => {IV.occn(bupd(bs, e, b), 1n+z) == 1n+IV.occn(bs, 1n+z) : Nat}, e, 0n, N.le_antisym(e, 0n, hq, N.zero_le(e)), occn_at(bs, e, b, hb, he, hz))
    case 1n+p:
      occn_hi_c(bs, e, b, hb, he, hz, p, hq, Nat.is_eq(e, 1n+p), {==}, hep => occn_hi(bs, e, b, hb, he, hz, p, hep))

# THEOREM: filling an empty bucket e < n adds one full bucket among the first n
def occn_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +hb: {B.occ(b) == True{} : Bool}, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}) -> {IV.occn(bupd(bs, e, b), n) == 1n+IV.occn(bs, n) : Nat}:
  match n:
    case 0n:
      Empty.absurd({IV.occn(bupd(bs, e, b), 0n) == 1n+IV.occn(bs, 0n) : Nat}, N.lt_zero_absurd(e, hen))
    case 1n+q:
      occn_hi(bs, e, b, hb, he, hz, q, N.lt_succ_le(e, q, hen))

# ---- no earlier bucket holds a key / has a link ----

def nohb_below(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +k: String, +i: Nat, +hi: {Nat.is_le(i, e) == True{} : Bool}, +h: {B.nohb(bs, k, i) == True{} : Bool}) -> {B.nohb(bupd(bs, e, b), k, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      +hje = N.succ_le_lt(j, e, hi)
      +ne = N.is_eq_sym_false(j, e, N.is_eq_lt(j, e, hje))
      L.and_intro(Bool.not(B.hold(k, B.at(bupd(bs, e, b), j))), B.nohb(bupd(bs, e, b), k, j), L.subst(B.Bk, x => {Bool.not(B.hold(k, x)) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, ne)), L.and_left(Bool.not(B.hold(k, B.at(bs, j))), B.nohb(bs, k, j), h)), nohb_below(bs, e, b, k, j, N.lt_le(j, e, hje), L.and_right(Bool.not(B.hold(k, B.at(bs, j))), B.nohb(bs, k, j), h)))

def nh_pt(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +k: String, +hnb: {Bool.not(B.hold(k, b)) == True{} : Bool}, +j: Nat, +h0: {Bool.not(B.hold(k, B.at(bs, j))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {Bool.not(B.hold(k, B.at(bupd(bs, e, b), j))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, x => {Bool.not(B.hold(k, x)) == True{} : Bool}, b, B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), b, at_bu_eq(bs, e, b, he, j, hc)), hnb)
    case False{}:
      L.subst(B.Bk, x => {Bool.not(B.hold(k, x)) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, hc)), h0)

def nohb_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +k: String, +hnb: {Bool.not(B.hold(k, b)) == True{} : Bool}, +i: Nat, +h: {B.nohb(bs, k, i) == True{} : Bool}) -> {B.nohb(bupd(bs, e, b), k, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(Bool.not(B.hold(k, B.at(bupd(bs, e, b), j))), B.nohb(bupd(bs, e, b), k, j), nh_pt(bs, e, b, he, k, hnb, j, L.and_left(Bool.not(B.hold(k, B.at(bs, j))), B.nohb(bs, k, j), h), Nat.is_eq(e, j), {==}), nohb_up(bs, e, b, he, k, hnb, j, L.and_right(Bool.not(B.hold(k, B.at(bs, j))), B.nohb(bs, k, j), h)))

def nolb_below(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +l: U32, +i: Nat, +hi: {Nat.is_le(i, e) == True{} : Bool}, +h: {B.nolb(bs, l, i) == True{} : Bool}) -> {B.nolb(bupd(bs, e, b), l, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      +hje = N.succ_le_lt(j, e, hi)
      +ne = N.is_eq_sym_false(j, e, N.is_eq_lt(j, e, hje))
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bupd(bs, e, b), j)), U32.is_eq(B.lnk(B.at(bupd(bs, e, b), j)), l))), B.nolb(bupd(bs, e, b), l, j), L.subst(B.Bk, x => {Bool.not(Bool.and(B.occ(x), U32.is_eq(B.lnk(x), l))) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, ne)), L.and_left(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), h)), nolb_below(bs, e, b, l, j, N.lt_le(j, e, hje), L.and_right(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), h)))

def nl_pt(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +l: U32, +hnb: {Bool.not(Bool.and(B.occ(b), U32.is_eq(B.lnk(b), l))) == True{} : Bool}, +j: Nat, +h0: {Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bupd(bs, e, b), j)), U32.is_eq(B.lnk(B.at(bupd(bs, e, b), j)), l))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, x => {Bool.not(Bool.and(B.occ(x), U32.is_eq(B.lnk(x), l))) == True{} : Bool}, b, B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), b, at_bu_eq(bs, e, b, he, j, hc)), hnb)
    case False{}:
      L.subst(B.Bk, x => {Bool.not(Bool.and(B.occ(x), U32.is_eq(B.lnk(x), l))) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, b), j), Equal.sym(B.Bk, B.at(bupd(bs, e, b), j), B.at(bs, j), at_bupd_other(bs, e, b, j, hc)), h0)

def nolb_up(+bs: List<&2, B.Bk>, +e: Nat, +b: B.Bk, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +l: U32, +hnb: {Bool.not(Bool.and(B.occ(b), U32.is_eq(B.lnk(b), l))) == True{} : Bool}, +i: Nat, +h: {B.nolb(bs, l, i) == True{} : Bool}) -> {B.nolb(bupd(bs, e, b), l, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bupd(bs, e, b), j)), U32.is_eq(B.lnk(B.at(bupd(bs, e, b), j)), l))), B.nolb(bupd(bs, e, b), l, j), nl_pt(bs, e, b, he, l, hnb, j, L.and_left(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), h), Nat.is_eq(e, j), {==}), nolb_up(bs, e, b, he, l, hnb, j, L.and_right(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), h)))

# no bucket holds key: none below i does
def nohb_pno(+bs: List<&2, B.Bk>, +key: String, +n: Nat, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_le(i, n) == True{} : Bool}) -> {B.nohb(bs, key, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hi)
      L.and_intro(Bool.not(B.hold(key, B.at(bs, j))), B.nohb(bs, key, j), B.all_inst(B.PNo{bs, key}, n, hno, j, hj), nohb_pno(bs, key, n, hno, j, N.lt_le(j, n, hj)))

# ---- slot links ----

def u32_ne_c(+a: U32, +l: U32, +h: {Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))) == False{} : Bool}, +c: Bool, +hc: {U32.is_eq(a, l) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +r = L.subst(U32, z => {Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(z))) == False{} : Bool}, l, a, Equal.sym(U32, a, l, A.eq_of(a, l, hc)), h)
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(a))), False{}, Equal.sym(Bool, Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(a))), True{}, N.is_eq_refl(UD.v(H.slot(a)))), r)))

# links with different slots differ
def u32_ne(+a: U32, +l: U32, +h: {Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))) == False{} : Bool}) -> {U32.is_eq(a, l) == False{} : Bool}:
  u32_ne_c(a, l, h, U32.is_eq(a, l), {==})

def not_f(+b: Bool, +h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, b, Equal.sym(Bool, b, False{}, h), {==})

def nl_bit(+o: Bool, +a: U32, +l: U32, +h: {Bool.not(Bool.and(o, Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))))) == True{} : Bool}) -> {Bool.not(Bool.and(o, U32.is_eq(a, l))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      not_f(U32.is_eq(a, l), u32_ne(a, l, K2.not_true_eq(Nat.is_eq(UD.v(H.slot(a)), UD.v(H.slot(l))), h)))

# no full bucket uses the slot of l: none has link l
def nolb_noslot(+bs: List<&2, B.Bk>, +l: U32, +m: Nat, +h: {ST.noslot(bs, UD.v(H.slot(l)), m) == True{} : Bool}) -> {B.nolb(bs, l, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +x = Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), UD.v(H.slot(l)))))
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), nl_bit(B.occ(B.at(bs, j)), B.lnk(B.at(bs, j)), l, L.and_left(x, ST.noslot(bs, UD.v(H.slot(l)), j), h)), nolb_noslot(bs, l, j, L.and_right(x, ST.noslot(bs, UD.v(H.slot(l)), j), h)))

def nolb_pre(+bs: List<&2, B.Bk>, +l: U32, +n: Nat, +h: {B.nolb(bs, l, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.nolb(bs, l, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hm)
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bs, j)), U32.is_eq(B.lnk(B.at(bs, j)), l))), B.nolb(bs, l, j), T.nolb_inst(bs, l, n, h, j, hj), nolb_pre(bs, l, n, h, j, N.lt_le(j, n, hj)))

def noslot_c(+bs: List<&2, B.Bk>, +s: Nat, +q: Nat, +h: {Bool.and(Bool.not(Bool.and(B.occ(B.at(bs, q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, q)))), s))), ST.noslot(bs, s, q)) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hlt: {Nat.is_lt(j, q) == True{} : Bool} -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), s))) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), s))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.not(Bool.and(B.occ(B.at(bs, z)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, z)))), s))) == True{} : Bool}, q, j, Equal.sym(Nat, j, q, N.eq_from_is_eq(j, q, hc)), L.and_left(Bool.not(Bool.and(B.occ(B.at(bs, q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, q)))), s))), ST.noslot(bs, s, q), h))
    case False{}:
      rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc))

def noslot_inst(+bs: List<&2, B.Bk>, +s: Nat, +m: Nat, +h: {ST.noslot(bs, s, m) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), s))) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), s))) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      noslot_c(bs, s, q, h, j, hj, Nat.is_eq(j, q), {==}, hlt => noslot_inst(bs, s, q, L.and_right(Bool.not(Bool.and(B.occ(B.at(bs, q)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, q)))), s))), ST.noslot(bs, s, q), h), j, hlt))

# a full bucket that does not use slot s has a slot other than s
def slot_other(+b: B.Bk, +s: Nat, +ho: {B.occ(b) == True{} : Bool}, +h: {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), s))) == True{} : Bool}) -> {Nat.is_eq(UD.v(H.slot(B.lnk(b))), s) == False{} : Bool}:
  K2.not_true_eq(Nat.is_eq(UD.v(H.slot(B.lnk(b))), s), L.subst(Bool, o => {Bool.not(Bool.and(o, Nat.is_eq(UD.v(H.slot(B.lnk(b))), s))) == True{} : Bool}, B.occ(b), True{}, ho, h))

# ---- uniqueness ----

def uq_oth(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +l: U32, +key: String, +i: Nat, +b: B.Bk, +hu: {B.uq_b(bs, i, b) == True{} : Bool}, +hpn: {Bool.not(B.hold(key, b)) == True{} : Bool}, +hns: {Bool.not(Bool.and(B.occ(b), Nat.is_eq(UD.v(H.slot(B.lnk(b))), UD.v(H.slot(l))))) == True{} : Bool}) -> {B.uq_b(bupd(bs, e, B.BF{w, l, key}), i, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w2, +l2, +k2}:
      +e1 = K2.not_true_eq(S.str_eq(k2, key), hpn)
      +e2 = Equal.trans(Bool, S.str_eq(key, k2), S.str_eq(k2, key), False{}, K2.str_sym(key, k2), e1)
      +hk = not_f(S.str_eq(key, k2), e2)
      +f1 = K2.not_true_eq(Nat.is_eq(UD.v(H.slot(l2)), UD.v(H.slot(l))), hns)
      +hl = not_f(U32.is_eq(l, l2), u32_ne(l, l2, N.is_eq_sym_false(UD.v(H.slot(l2)), UD.v(H.slot(l)), f1)))
      L.and_intro(B.nohb(bupd(bs, e, B.BF{w, l, key}), k2, i), B.nolb(bupd(bs, e, B.BF{w, l, key}), l2, i), nohb_up(bs, e, B.BF{w, l, key}, he, k2, hk, i, L.and_left(B.nohb(bs, k2, i), B.nolb(bs, l2, i), hu)), nolb_up(bs, e, B.BF{w, l, key}, he, l2, hl, i, L.and_right(B.nohb(bs, k2, i), B.nolb(bs, l2, i), hu)))

def uq_i(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {B.eval(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, j) == True{} : Bool}:
  match c:
    case True{}:
      +u0 = L.and_intro(B.nohb(bupd(bs, e, B.BF{w, L, key}), key, e), B.nolb(bupd(bs, e, B.BF{w, L, key}), L, e), nohb_below(bs, e, B.BF{w, L, key}, key, e, N.le_refl(e), nohb_pno(bs, key, n, hno, e, N.lt_le(e, n, hen))), nolb_below(bs, e, B.BF{w, L, key}, L, e, N.le_refl(e), nolb_pre(bs, L, n, nolb_noslot(bs, L, n, hns), e, N.lt_le(e, n, hen))))
      +u1 = L.subst(B.Bk, x => {B.uq_b(bupd(bs, e, B.BF{w, L, key}), e, x) == True{} : Bool}, B.BF{w, L, key}, B.at(bupd(bs, e, B.BF{w, L, key}), e), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), e), B.BF{w, L, key}, at_bupd_same(bs, e, B.BF{w, L, key}, he)), u0)
      L.subst(Nat, z => {B.eval(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, z) == True{} : Bool}, e, j, N.eq_from_is_eq(e, j, hc), u1)
    case False{}:
      +u0 = uq_oth(bs, e, he, w, L, key, j, B.at(bs, j), B.all_inst(B.PUniq{bs}, n, huq, j, hj), B.all_inst(B.PNo{bs, key}, n, hno, j, hj), noslot_inst(bs, UD.v(H.slot(L)), n, hns, j, hj))
      L.subst(B.Bk, x => {B.uq_b(bupd(bs, e, B.BF{w, L, key}), j, x) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.at(bs, j), at_bupd_other(bs, e, B.BF{w, L, key}, j, hc)), u0)

def uq_m(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.eval(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, q), B.all_lt(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, q), uq_i(bs, e, he, w, L, key, n, hen, huq, hno, hns, q, hq, Nat.is_eq(e, q), {==}), uq_m(bs, e, he, w, L, key, n, hen, huq, hno, hns, q, N.lt_le(q, n, hq)))

# THEOREM: a key held nowhere, in a slot used nowhere, keeps keys and links unique
def uq_up(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}) -> {B.all_lt(B.PUniq{bupd(bs, e, B.BF{w, L, key})}, n) == True{} : Bool}:
  uq_m(bs, e, he, w, L, key, n, hen, huq, hno, hns, n, N.le_refl(n))

# ---- liveness ----

def live_mono(+lv: List<&2, Bool>, +f: Nat, +f2: Nat, +hle: {Nat.is_le(f, f2) == True{} : Bool}, +b: B.Bk, +h: {B.live_b(lv, f, b) == True{} : Bool}) -> {B.live_b(lv, f2, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, k}:
      L.and_intro(B.nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), f2), L.and_left(B.nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), f), h), N.lt_le_trans(UD.v(H.slot(l)), f, f2, L.and_right(B.nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), f), h), hle))

def live_new(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +w: U32, +L: U32, +key: String, +x: V, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +fr2: Nat, +hs2: {Nat.is_lt(UD.v(H.slot(L)), fr2) == True{} : Bool}) -> {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2, B.BF{w, L, key}) == True{} : Bool}:
  +a = Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), UD.v(H.slot(L))), ST.some_b(~V, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(L)))), True{}, ST.lvs_nth(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(L))), Equal.cong(Maybe<&2, V>, Bool, m => ST.some_b(~V, m), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(L))), Some{x}, T.nthm_upd_same(~V, vsl, UD.v(H.slot(L)), Some{x}, hs)))
  L.and_intro(B.nthb(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), UD.v(H.slot(L))), Nat.is_lt(UD.v(H.slot(L)), fr2), a, hs2)

def live_i(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +fr: Nat, +fr2: Nat, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +hs2: {Nat.is_lt(UD.v(H.slot(L)), fr2) == True{} : Bool}, +n: Nat, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {B.eval(B.PLive{bupd(bs, e, B.BF{w, L, key}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2, y) == True{} : Bool}, B.BF{w, L, key}, B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.BF{w, L, key}, at_bu_eq(bs, e, B.BF{w, L, key}, he, j, hc)), live_new(~V, vsl, w, L, key, x, hs, fr2, hs2))
    case False{}:
      L.subst(B.Bk, y => {B.live_b(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2, y) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.at(bs, j), at_bupd_other(bs, e, B.BF{w, L, key}, j, hc)), live_mono(ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr, fr2, hle, B.at(bs, j), SV.lv_b(~V, vsl, UD.v(H.slot(L)), x, fr, hs, B.at(bs, j), B.all_inst(B.PLive{bs, ST.lvs(~V, vsl), fr}, n, hl, j, hj))))

# THEOREM: the new bucket's slot holds a value and is below the new fresh mark
def live_up(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +fr: Nat, +fr2: Nat, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +hs2: {Nat.is_lt(UD.v(H.slot(L)), fr2) == True{} : Bool}, +n: Nat, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PLive{bupd(bs, e, B.BF{w, L, key}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.eval(B.PLive{bupd(bs, e, B.BF{w, L, key}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2}, q), B.all_lt(B.PLive{bupd(bs, e, B.BF{w, L, key}), ST.lvs(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x})), fr2}, q), live_i(~V, bs, e, he, w, L, key, vsl, x, hs, fr, fr2, hle, hs2, n, hl, q, hq, Nat.is_eq(e, q), {==}), live_up(~V, bs, e, he, w, L, key, vsl, x, hs, fr, fr2, hle, hs2, n, hl, q, N.lt_le(q, n, hq)))

# ---- other keys and slots ----

def pno_i(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +n: Nat, +hno: {B.all_lt(B.PNo{bs, q}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> {B.eval(B.PNo{bupd(bs, e, B.BF{w, L, key}), q}, j) == True{} : Bool}:
  nh_pt(bs, e, B.BF{w, L, key}, he, q, not_f(S.str_eq(key, q), hq), j, B.all_inst(B.PNo{bs, q}, n, hno, j, hj), Nat.is_eq(e, j), {==})

def pno_up(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +n: Nat, +hno: {B.all_lt(B.PNo{bs, q}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PNo{bupd(bs, e, B.BF{w, L, key}), q}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hp = N.succ_le_lt(p, n, hm)
      L.and_intro(B.eval(B.PNo{bupd(bs, e, B.BF{w, L, key}), q}, p), B.all_lt(B.PNo{bupd(bs, e, B.BF{w, L, key}), q}, p), pno_i(bs, e, he, w, L, key, q, hq, n, hno, p, hp), pno_up(bs, e, he, w, L, key, q, hq, n, hno, p, N.lt_le(p, n, hp)))

def ns_pt(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +t: Nat, +hst: {Nat.is_eq(UD.v(H.slot(L)), t) == False{} : Bool}, +j: Nat, +h0: {Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), t))) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(bupd(bs, e, B.BF{w, L, key}), j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), j)))), t))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), t))) == True{} : Bool}, B.BF{w, L, key}, B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.BF{w, L, key}, at_bu_eq(bs, e, B.BF{w, L, key}, he, j, hc)), not_f(Nat.is_eq(UD.v(H.slot(L)), t), hst))
    case False{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), t))) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.at(bs, j), at_bupd_other(bs, e, B.BF{w, L, key}, j, hc)), h0)

# THEOREM: a slot other than the new one is still used by no bucket
def noslot_up(+bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +t: Nat, +hst: {Nat.is_eq(UD.v(H.slot(L)), t) == False{} : Bool}, +m: Nat, +h: {ST.noslot(bs, t, m) == True{} : Bool}) -> {ST.noslot(bupd(bs, e, B.BF{w, L, key}), t, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +x = Bool.not(Bool.and(B.occ(B.at(bs, j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, j)))), t)))
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(bupd(bs, e, B.BF{w, L, key}), j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), j)))), t))), ST.noslot(bupd(bs, e, B.BF{w, L, key}), t, j), ns_pt(bs, e, he, w, L, key, t, hst, j, L.and_left(x, ST.noslot(bs, t, j), h), Nat.is_eq(e, j), {==}), noslot_up(bs, e, he, w, L, key, t, hst, j, L.and_right(x, ST.noslot(bs, t, j), h)))

# ---- the model after the insertion ----


def ne_empty(+bs: List<&2, B.Bk>, +e: Nat, +q: String, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +j: Nat, +hk: {B.hold(q, B.at(bs, j)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(e, j) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +h1 = L.subst(Nat, z => {B.hold(q, B.at(bs, z)) == True{} : Bool}, j, e, Equal.sym(Nat, e, j, N.eq_from_is_eq(e, j, hc)), hk)
      Empty.absurd({True{} == False{} : Bool}, L.false_true(L.subst(B.Bk, y => {B.hold(q, y) == True{} : Bool}, B.at(bs, e), B.BE{}, hz, h1)))

def lk_held(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +q: String, e0: T.Holder(bs, q, n)) -> {S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q) == S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q) : Maybe<&2, V>}:
  match e0:
    case Tuple{+j, Tuple{+hj, +hkj}}:
      +ne = ne_empty(bs, e, q, hz, j, hkj, Nat.is_eq(e, j), {==})
      +eat = at_bupd_other(bs, e, B.BF{w, L, key}, j, ne)
      +hkj2 = L.subst(B.Bk, y => {B.hold(q, y) == True{} : Bool}, B.at(bs, j), B.at(bupd(bs, e, B.BF{w, L, key}), j), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), j), B.at(bs, j), eat), hkj)
      +sj = UD.v(H.slot(B.lnk(B.at(bs, j))))
      +hne = N.is_eq_sym_false(sj, UD.v(H.slot(L)), slot_other(B.at(bs, j), UD.v(H.slot(L)), B.hold_occ(q, B.at(bs, j), hkj), noslot_inst(bs, UD.v(H.slot(L)), n, hns, j, hj)))
      +huq2 = uq_up(bs, e, he, w, L, key, n, hen, huq, hno, hns)
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), j))))), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), LK.lookup_hit(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), q, n, huq2, j, hj, hkj2),
        Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), j))))), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), sj), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), Equal.cong(B.Bk, Maybe<&2, V>, y => ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(y)))), B.at(bupd(bs, e, B.BF{w, L, key}), j), B.at(bs, j), eat),
          Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), sj), ST.nthm(~V, vsl, sj), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), T.nthm_upd_other(~V, vsl, UD.v(H.slot(L)), sj, Some{x}, hne), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), ST.nthm(~V, vsl, sj), LK.lookup_hit(~V, bs, vsl, q, n, huq, j, hj, hkj)))))

def lk_other(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +q: String, +hq: {S.str_eq(key, q) == False{} : Bool}, +d: Bool, +hd: {B.all_lt(B.PNo{bs, q}, n) == d : Bool}) -> {S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q) == S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q) : Maybe<&2, V>}:
  match d:
    case True{}:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q), None{}, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), LK.lookup_none(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), q, n, pno_up(bs, e, he, w, L, key, q, hq, n, hd, n, N.le_refl(n))), Equal.sym(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), None{}, LK.lookup_none(~V, bs, vsl, q, n, hd)))
    case False{}:
      lk_held(~V, bs, e, he, w, L, key, vsl, x, n, hen, hs, hz, huq, hno, hns, q, T.find_hold(bs, q, n, hd))

def lk_c(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +q: String, +c: Bool, +hc: {S.str_eq(key, q) == c : Bool}) -> {S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q) == S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q) : Maybe<&2, V>}:
  match c:
    case True{}:
      +huq2 = uq_up(bs, e, he, w, L, key, n, hen, huq, hno, hns)
      +eat = at_bupd_same(bs, e, B.BF{w, L, key}, he)
      +hk2 = L.subst(B.Bk, y => {B.hold(q, y) == True{} : Bool}, B.BF{w, L, key}, B.at(bupd(bs, e, B.BF{w, L, key}), e), Equal.sym(B.Bk, B.at(bupd(bs, e, B.BF{w, L, key}), e), B.BF{w, L, key}, eat), hc)
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), e))))), S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), LK.lookup_hit(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), q, n, huq2, e, hen, hk2),
        Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(B.at(bupd(bs, e, B.BF{w, L, key}), e))))), ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(L))), S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), Equal.cong(B.Bk, Maybe<&2, V>, y => ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(B.lnk(y)))), B.at(bupd(bs, e, B.BF{w, L, key}), e), B.BF{w, L, key}, eat),
          Equal.trans(Maybe<&2, V>, ST.nthm(~V, SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), UD.v(H.slot(L))), Some{x}, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), T.nthm_upd_same(~V, vsl, UD.v(H.slot(L)), Some{x}, hs), Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), Some{x}, SL.lookup_set_same(~V, ST.absm(~V, bs, vsl, n, 0n), key, x, q, hc)))))
    case False{}:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), lk_other(~V, bs, e, he, w, L, key, vsl, x, n, hen, hs, hz, huq, hno, hns, q, hc, B.all_lt(B.PNo{bs, q}, n), {==}), Equal.sym(Maybe<&2, V>, S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q), S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), q), SL.lookup_set_other(~V, ST.absm(~V, bs, vsl, n, 0n), key, x, q, hc)))

# THEOREM: putting an absent key into an empty bucket, with its value in an
# unused slot, looks every key up as the specification's set does
def lookup_ins(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +q: String) -> {S.lookup(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n), q) == S.lookup(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x), q) : Maybe<&2, V>}:
  lk_c(~V, bs, e, he, w, L, key, vsl, x, n, hen, hs, hz, huq, hno, hns, q, S.str_eq(key, q), {==})

# THEOREM: ... and adds one entry
def size_ins(~V: Data, +bs: List<&2, B.Bk>, +e: Nat, +he: {Nat.is_lt(e, SC.length(B.Bk, bs)) == True{} : Bool}, +w: U32, +L: U32, +key: String, +vsl: List<&2, Maybe<&2, V>>, +x: V, +n: Nat, +hen: {Nat.is_lt(e, n) == True{} : Bool}, +hs: {Nat.is_lt(UD.v(H.slot(L)), SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +hz: {B.at(bs, e) == B.BE{} : B.Bk}, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +hns: {ST.noslot(bs, UD.v(H.slot(L)), n) == True{} : Bool}, +fr: Nat, +fr2: Nat, +hle: {Nat.is_le(fr, fr2) == True{} : Bool}, +hs2: {Nat.is_lt(UD.v(H.slot(L)), fr2) == True{} : Bool}, +hl: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), fr}, n) == True{} : Bool}) -> {S.size(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n)) == S.size(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x)) : Nat}:
  Equal.trans(Nat, S.size(~V, ST.absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), n, 0n)), IV.occn(bupd(bs, e, B.BF{w, L, key}), n), S.size(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x)), SZ.size_absm(~V, bupd(bs, e, B.BF{w, L, key}), SC.update(Maybe<&2, V>, vsl, UD.v(H.slot(L)), Some{x}), fr2, n, live_up(~V, bs, e, he, w, L, key, vsl, x, hs, fr, fr2, hle, hs2, n, hl, n, N.le_refl(n)), n, N.le_refl(n)),
    Equal.trans(Nat, IV.occn(bupd(bs, e, B.BF{w, L, key}), n), 1n+IV.occn(bs, n), S.size(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x)), occn_up(bs, e, B.BF{w, L, key}, {==}, he, hz, n, hen),
      Equal.trans(Nat, 1n+IV.occn(bs, n), 1n+S.size(~V, ST.absm(~V, bs, vsl, n, 0n)), S.size(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x)), Equal.cong(Nat, Nat, z => 1n+z, IV.occn(bs, n), S.size(~V, ST.absm(~V, bs, vsl, n, 0n)), Equal.sym(Nat, S.size(~V, ST.absm(~V, bs, vsl, n, 0n)), IV.occn(bs, n), SZ.size_absm(~V, bs, vsl, fr, n, hl, n, N.le_refl(n)))), Equal.sym(Nat, S.size(~V, S.set(~V, ST.absm(~V, bs, vsl, n, 0n), key, x)), 1n+S.size(~V, ST.absm(~V, bs, vsl, n, 0n)), SL.size_set_new(~V, ST.absm(~V, bs, vsl, n, 0n), key, x, LK.lookup_none(~V, bs, vsl, key, n, hno))))))
