import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/math/hash.bend as HS
import ./modn.bend as M
import ./keys.bend as K
import ../../../src/containers/hash_table.bend as H

# The bucket table as a list of n buckets, and the probe loop over it.
#   BE{}          an empty bucket
#   BF{w, l, k}   a full bucket: check word w, slot link l, holding key k

type Bk is Data:
  BE{}
  BF{w: U32, l: U32, k: String}

def at(bs: List<&2, Bk>, +i: Nat) -> Bk:
  match bs i:
    case Nil{} _:
      BE{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+p:
      at(t, p)

def occ(b: Bk) -> Bool:
  match b:
    case BE{}:
      False{}
    case BF{w, l, k}:
      True{}

# does bucket b hold key
def hold(+key: String, b: Bk) -> Bool:
  match b:
    case BE{}:
      False{}
    case BF{w, l, k}:
      S.str_eq(k, key)

# one probe step on bucket b
type MS is Data:
  MEnd{}
  MHit{l: U32}
  MNext{}

def mstep(+key: String, b: Bk) -> MS:
  match b:
    case BE{}:
      MEnd{}
    case BF{w, +l, k}:
      Bool.pick(MS, S.str_eq(k, key), MHit{l}, MNext{})

type Res is Data:
  RHit{at: Nat, l: U32}
  REnd{at: Nat}

# the probe loop, shaped as the implementation's find
def pf(+key: String, +bs: List<&2, Bk>, +n: Nat, fuel: Nat, s: MS, +i: Nat) -> Res:
  match fuel s:
    case 0n MEnd{}:
      REnd{i}
    case 0n MHit{l}:
      RHit{i, l}
    case 0n MNext{}:
      REnd{i}
    case 1n+p MEnd{}:
      REnd{i}
    case 1n+p MHit{l}:
      RHit{i, l}
    case 1n+p MNext{}:
      pf(key, bs, n, p, mstep(key, at(bs, Nat.mod(1n+i, n))), Nat.mod(1n+i, n))

# ---- invariants ----

# the home bucket of a full bucket's word
def hb(+mask: U32, b: Bk) -> Nat:
  match b:
    case BE{}:
      0n
    case BF{+w, l, k}:
      UD.v(HS.bucket(w, mask))

def hold_occ(+key: String, +b: Bk, +h: {hold(key, b) == True{} : Bool}) -> {occ(b) == True{} : Bool}:
  match b:
    case BE{}:
      Empty.absurd({occ(BE{}) == True{} : Bool}, L.false_true(h))
    case BF{w, l, k}:
      {==}

# the first m buckets from h are full
def occpath(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +m: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+s:
      Bool.and(occ(at(bs, M.pos(n, h, s))), occpath(bs, n, h, s))

# (an empty bucket's link is never read; 1 keeps slot(link) small)
def lnk(b: Bk) -> U32:
  match b:
    case BE{}:
      1
    case BF{w, l, k}:
      l

# no bucket below i holds key
def nohb(+bs: List<&2, Bk>, +key: String, +i: Nat) -> Bool:
  match i:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(Bool.not(hold(key, at(bs, j))), nohb(bs, key, j))

# no full bucket below i has link l
def nolb(+bs: List<&2, Bk>, +l: U32, +i: Nat) -> Bool:
  match i:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(Bool.not(Bool.and(occ(at(bs, j)), U32.is_eq(lnk(at(bs, j)), l))), nolb(bs, l, j))

def nthb(bs: List<&2, Bool>, +i: Nat) -> Bool:
  match bs i:
    case Nil{} _:
      False{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+p:
      nthb(t, p)

def uq_b(+bs: List<&2, Bk>, +i: Nat, b: Bk) -> Bool:
  match b:
    case BE{}:
      True{}
    case BF{w, +l, +k}:
      Bool.and(nohb(bs, k, i), nolb(bs, l, i))

def live_b(+lv: List<&2, Bool>, +f: Nat, b: Bk) -> Bool:
  match b:
    case BE{}:
      True{}
    case BF{w, +l, k}:
      Bool.and(nthb(lv, UD.v(H.slot(l))), Nat.is_lt(UD.v(H.slot(l)), f))

# equal buckets, as a Bool
def bk_eq(a: Bk, b: Bk) -> Bool:
  match a b:
    case BE{} BE{}:
      True{}
    case BE{} BF{w, l, k}:
      False{}
    case BF{w, l, k} BE{}:
      False{}
    case BF{+w, +l, +k} BF{+w2, +l2, +k2}:
      Bool.and(U32.is_eq(w, w2), Bool.and(U32.is_eq(l, l2), S.str_eq(k, k2)))

# some bucket below m equals b
def anyeq(+bs: List<&2, Bk>, +m: Nat, +b: Bk) -> Bool:
  match m:
    case 0n:
      False{}
    case 1n+j:
      Bool.or(bk_eq(at(bs, j), b), anyeq(bs, j, b))

# the first m buckets from a are full, except possibly the bucket at h
def opx(+bs: List<&2, Bk>, +n: Nat, +a: Nat, +m: Nat, +h: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+s:
      Bool.and(Bool.or(Nat.is_eq(h, M.pos(n, a, s)), occ(at(bs, M.pos(n, a, s)))), opx(bs, n, a, s, h))

# bounded quantifiers over first-order predicates
type Pred is Data:
  PClus{bs: List<&2, Bk>, n: Nat, mask: U32}
  PVis{bs: List<&2, Bk>, n: Nat, h: Nat, key: String}
  PHome{bs: List<&2, Bk>, mask: U32, key: String, h: Nat}
  PNo{bs: List<&2, Bk>, key: String}
  PWell{bs: List<&2, Bk>, sd: Nat}
  PUniq{bs: List<&2, Bk>}
  PLive{bs: List<&2, Bk>, lv: List<&2, Bool>, f: Nat}
  PFrom{bs: List<&2, Bk>, src: List<&2, Bk>, m: Nat}
  PTo{bs: List<&2, Bk>, dst: List<&2, Bk>, m: Nat}
  PHole{bs: List<&2, Bk>, n: Nat, mask: U32, h: Nat, dk: Nat}

def implies(a: Bool, b: Bool) -> Bool:
  Bool.or(Bool.not(a), b)

def imp_elim(+a: Bool, +b: Bool, +h: {implies(a, b) == True{} : Bool}, +ha: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, L.false_true(ha))

# a full bucket's link is a slot of the arena (2^sd slots) and its word is
# its key's word
def wb(+sd: Nat, b: Bk) -> Bool:
  match b:
    case BE{}:
      True{}
    case BF{+w, +l, +k}:
      Bool.and(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(w, K.kword(k)), Bool.not(U32.is_eq(l, 0))))

def eval(p: Pred, +i: Nat) -> Bool:
  match p:
    case PClus{+bs, +n, +mask}:
      implies(occ(at(bs, i)), occpath(bs, n, hb(mask, at(bs, i)), M.dist(n, hb(mask, at(bs, i)), i)))
    case PVis{+bs, +n, +h, +key}:
      Bool.and(occ(at(bs, M.pos(n, h, i))), Bool.not(hold(key, at(bs, M.pos(n, h, i)))))
    case PHome{+bs, +mask, +key, +h}:
      implies(hold(key, at(bs, i)), Nat.is_eq(hb(mask, at(bs, i)), h))
    case PNo{+bs, +key}:
      Bool.not(hold(key, at(bs, i)))
    case PWell{+bs, +sd}:
      wb(sd, at(bs, i))
    case PUniq{+bs}:
      uq_b(bs, i, at(bs, i))
    case PLive{+bs, +lv, +f}:
      live_b(lv, f, at(bs, i))
    case PFrom{+bs, +src, +m}:
      implies(occ(at(bs, i)), anyeq(src, m, at(bs, i)))
    case PTo{+bs, +dst, +m}:
      implies(occ(at(bs, i)), anyeq(dst, m, at(bs, i)))
    case PHole{+bs, +n, +mask, +h, +dk}:
      implies(occ(at(bs, i)), Bool.and(opx(bs, n, hb(mask, at(bs, i)), M.dist(n, hb(mask, at(bs, i)), i), h), implies(Nat.is_lt(M.dist(n, hb(mask, at(bs, i)), h), M.dist(n, hb(mask, at(bs, i)), i)), Nat.is_le(dk, M.dist(n, h, i)))))

# p(0) && ... && p(n - 1)
def all_lt(+p: Pred, +n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+q:
      Bool.and(eval(p, q), all_lt(p, q))

def all_inst_c(+p: Pred, +q: Nat, +h: {Bool.and(eval(p, q), all_lt(p, q)) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, q) == c : Bool}, rec: @hlt: {Nat.is_lt(i, q) == True{} : Bool} -> {eval(p, i) == True{} : Bool}) -> {eval(p, i) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {eval(p, z) == True{} : Bool}, q, i, Equal.sym(Nat, i, q, N.eq_from_is_eq(i, q, hc)), L.and_left(eval(p, q), all_lt(p, q), h))
    case False{}:
      rec(N.lt_or_eq(i, q, N.lt_succ_le(i, q, hi), hc))

# an instance of a bounded quantifier
def all_inst(+p: Pred, +n: Nat, +h: {all_lt(p, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}) -> {eval(p, i) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({eval(p, i) == True{} : Bool}, N.lt_zero_absurd(i, hi))
    case 1n+q:
      all_inst_c(p, q, h, i, hi, Nat.is_eq(i, q), {==}, hlt => all_inst(p, q, L.and_right(eval(p, q), all_lt(p, q), h), i, hlt))

def occ_c(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +q: Nat, +hp: {Bool.and(occ(at(bs, M.pos(n, h, q))), occpath(bs, n, h, q)) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, q) == c : Bool}, rec: @hlt: {Nat.is_lt(i, q) == True{} : Bool} -> {occ(at(bs, M.pos(n, h, i))) == True{} : Bool}) -> {occ(at(bs, M.pos(n, h, i))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {occ(at(bs, M.pos(n, h, z))) == True{} : Bool}, q, i, Equal.sym(Nat, i, q, N.eq_from_is_eq(i, q, hc)), L.and_left(occ(at(bs, M.pos(n, h, q))), occpath(bs, n, h, q), hp))
    case False{}:
      rec(N.lt_or_eq(i, q, N.lt_succ_le(i, q, hi), hc))

def occ_inst(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +m: Nat, +hp: {occpath(bs, n, h, m) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, m) == True{} : Bool}) -> {occ(at(bs, M.pos(n, h, i))) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({occ(at(bs, M.pos(n, h, i))) == True{} : Bool}, N.lt_zero_absurd(i, hi))
    case 1n+q:
      occ_c(bs, n, h, q, hp, i, hi, Nat.is_eq(i, q), {==}, hlt => occ_inst(bs, n, h, q, L.and_right(occ(at(bs, M.pos(n, h, q))), occpath(bs, n, h, q), hp), i, hlt))

def cluster(+bs: List<&2, Bk>, +n: Nat, +mask: U32) -> Bool:
  all_lt(PClus{bs, n, mask}, n)

# ---- the probe: correctness ----

def ResOK(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +key: String, r: Res) -> Type:
  match r:
    case RHit{+i, +l}:
      {Nat.is_lt(i, n) == True{} : Bool} & ({hold(key, at(bs, i)) == True{} : Bool} & {lnk(at(bs, i)) == l : U32})
    case REnd{+e}:
      {Nat.is_lt(e, n) == True{} : Bool} & ({at(bs, e) == BE{} : Bk} & ({occpath(bs, n, h, M.dist(n, h, e)) == True{} : Bool} & {all_lt(PNo{bs, key}, n) == True{} : Bool}))

def not_true_false(+e: {Bool.not(True{}) == True{} : Bool}) -> Empty:
  L.false_true(e)

def occ_be(+e: {occ(BE{}) == True{} : Bool}) -> Empty:
  L.false_true(e)

def occ_at_be(+bs: List<&2, Bk>, +i: Nat, +hz: {at(bs, i) == BE{} : Bk}, +ho: {occ(at(bs, i)) == True{} : Bool}) -> Empty:
  occ_be(L.subst(Bk, b => {occ(b) == True{} : Bool}, at(bs, i), BE{}, hz, ho))

# the probe stopped at the empty bucket pos(h, t), and d >= t is a full
# key's distance: impossible
def nh_far(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +t: Nat, +d: Nat, +hz: {at(bs, M.pos(n, h, t)) == BE{} : Bk}, +hp: {occpath(bs, n, h, d) == True{} : Bool}, +oj: {occ(at(bs, M.pos(n, h, d))) == True{} : Bool}, +htd: {Nat.is_le(t, d) == True{} : Bool}, +b2: Bool, +hb2: {Nat.is_eq(t, d) == b2 : Bool}) -> Empty:
  match b2:
    case True{}:
      occ_at_be(bs, M.pos(n, h, t), hz, L.subst(Nat, z => {occ(at(bs, M.pos(n, h, z))) == True{} : Bool}, d, t, Equal.sym(Nat, t, d, N.eq_from_is_eq(t, d, hb2)), oj))
    case False{}:
      occ_at_be(bs, M.pos(n, h, t), hz, occ_inst(bs, n, h, d, hp, t, N.lt_or_eq(t, d, htd, hb2)))

# ... and d < t is a visited bucket, which does not hold the key: impossible
def nh_near(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +t: Nat, +key: String, +d: Nat, +j: Nat, +hv: {all_lt(PVis{bs, n, h, key}, t) == True{} : Bool}, +hpj: {M.pos(n, h, d) == j : Nat}, +hk: {hold(key, at(bs, j)) == True{} : Bool}, +hdt: {Nat.is_lt(d, t) == True{} : Bool}) -> Empty:
  +vd = all_inst(PVis{bs, n, h, key}, t, hv, d, hdt)
  +nd = L.and_right(occ(at(bs, M.pos(n, h, d))), Bool.not(hold(key, at(bs, M.pos(n, h, d)))), vd)
  +nj = L.subst(Nat, z => {Bool.not(hold(key, at(bs, z))) == True{} : Bool}, M.pos(n, h, d), j, hpj, nd)
  not_true_false(L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, hold(key, at(bs, j)), True{}, hk, nj))

def nh_split(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +t: Nat, +key: String, +d: Nat, +j: Nat, +hv: {all_lt(PVis{bs, n, h, key}, t) == True{} : Bool}, +hz: {at(bs, M.pos(n, h, t)) == BE{} : Bk}, +hp: {occpath(bs, n, h, d) == True{} : Bool}, +hpj: {M.pos(n, h, d) == j : Nat}, +hk: {hold(key, at(bs, j)) == True{} : Bool}, +b1: Bool, +hb1: {Nat.is_lt(d, t) == b1 : Bool}) -> Empty:
  match b1:
    case True{}:
      nh_near(bs, n, h, t, key, d, j, hv, hpj, hk, hb1)
    case False{}:
      +oj = L.subst(Nat, z => {occ(at(bs, z)) == True{} : Bool}, j, M.pos(n, h, d), Equal.sym(Nat, M.pos(n, h, d), j, hpj), hold_occ(key, at(bs, j), hk))
      nh_far(bs, n, h, t, d, hz, hp, oj, N.not_lt_le(d, t, hb1), Nat.is_eq(t, d), {==})

def nh_c(+bs: List<&2, Bk>, +bp: Nat, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +cl: {cluster(bs, 1n+bp, mask) == True{} : Bool}, +ho: {all_lt(PHome{bs, mask, key, h}, 1n+bp) == True{} : Bool}, +t: Nat, +hv: {all_lt(PVis{bs, 1n+bp, h, key}, t) == True{} : Bool}, +hz: {at(bs, M.pos(1n+bp, h, t)) == BE{} : Bk}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +c: Bool, +hc: {hold(key, at(bs, j)) == c : Bool}) -> {Bool.not(hold(key, at(bs, j))) == True{} : Bool}:
  match c:
    case False{}:
      L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, hold(key, at(bs, j)), Equal.sym(Bool, hold(key, at(bs, j)), False{}, hc), {==})
    case True{}:
      +n = {1n+bp : Nat}
      +hbj = hb(mask, at(bs, j))
      +hom = N.eq_from_is_eq(hbj, h, imp_elim(hold(key, at(bs, j)), Nat.is_eq(hbj, h), all_inst(PHome{bs, mask, key, h}, n, ho, j, hj), hc))
      +clj = imp_elim(occ(at(bs, j)), occpath(bs, n, hbj, M.dist(n, hbj, j)), all_inst(PClus{bs, n, mask}, n, cl, j, hj), hold_occ(key, at(bs, j), hc))
      +hp = L.subst(Nat, z => {occpath(bs, n, z, M.dist(n, z, j)) == True{} : Bool}, hbj, h, hom, clj)
      Empty.absurd({Bool.not(hold(key, at(bs, j))) == True{} : Bool}, nh_split(bs, n, h, t, key, M.dist(n, h, j), j, hv, hz, hp, M.pos_dist(bp, h, j, hh, hj), hc, Nat.is_lt(M.dist(n, h, j), t), {==}))

def nh_all(+bs: List<&2, Bk>, +bp: Nat, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +cl: {cluster(bs, 1n+bp, mask) == True{} : Bool}, +ho: {all_lt(PHome{bs, mask, key, h}, 1n+bp) == True{} : Bool}, +t: Nat, +hv: {all_lt(PVis{bs, 1n+bp, h, key}, t) == True{} : Bool}, +hz: {at(bs, M.pos(1n+bp, h, t)) == BE{} : Bk}, +m: Nat, +hm: {Nat.is_le(m, 1n+bp) == True{} : Bool}) -> {all_lt(PNo{bs, key}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, 1n+bp, hm)
      L.and_intro(Bool.not(hold(key, at(bs, q))), all_lt(PNo{bs, key}, q), nh_c(bs, bp, mask, key, h, hh, cl, ho, t, hv, hz, q, hq, hold(key, at(bs, q)), {==}), nh_all(bs, bp, mask, key, h, hh, cl, ho, t, hv, hz, q, N.lt_le(q, 1n+bp, hq)))

def occ_of_vis(+bs: List<&2, Bk>, +n: Nat, +h: Nat, +key: String, +t: Nat, +hv: {all_lt(PVis{bs, n, h, key}, t) == True{} : Bool}) -> {occpath(bs, n, h, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      +hq = L.and_left(eval(PVis{bs, n, h, key}, q), all_lt(PVis{bs, n, h, key}, q), hv)
      L.and_intro(occ(at(bs, M.pos(n, h, q))), occpath(bs, n, h, q), L.and_left(occ(at(bs, M.pos(n, h, q))), Bool.not(hold(key, at(bs, M.pos(n, h, q)))), hq), occ_of_vis(bs, n, h, key, q, L.and_right(eval(PVis{bs, n, h, key}, q), all_lt(PVis{bs, n, h, key}, q), hv)))

# the step past pos(h, t) stays inside the table: the empty bucket e0 lies
# ahead
def next_in(+bs: List<&2, Bk>, +bp: Nat, +h: Nat, +key: String, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e0: Nat, +he0: {Nat.is_lt(e0, 1n+bp) == True{} : Bool}, +hz0: {at(bs, e0) == BE{} : Bk}, +t: Nat, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hv2: {all_lt(PVis{bs, 1n+bp, h, key}, 1n+t) == True{} : Bool}, +c: Bool, +hc: {Nat.is_lt(1n+t, 1n+bp) == c : Bool}) -> {Nat.is_lt(1n+t, 1n+bp) == True{} : Bool}:
  match c:
    case True{}:
      hc
    case False{}:
      +n = {1n+bp : Nat}
      +eq = N.le_antisym(1n+t, n, N.lt_succ_le_succ(t, n, ht), N.not_lt_le(1n+t, n, hc))
      +d0 = M.dist(n, h, e0)
      +hd0 = L.subst(Nat, z => {Nat.is_lt(d0, z) == True{} : Bool}, n, 1n+t, Equal.sym(Nat, 1n+t, n, eq), M.dist_lt(bp, h, e0))
      +v0 = all_inst(PVis{bs, n, h, key}, 1n+t, hv2, d0, hd0)
      +o0 = L.subst(Nat, z => {occ(at(bs, z)) == True{} : Bool}, M.pos(n, h, d0), e0, M.pos_dist(bp, h, e0, hh, he0), L.and_left(occ(at(bs, M.pos(n, h, d0))), Bool.not(hold(key, at(bs, M.pos(n, h, d0)))), v0))
      Empty.absurd({Nat.is_lt(1n+t, n) == True{} : Bool}, occ_at_be(bs, e0, hz0, o0))

def pf_bf(+bs: List<&2, Bk>, +bp: Nat, +key: String, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e0: Nat, +he0: {Nat.is_lt(e0, 1n+bp) == True{} : Bool}, +hz0: {at(bs, e0) == BE{} : Bk}, +fp: Nat, +t: Nat, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hv: {all_lt(PVis{bs, 1n+bp, h, key}, t) == True{} : Bool}, +x: U32, +l: U32, +k: String, +hb: {at(bs, M.pos(1n+bp, h, t)) == BF{x, l, k} : Bk}, +c: Bool, +hc: {S.str_eq(k, key) == c : Bool}, rec: @hv2: {all_lt(PVis{bs, 1n+bp, h, key}, 1n+t) == True{} : Bool} -> @ht2: {Nat.is_lt(1n+t, 1n+bp) == True{} : Bool} -> ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, fp, mstep(key, at(bs, M.pos(1n+bp, h, 1n+t))), M.pos(1n+bp, h, 1n+t)))) -> ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, 1n+fp, Bool.pick(MS, c, MHit{l}, MNext{}), M.pos(1n+bp, h, t))):
  match c:
    case True{}:
      (M.pos_lt(bp, h, t), (L.subst(Bk, b => {hold(key, b) == True{} : Bool}, BF{x, l, k}, at(bs, M.pos(1n+bp, h, t)), Equal.sym(Bk, at(bs, M.pos(1n+bp, h, t)), BF{x, l, k}, hb), hc), L.subst(Bk, b => {lnk(b) == l : U32}, BF{x, l, k}, at(bs, M.pos(1n+bp, h, t)), Equal.sym(Bk, at(bs, M.pos(1n+bp, h, t)), BF{x, l, k}, hb), {==})))
    case False{}:
      +vt = L.subst(Bk, b => {Bool.and(occ(b), Bool.not(hold(key, b))) == True{} : Bool}, BF{x, l, k}, at(bs, M.pos(1n+bp, h, t)), Equal.sym(Bk, at(bs, M.pos(1n+bp, h, t)), BF{x, l, k}, hb), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), False{}, hc), {==}))
      +hv2 = L.and_intro(eval(PVis{bs, 1n+bp, h, key}, t), all_lt(PVis{bs, 1n+bp, h, key}, t), vt, hv)
      +ht2 = next_in(bs, bp, h, key, hh, e0, he0, hz0, t, ht, hv2, Nat.is_lt(1n+t, 1n+bp), {==})
      L.subst(Nat, z => ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, fp, mstep(key, at(bs, z)), z)), M.pos(1n+bp, h, 1n+t), Nat.mod(1n+M.pos(1n+bp, h, t), 1n+bp), Equal.sym(Nat, Nat.mod(1n+M.pos(1n+bp, h, t), 1n+bp), M.pos(1n+bp, h, 1n+t), M.pos_next(bp, h, t)), rec(hv2, ht2))

def pf_b(+bs: List<&2, Bk>, +bp: Nat, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +cl: {cluster(bs, 1n+bp, mask) == True{} : Bool}, +ho: {all_lt(PHome{bs, mask, key, h}, 1n+bp) == True{} : Bool}, +e0: Nat, +he0: {Nat.is_lt(e0, 1n+bp) == True{} : Bool}, +hz0: {at(bs, e0) == BE{} : Bk}, +fp: Nat, +t: Nat, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hv: {all_lt(PVis{bs, 1n+bp, h, key}, t) == True{} : Bool}, +b: Bk, +hb: {at(bs, M.pos(1n+bp, h, t)) == b : Bk}, rec: @hv2: {all_lt(PVis{bs, 1n+bp, h, key}, 1n+t) == True{} : Bool} -> @ht2: {Nat.is_lt(1n+t, 1n+bp) == True{} : Bool} -> ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, fp, mstep(key, at(bs, M.pos(1n+bp, h, 1n+t))), M.pos(1n+bp, h, 1n+t)))) -> ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, 1n+fp, mstep(key, b), M.pos(1n+bp, h, t))):
  match b:
    case BE{}:
      +op = L.subst(Nat, z => {occpath(bs, 1n+bp, h, z) == True{} : Bool}, t, M.dist(1n+bp, h, M.pos(1n+bp, h, t)), Equal.sym(Nat, M.dist(1n+bp, h, M.pos(1n+bp, h, t)), t, M.dist_pos(bp, h, t, hh, ht)), occ_of_vis(bs, 1n+bp, h, key, t, hv))
      (M.pos_lt(bp, h, t), (hb, (op, nh_all(bs, bp, mask, key, h, hh, cl, ho, t, hv, hb, 1n+bp, N.le_refl(1n+bp)))))
    case BF{+x, +l, +k}:
      pf_bf(bs, bp, key, h, hh, e0, he0, hz0, fp, t, ht, hv, x, l, k, hb, S.str_eq(k, key), {==}, rec)

# THEOREM (bucket level): the probe from offset t of h, with the first t
# buckets full and not holding key and enough fuel, hits the bucket holding
# key or ends at an empty bucket whose path from h is full, key held nowhere.
def pf_ok(+bs: List<&2, Bk>, +bp: Nat, +mask: U32, +key: String, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +cl: {cluster(bs, 1n+bp, mask) == True{} : Bool}, +ho: {all_lt(PHome{bs, mask, key, h}, 1n+bp) == True{} : Bool}, +e0: Nat, +he0: {Nat.is_lt(e0, 1n+bp) == True{} : Bool}, +hz0: {at(bs, e0) == BE{} : Bk}, +f: Nat, +t: Nat, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hft: {Nat.add(t, f) == 1n+bp : Nat}, +hv: {all_lt(PVis{bs, 1n+bp, h, key}, t) == True{} : Bool}) -> ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, f, mstep(key, at(bs, M.pos(1n+bp, h, t))), M.pos(1n+bp, h, t))):
  match f:
    case 0n:
      +et = Equal.trans(Nat, t, Nat.add(t, 0n), 1n+bp, Equal.sym(Nat, Nat.add(t, 0n), t, N.add_zero(t)), hft)
      Empty.absurd(ResOK(bs, 1n+bp, h, key, pf(key, bs, 1n+bp, 0n, mstep(key, at(bs, M.pos(1n+bp, h, t))), M.pos(1n+bp, h, t))), N.lt_ne(t, 1n+bp, ht, et))
    case 1n+fp:
      +hft2 = Equal.trans(Nat, 1n+Nat.add(t, fp), Nat.add(t, 1n+fp), 1n+bp, Equal.sym(Nat, Nat.add(t, 1n+fp), 1n+Nat.add(t, fp), N.add_succ(t, fp)), hft)
      pf_b(bs, bp, mask, key, h, hh, cl, ho, e0, he0, hz0, fp, t, ht, hv, at(bs, M.pos(1n+bp, h, t)), {==}, hv2 => ht2 => pf_ok(bs, bp, mask, key, h, hh, cl, ho, e0, he0, hz0, fp, 1n+t, ht2, hft2, hv2))
