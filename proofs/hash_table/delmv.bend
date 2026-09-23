import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./buckets.bend as B
import ./inv.bend as IV
import ./state.bend as ST
import ./lookup.bend as LK
import ./tools.bend as T
import ./insm.bend as IM
import ./rehash.bend as RH
import ./ring.bend as RG
import ./keys.bend as K2

# Moving the scanned bucket b from k into the empty gap h keeps the table a
# set of copies of the original buckets, keys and links unique, and the
# number of full buckets.


def hlen2(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}) -> {Nat.is_lt(h, SC.length(B.Bk, IM.bupd(V, k, B.BE{}))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(h, z) == True{} : Bool}, SC.length(B.Bk, V), SC.length(B.Bk, IM.bupd(V, k, B.BE{})), Equal.sym(Nat, SC.length(B.Bk, IM.bupd(V, k, B.BE{})), SC.length(B.Bk, V), RG.len_bupd(V, k, B.BE{})), hlh)

def at_vh(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}) -> {B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), h) == b : B.Bk}:
  IM.at_bupd_same(IM.bupd(V, k, B.BE{}), h, b, hlen2(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk))

def at_vk(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}) -> {B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), k) == B.BE{} : B.Bk}:
  Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), k), B.at(IM.bupd(V, k, B.BE{}), k), B.BE{}, IM.at_bupd_other(IM.bupd(V, k, B.BE{}), h, b, k, hhk), IM.at_bupd_same(V, k, B.BE{}, hlk))

def at_vo(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +j: Nat, +hh: {Nat.is_eq(h, j) == False{} : Bool}, +hk: {Nat.is_eq(k, j) == False{} : Bool}) -> {B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j) == B.at(V, j) : B.Bk}:
  Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), B.at(IM.bupd(V, k, B.BE{}), j), B.at(V, j), IM.at_bupd_other(IM.bupd(V, k, B.BE{}), h, b, j, hh), IM.at_bupd_other(V, k, B.BE{}, j, hk))

# ---- copies ----


def fm_o(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +m: Nat, +hf: {B.all_lt(B.PFrom{V, src, m}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +hch: {Nat.is_eq(h, j) == False{} : Bool}, +ck: Bool, +hck: {Nat.is_eq(k, j) == ck : Bool}) -> {B.eval(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, j) == True{} : Bool}:
  match ck:
    case True{}:
      +e = Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), k), B.BE{}, Equal.cong(Nat, B.Bk, z => B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), z), j, k, Equal.sym(Nat, k, j, N.eq_from_is_eq(k, j, hck))), at_vk(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk))
      L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(src, m, y)) == True{} : Bool}, B.BE{}, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), B.BE{}, e), {==})
    case False{}:
      L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(src, m, y)) == True{} : Bool}, B.at(V, j), B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), B.at(V, j), at_vo(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, j, hch, hck)), B.all_inst(B.PFrom{V, src, m}, n, hf, j, hj))

def fm_k(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +m: Nat, +hf: {B.all_lt(B.PFrom{V, src, m}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +ch: Bool, +hch: {Nat.is_eq(h, j) == ch : Bool}, +hkn: {Nat.is_lt(k, n) == True{} : Bool}) -> {B.eval(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, j) == True{} : Bool}:
  match ch:
    case True{}:
      +e = Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), h), b, Equal.cong(Nat, B.Bk, z => B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), z), j, h, Equal.sym(Nat, h, j, N.eq_from_is_eq(h, j, hch))), at_vh(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk))
      L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(src, m, y)) == True{} : Bool}, b, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), j), b, e), L.subst(B.Bk, y => {B.implies(B.occ(y), B.anyeq(src, m, y)) == True{} : Bool}, B.at(V, k), b, hbk, B.all_inst(B.PFrom{V, src, m}, n, hf, k, hkn)))
    case False{}:
      fm_o(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, m, hf, j, hj, hch, Nat.is_eq(k, j), {==})

def from_move_m(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +m: Nat, +hf: {B.all_lt(B.PFrom{V, src, m}, n) == True{} : Bool}, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, n) == True{} : Bool}) -> {B.all_lt(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hq)
      L.and_intro(B.eval(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, j), B.all_lt(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, j), fm_k(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, m, hf, j, hj, Nat.is_eq(h, j), {==}, hkn), from_move_m(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, m, hf, hkn, j, N.lt_le(j, n, hj)))

# THEOREM: after the move every full bucket is still a copy
def from_move(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +m: Nat, +hf: {B.all_lt(B.PFrom{V, src, m}, n) == True{} : Bool}, +hkn: {Nat.is_lt(k, n) == True{} : Bool}) -> {B.all_lt(B.PFrom{IM.bupd(IM.bupd(V, k, B.BE{}), h, b), src, m}, n) == True{} : Bool}:
  from_move_m(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, m, hf, hkn, n, N.le_refl(n))

def tw_c(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +x: B.Bk, +hox: {B.occ(x) == True{} : Bool}, +p: Nat, +hp: {Nat.is_lt(p, n) == True{} : Bool}, +hat: {B.at(V, p) == x : B.Bk}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(k, p) == c : Bool}) -> {B.anyeq(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x) == True{} : Bool}:
  match c:
    case True{}:
      +ebx = Equal.trans(B.Bk, b, B.at(V, k), x, Equal.sym(B.Bk, B.at(V, k), b, hbk), Equal.trans(B.Bk, B.at(V, k), B.at(V, p), x, Equal.cong(Nat, B.Bk, z => B.at(V, z), k, p, N.eq_from_is_eq(k, p, hc)), hat))
      RH.anyeq_intro(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x, h, hhn, L.subst(B.Bk, y => {B.bk_eq(y, x) == True{} : Bool}, x, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), h), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), h), x, Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), h), b, x, at_vh(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk), ebx)), RH.bk_refl(x)))
    case False{}:
      +hpo = L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, x, B.at(V, p), Equal.sym(B.Bk, B.at(V, p), x, hat), hox)
      +hhp = RH.ne_occ(V, h, hzh, p, hpo, Nat.is_eq(h, p), {==})
      RH.anyeq_intro(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x, p, hp, L.subst(B.Bk, y => {B.bk_eq(y, x) == True{} : Bool}, x, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), Equal.sym(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), x, Equal.trans(B.Bk, B.at(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), p), B.at(V, p), x, at_vo(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, p, hhp, hc), hat)), RH.bk_refl(x)))

def tw(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +x: B.Bk, +hox: {B.occ(x) == True{} : Bool}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}, w0: RH.EqAt(V, n, x)) -> {B.anyeq(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x) == True{} : Bool}:
  match w0:
    case Tuple{+p, Tuple{+hp, +hat}}:
      tw_c(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, x, hox, p, hp, hat, hhn, Nat.is_eq(k, p), {==})

def tm_i(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}, +x: B.Bk, +hx: {B.implies(B.occ(x), B.anyeq(V, n, x)) == True{} : Bool}, +c: Bool, +hc: {B.occ(x) == c : Bool}) -> {B.implies(c, B.anyeq(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x)) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      tw(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, x, hc, hhn, RH.find_eq(V, n, x, B.imp_elim(B.occ(x), B.anyeq(V, n, x), hx, hc)))

def to_move_m(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +ms: Nat, +ht: {B.all_lt(B.PTo{src, V, n}, ms) == True{} : Bool}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, ms) == True{} : Bool}) -> {B.all_lt(B.PTo{src, IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n}, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, ms, hq)
      +x = B.at(src, j)
      L.and_intro(B.eval(B.PTo{src, IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n}, j), B.all_lt(B.PTo{src, IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n}, j), L.subst(Bool, c => {B.implies(c, B.anyeq(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n, x)) == True{} : Bool}, B.occ(x), B.occ(x), {==}, tm_i(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, hhn, x, B.all_inst(B.PTo{src, V, n}, ms, ht, j, hj), B.occ(x), {==})), to_move_m(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, ms, ht, hhn, j, N.lt_le(j, ms, hj)))

# THEOREM: after the move every original bucket still has a copy
def to_move(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +src: List<&2, B.Bk>, +ms: Nat, +ht: {B.all_lt(B.PTo{src, V, n}, ms) == True{} : Bool}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}) -> {B.all_lt(B.PTo{src, IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n}, ms) == True{} : Bool}:
  to_move_m(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk, src, ms, ht, hhn, ms, N.le_refl(ms))

# ---- uniqueness ----

def uqr_b(+bs: List<&2, B.Bk>, +k: Nat, +hlk: {Nat.is_lt(k, SC.length(B.Bk, bs)) == True{} : Bool}, +j: Nat, +x: B.Bk, +hu: {B.uq_b(bs, j, x) == True{} : Bool}) -> {B.uq_b(IM.bupd(bs, k, B.BE{}), j, x) == True{} : Bool}:
  match x:
    case B.BE{}:
      {==}
    case B.BF{w, +l, +key}:
      L.and_intro(B.nohb(IM.bupd(bs, k, B.BE{}), key, j), B.nolb(IM.bupd(bs, k, B.BE{}), l, j), IM.nohb_up(bs, k, B.BE{}, hlk, key, {==}, j, L.and_left(B.nohb(bs, key, j), B.nolb(bs, l, j), hu)), IM.nolb_up(bs, k, B.BE{}, hlk, l, {==}, j, L.and_right(B.nohb(bs, key, j), B.nolb(bs, l, j), hu)))

def uqr_i(+bs: List<&2, B.Bk>, +k: Nat, +hlk: {Nat.is_lt(k, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(k, j) == c : Bool}) -> {B.eval(B.PUniq{IM.bupd(bs, k, B.BE{})}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {B.uq_b(IM.bupd(bs, k, B.BE{}), j, y) == True{} : Bool}, B.BE{}, B.at(IM.bupd(bs, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(bs, k, B.BE{}), j), B.BE{}, IM.at_bu_eq(bs, k, B.BE{}, hlk, j, hc)), {==})
    case False{}:
      L.subst(B.Bk, y => {B.uq_b(IM.bupd(bs, k, B.BE{}), j, y) == True{} : Bool}, B.at(bs, j), B.at(IM.bupd(bs, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(bs, k, B.BE{}), j), B.at(bs, j), IM.at_bupd_other(bs, k, B.BE{}, j, hc)), uqr_b(bs, k, hlk, j, B.at(bs, j), B.all_inst(B.PUniq{bs}, n, huq, j, hj)))

# THEOREM: emptying a bucket keeps keys and links unique
def uq_rm(+bs: List<&2, B.Bk>, +k: Nat, +hlk: {Nat.is_lt(k, SC.length(B.Bk, bs)) == True{} : Bool}, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PUniq{IM.bupd(bs, k, B.BE{})}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hm)
      L.and_intro(B.eval(B.PUniq{IM.bupd(bs, k, B.BE{})}, j), B.all_lt(B.PUniq{IM.bupd(bs, k, B.BE{})}, j), uqr_i(bs, k, hlk, n, huq, j, hj, Nat.is_eq(k, j), {==}), uq_rm(bs, k, hlk, n, huq, j, N.lt_le(j, n, hj)))


def pno_rm_i(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(k, j) == c : Bool}) -> {B.eval(B.PNo{IM.bupd(V, k, B.BE{}), key}, j) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(B.hold(key, y)) == True{} : Bool}, B.BE{}, B.at(IM.bupd(V, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(V, k, B.BE{}), j), B.BE{}, IM.at_bu_eq(V, k, B.BE{}, hlk, j, hc)), {==})
    case False{}:
      +hk = L.subst(B.Bk, y => {B.hold(key, y) == True{} : Bool}, B.BF{w, l, key}, B.at(V, k), Equal.sym(B.Bk, B.at(V, k), B.BF{w, l, key}, hbk), K2.str_refl(key))
      L.subst(B.Bk, y => {Bool.not(B.hold(key, y)) == True{} : Bool}, B.at(V, j), B.at(IM.bupd(V, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(V, k, B.BE{}), j), B.at(V, j), IM.at_bupd_other(V, k, B.BE{}, j, hc)), LK.other(V, n, key, huq, k, hkn, hk, j, hj, N.is_eq_sym_false(k, j, hc)))

def pno_rm(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PNo{IM.bupd(V, k, B.BE{}), key}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hm)
      L.and_intro(B.eval(B.PNo{IM.bupd(V, k, B.BE{}), key}, j), B.all_lt(B.PNo{IM.bupd(V, k, B.BE{}), key}, j), pno_rm_i(V, n, k, hkn, hlk, huq, w, l, key, hbk, j, hj, Nat.is_eq(k, j), {==}), pno_rm(V, n, k, hkn, hlk, huq, w, l, key, hbk, j, N.lt_le(j, n, hj)))

def nsr_o(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +hc: {Nat.is_eq(k, j) == False{} : Bool}, +o: Bool, +ho: {B.occ(B.at(V, j)) == o : Bool}) -> {Bool.not(Bool.and(o, Nat.is_eq(UD.v(H.slot(B.lnk(B.at(V, j)))), UD.v(H.slot(l))))) == True{} : Bool}:
  match o:
    case False{}:
      {==}
    case True{}:
      +ok = L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, B.BF{w, l, key}, B.at(V, k), Equal.sym(B.Bk, B.at(V, k), B.BF{w, l, key}, hbk), {==})
      +ne = T.slot_ne(V, n, huq, k, j, hkn, hj, N.is_eq_sym_false(k, j, hc), ok, ho)
      +ne2 = L.subst(B.Bk, y => {Nat.is_eq(UD.v(H.slot(B.lnk(B.at(V, j)))), UD.v(H.slot(B.lnk(y)))) == False{} : Bool}, B.at(V, k), B.BF{w, l, key}, hbk, ne)
      IM.not_f(Nat.is_eq(UD.v(H.slot(B.lnk(B.at(V, j)))), UD.v(H.slot(l))), ne2)

def nsr_i(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(k, j) == c : Bool}) -> {Bool.not(Bool.and(B.occ(B.at(IM.bupd(V, k, B.BE{}), j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(IM.bupd(V, k, B.BE{}), j)))), UD.v(H.slot(l))))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), UD.v(H.slot(l))))) == True{} : Bool}, B.BE{}, B.at(IM.bupd(V, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(V, k, B.BE{}), j), B.BE{}, IM.at_bu_eq(V, k, B.BE{}, hlk, j, hc)), {==})
    case False{}:
      L.subst(B.Bk, y => {Bool.not(Bool.and(B.occ(y), Nat.is_eq(UD.v(H.slot(B.lnk(y))), UD.v(H.slot(l))))) == True{} : Bool}, B.at(V, j), B.at(IM.bupd(V, k, B.BE{}), j), Equal.sym(B.Bk, B.at(IM.bupd(V, k, B.BE{}), j), B.at(V, j), IM.at_bupd_other(V, k, B.BE{}, j, hc)), nsr_o(V, n, k, hkn, hlk, huq, w, l, key, hbk, j, hj, hc, B.occ(B.at(V, j)), {==}))

def ns_rm(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {ST.noslot(IM.bupd(V, k, B.BE{}), UD.v(H.slot(l)), m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.succ_le_lt(j, n, hm)
      L.and_intro(Bool.not(Bool.and(B.occ(B.at(IM.bupd(V, k, B.BE{}), j)), Nat.is_eq(UD.v(H.slot(B.lnk(B.at(IM.bupd(V, k, B.BE{}), j)))), UD.v(H.slot(l))))), ST.noslot(IM.bupd(V, k, B.BE{}), UD.v(H.slot(l)), j), nsr_i(V, n, k, hkn, hlk, huq, w, l, key, hbk, j, hj, Nat.is_eq(k, j), {==}), ns_rm(V, n, k, hkn, hlk, huq, w, l, key, hbk, j, N.lt_le(j, n, hj)))


# THEOREM: moving a bucket into an empty bucket keeps keys and links unique
def uq_move(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{V}, n) == True{} : Bool}, +w: U32, +l: U32, +key: String, +hbk: {B.at(V, k) == B.BF{w, l, key} : B.Bk}, +h: Nat, +hhn: {Nat.is_lt(h, n) == True{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}) -> {B.all_lt(B.PUniq{IM.bupd(IM.bupd(V, k, B.BE{}), h, B.BF{w, l, key})}, n) == True{} : Bool}:
  +hl2 = L.subst(Nat, z => {Nat.is_lt(h, z) == True{} : Bool}, SC.length(B.Bk, V), SC.length(B.Bk, IM.bupd(V, k, B.BE{})), Equal.sym(Nat, SC.length(B.Bk, IM.bupd(V, k, B.BE{})), SC.length(B.Bk, V), RG.len_bupd(V, k, B.BE{})), hlh)
  IM.uq_up(IM.bupd(V, k, B.BE{}), h, hl2, w, l, key, n, hhn, uq_rm(V, k, hlk, n, huq, n, N.le_refl(n)), pno_rm(V, n, k, hkn, hlk, huq, w, l, key, hbk, n, N.le_refl(n)), ns_rm(V, n, k, hkn, hlk, huq, w, l, key, hbk, n, N.le_refl(n)))

# ---- the count ----

def bupd_self(+xs: List<&2, B.Bk>, +k: Nat) -> {IM.bupd(xs, k, B.at(xs, k)) == xs : List<&2, B.Bk>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+p:
      Equal.cong(List<&2, B.Bk>, List<&2, B.Bk>, z => Con{c, z}, IM.bupd(t, p, B.at(t, p)), t, bupd_self(t, p))

# emptying a full bucket k < n: one fewer full bucket
def occn_rm(+V: List<&2, B.Bk>, +n: Nat, +k: Nat, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +hok: {B.occ(B.at(V, k)) == True{} : Bool}) -> {IV.occn(V, n) == 1n+IV.occn(IM.bupd(V, k, B.BE{}), n) : Nat}:
  +hl2 = L.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, SC.length(B.Bk, V), SC.length(B.Bk, IM.bupd(V, k, B.BE{})), Equal.sym(Nat, SC.length(B.Bk, IM.bupd(V, k, B.BE{})), SC.length(B.Bk, V), RG.len_bupd(V, k, B.BE{})), hlk)
  +ev = Equal.trans(List<&2, B.Bk>, IM.bupd(IM.bupd(V, k, B.BE{}), k, B.at(V, k)), IM.bupd(V, k, B.at(V, k)), V, RG.bupd_over(V, k, B.BE{}, B.at(V, k)), bupd_self(V, k))
  Equal.trans(Nat, IV.occn(V, n), IV.occn(IM.bupd(IM.bupd(V, k, B.BE{}), k, B.at(V, k)), n), 1n+IV.occn(IM.bupd(V, k, B.BE{}), n), Equal.cong(List<&2, B.Bk>, Nat, z => IV.occn(z, n), V, IM.bupd(IM.bupd(V, k, B.BE{}), k, B.at(V, k)), Equal.sym(List<&2, B.Bk>, IM.bupd(IM.bupd(V, k, B.BE{}), k, B.at(V, k)), V, ev)), IM.occn_up(IM.bupd(V, k, B.BE{}), k, B.at(V, k), hok, hl2, IM.at_bupd_same(V, k, B.BE{}, hlk), n, hkn))

# THEOREM: the move keeps the number of full buckets
def occn_move(+V: List<&2, B.Bk>, +n: Nat, +h: Nat, +k: Nat, +b: B.Bk, +hbk: {B.at(V, k) == b : B.Bk}, +hbo: {B.occ(b) == True{} : Bool}, +hzh: {B.at(V, h) == B.BE{} : B.Bk}, +hhk: {Nat.is_eq(h, k) == False{} : Bool}, +hlh: {Nat.is_lt(h, SC.length(B.Bk, V)) == True{} : Bool}, +hlk: {Nat.is_lt(k, SC.length(B.Bk, V)) == True{} : Bool}, +hkn: {Nat.is_lt(k, n) == True{} : Bool}, +hhn: {Nat.is_lt(h, n) == True{} : Bool}) -> {IV.occn(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n) == IV.occn(V, n) : Nat}:
  +hok = L.subst(B.Bk, y => {B.occ(y) == True{} : Bool}, b, B.at(V, k), Equal.sym(B.Bk, B.at(V, k), b, hbk), hbo)
  +hzr = Equal.trans(B.Bk, B.at(IM.bupd(V, k, B.BE{}), h), B.at(V, h), B.BE{}, IM.at_bupd_other(V, k, B.BE{}, h, N.is_eq_sym_false(h, k, hhk)), hzh)
  Equal.trans(Nat, IV.occn(IM.bupd(IM.bupd(V, k, B.BE{}), h, b), n), 1n+IV.occn(IM.bupd(V, k, B.BE{}), n), IV.occn(V, n), IM.occn_up(IM.bupd(V, k, B.BE{}), h, b, hbo, hlen2(V, n, h, k, b, hbk, hbo, hzh, hhk, hlh, hlk), hzr, n, hhn), Equal.sym(Nat, IV.occn(V, n), 1n+IV.occn(IM.bupd(V, k, B.BE{}), n), occn_rm(V, n, k, hkn, hlk, hok)))
