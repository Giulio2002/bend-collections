import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./state.bend as ST
import ./insa.bend as IA
import ../../lib/words32.bend as W32

# Growing the slot arena: the arrays gain a second half of blank cells, and
# every bucket, liveness fact and model entry reads the first half only.


# the blank value half
def vac_eq(~V: Data, +d: Nat) -> {H.vac(&2, V, d) == AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, d, None{})) : Array<Maybe<&2, V>>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Array<Maybe<&2, V>>, ANode{H.vac(&2, V, p), H.vac(&2, V, p)}, ANode{AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), H.vac(&2, V, p)}, AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, 1n+p, None{})), Equal.cong(Array<Maybe<&2, V>>, Array<Maybe<&2, V>>, a => ANode{a, H.vac(&2, V, p)}, H.vac(&2, V, p), AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), vac_eq(~V, p)), Equal.cong(Array<Maybe<&2, V>>, Array<Maybe<&2, V>>, a => ANode{AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), a}, H.vac(&2, V, p), AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), vac_eq(~V, p)))

# ---- reading the first half ----

def nths_app(+xs: List<&2, String>, +r: List<&2, String>, +t: Nat, +h: {Nat.is_lt(t, SC.length(String, xs)) == True{} : Bool}) -> {TB.nths(SC.append(String, xs, r), t) == TB.nths(xs, t) : String}:
  match xs t:
    case Nil{} _:
      Empty.absurd({TB.nths(SC.append(String, Nil{}, r), t) == TB.nths(Nil{}, t) : String}, N.lt_zero_absurd(t, h))
    case Con{x, u} 0n:
      {==}
    case Con{x, u} 1n+p:
      nths_app(u, r, p, h)

def nthm_app(~V: Data, +xs: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +t: Nat, +h: {Nat.is_lt(t, SC.length(Maybe<&2, V>, xs)) == True{} : Bool}) -> {ST.nthm(~V, SC.append(Maybe<&2, V>, xs, r), t) == ST.nthm(~V, xs, t) : Maybe<&2, V>}:
  match xs t:
    case Nil{} _:
      Empty.absurd({ST.nthm(~V, SC.append(Maybe<&2, V>, Nil{}, r), t) == ST.nthm(~V, Nil{}, t) : Maybe<&2, V>}, N.lt_zero_absurd(t, h))
    case Con{x, u} 0n:
      {==}
    case Con{x, u} 1n+p:
      nthm_app(~V, u, r, p, h)

def nthb_app(~V: Data, +xs: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +t: Nat, +h: {Nat.is_lt(t, SC.length(Maybe<&2, V>, xs)) == True{} : Bool}) -> {B.nthb(ST.lvs(~V, SC.append(Maybe<&2, V>, xs, r)), t) == B.nthb(ST.lvs(~V, xs), t) : Bool}:
  Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.append(Maybe<&2, V>, xs, r)), t), ST.some_b(~V, ST.nthm(~V, SC.append(Maybe<&2, V>, xs, r), t)), B.nthb(ST.lvs(~V, xs), t), ST.lvs_nth(~V, SC.append(Maybe<&2, V>, xs, r), t), Equal.trans(Bool, ST.some_b(~V, ST.nthm(~V, SC.append(Maybe<&2, V>, xs, r), t)), ST.some_b(~V, ST.nthm(~V, xs, t)), B.nthb(ST.lvs(~V, xs), t), Equal.cong(Maybe<&2, V>, Bool, m => ST.some_b(~V, m), ST.nthm(~V, SC.append(Maybe<&2, V>, xs, r), t), ST.nthm(~V, xs, t), nthm_app(~V, xs, r, t, h)), Equal.sym(Bool, B.nthb(ST.lvs(~V, xs), t), ST.some_b(~V, ST.nthm(~V, xs, t)), ST.lvs_nth(~V, xs, t))))

def len_eq_lt(-T: Data, +xs: List<&2, T>, +d: Nat, +hl: {SC.length(T, xs) == SC.pow2(d) : Nat}, +t: Nat, +h: {Nat.is_lt(t, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(t, SC.length(T, xs)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(t, z) == True{} : Bool}, SC.pow2(d), SC.length(T, xs), Equal.sym(Nat, SC.length(T, xs), SC.pow2(d), hl), h)

# ---- buckets ----

def dec_app_c(+w: U32, +l: U32, +kl: List<&2, String>, +r: List<&2, String>, +sd: Nat, +hlen: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +emp: Bool, +h: {B.wb(sd, TB.dec_c(w, l, kl, emp)) == True{} : Bool}) -> {TB.dec_c(w, l, SC.append(String, kl, r), emp) == TB.dec_c(w, l, kl, emp) : B.Bk}:
  match emp:
    case True{}:
      {==}
    case False{}:
      +hs = L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(w, K.kword(TB.keyof(w, TB.nths(kl, UD.v(H.slot(l)))))), Bool.not(U32.is_eq(l, 0))), h)
      Equal.cong(String, B.Bk, z => B.BF{w, l, TB.keyof(w, z)}, TB.nths(SC.append(String, kl, r), UD.v(H.slot(l))), TB.nths(kl, UD.v(H.slot(l))), nths_app(kl, r, UD.v(H.slot(l)), len_eq_lt(String, kl, sd, hlen, UD.v(H.slot(l)), hs)))


def dl_app(+tb: List<&2, U32>, +kl: List<&2, String>, +r: List<&2, String>, +sd: Nat, +hlen: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +n: Nat, +hw: {B.all_lt(B.PWell{TB.buckets(tb, kl, n), sd}, n) == True{} : Bool}, +m: Nat, +i: Nat, +hmi: {Nat.is_le(Nat.add(i, m), n) == True{} : Bool}) -> {TB.dlist(tb, SC.append(String, kl, r), m, i) == TB.dlist(tb, kl, m, i) : List<&2, B.Bk>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hi = IA.idx_lt(i, p, n, hmi)
      +hwi = L.subst(B.Bk, y => {B.wb(sd, y) == True{} : Bool}, B.at(TB.buckets(tb, kl, n), i), TB.dec(tb, kl, i), TB.at_buckets(tb, kl, n, i, hi), B.all_inst(B.PWell{TB.buckets(tb, kl, n), sd}, n, hw, i, hi))
      IA.con_eq(TB.dec(tb, SC.append(String, kl, r), i), TB.dec(tb, kl, i), TB.dlist(tb, SC.append(String, kl, r), p, 1n+i), TB.dlist(tb, kl, p, 1n+i), dec_app_c(W32.nth0(tb, Nat.double(i)), W32.nth0(tb, 1n+Nat.double(i)), kl, r, sd, hlen, U32.is_eq(W32.nth0(tb, Nat.double(i)), 0), hwi), dl_app(tb, kl, r, sd, hlen, n, hw, p, 1n+i, IA.idx_next(i, p, n, hmi)))

# THEOREM: appending cells to the key arena leaves every bucket as it was
def bs_app(+tb: List<&2, U32>, +kl: List<&2, String>, +r: List<&2, String>, +sd: Nat, +hlen: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +n: Nat, +hw: {B.all_lt(B.PWell{TB.buckets(tb, kl, n), sd}, n) == True{} : Bool}) -> {TB.buckets(tb, SC.append(String, kl, r), n) == TB.buckets(tb, kl, n) : List<&2, B.Bk>}:
  dl_app(tb, kl, r, sd, hlen, n, hw, n, 0n, N.le_refl(n))

# ---- invariants over the first half ----

def wb_mono(+sd: Nat, +sd2: Nat, +hle: {Nat.is_le(SC.pow2(sd), SC.pow2(sd2)) == True{} : Bool}, +b: B.Bk, +h: {B.wb(sd, b) == True{} : Bool}) -> {B.wb(sd2, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +rest = Bool.and(U32.is_eq(w, K.kword(k)), Bool.not(U32.is_eq(l, 0)))
      L.and_intro(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd2)), rest, N.lt_le_trans(UD.v(H.slot(l)), SC.pow2(sd), SC.pow2(sd2), L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), rest, h), hle), L.and_right(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), rest, h))

def well_mono(+bs: List<&2, B.Bk>, +sd: Nat, +sd2: Nat, +hle: {Nat.is_le(SC.pow2(sd), SC.pow2(sd2)) == True{} : Bool}, +n: Nat, +h: {B.all_lt(B.PWell{bs, sd}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PWell{bs, sd2}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.wb(sd2, B.at(bs, q)), B.all_lt(B.PWell{bs, sd2}, q), wb_mono(sd, sd2, hle, B.at(bs, q), B.all_inst(B.PWell{bs, sd}, n, h, q, hq)), well_mono(bs, sd, sd2, hle, n, h, q, N.lt_le(q, n, hq)))

def live_app_b(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +f: Nat, +hf: {Nat.is_le(f, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +b: B.Bk, +h: {B.live_b(ST.lvs(~V, vsl), f, b) == True{} : Bool}) -> {B.live_b(ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), f, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, k}:
      +t = UD.v(H.slot(l))
      +ht = L.and_right(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, f), h)
      +e = nthb_app(~V, vsl, r, t, N.lt_le_trans(t, f, SC.length(Maybe<&2, V>, vsl), ht, hf))
      L.and_intro(B.nthb(ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), t), Nat.is_lt(t, f), Equal.trans(Bool, B.nthb(ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), t), B.nthb(ST.lvs(~V, vsl), t), True{}, e, L.and_left(B.nthb(ST.lvs(~V, vsl), t), Nat.is_lt(t, f), h)), ht)

def live_app(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +f: Nat, +hf: {Nat.is_le(f, SC.length(Maybe<&2, V>, vsl)) == True{} : Bool}, +n: Nat, +h: {B.all_lt(B.PLive{bs, ST.lvs(~V, vsl), f}, n) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, n) == True{} : Bool}) -> {B.all_lt(B.PLive{bs, ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), f}, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, n, hm)
      L.and_intro(B.live_b(ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), f, B.at(bs, q)), B.all_lt(B.PLive{bs, ST.lvs(~V, SC.append(Maybe<&2, V>, vsl, r)), f}, q), live_app_b(~V, vsl, r, f, hf, B.at(bs, q), B.all_inst(B.PLive{bs, ST.lvs(~V, vsl), f}, n, h, q, hq)), live_app(~V, bs, vsl, r, f, hf, n, h, q, N.lt_le(q, n, hq)))

# ---- the model ----

def ent_app(~V: Data, +vsl: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +sd: Nat, +hlen: {SC.length(Maybe<&2, V>, vsl) == SC.pow2(sd) : Nat}, +b: B.Bk, +h: {B.wb(sd, b) == True{} : Bool}) -> {ST.ent(~V, b, SC.append(Maybe<&2, V>, vsl, r)) == ST.ent(~V, b, vsl) : List<&2, S.Entry<V>>}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +hs = L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(w, K.kword(k)), Bool.not(U32.is_eq(l, 0))), h)
      Equal.cong(Maybe<&2, V>, List<&2, S.Entry<V>>, m => ST.ent_m(~V, k, m), ST.nthm(~V, SC.append(Maybe<&2, V>, vsl, r), UD.v(H.slot(l))), ST.nthm(~V, vsl, UD.v(H.slot(l))), nthm_app(~V, vsl, r, UD.v(H.slot(l)), len_eq_lt(Maybe<&2, V>, vsl, sd, hlen, UD.v(H.slot(l)), hs)))

def absm_app(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +r: List<&2, Maybe<&2, V>>, +sd: Nat, +hlen: {SC.length(Maybe<&2, V>, vsl) == SC.pow2(sd) : Nat}, +n: Nat, +hw: {B.all_lt(B.PWell{bs, sd}, n) == True{} : Bool}, +m: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, m), n) == True{} : Bool}) -> {ST.absm(~V, bs, SC.append(Maybe<&2, V>, vsl, r), m, j) == ST.absm(~V, bs, vsl, m, j) : List<&2, S.Entry<V>>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hj = IA.idx_lt(j, p, n, hjm)
      Equal.trans(List<&2, S.Entry<V>>, SC.append(S.Entry<V>, ST.ent(~V, B.at(bs, j), SC.append(Maybe<&2, V>, vsl, r)), ST.absm(~V, bs, SC.append(Maybe<&2, V>, vsl, r), p, 1n+j)), SC.append(S.Entry<V>, ST.ent(~V, B.at(bs, j), vsl), ST.absm(~V, bs, SC.append(Maybe<&2, V>, vsl, r), p, 1n+j)), ST.absm(~V, bs, vsl, 1n+p, j),
        Equal.cong(List<&2, S.Entry<V>>, List<&2, S.Entry<V>>, z => SC.append(S.Entry<V>, z, ST.absm(~V, bs, SC.append(Maybe<&2, V>, vsl, r), p, 1n+j)), ST.ent(~V, B.at(bs, j), SC.append(Maybe<&2, V>, vsl, r)), ST.ent(~V, B.at(bs, j), vsl), ent_app(~V, vsl, r, sd, hlen, B.at(bs, j), B.all_inst(B.PWell{bs, sd}, n, hw, j, hj))),
        Equal.cong(List<&2, S.Entry<V>>, List<&2, S.Entry<V>>, z => SC.append(S.Entry<V>, ST.ent(~V, B.at(bs, j), vsl), z), ST.absm(~V, bs, SC.append(Maybe<&2, V>, vsl, r), p, 1n+j), ST.absm(~V, bs, vsl, p, 1n+j), absm_app(~V, bs, vsl, r, sd, hlen, n, hw, p, 1n+j, IA.idx_next(j, p, n, hjm))))
