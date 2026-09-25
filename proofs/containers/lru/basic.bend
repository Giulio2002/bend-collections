import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/lru.bend as SP
import ../../lib/u32div.bend as UD
import ../../../src/math/u64.bend as W
import ../../../src/containers/lru.bend as LR
import ../hash_table/state.bend as HT
import ../hash_table/probe_impl.bend as PI
import ./state.bend as ST
import ./meta.bend as MT
import ../hash_table/get.bend as G
import ../../lib/words32.bend as W32
import ../../lib/u32_tree.bend as UT

# capacity, len, counters and set_lifetime.


# ---- the number of entries ----

def es_len_m(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +s: Nat, +m: Maybe<&2, V>, +hm: {HT.some_b(~V, m) == True{} : Bool}, +r: List<&2, SP.Ent<V>>, +t: List<&2, Nat>, +ih: {SP.length(~V, r) == SC.length(Nat, t) : Nat}) -> {SP.length(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, m), r)) == 1n+SC.length(Nat, t) : Nat}:
  match m:
    case None{}:
      Empty.absurd({SP.length(~V, SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, s, None{}), r)) == 1n+SC.length(Nat, t) : Nat}, L.false_true(hm))
    case Some{v}:
      N.succ_cong(SP.length(~V, r), SC.length(Nat, t), ih)

# every slot live: one entry per slot
def es_len(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +fr: Nat, +sl: List<&2, Nat>, +h: {ST.slok(~V, sl, fr, el) == True{} : Bool}) -> {SP.length(~V, ST.es(~V, ll, kl, el, sl)) == SC.length(Nat, sl) : Nat}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +h1 = L.and_left(Bool.and(Nat.is_lt(s, fr), ST.live(~V, el, s)), ST.slok(~V, t, fr, el), h)
      +hl = L.and_right(Nat.is_lt(s, fr), ST.live(~V, el, s), h1)
      es_len_m(~V, ll, kl, s, HT.nthm(~V, el, s), hl, ST.es(~V, ll, kl, el, t), t, es_len(~V, ll, kl, el, fr, t, L.and_right(Bool.and(Nat.is_lt(s, fr), ST.live(~V, el, s)), ST.slok(~V, t, fr, el), h)))

# the model's length is the count n
def len_model(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}) -> {SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl)) == UD.v(n) : Nat}:
  Equal.trans(Nat, SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl)), SC.length(Nat, sl), UD.v(n), es_len(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), UD.v(W32.nth0(AR.slots(U32, mT), 0n)), sl, ST.g_csl(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg)), N.eq_from_is_eq(SC.length(Nat, sl), UD.v(n), ST.g_clen(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg)))

# n is below 2^k
def n_lt(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}) -> {Nat.is_lt(UD.v(n), SC.pow2(k)) == True{} : Bool}:
  G.load_lt(UD.v(n), SC.pow2(k), N.succ_le_lt(0n, SC.pow2(k), N.pow2_pos(k)), ST.g_cload(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg))

# ---- the operations ----

# THEOREM: capacity is the specification's; the cache is unchanged.
def capacity_ok(~V: Data, +sh: ST.Sh<V>) -> {LR.capacity(&2, V, ST.real(~V, sh)) == (ST.real(~V, sh), SP.capacity(~V, ST.model(~V, sh))) : LR.LRU<&2, V> & U32}:
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      {==}

# THEOREM: len is the specification's; the cache is unchanged.
def len_ok(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}) -> {LR.len(&2, V, ST.real(~V, sh)) == (ST.real(~V, sh), SP.len(~V, ST.model(~V, sh))) : LR.LRU<&2, V> & U32}:
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      +hk = L.and_left(Nat.is_lt(k, 30n), Nat.is_lt(0n, k), ST.g_ck(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg))
      +e1 = Equal.sym(U32, U32.from_nat(UD.v(n)), n, PI.from_v(n, k, N.lt_le(k, 32n, N.lt_trans(k, 30n, 32n, hk, {==})), n_lt(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg)))
      +e2 = Equal.cong(Nat, U32, z => U32.from_nat(z), UD.v(n), SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl)), Equal.sym(Nat, SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl)), UD.v(n), len_model(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg)))
      Equal.cong(U32, LR.LRU<&2, V> & U32, z => (ST.real(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}), z), n, U32.from_nat(SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl))), Equal.trans(U32, n, U32.from_nat(UD.v(n)), U32.from_nat(SP.length(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl))), e1, e2))

def mtree(~V: Data, sh: ST.Sh<V>) -> AR.Tree<U32>:
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      mT

# THEOREM: counters hands back the cache and a copy of the meta words, whose
# counter words are the specification's counters.
def counters_ok(~V: Data, +sh: ST.Sh<V>) -> {LR.counters(&2, V, ST.real(~V, sh)) == (ST.real(~V, sh), AR.thaw(U32, mtree(~V, sh))) : LR.LRU<&2, V> & Array<U32>} & {ST.ctr(AR.slots(U32, mtree(~V, sh))) == SP.counters(~V, ST.model(~V, sh)) : SP.Ctr}:
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      +e = Equal.cong(Array<U32> & Array<U32>, LR.LRU<&2, V> & Array<U32>, r => LR.cnt_fin(&2, V, cap, n, head, tail, free, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT), r), Array.clone(U32, AR.thaw(U32, mT)), (AR.thaw(U32, mT), AR.thaw(U32, mT)), AR.clone(U32, mT))
      (e, {==})

# ---- congruences ----

def ct5(+a1: W.U64, +a2: W.U64, +a3: W.U64, +a4: W.U64, +a5: W.U64, +b1: W.U64, +b2: W.U64, +b3: W.U64, +b4: W.U64, +b5: W.U64, +e1: {a1 == b1 : W.U64}, +e2: {a2 == b2 : W.U64}, +e3: {a3 == b3 : W.U64}, +e4: {a4 == b4 : W.U64}, +e5: {a5 == b5 : W.U64}) -> {SP.CT{a1, a2, a3, a4, a5} == SP.CT{b1, b2, b3, b4, b5} : SP.Ctr}:
  +r1 = L.subst(W.U64, z => {SP.CT{a1, a2, a3, a4, a5} == SP.CT{z, a2, a3, a4, a5} : SP.Ctr}, a1, b1, e1, {==})
  +r2 = L.subst(W.U64, z => {SP.CT{a1, a2, a3, a4, a5} == SP.CT{b1, z, a3, a4, a5} : SP.Ctr}, a2, b2, e2, r1)
  +r3 = L.subst(W.U64, z => {SP.CT{a1, a2, a3, a4, a5} == SP.CT{b1, b2, z, a4, a5} : SP.Ctr}, a3, b3, e3, r2)
  +r4 = L.subst(W.U64, z => {SP.CT{a1, a2, a3, a4, a5} == SP.CT{b1, b2, b3, z, a5} : SP.Ctr}, a4, b4, e4, r3)
  L.subst(W.U64, z => {SP.CT{a1, a2, a3, a4, a5} == SP.CT{b1, b2, b3, b4, z} : SP.Ctr}, a5, b5, e5, r4)

def w64_eq(+a: List<&2, U32>, +b: List<&2, U32>, +i: Nat, +e0: {W32.nth0(a, i) == W32.nth0(b, i) : U32}, +e1: {W32.nth0(a, 1n+i) == W32.nth0(b, 1n+i) : U32}) -> {ST.w64(a, i) == ST.w64(b, i) : W.U64}:
  +r = L.subst(U32, z => {ST.w64(a, i) == W.U64{z, W32.nth0(a, 1n+i)} : W.U64}, W32.nth0(a, i), W32.nth0(b, i), e0, {==})
  L.subst(U32, z => {ST.w64(a, i) == W.U64{W32.nth0(b, i), z} : W.U64}, W32.nth0(a, 1n+i), W32.nth0(b, 1n+i), e1, r)

# the counters of two meta word lists that agree on words 16 .. 25
def ctr_eq(+a: List<&2, U32>, +b: List<&2, U32>, +e16: {W32.nth0(a, 16n) == W32.nth0(b, 16n) : U32}, +e17: {W32.nth0(a, 17n) == W32.nth0(b, 17n) : U32}, +e18: {W32.nth0(a, 18n) == W32.nth0(b, 18n) : U32}, +e19: {W32.nth0(a, 19n) == W32.nth0(b, 19n) : U32}, +e20: {W32.nth0(a, 20n) == W32.nth0(b, 20n) : U32}, +e21: {W32.nth0(a, 21n) == W32.nth0(b, 21n) : U32}, +e22: {W32.nth0(a, 22n) == W32.nth0(b, 22n) : U32}, +e23: {W32.nth0(a, 23n) == W32.nth0(b, 23n) : U32}, +e24: {W32.nth0(a, 24n) == W32.nth0(b, 24n) : U32}, +e25: {W32.nth0(a, 25n) == W32.nth0(b, 25n) : U32}) -> {ST.ctr(a) == ST.ctr(b) : SP.Ctr}:
  ct5(ST.w64(a, 16n), ST.w64(a, 18n), ST.w64(a, 20n), ST.w64(a, 22n), ST.w64(a, 24n), ST.w64(b, 16n), ST.w64(b, 18n), ST.w64(b, 20n), ST.w64(b, 22n), ST.w64(b, 24n), w64_eq(a, b, 16n, e16, e17), w64_eq(a, b, 18n, e18, e19), w64_eq(a, b, 20n, e20, e21), w64_eq(a, b, 22n, e22, e23), w64_eq(a, b, 24n, e24, e25))

def w64_eq_l(+a: List<&2, U32>, +i: Nat, +lo: U32, +hi: U32, +e0: {W32.nth0(a, i) == lo : U32}, +e1: {W32.nth0(a, 1n+i) == hi : U32}) -> {ST.w64(a, i) == W.U64{lo, hi} : W.U64}:
  +r = L.subst(U32, z => {ST.w64(a, i) == W.U64{z, W32.nth0(a, 1n+i)} : W.U64}, W32.nth0(a, i), lo, e0, {==})
  L.subst(U32, z => {ST.w64(a, i) == W.U64{lo, z} : W.U64}, W32.nth0(a, 1n+i), hi, e1, r)

# the model's fields
def lru_eq(~V: Data, +cap: U32, +a: U32, +a2: U32, +b: W.U64, +b2: W.U64, +es: List<&2, SP.Ent<V>>, +es2: List<&2, SP.Ent<V>>, +c: SP.Ctr, +c2: SP.Ctr, +ea: {a == a2 : U32}, +eb: {b == b2 : W.U64}, +ee: {es == es2 : List<&2, SP.Ent<V>>}, +ec: {c == c2 : SP.Ctr}) -> {SP.L{cap, a, b, es, c} == SP.L{cap, a2, b2, es2, c2} : SP.Lru<V>}:
  +r1 = L.subst(U32, z => {SP.L{cap, a, b, es, c} == SP.L{cap, z, b, es, c} : SP.Lru<V>}, a, a2, ea, {==})
  +r2 = L.subst(W.U64, z => {SP.L{cap, a, b, es, c} == SP.L{cap, a2, z, es, c} : SP.Lru<V>}, b, b2, eb, r1)
  +r3 = L.subst(List<&2, SP.Ent<V>>, z => {SP.L{cap, a, b, es, c} == SP.L{cap, a2, b2, z, c} : SP.Lru<V>}, es, es2, ee, r2)
  L.subst(SP.Ctr, z => {SP.L{cap, a, b, es, c} == SP.L{cap, a2, b2, es2, z} : SP.Lru<V>}, c, c2, ec, r3)

# ---- set_lifetime ----


def SetOK(~V: Data, +sh: ST.Sh<V>, +spec: SP.Lru<V>, r: LR.LRU<&2, V>) -> Type:
  Sigma<&1, &1, ST.Sh<V>, sh2 => {r == ST.real(~V, sh2) : LR.LRU<&2, V>} & ({spec == ST.model(~V, sh2) : SP.Lru<V>} & {ST.good(~V, sh2) == True{} : Bool})>

# word j of the meta list after the three lifetime writes, j not 3, 4, 5
def oth3(+mT: AR.Tree<U32>, +on: U32, +lo: U32, +hi: U32, +h1: {AR.slots(U32, AR.upd(U32, 5n, mT, 3n, on)) == SC.update(U32, AR.slots(U32, mT), 3n, on) : List<&2, U32>}, +h2: {AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)) == SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, mT, 3n, on)), 4n, lo) : List<&2, U32>}, +h3: {AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)) == SC.update(U32, AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), 5n, hi) : List<&2, U32>}, +j: Nat, +n3: {Nat.is_eq(3n, j) == False{} : Bool}, +n4: {Nat.is_eq(4n, j) == False{} : Bool}, +n5: {Nat.is_eq(5n, j) == False{} : Bool}) -> {W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), j) == W32.nth0(AR.slots(U32, mT), j) : U32}:
  Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), j), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), j), W32.nth0(AR.slots(U32, mT), j), MT.nth_other(AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), h3, j, n5), Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), j), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, 3n, on)), j), W32.nth0(AR.slots(U32, mT), j), MT.nth_other(AR.upd(U32, 5n, mT, 3n, on), 4n, lo, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), h2, j, n4), MT.nth_other(mT, 3n, on, AR.upd(U32, 5n, mT, 3n, on), h1, j, n3)))


def sl_go(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, +s: W.U64, +on: U32) -> SetOK(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}, SP.L{cap, on, s, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, mT))}, LR.F{cap, n, head, tail, free, LR.set_life(AR.thaw(U32, mT), s, on), AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}):
  match s:
    case W.U64{+lo, +hi}:
      +pm = ST.g_cpm(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg)
      +a1 = UT.uset_a(5n, {==}, mT, pm, 3, {==}, on)
      +p1 = UT.uset_p(5n, mT, pm, 3n, on)
      +h1 = UT.uset_s(5n, mT, pm, 3n, {==}, on)
      +a2 = UT.uset_a(5n, {==}, AR.upd(U32, 5n, mT, 3n, on), p1, 4, {==}, lo)
      +p2 = UT.uset_p(5n, AR.upd(U32, 5n, mT, 3n, on), p1, 4n, lo)
      +h2 = UT.uset_s(5n, AR.upd(U32, 5n, mT, 3n, on), p1, 4n, {==}, lo)
      +a3 = UT.uset_a(5n, {==}, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), p2, 5, {==}, hi)
      +p3 = UT.uset_p(5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), p2, 5n, hi)
      +h3 = UT.uset_s(5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), p2, 5n, {==}, hi)
      +ea = Equal.trans(Array<U32>, Array.set(U32, Array.set(U32, Array.set(U32, AR.thaw(U32, mT), 3, on), 4, lo), 5, hi), Array.set(U32, Array.set(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, 3n, on)), 4, lo), 5, hi), AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), Equal.cong(Array<U32>, Array<U32>, z => Array.set(U32, Array.set(U32, z, 4, lo), 5, hi), Array.set(U32, AR.thaw(U32, mT), 3, on), AR.thaw(U32, AR.upd(U32, 5n, mT, 3n, on)), a1), Equal.trans(Array<U32>, Array.set(U32, Array.set(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, 3n, on)), 4, lo), 5, hi), Array.set(U32, AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), 5, hi), AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), Equal.cong(Array<U32>, Array<U32>, z => Array.set(U32, z, 5, hi), Array.set(U32, AR.thaw(U32, AR.upd(U32, 5n, mT, 3n, on)), 4, lo), AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), a2), a3))
      +er = Equal.cong(Array<U32>, LR.LRU<&2, V>, z => LR.F{cap, n, head, tail, free, z, AR.thaw(U32, tabT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, Array.set(U32, Array.set(U32, Array.set(U32, AR.thaw(U32, mT), 3, on), 4, lo), 5, hi), AR.thaw(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), ea)
      +e3 = Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 3n), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), 3n), on, MT.nth_other(AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), h3, 3n, {==}), Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), 3n), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, mT, 3n, on)), 3n), on, MT.nth_other(AR.upd(U32, 5n, mT, 3n, on), 4n, lo, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), h2, 3n, {==}), MT.nth_same(5n, mT, pm, 3n, {==}, on, AR.upd(U32, 5n, mT, 3n, on), h1)))
      +e4 = Equal.trans(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 4n), W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo)), 4n), lo, MT.nth_other(AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), h3, 4n, {==}), MT.nth_same(5n, AR.upd(U32, 5n, mT, 3n, on), p1, 4n, {==}, lo, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), h2))
      +e5 = MT.nth_same(5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), p2, 5n, {==}, hi, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), h3)
      +ew = Equal.sym(W.U64, ST.w64(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 4n), W.U64{lo, hi}, w64_eq_l(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 4n, lo, hi, e4, e5))
      +ec = ctr_eq(AR.slots(U32, mT), AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 16n), W32.nth0(AR.slots(U32, mT), 16n), oth3(mT, on, lo, hi, h1, h2, h3, 16n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 17n), W32.nth0(AR.slots(U32, mT), 17n), oth3(mT, on, lo, hi, h1, h2, h3, 17n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 18n), W32.nth0(AR.slots(U32, mT), 18n), oth3(mT, on, lo, hi, h1, h2, h3, 18n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 19n), W32.nth0(AR.slots(U32, mT), 19n), oth3(mT, on, lo, hi, h1, h2, h3, 19n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 20n), W32.nth0(AR.slots(U32, mT), 20n), oth3(mT, on, lo, hi, h1, h2, h3, 20n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 21n), W32.nth0(AR.slots(U32, mT), 21n), oth3(mT, on, lo, hi, h1, h2, h3, 21n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 22n), W32.nth0(AR.slots(U32, mT), 22n), oth3(mT, on, lo, hi, h1, h2, h3, 22n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 23n), W32.nth0(AR.slots(U32, mT), 23n), oth3(mT, on, lo, hi, h1, h2, h3, 23n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 24n), W32.nth0(AR.slots(U32, mT), 24n), oth3(mT, on, lo, hi, h1, h2, h3, 24n, {==}, {==}, {==})), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 25n), W32.nth0(AR.slots(U32, mT), 25n), oth3(mT, on, lo, hi, h1, h2, h3, 25n, {==}, {==}, {==})))
      +em = lru_eq(~V, cap, on, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 3n), W.U64{lo, hi}, ST.w64(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 4n), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl), ST.ctr(AR.slots(U32, mT)), ST.ctr(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi))), Equal.sym(U32, W32.nth0(AR.slots(U32, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi)), 3n), on, e3), ew, {==}, ec)
      +g2 = MT.good_m(~V, cap, n, head, tail, free, mT, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), k, sd, tabT, ksT, eT, lkT, sl, fl, hg, oth3(mT, on, lo, hi, h1, h2, h3, 0n, {==}, {==}, {==}), oth3(mT, on, lo, hi, h1, h2, h3, 1n, {==}, {==}, {==}), oth3(mT, on, lo, hi, h1, h2, h3, 2n, {==}, {==}, {==}), oth3(mT, on, lo, hi, h1, h2, h3, 6n, {==}, {==}, {==}), oth3(mT, on, lo, hi, h1, h2, h3, 7n, {==}, {==}, {==}), p3)
      (ST.LS{cap, n, head, tail, free, AR.upd(U32, 5n, AR.upd(U32, 5n, AR.upd(U32, 5n, mT, 3n, on), 4n, lo), 5n, hi), k, sd, tabT, ksT, eT, lkT, sl, fl}, (er, (em, g2)))


# THEOREM: set_lifetime is the specification's; the invariant is kept.
def set_lifetime_ok(~V: Data, +sh: ST.Sh<V>, +hg: {ST.good(~V, sh) == True{} : Bool}, +ns: W.U64) -> SetOK(~V, sh, SP.set_lifetime(~V, ST.model(~V, sh), ns), LR.set_lifetime_packed(&2, V, ST.real(~V, sh), ns)):
  match sh:
    case ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}:
      sl_go(~V, cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl, hg, W.div_small_signed(ns, 1000000), W.carry(Bool.not(W.is_zero(ns))))
