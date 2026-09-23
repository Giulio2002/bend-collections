import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/hash_table.bend as H
import ../../src/containers/lru.bend as LR
import ../hash_table/buckets.bend as B
import ../hash_table/state.bend as HT
import ../hash_table/table.bend as TB
import ../hash_table/arena.bend as AN
import ./state.bend as ST
import ./dll.bend as DL
import ./idx.bend as ID
import ../hash_table/keys.bend as K
import ../lib/nat_list.bend as NL
import ../lib/links.bend as LK
import ../lib/words32.bend as W32

# The grown arena: every array gains a blank second half; the invariant and
# the model read the first half only.

def nth0_app(+xs: List<&2, U32>, +r: List<&2, U32>, +t: Nat, +h: {Nat.is_lt(t, SC.length(U32, xs)) == True{} : Bool}) -> {W32.nth0(SC.append(U32, xs, r), t) == W32.nth0(xs, t) : U32}:
  match xs t:
    case Nil{} _:
      Empty.absurd({W32.nth0(SC.append(U32, Nil{}, r), t) == W32.nth0(Nil{}, t) : U32}, N.lt_zero_absurd(t, h))
    case Con{x, u} 0n:
      {==}
    case Con{x, u} 1n+p:
      nth0_app(u, r, p, h)


def lw_app(+ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +x: Nat, +hx: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}, +o: Nat, +ho: {Nat.is_lt(o, 8n) == True{} : Bool}) -> {ST.lw(SC.append(U32, ll, rl), x, o) == ST.lw(ll, x, o) : U32}:
  nth0_app(ll, rl, ST.off(x, o), AN.len_eq_lt(U32, ll, 3n+sd, hl, ST.off(x, o), ID.off_lt(x, sd, hx, o, ho)))

def skey_app(+ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +kl: List<&2, String>, +rk: List<&2, String>, +hk: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +x: Nat, +hx: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}) -> {ST.skey(SC.append(U32, ll, rl), SC.append(String, kl, rk), x) == ST.skey(ll, kl, x) : String}:
  Equal.trans(String, TB.keyof(ST.lw(SC.append(U32, ll, rl), x, 2n), TB.nths(SC.append(String, kl, rk), x)), TB.keyof(ST.lw(ll, x, 2n), TB.nths(SC.append(String, kl, rk), x)), TB.keyof(ST.lw(ll, x, 2n), TB.nths(kl, x)), Equal.cong(U32, String, z => TB.keyof(z, TB.nths(SC.append(String, kl, rk), x)), ST.lw(SC.append(U32, ll, rl), x, 2n), ST.lw(ll, x, 2n), lw_app(ll, rl, sd, hl, x, hx, 2n, {==})), Equal.cong(String, String, z => TB.keyof(ST.lw(ll, x, 2n), z), TB.nths(SC.append(String, kl, rk), x), TB.nths(kl, x), AN.nths_app(kl, rk, x, AN.len_eq_lt(String, kl, sd, hk, x, hx))))

def sent_app(~V: Data, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +kl: List<&2, String>, +rk: List<&2, String>, +hk: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +x: Nat, +hx: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}, +m: Maybe<&2, V>) -> {ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, m) == ST.sent_m(~V, ll, kl, x, m) : List<&2, SP.Ent<V>>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      +r1 = L.subst(String, z => {Con{SP.LE{z, w, ST.lw(SC.append(U32, ll, rl), x, 3n), W.U64{ST.lw(SC.append(U32, ll, rl), x, 4n), ST.lw(SC.append(U32, ll, rl), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, Some{w}) : List<&2, SP.Ent<V>>}, ST.skey(SC.append(U32, ll, rl), SC.append(String, kl, rk), x), ST.skey(ll, kl, x), skey_app(ll, rl, sd, hl, kl, rk, hk, x, hx), {==})
      +r2 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, z, W.U64{ST.lw(SC.append(U32, ll, rl), x, 4n), ST.lw(SC.append(U32, ll, rl), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.append(U32, ll, rl), x, 3n), ST.lw(ll, x, 3n), lw_app(ll, rl, sd, hl, x, hx, 3n, {==}), r1)
      +r3 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{z, ST.lw(SC.append(U32, ll, rl), x, 5n)}}, Nil{}} == ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.append(U32, ll, rl), x, 4n), ST.lw(ll, x, 4n), lw_app(ll, rl, sd, hl, x, hx, 4n, {==}), r2)
      +r4 = L.subst(U32, z => {Con{SP.LE{ST.skey(ll, kl, x), w, ST.lw(ll, x, 3n), W.U64{ST.lw(ll, x, 4n), z}}, Nil{}} == ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, Some{w}) : List<&2, SP.Ent<V>>}, ST.lw(SC.append(U32, ll, rl), x, 5n), ST.lw(ll, x, 5n), lw_app(ll, rl, sd, hl, x, hx, 5n, {==}), r3)
      Equal.sym(List<&2, SP.Ent<V>>, ST.sent_m(~V, ll, kl, x, Some{w}), ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, Some{w}), r4)


def es_pre(~V: Data, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +kl: List<&2, String>, +rk: List<&2, String>, +hk: {SC.length(String, kl) == SC.pow2(sd) : Nat}, +el: List<&2, Maybe<&2, V>>, +re: List<&2, Maybe<&2, V>>, +he: {SC.length(Maybe<&2, V>, el) == SC.pow2(sd) : Nat}, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +xs: List<&2, Nat>, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}) -> {ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), xs) == ST.es(~V, ll, kl, el, xs) : List<&2, SP.Ent<V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = N.lt_le_trans(x, fr, SC.pow2(sd), L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), hfr)
      +em = AN.nthm_app(~V, el, re, x, AN.len_eq_lt(Maybe<&2, V>, el, sd, he, x, hx))
      +a = Equal.cong(Maybe<&2, V>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, z), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), HT.nthm(~V, SC.append(Maybe<&2, V>, el, re), x), HT.nthm(~V, el, x), em)
      +b = Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, z, ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, HT.nthm(~V, el, x)), ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), sent_app(~V, ll, rl, sd, hl, kl, rk, hk, x, hx, HT.nthm(~V, el, x)))
      +c = Equal.cong(List<&2, SP.Ent<V>>, List<&2, SP.Ent<V>>, z => SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), z), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t), ST.es(~V, ll, kl, el, t), es_pre(~V, ll, rl, sd, hl, kl, rk, hk, el, re, he, fr, hfr, t, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)))
      Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, HT.nthm(~V, SC.append(Maybe<&2, V>, el, re), x)), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), SC.append(SP.Ent<V>, ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, HT.nthm(~V, el, x)), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), ST.es(~V, ll, kl, el, t)), a, Equal.trans(List<&2, SP.Ent<V>>, SC.append(SP.Ent<V>, ST.sent_m(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), x, HT.nthm(~V, el, x)), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), ST.es(~V, SC.append(U32, ll, rl), SC.append(String, kl, rk), SC.append(Maybe<&2, V>, el, re), t)), SC.append(SP.Ent<V>, ST.sent_m(~V, ll, kl, x, HT.nthm(~V, el, x)), ST.es(~V, ll, kl, el, t)), b, c))

def seg_pre(~V: Data, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +el: List<&2, Maybe<&2, V>>, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +xs: List<&2, Nat>, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}, +p: U32, +q: U32) -> {ST.seg(SC.append(U32, ll, rl), xs, p, q) == ST.seg(ll, xs, p, q) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = N.lt_le_trans(x, fr, SC.pow2(sd), L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), hfr)
      DL.seg_c(SC.append(U32, ll, rl), ll, x, t, p, q, lw_app(ll, rl, sd, hl, x, hx, 0n, {==}), lw_app(ll, rl, sd, hl, x, hx, 1n, {==}), seg_pre(~V, ll, rl, sd, hl, el, fr, hfr, t, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h), LK.lnk(x), q))

def has_pre(~V: Data, +bs: List<&2, B.Bk>, +m: Nat, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +el: List<&2, Maybe<&2, V>>, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +xs: List<&2, Nat>, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}) -> {ST.hasall(~V, bs, m, SC.append(U32, ll, rl), xs) == ST.hasall(~V, bs, m, ll, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = N.lt_le_trans(x, fr, SC.pow2(sd), L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), hfr)
      +e = Equal.cong(U32, Bool, z => ST.anyb(bs, m, LK.lnk(x), z), ST.lw(SC.append(U32, ll, rl), x, 2n), ST.lw(ll, x, 2n), lw_app(ll, rl, sd, hl, x, hx, 2n, {==}))
      Equal.trans(Bool, Bool.and(ST.anyb(bs, m, LK.lnk(x), ST.lw(SC.append(U32, ll, rl), x, 2n)), ST.hasall(~V, bs, m, SC.append(U32, ll, rl), t)), Bool.and(ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, m, SC.append(U32, ll, rl), t)), Bool.and(ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, m, ll, t)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.hasall(~V, bs, m, SC.append(U32, ll, rl), t)), ST.anyb(bs, m, LK.lnk(x), ST.lw(SC.append(U32, ll, rl), x, 2n)), ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), e), Equal.cong(Bool, Bool, z => Bool.and(ST.anyb(bs, m, LK.lnk(x), ST.lw(ll, x, 2n)), z), ST.hasall(~V, bs, m, SC.append(U32, ll, rl), t), ST.hasall(~V, bs, m, ll, t), has_pre(~V, bs, m, ll, rl, sd, hl, el, fr, hfr, t, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h))))

def slok_pre(~V: Data, +sd: Nat, +el: List<&2, Maybe<&2, V>>, +re: List<&2, Maybe<&2, V>>, +he: {SC.length(Maybe<&2, V>, el) == SC.pow2(sd) : Nat}, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +xs: List<&2, Nat>, +h: {ST.slok(~V, xs, fr, el) == True{} : Bool}) -> {ST.slok(~V, xs, fr, SC.append(Maybe<&2, V>, el, re)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = N.lt_le_trans(x, fr, SC.pow2(sd), L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), hfr)
      +hl = L.and_right(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h))
      +el2 = Equal.trans(Bool, ST.live(~V, SC.append(Maybe<&2, V>, el, re), x), ST.live(~V, el, x), True{}, Equal.cong(Maybe<&2, V>, Bool, z => HT.some_b(~V, z), HT.nthm(~V, SC.append(Maybe<&2, V>, el, re), x), HT.nthm(~V, el, x), AN.nthm_app(~V, el, re, x, AN.len_eq_lt(Maybe<&2, V>, el, sd, he, x, hx))), hl)
      L.and_intro(Bool.and(Nat.is_lt(x, fr), ST.live(~V, SC.append(Maybe<&2, V>, el, re), x)), ST.slok(~V, t, fr, SC.append(Maybe<&2, V>, el, re)), L.and_intro(Nat.is_lt(x, fr), ST.live(~V, SC.append(Maybe<&2, V>, el, re), x), L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)), el2), slok_pre(~V, sd, el, re, he, fr, hfr, t, L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, t, fr, el), h)))

def bslb_pre(+sl: List<&2, Nat>, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +b: B.Bk, +hw: {B.wb(sd, b) == True{} : Bool}) -> {ST.bslb(sl, SC.append(U32, ll, rl), b) == ST.bslb(sl, ll, b) : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +hx = L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), Bool.and(U32.is_eq(w, K.kword(k)), Bool.not(U32.is_eq(l, 0))), hw)
      Equal.cong(U32, Bool, z => Bool.and(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(z, w)), ST.lw(SC.append(U32, ll, rl), UD.v(H.slot(l)), 2n), ST.lw(ll, UD.v(H.slot(l)), 2n), lw_app(ll, rl, sd, hl, UD.v(H.slot(l)), hx, 2n, {==}))

def bsl_pre(+bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +ll: List<&2, U32>, +rl: List<&2, U32>, +sd: Nat, +hl: {SC.length(U32, ll) == SC.pow2(3n+sd) : Nat}, +m: Nat, +hw: {B.all_lt(B.PWell{bs, sd}, m) == True{} : Bool}) -> {ST.bsl(bs, sl, SC.append(U32, ll, rl), m) == ST.bsl(bs, sl, ll, m) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      +h1 = L.and_left(B.wb(sd, B.at(bs, j)), B.all_lt(B.PWell{bs, sd}, j), hw)
      +h2 = L.and_right(B.wb(sd, B.at(bs, j)), B.all_lt(B.PWell{bs, sd}, j), hw)
      Equal.trans(Bool, Bool.and(ST.bslb(sl, SC.append(U32, ll, rl), B.at(bs, j)), ST.bsl(bs, sl, SC.append(U32, ll, rl), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, SC.append(U32, ll, rl), j)), Bool.and(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j)), Equal.cong(Bool, Bool, z => Bool.and(z, ST.bsl(bs, sl, SC.append(U32, ll, rl), j)), ST.bslb(sl, SC.append(U32, ll, rl), B.at(bs, j)), ST.bslb(sl, ll, B.at(bs, j)), bslb_pre(sl, ll, rl, sd, hl, B.at(bs, j), h1)), Equal.cong(Bool, Bool, z => Bool.and(ST.bslb(sl, ll, B.at(bs, j)), z), ST.bsl(bs, sl, SC.append(U32, ll, rl), j), ST.bsl(bs, sl, ll, j), bsl_pre(bs, sl, ll, rl, sd, hl, j, h2)))

# ---- two writes to different cells commute ----


def upd_comm(+xs: List<&2, U32>, +i: Nat, +j: Nat, +x: U32, +y: U32, +h: {Nat.is_eq(i, j) == False{} : Bool}) -> {SC.update(U32, SC.update(U32, xs, i, x), j, y) == SC.update(U32, SC.update(U32, xs, j, y), i, x) : List<&2, U32>}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{+a, +t} 0n 0n:
      Empty.absurd({SC.update(U32, SC.update(U32, Con{a, t}, 0n, x), 0n, y) == SC.update(U32, SC.update(U32, Con{a, t}, 0n, y), 0n, x) : List<&2, U32>}, L.true_false(h))
    case Con{+a, +t} 0n 1n+q:
      {==}
    case Con{+a, +t} 1n+p 0n:
      {==}
    case Con{+a, +t} 1n+p 1n+q:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{a, z}, SC.update(U32, SC.update(U32, t, p, x), q, y), SC.update(U32, SC.update(U32, t, q, y), p, x), upd_comm(t, p, q, x, y, h))

# the blank value half
def vac_eq(~V: Data, +d: Nat) -> {LR.vac(&2, V, d) == AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, d, None{})) : Array<Maybe<&2, V>>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Array<Maybe<&2, V>>, ANode{LR.vac(&2, V, p), LR.vac(&2, V, p)}, ANode{AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), LR.vac(&2, V, p)}, AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, 1n+p, None{})), Equal.cong(Array<Maybe<&2, V>>, Array<Maybe<&2, V>>, a => ANode{a, LR.vac(&2, V, p)}, LR.vac(&2, V, p), AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), vac_eq(~V, p)), Equal.cong(Array<Maybe<&2, V>>, Array<Maybe<&2, V>>, a => ANode{AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), a}, LR.vac(&2, V, p), AR.thaw(Maybe<&2, V>, AR.trep(Maybe<&2, V>, p, None{})), vac_eq(~V, p)))
