import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/lru.bend as SP
import ../math/u32div.bend as UD
import ../../src/math/u64.bend as W
import ../../src/containers/hash_table.bend as H
import ../../src/containers/lru.bend as LR
import ../hash_table/table.bend as TB
import ../hash_table/state.bend as HT
import ../hash_table/keysw.bend as KW
import ../hash_table/strings.bend as STR
import ../hash_table/arena.bend as AN
import ./state.bend as ST
import ./unlink.bend as UL
import ./gone.bend as GO
import ./idx.bend as ID
import ./touch.bend as TO
import ../lib/nat_list.bend as NL
import ../lib/links.bend as LK

# The key walk of keys: from the tail back along prev links, prepending each
# slot's key (a one-character key read from its tagged word, a longer one
# copied out of ks and put back).

# ---- lists ----


# the value of a live slot
def some_v(~V: Data, +el: List<&2, Maybe<&2, V>>, +s: Nat, +m: Maybe<&2, V>, +hmm: {HT.nthm(~V, el, s) == m : Maybe<&2, V>}, +hsm: {HT.some_b(~V, m) == True{} : Bool}) -> Sigma<&1, &1, V, v => {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}>:
  match m:
    case None{}:
      Empty.absurd(Sigma<&1, &1, V, v => {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}>, L.false_true(hsm))
    case Some{+v}:
      (v, hmm)

# l reversed onto b

# the keys of the slots of l
def mapk(+ll: List<&2, U32>, +kl: List<&2, String>, l: List<&2, Nat>) -> List<&2, String>:
  match l:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{ST.skey(ll, kl, x), mapk(ll, kl, r)}

# the keys of the slots of back prepended to acc, one by one
def racc(+ll: List<&2, U32>, +kl: List<&2, String>, back: List<&2, Nat>, acc: List<&2, String>) -> List<&2, String>:
  match back:
    case Nil{}:
      acc
    case Con{+x, r}:
      racc(ll, kl, r, Con{ST.skey(ll, kl, x), acc})

# every slot of back is below fr and its prev is the next slot of back
def rok(+ll: List<&2, U32>, back: List<&2, Nat>, +fr: Nat) -> Bool:
  match back:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(Nat.is_lt(x, fr), Bool.and(U32.is_eq(ST.lw(ll, x, 0n), LK.fst_or(r, 0)), rok(ll, r, fr)))

def ra_rapp(+ll: List<&2, U32>, +kl: List<&2, String>, +l: List<&2, Nat>, +b: List<&2, Nat>, +acc: List<&2, String>) -> {racc(ll, kl, NL.rapp(l, b), acc) == racc(ll, kl, b, SC.append(String, mapk(ll, kl, l), acc)) : List<&2, String>}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      ra_rapp(ll, kl, r, Con{x, b}, acc)



def lo_idem(+l: List<&2, Nat>, +p: U32) -> {LK.last_or(l, LK.last_or(l, p)) == LK.last_or(l, p) : U32}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      {==}

def fo_of(+r: List<&2, Nat>, +a: U32, +h: {U32.is_eq(a, LK.fst_or(r, 0)) == True{} : Bool}) -> {LK.fst_or(r, a) == a : U32}:
  match r:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Equal.sym(U32, a, LK.lnk(y), A.eq_of(a, LK.lnk(y), h))

# the list sl, reversed, keeps its links backwards
def rok_app(~V: Data, +ll: List<&2, U32>, +el: List<&2, Maybe<&2, V>>, +l: List<&2, Nat>, +b: List<&2, Nat>, +fr: Nat, +p: U32, +q: U32, +hs: {ST.seg(ll, l, p, q) == True{} : Bool}, +hl: {ST.slok(~V, l, fr, el) == True{} : Bool}, +hb: {rok(ll, b, fr) == True{} : Bool}, +hp: {U32.is_eq(p, LK.fst_or(b, 0)) == True{} : Bool}) -> {rok(ll, NL.rapp(l, b), fr) == True{} : Bool}:
  match l:
    case Nil{}:
      hb
    case Con{+x, +r}:
      +ha = L.and_left(U32.is_eq(ST.lw(ll, x, 0n), p), Bool.and(U32.is_eq(ST.lw(ll, x, 1n), LK.fst_or(r, q)), ST.seg(ll, r, LK.lnk(x), q)), hs)
      +hc = L.and_right(U32.is_eq(ST.lw(ll, x, 1n), LK.fst_or(r, q)), ST.seg(ll, r, LK.lnk(x), q), L.and_right(U32.is_eq(ST.lw(ll, x, 0n), p), Bool.and(U32.is_eq(ST.lw(ll, x, 1n), LK.fst_or(r, q)), ST.seg(ll, r, LK.lnk(x), q)), hs))
      +hx = L.and_left(Nat.is_lt(x, fr), ST.live(~V, el, x), L.and_left(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, r, fr, el), hl))
      +hlr = L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.slok(~V, r, fr, el), hl)
      +el0 = A.eq_of(ST.lw(ll, x, 0n), p, ha)
      +hq = L.subst(U32, z => {U32.is_eq(z, LK.fst_or(b, 0)) == True{} : Bool}, p, ST.lw(ll, x, 0n), Equal.sym(U32, ST.lw(ll, x, 0n), p, el0), hp)
      +hb2 = L.and_intro(Nat.is_lt(x, fr), Bool.and(U32.is_eq(ST.lw(ll, x, 0n), LK.fst_or(b, 0)), rok(ll, b, fr)), hx, L.and_intro(U32.is_eq(ST.lw(ll, x, 0n), LK.fst_or(b, 0)), rok(ll, b, fr), hq, hb))
      rok_app(~V, ll, el, r, Con{x, b}, fr, LK.lnk(x), q, hc, hlr, hb2, A.eq_refl(LK.lnk(x)))


def km_v(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +s: Nat, +t: List<&2, Nat>, pv: Sigma<&1, &1, V, v => {HT.nthm(~V, el, s) == Some{v} : Maybe<&2, V>}>, +ih: {SP.keys_of(~V, ST.es(~V, ll, kl, el, t)) == mapk(ll, kl, t) : List<&2, String>}) -> {SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s, t})) == Con{ST.skey(ll, kl, s), mapk(ll, kl, t)} : List<&2, String>}:
  match pv:
    case Tuple{+v, hm}:
      +e = TO.es_cons(~V, ll, kl, el, s, v, hm, t)
      +e1 = Equal.cong(List<&2, SP.Ent<V>>, List<&2, String>, z => SP.keys_of(~V, z), ST.es(~V, ll, kl, el, Con{s, t}), Con{SP.LE{ST.skey(ll, kl, s), v, ST.lw(ll, s, 3n), W.U64{ST.lw(ll, s, 4n), ST.lw(ll, s, 5n)}}, ST.es(~V, ll, kl, el, t)}, e)
      +e2 = Equal.cong(List<&2, String>, List<&2, String>, z => Con{ST.skey(ll, kl, s), z}, SP.keys_of(~V, ST.es(~V, ll, kl, el, t)), mapk(ll, kl, t), ih)
      Equal.trans(List<&2, String>, SP.keys_of(~V, ST.es(~V, ll, kl, el, Con{s, t})), Con{ST.skey(ll, kl, s), SP.keys_of(~V, ST.es(~V, ll, kl, el, t))}, Con{ST.skey(ll, kl, s), mapk(ll, kl, t)}, e1, e2)

# the keys of live slots are the model's keys
def km(~V: Data, +ll: List<&2, U32>, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +fr: Nat, +sl: List<&2, Nat>, +h: {ST.slok(~V, sl, fr, el) == True{} : Bool}) -> {SP.keys_of(~V, ST.es(~V, ll, kl, el, sl)) == mapk(ll, kl, sl) : List<&2, String>}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +hls = L.and_left(Bool.and(Nat.is_lt(s, fr), ST.live(~V, el, s)), ST.slok(~V, t, fr, el), h)
      +ih = km(~V, ll, kl, el, fr, t, L.and_right(Bool.and(Nat.is_lt(s, fr), ST.live(~V, el, s)), ST.slok(~V, t, fr, el), h))
      km_v(~V, ll, kl, el, s, t, some_v(~V, el, s, HT.nthm(~V, el, s), {==}, L.and_right(Nat.is_lt(s, fr), ST.live(~V, el, s), hls)), ih)

# ---- one step ----


def WSt(+lkT: AR.Tree<U32>, +kl: List<&2, String>, +sd: Nat, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>) -> Type:
  Sigma<&1, &1, AR.Tree<String>, K2 => {LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}) == LR.WK{AR.thaw(String, K2), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)} : LR.Walk} & ({AR.slots(String, K2) == kl : List<&2, String>} & {AR.perfect(String, sd, K2) == True{} : Bool})>

def ws_e1(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}) -> {LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}) == LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n))) : LR.Walk}:
  +i2 = Equal.trans(Nat, UD.v(LR.hidx(H.slot(LK.lnk(x)))), ST.off(UD.v(H.slot(LK.lnk(x))), 2n), ST.off(x, 2n), ID.w2(one, h1, H.slot(LK.lnk(x)), sd, UL.sd3(sd, hsd), GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0)), Equal.cong(Nat, Nat, z => ST.off(z, 2n), UD.v(H.slot(LK.lnk(x))), x, UL.ix_o(one, h1, x, sd, hsd, hs0)))
  Equal.cong(Array<U32> & U32, LR.Walk, r => LR.wk_w(AR.thaw(String, KT), acc, LK.lnk(x), r), Array.get(U32, AR.thaw(U32, lkT), LR.hidx(H.slot(LK.lnk(x)))), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), x, 2n)), GO.rd(one, h1, lkT, sd, hsd, hpl, LR.hidx(H.slot(LK.lnk(x))), x, 2n, {==}, hs0, i2))

def ws_r0(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x)))) == (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), x, 0n)) : Array<U32> & U32}:
  +i0 = Equal.trans(Nat, UD.v(LR.pidx(H.slot(LK.lnk(x)))), ST.off(UD.v(H.slot(LK.lnk(x))), 0n), ST.off(x, 0n), ID.w0(one, h1, H.slot(LK.lnk(x)), sd, UL.sd3(sd, hsd), GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0)), Equal.cong(Nat, Nat, z => ST.off(z, 0n), UD.v(H.slot(LK.lnk(x))), x, UL.ix_o(one, h1, x, sd, hsd, hs0)))
  GO.rd(one, h1, lkT, sd, hsd, hpl, LR.pidx(H.slot(LK.lnk(x))), x, 0n, {==}, hs0, i0)


def ws_sh(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}, +hd: {H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)) == True{} : Bool}) -> WSt(lkT, kl, sd, x, acc, KT):
  +e1 = ws_e1(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0)
  +e2 = Equal.cong(Bool, LR.Walk, b => LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), b), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)), True{}, hd)
  +e3 = Equal.cong(Array<U32> & U32, LR.Walk, r => LR.wk_p(AR.thaw(String, KT), Con{SCon{Chr{U32.and(ST.lw(AR.slots(U32, lkT), x, 2n), 2147483647)}, SNil{}}, acc}, r), Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x)))), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), x, 0n)), ws_r0(one, h1, lkT, sd, hsd, hpl, kl, x, hs0))
  +ek = Equal.cong(Bool, String, b => TB.keyof_c(ST.lw(AR.slots(U32, lkT), x, 2n), TB.nths(kl, x), b), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)), True{}, hd)
  +e4 = Equal.cong(String, LR.Walk, z => LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), Con{z, acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, SCon{Chr{U32.and(ST.lw(AR.slots(U32, lkT), x, 2n), 2147483647)}, SNil{}}, ST.skey(AR.slots(U32, lkT), kl, x), Equal.sym(String, ST.skey(AR.slots(U32, lkT), kl, x), SCon{Chr{U32.and(ST.lw(AR.slots(U32, lkT), x, 2n), 2147483647)}, SNil{}}, ek))
  +eq = Equal.trans(LR.Walk, LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}), LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n))), LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e1, Equal.trans(LR.Walk, LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n))), LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), True{}), LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e2, Equal.trans(LR.Walk, LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), True{}), LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), Con{SCon{Chr{U32.and(ST.lw(AR.slots(U32, lkT), x, 2n), 2147483647)}, SNil{}}, acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e3, e4)))
  (KT, (eq, (hsl, pk)))


def ws_lg(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}, +hd: {H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)) == False{} : Bool}) -> WSt(lkT, kl, sd, x, acc, KT):
  +hsd32 = N.lt_trans(sd, 1n+sd, 32n, N.lt_succ(sd), UL.sd1(sd, hsd))
  +hx = TB.nths_some(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), AN.len_eq_lt(String, AR.slots(String, KT), sd, AR.slots_length(String, sd, KT, pk), UD.v(H.slot(LK.lnk(x))), GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0)))
  +esw = AR.swap(String, sd, KT, H.slot(LK.lnk(x)), SNil{}, TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), hsd32, GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0), hx, pk)
  +p1 = AR.upd_perfect(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}, pk)
  +es1 = AR.upd_slots(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}, GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0), pk)
  +hx1 = L.subst(List<&2, String>, z => {SC.nth(String, z, UD.v(H.slot(LK.lnk(x)))) == Some{SNil{}} : Maybe<&2, String>}, SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}), AR.slots(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), Equal.sym(List<&2, String>, AR.slots(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}), es1), KW.nth_upd_same(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}, AN.len_eq_lt(String, AR.slots(String, KT), sd, AR.slots_length(String, sd, KT, pk), UD.v(H.slot(LK.lnk(x))), GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0))))
  +est = AR.set(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), H.slot(LK.lnk(x)), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), SNil{}, hsd32, GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0), hx1, p1)
  +e1 = ws_e1(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0)
  +e2 = Equal.cong(Bool, LR.Walk, b => LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), b), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)), False{}, hd)
  +e3 = Equal.cong(Array<String> & String, LR.Walk, r => LR.wk_k(AR.thaw(U32, lkT), acc, LK.lnk(x), r), Array.swap(String, AR.thaw(String, KT), H.slot(LK.lnk(x)), SNil{}), (AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), esw)
  +e4 = Equal.cong(String & String, LR.Walk, r => LR.wk_c(AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), AR.thaw(U32, lkT), acc, LK.lnk(x), r), H.str_copy(TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), (TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), STR.str_copy(TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))))
  +e5 = Equal.cong(Array<String>, LR.Walk, a => LR.wk_p(a, Con{TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), acc}, Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x))))), Array.set(String, AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), H.slot(LK.lnk(x)), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), est)
  +e6 = Equal.cong(Array<U32> & U32, LR.Walk, r => LR.wk_p(AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), Con{TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), acc}, r), Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x)))), (AR.thaw(U32, lkT), ST.lw(AR.slots(U32, lkT), x, 0n)), ws_r0(one, h1, lkT, sd, hsd, hpl, kl, x, hs0))
  +ek1 = Equal.cong(List<&2, String>, String, z => TB.nths(z, UD.v(H.slot(LK.lnk(x)))), AR.slots(String, KT), kl, hsl)
  +ek2 = Equal.cong(Nat, String, z => TB.nths(kl, z), UD.v(H.slot(LK.lnk(x))), x, UL.ix_o(one, h1, x, sd, hsd, hs0))
  +ek3 = Equal.sym(String, ST.skey(AR.slots(U32, lkT), kl, x), TB.nths(kl, x), Equal.cong(Bool, String, b => TB.keyof_c(ST.lw(AR.slots(U32, lkT), x, 2n), TB.nths(kl, x), b), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)), False{}, hd))
  +ek = Equal.trans(String, TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), TB.nths(kl, UD.v(H.slot(LK.lnk(x)))), ST.skey(AR.slots(U32, lkT), kl, x), ek1, Equal.trans(String, TB.nths(kl, UD.v(H.slot(LK.lnk(x)))), TB.nths(kl, x), ST.skey(AR.slots(U32, lkT), kl, x), ek2, ek3))
  +e7 = Equal.cong(String, LR.Walk, z => LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{z, acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), ST.skey(AR.slots(U32, lkT), kl, x), ek)
  +eq = Equal.trans(LR.Walk, LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}), LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n))), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e1, Equal.trans(LR.Walk, LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n))), LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), False{}), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e2, Equal.trans(LR.Walk, LR.wk_word(AR.thaw(String, KT), acc, LK.lnk(x), ST.lw(AR.slots(U32, lkT), x, 2n), AR.thaw(U32, lkT), False{}), LR.wk_k(AR.thaw(U32, lkT), acc, LK.lnk(x), (AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e3, Equal.trans(LR.Walk, LR.wk_k(AR.thaw(U32, lkT), acc, LK.lnk(x), (AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), LR.wk_c(AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), AR.thaw(U32, lkT), acc, LK.lnk(x), (TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e4, Equal.trans(LR.Walk, LR.wk_c(AR.thaw(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), AR.thaw(U32, lkT), acc, LK.lnk(x), (TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), LR.wk_p(AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), Con{TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), acc}, Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x))))), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e5, Equal.trans(LR.Walk, LR.wk_p(AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), Con{TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), acc}, Array.get(U32, AR.thaw(U32, lkT), LR.pidx(H.slot(LK.lnk(x))))), LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, LR.WK{AR.thaw(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, e6, e7))))))
  +es2 = AR.upd_slots(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), GO.su_lt(H.slot(LK.lnk(x)), x, sd, UL.ix_o(one, h1, x, sd, hsd, hs0), hs0), p1)
  +ec = Equal.cong(List<&2, String>, List<&2, String>, z => SC.update(String, z, UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), AR.slots(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}), es1)
  +euu = TB.upd_upd(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}, TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))
  +eus = TB.upd_self(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))
  +esl = Equal.trans(List<&2, String>, AR.slots(String, AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))))), SC.update(String, AR.slots(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), kl, es2, Equal.trans(List<&2, String>, SC.update(String, AR.slots(String, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{})), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), SC.update(String, SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), kl, ec, Equal.trans(List<&2, String>, SC.update(String, SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), kl, euu, Equal.trans(List<&2, String>, SC.update(String, AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), AR.slots(String, KT), kl, eus, hsl))))
  (AR.upd(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x))))), (eq, (esl, AR.upd_perfect(String, sd, AR.upd(String, sd, KT, UD.v(H.slot(LK.lnk(x))), SNil{}), UD.v(H.slot(LK.lnk(x))), TB.nths(AR.slots(String, KT), UD.v(H.slot(LK.lnk(x)))), p1))))

def ws_d(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}, +d: Bool, +hd: {H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)) == d : Bool}) -> WSt(lkT, kl, sd, x, acc, KT):
  match d:
    case True{}:
      ws_sh(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0, hd)
    case False{}:
      ws_lg(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0, hd)

# THEOREM: one step of the walk prepends the slot's key and moves to its prev
def wstep(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +x: Nat, +acc: List<&2, String>, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hs0: {Nat.is_lt(x, SC.pow2(sd)) == True{} : Bool}) -> WSt(lkT, kl, sd, x, acc, KT):
  ws_d(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0, H.is_short(ST.lw(AR.slots(U32, lkT), x, 2n)), {==})

# ---- the walk ----

def WOK(+lkT: AR.Tree<U32>, +kl: List<&2, String>, +sd: Nat, +back: List<&2, Nat>, +acc: List<&2, String>, +at: U32, +KT: AR.Tree<String>) -> Type:
  Sigma<&1, &1, AR.Tree<String>, K2 => Sigma<&1, &1, U32, a2 => {LR.wk_loop(SC.length(Nat, back), LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, at}) == LR.WK{AR.thaw(String, K2), AR.thaw(U32, lkT), racc(AR.slots(U32, lkT), kl, back, acc), a2} : LR.Walk} & ({AR.slots(String, K2) == kl : List<&2, String>} & {AR.perfect(String, sd, K2) == True{} : Bool})>>

def wl_2(+lkT: AR.Tree<U32>, +kl: List<&2, String>, +sd: Nat, +x: Nat, +r: List<&2, Nat>, +acc: List<&2, String>, +KT: AR.Tree<String>, +K2: AR.Tree<String>, +es: {LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}) == LR.WK{AR.thaw(String, K2), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)} : LR.Walk}, wo: WOK(lkT, kl, sd, r, Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n), K2)) -> WOK(lkT, kl, sd, Con{x, r}, acc, LK.lnk(x), KT):
  match wo:
    case Tuple{+K3, Tuple{+a3, Tuple{+e3, Tuple{+hs3, pk3}}}}:
      +e = Equal.trans(LR.Walk, LR.wk_loop(SC.length(Nat, r), LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)})), LR.wk_loop(SC.length(Nat, r), LR.WK{AR.thaw(String, K2), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}), LR.WK{AR.thaw(String, K3), AR.thaw(U32, lkT), racc(AR.slots(U32, lkT), kl, r, Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}), a3}, Equal.cong(LR.Walk, LR.Walk, w => LR.wk_loop(SC.length(Nat, r), w), LR.wk_step(LR.WK{AR.thaw(String, KT), AR.thaw(U32, lkT), acc, LK.lnk(x)}), LR.WK{AR.thaw(String, K2), AR.thaw(U32, lkT), Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n)}, es), e3)
      (K3, (a3, (e, (hs3, pk3))))


def wl_1(+lkT: AR.Tree<U32>, +kl: List<&2, String>, +sd: Nat, +x: Nat, +r: List<&2, Nat>, +acc: List<&2, String>, +KT: AR.Tree<String>, st: WSt(lkT, kl, sd, x, acc, KT), rec: @+K2: AR.Tree<String> -> @+hs2: {AR.slots(String, K2) == kl : List<&2, String>} -> @+pk2: {AR.perfect(String, sd, K2) == True{} : Bool} -> WOK(lkT, kl, sd, r, Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n), K2)) -> WOK(lkT, kl, sd, Con{x, r}, acc, LK.lnk(x), KT):
  match st:
    case Tuple{+K2, Tuple{+es, Tuple{+hs2, pk2}}}:
      wl_2(lkT, kl, sd, x, r, acc, KT, K2, es, rec(K2, hs2, pk2))

# THEOREM: the walk from the first slot of back, for its length, prepends the
# keys of back one by one and keeps ks
def walk(+one: Nat, +h1: {one == 1n : Nat}, +lkT: AR.Tree<U32>, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +hpl: {AR.perfect(U32, 3n+sd, lkT) == True{} : Bool}, +kl: List<&2, String>, +fr: Nat, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +back: List<&2, Nat>, +acc: List<&2, String>, +at: U32, +KT: AR.Tree<String>, +hsl: {AR.slots(String, KT) == kl : List<&2, String>}, +pk: {AR.perfect(String, sd, KT) == True{} : Bool}, +hr: {rok(AR.slots(U32, lkT), back, fr) == True{} : Bool}, +hat: {LK.fst_or(back, at) == at : U32}) -> WOK(lkT, kl, sd, back, acc, at, KT):
  match back:
    case Nil{}:
      (KT, (at, ({==}, (hsl, pk))))
    case Con{+x, +r}:
      +hx = L.and_left(Nat.is_lt(x, fr), Bool.and(U32.is_eq(ST.lw(AR.slots(U32, lkT), x, 0n), LK.fst_or(r, 0)), rok(AR.slots(U32, lkT), r, fr)), hr)
      +hre = L.and_right(Nat.is_lt(x, fr), Bool.and(U32.is_eq(ST.lw(AR.slots(U32, lkT), x, 0n), LK.fst_or(r, 0)), rok(AR.slots(U32, lkT), r, fr)), hr)
      +hp = L.and_left(U32.is_eq(ST.lw(AR.slots(U32, lkT), x, 0n), LK.fst_or(r, 0)), rok(AR.slots(U32, lkT), r, fr), hre)
      +hr2 = L.and_right(U32.is_eq(ST.lw(AR.slots(U32, lkT), x, 0n), LK.fst_or(r, 0)), rok(AR.slots(U32, lkT), r, fr), hre)
      +hs0 = N.lt_le_trans(x, fr, SC.pow2(sd), hx, hfr)
      ok = wl_1(lkT, kl, sd, x, r, acc, KT, wstep(one, h1, lkT, sd, hsd, hpl, kl, x, acc, KT, hsl, pk, hs0), K2 => hs2 => pk2 => walk(one, h1, lkT, sd, hsd, hpl, kl, fr, hfr, r, Con{ST.skey(AR.slots(U32, lkT), kl, x), acc}, ST.lw(AR.slots(U32, lkT), x, 0n), K2, hs2, pk2, hr2, fo_of(r, ST.lw(AR.slots(U32, lkT), x, 0n), hp)))
      L.subst(U32, z => WOK(lkT, kl, sd, Con{x, r}, acc, z, KT), LK.lnk(x), at, hat, ok)
