import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as A
import ../../../spec/lib/common.bend as SC
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ../hash_table/buckets.bend as B
import ../hash_table/insm.bend as IM
import ../hash_table/rehash.bend as RH
import ../hash_table/tools.bend as TL
import ../hash_table/words.bend as WR
import ./state.bend as ST
import ./tfind.bend as TF
import ./unlink.bend as UL
import ../../lib/nat_list.bend as NL
import ../../lib/links.bend as LK

# The table and the recency list across table changes: copies of buckets
# (a rehash, a backward shift) and an emptied bucket.


# ---- a bucket with word w and link l ----

def AnybAt(+bs: List<&2, B.Bk>, +m: Nat, +l: U32, +w: U32) -> Type:
  Sigma<&1, &1, Nat, j => {Nat.is_lt(j, m) == True{} : Bool} & {ST.isbf(B.at(bs, j), w, l) == True{} : Bool}>

def ab_up(+bs: List<&2, B.Bk>, +q: Nat, +l: U32, +w: U32, e: AnybAt(bs, q, l, w)) -> AnybAt(bs, 1n+q, l, w):
  match e:
    case Tuple{+j, Tuple{+hj, hb}}:
      (j, (N.lt_trans(j, q, 1n+q, hj, N.lt_succ(q)), hb))

def ab_c(+bs: List<&2, B.Bk>, +q: Nat, +l: U32, +w: U32, +c: Bool, +hc: {ST.isbf(B.at(bs, q), w, l) == c : Bool}, +h: {Bool.or(c, ST.anyb(bs, q, l, w)) == True{} : Bool}, rec: @h2: {ST.anyb(bs, q, l, w) == True{} : Bool} -> AnybAt(bs, q, l, w)) -> AnybAt(bs, 1n+q, l, w):
  match c:
    case True{}:
      (q, (N.lt_succ(q), hc))
    case False{}:
      ab_up(bs, q, l, w, rec(h))


# some bucket below m has word w and link l: one is found
def find_anyb(+bs: List<&2, B.Bk>, +m: Nat, +l: U32, +w: U32, +h: {ST.anyb(bs, m, l, w) == True{} : Bool}) -> AnybAt(bs, m, l, w):
  match m:
    case 0n:
      Empty.absurd(AnybAt(bs, 0n, l, w), L.false_true(h))
    case 1n+q:
      ab_c(bs, q, l, w, ST.isbf(B.at(bs, q), w, l), {==}, h, h2 => find_anyb(bs, q, l, w, h2))

def ai_c(+bs: List<&2, B.Bk>, +q: Nat, +l: U32, +w: U32, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +h: {ST.isbf(B.at(bs, j), w, l) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hq: {Nat.is_lt(j, q) == True{} : Bool} -> {ST.anyb(bs, q, l, w) == True{} : Bool}) -> {ST.anyb(bs, 1n+q, l, w) == True{} : Bool}:
  match c:
    case True{}:
      NL.or_tl(ST.isbf(B.at(bs, q), w, l), ST.anyb(bs, q, l, w), L.subst(Nat, z => {ST.isbf(B.at(bs, z), w, l) == True{} : Bool}, j, q, N.eq_from_is_eq(j, q, hc), h))
    case False{}:
      NL.or_tr(ST.isbf(B.at(bs, q), w, l), ST.anyb(bs, q, l, w), rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc)))

def anyb_intro(+bs: List<&2, B.Bk>, +m: Nat, +l: U32, +w: U32, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}, +h: {ST.isbf(B.at(bs, j), w, l) == True{} : Bool}) -> {ST.anyb(bs, m, l, w) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({ST.anyb(bs, 0n, l, w) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      ai_c(bs, q, l, w, j, hj, h, Nat.is_eq(j, q), {==}, hq => anyb_intro(bs, q, l, w, j, hq, h))

def isbf_occ(+b: B.Bk, +w: U32, +l: U32, +h: {ST.isbf(b, w, l) == True{} : Bool}) -> {B.occ(b) == True{} : Bool}:
  match b:
    case B.BE{}:
      Empty.absurd({B.occ(B.BE{}) == True{} : Bool}, L.false_true(h))
    case B.BF{+x, +y, +k}:
      {==}

# ---- copies: every old bucket has a copy ----

def ht1(+nw: List<&2, B.Bk>, +n2: Nat, +l: U32, +w: U32, +b: B.Bk, +hb: {ST.isbf(b, w, l) == True{} : Bool}, e: RH.EqAt(nw, n2, b)) -> {ST.anyb(nw, n2, l, w) == True{} : Bool}:
  match e:
    case Tuple{+j2, Tuple{+hj2, e2}}:
      anyb_intro(nw, n2, l, w, j2, hj2, L.subst(B.Bk, z => {ST.isbf(z, w, l) == True{} : Bool}, b, B.at(nw, j2), Equal.sym(B.Bk, B.at(nw, j2), b, e2), hb))

def ht0(+od: List<&2, B.Bk>, +nw: List<&2, B.Bk>, +no: Nat, +n2: Nat, +hto: {B.all_lt(B.PTo{od, nw, n2}, no) == True{} : Bool}, +l: U32, +w: U32, e: AnybAt(od, no, l, w)) -> {ST.anyb(nw, n2, l, w) == True{} : Bool}:
  match e:
    case Tuple{+j, Tuple{+hj, hb}}:
      +hbb = {hb : {ST.isbf(B.at(od, j), w, l) == True{} : Bool}}
      +hae = B.imp_elim(B.occ(B.at(od, j)), B.anyeq(nw, n2, B.at(od, j)), B.all_inst(B.PTo{od, nw, n2}, no, hto, j, hj), isbf_occ(B.at(od, j), w, l, hbb))
      ht1(nw, n2, l, w, B.at(od, j), hbb, RH.find_eq(nw, n2, B.at(od, j), hae))

# THEOREM: a table holding copies of all old buckets has a bucket for every slot
def has_to(~V: Data, +od: List<&2, B.Bk>, +nw: List<&2, B.Bk>, +no: Nat, +n2: Nat, +hto: {B.all_lt(B.PTo{od, nw, n2}, no) == True{} : Bool}, +ll: List<&2, U32>, +sl: List<&2, Nat>, +h: {ST.hasall(~V, od, no, ll, sl) == True{} : Bool}) -> {ST.hasall(~V, nw, n2, ll, sl) == True{} : Bool}:
  match sl:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +h0 = L.and_left(ST.anyb(od, no, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, od, no, ll, t), h)
      L.and_intro(ST.anyb(nw, n2, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, nw, n2, ll, t), ht0(od, nw, no, n2, hto, LK.lnk(s), ST.lw(ll, s, 2n), find_anyb(od, no, LK.lnk(s), ST.lw(ll, s, 2n), h0)), has_to(~V, od, nw, no, n2, hto, ll, t, L.and_right(ST.anyb(od, no, LK.lnk(s), ST.lw(ll, s, 2n)), ST.hasall(~V, od, no, ll, t), h)))

# ---- copies: every new bucket is a copy ----

def bf1(+od: List<&2, B.Bk>, +no: Nat, +sl: List<&2, Nat>, +ll: List<&2, U32>, +h: {ST.bsl(od, sl, ll, no) == True{} : Bool}, +b: B.Bk, e: RH.EqAt(od, no, b)) -> {ST.bslb(sl, ll, b) == True{} : Bool}:
  match e:
    case Tuple{+j, Tuple{+hj, e2}}:
      L.subst(B.Bk, z => {ST.bslb(sl, ll, z) == True{} : Bool}, B.at(od, j), b, e2, TF.bsl_inst(od, sl, ll, no, h, j, hj))

def bf0(+od: List<&2, B.Bk>, +no: Nat, +sl: List<&2, Nat>, +ll: List<&2, U32>, +h: {ST.bsl(od, sl, ll, no) == True{} : Bool}, +b: B.Bk, +hq: {B.implies(B.occ(b), B.anyeq(od, no, b)) == True{} : Bool}) -> {ST.bslb(sl, ll, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      bf1(od, no, sl, ll, h, B.BF{w, l, k}, RH.find_eq(od, no, B.BF{w, l, k}, hq))

# THEOREM: a table of copies of old buckets keeps the slot correspondence
def bsl_from(+nw: List<&2, B.Bk>, +od: List<&2, B.Bk>, +no: Nat, +n2: Nat, +hf: {B.all_lt(B.PFrom{nw, od, no}, n2) == True{} : Bool}, +sl: List<&2, Nat>, +ll: List<&2, U32>, +h: {ST.bsl(od, sl, ll, no) == True{} : Bool}) -> {ST.bsl(nw, sl, ll, n2) == True{} : Bool}:
  match n2:
    case 0n:
      {==}
    case 1n+q:
      L.and_intro(ST.bslb(sl, ll, B.at(nw, q)), ST.bsl(nw, sl, ll, q), bf0(od, no, sl, ll, h, B.at(nw, q), L.and_left(B.eval(B.PFrom{nw, od, no}, q), B.all_lt(B.PFrom{nw, od, no}, q), hf)), bsl_from(nw, od, no, q, L.and_right(B.eval(B.PFrom{nw, od, no}, q), B.all_lt(B.PFrom{nw, od, no}, q), hf), sl, ll, h))

# ---- an emptied bucket ----

def ib_c(+bs: List<&2, B.Bk>, +i: Nat, +hlen: {Nat.is_lt(i, SC.length(B.Bk, bs)) == True{} : Bool}, +q: Nat, +l: U32, +w: U32, +hne: {ST.isbf(B.at(bs, i), w, l) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, q) == c : Bool}) -> {ST.isbf(B.at(IM.bupd(bs, i, B.BE{}), q), w, l) == ST.isbf(B.at(bs, q), w, l) : Bool}:
  match c:
    case True{}:
      +e = N.eq_from_is_eq(i, q, hc)
      Equal.trans(Bool, ST.isbf(B.at(IM.bupd(bs, i, B.BE{}), q), w, l), False{}, ST.isbf(B.at(bs, q), w, l), Equal.cong(B.Bk, Bool, z => ST.isbf(z, w, l), B.at(IM.bupd(bs, i, B.BE{}), q), B.BE{}, IM.at_bu_eq(bs, i, B.BE{}, hlen, q, hc)), Equal.sym(Bool, ST.isbf(B.at(bs, q), w, l), False{}, L.subst(Nat, z => {ST.isbf(B.at(bs, z), w, l) == False{} : Bool}, i, q, e, hne)))
    case False{}:
      Equal.cong(B.Bk, Bool, z => ST.isbf(z, w, l), B.at(IM.bupd(bs, i, B.BE{}), q), B.at(bs, q), IM.at_bupd_other(bs, i, B.BE{}, q, hc))

# emptying a bucket that does not have word w and link l keeps any other
def anyb_rm(+bs: List<&2, B.Bk>, +i: Nat, +hlen: {Nat.is_lt(i, SC.length(B.Bk, bs)) == True{} : Bool}, +l: U32, +w: U32, +hne: {ST.isbf(B.at(bs, i), w, l) == False{} : Bool}, +m: Nat) -> {ST.anyb(IM.bupd(bs, i, B.BE{}), m, l, w) == ST.anyb(bs, m, l, w) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +e1 = Equal.cong(Bool, Bool, z => Bool.or(z, ST.anyb(IM.bupd(bs, i, B.BE{}), q, l, w)), ST.isbf(B.at(IM.bupd(bs, i, B.BE{}), q), w, l), ST.isbf(B.at(bs, q), w, l), ib_c(bs, i, hlen, q, l, w, hne, Nat.is_eq(i, q), {==}))
      Equal.trans(Bool, ST.anyb(IM.bupd(bs, i, B.BE{}), 1n+q, l, w), Bool.or(ST.isbf(B.at(bs, q), w, l), ST.anyb(IM.bupd(bs, i, B.BE{}), q, l, w)), ST.anyb(bs, 1n+q, l, w), e1, Equal.cong(Bool, Bool, z => Bool.or(ST.isbf(B.at(bs, q), w, l), z), ST.anyb(IM.bupd(bs, i, B.BE{}), q, l, w), ST.anyb(bs, q, l, w), anyb_rm(bs, i, hlen, l, w, hne, q)))

def isbf_ne_c(+w0: U32, +l0: U32, +w: U32, +lx: U32, +s: Nat, +x: Nat, +hsi: {UD.v(H.slot(l0)) == s : Nat}, +hx: {UD.v(H.slot(lx)) == x : Nat}, +hne: {Nat.is_eq(x, s) == False{} : Bool}, +c: Bool, +hc: {U32.is_eq(l0, lx) == c : Bool}) -> {Bool.and(U32.is_eq(w0, w), c) == False{} : Bool}:
  match c:
    case False{}:
      WR.and_false(U32.is_eq(w0, w))
    case True{}:
      +el = A.eq_of(l0, lx, hc)
      +exq = Equal.trans(Nat, x, UD.v(H.slot(lx)), s, Equal.sym(Nat, UD.v(H.slot(lx)), x, hx), Equal.trans(Nat, UD.v(H.slot(lx)), UD.v(H.slot(l0)), s, Equal.cong(U32, Nat, z => UD.v(H.slot(z)), lx, l0, Equal.sym(U32, l0, lx, el)), hsi))
      Empty.absurd({Bool.and(U32.is_eq(w0, w), True{}) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(x, s), False{}, Equal.sym(Bool, Nat.is_eq(x, s), True{}, L.subst(Nat, z => {Nat.is_eq(x, z) == True{} : Bool}, x, s, exq, N.is_eq_refl(x))), hne)))

# the emptied bucket (slot s) is not the bucket of another slot x
def isbf_ne(+b: B.Bk, +w: U32, +lx: U32, +s: Nat, +x: Nat, +hsi: {UD.v(H.slot(B.lnk(b))) == s : Nat}, +hx: {UD.v(H.slot(lx)) == x : Nat}, +hne: {Nat.is_eq(x, s) == False{} : Bool}) -> {ST.isbf(b, w, lx) == False{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w0, +l0, +k0}:
      isbf_ne_c(w0, l0, w, lx, s, x, hsi, hx, hne, U32.is_eq(l0, lx), {==})

# THEOREM: emptying slot s's bucket leaves a bucket for every other slot
def has_rm(~V: Data, +one: Nat, +h1: {one == 1n : Nat}, +sd: Nat, +hsd: {Nat.is_lt(3n+sd, 32n) == True{} : Bool}, +fr: Nat, +el: List<&2, Maybe<&2, V>>, +hfr: {Nat.is_le(fr, SC.pow2(sd)) == True{} : Bool}, +bs: List<&2, B.Bk>, +no: Nat, +i: Nat, +hlen: {Nat.is_lt(i, SC.length(B.Bk, bs)) == True{} : Bool}, +s: Nat, +hsi: {UD.v(H.slot(B.lnk(B.at(bs, i)))) == s : Nat}, +ll: List<&2, U32>, +xs: List<&2, Nat>, +hs: {NL.memn(s, xs) == False{} : Bool}, +hb: {ST.sall(~V, ST.PLive{fr, el}, xs) == True{} : Bool}, +h: {ST.hasall(~V, bs, no, ll, xs) == True{} : Bool}) -> {ST.hasall(~V, IM.bupd(bs, i, B.BE{}), no, ll, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx0 = UL.bnd_of(~V, x, Con{x, t}, fr, el, sd, hfr, hb, UL.self_in(x, t))
      +hxs = NL.or_ff_l(Nat.is_eq(x, s), NL.memn(s, t), hs)
      +hn = isbf_ne(B.at(bs, i), ST.lw(ll, x, 2n), LK.lnk(x), s, x, hsi, UL.ix_o(one, h1, x, sd, hsd, hx0), hxs)
      +e = anyb_rm(bs, i, hlen, LK.lnk(x), ST.lw(ll, x, 2n), hn, no)
      +h0 = L.and_left(ST.anyb(bs, no, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, no, ll, t), h)
      L.and_intro(ST.anyb(IM.bupd(bs, i, B.BE{}), no, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, IM.bupd(bs, i, B.BE{}), no, ll, t), Equal.trans(Bool, ST.anyb(IM.bupd(bs, i, B.BE{}), no, LK.lnk(x), ST.lw(ll, x, 2n)), ST.anyb(bs, no, LK.lnk(x), ST.lw(ll, x, 2n)), True{}, e, h0), has_rm(~V, one, h1, sd, hsd, fr, el, hfr, bs, no, i, hlen, s, hsi, ll, t, NL.or_ff_r(Nat.is_eq(x, s), NL.memn(s, t), hs), L.and_right(Bool.and(Nat.is_lt(x, fr), ST.live(~V, el, x)), ST.sall(~V, ST.PLive{fr, el}, t), hb), L.and_right(ST.anyb(bs, no, LK.lnk(x), ST.lw(ll, x, 2n)), ST.hasall(~V, bs, no, ll, t), h)))

def brm_b(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +ll: List<&2, U32>, +b0: B.Bk, +hb: {ST.bslb(SC.append(Nat, a, Con{s, b}), ll, b0) == True{} : Bool}, +hne: {B.implies(B.occ(b0), Bool.not(Nat.is_eq(s, UD.v(H.slot(B.lnk(b0)))))) == True{} : Bool}) -> {ST.bslb(SC.append(Nat, a, b), ll, b0) == True{} : Bool}:
  match b0:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      +x = UD.v(H.slot(l))
      +hm = L.and_left(NL.memn(x, SC.append(Nat, a, Con{s, b})), U32.is_eq(ST.lw(ll, x, 2n), w), hb)
      +hm2 = L.subst(Bool, z => {z == True{} : Bool}, NL.memn(x, SC.append(Nat, a, Con{s, b})), Bool.or(NL.memn(x, SC.append(Nat, a, b)), Nat.is_eq(s, x)), NL.memn_mid(x, a, s, b), hm)
      +hm3 = L.subst(Bool, z => {Bool.or(NL.memn(x, SC.append(Nat, a, b)), z) == True{} : Bool}, Nat.is_eq(s, x), False{}, L.not_true(Nat.is_eq(s, x), hne), hm2)
      L.and_intro(NL.memn(x, SC.append(Nat, a, b)), U32.is_eq(ST.lw(ll, x, 2n), w), Equal.trans(Bool, NL.memn(x, SC.append(Nat, a, b)), Bool.or(NL.memn(x, SC.append(Nat, a, b)), False{}), True{}, Equal.sym(Bool, Bool.or(NL.memn(x, SC.append(Nat, a, b)), False{}), NL.memn(x, SC.append(Nat, a, b)), WR.or_false(NL.memn(x, SC.append(Nat, a, b)))), hm3), L.and_right(NL.memn(x, SC.append(Nat, a, Con{s, b})), U32.is_eq(ST.lw(ll, x, 2n), w), hb))


def imp_ne(+bs: List<&2, B.Bk>, +no: Nat, +huq: {B.all_lt(B.PUniq{bs}, no) == True{} : Bool}, +i: Nat, +q: Nat, +hi: {Nat.is_lt(i, no) == True{} : Bool}, +hq: {Nat.is_lt(q, no) == True{} : Bool}, +hqi: {Nat.is_eq(q, i) == False{} : Bool}, +hoi: {B.occ(B.at(bs, i)) == True{} : Bool}, +s: Nat, +hsi: {UD.v(H.slot(B.lnk(B.at(bs, i)))) == s : Nat}, +c: Bool, +hc: {B.occ(B.at(bs, q)) == c : Bool}) -> {B.implies(c, Bool.not(Nat.is_eq(s, UD.v(H.slot(B.lnk(B.at(bs, q))))))) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e0 = TL.slot_ne(bs, no, huq, i, q, hi, hq, hqi, hoi, hc)
      +e1 = L.subst(Nat, z => {Nat.is_eq(UD.v(H.slot(B.lnk(B.at(bs, q)))), z) == False{} : Bool}, UD.v(H.slot(B.lnk(B.at(bs, i)))), s, hsi, e0)
      NL.not_f(Nat.is_eq(s, UD.v(H.slot(B.lnk(B.at(bs, q))))), NL.ne_sym(UD.v(H.slot(B.lnk(B.at(bs, q)))), s, e1))

def br_c(+bs: List<&2, B.Bk>, +no: Nat, +huq: {B.all_lt(B.PUniq{bs}, no) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, no) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, bs)) == True{} : Bool}, +hoi: {B.occ(B.at(bs, i)) == True{} : Bool}, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hsi: {UD.v(H.slot(B.lnk(B.at(bs, i)))) == s : Nat}, +ll: List<&2, U32>, +h: {ST.bsl(bs, SC.append(Nat, a, Con{s, b}), ll, no) == True{} : Bool}, +q: Nat, +hq: {Nat.is_lt(q, no) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(i, q) == c : Bool}) -> {ST.bslb(SC.append(Nat, a, b), ll, B.at(IM.bupd(bs, i, B.BE{}), q)) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(B.Bk, z => {ST.bslb(SC.append(Nat, a, b), ll, z) == True{} : Bool}, B.BE{}, B.at(IM.bupd(bs, i, B.BE{}), q), Equal.sym(B.Bk, B.at(IM.bupd(bs, i, B.BE{}), q), B.BE{}, IM.at_bu_eq(bs, i, B.BE{}, hlen, q, hc)), {==})
    case False{}:
      +hb = brm_b(a, s, b, ll, B.at(bs, q), TF.bsl_inst(bs, SC.append(Nat, a, Con{s, b}), ll, no, h, q, hq), imp_ne(bs, no, huq, i, q, hi, hq, NL.ne_sym(i, q, hc), hoi, s, hsi, B.occ(B.at(bs, q)), {==}))
      L.subst(B.Bk, z => {ST.bslb(SC.append(Nat, a, b), ll, z) == True{} : Bool}, B.at(bs, q), B.at(IM.bupd(bs, i, B.BE{}), q), Equal.sym(B.Bk, B.at(IM.bupd(bs, i, B.BE{}), q), B.at(bs, q), IM.at_bupd_other(bs, i, B.BE{}, q, hc)), hb)

# THEOREM: emptying slot s's bucket: every full bucket's slot is listed
# once s is taken off the list
def bsl_rm(+bs: List<&2, B.Bk>, +no: Nat, +huq: {B.all_lt(B.PUniq{bs}, no) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, no) == True{} : Bool}, +hlen: {Nat.is_lt(i, SC.length(B.Bk, bs)) == True{} : Bool}, +hoi: {B.occ(B.at(bs, i)) == True{} : Bool}, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +hsi: {UD.v(H.slot(B.lnk(B.at(bs, i)))) == s : Nat}, +ll: List<&2, U32>, +h: {ST.bsl(bs, SC.append(Nat, a, Con{s, b}), ll, no) == True{} : Bool}, +m: Nat, +hm: {Nat.is_le(m, no) == True{} : Bool}) -> {ST.bsl(IM.bupd(bs, i, B.BE{}), SC.append(Nat, a, b), ll, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +hq = N.succ_le_lt(q, no, hm)
      L.and_intro(ST.bslb(SC.append(Nat, a, b), ll, B.at(IM.bupd(bs, i, B.BE{}), q)), ST.bsl(IM.bupd(bs, i, B.BE{}), SC.append(Nat, a, b), ll, q), br_c(bs, no, huq, i, hi, hlen, hoi, a, s, b, hsi, ll, h, q, hq, Nat.is_eq(i, q), {==}), bsl_rm(bs, no, huq, i, hi, hlen, hoi, a, s, b, hsi, ll, h, q, N.lt_le(q, no, hq)))
