import Base
import ../../lib/logic.bend as L
import ../../lib/array.bend as AR
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/hash_table.bend as S
import ../../../spec/containers/lru.bend as SP
import ../../lib/u32div.bend as UD
import ../hash_table/table.bend as TB
import ../hash_table/buckets.bend as B
import ../../../src/containers/hash_table.bend as H
import ./state.bend as ST
import ./lists.bend as LS
import ./trace.bend as TR
import ./unlink.bend as UL
import ../hash_table/insf.bend as IF
import ../../lib/nat_list.bend as NL
import ../../lib/links.bend as LK
import ../../lib/words32.bend as W32

# Rebuilding the invariant after an operation that only re-links the
# recency list: it permutes the listed slots and writes link words.


# ---- sub-lists ----

def subl_refl(+xs: List<&2, Nat>) -> {IF.subl(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, Con{x, t}), IF.subl(t, Con{x, t}), UL.self_in(x, t), IF.subl_cons(t, t, x, subl_refl(t)))

def subl_ml(+xs: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {IF.subl(xs, a) == True{} : Bool}) -> {IF.subl(xs, SC.append(Nat, a, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, SC.append(Nat, a, b)), IF.subl(t, SC.append(Nat, a, b)), NL.mem_app_l(x, a, b, L.and_left(NL.memn(x, a), IF.subl(t, a), h)), subl_ml(t, a, b, L.and_right(NL.memn(x, a), IF.subl(t, a), h)))

def subl_mr(+xs: List<&2, Nat>, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {IF.subl(xs, b) == True{} : Bool}) -> {IF.subl(xs, SC.append(Nat, a, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, SC.append(Nat, a, b)), IF.subl(t, SC.append(Nat, a, b)), NL.mem_app_r(x, a, b, L.and_left(NL.memn(x, b), IF.subl(t, b), h)), subl_mr(t, a, b, L.and_right(NL.memn(x, b), IF.subl(t, b), h)))

def subl_app(+a: List<&2, Nat>, +b: List<&2, Nat>, +ys: List<&2, Nat>, +ha: {IF.subl(a, ys) == True{} : Bool}, +hb: {IF.subl(b, ys) == True{} : Bool}) -> {IF.subl(SC.append(Nat, a, b), ys) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+x, +t}:
      L.and_intro(NL.memn(x, ys), IF.subl(SC.append(Nat, t, b), ys), L.and_left(NL.memn(x, ys), IF.subl(t, ys), ha), subl_app(t, b, ys, L.and_right(NL.memn(x, ys), IF.subl(t, ys), ha), hb))

# ---- predicates over a sub-list ----

def sall_sub(~V: Data, +p: ST.SP1<V>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +h: {ST.sall(~V, p, xs) == True{} : Bool}, +sub: {IF.subl(ys, xs) == True{} : Bool}) -> {ST.sall(~V, p, ys) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      L.and_intro(ST.sev(~V, p, y), ST.sall(~V, p, t), LS.sall_mem(~V, p, y, xs, h, L.and_left(NL.memn(y, xs), IF.subl(t, xs), sub)), sall_sub(~V, p, xs, t, h, L.and_right(NL.memn(y, xs), IF.subl(t, xs), sub)))

def bslb_sub(+sl: List<&2, Nat>, +sl2: List<&2, Nat>, +ll: List<&2, U32>, +b: B.Bk, +h: {ST.bslb(sl, ll, b) == True{} : Bool}, +sub: {IF.subl(sl, sl2) == True{} : Bool}) -> {ST.bslb(sl2, ll, b) == True{} : Bool}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{+w, +l, +k}:
      L.and_intro(NL.memn(UD.v(H.slot(l)), sl2), U32.is_eq(ST.lw(ll, UD.v(H.slot(l)), 2n), w), IF.memn_sub(UD.v(H.slot(l)), sl, sl2, sub, L.and_left(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(ST.lw(ll, UD.v(H.slot(l)), 2n), w), h)), L.and_right(NL.memn(UD.v(H.slot(l)), sl), U32.is_eq(ST.lw(ll, UD.v(H.slot(l)), 2n), w), h))

def bsl_sub(+bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +sl2: List<&2, Nat>, +ll: List<&2, U32>, +m: Nat, +h: {ST.bsl(bs, sl, ll, m) == True{} : Bool}, +sub: {IF.subl(sl, sl2) == True{} : Bool}) -> {ST.bsl(bs, sl2, ll, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(ST.bslb(sl2, ll, B.at(bs, j)), ST.bsl(bs, sl2, ll, j), bslb_sub(sl, sl2, ll, B.at(bs, j), L.and_left(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h), sub), bsl_sub(bs, sl, sl2, ll, j, L.and_right(ST.bslb(sl, ll, B.at(bs, j)), ST.bsl(bs, sl, ll, j), h), sub))

def tr_eq_bool(+a: Bool, +b: Bool, +e: {a == b : Bool}, +h: {b == True{} : Bool}) -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)


# THEOREM: re-linking the recency list (a permutation sl2 of sl, link-word
# writes to its slots) keeps the invariant.
def good_lk(~V: Data, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +k: Nat, +sd: Nat, +tabT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +hg: {ST.good(~V, ST.LS{cap, n, head, tail, free, mT, k, sd, tabT, ksT, eT, lkT, sl, fl}) == True{} : Bool}, +head2: U32, +tail2: U32, +lkT2: AR.Tree<U32>, +sl2: List<&2, Nat>, +tr: TR.Tr, +hp2: {AR.perfect(U32, 3n+sd, lkT2) == True{} : Bool}, +hs2: {AR.slots(U32, lkT2) == TR.app(AR.slots(U32, lkT), tr) : List<&2, U32>}, +hlo: {TR.trlo(tr) == True{} : Bool}, +hin: {TR.trin(tr, sl2) == True{} : Bool}, +hseg: {ST.seg(AR.slots(U32, lkT2), sl2, 0, 0) == True{} : Bool}, +hh: {U32.is_eq(head2, LK.fst_or(sl2, 0)) == True{} : Bool}, +ht: {U32.is_eq(tail2, LK.last_or(sl2, 0)) == True{} : Bool}, +hsub: {IF.subl(sl, sl2) == True{} : Bool}, +hsub2: {IF.subl(sl2, sl) == True{} : Bool}, +hnd: {NL.nodupn(sl2) == True{} : Bool}, +hlen: {SC.length(Nat, sl2) == SC.length(Nat, sl) : Nat}, +hkeys: {S.nodup(SP.keys_of(~V, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2))) == True{} : Bool}) -> {ST.good(~V, ST.LS{cap, n, head2, tail2, free, mT, k, sd, tabT, ksT, eT, lkT2, sl2, fl}) == True{} : Bool}:
  +bsl0 = bsl_sub(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), sl, sl2, AR.slots(U32, lkT), SC.pow2(k), ST.g_cbsl(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), hsub)
  +bsl1 = L.subst(List<&2, U32>, z => {ST.bsl(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), sl2, z, SC.pow2(k)) == True{} : Bool}, TR.app(AR.slots(U32, lkT), tr), AR.slots(U32, lkT2), Equal.sym(List<&2, U32>, AR.slots(U32, lkT2), TR.app(AR.slots(U32, lkT), tr), hs2), tr_eq_bool(ST.bsl(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), sl2, TR.app(AR.slots(U32, lkT), tr), SC.pow2(k)), ST.bsl(TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), sl2, AR.slots(U32, lkT), SC.pow2(k)), TR.bsl_tr(AR.slots(U32, lkT), tr, hlo, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), sl2, SC.pow2(k)), bsl0))
  +has0 = sall_sub(~V, ST.PHas{TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), AR.slots(U32, lkT)}, sl, sl2, ST.g_chas(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), hsub2)
  +has1 = L.subst(List<&2, U32>, z => {ST.hasall(~V, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), z, sl2) == True{} : Bool}, TR.app(AR.slots(U32, lkT), tr), AR.slots(U32, lkT2), Equal.sym(List<&2, U32>, AR.slots(U32, lkT2), TR.app(AR.slots(U32, lkT), tr), hs2), tr_eq_bool(ST.hasall(~V, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), TR.app(AR.slots(U32, lkT), tr), sl2), ST.hasall(~V, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), AR.slots(U32, lkT), sl2), TR.has_tr(~V, AR.slots(U32, lkT), tr, hlo, TB.buckets(AR.slots(U32, tabT), AR.slots(String, ksT), SC.pow2(k)), SC.pow2(k), sl2), has0))
  +csl2 = sall_sub(~V, ST.PLive{UD.v(W32.nth0(AR.slots(U32, mT), 0n)), AR.slots(Maybe<&2, V>, eT)}, sl, sl2, ST.g_csl(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), hsub2)
  +clen2 = L.subst(Nat, z => {Nat.is_eq(z, UD.v(n)) == True{} : Bool}, SC.length(Nat, sl), SC.length(Nat, sl2), Equal.sym(Nat, SC.length(Nat, sl2), SC.length(Nat, sl), hlen), ST.g_clen(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg))
  +keys2 = L.subst(List<&2, U32>, z => {S.nodup(SP.keys_of(~V, ST.es(~V, z, AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2))) == True{} : Bool}, TR.app(AR.slots(U32, lkT), tr), AR.slots(U32, lkT2), Equal.sym(List<&2, U32>, AR.slots(U32, lkT2), TR.app(AR.slots(U32, lkT), tr), hs2), L.subst(List<&2, SP.Ent<V>>, z => {S.nodup(SP.keys_of(~V, z)) == True{} : Bool}, ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2), ST.es(~V, TR.app(AR.slots(U32, lkT), tr), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2), Equal.sym(List<&2, SP.Ent<V>>, ST.es(~V, TR.app(AR.slots(U32, lkT), tr), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2), ST.es(~V, AR.slots(U32, lkT), AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2), TR.es_tr(~V, AR.slots(U32, lkT), tr, hlo, AR.slots(String, ksT), AR.slots(Maybe<&2, V>, eT), sl2)), hkeys))
  +out = TR.out_of_in(~V, tr, sl2, fl, UD.v(W32.nth0(AR.slots(U32, mT), 0n)), AR.slots(Maybe<&2, V>, eT), hin, csl2, ST.g_cfl(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg))
  +fll2 = L.subst(List<&2, U32>, z => {ST.fll(z, fl) == True{} : Bool}, TR.app(AR.slots(U32, lkT), tr), AR.slots(U32, lkT2), Equal.sym(List<&2, U32>, AR.slots(U32, lkT2), TR.app(AR.slots(U32, lkT), tr), hs2), tr_eq_bool(ST.fll(TR.app(AR.slots(U32, lkT), tr), fl), ST.fll(AR.slots(U32, lkT), fl), TR.fll_tr(AR.slots(U32, lkT), tr, hlo, fl, out), ST.g_cfll(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg)))
  +cnt2 = L.subst(Nat, z => {Nat.is_eq(Nat.add(z, SC.length(Nat, fl)), UD.v(W32.nth0(AR.slots(U32, mT), 0n))) == True{} : Bool}, SC.length(Nat, sl), SC.length(Nat, sl2), Equal.sym(Nat, SC.length(Nat, sl2), SC.length(Nat, sl), hlen), ST.g_cfcnt(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg))
  ST.good_intro(~V, cap, n, head2, tail2, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT2, sl2, fl, ST.g_ck(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_csdk(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cpt(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cpk(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cpe(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), hp2, ST.g_cpm(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cmask(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cbits(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_csize(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cdepth(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cfresh(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cwell(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cclus(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cuniq(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cn(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cload(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_ccap(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), bsl1, has1, csl2, hnd, clen2, hh, ht, hseg, keys2, ST.g_cfree(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), fll2, ST.g_cfl(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), ST.g_cfnd(~V, cap, n, head, tail, free, W32.nth0(AR.slots(U32, mT), 0n), W32.nth0(AR.slots(U32, mT), 1n), W32.nth0(AR.slots(U32, mT), 2n), W32.nth0(AR.slots(U32, mT), 6n), W32.nth0(AR.slots(U32, mT), 7n), AR.perfect(U32, 5n, mT), k, sd, tabT, AR.slots(String, ksT), AR.perfect(String, sd, ksT), eT, lkT, sl, fl, hg), cnt2)
