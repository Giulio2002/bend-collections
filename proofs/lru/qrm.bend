import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../math/word.bend as WD
import ../../src/containers/hash_table.bend as H
import ../../src/containers/lru.bend as LR
import ../hash_table/words.bend as WR
import ../hash_table/keys.bend as K
import ../hash_table/table.bend as TB
import ../hash_table/buckets.bend as B
import ../hash_table/arr.bend as AX
import ../hash_table/probe_impl.bend as PI
import ../hash_table/cyc.bend as CY
import ../hash_table/qprobe.bend as QP

# The fused one-character remove loop qrm is the model probe B.pf followed by
# the removal at the bucket it finds (nothing when it finds none).


def qrm_of(~V: Data, r: B.Res, tab: Array<U32>, +mask: U32, +cap: U32, +n: U32, +head: U32, +tail: U32, +free: U32, m: Array<U32>, ks: Array<String>, ents: Array<Maybe<&2, V>>, lk: Array<U32>) -> LR.LRU<&2, V> & Maybe<&2, V>:
  match r:
    case B.RHit{+at, +l}:
      LR.drop_slot(&2, V, LR.F{cap, n, head, tail, free, m, H.del_at(tab, mask, U32.from_nat(at)), ks, ents, lk}, H.slot(l), 2)
    case B.REnd{at}:
      (LR.F{cap, n, head, tail, free, m, tab, ks, ents, lk}, None{})

def rq0(~V: Data, +cap: U32, +nn: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +tabT: AR.Tree<U32>, +key: String, +bs: List<&2, B.Bk>, +nb: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +ms: B.MS) -> {LR.qrm(&2, V, 0n, QP.qstep_of(ms, AR.thaw(U32, tabT)), mask, w, i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, nb, 0n, ms, UD.v(i)), AR.thaw(U32, tabT), mask, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}:
  match ms:
    case B.MEnd{}:
      {==}
    case B.MHit{+l}:
      Equal.cong(U32, LR.LRU<&2, V> & Maybe<&2, V>, z => LR.drop_slot(&2, V, LR.F{cap, nn, head, tail, free, AR.thaw(U32, mT), H.del_at(AR.thaw(U32, tabT), mask, z), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(l), 2), i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MNext{}:
      {==}

def rq1(~V: Data, +cap: U32, +nn: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +tabT: AR.Tree<U32>, +key: String, +bs: List<&2, B.Bk>, +nb: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +p: Nat, +hnext: {UD.v(H.bnext(i, mask)) == Nat.mod(1n+UD.v(i), nb) : Nat}, +rec: {LR.qrm(&2, V, p, H.qstep(AR.thaw(U32, tabT), H.bnext(i, mask), w), mask, w, H.bnext(i, mask), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, nb, p, B.mstep(key, B.at(bs, UD.v(H.bnext(i, mask)))), UD.v(H.bnext(i, mask))), AR.thaw(U32, tabT), mask, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, +ms: B.MS) -> {LR.qrm(&2, V, 1n+p, QP.qstep_of(ms, AR.thaw(U32, tabT)), mask, w, i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, nb, 1n+p, ms, UD.v(i)), AR.thaw(U32, tabT), mask, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}:
  match ms:
    case B.MEnd{}:
      {==}
    case B.MHit{+l}:
      Equal.cong(U32, LR.LRU<&2, V> & Maybe<&2, V>, z => LR.drop_slot(&2, V, LR.F{cap, nn, head, tail, free, AR.thaw(U32, mT), H.del_at(AR.thaw(U32, tabT), mask, z), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)}, H.slot(l), 2), i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MNext{}:
      L.subst(Nat, z => {LR.qrm(&2, V, p, H.qstep(AR.thaw(U32, tabT), H.bnext(i, mask), w), mask, w, H.bnext(i, mask), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, nb, p, B.mstep(key, B.at(bs, z)), z), AR.thaw(U32, tabT), mask, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, UD.v(H.bnext(i, mask)), Nat.mod(1n+UD.v(i), nb), hnext, rec)


# THEOREM: the fused loop is the model probe then the removal
def qrm_ok(~V: Data, +cap: U32, +nn: U32, +head: U32, +tail: U32, +free: U32, +mT: AR.Tree<U32>, +ksT: AR.Tree<String>, +eT: AR.Tree<Maybe<&2, V>>, +lkT: AR.Tree<U32>, +one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +kl0: List<&2, String>, +c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +f: Nat, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}) -> {LR.qrm(&2, V, f, H.qstep(AR.thaw(U32, tabT), i, H.short_word(c)), CY.msk(k), H.short_word(c), i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(SCon{Chr{c}, SNil{}}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), f, B.mstep(SCon{Chr{c}, SNil{}}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(i))), UD.v(i)), AR.thaw(U32, tabT), CY.msk(k), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}:
  match f:
    case 0n:
      +tb = AR.slots(U32, tabT)
      +n = SC.pow2(k)
      +bs = TB.buckets(tb, kl0, n)
      +w = H.short_word(c)
      +key = {SCon{Chr{c}, SNil{}} : String}
      +hb = N.double_lt_bit(True{}, UD.v(i), SC.pow2(k), hi)
      +ew = AX.ix_w(i, 1n+k, hk31, hb)
      +el = AX.ix_l(i, 1n+k, hk31, hb)
      +hwb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(1n+k), N.lt_succ(Nat.double(UD.v(i))), hb))
      +hlb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(UD.v(i)), UD.v(U32.inc(U32.shl(i))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), el), hb)
      +x = TB.nth0(tb, UD.v(U32.shl(i)))
      +l = TB.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = PI.dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, PI.wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = QP.qdec(w, x, l)
      +em = Equal.trans(B.MS, ms, B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), QP.qdecide(c, hc, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd)))
      +es = QP.qstep(1n+k, tabT, i, w, hk31, pt, hwb0, hlb0)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +p3 = rq0(~V, cap, nn, head, tail, free, mT, ksT, eT, lkT, tabT, key, bs, n, CY.msk(k), w, i, k, hk32, hi, ms)
      +p2 = L.subst(B.MS, m => {LR.qrm(&2, V, 0n, QP.qstep_of(ms, AR.thaw(U32, tabT)), CY.msk(k), H.short_word(c), i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, n, 0n, m, UD.v(i)), AR.thaw(U32, tabT), CY.msk(k), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.QStep, s => {LR.qrm(&2, V, 0n, s, CY.msk(k), H.short_word(c), i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, n, 0n, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), AR.thaw(U32, tabT), CY.msk(k), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, QP.qstep_of(ms, AR.thaw(U32, tabT)), H.qstep(AR.thaw(U32, tabT), i, w), Equal.sym(H.QStep, H.qstep(AR.thaw(U32, tabT), i, w), QP.qstep_of(ms, AR.thaw(U32, tabT)), es), p2)
    case 1n+p:
      +tb = AR.slots(U32, tabT)
      +n = SC.pow2(k)
      +bs = TB.buckets(tb, kl0, n)
      +w = H.short_word(c)
      +key = {SCon{Chr{c}, SNil{}} : String}
      +hb = N.double_lt_bit(True{}, UD.v(i), SC.pow2(k), hi)
      +ew = AX.ix_w(i, 1n+k, hk31, hb)
      +el = AX.ix_l(i, 1n+k, hk31, hb)
      +hwb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(1n+k), N.lt_succ(Nat.double(UD.v(i))), hb))
      +hlb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(UD.v(i)), UD.v(U32.inc(U32.shl(i))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), el), hb)
      +x = TB.nth0(tb, UD.v(U32.shl(i)))
      +l = TB.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = PI.dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, PI.wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = QP.qdec(w, x, l)
      +em = Equal.trans(B.MS, ms, B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), QP.qdecide(c, hc, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd)))
      +es = QP.qstep(1n+k, tabT, i, w, hk31, pt, hwb0, hlb0)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +hks = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), AX.pow_le32(one, h1, 1n+k, hk31)))
      +hi1 = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k), hi)
      +hnext = Equal.trans(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), WD.sc(k, one)), Nat.mod(1n+UD.v(i), n), CY.next_val(one, h1, k, i, hks, hi1), Equal.cong(Nat, Nat, z => Nat.mod(1n+UD.v(i), z), WD.sc(k, one), SC.pow2(k), Equal.sym(Nat, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k))))
      +hi2 = L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, Nat.mod(1n+UD.v(i), n), UD.v(H.bnext(i, CY.msk(k))), Equal.sym(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), n), hnext), PI.mod_lt(n, N.succ_le_lt(0n, n, N.pow2_pos(k)), 1n+UD.v(i)))
      +p3 = rq1(~V, cap, nn, head, tail, free, mT, ksT, eT, lkT, tabT, key, bs, n, CY.msk(k), w, i, k, hk32, hi, p, hnext, qrm_ok(~V, cap, nn, head, tail, free, mT, ksT, eT, lkT, one, h1, k, hk31, tabT, pt, sd, kl0, c, hc, hwell, p, H.bnext(i, CY.msk(k)), hi2), ms)
      +p2 = L.subst(B.MS, m => {LR.qrm(&2, V, 1n+p, QP.qstep_of(ms, AR.thaw(U32, tabT)), CY.msk(k), H.short_word(c), i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, n, 1n+p, m, UD.v(i)), AR.thaw(U32, tabT), CY.msk(k), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.QStep, s => {LR.qrm(&2, V, 1n+p, s, CY.msk(k), H.short_word(c), i, cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) == qrm_of(~V, B.pf(key, bs, n, 1n+p, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), AR.thaw(U32, tabT), CY.msk(k), cap, nn, head, tail, free, AR.thaw(U32, mT), AR.thaw(String, ksT), AR.thaw(Maybe<&2, V>, eT), AR.thaw(U32, lkT)) : LR.LRU<&2, V> & Maybe<&2, V>}, QP.qstep_of(ms, AR.thaw(U32, tabT)), H.qstep(AR.thaw(U32, tabT), i, w), Equal.sym(H.QStep, H.qstep(AR.thaw(U32, tabT), i, w), QP.qstep_of(ms, AR.thaw(U32, tabT)), es), p2)
