import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../math/word.bend as WD
import ../../src/math/hash.bend as HS
import ../../src/containers/hash_table.bend as H
import ../../src/containers/lru.bend as LR
import ../hash_table/table.bend as TB
import ../hash_table/buckets.bend as B
import ../hash_table/cyc.bend as CY
import ../hash_table/modn.bend as M
import ../hash_table/arr.bend as AX
import ../hash_table/inv.bend as IV
import ../hash_table/insm.bend as IM
import ../hash_table/tools.bend as TL
import ../hash_table/probe_impl.bend as PI
import ../hash_table/probe_all.bend as PA
import ../hash_table/delw.bend as DW
import ../hash_table/keys.bend as K

# del_link finds the bucket holding link l by walking the probe path of its
# word and comparing links only: it deletes that bucket.


# a full bucket's link is the raw link word
def lnk_c(+x: U32, +y: U32, +kl: List<&2, String>, +e: Bool, +ho: {B.occ(TB.dec_c(x, y, kl, e)) == True{} : Bool}) -> {B.lnk(TB.dec_c(x, y, kl, e)) == y : U32}:
  match e:
    case True{}:
      Empty.absurd({B.lnk(B.BE{}) == y : U32}, L.false_true(ho))
    case False{}:
      {==}

def lnk_raw(+tb: List<&2, U32>, +kl: List<&2, String>, +n: Nat, +p: Nat, +hp: {Nat.is_lt(p, n) == True{} : Bool}, +ho: {B.occ(B.at(TB.buckets(tb, kl, n), p)) == True{} : Bool}) -> {B.lnk(B.at(TB.buckets(tb, kl, n), p)) == TB.nth0(tb, 1n+Nat.double(p)) : U32}:
  +e = TB.at_buckets(tb, kl, n, p, hp)
  +ho2 = L.subst(B.Bk, z => {B.occ(z) == True{} : Bool}, B.at(TB.buckets(tb, kl, n), p), TB.dec(tb, kl, p), e, ho)
  Equal.trans(U32, B.lnk(B.at(TB.buckets(tb, kl, n), p)), B.lnk(TB.dec(tb, kl, p)), TB.nth0(tb, 1n+Nat.double(p)), Equal.cong(B.Bk, U32, z => B.lnk(z), B.at(TB.buckets(tb, kl, n), p), TB.dec(tb, kl, p), e), lnk_c(TB.nth0(tb, Nat.double(p)), TB.nth0(tb, 1n+Nat.double(p)), kl, U32.is_eq(TB.nth0(tb, Nat.double(p)), 0), ho2))

def op_c(+bs: List<&2, B.Bk>, +n: Nat, +h: Nat, +q: Nat, +hp: {Bool.and(B.occ(B.at(bs, M.pos(n, h, q))), B.occpath(bs, n, h, q)) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hq: {Nat.is_lt(j, q) == True{} : Bool} -> {B.occ(B.at(bs, M.pos(n, h, j))) == True{} : Bool}) -> {B.occ(B.at(bs, M.pos(n, h, j))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {B.occ(B.at(bs, M.pos(n, h, z))) == True{} : Bool}, q, j, Equal.sym(Nat, j, q, N.eq_from_is_eq(j, q, hc)), L.and_left(B.occ(B.at(bs, M.pos(n, h, q))), B.occpath(bs, n, h, q), hp))
    case False{}:
      rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc))

# the buckets before position d of a full path are full
def op_inst(+bs: List<&2, B.Bk>, +n: Nat, +h: Nat, +d: Nat, +hp: {B.occpath(bs, n, h, d) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, d) == True{} : Bool}) -> {B.occ(B.at(bs, M.pos(n, h, j))) == True{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({B.occ(B.at(bs, M.pos(n, h, j))) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      op_c(bs, n, h, q, hp, j, hj, Nat.is_eq(j, q), {==}, hq => op_inst(bs, n, h, q, L.and_right(B.occ(B.at(bs, M.pos(n, h, q))), B.occpath(bs, n, h, q), hp), j, hq))

# one step reads bucket p's raw link
def dstep_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +bp: Nat, +hN: {1n+bp == SC.pow2(k) : Nat}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +kl: List<&2, String>, +i: U32, +p: Nat, +hi: {UD.v(i) == p : Nat}, +hp: {Nat.is_lt(p, 1n+bp) == True{} : Bool}, +l: U32) -> {LR.dstep(AR.thaw(U32, tabT), i, l) == LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(p)), l)) : LR.DStep}:
  +hik = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, 1n+bp, SC.pow2(k), hN, L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, p, UD.v(i), Equal.sym(Nat, UD.v(i), p, hi), hp))
  +hb = N.double_lt_bit(True{}, UD.v(i), SC.pow2(k), hik)
  +el = AX.ix_l(i, 1n+k, hk31, hb)
  +hj = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(UD.v(i)), UD.v(U32.inc(U32.shl(i))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), el), hb)
  +g = AX.getw(1n+k, tabT, U32.inc(U32.shl(i)), hk31, hj, pt)
  +e2 = Equal.trans(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), 1n+Nat.double(p), el, Equal.cong(Nat, Nat, z => 1n+Nat.double(z), UD.v(i), p, hi))
  +g2 = Equal.trans(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tabT), U32.inc(U32.shl(i))), (AR.thaw(U32, tabT), TB.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))), (AR.thaw(U32, tabT), TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(p))), g, Equal.cong(Nat, Array<U32> & U32, z => (AR.thaw(U32, tabT), TB.nth0(AR.slots(U32, tabT), z)), UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(p), e2))
  Equal.cong(Array<U32> & U32, LR.DStep, r => LR.ds_l(l, r), Array.get(U32, AR.thaw(U32, tabT), U32.inc(U32.shl(i))), (AR.thaw(U32, tabT), TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(p))), g2)

def next_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +bp: Nat, +hN: {1n+bp == SC.pow2(k) : Nat}, +i: U32, +hi: {Nat.is_lt(UD.v(i), 1n+bp) == True{} : Bool}) -> {UD.v(H.bnext(i, CY.msk(k))) == Nat.mod(1n+UD.v(i), 1n+bp) : Nat}:
  +hks = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), AX.pow_le32(one, h1, 1n+k, hk31)))
  +e = Equal.trans(Nat, 1n+bp, SC.pow2(k), WD.sc(k, one), hN, AX.pow_one(one, h1, k))
  +hi1 = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, 1n+bp, WD.sc(k, one), e, hi)
  Equal.trans(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), WD.sc(k, one)), Nat.mod(1n+UD.v(i), 1n+bp), CY.next_val(one, h1, k, i, hks, hi1), Equal.cong(Nat, Nat, z => Nat.mod(1n+UD.v(i), z), WD.sc(k, one), 1n+bp, Equal.sym(Nat, 1n+bp, WD.sc(k, one), e)))


def pe_ne(+bp: Nat, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hjd: {Nat.is_eq(j, M.dist(1n+bp, h, e)) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(M.pos(1n+bp, h, j), e) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +ep = N.eq_from_is_eq(M.pos(1n+bp, h, j), e, hc)
      +ej = Equal.trans(Nat, j, M.dist(1n+bp, h, M.pos(1n+bp, h, j)), M.dist(1n+bp, h, e), Equal.sym(Nat, M.dist(1n+bp, h, M.pos(1n+bp, h, j)), j, M.dist_pos(bp, h, j, hh, hj)), Equal.cong(Nat, Nat, z => M.dist(1n+bp, h, z), M.pos(1n+bp, h, j), e, ep))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(j, M.dist(1n+bp, h, e)), False{}, Equal.sym(Bool, Nat.is_eq(j, M.dist(1n+bp, h, e)), True{}, L.subst(Nat, z => {Nat.is_eq(j, z) == True{} : Bool}, j, M.dist(1n+bp, h, e), ej, N.is_eq_refl(j))), hjd)))

def dl_c(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +bp: Nat, +hN: {1n+bp == SC.pow2(k) : Nat}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +kl: List<&2, String>, +huq: {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, tabT), kl, 1n+bp)}, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +w: U32, +l: U32, +kk: String, +hbe: {B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e) == B.BF{w, l, kk} : B.Bk}, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hop: {B.occpath(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +p: Nat, +j: Nat, +iu: U32, +hiu: {UD.v(iu) == M.pos(1n+bp, h, j) : Nat}, +hjd: {Nat.is_le(j, M.dist(1n+bp, h, e)) == True{} : Bool}, +hf: {Nat.is_lt(M.dist(1n+bp, h, e), Nat.add(j, 1n+p)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, M.dist(1n+bp, h, e)) == c : Bool}, rec: @iu2: U32 -> @hiu2: {UD.v(iu2) == M.pos(1n+bp, h, 1n+j) : Nat} -> @hjd2: {Nat.is_le(1n+j, M.dist(1n+bp, h, e)) == True{} : Bool} -> @hf2: {Nat.is_lt(M.dist(1n+bp, h, e), Nat.add(1n+j, p)) == True{} : Bool} -> {LR.dfind(p, LR.dstep(AR.thaw(U32, tabT), iu2, l), CY.msk(k), l, iu2) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}) -> {LR.dfind(1n+p, LR.dstep(AR.thaw(U32, tabT), iu, l), CY.msk(k), l, iu) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}:
  match c:
    case True{}:
      +hpj = M.pos_lt(bp, h, j)
      +E = dstep_ok(one, h1, k, hk31, bp, hN, tabT, pt, kl, iu, M.pos(1n+bp, h, j), hiu, hpj, l)
      +oe = L.subst(B.Bk, z => {B.occ(z) == True{} : Bool}, B.BF{w, l, kk}, B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), Equal.sym(B.Bk, B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), B.BF{w, l, kk}, hbe), {==})
      +le = Equal.cong(B.Bk, U32, z => B.lnk(z), B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), B.BF{w, l, kk}, hbe)
      +ej = N.eq_from_is_eq(j, M.dist(1n+bp, h, e), hc)
      +epe = Equal.trans(Nat, M.pos(1n+bp, h, j), M.pos(1n+bp, h, M.dist(1n+bp, h, e)), e, Equal.cong(Nat, Nat, z => M.pos(1n+bp, h, z), j, M.dist(1n+bp, h, e), ej), M.pos_dist(bp, h, e, hh, he))
      +er = Equal.trans(U32, TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(e)), l, Equal.cong(Nat, U32, z => TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(z)), M.pos(1n+bp, h, j), e, epe), Equal.trans(U32, TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(e)), B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e)), l, Equal.sym(U32, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e)), TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(e)), lnk_raw(AR.slots(U32, tabT), kl, 1n+bp, e, he, oe)), le))
      +ht = L.subst(U32, z => {U32.is_eq(z, l) == True{} : Bool}, l, TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), Equal.sym(U32, TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l, er), K.u32_eq_refl(l))
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +hiuk = L.subst(Nat, z => {Nat.is_lt(UD.v(iu), z) == True{} : Bool}, 1n+bp, SC.pow2(k), hN, L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, M.pos(1n+bp, h, j), UD.v(iu), Equal.sym(Nat, UD.v(iu), M.pos(1n+bp, h, j), hiu), hpj))
      +eiu = Equal.trans(U32, iu, U32.from_nat(UD.v(iu)), U32.from_nat(e), Equal.sym(U32, U32.from_nat(UD.v(iu)), iu, PI.from_v(iu, k, hk32, hiuk)), Equal.cong(Nat, U32, z => U32.from_nat(z), UD.v(iu), e, Equal.trans(Nat, UD.v(iu), M.pos(1n+bp, h, j), e, hiu, epe)))
      +E2 = Equal.cong(Bool, Array<U32>, z => LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), z), CY.msk(k), l, iu), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l), True{}, ht)
      Equal.trans(Array<U32>, LR.dfind(1n+p, LR.dstep(AR.thaw(U32, tabT), iu, l), CY.msk(k), l, iu), LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), CY.msk(k), l, iu), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), Equal.cong(LR.DStep, Array<U32>, s => LR.dfind(1n+p, s, CY.msk(k), l, iu), LR.dstep(AR.thaw(U32, tabT), iu, l), LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), E), Equal.trans(Array<U32>, LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), CY.msk(k), l, iu), H.del_at(AR.thaw(U32, tabT), CY.msk(k), iu), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), E2, Equal.cong(U32, Array<U32>, z => H.del_at(AR.thaw(U32, tabT), CY.msk(k), z), iu, U32.from_nat(e), eiu)))
    case False{}:
      +hpj = M.pos_lt(bp, h, j)
      +E = dstep_ok(one, h1, k, hk31, bp, hN, tabT, pt, kl, iu, M.pos(1n+bp, h, j), hiu, hpj, l)
      +oe = L.subst(B.Bk, z => {B.occ(z) == True{} : Bool}, B.BF{w, l, kk}, B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), Equal.sym(B.Bk, B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), B.BF{w, l, kk}, hbe), {==})
      +le = Equal.cong(B.Bk, U32, z => B.lnk(z), B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), B.BF{w, l, kk}, hbe)
      +hjl = N.lt_or_eq(j, M.dist(1n+bp, h, e), hjd, hc)
      +opj = op_inst(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e), hop, j, hjl)
      +hj = N.lt_trans(j, M.dist(1n+bp, h, e), 1n+bp, hjl, M.dist_lt(bp, h, e))
      +hne = pe_ne(bp, h, hh, e, he, j, hj, hc, Nat.is_eq(M.pos(1n+bp, h, j), e), {==})
      +hl0 = IM.u32_ne(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), M.pos(1n+bp, h, j))), B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e)), TL.slot_ne(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, huq, e, M.pos(1n+bp, h, j), he, hpj, hne, oe, opj))
      +hl1 = L.subst(U32, z => {U32.is_eq(B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), M.pos(1n+bp, h, j))), z) == False{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e)), l, le, hl0)
      +hr = L.subst(U32, z => {U32.is_eq(z, l) == False{} : Bool}, B.lnk(B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), M.pos(1n+bp, h, j))), TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), lnk_raw(AR.slots(U32, tabT), kl, 1n+bp, M.pos(1n+bp, h, j), hpj, opj), hl1)
      +E2 = Equal.cong(Bool, Array<U32>, z => LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), z), CY.msk(k), l, iu), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l), False{}, hr)
      +hiu1 = L.subst(Nat, z => {Nat.is_lt(z, 1n+bp) == True{} : Bool}, M.pos(1n+bp, h, j), UD.v(iu), Equal.sym(Nat, UD.v(iu), M.pos(1n+bp, h, j), hiu), hpj)
      +hn = Equal.trans(Nat, UD.v(H.bnext(iu, CY.msk(k))), Nat.mod(1n+UD.v(iu), 1n+bp), M.pos(1n+bp, h, 1n+j), next_ok(one, h1, k, hk31, bp, hN, iu, hiu1), Equal.trans(Nat, Nat.mod(1n+UD.v(iu), 1n+bp), Nat.mod(1n+M.pos(1n+bp, h, j), 1n+bp), M.pos(1n+bp, h, 1n+j), Equal.cong(Nat, Nat, z => Nat.mod(1n+z, 1n+bp), UD.v(iu), M.pos(1n+bp, h, j), hiu), M.pos_next(bp, h, j)))
      +hf2 = L.subst(Nat, z => {Nat.is_lt(M.dist(1n+bp, h, e), z) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hf)
      Equal.trans(Array<U32>, LR.dfind(1n+p, LR.dstep(AR.thaw(U32, tabT), iu, l), CY.msk(k), l, iu), LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), CY.msk(k), l, iu), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), Equal.cong(LR.DStep, Array<U32>, s => LR.dfind(1n+p, s, CY.msk(k), l, iu), LR.dstep(AR.thaw(U32, tabT), iu, l), LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), E), Equal.trans(Array<U32>, LR.dfind(1n+p, LR.ds_if(AR.thaw(U32, tabT), U32.is_eq(TB.nth0(AR.slots(U32, tabT), 1n+Nat.double(M.pos(1n+bp, h, j))), l)), CY.msk(k), l, iu), LR.dfind(p, LR.dstep(AR.thaw(U32, tabT), H.bnext(iu, CY.msk(k)), l), CY.msk(k), l, H.bnext(iu, CY.msk(k))), H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)), E2, rec(H.bnext(iu, CY.msk(k)), hn, N.lt_succ_le_succ(j, M.dist(1n+bp, h, e), hjl), hf2)))

def dl_go(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +bp: Nat, +hN: {1n+bp == SC.pow2(k) : Nat}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +kl: List<&2, String>, +huq: {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, tabT), kl, 1n+bp)}, 1n+bp) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, 1n+bp) == True{} : Bool}, +w: U32, +l: U32, +kk: String, +hbe: {B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e) == B.BF{w, l, kk} : B.Bk}, +h: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hop: {B.occpath(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, h, M.dist(1n+bp, h, e)) == True{} : Bool}, +f: Nat, +j: Nat, +iu: U32, +hiu: {UD.v(iu) == M.pos(1n+bp, h, j) : Nat}, +hjd: {Nat.is_le(j, M.dist(1n+bp, h, e)) == True{} : Bool}, +hf: {Nat.is_lt(M.dist(1n+bp, h, e), Nat.add(j, f)) == True{} : Bool}) -> {LR.dfind(f, LR.dstep(AR.thaw(U32, tabT), iu, l), CY.msk(k), l, iu) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}:
  match f:
    case 0n:
      +hf0 = L.subst(Nat, z => {Nat.is_lt(M.dist(1n+bp, h, e), z) == True{} : Bool}, Nat.add(j, 0n), j, N.add_zero(j), hf)
      Empty.absurd({LR.dfind(0n, LR.dstep(AR.thaw(U32, tabT), iu, l), CY.msk(k), l, iu) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}, L.true_false(Equal.trans(Bool, True{}, Nat.is_lt(M.dist(1n+bp, h, e), j), False{}, Equal.sym(Bool, Nat.is_lt(M.dist(1n+bp, h, e), j), True{}, hf0), N.le_not_lt(M.dist(1n+bp, h, e), j, hjd))))
    case 1n+p:
      dl_c(one, h1, k, hk31, bp, hN, tabT, pt, kl, huq, e, he, w, l, kk, hbe, h, hh, hop, p, j, iu, hiu, hjd, hf, Nat.is_eq(j, M.dist(1n+bp, h, e)), {==}, iu2 => hiu2 => hjd2 => hf2 => dl_go(one, h1, k, hk31, bp, hN, tabT, pt, kl, huq, e, he, w, l, kk, hbe, h, hh, hop, p, 1n+j, iu2, hiu2, hjd2, hf2))


# THEOREM (del_link): with bucket e holding word w and link l in a clustered
# table of unique links, del_link deletes bucket e
def del_link_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +kl: List<&2, String>, +cl: {B.cluster(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), SC.pow2(k), CY.msk(k)) == True{} : Bool}, +huq: {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k))}, SC.pow2(k)) == True{} : Bool}, +e: Nat, +he: {Nat.is_lt(e, SC.pow2(k)) == True{} : Bool}, +w: U32, +l: U32, +kk: String, +hbe: {B.at(TB.buckets(AR.slots(U32, tabT), kl, SC.pow2(k)), e) == B.BF{w, l, kk} : B.Bk}) -> {LR.del_link(AR.thaw(U32, tabT), CY.msk(k), w, l) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}:
  +bp = UD.v(CY.msk(k))
  +hN = DW.hN(k, hk31)
  +cl2 = L.subst(Nat, z => {B.cluster(TB.buckets(AR.slots(U32, tabT), kl, z), z, CY.msk(k)) == True{} : Bool}, SC.pow2(k), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(k), hN), cl)
  +hu2 = L.subst(Nat, z => {B.all_lt(B.PUniq{TB.buckets(AR.slots(U32, tabT), kl, z)}, z) == True{} : Bool}, SC.pow2(k), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(k), hN), huq)
  +he2 = L.subst(Nat, z => {Nat.is_lt(e, z) == True{} : Bool}, SC.pow2(k), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(k), hN), he)
  +hb2 = L.subst(Nat, z => {B.at(TB.buckets(AR.slots(U32, tabT), kl, z), e) == B.BF{w, l, kk} : B.Bk}, SC.pow2(k), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(k), hN), hbe)
  +hh = L.subst(Nat, z => {Nat.is_lt(UD.v(HS.bucket(w, CY.msk(k))), z) == True{} : Bool}, SC.pow2(k), 1n+bp, Equal.sym(Nat, 1n+bp, SC.pow2(k), hN), PA.home_lt(w, k))
  +hc0 = B.all_inst(B.PClus{TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, CY.msk(k)}, 1n+bp, cl2, e, he2)
  +hop = L.subst(B.Bk, z => {B.implies(B.occ(z), B.occpath(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), 1n+bp, B.hb(CY.msk(k), z), M.dist(1n+bp, B.hb(CY.msk(k), z), e))) == True{} : Bool}, B.at(TB.buckets(AR.slots(U32, tabT), kl, 1n+bp), e), B.BF{w, l, kk}, hb2, hc0)
  +hiu = Equal.sym(Nat, M.pos(1n+bp, UD.v(HS.bucket(w, CY.msk(k))), 0n), UD.v(HS.bucket(w, CY.msk(k))), IV.pos0(bp, UD.v(HS.bucket(w, CY.msk(k))), hh))
  +hf = M.dist_lt(bp, UD.v(HS.bucket(w, CY.msk(k))), e)
  +g = dl_go(one, h1, k, hk31, bp, hN, tabT, pt, kl, hu2, e, he2, w, l, kk, hb2, UD.v(HS.bucket(w, CY.msk(k))), hh, hop, 1n+bp, 0n, HS.bucket(w, CY.msk(k)), hiu, N.zero_le(M.dist(1n+bp, UD.v(HS.bucket(w, CY.msk(k))), e)), hf)
  +ef = Equal.trans(Nat, U32.to_nat(U32.inc(CY.msk(k))), SC.pow2(k), 1n+bp, PA.fuel_eq(one, h1, k, hk31), Equal.sym(Nat, 1n+bp, SC.pow2(k), hN))
  L.subst(Nat, f => {LR.dfind(f, LR.dstep(AR.thaw(U32, tabT), HS.bucket(w, CY.msk(k)), l), CY.msk(k), l, HS.bucket(w, CY.msk(k))) == H.del_at(AR.thaw(U32, tabT), CY.msk(k), U32.from_nat(e)) : Array<U32>}, 1n+bp, U32.to_nat(U32.inc(CY.msk(k))), Equal.sym(Nat, U32.to_nat(U32.inc(CY.msk(k))), 1n+bp, ef), g)
