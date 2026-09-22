import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32.bend as U
import ../lib/array.bend as AR
import ../spec/common.bend as SC
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./strings.bend as STR
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./step.bend as SP
import ./decide.bend as DC
import ./arr.bend as AX
import ./cyc.bend as CY
import ./modn.bend as MN
import ../math/word.bend as WD

# The implementation's long-key probe loop (find over step) refines the
# model loop B.pf on the decoded buckets; the stored keys are unchanged.

def or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def wb_sh(+x: U32, +l: U32, +kl: List<&2, String>, +sh: Bool, +hsh: {H.is_short(x) == sh : Bool}, +h: {B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.keyof_c(x, TB.nths(kl, UD.v(H.slot(l))), sh)))) == True{} : Bool}) -> {B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l)))))) == True{} : Bool}:
  match sh:
    case True{}:
      L.subst(Bool, b => {B.implies(Bool.not(b), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l)))))) == True{} : Bool}, True{}, H.is_short(x), Equal.sym(Bool, H.is_short(x), True{}, hsh), {==})
    case False{}:
      h

def wb_facts(+sd: Nat, +x: U32, +l: U32, +kl: List<&2, String>, +e: Bool, +he: {U32.is_eq(x, 0) == e : Bool}, +hw: {B.wb(sd, TB.dec_c(x, l, kl, e)) == True{} : Bool}) -> {B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool} & {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l))))))) == True{} : Bool}:
  match e:
    case True{}:
      (L.subst(Bool, b => {B.implies(Bool.not(b), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, True{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), True{}, he), {==}),
       L.subst(Bool, b => {B.implies(Bool.not(b), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l))))))) == True{} : Bool}, True{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), True{}, he), {==}))
    case False{}:
      +s = TB.nths(kl, UD.v(H.slot(l)))
      +ha = L.and_left(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.keyof(x, s)))), hw)
      +hb = L.and_right(Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.keyof(x, s)))), hw)
      (L.subst(Bool, b => {B.implies(Bool.not(b), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), ha),
       L.subst(Bool, b => {B.implies(Bool.not(b), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(s)))) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), wb_sh(x, l, kl, H.is_short(x), {==}, hb)))

# ---- the stored keys after a step ----

def ka_w_ok(+sd: Nat, +K: AR.Tree<String>, +l: U32, +hs: {Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)) == True{} : Bool}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +same: Bool) -> {AR.slots(String, SP.ka_w(sd, K, l, same)) == AR.slots(String, K) : List<&2, String>} & {AR.perfect(String, sd, SP.ka_w(sd, K, l, same)) == True{} : Bool}:
  match same:
    case False{}:
      ({==}, pk)
    case True{}:
      (SP.kcmp_slots(sd, K, l, hs, pk), SP.kcmp_perfect(sd, K, l, pk))

def ka_e_ok(+sd: Nat, +K: AR.Tree<String>, +w: U32, +x: U32, +l: U32, +hs: {B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}, +e: Bool, +he: {U32.is_eq(x, 0) == e : Bool}) -> {AR.slots(String, SP.ka_e(sd, K, w, x, l, e)) == AR.slots(String, K) : List<&2, String>} & {AR.perfect(String, sd, SP.ka_e(sd, K, w, x, l, e)) == True{} : Bool}:
  match e:
    case True{}:
      ({==}, pk)
    case False{}:
      ka_w_ok(sd, K, l, B.imp_elim(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd)), hs, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), {==})), pk, U32.is_eq(x, w))

def kafter_ok(+sd: Nat, +K: AR.Tree<String>, +w: U32, +x: U32, +l: U32, +hs: {B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}) -> {AR.slots(String, SP.kafter(sd, K, w, x, l)) == AR.slots(String, K) : List<&2, String>} & {AR.perfect(String, sd, SP.kafter(sd, K, w, x, l)) == True{} : Bool}:
  ka_e_ok(sd, K, w, x, l, hs, pk, U32.is_eq(x, 0), {==})

# ---- the result of the loop ----

def fd_of(r: B.Res, tab: Array<U32>, ks: Array<String>, key: String) -> H.Found:
  match r:
    case B.RHit{+a, +l}:
      H.FD{tab, ks, key, U32.from_nat(a), l}
    case B.REnd{+a}:
      H.FD{tab, ks, key, U32.from_nat(a), 0}

def FindOK(+tabT: AR.Tree<U32>, +sd: Nat, +kl0: List<&2, String>, +key: String, r: B.Res, fd: H.Found) -> Type:
  Sigma<&1, &1, AR.Tree<String>, K2 => {fd == fd_of(r, AR.thaw(U32, tabT), AR.thaw(String, K2), key) : H.Found} & ({AR.slots(String, K2) == kl0 : List<&2, String>} & {AR.perfect(String, sd, K2) == True{} : Bool})>

# a U32 is the U32 of its value
def from_v(+i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}) -> {U32.from_nat(UD.v(i)) == i : U32}:
  U.injective(U32.from_nat(UD.v(i)), i, U.to_nat_from_nat(UD.v(i), k, hk, hi))

# bucket i read through the word/link indices 2i, 2i + 1
def dec_ix(+tb: List<&2, U32>, +kl: List<&2, String>, +i: Nat, +a: Nat, +b: Nat, +ea: {a == Nat.double(i) : Nat}, +eb: {b == 1n+Nat.double(i) : Nat}) -> {TB.dec_c(TB.nth0(tb, a), TB.nth0(tb, b), kl, U32.is_eq(TB.nth0(tb, a), 0)) == TB.dec(tb, kl, i) : B.Bk}:
  +e1 = L.subst(Nat, z => {TB.dec_c(TB.nth0(tb, z), TB.nth0(tb, b), kl, U32.is_eq(TB.nth0(tb, z), 0)) == TB.dec_c(TB.nth0(tb, Nat.double(i)), TB.nth0(tb, b), kl, U32.is_eq(TB.nth0(tb, Nat.double(i)), 0)) : B.Bk}, Nat.double(i), a, Equal.sym(Nat, a, Nat.double(i), ea), {==})
  Equal.trans(B.Bk, TB.dec_c(TB.nth0(tb, a), TB.nth0(tb, b), kl, U32.is_eq(TB.nth0(tb, a), 0)), TB.dec_c(TB.nth0(tb, Nat.double(i)), TB.nth0(tb, b), kl, U32.is_eq(TB.nth0(tb, Nat.double(i)), 0)), TB.dec(tb, kl, i), e1,
    Equal.cong(Nat, B.Bk, z => TB.dec_c(TB.nth0(tb, Nat.double(i)), TB.nth0(tb, z), kl, U32.is_eq(TB.nth0(tb, Nat.double(i)), 0)), b, 1n+Nat.double(i), eb))

def fm0(+tabT: AR.Tree<U32>, +sd: Nat, +kl0: List<&2, String>, +key: String, +bs: List<&2, B.Bk>, +n: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +K1: AR.Tree<String>, +hs1: {AR.slots(String, K1) == kl0 : List<&2, String>}, +pk1: {AR.perfect(String, sd, K1) == True{} : Bool}, +ms: B.MS) -> FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 0n, ms, UD.v(i)), H.find(0n, SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), mask, w, i)):
  match ms:
    case B.MEnd{}:
      (K1, (Equal.cong(U32, H.Found, z => H.FD{AR.thaw(U32, tabT), AR.thaw(String, K1), key, z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, from_v(i, k, hk, hi))), (hs1, pk1)))
    case B.MHit{+l}:
      (K1, (Equal.cong(U32, H.Found, z => H.FD{AR.thaw(U32, tabT), AR.thaw(String, K1), key, z, l}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, from_v(i, k, hk, hi))), (hs1, pk1)))
    case B.MNext{}:
      (K1, (Equal.cong(U32, H.Found, z => H.FD{AR.thaw(U32, tabT), AR.thaw(String, K1), key, z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, from_v(i, k, hk, hi))), (hs1, pk1)))

def fm1(+tabT: AR.Tree<U32>, +sd: Nat, +kl0: List<&2, String>, +key: String, +bs: List<&2, B.Bk>, +n: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +K1: AR.Tree<String>, +hs1: {AR.slots(String, K1) == kl0 : List<&2, String>}, +pk1: {AR.perfect(String, sd, K1) == True{} : Bool}, +p: Nat, +hnext: {UD.v(H.bnext(i, mask)) == Nat.mod(1n+UD.v(i), n) : Nat}, rec: FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, p, B.mstep(key, B.at(bs, UD.v(H.bnext(i, mask)))), UD.v(H.bnext(i, mask))), H.find(p, H.step(AR.thaw(U32, tabT), AR.thaw(String, K1), H.bnext(i, mask), key, w), mask, w, H.bnext(i, mask))), +ms: B.MS) -> FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 1n+p, ms, UD.v(i)), H.find(1n+p, SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), mask, w, i)):
  match ms:
    case B.MEnd{}:
      (K1, (Equal.cong(U32, H.Found, z => H.FD{AR.thaw(U32, tabT), AR.thaw(String, K1), key, z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, from_v(i, k, hk, hi))), (hs1, pk1)))
    case B.MHit{+l}:
      (K1, (Equal.cong(U32, H.Found, z => H.FD{AR.thaw(U32, tabT), AR.thaw(String, K1), key, z, l}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, from_v(i, k, hk, hi))), (hs1, pk1)))
    case B.MNext{}:
      L.subst(Nat, z => FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, p, B.mstep(key, B.at(bs, z)), z), H.find(p, H.step(AR.thaw(U32, tabT), AR.thaw(String, K1), H.bnext(i, mask), key, w), mask, w, H.bnext(i, mask))), UD.v(H.bnext(i, mask)), Nat.mod(1n+UD.v(i), n), hnext, rec)

def mod_lt(+n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +x: Nat) -> {Nat.is_lt(Nat.mod(x, n), n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.mod(x, 0n), 0n) == True{} : Bool}, L.false_true(hn))
    case 1n+bp:
      MN.dm_lt(bp, x)

# THEOREM: the implementation's long-key probe loop is the model loop B.pf on
# the decoded buckets (a table of 2^k buckets, word/link pairs in tabT, the
# stored keys unchanged).
def find_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +hsd: {Nat.is_lt(sd, 32n) == True{} : Bool}, +kl0: List<&2, String>, +key: String, +hkey: {K.shortk(key) == False{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +f: Nat, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +K: AR.Tree<String>, +hsl: {AR.slots(String, K) == kl0 : List<&2, String>}, +pk: {AR.perfect(String, sd, K) == True{} : Bool}) -> FindOK(tabT, sd, kl0, key, B.pf(key, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), f, B.mstep(key, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(i))), UD.v(i)), H.find(f, H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, STR.lword(key)), CY.msk(k), STR.lword(key), i)):
  match f:
    case 0n:
      +tb = AR.slots(U32, tabT)
      +n = SC.pow2(k)
      +bs = TB.buckets(tb, kl0, n)
      +w = STR.lword(key)
      +hb = N.double_lt_bit(True{}, UD.v(i), SC.pow2(k), hi)
      +ew = AX.ix_w(i, 1n+k, hk31, hb)
      +el = AX.ix_l(i, 1n+k, hk31, hb)
      +hwb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(1n+k), N.lt_succ(Nat.double(UD.v(i))), hb))
      +hlb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(UD.v(i)), UD.v(U32.inc(U32.shl(i))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), el), hb)
      +x = TB.nth0(tb, UD.v(U32.shl(i)))
      +l = TB.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hsI = Pair.fst({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = SP.ldec(key, w, x, l, TB.nths(AR.slots(String, K), UD.v(H.slot(l))))
      +em = Equal.trans(B.MS, ms, SP.ldec(key, w, x, l, TB.nths(kl0, UD.v(H.slot(l)))), B.mstep(key, B.at(bs, UD.v(i))),
        Equal.cong(List<&2, String>, B.MS, z => SP.ldec(key, w, x, l, TB.nths(z, UD.v(H.slot(l)))), AR.slots(String, K), kl0, hsl),
        Equal.trans(B.MS, SP.ldec(key, w, x, l, TB.nths(kl0, UD.v(H.slot(l)))), B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), DC.decide(key, hkey, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd))))
      +K1 = SP.kafter(sd, K, w, x, l)
      +hs1 = Equal.trans(List<&2, String>, AR.slots(String, K1), AR.slots(String, K), kl0, Pair.fst({AR.slots(String, K1) == AR.slots(String, K) : List<&2, String>}, {AR.perfect(String, sd, K1) == True{} : Bool}, kafter_ok(sd, K, w, x, l, hsI, pk)), hsl)
      +pk1 = Pair.snd({AR.slots(String, K1) == AR.slots(String, K) : List<&2, String>}, {AR.perfect(String, sd, K1) == True{} : Bool}, kafter_ok(sd, K, w, x, l, hsI, pk))
      +es = SP.step_long(1n+k, tabT, sd, K, i, key, w, hk31, hsd, pt, pk, hwb0, hlb0, hsI)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      p3 = fm0(tabT, sd, kl0, key, bs, n, CY.msk(k), w, i, k, hk32, hi, K1, hs1, pk1, ms)
      p2 = L.subst(B.MS, m => FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 0n, m, UD.v(i)), H.find(0n, SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), CY.msk(k), w, i)), ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.Step, s => FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 0n, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), H.find(0n, s, CY.msk(k), w, i)), SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), Equal.sym(H.Step, H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), es), p2)
    case 1n+p:
      +tb = AR.slots(U32, tabT)
      +n = SC.pow2(k)
      +bs = TB.buckets(tb, kl0, n)
      +w = STR.lword(key)
      +hb = N.double_lt_bit(True{}, UD.v(i), SC.pow2(k), hi)
      +ew = AX.ix_w(i, 1n+k, hk31, hb)
      +el = AX.ix_l(i, 1n+k, hk31, hb)
      +hwb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, Nat.double(UD.v(i)), UD.v(U32.shl(i)), Equal.sym(Nat, UD.v(U32.shl(i)), Nat.double(UD.v(i)), ew), N.lt_trans(Nat.double(UD.v(i)), 1n+Nat.double(UD.v(i)), SC.pow2(1n+k), N.lt_succ(Nat.double(UD.v(i))), hb))
      +hlb0 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(1n+k)) == True{} : Bool}, 1n+Nat.double(UD.v(i)), UD.v(U32.inc(U32.shl(i))), Equal.sym(Nat, UD.v(U32.inc(U32.shl(i))), 1n+Nat.double(UD.v(i)), el), hb)
      +x = TB.nth0(tb, UD.v(U32.shl(i)))
      +l = TB.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hsI = Pair.fst({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = SP.ldec(key, w, x, l, TB.nths(AR.slots(String, K), UD.v(H.slot(l))))
      +em = Equal.trans(B.MS, ms, SP.ldec(key, w, x, l, TB.nths(kl0, UD.v(H.slot(l)))), B.mstep(key, B.at(bs, UD.v(i))),
        Equal.cong(List<&2, String>, B.MS, z => SP.ldec(key, w, x, l, TB.nths(z, UD.v(H.slot(l)))), AR.slots(String, K), kl0, hsl),
        Equal.trans(B.MS, SP.ldec(key, w, x, l, TB.nths(kl0, UD.v(H.slot(l)))), B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), DC.decide(key, hkey, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd))))
      +K1 = SP.kafter(sd, K, w, x, l)
      +hs1 = Equal.trans(List<&2, String>, AR.slots(String, K1), AR.slots(String, K), kl0, Pair.fst({AR.slots(String, K1) == AR.slots(String, K) : List<&2, String>}, {AR.perfect(String, sd, K1) == True{} : Bool}, kafter_ok(sd, K, w, x, l, hsI, pk)), hsl)
      +pk1 = Pair.snd({AR.slots(String, K1) == AR.slots(String, K) : List<&2, String>}, {AR.perfect(String, sd, K1) == True{} : Bool}, kafter_ok(sd, K, w, x, l, hsI, pk))
      +es = SP.step_long(1n+k, tabT, sd, K, i, key, w, hk31, hsd, pt, pk, hwb0, hlb0, hsI)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +hks = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), AX.pow_le32(one, h1, 1n+k, hk31)))
      +hi1 = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k), hi)
      +hnext = Equal.trans(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), WD.sc(k, one)), Nat.mod(1n+UD.v(i), n), CY.next_val(one, h1, k, i, hks, hi1), Equal.cong(Nat, Nat, z => Nat.mod(1n+UD.v(i), z), WD.sc(k, one), SC.pow2(k), Equal.sym(Nat, SC.pow2(k), WD.sc(k, one), AX.pow_one(one, h1, k))))
      +hi2 = L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, Nat.mod(1n+UD.v(i), n), UD.v(H.bnext(i, CY.msk(k))), Equal.sym(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), n), hnext), mod_lt(n, N.succ_le_lt(0n, n, N.pow2_pos(k)), 1n+UD.v(i)))
      p3 = fm1(tabT, sd, kl0, key, bs, n, CY.msk(k), w, i, k, hk32, hi, K1, hs1, pk1, p, hnext, find_ok(one, h1, k, hk31, tabT, pt, sd, hsd, kl0, key, hkey, hwell, p, H.bnext(i, CY.msk(k)), hi2, K1, hs1, pk1), ms)
      p2 = L.subst(B.MS, m => FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 1n+p, m, UD.v(i)), H.find(1n+p, SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), CY.msk(k), w, i)), ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.Step, s => FindOK(tabT, sd, kl0, key, B.pf(key, bs, n, 1n+p, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), H.find(1n+p, s, CY.msk(k), w, i)), SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), Equal.sym(H.Step, H.step(AR.thaw(U32, tabT), AR.thaw(String, K), i, key, w), SP.step_of(ms, AR.thaw(U32, tabT), AR.thaw(String, K1), key), es), p2)
