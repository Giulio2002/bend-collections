import Base
import ../../lib/logic.bend as L
import ../../lib/u32alg.bend as A
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../lib/u32div.bend as UD
import ../../../src/containers/hash_table.bend as H
import ./words.bend as WR
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./arr.bend as AX
import ./decide.bend as DC
import ./probe_impl.bend as PI
import ./cyc.bend as CY
import ../../lib/nat.bend as N
import ../../lib/word.bend as WD
import ../../lib/u32.bend as UW
import ../../lib/words32.bend as W32

# One-character keys below 2^31: the probe decides on bucket words alone.

def qd_w(+l: U32, same: Bool) -> B.MS:
  match same:
    case True{}:
      B.MHit{l}
    case False{}:
      B.MNext{}

def qd_e(+w: U32, +x: U32, +l: U32, empty: Bool) -> B.MS:
  match empty:
    case True{}:
      B.MEnd{}
    case False{}:
      qd_w(l, U32.is_eq(x, w))

def qdec(+w: U32, +x: U32, +l: U32) -> B.MS:
  qd_e(w, x, l, U32.is_eq(x, 0))

def qstep_of(ms: B.MS, tab: Array<U32>) -> H.QStep:
  match ms:
    case B.MEnd{}:
      H.QEnd{tab}
    case B.MHit{l}:
      H.QHit{tab, l}
    case B.MNext{}:
      H.QNext{tab}

def qs_same(+td: Nat, +tabT: AR.Tree<U32>, +i: U32, +hd: {Nat.is_lt(td, 32n) == True{} : Bool}, +pt: {AR.perfect(U32, td, tabT) == True{} : Bool}, +hl: {Nat.is_lt(UD.v(U32.inc(U32.shl(i))), SC.pow2(td)) == True{} : Bool}, +same: Bool) -> {H.qs_same(AR.thaw(U32, tabT), i, same) == qstep_of(qd_w(W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), same), AR.thaw(U32, tabT)) : H.QStep}:
  match same:
    case True{}:
      Equal.cong(Array<U32> & U32, H.QStep, r => H.qs_l(r), Array.get(U32, AR.thaw(U32, tabT), U32.inc(U32.shl(i))), (AR.thaw(U32, tabT), W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))), AX.getw(td, tabT, U32.inc(U32.shl(i)), hd, hl, pt))
    case False{}:
      {==}

def qs_if(+td: Nat, +tabT: AR.Tree<U32>, +i: U32, +w: U32, +hd: {Nat.is_lt(td, 32n) == True{} : Bool}, +pt: {AR.perfect(U32, td, tabT) == True{} : Bool}, +hl: {Nat.is_lt(UD.v(U32.inc(U32.shl(i))), SC.pow2(td)) == True{} : Bool}, +x: U32, +e: Bool) -> {H.qs_if(AR.thaw(U32, tabT), i, w, x, e) == qstep_of(qd_e(w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i)))), e), AR.thaw(U32, tabT)) : H.QStep}:
  match e:
    case True{}:
      {==}
    case False{}:
      qs_same(td, tabT, i, hd, pt, hl, U32.is_eq(x, w))

# THEOREM: a short-key probe step reads bucket i and decides as qdec.
def qstep(+td: Nat, +tabT: AR.Tree<U32>, +i: U32, +w: U32, +hd: {Nat.is_lt(td, 32n) == True{} : Bool}, +pt: {AR.perfect(U32, td, tabT) == True{} : Bool}, +hw: {Nat.is_lt(UD.v(U32.shl(i)), SC.pow2(td)) == True{} : Bool}, +hl: {Nat.is_lt(UD.v(U32.inc(U32.shl(i))), SC.pow2(td)) == True{} : Bool}) -> {H.qstep(AR.thaw(U32, tabT), i, w) == qstep_of(qdec(w, W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i))), W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))), AR.thaw(U32, tabT)) : H.QStep}:
  +x = W32.nth0(AR.slots(U32, tabT), UD.v(U32.shl(i)))
  Equal.trans(H.QStep, H.qs_w(i, w, Array.get(U32, AR.thaw(U32, tabT), U32.shl(i))), H.qs_w(i, w, (AR.thaw(U32, tabT), x)), qstep_of(qdec(w, x, W32.nth0(AR.slots(U32, tabT), UD.v(U32.inc(U32.shl(i))))), AR.thaw(U32, tabT)),
    Equal.cong(Array<U32> & U32, H.QStep, r => H.qs_w(i, w, r), Array.get(U32, AR.thaw(U32, tabT), U32.shl(i)), (AR.thaw(U32, tabT), x), AX.getw(td, tabT, U32.shl(i), hd, hw, pt)),
    qs_if(td, tabT, i, w, hd, pt, hl, x, U32.is_eq(x, 0)))



# ---- the short-key decision ----

def eqc_false(+x: U32, +c: U32, +hx: {H.is_short(x) == True{} : Bool}, +hs: {U32.is_eq(x, H.short_word(c)) == False{} : Bool}, +e: Bool, +he: {U32.is_eq(U32.and(x, 2147483647), c) == e : Bool}) -> {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +xc = Equal.trans(U32, x, H.short_word(U32.and(x, 2147483647)), H.short_word(c), Equal.sym(U32, H.short_word(U32.and(x, 2147483647)), x, WR.short_eta(x, hx)), Equal.cong(U32, U32, z => H.short_word(z), U32.and(x, 2147483647), c, A.eq_of(U32.and(x, 2147483647), c, he)))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_eq(x, H.short_word(c)), False{}, L.subst(U32, z => {True{} == U32.is_eq(x, z) : Bool}, x, H.short_word(c), xc, Equal.sym(Bool, U32.is_eq(x, x), True{}, UW.u32_eq_refl(x))), hs)))

def qd_short(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +x: U32, +l: U32, +hx: {H.is_short(x) == True{} : Bool}, +s: Bool, +hs: {U32.is_eq(x, H.short_word(c)) == s : Bool}) -> {qd_w(l, s) == Bool.pick(B.MS, S.str_eq(SCon{Chr{U32.and(x, 2147483647)}, SNil{}}, SCon{Chr{c}, SNil{}}), B.MHit{l}, B.MNext{}) : B.MS}:
  match s:
    case True{}:
      +ac = Equal.trans(U32, U32.and(x, 2147483647), U32.and(H.short_word(c), 2147483647), c, Equal.cong(U32, U32, z => U32.and(z, 2147483647), x, H.short_word(c), A.eq_of(x, H.short_word(c), hs)), WR.short_back(c, hc))
      +t = L.subst(U32, z => {U32.is_eq(z, c) == True{} : Bool}, c, U32.and(x, 2147483647), Equal.sym(U32, U32.and(x, 2147483647), c, ac), UW.u32_eq_refl(c))
      Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), True{}, Bool.and(U32.is_eq(U32.and(x, 2147483647), c), True{}), Equal.sym(Bool, Bool.and(U32.is_eq(U32.and(x, 2147483647), c), True{}), True{}, L.subst(Bool, b => {Bool.and(b, True{}) == True{} : Bool}, True{}, U32.is_eq(U32.and(x, 2147483647), c), Equal.sym(Bool, U32.is_eq(U32.and(x, 2147483647), c), True{}, t), {==})))
    case False{}:
      +f = eqc_false(x, c, hx, hs, U32.is_eq(U32.and(x, 2147483647), c), {==})
      Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), False{}, Bool.and(U32.is_eq(U32.and(x, 2147483647), c), True{}), Equal.sym(Bool, Bool.and(U32.is_eq(U32.and(x, 2147483647), c), True{}), False{}, L.subst(Bool, b => {Bool.and(b, True{}) == False{} : Bool}, False{}, U32.is_eq(U32.and(x, 2147483647), c), Equal.sym(Bool, U32.is_eq(U32.and(x, 2147483647), c), False{}, f), {==})))

# a long bucket never holds a one-character key below 2^31
def ql_false(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +x: U32, +k: String, +hx: {H.is_short(x) == False{} : Bool}, +hinv: {x == K.kword(k) : U32}, +e: Bool, +he: {S.str_eq(k, SCon{Chr{c}, SNil{}}) == e : Bool}) -> {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +xs = Equal.trans(U32, x, K.kword(k), H.short_word(c), hinv, Equal.trans(U32, K.kword(k), K.kword(SCon{Chr{c}, SNil{}}), H.short_word(c), Equal.cong(String, U32, z => K.kword(z), k, SCon{Chr{c}, SNil{}}, K.str_eq_of(k, SCon{Chr{c}, SNil{}}, he)), K.kword_short(c, hc)))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, H.is_short(x), False{}, Equal.trans(Bool, True{}, H.is_short(H.short_word(c)), H.is_short(x), Equal.sym(Bool, H.is_short(H.short_word(c)), True{}, WR.short_is_short(c)), Equal.cong(U32, Bool, z => H.is_short(z), H.short_word(c), x, Equal.sym(U32, x, H.short_word(c), xs))), hx)))

def qsh(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +x: U32, +l: U32, +k: String, +hinv: {B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(k))) == True{} : Bool}, +sh: Bool, +hsh: {H.is_short(x) == sh : Bool}) -> {qd_w(l, U32.is_eq(x, H.short_word(c))) == B.mstep(SCon{Chr{c}, SNil{}}, B.BF{x, l, TB.keyof_c(x, k, sh)}) : B.MS}:
  match sh:
    case True{}:
      qd_short(c, hc, x, l, hsh, U32.is_eq(x, H.short_word(c)), {==})
    case False{}:
      +e = B.imp_elim(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(k)), hinv, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, H.is_short(x), Equal.sym(Bool, H.is_short(x), False{}, hsh), {==}))
      +ne = DC.kinds_ne(H.short_word(c), x, WR.short_is_short(c), hsh, U32.is_eq(H.short_word(c), x), {==})
      +ne2 = Equal.trans(Bool, U32.is_eq(x, H.short_word(c)), U32.is_eq(H.short_word(c), x), False{}, W32.eq_sym_u32(x, H.short_word(c)), ne)
      Equal.trans(B.MS, qd_w(l, U32.is_eq(x, H.short_word(c))), B.MNext{}, Bool.pick(B.MS, S.str_eq(k, SCon{Chr{c}, SNil{}}), B.MHit{l}, B.MNext{}),
        Equal.cong(Bool, B.MS, b => qd_w(l, b), U32.is_eq(x, H.short_word(c)), False{}, ne2),
        Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), False{}, S.str_eq(k, SCon{Chr{c}, SNil{}}), Equal.sym(Bool, S.str_eq(k, SCon{Chr{c}, SNil{}}), False{}, ql_false(c, hc, x, k, hsh, A.eq_of(x, K.kword(k), e), S.str_eq(k, SCon{Chr{c}, SNil{}}), {==}))))

def qde(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +x: U32, +l: U32, +kl: List<&2, String>, +hinv: {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l))))))) == True{} : Bool}, +e: Bool, +he: {U32.is_eq(x, 0) == e : Bool}) -> {qd_e(H.short_word(c), x, l, e) == B.mstep(SCon{Chr{c}, SNil{}}, TB.dec_c(x, l, kl, e)) : B.MS}:
  match e:
    case True{}:
      {==}
    case False{}:
      +h2 = B.imp_elim(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l)))))), hinv, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), {==}))
      qsh(c, hc, x, l, TB.nths(kl, UD.v(H.slot(l))), h2, H.is_short(x), {==})

# THEOREM: a short-key step decides as the model's step on the decoded bucket.
def qdecide(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +x: U32, +l: U32, +kl: List<&2, String>, +hinv: {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl, UD.v(H.slot(l))))))) == True{} : Bool}) -> {qdec(H.short_word(c), x, l) == B.mstep(SCon{Chr{c}, SNil{}}, TB.dec_c(x, l, kl, U32.is_eq(x, 0))) : B.MS}:
  qde(c, hc, x, l, kl, hinv, U32.is_eq(x, 0), {==})

# ---- the loop ----

def qf_of(r: B.Res, tab: Array<U32>) -> H.QFound:
  match r:
    case B.RHit{+a, +l}:
      H.QF{tab, U32.from_nat(a), l}
    case B.REnd{+a}:
      H.QF{tab, U32.from_nat(a), 0}

def qm0(+tabT: AR.Tree<U32>, +key: String, +bs: List<&2, B.Bk>, +n: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +ms: B.MS) -> {H.qfind(0n, qstep_of(ms, AR.thaw(U32, tabT)), mask, w, i) == qf_of(B.pf(key, bs, n, 0n, ms, UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}:
  match ms:
    case B.MEnd{}:
      Equal.cong(U32, H.QFound, z => H.QF{AR.thaw(U32, tabT), z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MHit{+l}:
      Equal.cong(U32, H.QFound, z => H.QF{AR.thaw(U32, tabT), z, l}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MNext{}:
      Equal.cong(U32, H.QFound, z => H.QF{AR.thaw(U32, tabT), z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))

def qm1(+tabT: AR.Tree<U32>, +key: String, +bs: List<&2, B.Bk>, +n: Nat, +mask: U32, +w: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(k, 32n) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}, +p: Nat, +hnext: {UD.v(H.bnext(i, mask)) == Nat.mod(1n+UD.v(i), n) : Nat}, +rec: {H.qfind(p, H.qstep(AR.thaw(U32, tabT), H.bnext(i, mask), w), mask, w, H.bnext(i, mask)) == qf_of(B.pf(key, bs, n, p, B.mstep(key, B.at(bs, UD.v(H.bnext(i, mask)))), UD.v(H.bnext(i, mask))), AR.thaw(U32, tabT)) : H.QFound}, +ms: B.MS) -> {H.qfind(1n+p, qstep_of(ms, AR.thaw(U32, tabT)), mask, w, i) == qf_of(B.pf(key, bs, n, 1n+p, ms, UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}:
  match ms:
    case B.MEnd{}:
      Equal.cong(U32, H.QFound, z => H.QF{AR.thaw(U32, tabT), z, 0}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MHit{+l}:
      Equal.cong(U32, H.QFound, z => H.QF{AR.thaw(U32, tabT), z, l}, i, U32.from_nat(UD.v(i)), Equal.sym(U32, U32.from_nat(UD.v(i)), i, PI.from_v(i, k, hk, hi)))
    case B.MNext{}:
      L.subst(Nat, z => {H.qfind(p, H.qstep(AR.thaw(U32, tabT), H.bnext(i, mask), w), mask, w, H.bnext(i, mask)) == qf_of(B.pf(key, bs, n, p, B.mstep(key, B.at(bs, z)), z), AR.thaw(U32, tabT)) : H.QFound}, UD.v(H.bnext(i, mask)), Nat.mod(1n+UD.v(i), n), hnext, rec)

# THEOREM: the implementation's short-key probe loop is the model loop B.pf
# on the decoded buckets for the key SCon{Chr{c}, ""}.
def qfind_ok(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +hk31: {Nat.is_lt(k, 31n) == True{} : Bool}, +tabT: AR.Tree<U32>, +pt: {AR.perfect(U32, 1n+k, tabT) == True{} : Bool}, +sd: Nat, +kl0: List<&2, String>, +c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +hwell: {B.all_lt(B.PWell{TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), sd}, SC.pow2(k)) == True{} : Bool}, +f: Nat, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(k)) == True{} : Bool}) -> {H.qfind(f, H.qstep(AR.thaw(U32, tabT), i, H.short_word(c)), CY.msk(k), H.short_word(c), i) == qf_of(B.pf(SCon{Chr{c}, SNil{}}, TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), SC.pow2(k), f, B.mstep(SCon{Chr{c}, SNil{}}, B.at(TB.buckets(AR.slots(U32, tabT), kl0, SC.pow2(k)), UD.v(i))), UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}:
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
      +x = W32.nth0(tb, UD.v(U32.shl(i)))
      +l = W32.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = PI.dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, PI.wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = qdec(w, x, l)
      +em = Equal.trans(B.MS, ms, B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), qdecide(c, hc, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd)))
      +es = qstep(1n+k, tabT, i, w, hk31, pt, hwb0, hlb0)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +p3 = qm0(tabT, key, bs, n, CY.msk(k), w, i, k, hk32, hi, ms)
      +p2 = L.subst(B.MS, m => {H.qfind(0n, qstep_of(ms, AR.thaw(U32, tabT)), CY.msk(k), w, i) == qf_of(B.pf(key, bs, n, 0n, m, UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}, ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.QStep, s => {H.qfind(0n, s, CY.msk(k), w, i) == qf_of(B.pf(key, bs, n, 0n, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}, qstep_of(ms, AR.thaw(U32, tabT)), H.qstep(AR.thaw(U32, tabT), i, w), Equal.sym(H.QStep, H.qstep(AR.thaw(U32, tabT), i, w), qstep_of(ms, AR.thaw(U32, tabT)), es), p2)
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
      +x = W32.nth0(tb, UD.v(U32.shl(i)))
      +l = W32.nth0(tb, UD.v(U32.inc(U32.shl(i))))
      +dx = PI.dec_ix(tb, kl0, UD.v(i), UD.v(U32.shl(i)), UD.v(U32.inc(U32.shl(i))), ew, el)
      +dat = TB.at_buckets(tb, kl0, n, UD.v(i), hi)
      +dd = Equal.trans(B.Bk, B.at(bs, UD.v(i)), TB.dec(tb, kl0, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dat, Equal.sym(B.Bk, TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), TB.dec(tb, kl0, UD.v(i)), dx))
      +hwb = L.subst(B.Bk, b => {B.wb(sd, b) == True{} : Bool}, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd, B.all_inst(B.PWell{bs, sd}, n, hwell, UD.v(i), hi))
      +hvI = Pair.snd({B.implies(Bool.not(U32.is_eq(x, 0)), Nat.is_lt(UD.v(H.slot(l)), SC.pow2(sd))) == True{} : Bool}, {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(kl0, UD.v(H.slot(l))))))) == True{} : Bool}, PI.wb_facts(sd, x, l, kl0, U32.is_eq(x, 0), {==}, hwb))
      +ms = qdec(w, x, l)
      +em = Equal.trans(B.MS, ms, B.mstep(key, TB.dec_c(x, l, kl0, U32.is_eq(x, 0))), B.mstep(key, B.at(bs, UD.v(i))), qdecide(c, hc, x, l, kl0, hvI), Equal.cong(B.Bk, B.MS, b => B.mstep(key, b), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), B.at(bs, UD.v(i)), Equal.sym(B.Bk, B.at(bs, UD.v(i)), TB.dec_c(x, l, kl0, U32.is_eq(x, 0)), dd)))
      +es = qstep(1n+k, tabT, i, w, hk31, pt, hwb0, hlb0)
      +hk32 = N.lt_le(k, 32n, N.lt_trans(k, 31n, 32n, hk31, {==}))
      +hks = L.subst(Nat, z => {Nat.is_lt(z, WD.sc(32n, one)) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), W32.pow_one(one, h1, k), N.lt_le_trans(SC.pow2(k), SC.pow2(1n+k), WD.sc(32n, one), N.pow2_lt_succ(k), W32.pow_le32(one, h1, 1n+k, hk31)))
      +hi1 = L.subst(Nat, z => {Nat.is_lt(UD.v(i), z) == True{} : Bool}, SC.pow2(k), WD.sc(k, one), W32.pow_one(one, h1, k), hi)
      +hnext = Equal.trans(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), WD.sc(k, one)), Nat.mod(1n+UD.v(i), n), CY.next_val(one, h1, k, i, hks, hi1), Equal.cong(Nat, Nat, z => Nat.mod(1n+UD.v(i), z), WD.sc(k, one), SC.pow2(k), Equal.sym(Nat, SC.pow2(k), WD.sc(k, one), W32.pow_one(one, h1, k))))
      +hi2 = L.subst(Nat, z => {Nat.is_lt(z, n) == True{} : Bool}, Nat.mod(1n+UD.v(i), n), UD.v(H.bnext(i, CY.msk(k))), Equal.sym(Nat, UD.v(H.bnext(i, CY.msk(k))), Nat.mod(1n+UD.v(i), n), hnext), PI.mod_lt(n, N.succ_le_lt(0n, n, N.pow2_pos(k)), 1n+UD.v(i)))
      +p3 = qm1(tabT, key, bs, n, CY.msk(k), w, i, k, hk32, hi, p, hnext, qfind_ok(one, h1, k, hk31, tabT, pt, sd, kl0, c, hc, hwell, p, H.bnext(i, CY.msk(k)), hi2), ms)
      +p2 = L.subst(B.MS, m => {H.qfind(1n+p, qstep_of(ms, AR.thaw(U32, tabT)), CY.msk(k), w, i) == qf_of(B.pf(key, bs, n, 1n+p, m, UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}, ms, B.mstep(key, B.at(bs, UD.v(i))), em, p3)
      L.subst(H.QStep, s => {H.qfind(1n+p, s, CY.msk(k), w, i) == qf_of(B.pf(key, bs, n, 1n+p, B.mstep(key, B.at(bs, UD.v(i))), UD.v(i)), AR.thaw(U32, tabT)) : H.QFound}, qstep_of(ms, AR.thaw(U32, tabT)), H.qstep(AR.thaw(U32, tabT), i, w), Equal.sym(H.QStep, H.qstep(AR.thaw(U32, tabT), i, w), qstep_of(ms, AR.thaw(U32, tabT)), es), p2)
