import ./promote.bend as OptPromote
import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import support/links_state.bend as DST
import support/links_links.bend as LK
import support/links_split.bend as SP
import support/links_retarget.bend as RT
import support/links_rmfacts.bend as RM
import support/links_facts.bend as DF
import support/links_tset.bend as TS
import support/links_tolist.bend as TL
import support/links_inslk.bend as IL
import ../../reference/lru/proofs/invariants.bend as Inv
import ./state.bend as ST
import ./table.bend as TB
import ./chain.bend as CHN
import ./lists.bend as LS
import ./rs.bend as RS

# touch(s): slot s (in the order at a ++ [s] ++ b) becomes the newest. When b
# is empty it already is and nothing changes; otherwise s is unlinked and
# linked at the tail. Either way the order becomes (a ++ b) ++ [s].

def ln_eq(+s: Nat, +q: Nat, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(depth)) == True{} : Bool}, +hq: {Nat.is_lt(q, SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(DST.ln(s), DST.ln(q)) == Nat.is_eq(s, q) : Bool}:
  Equal.trans(Bool, U32.is_eq(DST.ln(s), DST.ln(q)), Nat.is_eq(U32.to_nat(DST.ln(s)), U32.to_nat(DST.ln(q))), Nat.is_eq(1n+s, 1n+q),
    DF.u32_eq_nat(DST.ln(s), DST.ln(q)),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(DST.ln(s)), U32.to_nat(DST.ln(q))), Nat.is_eq(1n+s, U32.to_nat(DST.ln(q))), Nat.is_eq(1n+s, 1n+q),
      Equal.cong(Nat, Bool, z => Nat.is_eq(z, U32.to_nat(DST.ln(q))), U32.to_nat(DST.ln(s)), 1n+s, DF.ln_nat(s, depth, hd, hs)),
      Equal.cong(Nat, Bool, z => Nat.is_eq(1n+s, z), U32.to_nat(DST.ln(q)), 1n+q, DF.ln_nat(q, depth, hd, hq))))

# ---- the order, prevs and nexts after touching ----

def t_ord(+a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case Nil{}:
      SC.append(Nat, a, Con{s, Nil{}})
    case Con{+y, +r}:
      SC.append(Nat, SC.append(Nat, a, Con{y, r}), Con{s, Nil{}})

def t_tp(+depth: Nat, +tp: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>) -> AR.Tree<U32>:
  match b:
    case Nil{}:
      tp
    case Con{+y, +r}:
      AR.upd(U32, depth, TS.tpup(depth, tp, Con{y, r}, LK.lastl(a, D.nil())), s, LK.lastl(SC.append(Nat, a, Con{y, r}), D.nil()))

def t_tn(+depth: Nat, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>) -> AR.Tree<U32>:
  match b:
    case Nil{}:
      tn
    case Con{+y, +r}:
      TS.tnup(depth, AR.upd(U32, depth, TS.tnup(depth, tn, a, DST.hd_or(Con{y, r}, D.nil())), s, D.nil()), SC.append(Nat, a, Con{y, r}), DST.ln(s))

def mv(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> List<&2, Nat>:
  SC.append(Nat, SC.append(Nat, a, b), Con{s, Nil{}})

def t_ord_eq(+a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>) -> {t_ord(a, s, b) == mv(a, s, b) : List<&2, Nat>}:
  match b:
    case Nil{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => SC.append(Nat, z, Con{s, Nil{}}), a, SC.append(Nat, a, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, a, Nil{}), a, LL.append_nil(Nat, a)))
    case Con{+y, +r}:
      {==}

# ---- the chain ----

def tc_nil(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +fh: U32) -> {F.touch(F.CH{DST.hd(SC.append(Nat, a, Con{s, Nil{}})), DST.lst(SC.append(Nat, a, Con{s, Nil{}})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(SC.append(Nat, a, Con{s, Nil{}})), DST.lst(SC.append(Nat, a, Con{s, Nil{}})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)} : F.Chain}:
  +o = SC.append(Nat, a, Con{s, Nil{}})
  +enw = Equal.trans(Bool, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), U32.is_eq(DST.ln(s), DST.lst(o)), True{},
    Equal.cong(U32, Bool, z => U32.is_eq(z, DST.lst(o)), F.link(U32.from_nat(s)), DST.ln(s), CHN.link_ln(s)),
    L.subst(U32, z => {U32.is_eq(DST.ln(s), z) == True{} : Bool}, DST.ln(s), DST.lst(o), Equal.sym(U32, DST.lst(o), DST.ln(s), RM.lst_app_cons(a, s, Nil{})), RT.eq_self(DST.ln(s), DST.ln(s), {==})))
  L.subst(Bool, z => {F.touch_go(F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), z) == F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)} : F.Chain}, True{}, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), Equal.sym(Bool, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), True{}, enw), {==})

def tc_con(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +y: Nat, +r: List<&2, Nat>, +fh: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, Con{y, r}}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, Con{y, r}})) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, Con{y, r}}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {F.touch(F.CH{DST.hd(SC.append(Nat, a, Con{s, Con{y, r}})), DST.lst(SC.append(Nat, a, Con{s, Con{y, r}})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(t_ord(a, s, Con{y, r})), DST.lst(t_ord(a, s, Con{y, r})), fh, AR.thaw(U32, t_tp(depth, tp, a, s, Con{y, r})), AR.thaw(U32, t_tn(depth, tn, a, s, Con{y, r}))} : F.Chain}:
  +o = SC.append(Nat, a, Con{s, Con{y, r}})
  +ab = SC.append(Nat, a, Con{y, r})
  +P = SC.pow2(depth)
  +q = DST.lst_or(r, y)
  +hsb = LS.notin_r_c(a, s, Con{y, r}, hnd)
  +hlb = L.and_right(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), TL.alllt_r(a, Con{s, Con{y, r}}, P, hl))
  +hs = L.and_left(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), TL.alllt_r(a, Con{s, Con{y, r}}, P, hl))
  +hq = RT.lst_lt(r, y, P, hlb)
  +enw = Equal.trans(Bool, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), U32.is_eq(DST.ln(s), DST.ln(q)), False{},
    Equal.trans(Bool, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), U32.is_eq(DST.ln(s), DST.lst(o)), U32.is_eq(DST.ln(s), DST.ln(q)),
      Equal.cong(U32, Bool, z => U32.is_eq(z, DST.lst(o)), F.link(U32.from_nat(s)), DST.ln(s), CHN.link_ln(s)),
      Equal.cong(U32, Bool, z => U32.is_eq(DST.ln(s), z), DST.lst(o), DST.ln(q), RM.lst_app_cons(a, s, Con{y, r}))),
    Equal.trans(Bool, U32.is_eq(DST.ln(s), DST.ln(q)), Nat.is_eq(s, q), False{}, ln_eq(s, q, depth, hd, hs, hq), SP.ne_of_mem(s, q, Con{y, r}, hsb, RT.lst_mem(r, y))))
  +tp1 = TS.tpup(depth, tp, Con{y, r}, LK.lastl(a, D.nil()))
  +tn1 = TS.tnup(depth, tn, a, DST.hd_or(Con{y, r}, D.nil()))
  +hlab = SP.alllt_join(a, Con{y, r}, P, TL.alllt_l(a, Con{s, Con{y, r}}, P, hl), hlb)
  +e = Equal.trans(F.Chain, F.link_tail(F.unlink(F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), U32.from_nat(s)), F.link_tail(F.CH{DST.hd(ab), DST.lst(ab), fh, AR.thaw(U32, tp1), AR.thaw(U32, tn1)}, U32.from_nat(s)), F.CH{DST.hd(t_ord(a, s, Con{y, r})), DST.lst(t_ord(a, s, Con{y, r})), fh, AR.thaw(U32, t_tp(depth, tp, a, s, Con{y, r})), AR.thaw(U32, t_tn(depth, tn, a, s, Con{y, r}))},
    Equal.cong(F.Chain, F.Chain, c => F.link_tail(c, U32.from_nat(s)), F.unlink(F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)), F.CH{DST.hd(ab), DST.lst(ab), fh, AR.thaw(U32, tp1), AR.thaw(U32, tn1)}, CHN.unlink_ok(depth, tp, tn, a, s, Con{y, r}, fh, hd, pfp, pfn, hl, hk)),
    CHN.link_tail_ok(depth, tp1, tn1, ab, s, fh, hd, TS.tpup_pf(depth, tp, Con{y, r}, LK.lastl(a, D.nil()), pfp), TS.tnup_pf(depth, tn, a, DST.hd_or(Con{y, r}, D.nil()), pfn), hs, hlab))
  L.subst(Bool, z => {F.touch_go(F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), z) == F.CH{DST.hd(t_ord(a, s, Con{y, r})), DST.lst(t_ord(a, s, Con{y, r})), fh, AR.thaw(U32, t_tp(depth, tp, a, s, Con{y, r})), AR.thaw(U32, t_tn(depth, tn, a, s, Con{y, r}))} : F.Chain}, False{}, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), Equal.sym(Bool, U32.is_eq(F.link(U32.from_nat(s)), DST.lst(o)), False{}, enw), OptPromote.result(F.CH{DST.hd(o), DST.lst(o), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s), F.CH{DST.hd(t_ord(a, s, Con{y, r})), DST.lst(t_ord(a, s, Con{y, r})), fh, AR.thaw(U32, t_tp(depth, tp, a, s, Con{y, r})), AR.thaw(U32, t_tn(depth, tn, a, s, Con{y, r}))}, e))

def touch_chain(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>, +fh: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, b}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {F.touch(F.CH{DST.hd(SC.append(Nat, a, Con{s, b})), DST.lst(SC.append(Nat, a, Con{s, b})), fh, AR.thaw(U32, tp), AR.thaw(U32, tn)}, U32.from_nat(s)) == F.CH{DST.hd(t_ord(a, s, b)), DST.lst(t_ord(a, s, b)), fh, AR.thaw(U32, t_tp(depth, tp, a, s, b)), AR.thaw(U32, t_tn(depth, tn, a, s, b))} : F.Chain}:
  match b:
    case Nil{}:
      tc_nil(depth, tp, tn, a, s, fh)
    case Con{+y, +r}:
      tc_con(depth, tp, tn, a, s, y, r, fh, hd, pfp, pfn, hl, hnd, hk)

# ---- the invariant's link parts after touching ----

def t_pf_p(+depth: Nat, +tp: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}) -> {AR.perfect(U32, depth, t_tp(depth, tp, a, s, b)) == True{} : Bool}:
  match b:
    case Nil{}:
      pfp
    case Con{+y, +r}:
      AR.upd_perfect(U32, depth, TS.tpup(depth, tp, Con{y, r}, LK.lastl(a, D.nil())), s, LK.lastl(SC.append(Nat, a, Con{y, r}), D.nil()), TS.tpup_pf(depth, tp, Con{y, r}, LK.lastl(a, D.nil()), pfp))

def t_pf_n(+depth: Nat, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}) -> {AR.perfect(U32, depth, t_tn(depth, tn, a, s, b)) == True{} : Bool}:
  match b:
    case Nil{}:
      pfn
    case Con{+y, +r}:
      TS.tnup_pf(depth, AR.upd(U32, depth, TS.tnup(depth, tn, a, DST.hd_or(Con{y, r}, D.nil())), s, D.nil()), SC.append(Nat, a, Con{y, r}), DST.ln(s), AR.upd_perfect(U32, depth, TS.tnup(depth, tn, a, DST.hd_or(Con{y, r}, D.nil())), s, D.nil(), TS.tnup_pf(depth, tn, a, DST.hd_or(Con{y, r}, D.nil()), pfn)))

def len_of(+t: AR.Tree<U32>, +xs: List<&2, U32>, +depth: Nat, +pf: {AR.perfect(U32, depth, t) == True{} : Bool}, +e: {AR.slots(U32, t) == xs : List<&2, U32>}) -> {SC.length(U32, xs) == SC.pow2(depth) : Nat}:
  L.subst(List<&2, U32>, z => {SC.length(U32, z) == SC.pow2(depth) : Nat}, AR.slots(U32, t), xs, e, AR.slots_length(U32, depth, t, pf))

def lt_len(+i: Nat, +xs: List<&2, U32>, +n: Nat, +e: {SC.length(U32, xs) == n : Nat}, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {Nat.is_lt(i, SC.length(U32, xs)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, n, SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), n, e), h)

def alllt_len(+o: List<&2, Nat>, +xs: List<&2, U32>, +n: Nat, +e: {SC.length(U32, xs) == n : Nat}, +h: {DST.alllt(o, n) == True{} : Bool}) -> {DST.alllt(o, SC.length(U32, xs)) == True{} : Bool}:
  L.subst(Nat, z => {DST.alllt(o, z) == True{} : Bool}, n, SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), n, e), h)

def tl_con(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +y: Nat, +r: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, Con{y, r}}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, Con{y, r}})) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, Con{y, r}}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {DST.lk(t_ord(a, s, Con{y, r}), D.nil(), D.nil(), AR.slots(U32, t_tp(depth, tp, a, s, Con{y, r})), AR.slots(U32, t_tn(depth, tn, a, s, Con{y, r}))) == True{} : Bool}:
  +o = SC.append(Nat, a, Con{s, Con{y, r}})
  +ab = SC.append(Nat, a, Con{y, r})
  +P = SC.pow2(depth)
  +ps = AR.slots(U32, tp)
  +ns = AR.slots(U32, tn)
  +la = LK.lastl(a, D.nil())
  +hb = DST.hd_or(Con{y, r}, D.nil())
  +lab = LK.lastl(ab, D.nil())
  +PU = RT.pupd(ps, Con{y, r}, la)
  +NU = RT.nupd(ns, a, hb)
  +tp1 = TS.tpup(depth, tp, Con{y, r}, la)
  +tn1 = TS.tnup(depth, tn, a, hb)
  +pf1 = TS.tpup_pf(depth, tp, Con{y, r}, la, pfp)
  +pf2 = TS.tnup_pf(depth, tn, a, hb, pfn)
  +hla = TL.alllt_l(a, Con{s, Con{y, r}}, P, hl)
  +hr = TL.alllt_r(a, Con{s, Con{y, r}}, P, hl)
  +hs = L.and_left(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), hr)
  +hlb = L.and_right(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), hr)
  +hlab = SP.alllt_join(a, Con{y, r}, P, hla, hlb)
  +e1 = TS.tpup_slots(depth, tp, Con{y, r}, la, pfp, hlb)
  +e3 = TS.tnup_slots(depth, tn, a, hb, pfn, hla)
  +lp = len_of(tp1, PU, depth, pf1, e1)
  +lnn = len_of(tn1, NU, depth, pf2, e3)
  +hlp = alllt_len(o, ps, P, AR.slots_length(U32, depth, tp, pfp), hl)
  +hln = alllt_len(o, ns, P, AR.slots_length(U32, depth, tn, pfn), hl)
  +lk1 = RM.lk_cut(a, s, Con{y, r}, ps, ns, hnd, hlp, hln, hk)
  +hn = LS.notin_rm(a, s, Con{y, r}, hnd)
  +enil = Equal.sym(List<&2, Nat>, SC.append(Nat, ab, Nil{}), ab, LL.append_nil(Nat, ab))
  +lk2 = IL.lk_ins(SC.append(Nat, ab, Nil{}), Nil{}, s, PU, NU,
    L.subst(List<&2, Nat>, z => {DST.nodup(SC.append(Nat, z, Nil{})) == True{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, SP.nodup_cut(a, s, Con{y, r}, hnd))),
    L.subst(List<&2, Nat>, z => {DST.lmem(s, SC.append(Nat, z, Nil{})) == False{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, L.subst(List<&2, Nat>, z => {DST.lmem(s, z) == False{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, hn)),
    L.subst(List<&2, Nat>, z => {DST.alllt(z, SC.length(U32, NU)) == True{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, alllt_len(ab, NU, P, lnn, hlab)),
    {==}, lt_len(s, PU, P, lp, hs), lt_len(s, NU, P, lnn, hs),
    L.subst(List<&2, Nat>, z => {DST.lk(SC.append(Nat, z, Nil{}), D.nil(), D.nil(), PU, NU) == True{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, L.subst(List<&2, Nat>, z => {DST.lk(z, D.nil(), D.nil(), PU, NU) == True{} : Bool}, ab, SC.append(Nat, ab, Nil{}), enil, lk1)))
  +ep = Equal.trans(List<&2, U32>, AR.slots(U32, AR.upd(U32, depth, tp1, s, lab)), SC.update(U32, AR.slots(U32, tp1), s, lab), SC.update(U32, PU, s, lab),
    AR.upd_slots(U32, depth, tp1, s, lab, hs, pf1),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, s, lab), AR.slots(U32, tp1), PU, e1))
  +tn2 = AR.upd(U32, depth, tn1, s, D.nil())
  +pf3 = AR.upd_perfect(U32, depth, tn1, s, D.nil(), pf2)
  +en = Equal.trans(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn2, ab, DST.ln(s))), RT.nupd(AR.slots(U32, tn2), ab, DST.ln(s)), RT.nupd(SC.update(U32, NU, s, D.nil()), ab, DST.ln(s)),
    TS.tnup_slots(depth, tn2, ab, DST.ln(s), pf3, hlab),
    Equal.trans(List<&2, U32>, RT.nupd(AR.slots(U32, tn2), ab, DST.ln(s)), RT.nupd(SC.update(U32, AR.slots(U32, tn1), s, D.nil()), ab, DST.ln(s)), RT.nupd(SC.update(U32, NU, s, D.nil()), ab, DST.ln(s)),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(z, ab, DST.ln(s)), AR.slots(U32, tn2), SC.update(U32, AR.slots(U32, tn1), s, D.nil()), AR.upd_slots(U32, depth, tn1, s, D.nil(), hs, pf2)),
      Equal.cong(List<&2, U32>, List<&2, U32>, z => RT.nupd(SC.update(U32, z, s, D.nil()), ab, DST.ln(s)), AR.slots(U32, tn1), NU, e3)))
  +lk3 = L.subst(List<&2, Nat>, z => {DST.lk(SC.append(Nat, z, Con{s, Nil{}}), D.nil(), D.nil(), SC.update(U32, PU, s, LK.lastl(z, D.nil())), RT.nupd(SC.update(U32, NU, s, D.nil()), z, DST.ln(s))) == True{} : Bool}, SC.append(Nat, ab, Nil{}), ab, LL.append_nil(Nat, ab), lk2)
  +lk4 = L.subst(List<&2, U32>, z => {DST.lk(SC.append(Nat, ab, Con{s, Nil{}}), D.nil(), D.nil(), z, RT.nupd(SC.update(U32, NU, s, D.nil()), ab, DST.ln(s))) == True{} : Bool}, SC.update(U32, PU, s, lab), AR.slots(U32, AR.upd(U32, depth, tp1, s, lab)), Equal.sym(List<&2, U32>, AR.slots(U32, AR.upd(U32, depth, tp1, s, lab)), SC.update(U32, PU, s, lab), ep), lk3)
  L.subst(List<&2, U32>, z => {DST.lk(SC.append(Nat, ab, Con{s, Nil{}}), D.nil(), D.nil(), AR.slots(U32, AR.upd(U32, depth, tp1, s, lab)), z) == True{} : Bool}, RT.nupd(SC.update(U32, NU, s, D.nil()), ab, DST.ln(s)), AR.slots(U32, TS.tnup(depth, tn2, ab, DST.ln(s))), Equal.sym(List<&2, U32>, AR.slots(U32, TS.tnup(depth, tn2, ab, DST.ln(s))), RT.nupd(SC.update(U32, NU, s, D.nil()), ab, DST.ln(s)), en), lk4)

def t_lk(+depth: Nat, +tp: AR.Tree<U32>, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hnd: {DST.nodup(SC.append(Nat, a, Con{s, b})) == True{} : Bool}, +hk: {DST.lk(SC.append(Nat, a, Con{s, b}), D.nil(), D.nil(), AR.slots(U32, tp), AR.slots(U32, tn)) == True{} : Bool}) -> {DST.lk(t_ord(a, s, b), D.nil(), D.nil(), AR.slots(U32, t_tp(depth, tp, a, s, b)), AR.slots(U32, t_tn(depth, tn, a, s, b))) == True{} : Bool}:
  match b:
    case Nil{}:
      hk
    case Con{+y, +r}:
      tl_con(depth, tp, tn, a, s, y, r, hd, pfp, pfn, hl, hnd, hk)

def tf_con(+depth: Nat, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, +y: Nat, +r: List<&2, Nat>, +fl: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, Con{y, r}}), SC.pow2(depth)) == True{} : Bool}, +hnd2: {DST.nodup(SC.append(Nat, SC.append(Nat, a, Con{s, Con{y, r}}), fl)) == True{} : Bool}, +hfk: {ST.fk(fl, AR.slots(U32, tn)) == True{} : Bool}) -> {ST.fk(fl, AR.slots(U32, t_tn(depth, tn, a, s, Con{y, r}))) == True{} : Bool}:
  +ab = SC.append(Nat, a, Con{y, r})
  +P = SC.pow2(depth)
  +hb = DST.hd_or(Con{y, r}, D.nil())
  +tn1 = TS.tnup(depth, tn, a, hb)
  +pf2 = TS.tnup_pf(depth, tn, a, hb, pfn)
  +tn2 = AR.upd(U32, depth, tn1, s, D.nil())
  +pf3 = AR.upd_perfect(U32, depth, tn1, s, D.nil(), pf2)
  +hla = TL.alllt_l(a, Con{s, Con{y, r}}, P, hl)
  +hr = TL.alllt_r(a, Con{s, Con{y, r}}, P, hl)
  +hs = L.and_left(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), hr)
  +hlab = SP.alllt_join(a, Con{y, r}, P, hla, L.and_right(Nat.is_lt(s, P), DST.alllt(Con{y, r}, P), hr))
  +h9 = LS.nodup_rm(a, s, Con{y, r}, fl, hnd2)
  +hsfl = TB.not_false(DST.lmem(s, fl), L.and_left(Bool.not(DST.lmem(s, fl)), DST.nodup(fl), SP.nodup_app_r(ab, Con{s, fl}, h9)))
  +hdab = RM.disj_tail(ab, s, fl, SP.nodup_disj(ab, Con{s, fl}, h9))
  +hda = RS.disj_app_l(a, Con{y, r}, fl, hdab)
  +ns = AR.slots(U32, tn)
  +NU = RT.nupd(ns, a, hb)
  +e3 = TS.tnup_slots(depth, tn, a, hb, pfn, hla)
  +f1 = Equal.trans(Bool, ST.fk(fl, AR.slots(U32, tn1)), ST.fk(fl, NU), True{}, Equal.cong(List<&2, U32>, Bool, z => ST.fk(fl, z), AR.slots(U32, tn1), NU, e3), Equal.trans(Bool, ST.fk(fl, NU), ST.fk(fl, ns), True{}, LS.fk_frame_nupd(fl, ns, a, hb, hda), hfk))
  +f2 = Equal.trans(Bool, ST.fk(fl, AR.slots(U32, tn2)), ST.fk(fl, SC.update(U32, AR.slots(U32, tn1), s, D.nil())), True{}, Equal.cong(List<&2, U32>, Bool, z => ST.fk(fl, z), AR.slots(U32, tn2), SC.update(U32, AR.slots(U32, tn1), s, D.nil()), AR.upd_slots(U32, depth, tn1, s, D.nil(), hs, pf2)), Equal.trans(Bool, ST.fk(fl, SC.update(U32, AR.slots(U32, tn1), s, D.nil())), ST.fk(fl, AR.slots(U32, tn1)), True{}, LS.fk_frame(fl, AR.slots(U32, tn1), s, D.nil(), hsfl), f1))
  Equal.trans(Bool, ST.fk(fl, AR.slots(U32, TS.tnup(depth, tn2, ab, DST.ln(s)))), ST.fk(fl, RT.nupd(AR.slots(U32, tn2), ab, DST.ln(s))), True{},
    Equal.cong(List<&2, U32>, Bool, z => ST.fk(fl, z), AR.slots(U32, TS.tnup(depth, tn2, ab, DST.ln(s))), RT.nupd(AR.slots(U32, tn2), ab, DST.ln(s)), TS.tnup_slots(depth, tn2, ab, DST.ln(s), pf3, hlab)),
    Equal.trans(Bool, ST.fk(fl, RT.nupd(AR.slots(U32, tn2), ab, DST.ln(s))), ST.fk(fl, AR.slots(U32, tn2)), True{}, LS.fk_frame_nupd(fl, AR.slots(U32, tn2), ab, DST.ln(s), hdab), f2))

def t_fk(+depth: Nat, +tn: AR.Tree<U32>, +a: List<&2, Nat>, +s: Nat, b: List<&2, Nat>, +fl: List<&2, Nat>, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfn: {AR.perfect(U32, depth, tn) == True{} : Bool}, +hl: {DST.alllt(SC.append(Nat, a, Con{s, b}), SC.pow2(depth)) == True{} : Bool}, +hnd2: {DST.nodup(SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl)) == True{} : Bool}, +hfk: {ST.fk(fl, AR.slots(U32, tn)) == True{} : Bool}) -> {ST.fk(fl, AR.slots(U32, t_tn(depth, tn, a, s, b))) == True{} : Bool}:
  match b:
    case Nil{}:
      hfk
    case Con{+y, +r}:
      tf_con(depth, tn, a, s, y, r, fl, hd, pfn, hl, hnd2, hfk)

# ---- the order (a ++ b) ++ [s] against a ++ [s] ++ b ----

def or_perm(a: Bool, b: Bool, c: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(c, False{})) == Bool.or(a, Bool.or(c, b)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def and_perm(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, True{})) == Bool.and(a, Bool.and(c, b)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def nodup_cs(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +h: {DST.nodup(SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl)) == True{} : Bool}) -> {DST.nodup(Con{s, SC.append(Nat, SC.append(Nat, a, b), fl)}) == True{} : Bool}:
  +h1 = L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl), SC.append(Nat, a, Con{s, SC.append(Nat, b, fl)}), LL.append_assoc(Nat, a, Con{s, b}, fl), h)
  +h2 = L.subst(Bool, z => {z == True{} : Bool}, DST.nodup(SC.append(Nat, a, Con{s, SC.append(Nat, b, fl)})), DST.nodup(Con{s, SC.append(Nat, a, SC.append(Nat, b, fl))}), LS.nodup_front(a, s, SC.append(Nat, b, fl)), h1)
  L.subst(List<&2, Nat>, z => {DST.nodup(Con{s, z}) == True{} : Bool}, SC.append(Nat, a, SC.append(Nat, b, fl)), SC.append(Nat, SC.append(Nat, a, b), fl), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, a, b), fl), SC.append(Nat, a, SC.append(Nat, b, fl)), LL.append_assoc(Nat, a, b, fl)), h2)

def nodup_mv(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +fl: List<&2, Nat>, +h: {DST.nodup(SC.append(Nat, SC.append(Nat, a, Con{s, b}), fl)) == True{} : Bool}) -> {DST.nodup(SC.append(Nat, mv(a, s, b), fl)) == True{} : Bool}:
  +ab = SC.append(Nat, a, b)
  +h3 = nodup_cs(a, s, b, fl, h)
  +h4 = L.subst(Bool, z => {z == True{} : Bool}, DST.nodup(Con{s, SC.append(Nat, ab, fl)}), DST.nodup(SC.append(Nat, ab, Con{s, fl})), Equal.sym(Bool, DST.nodup(SC.append(Nat, ab, Con{s, fl})), DST.nodup(Con{s, SC.append(Nat, ab, fl)}), LS.nodup_front(ab, s, fl)), h3)
  L.subst(List<&2, Nat>, z => {DST.nodup(z) == True{} : Bool}, SC.append(Nat, ab, Con{s, fl}), SC.append(Nat, SC.append(Nat, ab, Con{s, Nil{}}), fl), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, ab, Con{s, Nil{}}), fl), SC.append(Nat, ab, Con{s, fl}), LL.append_assoc(Nat, ab, Con{s, Nil{}}, fl)), h4)

def alllt_mv(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +n: Nat, +h: {DST.alllt(SC.append(Nat, a, Con{s, b}), n) == True{} : Bool}) -> {DST.alllt(mv(a, s, b), n) == True{} : Bool}:
  +hr = TL.alllt_r(a, Con{s, b}, n, h)
  SP.alllt_join(SC.append(Nat, a, b), Con{s, Nil{}}, n, SP.alllt_join(a, b, n, TL.alllt_l(a, Con{s, b}, n, h), L.and_right(Nat.is_lt(s, n), DST.alllt(b, n), hr)), L.and_intro(Nat.is_lt(s, n), True{}, L.and_left(Nat.is_lt(s, n), DST.alllt(b, n), hr), {==}))

def len_mv(+a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>) -> {SC.length(Nat, mv(a, s, b)) == SC.length(Nat, SC.append(Nat, a, Con{s, b})) : Nat}:
  +l = SC.length(Nat, SC.append(Nat, a, b))
  Equal.trans(Nat, SC.length(Nat, mv(a, s, b)), Nat.add(l, 1n), SC.length(Nat, SC.append(Nat, a, Con{s, b})),
    LL.length_append(Nat, SC.append(Nat, a, b), Con{s, Nil{}}),
    Equal.trans(Nat, Nat.add(l, 1n), 1n+Nat.add(l, 0n), SC.length(Nat, SC.append(Nat, a, Con{s, b})),
      N.add_succ(l, 0n),
      Equal.trans(Nat, 1n+Nat.add(l, 0n), 1n+l, SC.length(Nat, SC.append(Nat, a, Con{s, b})),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(l, 0n), l, N.add_zero(l)),
        Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, Con{s, b})), 1n+l, RS.len_cut(a, s, b)))))

def kmem_mv(+ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +q: String) -> {Inv.member(ST.keys_at(ks, mv(a, s, b)), q) == Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q) : Bool}:
  +A = Inv.member(ST.keys_at(ks, a), q)
  +B = Inv.member(ST.keys_at(ks, b), q)
  +C = String.eq(ST.kat(ks, s), q)
  Equal.trans(Bool, Inv.member(ST.keys_at(ks, mv(a, s, b)), q), Bool.or(Bool.or(A, B), Bool.or(C, False{})), Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q),
    Equal.trans(Bool, Inv.member(ST.keys_at(ks, mv(a, s, b)), q), Bool.or(Inv.member(ST.keys_at(ks, SC.append(Nat, a, b)), q), Bool.or(C, False{})), Bool.or(Bool.or(A, B), Bool.or(C, False{})),
      TB.kmem_app(ks, SC.append(Nat, a, b), Con{s, Nil{}}, q),
      Equal.cong(Bool, Bool, z => Bool.or(z, Bool.or(C, False{})), Inv.member(ST.keys_at(ks, SC.append(Nat, a, b)), q), Bool.or(A, B), TB.kmem_app(ks, a, b, q))),
    Equal.trans(Bool, Bool.or(Bool.or(A, B), Bool.or(C, False{})), Bool.or(A, Bool.or(C, B)), Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q),
      or_perm(A, B, C),
      Equal.sym(Bool, Inv.member(ST.keys_at(ks, SC.append(Nat, a, Con{s, b})), q), Bool.or(A, Bool.or(C, B)), TB.kmem_app(ks, a, Con{s, b}, q))))

def incl_mv(+xs: List<&2, String>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {Inv.included(xs, ST.keys_at(ks, SC.append(Nat, a, Con{s, b}))) == True{} : Bool}) -> {Inv.included(xs, ST.keys_at(ks, mv(a, s, b))) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +K = ST.keys_at(ks, SC.append(Nat, a, Con{s, b}))
      L.and_intro(Inv.member(ST.keys_at(ks, mv(a, s, b)), x), Inv.included(r, ST.keys_at(ks, mv(a, s, b))),
        L.subst(Bool, z => {z == True{} : Bool}, Inv.member(K, x), Inv.member(ST.keys_at(ks, mv(a, s, b)), x), Equal.sym(Bool, Inv.member(ST.keys_at(ks, mv(a, s, b)), x), Inv.member(K, x), kmem_mv(ks, a, s, b, x)), L.and_left(Inv.member(K, x), Inv.included(r, K), h)),
        incl_mv(r, ks, a, s, b, L.and_right(Inv.member(K, x), Inv.included(r, K), h)))

def am_mv(+t: Map<&2, Maybe<&2, U32>>, +ks: List<&2, String>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.all_mapped(t, ks, mv(a, s, b)) == True{} : Bool}:
  +A = ST.all_mapped(t, ks, a)
  +B = ST.all_mapped(t, ks, b)
  +C = ST.mapped(t, ST.kat(ks, s), s)
  +e = Equal.trans(Bool, ST.all_mapped(t, ks, mv(a, s, b)), Bool.and(Bool.and(A, B), Bool.and(C, True{})), ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})),
    Equal.trans(Bool, ST.all_mapped(t, ks, mv(a, s, b)), Bool.and(ST.all_mapped(t, ks, SC.append(Nat, a, b)), Bool.and(C, True{})), Bool.and(Bool.and(A, B), Bool.and(C, True{})),
      LS.am_app(t, ks, SC.append(Nat, a, b), Con{s, Nil{}}),
      Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(C, True{})), ST.all_mapped(t, ks, SC.append(Nat, a, b)), Bool.and(A, B), LS.am_app(t, ks, a, b))),
    Equal.trans(Bool, Bool.and(Bool.and(A, B), Bool.and(C, True{})), Bool.and(A, Bool.and(C, B)), ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})),
      and_perm(A, B, C),
      Equal.sym(Bool, ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})), Bool.and(A, Bool.and(C, B)), LS.am_app(t, ks, a, Con{s, b}))))
  L.subst(Bool, z => {z == True{} : Bool}, ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})), ST.all_mapped(t, ks, mv(a, s, b)), Equal.sym(Bool, ST.all_mapped(t, ks, mv(a, s, b)), ST.all_mapped(t, ks, SC.append(Nat, a, Con{s, b})), e), h)

def occ_mv(-V: Data, +es: List<&2, F.Slot<V>>, +a: List<&2, Nat>, +s: Nat, +b: List<&2, Nat>, +h: {ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})) == True{} : Bool}) -> {ST.all_occ(V, es, mv(a, s, b)) == True{} : Bool}:
  +A = ST.all_occ(V, es, a)
  +B = ST.all_occ(V, es, b)
  +C = ST.is_occ(V, ST.sat(V, es, s))
  +e = Equal.trans(Bool, ST.all_occ(V, es, mv(a, s, b)), Bool.and(Bool.and(A, B), Bool.and(C, True{})), ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})),
    Equal.trans(Bool, ST.all_occ(V, es, mv(a, s, b)), Bool.and(ST.all_occ(V, es, SC.append(Nat, a, b)), Bool.and(C, True{})), Bool.and(Bool.and(A, B), Bool.and(C, True{})),
      LS.occ_app(V, es, SC.append(Nat, a, b), Con{s, Nil{}}),
      Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(C, True{})), ST.all_occ(V, es, SC.append(Nat, a, b)), Bool.and(A, B), LS.occ_app(V, es, a, b))),
    Equal.trans(Bool, Bool.and(Bool.and(A, B), Bool.and(C, True{})), Bool.and(A, Bool.and(C, B)), ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})),
      and_perm(A, B, C),
      Equal.sym(Bool, ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})), Bool.and(A, Bool.and(C, B)), LS.occ_app(V, es, a, Con{s, b}))))
  L.subst(Bool, z => {z == True{} : Bool}, ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})), ST.all_occ(V, es, mv(a, s, b)), Equal.sym(Bool, ST.all_occ(V, es, mv(a, s, b)), ST.all_occ(V, es, SC.append(Nat, a, Con{s, b})), e), h)
