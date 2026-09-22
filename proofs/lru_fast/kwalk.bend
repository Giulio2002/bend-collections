import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import support/link_primitives.bend as D
import support/links_state.bend as DST
import support/links_links.bend as LK
import support/links_facts.bend as DF
import support/links_tolist.bend as TL
import ./state.bend as ST

# keys_list walks the recency chain backwards from the tail through prevs,
# consing each slot's key: after walking the whole order the accumulator holds
# the keys oldest first.

def kcur(+tk: AR.Tree<String>, +tp: AR.Tree<U32>, +acc: List<&2, String>, +at: U32) -> F.Walk:
  F.WK{AR.thaw(String, tk), AR.thaw(U32, tp), acc, at}

def keys_app(+ks: List<&2, String>, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {ST.keys_at(ks, SC.append(Nat, a, b)) == SC.append(String, ST.keys_at(ks, a), ST.keys_at(ks, b)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LL.cons_cong(String, ST.kat(ks, x), ST.keys_at(ks, SC.append(Nat, t, b)), SC.append(String, ST.keys_at(ks, t), ST.keys_at(ks, b)), keys_app(ks, t, b))

def kstep_ok(+depth: Nat, +tk: AR.Tree<String>, +tp: AR.Tree<U32>, +acc: List<&2, String>, +x: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +hx: {Nat.is_lt(x, SC.pow2(depth)) == True{} : Bool}) -> {F.wk_step(kcur(tk, tp, acc, DST.ln(x))) == kcur(tk, tp, Con{ST.kat(AR.slots(String, tk), x), acc}, DST.lat(AR.slots(U32, tp), x)) : F.Walk}:
  +k = ST.kat(AR.slots(String, tk), x)
  +es = DF.slot_ln(x, depth, hd, hx)
  +e1 = Equal.cong(U32, F.Walk, z => F.wk_k(AR.thaw(U32, tp), acc, DST.ln(x), Array.get(String, AR.thaw(String, tk), z)), F.slot(DST.ln(x)), U32.from_nat(x), es)
  +e2 = Equal.cong(Array<String> & String, F.Walk, r => F.wk_k(AR.thaw(U32, tp), acc, DST.ln(x), r), Array.get(String, AR.thaw(String, tk), U32.from_nat(x)), (AR.thaw(String, tk), k), TL.get_at(String, depth, tk, x, "", hd, pfk, hx))
  +e3 = Equal.cong(U32, F.Walk, z => F.wk_p(AR.thaw(String, tk), Con{k, acc}, Array.get(U32, AR.thaw(U32, tp), z)), F.slot(DST.ln(x)), U32.from_nat(x), es)
  +e4 = Equal.cong(Array<U32> & U32, F.Walk, r => F.wk_p(AR.thaw(String, tk), Con{k, acc}, r), Array.get(U32, AR.thaw(U32, tp), U32.from_nat(x)), (AR.thaw(U32, tp), DST.lat(AR.slots(U32, tp), x)), TL.get_at(U32, depth, tp, x, 0, hd, pfp, hx))
  Equal.trans(F.Walk, F.wk_k(AR.thaw(U32, tp), acc, DST.ln(x), Array.get(String, AR.thaw(String, tk), F.slot(DST.ln(x)))), F.wk_k(AR.thaw(U32, tp), acc, DST.ln(x), Array.get(String, AR.thaw(String, tk), U32.from_nat(x))), kcur(tk, tp, Con{k, acc}, DST.lat(AR.slots(U32, tp), x)), e1,
    Equal.trans(F.Walk, F.wk_k(AR.thaw(U32, tp), acc, DST.ln(x), Array.get(String, AR.thaw(String, tk), U32.from_nat(x))), F.wk_p(AR.thaw(String, tk), Con{k, acc}, Array.get(U32, AR.thaw(U32, tp), F.slot(DST.ln(x)))), kcur(tk, tp, Con{k, acc}, DST.lat(AR.slots(U32, tp), x)), e2,
      Equal.trans(F.Walk, F.wk_p(AR.thaw(String, tk), Con{k, acc}, Array.get(U32, AR.thaw(U32, tp), F.slot(DST.ln(x)))), F.wk_p(AR.thaw(String, tk), Con{k, acc}, Array.get(U32, AR.thaw(U32, tp), U32.from_nat(x))), kcur(tk, tp, Con{k, acc}, DST.lat(AR.slots(U32, tp), x)), e3, e4)))

def kwalk_ok(+depth: Nat, +tk: AR.Tree<String>, +tp: AR.Tree<U32>, +ns: List<&2, U32>, +r: List<&2, Nat>, +acc: List<&2, String>, +e: U32, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +pfk: {AR.perfect(String, depth, tk) == True{} : Bool}, +pfp: {AR.perfect(U32, depth, tp) == True{} : Bool}, +hl: {DST.alllt(SC.reverse(Nat, r), SC.pow2(depth)) == True{} : Bool}, +hk: {DST.lk(SC.reverse(Nat, r), D.nil(), e, AR.slots(U32, tp), ns) == True{} : Bool}) -> {F.wk_loop(SC.length(Nat, r), kcur(tk, tp, acc, LK.lastl(SC.reverse(Nat, r), D.nil()))) == kcur(tk, tp, SC.append(String, ST.keys_at(AR.slots(String, tk), SC.reverse(Nat, r)), acc), D.nil()) : F.Walk}:
  match r:
    case Nil{}:
      {==}
    case Con{+x, +rt}:
      +ks = AR.slots(String, tk)
      +ps = AR.slots(U32, tp)
      +a1 = SC.reverse(Nat, rt)
      +ap = SC.append(Nat, a1, Con{x, Nil{}})
      +esn = LL.snoc_append(Nat, a1, x)
      +hl1 = L.subst(List<&2, Nat>, z => {DST.alllt(z, SC.pow2(depth)) == True{} : Bool}, SC.snoc(Nat, a1, x), ap, esn, hl)
      +hk1 = L.subst(List<&2, Nat>, z => {DST.lk(z, D.nil(), e, ps, ns) == True{} : Bool}, SC.snoc(Nat, a1, x), ap, esn, hk)
      +hk2 = L.subst(Bool, b => {b == True{} : Bool}, DST.lk(ap, D.nil(), e, ps, ns), Bool.and(DST.lk(a1, D.nil(), DST.ln(x), ps, ns), DST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns)), LK.lk_app(a1, Con{x, Nil{}}, D.nil(), e, ps, ns), hk1)
      +hka = L.and_left(DST.lk(a1, D.nil(), DST.ln(x), ps, ns), DST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns), hk2)
      +hkx = L.and_right(DST.lk(a1, D.nil(), DST.ln(x), ps, ns), DST.lk(Con{x, Nil{}}, LK.lastl(a1, D.nil()), e, ps, ns), hk2)
      +hx = L.and_left(Nat.is_lt(x, SC.pow2(depth)), True{}, TL.alllt_r(a1, Con{x, Nil{}}, SC.pow2(depth), hl1))
      +k = ST.kat(ks, x)
      +ih = kwalk_ok(depth, tk, tp, ns, rt, Con{k, acc}, DST.ln(x), hd, pfk, pfp, TL.alllt_l(a1, Con{x, Nil{}}, SC.pow2(depth), hl1), hka)
      +elast = Equal.trans(U32, LK.lastl(SC.snoc(Nat, a1, x), D.nil()), LK.lastl(ap, D.nil()), DST.ln(x), Equal.cong(List<&2, Nat>, U32, z => LK.lastl(z, D.nil()), SC.snoc(Nat, a1, x), ap, esn), TL.lastl_snoc(a1, x, D.nil()))
      +vv = SC.append(String, ST.keys_at(ks, a1), Con{k, acc})
      +lhs = Equal.trans(F.Walk, F.wk_loop(1n+SC.length(Nat, rt), kcur(tk, tp, acc, LK.lastl(SC.snoc(Nat, a1, x), D.nil()))), F.wk_loop(SC.length(Nat, rt), F.wk_step(kcur(tk, tp, acc, DST.ln(x)))), kcur(tk, tp, vv, D.nil()),
        Equal.cong(U32, F.Walk, z => F.wk_loop(1n+SC.length(Nat, rt), kcur(tk, tp, acc, z)), LK.lastl(SC.snoc(Nat, a1, x), D.nil()), DST.ln(x), elast),
        Equal.trans(F.Walk, F.wk_loop(SC.length(Nat, rt), F.wk_step(kcur(tk, tp, acc, DST.ln(x)))), F.wk_loop(SC.length(Nat, rt), kcur(tk, tp, Con{k, acc}, DST.lat(ps, x))), kcur(tk, tp, vv, D.nil()),
          Equal.cong(F.Walk, F.Walk, c => F.wk_loop(SC.length(Nat, rt), c), F.wk_step(kcur(tk, tp, acc, DST.ln(x))), kcur(tk, tp, Con{k, acc}, DST.lat(ps, x)), kstep_ok(depth, tk, tp, acc, x, hd, pfk, pfp, hx)),
          Equal.trans(F.Walk, F.wk_loop(SC.length(Nat, rt), kcur(tk, tp, Con{k, acc}, DST.lat(ps, x))), F.wk_loop(SC.length(Nat, rt), kcur(tk, tp, Con{k, acc}, LK.lastl(a1, D.nil()))), kcur(tk, tp, vv, D.nil()),
            Equal.cong(U32, F.Walk, z => F.wk_loop(SC.length(Nat, rt), kcur(tk, tp, Con{k, acc}, z)), DST.lat(ps, x), LK.lastl(a1, D.nil()), TL.lk_single_p(x, LK.lastl(a1, D.nil()), e, ps, ns, hkx)),
            ih)))
      +ekeys0 = Equal.trans(List<&2, String>, SC.append(String, ST.keys_at(ks, SC.snoc(Nat, a1, x)), acc), SC.append(String, ST.keys_at(ks, ap), acc), vv,
        Equal.cong(List<&2, Nat>, List<&2, String>, z => SC.append(String, ST.keys_at(ks, z), acc), SC.snoc(Nat, a1, x), ap, esn),
        Equal.trans(List<&2, String>, SC.append(String, ST.keys_at(ks, ap), acc), SC.append(String, SC.append(String, ST.keys_at(ks, a1), Con{k, Nil{}}), acc), vv,
          Equal.cong(List<&2, String>, List<&2, String>, z => SC.append(String, z, acc), ST.keys_at(ks, ap), SC.append(String, ST.keys_at(ks, a1), Con{k, Nil{}}), keys_app(ks, a1, Con{x, Nil{}})),
          LL.append_assoc(String, ST.keys_at(ks, a1), Con{k, Nil{}}, acc)))
      Equal.trans(F.Walk, F.wk_loop(1n+SC.length(Nat, rt), kcur(tk, tp, acc, LK.lastl(SC.snoc(Nat, a1, x), D.nil()))), kcur(tk, tp, vv, D.nil()), kcur(tk, tp, SC.append(String, ST.keys_at(ks, SC.snoc(Nat, a1, x)), acc), D.nil()),
        lhs,
        Equal.cong(List<&2, String>, F.Walk, z => kcur(tk, tp, z, D.nil()), vv, SC.append(String, ST.keys_at(ks, SC.snoc(Nat, a1, x)), acc), Equal.sym(List<&2, String>, SC.append(String, ST.keys_at(ks, SC.snoc(Nat, a1, x)), acc), vv, ekeys0)))
