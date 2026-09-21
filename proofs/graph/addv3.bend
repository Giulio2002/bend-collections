import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../binary_heap/u32idx.bend as IX
import ../../reference/lru/proofs/nat_algebra.bend as NA
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./search.bend as SE
import ./window.bend as W
import ./ops.bend as OP
import ./blk.bend as BK
import ./edge.bend as ED
import ./blkops.bend as BO
import ./gstep.bend as GT
import ./zip.bend as ZP
import ./asc.bend as AS
import ./ashift.bend as AS2
import ./rmedge.bend as RM
import ./ucore.bend as UC
import ./addv1.bend as AV
import ./addv2.bend as AV2
import ./addedge.bend as AE
import ./lb.bend as LB

# add_vertex, part 3: doubling the vertex table on either side, and the
# case analysis of src/graph.bend's add_vertex.

# ---- a relocated window describes the same graph ----

# (lg, hg, dg, ig, ag) holds the same window as the good shadow (lo, hi, depth, it, at).
def gs_good(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +lg: Nat, +hg: Nat, +dg: Nat, +ig: AR.Tree<U32>, +ag: AR.Tree<AR.Tree<U32>>, +hdg: {Nat.is_le(dg, 31n) == True{} : Bool}, +hpi: {AR.perfect(U32, dg, ig) == True{} : Bool}, +hpa: {AR.perfect(AR.Tree<U32>, dg, ag) == True{} : Bool}, +hlo: {Nat.is_le(lg, hg) == True{} : Bool}, +hcap: {Nat.is_le(hg, SC.pow2(dg)) == True{} : Bool}, +hwk: {RM.KS(lg, hg, ig) == RM.KS(lo, hi, it) : List<&2, U32>}, +hwb: {RM.BW(lg, hg, ag) == RM.BW(lo, hi, at) : List<&2, AR.Tree<U32>>}) -> {ST.good(ST.Sh{dir, lg, hg, dg, ig, ag}) == True{} : Bool}:
  +hasc = AS.asc_at_of_win(Nat.sub(hg, lg), AR.slots(U32, ig), lg, ED.win_fits(U32, dg, ig, lg, hg, hpi, hlo, hcap),
    L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, RM.KS(lo, hi, it), RM.KS(lg, hg, ig), Equal.sym(List<&2, U32>, RM.KS(lg, hg, ig), RM.KS(lo, hi, it), hwk), W.asc_win(Nat.sub(hi, lo), AR.slots(U32, it), lo, OP.g_asc(dir, lo, hi, depth, it, at, h))))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, RM.BW(lo, hi, at), RM.BW(lg, hg, ag), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lg, hg, ag), RM.BW(lo, hi, at), hwb), OP.g_blocks(dir, lo, hi, depth, it, at, h))
  +hwf = L.subst(List<&2, U32>, z => {GS.wf(GS.GM{dir, ST.amodel(z, RM.BW(lg, hg, ag))}) == True{} : Bool}, RM.KS(lo, hi, it), RM.KS(lg, hg, ig), Equal.sym(List<&2, U32>, RM.KS(lg, hg, ig), RM.KS(lo, hi, it), hwk),
    L.subst(List<&2, AR.Tree<U32>>, z => {GS.wf(GS.GM{dir, ST.amodel(RM.KS(lo, hi, it), z)}) == True{} : Bool}, RM.BW(lo, hi, at), RM.BW(lg, hg, ag), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lg, hg, ag), RM.BW(lo, hi, at), hwb), OP.g_wf(dir, lo, hi, depth, it, at, h)))
  GT.good_mk(dir, lg, hg, dg, ig, ag, hdg, hpi, hpa, hlo, hcap, hasc, hbl, hwf)

def gs_am(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +lg: Nat, +hg: Nat, +ig: AR.Tree<U32>, +ag: AR.Tree<AR.Tree<U32>>, +hwk: {RM.KS(lg, hg, ig) == RM.KS(lo, hi, it) : List<&2, U32>}, +hwb: {RM.BW(lg, hg, ag) == RM.BW(lo, hi, at) : List<&2, AR.Tree<U32>>}) -> {RM.AM(lg, hg, ig, ag) == RM.AM(lo, hi, it, at) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, RM.AM(lg, hg, ig, ag), ST.amodel(RM.KS(lo, hi, it), RM.BW(lg, hg, ag)), RM.AM(lo, hi, it, at),
    Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(z, RM.BW(lg, hg, ag)), RM.KS(lg, hg, ig), RM.KS(lo, hi, it), hwk),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(RM.KS(lo, hi, it), z), RM.BW(lg, hg, ag), RM.BW(lo, hi, at), hwb))

def gs_mu(+d1: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +lg: Nat, +hg: Nat, +dg: Nat, +ig: AR.Tree<U32>, +ag: AR.Tree<AR.Tree<U32>>, +hk: {Nat.sub(hg, lg) == Nat.sub(hi, lo) : Nat}, +hwb: {RM.BW(lg, hg, ag) == RM.BW(lo, hi, at) : List<&2, AR.Tree<U32>>}) -> {GT.mu(ST.Sh{d1, lg, hg, dg, ig, ag}) == GT.mu(ST.Sh{d1, lo, hi, depth, it, at}) : Nat}:
  Equal.trans(Nat, GT.mu(ST.Sh{d1, lg, hg, dg, ig, ag}), Nat.add(Nat.sub(hi, lo), GT.mdeg(RM.BW(lg, hg, ag))), GT.mu(ST.Sh{d1, lo, hi, depth, it, at}),
    Equal.cong(Nat, Nat, z => Nat.add(z, GT.mdeg(RM.BW(lg, hg, ag))), Nat.sub(hg, lg), Nat.sub(hi, lo), hk),
    Equal.cong(List<&2, AR.Tree<U32>>, Nat, z => Nat.add(Nat.sub(hi, lo), GT.mdeg(z)), RM.BW(lg, hg, ag), RM.BW(lo, hi, at), hwb))

def gs_lv(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +lg: Nat, +hg: Nat, +ig: AR.Tree<U32>, +v: U32, +hwk: {RM.KS(lg, hg, ig) == RM.KS(lo, hi, it) : List<&2, U32>}) -> {AV.LV(lg, hg, ig, v) == AV.LV(lo, hi, it, v) : Nat}:
  Equal.trans(Nat, AV.LV(lg, hg, ig, v), W.lbu(v, RM.KS(lg, hg, ig)), AV.LV(lo, hi, it, v), W.lbs_lbu(v, AR.slots(U32, ig), Nat.sub(hg, lg), lg),
    Equal.trans(Nat, W.lbu(v, RM.KS(lg, hg, ig)), W.lbu(v, RM.KS(lo, hi, it)), AV.LV(lo, hi, it, v),
      Equal.cong(List<&2, U32>, Nat, z => W.lbu(v, z), RM.KS(lg, hg, ig), RM.KS(lo, hi, it), hwk),
      Equal.sym(Nat, AV.LV(lo, hi, it, v), W.lbu(v, RM.KS(lo, hi, it)), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo))))

def fx_eqat(+t: AR.Tree<U32>, +d: Nat, +lo: Nat, +hi: Nat, +v: U32, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(d)) == True{} : Bool}) -> {RM.FX(lo, hi, t, v) == W.eq_at(RM.KS(lo, hi, t), AV.LV(lo, hi, t, v), v) : Bool}:
  W.found_bridge(t, lo, hi, Nat.sub(hi, lo), AV.LV(lo, hi, t, v), v, {==}, hlo, AV.av_hl(lo, hi, t, v),
    L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, AR.slots(U32, t)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, t)), SC.pow2(d), AR.slots_length(U32, d, t, pf)), hcap))

def gs_fx(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +lg: Nat, +hg: Nat, +dg: Nat, +ig: AR.Tree<U32>, +v: U32, +hpi: {AR.perfect(U32, dg, ig) == True{} : Bool}, +hlo: {Nat.is_le(lg, hg) == True{} : Bool}, +hcap: {Nat.is_le(hg, SC.pow2(dg)) == True{} : Bool}, +hwk: {RM.KS(lg, hg, ig) == RM.KS(lo, hi, it) : List<&2, U32>}) -> {RM.FX(lg, hg, ig, v) == RM.FX(lo, hi, it, v) : Bool}:
  Equal.trans(Bool, RM.FX(lg, hg, ig, v), W.eq_at(RM.KS(lg, hg, ig), AV.LV(lg, hg, ig, v), v), RM.FX(lo, hi, it, v), fx_eqat(ig, dg, lg, hg, v, hpi, hlo, hcap),
    Equal.trans(Bool, W.eq_at(RM.KS(lg, hg, ig), AV.LV(lg, hg, ig, v), v), W.eq_at(RM.KS(lo, hi, it), AV.LV(lo, hi, it, v), v), RM.FX(lo, hi, it, v),
      Equal.trans(Bool, W.eq_at(RM.KS(lg, hg, ig), AV.LV(lg, hg, ig, v), v), W.eq_at(RM.KS(lo, hi, it), AV.LV(lg, hg, ig, v), v), W.eq_at(RM.KS(lo, hi, it), AV.LV(lo, hi, it, v), v),
        Equal.cong(List<&2, U32>, Bool, z => W.eq_at(z, AV.LV(lg, hg, ig, v), v), RM.KS(lg, hg, ig), RM.KS(lo, hi, it), hwk),
        Equal.cong(Nat, Bool, n => W.eq_at(RM.KS(lo, hi, it), n, v), AV.LV(lg, hg, ig, v), AV.LV(lo, hi, it, v), gs_lv(lo, hi, it, lg, hg, ig, v, hwk))),
      Equal.sym(Bool, RM.FX(lo, hi, it, v), W.eq_at(RM.KS(lo, hi, it), AV.LV(lo, hi, it, v), v), fx_eqat(it, depth, lo, hi, v, OP.g_ids(dir, lo, hi, depth, it, at, h), OP.g_lohi(dir, lo, hi, depth, it, at, h), OP.g_cap(dir, lo, hi, depth, it, at, h)))))

# ---- arithmetic of the doubling ----

def sub_add_l(+c: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(c, a), Nat.add(c, b)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      sub_add_l(p, a, b)

# up(cap, x) = cap + x for x <= cap = 2^d, computed without addition.
def up_val(+d: Nat, +x: Nat, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hx: {Nat.is_le(x, SC.pow2(d)) == True{} : Bool}) -> {G.up(U.pow2u(d), U32.from_nat(x)) == U32.from_nat(Nat.add(SC.pow2(d), x)) : U32}:
  +p = SC.pow2(d)
  +hd1 = N.lt_trans(d, 1n+d, 32n, N.lt_succ(d), hd)
  +tp = U.pow2u_value(d, hd1)
  +tp2 = U.pow2u_value(1n+d, hd)
  +hx2 = AV2.lt_up(x, d, hx)
  +tx = IX.nat_round(x, 1n+d, N.lt_le(1n+d, 32n, hd), hx2)
  +ti = Equal.trans(Nat, U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x))), Nat.sub(U32.to_nat(U.pow2u(d)), U32.to_nat(U32.from_nat(x))), Nat.sub(p, x),
    U.sub_nat(U.pow2u(d), U32.from_nat(x), L.subst(Nat, z => {Nat.is_le(U32.to_nat(U32.from_nat(x)), z) == True{} : Bool}, p, U32.to_nat(U.pow2u(d)), Equal.sym(Nat, U32.to_nat(U.pow2u(d)), p, tp), L.subst(Nat, z => {Nat.is_le(z, p) == True{} : Bool}, x, U32.to_nat(U32.from_nat(x)), Equal.sym(Nat, U32.to_nat(U32.from_nat(x)), x, tx), hx))),
    Equal.trans(Nat, Nat.sub(U32.to_nat(U.pow2u(d)), U32.to_nat(U32.from_nat(x))), Nat.sub(p, U32.to_nat(U32.from_nat(x))), Nat.sub(p, x),
      Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(U32.from_nat(x))), U32.to_nat(U.pow2u(d)), p, tp),
      Equal.cong(Nat, Nat, z => Nat.sub(p, z), U32.to_nat(U32.from_nat(x)), x, tx)))
  +hspx = H.sub_le(p, x)
  +hsp2 = N.le_trans(Nat.sub(p, x), p, Nat.double(p), hspx, N.double_self_le(p))
  +to = Equal.trans(Nat, U32.to_nat(G.up(U.pow2u(d), U32.from_nat(x))), Nat.sub(U32.to_nat(U.pow2u(1n+d)), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), Nat.add(p, x),
    U.sub_nat(U.pow2u(1n+d), U32.sub(U.pow2u(d), U32.from_nat(x)),
      L.subst(Nat, z => {Nat.is_le(U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x))), z) == True{} : Bool}, Nat.double(p), U32.to_nat(U.pow2u(1n+d)), Equal.sym(Nat, U32.to_nat(U.pow2u(1n+d)), Nat.double(p), tp2),
        L.subst(Nat, z => {Nat.is_le(z, Nat.double(p)) == True{} : Bool}, Nat.sub(p, x), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x))), Equal.sym(Nat, U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x))), Nat.sub(p, x), ti), hsp2))),
    Equal.trans(Nat, Nat.sub(U32.to_nat(U.pow2u(1n+d)), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), Nat.sub(Nat.add(p, p), Nat.sub(p, x)), Nat.add(p, x),
      Equal.trans(Nat, Nat.sub(U32.to_nat(U.pow2u(1n+d)), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), Nat.sub(Nat.double(p), Nat.sub(p, x)), Nat.sub(Nat.add(p, p), Nat.sub(p, x)),
        Equal.trans(Nat, Nat.sub(U32.to_nat(U.pow2u(1n+d)), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), Nat.sub(Nat.double(p), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), Nat.sub(Nat.double(p), Nat.sub(p, x)),
          Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x)))), U32.to_nat(U.pow2u(1n+d)), Nat.double(p), tp2),
          Equal.cong(Nat, Nat, z => Nat.sub(Nat.double(p), z), U32.to_nat(U32.sub(U.pow2u(d), U32.from_nat(x))), Nat.sub(p, x), ti)),
        Equal.cong(Nat, Nat, z => Nat.sub(z, Nat.sub(p, x)), Nat.double(p), Nat.add(p, p), NA.double_self(p))),
      Equal.trans(Nat, Nat.sub(Nat.add(p, p), Nat.sub(p, x)), Nat.add(p, Nat.sub(p, Nat.sub(p, x))), Nat.add(p, x),
        BO.sub_shift(p, p, Nat.sub(p, x), hspx),
        Equal.cong(Nat, Nat, z => Nat.add(p, z), Nat.sub(p, Nat.sub(p, x)), x, SE.sub_sub_cancel(p, x, hx)))))
  +hpx = L.subst(Nat, z => {Nat.is_le(Nat.add(p, x), z) == True{} : Bool}, Nat.add(p, p), Nat.double(p), Equal.sym(Nat, Nat.double(p), Nat.add(p, p), NA.double_self(p)), W.add_mono(p, x, p, hx))
  +tr = IX.nat_round(Nat.add(p, x), 2n+d, N.lt_succ_le(d, 30n, hd), AV2.lt_up(Nat.add(p, x), 1n+d, hpx))
  U.injective(G.up(U.pow2u(d), U32.from_nat(x)), U32.from_nat(Nat.add(p, x)), Equal.trans(Nat, U32.to_nat(G.up(U.pow2u(d), U32.from_nat(x))), Nat.add(p, x), U32.to_nat(U32.from_nat(Nat.add(p, x))), to, Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.add(p, x))), Nat.add(p, x), tr)))

def aleaf(z: Array<U32>) -> Array<Array<U32>>:
  ALeaf{z}

def anode(a: Array<Array<U32>>, b: Array<Array<U32>>) -> Array<Array<U32>>:
  ANode{a, b}

def spare_eq(+d: Nat) -> {G.spare_blks(d) == A2.thaw2(AR.trep(AR.Tree<U32>, d, BK.leaf0())) : Array<Array<U32>>}:
  match d:
    case 0n:
      Equal.cong(Array<U32>, Array<Array<U32>>, z => aleaf(z), G.zeros(0n), AR.thaw(U32, BK.leaf0()), AS2.zeros0())
    case 1n+p:
      Equal.trans(Array<Array<U32>>, anode(G.spare_blks(p), G.spare_blks(p)), anode(A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0())), G.spare_blks(p)), anode(A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0())), A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0()))),
        Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => anode(z, G.spare_blks(p)), G.spare_blks(p), A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0())), spare_eq(p)),
        Equal.cong(Array<Array<U32>>, Array<Array<U32>>, z => anode(A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0())), z), G.spare_blks(p), A2.thaw2(AR.trep(AR.Tree<U32>, p, BK.leaf0())), spare_eq(p)))

def zeros_eq(+d: Nat) -> {G.zeros(d) == AR.thaw(U32, AR.trep(U32, d, 0)) : Array<U32>}:
  AR.new(U32, d, 0)

# ---- windows of a doubled table ----

def drop_app_add(-T: Data, +zs: List<&2, T>, +xs: List<&2, T>, +n: Nat) -> {SC.drop(T, SC.append(T, zs, xs), Nat.add(SC.length(T, zs), n)) == SC.drop(T, xs, n) : List<&2, T>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      drop_app_add(T, t, xs, n)

def drop_app_le(-T: Data, +xs: List<&2, T>, +zs: List<&2, T>, +n: Nat, +h: {Nat.is_le(n, SC.length(T, xs)) == True{} : Bool}) -> {SC.drop(T, SC.append(T, xs, zs), n) == SC.append(T, SC.drop(T, xs, n), zs) : List<&2, T>}:
  match xs n:
    case Nil{} 0n:
      ZP.drop0(T, zs)
    case Nil{} 1n+p:
      Empty.absurd({SC.drop(T, zs, 1n+p) == SC.append(T, SC.drop(T, Nil{}, 1n+p), zs) : List<&2, T>}, L.false_true(h))
    case Con{+hh, +t} 0n:
      {==}
    case Con{+hh, +t} 1n+p:
      drop_app_le(T, t, zs, p, h)

def win_gl(-T: Data, +d: Nat, +zt: AR.Tree<T>, +xs: List<&2, T>, +lo: Nat, +n: Nat, +pz: {AR.perfect(T, d, zt) == True{} : Bool}) -> {SC.take(T, SC.drop(T, SC.append(T, AR.slots(T, zt), xs), Nat.add(SC.pow2(d), lo)), n) == SC.take(T, SC.drop(T, xs, lo), n) : List<&2, T>}:
  Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, n), SC.drop(T, SC.append(T, AR.slots(T, zt), xs), Nat.add(SC.pow2(d), lo)), SC.drop(T, xs, lo),
    L.subst(Nat, m => {SC.drop(T, SC.append(T, AR.slots(T, zt), xs), Nat.add(m, lo)) == SC.drop(T, xs, lo) : List<&2, T>}, SC.length(T, AR.slots(T, zt)), SC.pow2(d), AR.slots_length(T, d, zt, pz), drop_app_add(T, AR.slots(T, zt), xs, lo)))

def win_gr(-T: Data, +xs: List<&2, T>, +zs: List<&2, T>, +lo: Nat, +k: Nat, +hk: {Nat.is_le(Nat.add(lo, k), SC.length(T, xs)) == True{} : Bool}) -> {SC.take(T, SC.drop(T, SC.append(T, xs, zs), lo), k) == SC.take(T, SC.drop(T, xs, lo), k) : List<&2, T>}:
  +hlo = N.le_trans(lo, Nat.add(lo, k), SC.length(T, xs), N.le_add_right(lo, k), hk)
  +hkd = ZP.le_cancel(lo, k, SC.length(T, SC.drop(T, xs, lo)), L.subst(Nat, z => {Nat.is_le(Nat.add(lo, k), z) == True{} : Bool}, SC.length(T, xs), Nat.add(lo, SC.length(T, SC.drop(T, xs, lo))), Equal.sym(Nat, Nat.add(lo, SC.length(T, SC.drop(T, xs, lo))), SC.length(T, xs), ZP.len_split(T, xs, lo, hlo)), hk))
  Equal.trans(List<&2, T>, SC.take(T, SC.drop(T, SC.append(T, xs, zs), lo), k), SC.take(T, SC.append(T, SC.drop(T, xs, lo), zs), k), SC.take(T, SC.drop(T, xs, lo), k),
    Equal.cong(List<&2, T>, List<&2, T>, z => SC.take(T, z, k), SC.drop(T, SC.append(T, xs, zs), lo), SC.append(T, SC.drop(T, xs, lo), zs), drop_app_le(T, xs, zs, lo, hlo)),
    LL.sc_take_append_left(T, SC.drop(T, xs, lo), zs, k, hkd))

# ---- insertion by shifting left, for any window starting at 1 or later ----

def av_left_gen(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +hpos: {Nat.is_le(1n, lo) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_left(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  match lo:
    case 0n:
      Empty.absurd(UC.UCore(ST.Sh{dir, 0n, hi, depth, it, at}, G.av_left(dir, U32.from_nat(0n), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(0n, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(0n, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n), L.false_true(hpos))
    case 1n+lo1:
      AV2.av_left_core(dir, lo1, hi, depth, it, at, v, h, hv0)

# ---- doubling ----

def ZT(+d: Nat) -> AR.Tree<U32>:
  AR.trep(U32, d, 0)

def STR(+d: Nat) -> AR.Tree<AR.Tree<U32>>:
  AR.trep(AR.Tree<U32>, d, BK.leaf0())

def AVLG(+dir: Bool, +a: U32, +b: U32, +d: Nat, z: Array<U32>, s: Array<Array<U32>>, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  G.av_left(dir, a, b, U.pow2u(1n+d), 1n+d, ANode{z, ids}, ANode{s, adj}, i, v)

def AVRG(+dir: Bool, +lo: Nat, +hi: Nat, +d: Nat, z: Array<U32>, s: Array<Array<U32>>, ids: Array<U32>, adj: Array<Array<U32>>, +i: U32, +v: U32) -> G.Graph & Result<&2, &2, E.Error, Unit>:
  G.av_right(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(1n+d), 1n+d, ANode{ids, z}, ANode{adj, s}, i, v)

def grow_left_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +hdg: {Nat.is_le(1n+depth, 31n) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_grow_left(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  +p = SC.pow2(depth)
  +lg = Nat.add(p, lo)
  +hg = Nat.add(p, hi)
  +k = Nat.sub(hi, lo)
  +l = AV.LV(lo, hi, it, v)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, lo, hi, depth, it, at, h)
  +pfa = OP.g_adj(dir, lo, hi, depth, it, at, h)
  +hd1 = N.le_lt_trans(1n+depth, 31n, 32n, hdg, N.lt_succ(31n))
  +hk = sub_add_l(p, hi, lo)
  +hwk = Equal.trans(List<&2, U32>, RM.KS(lg, hg, AR.TNode{ZT(depth), it}), SC.take(U32, SC.drop(U32, SC.append(U32, AR.slots(U32, ZT(depth)), AR.slots(U32, it)), lg), k), RM.KS(lo, hi, it),
    Equal.cong(Nat, List<&2, U32>, n => SC.take(U32, SC.drop(U32, SC.append(U32, AR.slots(U32, ZT(depth)), AR.slots(U32, it)), lg), n), Nat.sub(hg, lg), k, hk),
    win_gl(U32, depth, ZT(depth), AR.slots(U32, it), lo, k, AR.trep_perfect(U32, depth, 0)))
  +hwb = Equal.trans(List<&2, AR.Tree<U32>>, RM.BW(lg, hg, AR.TNode{STR(depth), at}), SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, STR(depth)), AR.slots(AR.Tree<U32>, at)), lg), k), RM.BW(lo, hi, at),
    Equal.cong(Nat, List<&2, AR.Tree<U32>>, n => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, SC.append(AR.Tree<U32>, AR.slots(AR.Tree<U32>, STR(depth)), AR.slots(AR.Tree<U32>, at)), lg), n), Nat.sub(hg, lg), k, hk),
    win_gl(AR.Tree<U32>, depth, STR(depth), AR.slots(AR.Tree<U32>, at), lo, k, AR.trep_perfect(AR.Tree<U32>, depth, BK.leaf0())))
  +hpi = L.and_intro(AR.perfect(U32, depth, ZT(depth)), AR.perfect(U32, depth, it), AR.trep_perfect(U32, depth, 0), pfi)
  +hpa = L.and_intro(AR.perfect(AR.Tree<U32>, depth, STR(depth)), AR.perfect(AR.Tree<U32>, depth, at), AR.trep_perfect(AR.Tree<U32>, depth, BK.leaf0()), pfa)
  +hlog = W.add_mono(p, lo, hi, hlo)
  +hcapg = L.subst(Nat, z => {Nat.is_le(hg, z) == True{} : Bool}, Nat.add(p, p), Nat.double(p), Equal.sym(Nat, Nat.double(p), Nat.add(p, p), NA.double_self(p)), W.add_mono(p, hi, p, hcap))
  +goodg = gs_good(dir, lo, hi, depth, it, at, h, lg, hg, 1n+depth, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}, hdg, hpi, hpa, hlog, hcapg, hwk, hwb)
  +hv0g = Equal.trans(Bool, RM.FX(lg, hg, AR.TNode{ZT(depth), it}, v), RM.FX(lo, hi, it, v), False{}, gs_fx(dir, lo, hi, depth, it, at, h, lg, hg, 1n+depth, AR.TNode{ZT(depth), it}, v, hpi, hlog, hcapg, hwk), hv0)
  +hpos = N.le_trans(1n, p, lg, N.pow2_pos(depth), N.le_add_right(p, lo))
  +hil = N.le_trans(Nat.add(lo, l), hi, p, L.subst(Nat, z => {Nat.is_le(Nat.add(lo, l), z) == True{} : Bool}, Nat.add(lo, k), hi, W.window_end(lo, hi, k, {==}, hlo), W.add_mono(lo, l, k, AV.av_hl(lo, hi, it, v))), hcap)
  +eix = Equal.trans(U32, G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), U32.from_nat(Nat.add(p, Nat.add(lo, l))), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v),
    up_val(depth, Nat.add(lo, l), hd1, hil),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.add(p, Nat.add(lo, l)), Nat.add(lg, AV.LV(lg, hg, AR.TNode{ZT(depth), it}, v)),
      Equal.trans(Nat, Nat.add(p, Nat.add(lo, l)), Nat.add(lg, l), Nat.add(lg, AV.LV(lg, hg, AR.TNode{ZT(depth), it}, v)),
        Equal.sym(Nat, Nat.add(lg, l), Nat.add(p, Nat.add(lo, l)), N.add_assoc(p, lo, l)),
        Equal.cong(Nat, Nat, z => Nat.add(lg, z), l, AV.LV(lg, hg, AR.TNode{ZT(depth), it}, v), Equal.sym(Nat, AV.LV(lg, hg, AR.TNode{ZT(depth), it}, v), l, gs_lv(lo, hi, it, lg, hg, AR.TNode{ZT(depth), it}, v, hwk))))))
  +ert = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVLG(dir, G.up(U.pow2u(depth), U32.from_nat(lo)), G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v),
    Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVLG(dir, z, G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), G.up(U.pow2u(depth), U32.from_nat(lo)), U32.from_nat(lg), up_val(depth, lo, hd1, N.le_trans(lo, hi, p, hlo, hcap))),
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVLG(dir, U32.from_nat(lg), G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v),
      Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVLG(dir, U32.from_nat(lg), z, depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), G.up(U.pow2u(depth), U32.from_nat(hi)), U32.from_nat(hg), up_val(depth, hi, hd1, hcap)),
      Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v),
        Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, z, G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), G.zeros(depth), AR.thaw(U32, ZT(depth)), zeros_eq(depth)),
        Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v),
          Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), z, AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), G.spare_blks(depth), A2.thaw2(STR(depth)), spare_eq(depth)),
          Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), z, v), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), eix)))))
  UC.uc_conv(ST.Sh{dir, lo, hi, depth, it, at}, ST.Sh{dir, lg, hg, 1n+depth, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}}, AVLG(dir, G.up(U.pow2u(depth), U32.from_nat(lo)), G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v),
    (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lg, hg, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}))}, E.OUnit{Done{Unit{}}}), 1n,
    gs_mu(dir, lo, hi, depth, it, at, lg, hg, 1n+depth, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}, hk, hwb),
    Equal.sym(G.Graph & Result<&2, &2, E.Error, Unit>, AVLG(dir, G.up(U.pow2u(depth), U32.from_nat(lo)), G.up(U.pow2u(depth), U32.from_nat(hi)), depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), G.up(U.pow2u(depth), RM.IX(lo, hi, it, v)), v), AVLG(dir, U32.from_nat(lg), U32.from_nat(hg), depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lg, hg, AR.TNode{ZT(depth), it}, v), v), ert),
    Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(dir, GS.put(v, Nil{}, z)), RM.AM(lg, hg, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}), RM.AM(lo, hi, it, at), gs_am(lo, hi, it, at, lg, hg, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}, hwk, hwb)),
    av_left_gen(dir, lg, hg, 1n+depth, AR.TNode{ZT(depth), it}, AR.TNode{STR(depth), at}, v, goodg, hv0g, hpos))

def grow_right_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +hdg: {Nat.is_le(1n+depth, 31n) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_grow_right(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  +p = SC.pow2(depth)
  +k = Nat.sub(hi, lo)
  +l = AV.LV(lo, hi, it, v)
  +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
  +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
  +pfi = OP.g_ids(dir, lo, hi, depth, it, at, h)
  +pfa = OP.g_adj(dir, lo, hi, depth, it, at, h)
  +hwk = win_gr(U32, AR.slots(U32, it), AR.slots(U32, ZT(depth)), lo, k, ED.win_fits(U32, depth, it, lo, hi, pfi, hlo, hcap))
  +hwb = win_gr(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), AR.slots(AR.Tree<U32>, STR(depth)), lo, k, ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, pfa, hlo, hcap))
  +hpi = L.and_intro(AR.perfect(U32, depth, it), AR.perfect(U32, depth, ZT(depth)), pfi, AR.trep_perfect(U32, depth, 0))
  +hpa = L.and_intro(AR.perfect(AR.Tree<U32>, depth, at), AR.perfect(AR.Tree<U32>, depth, STR(depth)), pfa, AR.trep_perfect(AR.Tree<U32>, depth, BK.leaf0()))
  +hcapg = N.le_trans(hi, p, Nat.double(p), hcap, N.double_self_le(p))
  +goodg = gs_good(dir, lo, hi, depth, it, at, h, lo, hi, 1n+depth, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}, hdg, hpi, hpa, hlo, hcapg, hwk, hwb)
  +hv0g = Equal.trans(Bool, RM.FX(lo, hi, AR.TNode{it, ZT(depth)}, v), RM.FX(lo, hi, it, v), False{}, gs_fx(dir, lo, hi, depth, it, at, h, lo, hi, 1n+depth, AR.TNode{it, ZT(depth)}, v, hpi, hlo, hcapg, hwk), hv0)
  +hrg = N.le_lt_trans(hi, p, Nat.double(p), hcap, N.pow2_lt_succ(depth))
  +eix = Equal.cong(Nat, U32, z => U32.from_nat(Nat.add(lo, z)), l, AV.LV(lo, hi, AR.TNode{it, ZT(depth)}, v), Equal.sym(Nat, AV.LV(lo, hi, AR.TNode{it, ZT(depth)}, v), l, gs_lv(lo, hi, it, lo, hi, AR.TNode{it, ZT(depth)}, v, hwk)))
  +ert = Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVRG(dir, lo, hi, depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, AR.TNode{it, ZT(depth)}, v), v),
    Equal.cong(Array<U32>, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVRG(dir, lo, hi, depth, z, G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), G.zeros(depth), AR.thaw(U32, ZT(depth)), zeros_eq(depth)),
    Equal.trans(G.Graph & Result<&2, &2, E.Error, Unit>, AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, AR.TNode{it, ZT(depth)}, v), v),
      Equal.cong(Array<Array<U32>>, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), z, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), G.spare_blks(depth), A2.thaw2(STR(depth)), spare_eq(depth)),
      Equal.cong(U32, G.Graph & Result<&2, &2, E.Error, Unit>, z => AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), z, v), RM.IX(lo, hi, it, v), RM.IX(lo, hi, AR.TNode{it, ZT(depth)}, v), eix)))
  UC.uc_conv(ST.Sh{dir, lo, hi, depth, it, at}, ST.Sh{dir, lo, hi, 1n+depth, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}}, AVRG(dir, lo, hi, depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, AR.TNode{it, ZT(depth)}, v), v),
    (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}))}, E.OUnit{Done{Unit{}}}), 1n,
    gs_mu(dir, lo, hi, depth, it, at, lo, hi, 1n+depth, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}, {==}, hwb),
    Equal.sym(G.Graph & Result<&2, &2, E.Error, Unit>, AVRG(dir, lo, hi, depth, G.zeros(depth), G.spare_blks(depth), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v), AVRG(dir, lo, hi, depth, AR.thaw(U32, ZT(depth)), A2.thaw2(STR(depth)), AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, AR.TNode{it, ZT(depth)}, v), v), ert),
    Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(dir, GS.put(v, Nil{}, z)), RM.AM(lo, hi, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}), RM.AM(lo, hi, it, at), gs_am(lo, hi, it, at, lo, hi, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}, hwk, hwb)),
    AV2.av_right_core(dir, lo, hi, 1n+depth, AR.TNode{it, ZT(depth)}, AR.TNode{at, STR(depth)}, v, goodg, hv0g, hrg))

# ---- the flags of av_ins ----

def lt0_false(+n: Nat, +h: {Nat.is_lt(0n, n) == False{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, L.false_true(Equal.sym(Bool, Nat.is_lt(0n, 1n+p), False{}, h)))

def lroom_nat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, b: Bool, +e: {U32.is_lt(0, U32.from_nat(lo)) == b : Bool}) -> {Nat.is_lt(0n, lo) == b : Bool}:
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +rl = IX.nat_round(lo, 1n+depth, OP.g_depth(dir, lo, hi, depth, it, at, h), AV2.lt_up(lo, depth, N.le_trans(lo, hi, SC.pow2(depth), OP.g_lohi(dir, lo, hi, depth, it, at, h), OP.g_cap(dir, lo, hi, depth, it, at, h))))
  Equal.trans(Bool, Nat.is_lt(0n, lo), U32.is_lt(0, U32.from_nat(lo)), b,
    Equal.sym(Bool, U32.is_lt(0, U32.from_nat(lo)), Nat.is_lt(0n, lo), Equal.trans(Bool, U32.is_lt(0, U32.from_nat(lo)), Nat.is_lt(0n, U32.to_nat(U32.from_nat(lo))), Nat.is_lt(0n, lo), U.is_lt_nat(0, U32.from_nat(lo)), Equal.cong(Nat, Bool, z => Nat.is_lt(0n, z), U32.to_nat(U32.from_nat(lo)), lo, rl))),
    e)

def rroom_nat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, b: Bool, +e: {U32.is_lt(U32.from_nat(hi), U.pow2u(depth)) == b : Bool}) -> {Nat.is_lt(hi, SC.pow2(depth)) == b : Bool}:
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +rh = IX.nat_round(hi, 1n+depth, OP.g_depth(dir, lo, hi, depth, it, at, h), AV2.lt_up(hi, depth, OP.g_cap(dir, lo, hi, depth, it, at, h)))
  +e1 = Equal.trans(Bool, U32.is_lt(U32.from_nat(hi), U.pow2u(depth)), Nat.is_lt(U32.to_nat(U32.from_nat(hi)), U32.to_nat(U.pow2u(depth))), Nat.is_lt(hi, SC.pow2(depth)), U.is_lt_nat(U32.from_nat(hi), U.pow2u(depth)),
    Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.from_nat(hi)), U32.to_nat(U.pow2u(depth))), Nat.is_lt(hi, U32.to_nat(U.pow2u(depth))), Nat.is_lt(hi, SC.pow2(depth)),
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, U32.to_nat(U.pow2u(depth))), U32.to_nat(U32.from_nat(hi)), hi, rh),
      Equal.cong(Nat, Bool, z => Nat.is_lt(hi, z), U32.to_nat(U.pow2u(depth)), SC.pow2(depth), U.pow2u_value(depth, hd))))
  Equal.trans(Bool, Nat.is_lt(hi, SC.pow2(depth)), U32.is_lt(U32.from_nat(hi), U.pow2u(depth)), b, Equal.sym(Bool, U32.is_lt(U32.from_nat(hi), U.pow2u(depth)), Nat.is_lt(hi, SC.pow2(depth)), e1), e)

# A full table (lo = 0, hi = 2^depth) under the room premise can double.
def full_room(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, +elo: {lo == 0n : Nat}, +ehi: {Nat.is_le(SC.pow2(depth), hi) == True{} : Bool}) -> {Nat.is_le(1n+depth, 31n) == True{} : Bool}:
  +mu = GT.mu(ST.Sh{dir, lo, hi, depth, it, at})
  +hk = L.subst(Nat, z => {Nat.is_le(SC.pow2(depth), Nat.sub(hi, z)) == True{} : Bool}, 0n, lo, Equal.sym(Nat, lo, 0n, elo), L.subst(Nat, z => {Nat.is_le(SC.pow2(depth), z) == True{} : Bool}, hi, Nat.sub(hi, 0n), Equal.sym(Nat, Nat.sub(hi, 0n), hi, N.sub_zero(hi)), ehi))
  +hmu = N.le_trans(SC.pow2(depth), Nat.sub(hi, lo), mu, hk, N.le_add_right(Nat.sub(hi, lo), GT.mdeg(RM.BW(lo, hi, at))))
  +h3 = L.subst(Nat, z => {Nat.is_le(mu, z) == True{} : Bool}, Nat.add(mu, 3n), Nat.add(3n, mu), N.add_comm(mu, 3n), N.le_add_right(mu, 3n))
  +hp = N.le_lt_trans(SC.pow2(depth), mu, SC.pow2(q), hmu, N.le_lt_trans(mu, Nat.add(3n, mu), SC.pow2(q), h3, hroom))
  +hdq = AE.pow2_inv(depth, q, hp)
  N.le_trans(1n+depth, 30n, 31n, N.le_trans(1n+depth, q, 30n, N.lt_succ_le_succ(depth, q, hdq), hq), N.le_succ(30n))

def av_side_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, left: Bool, lroom: Bool, +elr: {U32.is_lt(0, U32.from_nat(lo)) == lroom : Bool}, rroom: Bool, +err: {U32.is_lt(U32.from_nat(hi), U.pow2u(depth)) == rroom : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_side(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, left, lroom, rroom), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  match left lroom rroom:
    case True{} True{} r0:
      av_left_gen(dir, lo, hi, depth, it, at, v, h, hv0, N.lt_succ_le_succ(0n, lo, lroom_nat(dir, lo, hi, depth, it, at, h, True{}, elr)))
    case True{} False{} True{}:
      AV2.av_right_core(dir, lo, hi, depth, it, at, v, h, hv0, rroom_nat(dir, lo, hi, depth, it, at, h, True{}, err))
    case True{} False{} False{}:
      grow_left_core(dir, lo, hi, depth, it, at, v, h, hv0, full_room(dir, lo, hi, depth, it, at, h, q, hq, hroom, lt0_false(lo, lroom_nat(dir, lo, hi, depth, it, at, h, False{}, elr)), N.not_lt_le(hi, SC.pow2(depth), rroom_nat(dir, lo, hi, depth, it, at, h, False{}, err))))
    case False{} True{} True{}:
      AV2.av_right_core(dir, lo, hi, depth, it, at, v, h, hv0, rroom_nat(dir, lo, hi, depth, it, at, h, True{}, err))
    case False{} False{} True{}:
      AV2.av_right_core(dir, lo, hi, depth, it, at, v, h, hv0, rroom_nat(dir, lo, hi, depth, it, at, h, True{}, err))
    case False{} True{} False{}:
      av_left_gen(dir, lo, hi, depth, it, at, v, h, hv0, N.lt_succ_le_succ(0n, lo, lroom_nat(dir, lo, hi, depth, it, at, h, True{}, elr)))
    case False{} False{} False{}:
      grow_right_core(dir, lo, hi, depth, it, at, v, h, hv0, full_room(dir, lo, hi, depth, it, at, h, q, hq, hroom, lt0_false(lo, lroom_nat(dir, lo, hi, depth, it, at, h, False{}, elr)), N.not_lt_le(hi, SC.pow2(depth), rroom_nat(dir, lo, hi, depth, it, at, h, False{}, err))))

def av_case1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}, found: Bool, +ef: {RM.FX(lo, hi, it, v) == found : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, found), GS.add_vertex_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, found, RM.SX(dir, lo, hi, depth, it, at, v)), dir, RM.AM(lo, hi, it, at), v), 1n):
  match found:
    case True{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.av_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, True{}), GS.add_vertex_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, True{}, RM.SX(dir, lo, hi, depth, it, at, v)), dir, RM.AM(lo, hi, it, at), v), 1n, E.VertexExists{}, {==}, {==})
    case False{}:
      av_side_case(dir, lo, hi, depth, it, at, v, h, ef, q, hq, hroom, U32.is_lt(U32.sub(RM.IX(lo, hi, it, v), U32.from_nat(lo)), U32.sub(U32.from_nat(hi), RM.IX(lo, hi, it, v))), U32.is_lt(0, U32.from_nat(lo)), {==}, U32.is_lt(U32.from_nat(hi), U.pow2u(depth)), {==})

def av_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.add_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddVertex{v}), 1n):
  L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), v, z), GS.add_vertex_at(GS.find(v, RM.AM(lo, hi, it, at)), dir, RM.AM(lo, hi, it, at), v), 1n),
    G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
    Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)),
    L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.av_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, RM.FX(lo, hi, it, v)), GS.add_vertex_at(m, dir, RM.AM(lo, hi, it, at), v), 1n),
      LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), GS.find(v, RM.AM(lo, hi, it, at)),
      Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), ED.gfind(dir, lo, hi, depth, it, at, v, h)),
      av_case1(dir, lo, hi, depth, it, at, v, h, q, hq, hroom, RM.FX(lo, hi, it, v), {==})))

# add_vertex refines the specification, preserves the invariant and raises the measure by at most one.
def so_add_vertex(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +q: Nat, +hq: {Nat.is_le(q, 30n) == True{} : Bool}, +hroom: {Nat.is_lt(Nat.add(3n, GT.mu(ST.Sh{dir, lo, hi, depth, it, at})), SC.pow2(q)) == True{} : Bool}) -> GT.StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.AddVertex{v}):
  UC.uc_step(ST.Sh{dir, lo, hi, depth, it, at}, E.AddVertex{v}, G.add_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), av_core(dir, lo, hi, depth, it, at, v, h, q, hq, hroom), {==})
