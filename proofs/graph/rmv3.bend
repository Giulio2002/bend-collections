import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../binary_heap/u32idx.bend as IX
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./window.bend as W
import ./search.bend as SE
import ./ops.bend as OP
import ./blk.bend as BK
import ./edge.bend as ED
import ./shift.bend as SH
import ./blkops.bend as BO
import ./gstep.bend as GT
import ./zip.bend as ZP
import ./ashift.bend as AS2
import ./rmedge.bend as RM
import ./ucore.bend as UC
import ./addv1.bend as AV
import ./nbrops.bend as NO
import ./addv1.bend as AV
import ./rmv1.bend as RV
import ./rmv2.bend as RV2
import ./edges.bend as EG
import ./lb.bend as LB

# remove_vertex, part 3: the strip loop removes v from every block of the
# window, against its mirror tree and its list-level effect.

def sd_tree(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +idx: Nat, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  match k:
    case 0n:
      t
    case 1n+m:
      sd_tree(m, d, AR.upd(AR.Tree<U32>, d, t, idx, RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), idx))), 1n+idx, v)

def lsd(k: Nat, +xs: List<&2, AR.Tree<U32>>, +idx: Nat, +v: U32) -> List<&2, AR.Tree<U32>>:
  match k:
    case 0n:
      xs
    case 1n+m:
      lsd(m, SC.update(AR.Tree<U32>, xs, idx, RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), xs, idx))), 1n+idx, v)

def sd_perfect(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +idx: Nat, +v: U32, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}) -> {AR.perfect(AR.Tree<U32>, d, sd_tree(k, d, t, idx, v)) == True{} : Bool}:
  match k:
    case 0n:
      pf
    case 1n+m:
      +b = RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), idx))
      sd_perfect(m, d, AR.upd(AR.Tree<U32>, d, t, idx, b), 1n+idx, v, AR.upd_perfect(AR.Tree<U32>, d, t, idx, b, pf))

def sd_slots(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +idx: Nat, +v: U32, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(idx, k), SC.pow2(d)) == True{} : Bool}) -> {AR.slots(AR.Tree<U32>, sd_tree(k, d, t, idx, v)) == lsd(k, AR.slots(AR.Tree<U32>, t), idx, v) : List<&2, AR.Tree<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +b = RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), AR.slots(AR.Tree<U32>, t), idx))
      +hi = N.lt_le_trans(idx, Nat.add(idx, 1n+m), SC.pow2(d), L.subst(Nat, z => {Nat.is_lt(idx, z) == True{} : Bool}, 1n+Nat.add(idx, m), Nat.add(idx, 1n+m), Equal.sym(Nat, Nat.add(idx, 1n+m), 1n+Nat.add(idx, m), N.add_succ(idx, m)), N.le_lt_trans(idx, Nat.add(idx, m), 1n+Nat.add(idx, m), N.le_add_right(idx, m), N.lt_succ(Nat.add(idx, m)))), hk)
      +ih = sd_slots(m, d, AR.upd(AR.Tree<U32>, d, t, idx, b), 1n+idx, v, AR.upd_perfect(AR.Tree<U32>, d, t, idx, b, pf), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(idx, 1n+m), Nat.add(1n+idx, m), SH.add_shift(idx, m), hk))
      Equal.trans(List<&2, AR.Tree<U32>>, AR.slots(AR.Tree<U32>, sd_tree(m, d, AR.upd(AR.Tree<U32>, d, t, idx, b), 1n+idx, v)), lsd(m, AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t, idx, b)), 1n+idx, v), lsd(m, SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), idx, b), 1n+idx, v),
        ih, Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => lsd(m, z, 1n+idx, v), AR.slots(AR.Tree<U32>, AR.upd(AR.Tree<U32>, d, t, idx, b)), SC.update(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), idx, b), AR.upd_slots(AR.Tree<U32>, d, t, idx, b, hi, pf)))

def sd_run(+k: Nat, +d: Nat, +t: AR.Tree<AR.Tree<U32>>, +idx: Nat, +v: U32, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(AR.Tree<U32>, d, t) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(idx, k), SC.pow2(d)) == True{} : Bool}, +hbl: {ST.blocks_ok(SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t), idx), k)) == True{} : Bool}) -> {G.sd_loop(k, v, U32.from_nat(idx), A2.thaw2(t)) == A2.thaw2(sd_tree(k, d, t, idx, v)) : Array<Array<U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      +xs = AR.slots(AR.Tree<U32>, t)
      +bt = ZP.vget(AR.Tree<U32>, BK.leaf0(), xs, idx)
      +b = RV.ds(v, bt)
      +t1 = AR.upd(AR.Tree<U32>, d, t, idx, b)
      +hi = N.lt_le_trans(idx, Nat.add(idx, 1n+m), SC.pow2(d), L.subst(Nat, z => {Nat.is_lt(idx, z) == True{} : Bool}, 1n+Nat.add(idx, m), Nat.add(idx, 1n+m), Equal.sym(Nat, Nat.add(idx, 1n+m), 1n+Nat.add(idx, m), N.add_succ(idx, m)), N.le_lt_trans(idx, Nat.add(idx, m), 1n+Nat.add(idx, m), N.le_add_right(idx, m), N.lt_succ(Nat.add(idx, m)))), hk)
      +ri = IX.nat_round(idx, d, N.lt_le(d, 32n, hd), hi)
      +hlen = AR.len_lt(AR.Tree<U32>, d, t, idx, pf, hi)
      +et = Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, z, 1n+m), SC.drop(AR.Tree<U32>, xs, idx), Con{bt, SC.drop(AR.Tree<U32>, xs, 1n+idx)}, ZP.drop_cons_g(AR.Tree<U32>, xs, idx, BK.leaf0(), hlen))
      +hb2 = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, xs, idx), 1n+m), Con{bt, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, xs, 1n+idx), m)}, et, hbl)
      +bk = L.and_left(ST.blk_ok(bt), ST.blocks_ok(SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, xs, 1n+idx), m)), hb2)
      +hrest = L.and_right(ST.blk_ok(bt), ST.blocks_ok(SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, xs, 1n+idx), m)), hb2)
      +hx = L.subst(Nat, z => {SC.nth(AR.Tree<U32>, xs, z) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, idx, U32.to_nat(U32.from_nat(idx)), Equal.sym(Nat, U32.to_nat(U32.from_nat(idx)), idx, ri), AS2.tsat(AR.Tree<U32>, d, t, idx, BK.leaf0(), pf, hi))
      +edn = NO.del_nbr_ok(d, t, U32.from_nat(idx), bt, v, hd, L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(d)) == True{} : Bool}, idx, U32.to_nat(U32.from_nat(idx)), Equal.sym(Nat, U32.to_nat(U32.from_nat(idx)), idx, ri), hi), hx, pf, bk)
      +es1 = Equal.trans(List<&2, AR.Tree<U32>>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t1), 1n+idx), SC.drop(AR.Tree<U32>, SC.update(AR.Tree<U32>, xs, idx, b), 1n+idx), SC.drop(AR.Tree<U32>, xs, 1n+idx),
        Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.drop(AR.Tree<U32>, z, 1n+idx), AR.slots(AR.Tree<U32>, t1), SC.update(AR.Tree<U32>, xs, idx, b), AR.upd_slots(AR.Tree<U32>, d, t, idx, b, hi, pf)),
        ZP.drop_upd_lt(AR.Tree<U32>, xs, idx, b, 1n+idx, N.lt_succ(idx)))
      +hbl1 = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(SC.take(AR.Tree<U32>, z, m)) == True{} : Bool}, SC.drop(AR.Tree<U32>, xs, 1n+idx), SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t1), 1n+idx), Equal.sym(List<&2, AR.Tree<U32>>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, t1), 1n+idx), SC.drop(AR.Tree<U32>, xs, 1n+idx), es1), hrest)
      +ih = sd_run(m, d, t1, 1n+idx, v, hd, AR.upd_perfect(AR.Tree<U32>, d, t, idx, b, pf), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(idx, 1n+m), Nat.add(1n+idx, m), SH.add_shift(idx, m), hk), hbl1)
      Equal.trans(Array<Array<U32>>, G.sd_loop(m, v, U32.from_nat(1n+idx), G.del_nbr_fin(G.del_nbr(A2.thaw2(t), U32.from_nat(idx), v))), G.sd_loop(m, v, U32.from_nat(1n+idx), A2.thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(U32.from_nat(idx)), b))), A2.thaw2(sd_tree(m, d, t1, 1n+idx, v)),
        Equal.cong(G.Upd, Array<Array<U32>>, z => G.sd_loop(m, v, U32.from_nat(1n+idx), G.del_nbr_fin(z)), G.del_nbr(A2.thaw2(t), U32.from_nat(idx), v), G.UP{A2.thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(U32.from_nat(idx)), b)), NO.fnd(bt, v)}, edn),
        Equal.trans(Array<Array<U32>>, G.sd_loop(m, v, U32.from_nat(1n+idx), A2.thaw2(AR.upd(AR.Tree<U32>, d, t, U32.to_nat(U32.from_nat(idx)), b))), G.sd_loop(m, v, U32.from_nat(1n+idx), A2.thaw2(t1)), A2.thaw2(sd_tree(m, d, t1, 1n+idx, v)),
          Equal.cong(Nat, Array<Array<U32>>, z => G.sd_loop(m, v, U32.from_nat(1n+idx), A2.thaw2(AR.upd(AR.Tree<U32>, d, t, z, b))), U32.to_nat(U32.from_nat(idx)), idx, ri),
          ih))

# Stripping a window of blocks W between a prefix P and a suffix R.
def lsd_zip(+v: U32, +w: List<&2, AR.Tree<U32>>, +p: List<&2, AR.Tree<U32>>, +r: List<&2, AR.Tree<U32>>) -> {lsd(SC.length(AR.Tree<U32>, w), SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, w, r)), SC.length(AR.Tree<U32>, p), v) == SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, RV.dsl(v, w), r)) : List<&2, AR.Tree<U32>>}:
  match w:
    case Nil{}:
      {==}
    case Con{+b, +wt}:
      +x = SC.append(AR.Tree<U32>, p, Con{b, SC.append(AR.Tree<U32>, wt, r)})
      +p1 = SC.snoc(AR.Tree<U32>, p, RV.ds(v, b))
      +x1 = SC.append(AR.Tree<U32>, p1, SC.append(AR.Tree<U32>, wt, r))
      +e1 = Equal.trans(List<&2, AR.Tree<U32>>, SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), x, SC.length(AR.Tree<U32>, p)))), SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, b)), x1,
        Equal.cong(Maybe<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, mb => SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, L.some_value(AR.Tree<U32>, mb, BK.leaf0()))), SC.nth(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p)), Some{b}, ZP.nth0(AR.Tree<U32>, p, b, SC.append(AR.Tree<U32>, wt, r))),
        Equal.trans(List<&2, AR.Tree<U32>>, SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, b)), SC.append(AR.Tree<U32>, p, Con{RV.ds(v, b), SC.append(AR.Tree<U32>, wt, r)}), x1,
          ZP.upd0(AR.Tree<U32>, p, b, SC.append(AR.Tree<U32>, wt, r), RV.ds(v, b)),
          Equal.sym(List<&2, AR.Tree<U32>>, x1, SC.append(AR.Tree<U32>, p, Con{RV.ds(v, b), SC.append(AR.Tree<U32>, wt, r)}), LL.snoc_append_cons(AR.Tree<U32>, p, RV.ds(v, b), SC.append(AR.Tree<U32>, wt, r)))))
      +ih = L.subst(Nat, n => {lsd(SC.length(AR.Tree<U32>, wt), x1, n, v) == SC.append(AR.Tree<U32>, p1, SC.append(AR.Tree<U32>, RV.dsl(v, wt), r)) : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, p1), 1n+SC.length(AR.Tree<U32>, p), LL.length_snoc(AR.Tree<U32>, p, RV.ds(v, b)), lsd_zip(v, wt, p1, r))
      +ih2 = L.subst(List<&2, AR.Tree<U32>>, z => {lsd(SC.length(AR.Tree<U32>, wt), z, 1n+SC.length(AR.Tree<U32>, p), v) == SC.append(AR.Tree<U32>, p1, SC.append(AR.Tree<U32>, RV.dsl(v, wt), r)) : List<&2, AR.Tree<U32>>}, x1, SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), x, SC.length(AR.Tree<U32>, p)))), Equal.sym(List<&2, AR.Tree<U32>>, SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), x, SC.length(AR.Tree<U32>, p)))), x1, e1), ih)
      Equal.trans(List<&2, AR.Tree<U32>>, lsd(SC.length(AR.Tree<U32>, wt), SC.update(AR.Tree<U32>, x, SC.length(AR.Tree<U32>, p), RV.ds(v, ZP.vget(AR.Tree<U32>, BK.leaf0(), x, SC.length(AR.Tree<U32>, p)))), 1n+SC.length(AR.Tree<U32>, p), v), SC.append(AR.Tree<U32>, p1, SC.append(AR.Tree<U32>, RV.dsl(v, wt), r)), SC.append(AR.Tree<U32>, p, Con{RV.ds(v, b), SC.append(AR.Tree<U32>, RV.dsl(v, wt), r)}),
        ih2, LL.snoc_append_cons(AR.Tree<U32>, p, RV.ds(v, b), SC.append(AR.Tree<U32>, RV.dsl(v, wt), r)))

def SDT(+lo: Nat, +hi: Nat, +depth: Nat, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> AR.Tree<AR.Tree<U32>>:
  sd_tree(Nat.sub(hi, lo), depth, at, lo, v)

def sd_bound(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {Nat.is_le(Nat.add(lo, Nat.sub(hi, lo)), SC.pow2(depth)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_le(z, SC.pow2(depth)) == True{} : Bool}, hi, Nat.add(lo, Nat.sub(hi, lo)), Equal.sym(Nat, Nat.add(lo, Nat.sub(hi, lo)), hi, W.window_end(lo, hi, Nat.sub(hi, lo), {==}, OP.g_lohi(dir, lo, hi, depth, it, at, h))), OP.g_cap(dir, lo, hi, depth, it, at, h))

# After the strip the window holds every block with v removed.
def sd_win(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, SDT(lo, hi, depth, at, v)), lo, Nat.sub(hi, lo)) == RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))) : List<&2, AR.Tree<U32>>}:
  +k = Nat.sub(hi, lo)
  +xs = AR.slots(AR.Tree<U32>, at)
  +p = SC.take(AR.Tree<U32>, xs, lo)
  +dd = SC.drop(AR.Tree<U32>, xs, lo)
  +bw = RM.BW(lo, hi, at)
  +r = SC.drop(AR.Tree<U32>, dd, k)
  +pfa = OP.g_adj(dir, lo, hi, depth, it, at, h)
  +hle = N.le_trans(lo, Nat.add(lo, k), SC.length(AR.Tree<U32>, xs), N.le_add_right(lo, k), ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, pfa, OP.g_lohi(dir, lo, hi, depth, it, at, h), OP.g_cap(dir, lo, hi, depth, it, at, h)))
  +lenp = LL.sc_length_take(AR.Tree<U32>, xs, lo, hle)
  +lenbw = AV.av_lenbw(dir, lo, hi, depth, it, at, h)
  +hxs = Equal.trans(List<&2, AR.Tree<U32>>, xs, SC.append(AR.Tree<U32>, p, dd), SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, bw, r)),
    Equal.sym(List<&2, AR.Tree<U32>>, SC.append(AR.Tree<U32>, p, dd), xs, ZP.take_drop_app(AR.Tree<U32>, xs, lo)),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.append(AR.Tree<U32>, p, z), dd, SC.append(AR.Tree<U32>, bw, r), Equal.sym(List<&2, AR.Tree<U32>>, SC.append(AR.Tree<U32>, bw, r), dd, ZP.take_drop_app(AR.Tree<U32>, dd, k))))
  +yy = SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, RV.dsl(v, bw), r))
  +z1 = L.subst(Nat, n => {lsd(n, SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, bw, r)), SC.length(AR.Tree<U32>, p), v) == yy : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, bw), k, lenbw, lsd_zip(v, bw, p, r))
  +z2 = L.subst(Nat, n => {lsd(k, SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, bw, r)), n, v) == yy : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, p), lo, lenp, z1)
  +z3 = L.subst(List<&2, AR.Tree<U32>>, z => {lsd(k, z, lo, v) == yy : List<&2, AR.Tree<U32>>}, SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, bw, r)), xs, Equal.sym(List<&2, AR.Tree<U32>>, xs, SC.append(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, bw, r)), hxs), z2)
  +ed = L.subst(Nat, n => {SC.drop(AR.Tree<U32>, yy, n) == SC.append(AR.Tree<U32>, RV.dsl(v, bw), r) : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, p), lo, lenp, ZP.drop_app_len(AR.Tree<U32>, p, SC.append(AR.Tree<U32>, RV.dsl(v, bw), r)))
  +lend = Equal.trans(Nat, SC.length(AR.Tree<U32>, RV.dsl(v, bw)), SC.length(AR.Tree<U32>, bw), k, RV.len_dsl(v, bw), lenbw)
  +et = L.subst(Nat, n => {SC.take(AR.Tree<U32>, SC.append(AR.Tree<U32>, RV.dsl(v, bw), r), n) == RV.dsl(v, bw) : List<&2, AR.Tree<U32>>}, SC.length(AR.Tree<U32>, RV.dsl(v, bw)), k, lend, ZP.take_app_exact(AR.Tree<U32>, RV.dsl(v, bw), r))
  +ews = Equal.trans(List<&2, AR.Tree<U32>>, RV.dsl(v, bw), RV.dsl(v, SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), RV.BBd(lo, hi, it, at, v)})), RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => RV.dsl(v, z), bw, SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), RV.BBd(lo, hi, it, at, v)}), RV.rv_bw(dir, lo, hi, depth, it, at, v, h, hf)),
    RV.dsl_app(v, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), RV.BBd(lo, hi, it, at, v)}))
  Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, SDT(lo, hi, depth, at, v)), lo), k), SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, lsd(k, xs, lo, v), lo), k), RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, z, lo), k), AR.slots(AR.Tree<U32>, SDT(lo, hi, depth, at, v)), lsd(k, xs, lo, v), sd_slots(k, depth, at, lo, v, pfa, sd_bound(dir, lo, hi, depth, it, at, h))),
    Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, lsd(k, xs, lo, v), lo), k), SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, yy, lo), k), RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, z, lo), k), lsd(k, xs, lo, v), yy, z3),
      Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.drop(AR.Tree<U32>, yy, lo), k), SC.take(AR.Tree<U32>, SC.append(AR.Tree<U32>, RV.dsl(v, bw), r), k), RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))),
        Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.take(AR.Tree<U32>, z, k), SC.drop(AR.Tree<U32>, yy, lo), SC.append(AR.Tree<U32>, RV.dsl(v, bw), r), ed),
        Equal.trans(List<&2, AR.Tree<U32>>, SC.take(AR.Tree<U32>, SC.append(AR.Tree<U32>, RV.dsl(v, bw), r), k), RV.dsl(v, bw), RV2.WS(v, lo, hi, it, at, RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v))), et, ews))))

def p2(ids: Array<U32>, adj: Array<Array<U32>>) -> G.Pair2:
  G.P2{ids, adj}

def strip_eq(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.strip_all(U32.from_nat(lo), U32.from_nat(hi), v, AR.thaw(U32, it), A2.thaw2(at)) == p2(AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v))) : G.Pair2}:
  Equal.trans(G.Pair2, p2(AR.thaw(U32, it), G.sd_loop(U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), v, U32.from_nat(lo), A2.thaw2(at))), p2(AR.thaw(U32, it), G.sd_loop(Nat.sub(hi, lo), v, U32.from_nat(lo), A2.thaw2(at))), p2(AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v))),
    Equal.cong(Nat, G.Pair2, n => p2(AR.thaw(U32, it), G.sd_loop(n, v, U32.from_nat(lo), A2.thaw2(at))), U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), Nat.sub(hi, lo), EG.span_nat(dir, lo, hi, depth, it, at, h)),
    Equal.cong(Array<Array<U32>>, G.Pair2, z => p2(AR.thaw(U32, it), z), G.sd_loop(Nat.sub(hi, lo), v, U32.from_nat(lo), A2.thaw2(at)), A2.thaw2(SDT(lo, hi, depth, at, v)), sd_run(Nat.sub(hi, lo), depth, at, lo, v, ED.dep32(dir, lo, hi, depth, it, at, h), OP.g_adj(dir, lo, hi, depth, it, at, h), sd_bound(dir, lo, hi, depth, it, at, h), OP.g_blocks(dir, lo, hi, depth, it, at, h))))

# ---- remove_vertex: the case analysis ----

def rv_side_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}, head: Bool) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, RV2.RVR(G.rv_side(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v)), head)), (GS.GM{dir, RV.DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n):
  match head:
    case True{}:
      RV2.rv_head_core(dir, lo, hi, depth, it, at, v, h, hf, SDT(lo, hi, depth, at, v), RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v)), sd_perfect(Nat.sub(hi, lo), depth, at, lo, v, OP.g_adj(dir, lo, hi, depth, it, at, h)), sd_win(dir, lo, hi, depth, it, at, v, h, hf))
    case False{}:
      RV2.rv_tail_core(dir, lo, hi, depth, it, at, v, h, hf, SDT(lo, hi, depth, at, v), RV.ds(v, RM.BX(dir, lo, hi, depth, it, at, v)), sd_perfect(Nat.sub(hi, lo), depth, at, lo, v, OP.g_adj(dir, lo, hi, depth, it, at, h)), sd_win(dir, lo, hi, depth, it, at, v, h, hf))

def rv_case1(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, found: Bool, +ef: {RM.FX(lo, hi, it, v) == found : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.rv_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, found), GS.remove_vertex_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, found, RM.SX(dir, lo, hi, depth, it, at, v)), dir, RM.AM(lo, hi, it, at), v), 0n):
  match found:
    case False{}:
      UC.uc_same(dir, lo, hi, depth, it, at, h, G.rv_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, False{}), GS.remove_vertex_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, False{}, RM.SX(dir, lo, hi, depth, it, at, v)), dir, RM.AM(lo, hi, it, at), v), 0n, E.VertexNotFound{}, {==}, {==})
    case True{}:
      UC.uc_conv(ST.Sh{dir, lo, hi, depth, it, at}, ST.Sh{dir, lo, hi, depth, it, at}, G.rv_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, True{}), RV2.RVR(G.rv_drop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), p2(AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v))))),
        GS.remove_vertex_at(LB.pickv(List<&2, BE.Entry<U32, Unit>>, True{}, RM.SX(dir, lo, hi, depth, it, at, v)), dir, RM.AM(lo, hi, it, at), v), (GS.GM{dir, RV.DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n,
        {==},
        Equal.cong(G.Pair2, G.Graph & Result<&2, &2, E.Error, Unit>, z => RV2.RVR(G.rv_drop(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, RM.IX(lo, hi, it, v), z)), p2(AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v))), G.strip_all(U32.from_nat(lo), U32.from_nat(hi), v, AR.thaw(U32, it), A2.thaw2(at)), Equal.sym(G.Pair2, G.strip_all(U32.from_nat(lo), U32.from_nat(hi), v, AR.thaw(U32, it), A2.thaw2(at)), p2(AR.thaw(U32, it), A2.thaw2(SDT(lo, hi, depth, at, v))), strip_eq(dir, lo, hi, depth, it, at, v, h))),
        {==},
        rv_side_case(dir, lo, hi, depth, it, at, v, h, ef, U32.is_lt(U32.sub(RM.IX(lo, hi, it, v), U32.from_nat(lo)), U32.sub(U32.sub(U32.from_nat(hi), 1), RM.IX(lo, hi, it, v)))))

def rv_core(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.remove_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveVertex{v}), 0n):
  L.subst(G.Loc, z => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.rv_fin(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, A2.thaw2(at), v, z), GS.remove_vertex_at(GS.find(v, RM.AM(lo, hi, it, at)), dir, RM.AM(lo, hi, it, at), v), 0n),
    G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)),
    Equal.sym(G.Loc, G.locate(depth, v, U32.from_nat(lo), U32.from_nat(hi), AR.thaw(U32, it)), G.LC{AR.thaw(U32, it), RM.IX(lo, hi, it, v), RM.FX(lo, hi, it, v)}, OP.hv_locate(dir, lo, hi, depth, it, at, v, h)),
    L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, G.rv_pick(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, AR.thaw(U32, it), A2.thaw2(at), RM.IX(lo, hi, it, v), v, RM.FX(lo, hi, it, v)), GS.remove_vertex_at(m, dir, RM.AM(lo, hi, it, at), v), 0n),
      LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), GS.find(v, RM.AM(lo, hi, it, at)),
      Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), LB.pickv(List<&2, BE.Entry<U32, Unit>>, RM.FX(lo, hi, it, v), RM.SX(dir, lo, hi, depth, it, at, v)), ED.gfind(dir, lo, hi, depth, it, at, v, h)),
      rv_case1(dir, lo, hi, depth, it, at, v, h, RM.FX(lo, hi, it, v), {==})))

# remove_vertex refines the specification, preserves the invariant and does not grow the measure.
def so_remove_vertex(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> GT.StepOK(ST.Sh{dir, lo, hi, depth, it, at}, E.RemoveVertex{v}):
  UC.uc_step(ST.Sh{dir, lo, hi, depth, it, at}, E.RemoveVertex{v}, G.remove_vertex(ST.real(ST.Sh{dir, lo, hi, depth, it, at}), v), rv_core(dir, lo, hi, depth, it, at, v, h), {==})
