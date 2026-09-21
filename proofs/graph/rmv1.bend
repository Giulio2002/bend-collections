import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/order.bend as O
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../balanced_search_tree/sorted.bend as SO
import ../balanced_search_tree/specops.bend as SP
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./search.bend as SE
import ./window.bend as W
import ./lb.bend as LB
import ./ops.bend as OP
import ./blk.bend as BK
import ./edge.bend as ED
import ./lists.bend as LS
import ./ext.bend as X
import ./nbrops.bend as NO
import ./gstep.bend as GT
import ./zip.bend as ZP
import ./rmedge.bend as RM
import ./ucore.bend as UC
import ./asc.bend as AS
import ./ucore.bend as UC
import ./asc.bend as AS
import ./eops.bend as EO
import ./addv1.bend as AV

# remove_vertex, part 1: deleting a present vertex from the window lists, the
# abstract model, the invariant and the measure.

def ds(+v: U32, +b: AR.Tree<U32>) -> AR.Tree<U32>:
  NO.dsel(b, v, NO.fnd(b, v))

def dsl(+v: U32, bs: List<&2, AR.Tree<U32>>) -> List<&2, AR.Tree<U32>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{ds(v, b), dsl(v, t)}

def len_dsl(+v: U32, +bs: List<&2, AR.Tree<U32>>) -> {SC.length(AR.Tree<U32>, dsl(v, bs)) == SC.length(AR.Tree<U32>, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(AR.Tree<U32>, dsl(v, t)), SC.length(AR.Tree<U32>, t), len_dsl(v, t))

def dsl_app(+v: U32, +xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>) -> {dsl(v, SC.append(AR.Tree<U32>, xs, ys)) == SC.append(AR.Tree<U32>, dsl(v, xs), dsl(v, ys)) : List<&2, AR.Tree<U32>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      LL.cons_cong(AR.Tree<U32>, ds(v, b), dsl(v, SC.append(AR.Tree<U32>, t, ys)), SC.append(AR.Tree<U32>, dsl(v, t), dsl(v, ys)), dsl_app(v, t, ys))

def blocks_split_l(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}) -> {ST.blocks_ok(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      L.and_intro(ST.blk_ok(b), ST.blocks_ok(t), L.and_left(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h), blocks_split_l(t, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h)))

def blocks_split_r(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}) -> {ST.blocks_ok(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+b, +t}:
      blocks_split_r(t, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h))

def blocks_app(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +hx: {ST.blocks_ok(xs) == True{} : Bool}, +hy: {ST.blocks_ok(ys) == True{} : Bool}) -> {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+b, +t}:
      L.and_intro(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), L.and_left(ST.blk_ok(b), ST.blocks_ok(t), hx), blocks_app(t, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(t), hx), hy))

def blocks_dsl(+v: U32, +bs: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(bs) == True{} : Bool}) -> {ST.blocks_ok(dsl(v, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      L.and_intro(ST.blk_ok(ds(v, b)), ST.blocks_ok(dsl(v, t)), NO.dsel_ok(b, v, L.and_left(ST.blk_ok(b), ST.blocks_ok(t), h), NO.fnd(b, v), {==}), blocks_dsl(v, t, L.and_right(ST.blk_ok(b), ST.blocks_ok(t), h)))

def amodel_dsl(+v: U32, +ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(bs) == True{} : Bool}) -> {ST.amodel(ks, dsl(v, bs)) == GS.strip(v, ST.amodel(ks, bs)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match ks bs:
    case Con{+k, +kt} Con{+b, +bt}:
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, Con{BE.Entry{k, ST.uset(ST.bents(ds(v, b)))}, ST.amodel(kt, dsl(v, bt))}, Con{BE.Entry{k, GS.sdel(v, ST.uset(ST.bents(b)))}, ST.amodel(kt, dsl(v, bt))}, GS.strip(v, ST.amodel(Con{k, kt}, Con{b, bt})),
        Equal.cong(List<&2, BE.Entry<U32, Unit>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => Con{BE.Entry{k, z}, ST.amodel(kt, dsl(v, bt))}, ST.uset(ST.bents(ds(v, b))), GS.sdel(v, ST.uset(ST.bents(b))), NO.dsem(b, v, L.and_left(ST.blk_ok(b), ST.blocks_ok(bt), h), NO.fnd(b, v), {==})),
        LL.cons_cong(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, BE.Entry{k, GS.sdel(v, ST.uset(ST.bents(b)))}, ST.amodel(kt, dsl(v, bt)), GS.strip(v, ST.amodel(kt, bt)), amodel_dsl(v, kt, bt, L.and_right(ST.blk_ok(b), ST.blocks_ok(bt), h))))
    case Nil{} bs0:
      {==}
    case Con{+k, +kt} Nil{}:
      {==}

def strip_app(+v: U32, +xs: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +ys: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>) -> {GS.strip(v, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, xs, ys)) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, xs), GS.strip(v, ys)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +s}, +t}:
      LL.cons_cong(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, BE.Entry{k, GS.sdel(v, s)}, GS.strip(v, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, t, ys)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, t), GS.strip(v, ys)), strip_app(v, t, ys))

def del_at_app(-V: Data, +e1: List<&2, BE.Entry<U32, V>>, +e: BE.Entry<U32, V>, +e2: List<&2, BE.Entry<U32, V>>) -> {LB.del_at(V, SC.append(BE.Entry<U32, V>, e1, Con{e, e2}), SC.length(BE.Entry<U32, V>, e1)) == SC.append(BE.Entry<U32, V>, e1, e2) : List<&2, BE.Entry<U32, V>>}:
  match e1:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(BE.Entry<U32, V>, h, LB.del_at(V, SC.append(BE.Entry<U32, V>, t, Con{e, e2}), SC.length(BE.Entry<U32, V>, t)), SC.append(BE.Entry<U32, V>, t, e2), del_at_app(V, t, e, e2))

def mdeg_dsl(+v: U32, +bs: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(bs) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(dsl(v, bs)), GT.mdeg(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +hb = L.and_left(ST.blk_ok(b), ST.blocks_ok(t), h)
      GT.max_le(ST.bdeg(ds(v, b)), GT.mdeg(dsl(v, t)), Nat.max(ST.bdeg(b), GT.mdeg(t)),
        N.le_trans(ST.bdeg(ds(v, b)), ST.bdeg(b), Nat.max(ST.bdeg(b), GT.mdeg(t)), RM.dsel_deg(b, v, hb, NO.fnd(b, v), {==}), GT.le_max_l(ST.bdeg(b), GT.mdeg(t))),
        N.le_trans(GT.mdeg(dsl(v, t)), GT.mdeg(t), Nat.max(ST.bdeg(b), GT.mdeg(t)), mdeg_dsl(v, t, L.and_right(ST.blk_ok(b), ST.blocks_ok(t), h)), GT.le_max_r(ST.bdeg(b), GT.mdeg(t))))

# Deleting one block and removing v from the others does not raise the maximum degree.
def mdeg_del(+v: U32, +xs: List<&2, AR.Tree<U32>>, +b: AR.Tree<U32>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, Con{b, ys})) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(SC.append(AR.Tree<U32>, dsl(v, xs), dsl(v, ys))), GT.mdeg(SC.append(AR.Tree<U32>, xs, Con{b, ys}))) == True{} : Bool}:
  match xs:
    case Nil{}:
      N.le_trans(GT.mdeg(dsl(v, ys)), GT.mdeg(ys), Nat.max(ST.bdeg(b), GT.mdeg(ys)), mdeg_dsl(v, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(ys), h)), GT.le_max_r(ST.bdeg(b), GT.mdeg(ys)))
    case Con{+x, +xt}:
      +hx = L.and_left(ST.blk_ok(x), ST.blocks_ok(SC.append(AR.Tree<U32>, xt, Con{b, ys})), h)
      +ht = L.and_right(ST.blk_ok(x), ST.blocks_ok(SC.append(AR.Tree<U32>, xt, Con{b, ys})), h)
      GT.max_le(ST.bdeg(ds(v, x)), GT.mdeg(SC.append(AR.Tree<U32>, dsl(v, xt), dsl(v, ys))), Nat.max(ST.bdeg(x), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys}))),
        N.le_trans(ST.bdeg(ds(v, x)), ST.bdeg(x), Nat.max(ST.bdeg(x), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys}))), RM.dsel_deg(x, v, hx, NO.fnd(x, v), {==}), GT.le_max_l(ST.bdeg(x), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys})))),
        N.le_trans(GT.mdeg(SC.append(AR.Tree<U32>, dsl(v, xt), dsl(v, ys))), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys})), Nat.max(ST.bdeg(x), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys}))), mdeg_del(v, xt, b, ys, ht), GT.le_max_r(ST.bdeg(x), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{b, ys})))))


# ---- the present vertex v in a good shadow ----

def BKd(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> List<&2, U32>:
  SC.drop(U32, RM.KS(lo, hi, it), 1n+AV.LV(lo, hi, it, v))

def BBd(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.drop(AR.Tree<U32>, RM.BW(lo, hi, at), 1n+AV.LV(lo, hi, it, v))

def DK(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> List<&2, U32>:
  SC.append(U32, AV.AK(lo, hi, it, v), BKd(lo, hi, it, v))

def DB(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.append(AR.Tree<U32>, dsl(v, AV.ABW(lo, hi, it, at, v)), dsl(v, BBd(lo, hi, it, at, v)))

def DM(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>:
  GS.strip(v, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, RM.AM(lo, hi, it, at)))

def rv_lt(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {Nat.is_lt(AV.LV(lo, hi, it, v), Nat.sub(hi, lo)) == True{} : Bool}:
  ZP.lt_cancel(lo, AV.LV(lo, hi, it, v), Nat.sub(hi, lo), L.subst(Nat, z => {Nat.is_lt(OP.lbv(lo, hi, it, v), z) == True{} : Bool}, hi, Nat.add(lo, Nat.sub(hi, lo)), Equal.sym(Nat, Nat.add(lo, Nat.sub(hi, lo)), hi, W.window_end(lo, hi, Nat.sub(hi, lo), {==}, OP.g_lohi(dir, lo, hi, depth, it, at, h))), RM.fx_hin(dir, lo, hi, depth, it, at, v, hf)))

def rv_eqat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {LB.eq_at(RM.KS(lo, hi, it), AV.LV(lo, hi, it, v), v) == True{} : Bool}:
  L.subst(Nat, z => {LB.eq_at(RM.KS(lo, hi, it), z, v) == True{} : Bool}, W.lbu(v, RM.KS(lo, hi, it)), AV.LV(lo, hi, it, v), Equal.sym(Nat, AV.LV(lo, hi, it, v), W.lbu(v, RM.KS(lo, hi, it)), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo)), RM.fx_eq(dir, lo, hi, depth, it, at, v, h, hf))

def rv_ks(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {RM.KS(lo, hi, it) == SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}) : List<&2, U32>}:
  +ks = RM.KS(lo, hi, it)
  +l = AV.LV(lo, hi, it, v)
  +hl = L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, Nat.sub(hi, lo), SC.length(U32, ks), Equal.sym(Nat, SC.length(U32, ks), Nat.sub(hi, lo), AV.av_lenks(dir, lo, hi, depth, it, at, h)), rv_lt(dir, lo, hi, depth, it, at, v, h, hf))
  Equal.trans(List<&2, U32>, ks, SC.append(U32, AV.AK(lo, hi, it, v), SC.drop(U32, ks, l)), SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}),
    Equal.sym(List<&2, U32>, SC.append(U32, AV.AK(lo, hi, it, v), SC.drop(U32, ks, l)), ks, ZP.take_drop_app(U32, ks, l)),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, AV.AK(lo, hi, it, v), z), SC.drop(U32, ks, l), Con{v, BKd(lo, hi, it, v)},
      Equal.trans(List<&2, U32>, SC.drop(U32, ks, l), Con{ZP.vget(U32, 0, ks, l), BKd(lo, hi, it, v)}, Con{v, BKd(lo, hi, it, v)}, ZP.drop_cons_g(U32, ks, l, 0, hl),
        Equal.cong(U32, List<&2, U32>, z => Con{z, BKd(lo, hi, it, v)}, ZP.vget(U32, 0, ks, l), v, EO.val_of_eq(ks, l, v, rv_eqat(dir, lo, hi, depth, it, at, v, h, hf))))))

def rv_bw(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {RM.BW(lo, hi, at) == SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}) : List<&2, AR.Tree<U32>>}:
  +bw = RM.BW(lo, hi, at)
  +l = AV.LV(lo, hi, it, v)
  +hl = L.subst(Nat, z => {Nat.is_lt(l, z) == True{} : Bool}, Nat.sub(hi, lo), SC.length(AR.Tree<U32>, bw), Equal.sym(Nat, SC.length(AR.Tree<U32>, bw), Nat.sub(hi, lo), AV.av_lenbw(dir, lo, hi, depth, it, at, h)), rv_lt(dir, lo, hi, depth, it, at, v, h, hf))
  Equal.trans(List<&2, AR.Tree<U32>>, bw, SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), SC.drop(AR.Tree<U32>, bw, l)), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}),
    Equal.sym(List<&2, AR.Tree<U32>>, SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), SC.drop(AR.Tree<U32>, bw, l)), bw, ZP.take_drop_app(AR.Tree<U32>, bw, l)),
    Equal.cong(List<&2, AR.Tree<U32>>, List<&2, AR.Tree<U32>>, z => SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), z), SC.drop(AR.Tree<U32>, bw, l), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}, ZP.drop_cons_g(AR.Tree<U32>, bw, l, BK.leaf0(), hl)))

def rv_del(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, RM.AM(lo, hi, it, at)) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), AV.ABW(lo, hi, it, at, v)), ST.amodel(BKd(lo, hi, it, v), BBd(lo, hi, it, at, v))) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +am = RM.AM(lo, hi, it, at)
  +e1 = ST.amodel(AV.AK(lo, hi, it, v), AV.ABW(lo, hi, it, at, v))
  +e2 = ST.amodel(BKd(lo, hi, it, v), BBd(lo, hi, it, at, v))
  +ek = W.amodel_keys(RM.KS(lo, hi, it), RM.BW(lo, hi, at), RM.hlen_of(dir, lo, hi, depth, it, at, h))
  +elb = Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), W.lbu(v, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am)), W.lbu(v, RM.KS(lo, hi, it)), W.lbx_lbu(List<&2, BE.Entry<U32, Unit>>, v, am), Equal.cong(List<&2, U32>, Nat, z => W.lbu(v, z), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), RM.KS(lo, hi, it), ek))
  +el = Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), W.lbu(v, RM.KS(lo, hi, it)), AV.LV(lo, hi, it, v), elb, Equal.sym(Nat, AV.LV(lo, hi, it, v), W.lbu(v, RM.KS(lo, hi, it)), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo)))
  +hfk = L.subst(List<&2, U32>, z => {LB.eq_at(z, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), v) == True{} : Bool}, RM.KS(lo, hi, it), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), Equal.sym(List<&2, U32>, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), RM.KS(lo, hi, it), ek),
    L.subst(Nat, z => {LB.eq_at(RM.KS(lo, hi, it), z, v) == True{} : Bool}, W.lbu(v, RM.KS(lo, hi, it)), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), Equal.sym(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), W.lbu(v, RM.KS(lo, hi, it)), elb), RM.fx_eq(dir, lo, hi, depth, it, at, v, h, hf)))
  +hs = W.sorted_amodel(RM.KS(lo, hi, it), RM.BW(lo, hi, at), W.asc_win(Nat.sub(hi, lo), AR.slots(U32, it), lo, OP.g_asc(dir, lo, hi, depth, it, at, h)))
  +eam = Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, am, ST.amodel(SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)})), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, Con{BE.Entry{v, RM.SX(dir, lo, hi, depth, it, at, v)}, e2}),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, am, ST.amodel(SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}), RM.BW(lo, hi, at)), ST.amodel(SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)})),
      Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(z, RM.BW(lo, hi, at)), RM.KS(lo, hi, it), SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}), rv_ks(dir, lo, hi, depth, it, at, v, h, hf)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)}), z), RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}), rv_bw(dir, lo, hi, depth, it, at, v, h, hf))),
    AV.amodel_app(AV.AK(lo, hi, it, v), AV.ABW(lo, hi, it, at, v), Con{v, BKd(lo, hi, it, v)}, Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}, AV.av_hlab(dir, lo, hi, depth, it, at, v, h)))
  +elen = Equal.trans(Nat, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), SC.length(U32, AV.AK(lo, hi, it, v)), AV.LV(lo, hi, it, v), AV.amodel_len(AV.AK(lo, hi, it, v), AV.ABW(lo, hi, it, at, v), AV.av_hlab(dir, lo, hi, depth, it, at, v, h)), AV.av_lena(dir, lo, hi, depth, it, at, v, h))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, am), LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2),
    Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am)), S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, am), LS.del_found(List<&2, BE.Entry<U32, Unit>>, am, v, hs, hfk)),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am)), LB.del_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, Con{BE.Entry{v, RM.SX(dir, lo, hi, depth, it, at, v)}, e2}), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2),
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am)), LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1)), LB.del_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, Con{BE.Entry{v, RM.SX(dir, lo, hi, depth, it, at, v)}, e2}), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1)),
        Equal.cong(Nat, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, n => LB.del_at(List<&2, BE.Entry<U32, Unit>>, am, n), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), AV.LV(lo, hi, it, v), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), el, Equal.sym(Nat, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), AV.LV(lo, hi, it, v), elen))),
        Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => LB.del_at(List<&2, BE.Entry<U32, Unit>>, z, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1)), am, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, Con{BE.Entry{v, RM.SX(dir, lo, hi, depth, it, at, v)}, e2}), eam)),
      del_at_app(List<&2, BE.Entry<U32, Unit>>, e1, BE.Entry{v, RM.SX(dir, lo, hi, depth, it, at, v)}, e2)))

def rv_blocks2(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {ST.blocks_ok(SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)})) == True{} : Bool}:
  L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}), rv_bw(dir, lo, hi, depth, it, at, v, h, hf), OP.g_blocks(dir, lo, hi, depth, it, at, h))

def rv_model(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {ST.amodel(DK(lo, hi, it, v), DB(lo, hi, it, at, v)) == DM(lo, hi, it, at, v) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +ba = AV.ABW(lo, hi, it, at, v)
  +bb = BBd(lo, hi, it, at, v)
  +hb = rv_blocks2(dir, lo, hi, depth, it, at, v, h, hf)
  +hba = blocks_split_l(ba, Con{RM.BX(dir, lo, hi, depth, it, at, v), bb}, hb)
  +hbb = L.and_right(ST.blk_ok(RM.BX(dir, lo, hi, depth, it, at, v)), ST.blocks_ok(bb), blocks_split_r(ba, Con{RM.BX(dir, lo, hi, depth, it, at, v), bb}, hb))
  +hl = Equal.trans(Nat, SC.length(U32, AV.AK(lo, hi, it, v)), SC.length(AR.Tree<U32>, ba), SC.length(AR.Tree<U32>, dsl(v, ba)), AV.av_hlab(dir, lo, hi, depth, it, at, v, h), Equal.sym(Nat, SC.length(AR.Tree<U32>, dsl(v, ba)), SC.length(AR.Tree<U32>, ba), len_dsl(v, ba)))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(DK(lo, hi, it, v), DB(lo, hi, it, at, v)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), dsl(v, ba)), ST.amodel(BKd(lo, hi, it, v), dsl(v, bb))), DM(lo, hi, it, at, v),
    AV.amodel_app(AV.AK(lo, hi, it, v), dsl(v, ba), BKd(lo, hi, it, v), dsl(v, bb), hl),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), dsl(v, ba)), ST.amodel(BKd(lo, hi, it, v), dsl(v, bb))), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), GS.strip(v, ST.amodel(BKd(lo, hi, it, v), bb))), DM(lo, hi, it, at, v),
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), dsl(v, ba)), ST.amodel(BKd(lo, hi, it, v), dsl(v, bb))), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), ST.amodel(BKd(lo, hi, it, v), dsl(v, bb))), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), GS.strip(v, ST.amodel(BKd(lo, hi, it, v), bb))),
        Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, z, ST.amodel(BKd(lo, hi, it, v), dsl(v, bb))), ST.amodel(AV.AK(lo, hi, it, v), dsl(v, ba)), GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), amodel_dsl(v, AV.AK(lo, hi, it, v), ba, hba)),
        Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), z), ST.amodel(BKd(lo, hi, it, v), dsl(v, bb)), GS.strip(v, ST.amodel(BKd(lo, hi, it, v), bb)), amodel_dsl(v, BKd(lo, hi, it, v), bb, hbb))),
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), GS.strip(v, ST.amodel(BKd(lo, hi, it, v), bb))), GS.strip(v, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), ba), ST.amodel(BKd(lo, hi, it, v), bb))), DM(lo, hi, it, at, v),
        Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.strip(v, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), ba), ST.amodel(BKd(lo, hi, it, v), bb))), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, GS.strip(v, ST.amodel(AV.AK(lo, hi, it, v), ba)), GS.strip(v, ST.amodel(BKd(lo, hi, it, v), bb))), strip_app(v, ST.amodel(AV.AK(lo, hi, it, v), ba), ST.amodel(BKd(lo, hi, it, v), bb))),
        Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => GS.strip(v, z), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), ba), ST.amodel(BKd(lo, hi, it, v), bb)), S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, RM.AM(lo, hi, it, at)), Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, S.del(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, v, RM.AM(lo, hi, it, at)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AV.AK(lo, hi, it, v), ba), ST.amodel(BKd(lo, hi, it, v), bb)), rv_del(dir, lo, hi, depth, it, at, v, h, hf))))))

def rv_asc(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {ST.asc(DK(lo, hi, it, v)) == True{} : Bool}:
  +w = SC.append(U32, AV.AK(lo, hi, it, v), Con{v, BKd(lo, hi, it, v)})
  L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, LS.dl(w, SC.length(U32, AV.AK(lo, hi, it, v))), DK(lo, hi, it, v), X.dl_app(AV.AK(lo, hi, it, v), v, BKd(lo, hi, it, v)),
    AS.asc_dl(w, SC.length(U32, AV.AK(lo, hi, it, v)), L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, RM.KS(lo, hi, it), w, rv_ks(dir, lo, hi, depth, it, at, v, h, hf), W.asc_win(Nat.sub(hi, lo), AR.slots(U32, it), lo, OP.g_asc(dir, lo, hi, depth, it, at, h)))))

def rv_blocks(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {ST.blocks_ok(DB(lo, hi, it, at, v)) == True{} : Bool}:
  +ba = AV.ABW(lo, hi, it, at, v)
  +bb = BBd(lo, hi, it, at, v)
  +hb = rv_blocks2(dir, lo, hi, depth, it, at, v, h, hf)
  blocks_app(dsl(v, ba), dsl(v, bb), blocks_dsl(v, ba, blocks_split_l(ba, Con{RM.BX(dir, lo, hi, depth, it, at, v), bb}, hb)), blocks_dsl(v, bb, L.and_right(ST.blk_ok(RM.BX(dir, lo, hi, depth, it, at, v)), ST.blocks_ok(bb), blocks_split_r(ba, Con{RM.BX(dir, lo, hi, depth, it, at, v), bb}, hb))))

def rv_mdeg(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {Nat.is_le(GT.mdeg(DB(lo, hi, it, at, v)), GT.mdeg(RM.BW(lo, hi, at))) == True{} : Bool}:
  L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(DB(lo, hi, it, at, v)), GT.mdeg(z)) == True{} : Bool}, SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}), RM.BW(lo, hi, at), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, AV.ABW(lo, hi, it, at, v), Con{RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v)}), rv_bw(dir, lo, hi, depth, it, at, v, h, hf)),
    mdeg_del(v, AV.ABW(lo, hi, it, at, v), RM.BX(dir, lo, hi, depth, it, at, v), BBd(lo, hi, it, at, v), rv_blocks2(dir, lo, hi, depth, it, at, v, h, hf)))

def rv_spec(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}) -> {GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveVertex{v}) == (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}:
  L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => {GS.remove_vertex_at(m, dir, RM.AM(lo, hi, it, at), v) == (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}, Some{RM.SX(dir, lo, hi, depth, it, at, v)}, GS.find(v, RM.AM(lo, hi, it, at)), Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), Some{RM.SX(dir, lo, hi, depth, it, at, v)}, RM.fx_find(dir, lo, hi, depth, it, at, v, h, hf)), {==})

# Any new shadow whose windows are the deleted lists is a correct remove_vertex step.
def rv_new(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hf: {RM.FX(lo, hi, it, v) == True{} : Bool}, +lo2: Nat, +hi2: Nat, +d2: Nat, +it2: AR.Tree<U32>, +at2: AR.Tree<AR.Tree<U32>>, -rt: G.Graph & Result<&2, &2, E.Error, Unit>, +e1: {rt == (ST.real(ST.Sh{dir, lo2, hi2, d2, it2, at2}), Done{Unit{}}) : G.Graph & Result<&2, &2, E.Error, Unit>}, +hk2: {1n+Nat.sub(hi2, lo2) == Nat.sub(hi, lo) : Nat}, +hw1: {ST.win(U32, AR.slots(U32, it2), lo2, Nat.sub(hi2, lo2)) == DK(lo, hi, it, v) : List<&2, U32>}, +hw2: {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at2), lo2, Nat.sub(hi2, lo2)) == DB(lo, hi, it, at, v) : List<&2, AR.Tree<U32>>}, +hd2: {Nat.is_le(d2, 31n) == True{} : Bool}, +hpi2: {AR.perfect(U32, d2, it2) == True{} : Bool}, +hpa2: {AR.perfect(AR.Tree<U32>, d2, at2) == True{} : Bool}, +hlo2: {Nat.is_le(lo2, hi2) == True{} : Bool}, +hcap2: {Nat.is_le(hi2, SC.pow2(d2)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, rt, (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n):
  +wk = ST.win(U32, AR.slots(U32, it2), lo2, Nat.sub(hi2, lo2))
  +wb = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at2), lo2, Nat.sub(hi2, lo2))
  +em = Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(wk, wb), ST.amodel(DK(lo, hi, it, v), wb), DM(lo, hi, it, at, v),
    Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(z, wb), wk, DK(lo, hi, it, v), hw1),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(DK(lo, hi, it, v), wb), ST.amodel(DK(lo, hi, it, v), DB(lo, hi, it, at, v)), DM(lo, hi, it, at, v),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(DK(lo, hi, it, v), z), wb, DB(lo, hi, it, at, v), hw2),
      rv_model(dir, lo, hi, depth, it, at, v, h, hf)))
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(dir, z), ST.amodel(wk, wb), DM(lo, hi, it, at, v), em)
  +wf = GT.wf_after(dir, lo, hi, depth, it, at, h, E.RemoveVertex{v}, GS.GM{dir, ST.amodel(wk, wb)}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{dir, ST.amodel(wk, wb)}, E.OUnit{Done{Unit{}}}), (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveVertex{v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.RemoveVertex{v}), (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), rv_spec(dir, lo, hi, depth, it, at, v, h, hf))))
  +hasc = AS.asc_at_of_win(Nat.sub(hi2, lo2), AR.slots(U32, it2), lo2, ED.win_fits(U32, d2, it2, lo2, hi2, hpi2, hlo2, hcap2), L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, DK(lo, hi, it, v), wk, Equal.sym(List<&2, U32>, wk, DK(lo, hi, it, v), hw1), rv_asc(dir, lo, hi, depth, it, at, v, h, hf)))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, DB(lo, hi, it, at, v), wb, Equal.sym(List<&2, AR.Tree<U32>>, wb, DB(lo, hi, it, at, v), hw2), rv_blocks(dir, lo, hi, depth, it, at, v, h, hf))
  +mu0 = GT.mu(ST.Sh{dir, lo, hi, depth, it, at})
  +md = GT.mdeg(RM.BW(lo, hi, at))
  +hm = L.subst(List<&2, AR.Tree<U32>>, z => {Nat.is_le(GT.mdeg(z), md) == True{} : Bool}, DB(lo, hi, it, at, v), wb, Equal.sym(List<&2, AR.Tree<U32>>, wb, DB(lo, hi, it, at, v), hw2), rv_mdeg(dir, lo, hi, depth, it, at, v, h, hf))
  +h1 = N.le_trans(Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), Nat.add(Nat.sub(hi2, lo2), md), 1n+Nat.add(Nat.sub(hi2, lo2), md), W.add_mono(Nat.sub(hi2, lo2), GT.mdeg(wb), md, hm), N.le_succ(Nat.add(Nat.sub(hi2, lo2), md)))
  +h2 = L.subst(Nat, z => {Nat.is_le(Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), Nat.add(z, md)) == True{} : Bool}, 1n+Nat.sub(hi2, lo2), Nat.sub(hi, lo), hk2, h1)
  UC.uc_mk(ST.Sh{dir, lo, hi, depth, it, at}, rt, (GS.GM{dir, DM(lo, hi, it, at, v)}, E.OUnit{Done{Unit{}}}), 0n, ST.Sh{dir, lo2, hi2, d2, it2, at2}, Done{Unit{}}, e1,
    GT.good_mk(dir, lo2, hi2, d2, it2, at2, hd2, hpi2, hpa2, hlo2, hcap2, hasc, hbl, wf), e3,
    N.le_trans(Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), mu0, Nat.add(mu0, 0n), h2, N.le_add_right(mu0, 0n)))
