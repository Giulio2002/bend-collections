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

# add_vertex, part 1: what inserting an absent vertex does to the window
# lists, the abstract model, the invariant and the measure.

# The fresh adjacency block of src/graph.bend (empty_blk): deg 0, size 4, lcap 2.
def ebt() -> AR.Tree<U32>:
  AR.TNode{AR.TNode{AR.TLeaf{0}, AR.TLeaf{4}}, AR.TNode{AR.TLeaf{2}, AR.TLeaf{0}}}

def ebt_thaw() -> {G.empty_blk() == AR.thaw(U32, ebt()) : Array<U32>}:
  {==}

def ebt_ok() -> {ST.blk_ok(ebt()) == True{} : Bool}:
  {==}

# ---- zipped lists ----

def nz(+n: Nat, +h: {0n == 1n+n : Nat}) -> Empty:
  L.false_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+n, 0n, Equal.sym(Nat, 0n, 1n+n, h)))

def amodel_app(+k1: List<&2, U32>, +b1: List<&2, AR.Tree<U32>>, +k2: List<&2, U32>, +b2: List<&2, AR.Tree<U32>>, +h: {SC.length(U32, k1) == SC.length(AR.Tree<U32>, b1) : Nat}) -> {ST.amodel(SC.append(U32, k1, k2), SC.append(AR.Tree<U32>, b1, b2)) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(k1, b1), ST.amodel(k2, b2)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match k1 b1:
    case Nil{} Nil{}:
      {==}
    case Con{+k, +kt} Con{+b, +bt}:
      LL.cons_cong(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, BE.Entry{k, ST.uset(ST.bents(b))}, ST.amodel(SC.append(U32, kt, k2), SC.append(AR.Tree<U32>, bt, b2)), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(kt, bt), ST.amodel(k2, b2)),
        amodel_app(kt, bt, k2, b2, Equal.cong(Nat, Nat, z => N.pred(z), 1n+SC.length(U32, kt), 1n+SC.length(AR.Tree<U32>, bt), h)))
    case Nil{} Con{+b, +bt}:
      Empty.absurd({ST.amodel(k2, SC.append(AR.Tree<U32>, Con{b, bt}, b2)) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Nil{}, Con{b, bt}), ST.amodel(k2, b2)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, nz(SC.length(AR.Tree<U32>, bt), h))
    case Con{+k, +kt} Nil{}:
      Empty.absurd({ST.amodel(SC.append(U32, Con{k, kt}, k2), b2) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Con{k, kt}, Nil{}), ST.amodel(k2, b2)) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, nz(SC.length(U32, kt), Equal.sym(Nat, 1n+SC.length(U32, kt), 0n, h)))

def amodel_len(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +h: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(ks, bs)) == SC.length(U32, ks) : Nat}:
  match ks bs:
    case Nil{} Nil{}:
      {==}
    case Con{+k, +kt} Con{+b, +bt}:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(kt, bt)), SC.length(U32, kt), amodel_len(kt, bt, Equal.cong(Nat, Nat, z => N.pred(z), 1n+SC.length(U32, kt), 1n+SC.length(AR.Tree<U32>, bt), h)))
    case Nil{} Con{+b, +bt}:
      {==}
    case Con{+k, +kt} Nil{}:
      Empty.absurd({SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Con{k, kt}, Nil{})) == SC.length(U32, Con{k, kt}) : Nat}, nz(SC.length(U32, kt), Equal.sym(Nat, 1n+SC.length(U32, kt), 0n, h)))

def ins_at0(-V: Data, +xs: List<&2, BE.Entry<U32, V>>, +e: BE.Entry<U32, V>) -> {LB.ins_at(V, xs, 0n, e) == Con{e, xs} : List<&2, BE.Entry<U32, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

def ins_at_app(-V: Data, +e1: List<&2, BE.Entry<U32, V>>, +e2: List<&2, BE.Entry<U32, V>>, +e: BE.Entry<U32, V>) -> {LB.ins_at(V, SC.append(BE.Entry<U32, V>, e1, e2), SC.length(BE.Entry<U32, V>, e1), e) == SC.append(BE.Entry<U32, V>, e1, Con{e, e2}) : List<&2, BE.Entry<U32, V>>}:
  match e1:
    case Nil{}:
      ins_at0(V, e2, e)
    case Con{+h, +t}:
      LL.cons_cong(BE.Entry<U32, V>, h, LB.ins_at(V, SC.append(BE.Entry<U32, V>, t, e2), SC.length(BE.Entry<U32, V>, t), e), SC.append(BE.Entry<U32, V>, t, Con{e, e2}), ins_at_app(V, t, e2, e))

def max0(+m: Nat) -> {Nat.max(0n, m) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def mdeg_ebt(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>) -> {GT.mdeg(SC.append(AR.Tree<U32>, xs, Con{ebt(), ys})) == GT.mdeg(SC.append(AR.Tree<U32>, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      max0(GT.mdeg(ys))
    case Con{+x, +xt}:
      Equal.cong(Nat, Nat, z => Nat.max(ST.bdeg(x), z), GT.mdeg(SC.append(AR.Tree<U32>, xt, Con{ebt(), ys})), GT.mdeg(SC.append(AR.Tree<U32>, xt, ys)), mdeg_ebt(xt, ys))

def blocks_ebt(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}) -> {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, Con{ebt(), ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +xt}:
      L.and_intro(ST.blk_ok(x), ST.blocks_ok(SC.append(AR.Tree<U32>, xt, Con{ebt(), ys})), L.and_left(ST.blk_ok(x), ST.blocks_ok(SC.append(AR.Tree<U32>, xt, ys)), h),
        blocks_ebt(xt, ys, L.and_right(ST.blk_ok(x), ST.blocks_ok(SC.append(AR.Tree<U32>, xt, ys)), h)))

# ---- the absent vertex v in a good shadow ----

def LV(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> Nat:
  RM.LX(lo, hi, it, v)

def AK(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> List<&2, U32>:
  SC.take(U32, RM.KS(lo, hi, it), LV(lo, hi, it, v))

def BKs(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> List<&2, U32>:
  SC.drop(U32, RM.KS(lo, hi, it), LV(lo, hi, it, v))

def ABW(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.take(AR.Tree<U32>, RM.BW(lo, hi, at), LV(lo, hi, it, v))

def BBW(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.drop(AR.Tree<U32>, RM.BW(lo, hi, at), LV(lo, hi, it, v))

def NK(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> List<&2, U32>:
  SC.append(U32, AK(lo, hi, it, v), Con{v, BKs(lo, hi, it, v)})

def NB(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, AR.Tree<U32>>:
  SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), Con{ebt(), BBW(lo, hi, it, at, v)})

def NM(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>:
  SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(AK(lo, hi, it, v), ABW(lo, hi, it, at, v)), Con{BE.Entry{v, Nil{}}, ST.amodel(BKs(lo, hi, it, v), BBW(lo, hi, it, at, v))})

def av_hl(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> {Nat.is_le(LV(lo, hi, it, v), Nat.sub(hi, lo)) == True{} : Bool}:
  W.lbs_le(v, AR.slots(U32, it), Nat.sub(hi, lo), lo)

def av_lenks(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(U32, RM.KS(lo, hi, it)) == Nat.sub(hi, lo) : Nat}:
  ED.win_len(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo), ED.win_fits(U32, depth, it, lo, hi, OP.g_ids(dir, lo, hi, depth, it, at, h), OP.g_lohi(dir, lo, hi, depth, it, at, h), OP.g_cap(dir, lo, hi, depth, it, at, h)))

def av_lenbw(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(AR.Tree<U32>, RM.BW(lo, hi, at)) == Nat.sub(hi, lo) : Nat}:
  ED.win_len(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo), ED.win_fits(AR.Tree<U32>, depth, at, lo, hi, OP.g_adj(dir, lo, hi, depth, it, at, h), OP.g_lohi(dir, lo, hi, depth, it, at, h), OP.g_cap(dir, lo, hi, depth, it, at, h)))

def av_lena(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(U32, AK(lo, hi, it, v)) == LV(lo, hi, it, v) : Nat}:
  LL.sc_length_take(U32, RM.KS(lo, hi, it), LV(lo, hi, it, v), L.subst(Nat, z => {Nat.is_le(LV(lo, hi, it, v), z) == True{} : Bool}, Nat.sub(hi, lo), SC.length(U32, RM.KS(lo, hi, it)), Equal.sym(Nat, SC.length(U32, RM.KS(lo, hi, it)), Nat.sub(hi, lo), av_lenks(dir, lo, hi, depth, it, at, h)), av_hl(lo, hi, it, v)))

def av_lenba(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(AR.Tree<U32>, ABW(lo, hi, it, at, v)) == LV(lo, hi, it, v) : Nat}:
  LL.sc_length_take(AR.Tree<U32>, RM.BW(lo, hi, at), LV(lo, hi, it, v), L.subst(Nat, z => {Nat.is_le(LV(lo, hi, it, v), z) == True{} : Bool}, Nat.sub(hi, lo), SC.length(AR.Tree<U32>, RM.BW(lo, hi, at)), Equal.sym(Nat, SC.length(AR.Tree<U32>, RM.BW(lo, hi, at)), Nat.sub(hi, lo), av_lenbw(dir, lo, hi, depth, it, at, h)), av_hl(lo, hi, it, v)))

def av_hlab(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {SC.length(U32, AK(lo, hi, it, v)) == SC.length(AR.Tree<U32>, ABW(lo, hi, it, at, v)) : Nat}:
  Equal.trans(Nat, SC.length(U32, AK(lo, hi, it, v)), LV(lo, hi, it, v), SC.length(AR.Tree<U32>, ABW(lo, hi, it, at, v)), av_lena(dir, lo, hi, depth, it, at, v, h), Equal.sym(Nat, SC.length(AR.Tree<U32>, ABW(lo, hi, it, at, v)), LV(lo, hi, it, v), av_lenba(dir, lo, hi, depth, it, at, v, h)))

def av_eqat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}) -> {W.eq_at(RM.KS(lo, hi, it), LV(lo, hi, it, v), v) == False{} : Bool}:
  +hlen = L.subst(Nat, z => {Nat.is_le(hi, z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, AR.slots(U32, it)), Equal.sym(Nat, SC.length(U32, AR.slots(U32, it)), SC.pow2(depth), AR.slots_length(U32, depth, it, OP.g_ids(dir, lo, hi, depth, it, at, h))), OP.g_cap(dir, lo, hi, depth, it, at, h))
  Equal.trans(Bool, W.eq_at(RM.KS(lo, hi, it), LV(lo, hi, it, v), v), RM.FX(lo, hi, it, v), False{},
    Equal.sym(Bool, RM.FX(lo, hi, it, v), W.eq_at(RM.KS(lo, hi, it), LV(lo, hi, it, v), v), W.found_bridge(it, lo, hi, Nat.sub(hi, lo), LV(lo, hi, it, v), v, {==}, OP.g_lohi(dir, lo, hi, depth, it, at, h), av_hl(lo, hi, it, v), hlen)),
    hv0)

def av_find(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}) -> {GS.find(v, RM.AM(lo, hi, it, at)) == None{} : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}:
  L.subst(Bool, b => {GS.find(v, RM.AM(lo, hi, it, at)) == LB.pickv(List<&2, BE.Entry<U32, Unit>>, b, RM.SX(dir, lo, hi, depth, it, at, v)) : Maybe<&2, List<&2, BE.Entry<U32, Unit>>>}, RM.FX(lo, hi, it, v), False{}, hv0, ED.gfind(dir, lo, hi, depth, it, at, v, h))

def av_ks(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +v: U32) -> {RM.KS(lo, hi, it) == SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), RM.KS(lo, hi, it), ZP.take_drop_app(U32, RM.KS(lo, hi, it), LV(lo, hi, it, v)))

def av_bw(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> {RM.BW(lo, hi, at) == SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)) : List<&2, AR.Tree<U32>>}:
  Equal.sym(List<&2, AR.Tree<U32>>, SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)), RM.BW(lo, hi, at), ZP.take_drop_app(AR.Tree<U32>, RM.BW(lo, hi, at), LV(lo, hi, it, v)))

def EV(+v: U32) -> BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>:
  BE.Entry{v, Nil{}}

# The model after the insertion: the specification's put.
def av_put(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}) -> {GS.put(v, Nil{}, RM.AM(lo, hi, it, at)) == NM(lo, hi, it, at, v) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  +am = RM.AM(lo, hi, it, at)
  +e1 = ST.amodel(AK(lo, hi, it, v), ABW(lo, hi, it, at, v))
  +e2 = ST.amodel(BKs(lo, hi, it, v), BBW(lo, hi, it, at, v))
  +el = Equal.trans(Nat, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), W.lbu(v, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am)), LV(lo, hi, it, v), W.lbx_lbu(List<&2, BE.Entry<U32, Unit>>, v, am),
    Equal.trans(Nat, W.lbu(v, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am)), W.lbu(v, RM.KS(lo, hi, it)), LV(lo, hi, it, v),
      Equal.cong(List<&2, U32>, Nat, z => W.lbu(v, z), LB.keys_of(List<&2, BE.Entry<U32, Unit>>, am), RM.KS(lo, hi, it), W.amodel_keys(RM.KS(lo, hi, it), RM.BW(lo, hi, at), RM.hlen_of(dir, lo, hi, depth, it, at, h))),
      Equal.sym(Nat, LV(lo, hi, it, v), W.lbu(v, RM.KS(lo, hi, it)), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo))))
  +eam = Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, am, ST.amodel(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v))), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, am, ST.amodel(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), RM.BW(lo, hi, at)), ST.amodel(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v))),
      Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(z, RM.BW(lo, hi, at)), RM.KS(lo, hi, it), SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), av_ks(lo, hi, it, v)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), z), RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)), av_bw(lo, hi, it, at, v))),
    amodel_app(AK(lo, hi, it, v), ABW(lo, hi, it, at, v), BKs(lo, hi, it, v), BBW(lo, hi, it, at, v), av_hlab(dir, lo, hi, depth, it, at, v, h)))
  +elen = Equal.trans(Nat, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), SC.length(U32, AK(lo, hi, it, v)), LV(lo, hi, it, v), amodel_len(AK(lo, hi, it, v), ABW(lo, hi, it, at, v), av_hlab(dir, lo, hi, depth, it, at, v, h)), av_lena(dir, lo, hi, depth, it, at, v, h))
  Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.put(v, Nil{}, am), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), EV(v)), NM(lo, hi, it, at, v),
    Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), EV(v)), GS.put(v, Nil{}, am), LB.ins_new(List<&2, BE.Entry<U32, Unit>>, am, v, Nil{}, av_find(dir, lo, hi, depth, it, at, v, h, hv0))),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), EV(v)), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), EV(v)), NM(lo, hi, it, at, v),
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), EV(v)), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), LV(lo, hi, it, v), EV(v)), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), EV(v)),
        Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), EV(v)), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, LV(lo, hi, it, v), EV(v)), LB.ins_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), LV(lo, hi, it, v), EV(v)),
          Equal.cong(Nat, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, n => LB.ins_at(List<&2, BE.Entry<U32, Unit>>, am, n, EV(v)), LB.lbx(List<&2, BE.Entry<U32, Unit>>, v, am), LV(lo, hi, it, v), el),
          Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => LB.ins_at(List<&2, BE.Entry<U32, Unit>>, z, LV(lo, hi, it, v), EV(v)), am, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), eam)),
        Equal.cong(Nat, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, n => LB.ins_at(List<&2, BE.Entry<U32, Unit>>, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1, e2), n, EV(v)), LV(lo, hi, it, v), SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), Equal.sym(Nat, SC.length(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, e1), LV(lo, hi, it, v), elen))),
      ins_at_app(List<&2, BE.Entry<U32, Unit>>, e1, e2, EV(v))))

def av_asc(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}) -> {ST.asc(NK(lo, hi, it, v)) == True{} : Bool}:
  +ks = RM.KS(lo, hi, it)
  +l = LV(lo, hi, it, v)
  +so = ED.sorted_uset(ks, W.asc_win(Nat.sub(hi, lo), AR.slots(U32, it), lo, OP.g_asc(dir, lo, hi, depth, it, at, h)))
  +el = Equal.trans(Nat, LB.lbx(Unit, v, ST.uset(ks)), W.lbu(v, ks), l, ED.uset_lbx(v, ks), Equal.sym(Nat, l, W.lbu(v, ks), W.lbs_lbu(v, AR.slots(U32, it), Nat.sub(hi, lo), lo)))
  +fs1 = L.subst(List<&2, U32>, z => {S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ks))) == LB.eq_at(z, LB.lbx(Unit, v, ST.uset(ks)), v) : Bool}, LB.keys_of(Unit, ST.uset(ks)), ks, ED.uset_keys(ks), LB.find_some(Unit, ST.uset(ks), v, so))
  +fs2 = L.subst(Nat, n => {S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ks))) == LB.eq_at(ks, n, v) : Bool}, LB.lbx(Unit, v, ST.uset(ks)), l, el, fs1)
  +fs3 = Equal.trans(Bool, S.is_some(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ks))), LB.eq_at(ks, l, v), False{}, fs2,
    Equal.trans(Bool, LB.eq_at(ks, l, v), W.eq_at(ks, l, v), False{}, W.eqm_same(SC.nth(U32, ks, l), v), av_eqat(dir, lo, hi, depth, it, at, v, h, hv0)))
  +hf = NO.none_of(Unit, S.find(~U32, ~U32.cmp, Unit, v, ST.uset(ks)), fs3)
  +sins = SP.sorted_ins(~U32, ~U32.cmp, ~O.u32_order, Unit, ST.uset(ks), v, Unit{}, so)
  +s1 = L.subst(List<&2, BE.Entry<U32, Unit>>, z => {SO.sorted(~U32, ~U32.cmp, Unit, z) == True{} : Bool}, S.ins(~U32, ~U32.cmp, Unit, v, Unit{}, ST.uset(ks)), LB.ins_at(Unit, ST.uset(ks), LB.lbx(Unit, v, ST.uset(ks)), BE.Entry{v, Unit{}}), Equal.sym(List<&2, BE.Entry<U32, Unit>>, LB.ins_at(Unit, ST.uset(ks), LB.lbx(Unit, v, ST.uset(ks)), BE.Entry{v, Unit{}}), S.ins(~U32, ~U32.cmp, Unit, v, Unit{}, ST.uset(ks)), LB.ins_new(Unit, ST.uset(ks), v, Unit{}, hf)), sins)
  +s2 = L.subst(Nat, n => {SO.sorted(~U32, ~U32.cmp, Unit, LB.ins_at(Unit, ST.uset(ks), n, BE.Entry{v, Unit{}})) == True{} : Bool}, LB.lbx(Unit, v, ST.uset(ks)), l, el, s1)
  +s3 = L.subst(List<&2, BE.Entry<U32, Unit>>, z => {SO.sorted(~U32, ~U32.cmp, Unit, z) == True{} : Bool}, LB.ins_at(Unit, ST.uset(ks), l, BE.Entry{v, Unit{}}), ST.uset(LS.il(ks, l, v)), Equal.sym(List<&2, BE.Entry<U32, Unit>>, ST.uset(LS.il(ks, l, v)), LB.ins_at(Unit, ST.uset(ks), l, BE.Entry{v, Unit{}}), LS.uset_il(ks, l, v)), s2)
  +eil = Equal.trans(List<&2, U32>, LS.il(ks, l, v), LS.il(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), l, v), NK(lo, hi, it, v),
    Equal.cong(List<&2, U32>, List<&2, U32>, z => LS.il(z, l, v), ks, SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), av_ks(lo, hi, it, v)),
    Equal.trans(List<&2, U32>, LS.il(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), l, v), LS.il(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), SC.length(U32, AK(lo, hi, it, v)), v), NK(lo, hi, it, v),
      Equal.cong(Nat, List<&2, U32>, n => LS.il(SC.append(U32, AK(lo, hi, it, v), BKs(lo, hi, it, v)), n, v), l, SC.length(U32, AK(lo, hi, it, v)), Equal.sym(Nat, SC.length(U32, AK(lo, hi, it, v)), l, av_lena(dir, lo, hi, depth, it, at, v, h))),
      X.il_app(AK(lo, hi, it, v), v, BKs(lo, hi, it, v))))
  LS.asc_back(NK(lo, hi, it, v), L.subst(List<&2, U32>, z => {SO.sorted(~U32, ~U32.cmp, Unit, ST.uset(z)) == True{} : Bool}, LS.il(ks, l, v), NK(lo, hi, it, v), eil, s3))

def av_blocks(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {ST.blocks_ok(NB(lo, hi, it, at, v)) == True{} : Bool}:
  blocks_ebt(ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v), L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)), av_bw(lo, hi, it, at, v), OP.g_blocks(dir, lo, hi, depth, it, at, h)))

def av_mdeg(+lo: Nat, +hi: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32) -> {GT.mdeg(NB(lo, hi, it, at, v)) == GT.mdeg(RM.BW(lo, hi, at)) : Nat}:
  Equal.trans(Nat, GT.mdeg(NB(lo, hi, it, at, v)), GT.mdeg(SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v))), GT.mdeg(RM.BW(lo, hi, at)),
    mdeg_ebt(ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)),
    Equal.cong(List<&2, AR.Tree<U32>>, Nat, z => GT.mdeg(z), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)), RM.BW(lo, hi, at), Equal.sym(List<&2, AR.Tree<U32>>, RM.BW(lo, hi, at), SC.append(AR.Tree<U32>, ABW(lo, hi, it, at, v), BBW(lo, hi, it, at, v)), av_bw(lo, hi, it, at, v))))

def av_spec(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}) -> {GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddVertex{v}) == (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}:
  L.subst(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, m => {GS.add_vertex_at(m, dir, RM.AM(lo, hi, it, at), v) == (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}) : GS.Model & E.Obs}, None{}, GS.find(v, RM.AM(lo, hi, it, at)), Equal.sym(Maybe<&2, List<&2, BE.Entry<U32, Unit>>>, GS.find(v, RM.AM(lo, hi, it, at)), None{}, av_find(dir, lo, hi, depth, it, at, v, h, hv0)), {==})

# Any new shadow whose windows are the inserted lists is a correct add_vertex step.
def av_new(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +v: U32, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, +hv0: {RM.FX(lo, hi, it, v) == False{} : Bool}, +lo2: Nat, +hi2: Nat, +d2: Nat, +it2: AR.Tree<U32>, +at2: AR.Tree<AR.Tree<U32>>, -rt: G.Graph & Result<&2, &2, E.Error, Unit>, +e1: {rt == (ST.real(ST.Sh{dir, lo2, hi2, d2, it2, at2}), Done{Unit{}}) : G.Graph & Result<&2, &2, E.Error, Unit>}, +hk2: {Nat.sub(hi2, lo2) == 1n+Nat.sub(hi, lo) : Nat}, +hw1: {ST.win(U32, AR.slots(U32, it2), lo2, Nat.sub(hi2, lo2)) == NK(lo, hi, it, v) : List<&2, U32>}, +hw2: {ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at2), lo2, Nat.sub(hi2, lo2)) == NB(lo, hi, it, at, v) : List<&2, AR.Tree<U32>>}, +hd2: {Nat.is_le(d2, 31n) == True{} : Bool}, +hpi2: {AR.perfect(U32, d2, it2) == True{} : Bool}, +hpa2: {AR.perfect(AR.Tree<U32>, d2, at2) == True{} : Bool}, +hlo2: {Nat.is_le(lo2, hi2) == True{} : Bool}, +hcap2: {Nat.is_le(hi2, SC.pow2(d2)) == True{} : Bool}) -> UC.UCore(ST.Sh{dir, lo, hi, depth, it, at}, rt, (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n):
  +wk = ST.win(U32, AR.slots(U32, it2), lo2, Nat.sub(hi2, lo2))
  +wb = ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at2), lo2, Nat.sub(hi2, lo2))
  +em = Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(wk, wb), ST.amodel(NK(lo, hi, it, v), wb), GS.put(v, Nil{}, RM.AM(lo, hi, it, at)),
    Equal.cong(List<&2, U32>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(z, wb), wk, NK(lo, hi, it, v), hw1),
    Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(NK(lo, hi, it, v), wb), ST.amodel(NK(lo, hi, it, v), NB(lo, hi, it, at, v)), GS.put(v, Nil{}, RM.AM(lo, hi, it, at)),
      Equal.cong(List<&2, AR.Tree<U32>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => ST.amodel(NK(lo, hi, it, v), z), wb, NB(lo, hi, it, at, v), hw2),
      Equal.trans(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(NK(lo, hi, it, v), NB(lo, hi, it, at, v)), NM(lo, hi, it, at, v), GS.put(v, Nil{}, RM.AM(lo, hi, it, at)),
        amodel_app(AK(lo, hi, it, v), ABW(lo, hi, it, at, v), Con{v, BKs(lo, hi, it, v)}, Con{ebt(), BBW(lo, hi, it, at, v)}, av_hlab(dir, lo, hi, depth, it, at, v, h)),
        Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.put(v, Nil{}, RM.AM(lo, hi, it, at)), NM(lo, hi, it, at, v), av_put(dir, lo, hi, depth, it, at, v, h, hv0)))))
  +e3 = Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, GS.Model & E.Obs, z => RM.gm_done(dir, z), ST.amodel(wk, wb), GS.put(v, Nil{}, RM.AM(lo, hi, it, at)), em)
  +wf = GT.wf_after(dir, lo, hi, depth, it, at, h, E.AddVertex{v}, GS.GM{dir, ST.amodel(wk, wb)}, E.OUnit{Done{Unit{}}},
    Equal.trans(GS.Model & E.Obs, (GS.GM{dir, ST.amodel(wk, wb)}, E.OUnit{Done{Unit{}}}), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddVertex{v}),
      e3, Equal.sym(GS.Model & E.Obs, GS.step(ST.model(ST.Sh{dir, lo, hi, depth, it, at}), E.AddVertex{v}), (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), av_spec(dir, lo, hi, depth, it, at, v, h, hv0))))
  +hasc = AS.asc_at_of_win(Nat.sub(hi2, lo2), AR.slots(U32, it2), lo2, ED.win_fits(U32, d2, it2, lo2, hi2, hpi2, hlo2, hcap2), L.subst(List<&2, U32>, z => {ST.asc(z) == True{} : Bool}, NK(lo, hi, it, v), wk, Equal.sym(List<&2, U32>, wk, NK(lo, hi, it, v), hw1), av_asc(dir, lo, hi, depth, it, at, v, h, hv0)))
  +hbl = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, NB(lo, hi, it, at, v), wb, Equal.sym(List<&2, AR.Tree<U32>>, wb, NB(lo, hi, it, at, v), hw2), av_blocks(dir, lo, hi, depth, it, at, v, h))
  +mu0 = GT.mu(ST.Sh{dir, lo, hi, depth, it, at})
  +em1 = Equal.trans(Nat, GT.mdeg(wb), GT.mdeg(NB(lo, hi, it, at, v)), GT.mdeg(RM.BW(lo, hi, at)), Equal.cong(List<&2, AR.Tree<U32>>, Nat, z => GT.mdeg(z), wb, NB(lo, hi, it, at, v), hw2), av_mdeg(lo, hi, it, at, v))
  +emu = Equal.trans(Nat, Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), Nat.add(1n+Nat.sub(hi, lo), GT.mdeg(wb)), 1n+mu0,
    Equal.cong(Nat, Nat, z => Nat.add(z, GT.mdeg(wb)), Nat.sub(hi2, lo2), 1n+Nat.sub(hi, lo), hk2),
    Equal.cong(Nat, Nat, z => Nat.add(1n+Nat.sub(hi, lo), z), GT.mdeg(wb), GT.mdeg(RM.BW(lo, hi, at)), em1))
  +hmu = L.subst(Nat, z => {Nat.is_le(z, Nat.add(mu0, 1n)) == True{} : Bool}, 1n+mu0, Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), Equal.sym(Nat, Nat.add(Nat.sub(hi2, lo2), GT.mdeg(wb)), 1n+mu0, emu),
    L.subst(Nat, z => {Nat.is_le(1n+mu0, z) == True{} : Bool}, 1n+mu0, Nat.add(mu0, 1n), Equal.sym(Nat, Nat.add(mu0, 1n), 1n+mu0, N.add_comm(mu0, 1n)), N.le_refl(1n+mu0)))
  UC.uc_mk(ST.Sh{dir, lo, hi, depth, it, at}, rt, (GS.GM{dir, GS.put(v, Nil{}, RM.AM(lo, hi, it, at))}, E.OUnit{Done{Unit{}}}), 1n, ST.Sh{dir, lo2, hi2, d2, it2, at2}, Done{Unit{}}, e1,
    GT.good_mk(dir, lo2, hi2, d2, it2, at2, hd2, hpi2, hpa2, hlo2, hcap2, hasc, hbl, wf), e3, hmu)
