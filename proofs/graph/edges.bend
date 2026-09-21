import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32.bend as U
import ../lib/u32half.bend as H
import ../lib/array.bend as AR
import ../lib/array2.bend as A2
import ../../spec/common.bend as SC
import ../../spec/graph.bend as GS
import ../../src/graph.bend as G
import ../../types/balanced_search_tree.bend as BE
import ../../types/graph.bend as E
import ./state.bend as ST
import ./shift.bend as SH
import ./search.bend as SE
import ./window.bend as W
import ./blk.bend as BK
import ./edge.bend as ED
import ./ops.bend as OP
import ./nbrs.bend as NB

# `edges`: the runtime walks the vertex slots from the last to the first and,
# inside each adjacency block, the entries from the last to the first,
# consing every kept edge onto one accumulator. That is the specification's
# `all_edges` read backwards, so the accumulator ends in forward order.

# ---- list algebra of the specification ----

def keep_bridge(b: Bool, +x: E.Edge, +rest: List<&2, E.Edge>) -> {G.keep_if(b, x, rest) == GS.keep_if(b, x, rest) : List<&2, E.Edge>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def keep_app(b: Bool, +x: E.Edge, +r: List<&2, E.Edge>, +s: List<&2, E.Edge>) -> {SC.append(E.Edge, GS.keep_if(b, x, r), s) == GS.keep_if(b, x, SC.append(E.Edge, r, s)) : List<&2, E.Edge>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def keep_nil(b: Bool, +x: E.Edge, +acc: List<&2, E.Edge>) -> {SC.append(E.Edge, GS.keep_if(b, x, Nil{}), acc) == G.keep_if(b, x, acc) : List<&2, E.Edge>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def out_app(+d: Bool, +u: U32, +ws: List<&2, U32>, +vs: List<&2, U32>) -> {GS.out_edges(d, u, SC.append(U32, ws, vs)) == SC.append(E.Edge, GS.out_edges(d, u, ws), GS.out_edges(d, u, vs)) : List<&2, E.Edge>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +c = Bool.or(d, Cmp.is_lt(U32.cmp(u, w)))
      Equal.trans(List<&2, E.Edge>, GS.keep_if(c, E.Edge{u, w}, GS.out_edges(d, u, SC.append(U32, t, vs))), GS.keep_if(c, E.Edge{u, w}, SC.append(E.Edge, GS.out_edges(d, u, t), GS.out_edges(d, u, vs))), SC.append(E.Edge, GS.keep_if(c, E.Edge{u, w}, GS.out_edges(d, u, t)), GS.out_edges(d, u, vs)),
        Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => GS.keep_if(c, E.Edge{u, w}, z), GS.out_edges(d, u, SC.append(U32, t, vs)), SC.append(E.Edge, GS.out_edges(d, u, t), GS.out_edges(d, u, vs)), out_app(d, u, t, vs)),
        Equal.sym(List<&2, E.Edge>, SC.append(E.Edge, GS.keep_if(c, E.Edge{u, w}, GS.out_edges(d, u, t)), GS.out_edges(d, u, vs)), GS.keep_if(c, E.Edge{u, w}, SC.append(E.Edge, GS.out_edges(d, u, t), GS.out_edges(d, u, vs))),
          keep_app(c, E.Edge{u, w}, GS.out_edges(d, u, t), GS.out_edges(d, u, vs))))

def all_app(+d: Bool, +es: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, +fs: List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>) -> {GS.all_edges(d, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, es, fs)) == SC.append(E.Edge, GS.all_edges(d, es), GS.all_edges(d, fs)) : List<&2, E.Edge>}:
  match es:
    case Nil{}:
      {==}
    case Con{BE.Entry{+u, +s}, +t}:
      +o = GS.out_edges(d, u, GS.keys(Unit, s))
      Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, o, GS.all_edges(d, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, t, fs))), SC.append(E.Edge, o, SC.append(E.Edge, GS.all_edges(d, t), GS.all_edges(d, fs))), SC.append(E.Edge, SC.append(E.Edge, o, GS.all_edges(d, t)), GS.all_edges(d, fs)),
        Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, o, z), GS.all_edges(d, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, t, fs)), SC.append(E.Edge, GS.all_edges(d, t), GS.all_edges(d, fs)), all_app(d, t, fs)),
        Equal.sym(List<&2, E.Edge>, SC.append(E.Edge, SC.append(E.Edge, o, GS.all_edges(d, t)), GS.all_edges(d, fs)), SC.append(E.Edge, o, SC.append(E.Edge, GS.all_edges(d, t), GS.all_edges(d, fs))), LL.append_assoc(E.Edge, o, GS.all_edges(d, t), GS.all_edges(d, fs))))

# rd with an accumulator is rd from Nil followed by the accumulator.
def rd_acc(+p: Nat, +xs: List<&2, U32>, +j: Nat, +ys: List<&2, U32>) -> {NB.rd(p, xs, j, ys) == SC.append(U32, NB.rd(p, xs, j, Nil{}), ys) : List<&2, U32>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      +x = SH.val_at(xs, j)
      +j1 = Nat.sub(j, 1n)
      Equal.trans(List<&2, U32>, NB.rd(q, xs, j1, Con{x, ys}), SC.append(U32, NB.rd(q, xs, j1, Nil{}), Con{x, ys}), SC.append(U32, NB.rd(q, xs, j1, Con{x, Nil{}}), ys),
        rd_acc(q, xs, j1, Con{x, ys}),
        Equal.sym(List<&2, U32>, SC.append(U32, NB.rd(q, xs, j1, Con{x, Nil{}}), ys), SC.append(U32, NB.rd(q, xs, j1, Nil{}), Con{x, ys}),
          Equal.trans(List<&2, U32>, SC.append(U32, NB.rd(q, xs, j1, Con{x, Nil{}}), ys), SC.append(U32, SC.append(U32, NB.rd(q, xs, j1, Nil{}), Con{x, Nil{}}), ys), SC.append(U32, NB.rd(q, xs, j1, Nil{}), Con{x, ys}),
            Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.append(U32, z, ys), NB.rd(q, xs, j1, Con{x, Nil{}}), SC.append(U32, NB.rd(q, xs, j1, Nil{}), Con{x, Nil{}}), rd_acc(q, xs, j1, Con{x, Nil{}})),
            LL.append_assoc(U32, NB.rd(q, xs, j1, Nil{}), Con{x, Nil{}}, ys))))

# ---- the inner loop: one block ----

def ri(m: Nat, +xs: List<&2, U32>, +j: Nat, +dir: Bool, +u: U32, acc: List<&2, E.Edge>) -> List<&2, E.Edge>:
  match m:
    case 0n:
      acc
    case 1n+p:
      ri(p, xs, Nat.sub(j, 1n), dir, u, G.keep_if(Bool.or(dir, U32.is_lt(u, SH.val_at(xs, j))), E.Edge{u, SH.val_at(xs, j)}, acc))

def ri_rd(+m: Nat, +xs: List<&2, U32>, +j: Nat, +dir: Bool, +u: U32, +acc: List<&2, E.Edge>) -> {ri(m, xs, j, dir, u, acc) == SC.append(E.Edge, GS.out_edges(dir, u, NB.rd(m, xs, j, Nil{})), acc) : List<&2, E.Edge>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +x = SH.val_at(xs, j)
      +j1 = Nat.sub(j, 1n)
      +c = Bool.or(dir, U32.is_lt(u, x))
      +r = NB.rd(p, xs, j1, Nil{})
      Equal.trans(List<&2, E.Edge>, ri(p, xs, j1, dir, u, G.keep_if(c, E.Edge{u, x}, acc)), SC.append(E.Edge, GS.out_edges(dir, u, r), G.keep_if(c, E.Edge{u, x}, acc)), SC.append(E.Edge, GS.out_edges(dir, u, NB.rd(p, xs, j1, Con{x, Nil{}})), acc),
        ri_rd(p, xs, j1, dir, u, G.keep_if(c, E.Edge{u, x}, acc)),
        Equal.sym(List<&2, E.Edge>, SC.append(E.Edge, GS.out_edges(dir, u, NB.rd(p, xs, j1, Con{x, Nil{}})), acc), SC.append(E.Edge, GS.out_edges(dir, u, r), G.keep_if(c, E.Edge{u, x}, acc)),
          Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, GS.out_edges(dir, u, NB.rd(p, xs, j1, Con{x, Nil{}})), acc), SC.append(E.Edge, GS.out_edges(dir, u, SC.append(U32, r, Con{x, Nil{}})), acc), SC.append(E.Edge, GS.out_edges(dir, u, r), G.keep_if(c, E.Edge{u, x}, acc)),
            Equal.cong(List<&2, U32>, List<&2, E.Edge>, z => SC.append(E.Edge, GS.out_edges(dir, u, z), acc), NB.rd(p, xs, j1, Con{x, Nil{}}), SC.append(U32, r, Con{x, Nil{}}), rd_acc(p, xs, j1, Con{x, Nil{}})),
            Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, GS.out_edges(dir, u, SC.append(U32, r, Con{x, Nil{}})), acc), SC.append(E.Edge, SC.append(E.Edge, GS.out_edges(dir, u, r), GS.out_edges(dir, u, Con{x, Nil{}})), acc), SC.append(E.Edge, GS.out_edges(dir, u, r), G.keep_if(c, E.Edge{u, x}, acc)),
              Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, z, acc), GS.out_edges(dir, u, SC.append(U32, r, Con{x, Nil{}})), SC.append(E.Edge, GS.out_edges(dir, u, r), GS.out_edges(dir, u, Con{x, Nil{}})), out_app(dir, u, r, Con{x, Nil{}})),
              Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, SC.append(E.Edge, GS.out_edges(dir, u, r), GS.out_edges(dir, u, Con{x, Nil{}})), acc), SC.append(E.Edge, GS.out_edges(dir, u, r), SC.append(E.Edge, GS.out_edges(dir, u, Con{x, Nil{}}), acc)), SC.append(E.Edge, GS.out_edges(dir, u, r), G.keep_if(c, E.Edge{u, x}, acc)),
                LL.append_assoc(E.Edge, GS.out_edges(dir, u, r), GS.out_edges(dir, u, Con{x, Nil{}}), acc),
                Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, GS.out_edges(dir, u, r), z), SC.append(E.Edge, GS.out_edges(dir, u, Con{x, Nil{}}), acc), G.keep_if(c, E.Edge{u, x}, acc), keep_nil(c, E.Edge{u, x}, acc)))))))

# One well-formed block: the kept edges out of u, in entry order.
def ri_blk(+bt: AR.Tree<U32>, +dir: Bool, +u: U32, +acc: List<&2, E.Edge>, +bp: {AR.perfect(U32, ST.blcap(bt), bt) == True{} : Bool}, +bcap: {Nat.is_le(Nat.add(3n, ST.bdeg(bt)), SC.pow2(ST.blcap(bt))) == True{} : Bool}) -> {ri(ST.bdeg(bt), AR.slots(U32, bt), Nat.add(2n, ST.bdeg(bt)), dir, u, acc) == SC.append(E.Edge, GS.out_edges(dir, u, ST.bents(bt)), acc) : List<&2, E.Edge>}:
  +dg = ST.bdeg(bt)
  +xs = AR.slots(U32, bt)
  Equal.trans(List<&2, E.Edge>, ri(dg, xs, Nat.add(2n, dg), dir, u, acc), SC.append(E.Edge, GS.out_edges(dir, u, NB.rd(dg, xs, Nat.add(2n, dg), Nil{})), acc), SC.append(E.Edge, GS.out_edges(dir, u, ST.bents(bt)), acc),
    ri_rd(dg, xs, Nat.add(2n, dg), dir, u, acc),
    Equal.cong(List<&2, U32>, List<&2, E.Edge>, z => SC.append(E.Edge, GS.out_edges(dir, u, z), acc), NB.rd(dg, xs, Nat.add(2n, dg), Nil{}), ST.bents(bt),
      Equal.trans(List<&2, U32>, NB.rd(dg, xs, Nat.add(2n, dg), Nil{}), SC.append(U32, ST.bents(bt), Nil{}), ST.bents(bt),
        NB.rd_win(xs, 2n, dg, Nil{}, L.subst(Nat, z => {Nat.is_le(Nat.add(3n, dg), z) == True{} : Bool}, SC.pow2(ST.blcap(bt)), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(ST.blcap(bt)), AR.slots_length(U32, ST.blcap(bt), bt, bp)), bcap)),
        LL.append_nil(U32, ST.bents(bt)))))

# ---- the inner runtime loop is ri ----

def ei0_fin(+dir: Bool, +u: U32, +acc: List<&2, E.Edge>, +j: U32, +t: AR.Tree<U32>, +i: U32, s: Sigma<&1, &1, U32, x => {Array.get(U32, AR.thaw(U32, t), i) == (AR.thaw(U32, t), x) : Array<U32> & U32}>) -> {G.ed_inner(0n, dir, u, acc, j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, E.Edge>}:
  (x, e) = s
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, t), i), (AR.thaw(U32, t), x), e) : {G.ed_inner(0n, dir, u, acc, j, _) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, E.Edge>}
  {==}

def ei0(+dir: Bool, +u: U32, +acc: List<&2, E.Edge>, +j: U32, +d: Nat, +t: AR.Tree<U32>, +i: U32, +pf: {AR.perfect(U32, d, t) == True{} : Bool}) -> {G.ed_inner(0n, dir, u, acc, j, Array.get(U32, AR.thaw(U32, t), i)) == (AR.thaw(U32, t), acc) : Array<U32> & List<&2, E.Edge>}:
  ei0_fin(dir, u, acc, j, t, i, BK.get_any(U32, d, t, i, pf))

def EiIH(+p: Nat, +d: Nat, +t: AR.Tree<U32>, +dir: Bool, +u: U32) -> Type:
  @+acc2: List<&2, E.Edge> -> @+j2: Nat ->
  @+h1: {Nat.is_lt(j2, SC.pow2(d)) == True{} : Bool} ->
  @+h2: {Nat.is_le(p, 1n+j2) == True{} : Bool} ->
  {G.ed_inner(p, dir, u, acc2, U32.from_nat(j2), Array.get(U32, AR.thaw(U32, t), U32.from_nat(j2))) == (AR.thaw(U32, t), ri(p, AR.slots(U32, t), j2, dir, u, acc2)) : Array<U32> & List<&2, E.Edge>}

def ei_succ(+p: Nat, +dir: Bool, +u: U32, +acc: List<&2, E.Edge>, +j: Nat, +d: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(1n+p, 1n+j) == True{} : Bool}, ih: EiIH(p, d, t, dir, u)) -> {G.ed_inner(p, dir, u, G.keep_if(Bool.or(dir, U32.is_lt(u, SH.val_at(AR.slots(U32, t), j))), E.Edge{u, SH.val_at(AR.slots(U32, t), j)}, acc), U32.sub(U32.from_nat(j), 1), Array.get(U32, AR.thaw(U32, t), U32.sub(U32.from_nat(j), 1))) == (AR.thaw(U32, t), ri(1n+p, AR.slots(U32, t), j, dir, u, acc)) : Array<U32> & List<&2, E.Edge>}:
  match p:
    case 0n:
      ei0(dir, u, G.keep_if(Bool.or(dir, U32.is_lt(u, SH.val_at(AR.slots(U32, t), j))), E.Edge{u, SH.val_at(AR.slots(U32, t), j)}, acc), U32.sub(U32.from_nat(j), 1), d, t, U32.sub(U32.from_nat(j), 1), pf)
    case 1n+q:
      +j1 = Nat.sub(j, 1n)
      +h1 = N.le_trans(1n, 1n+q, j, N.le_add_right(1n, q), hm)
      +es = H.sub_bridge(j, 1n, d, N.lt_le(d, 32n, hd), hj, h1)
      +hj1 = N.le_lt_trans(j1, j, SC.pow2(d), H.sub_le(j, 1n), hj)
      +hm1 = N.le_trans(1n+q, j, 1n+j1, hm, SE.le_of_pred_le(j, j1, N.le_refl(j1)))
      +ka = G.keep_if(Bool.or(dir, U32.is_lt(u, SH.val_at(AR.slots(U32, t), j))), E.Edge{u, SH.val_at(AR.slots(U32, t), j)}, acc)
      %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(j1), es) : {G.ed_inner(1n+q, dir, u, ka, _, Array.get(U32, AR.thaw(U32, t), _)) == (AR.thaw(U32, t), ri(2n+q, AR.slots(U32, t), j, dir, u, acc)) : Array<U32> & List<&2, E.Edge>}
      ih(ka, j1, hj1, hm1)

def ed_inner_ok(+m: Nat, +dir: Bool, +u: U32, +acc: List<&2, E.Edge>, +j: Nat, +d: Nat, +t: AR.Tree<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +hm: {Nat.is_le(m, 1n+j) == True{} : Bool}) -> {G.ed_inner(m, dir, u, acc, U32.from_nat(j), Array.get(U32, AR.thaw(U32, t), U32.from_nat(j))) == (AR.thaw(U32, t), ri(m, AR.slots(U32, t), j, dir, u, acc)) : Array<U32> & List<&2, E.Edge>}:
  match m:
    case 0n:
      ei0(dir, u, acc, U32.from_nat(j), d, t, U32.from_nat(j), pf)
    case 1n+p:
      %NB.get_at(j, d, t, hd, pf, hj) : {G.ed_inner(1n+p, dir, u, acc, U32.from_nat(j), _) == (AR.thaw(U32, t), ri(1n+p, AR.slots(U32, t), j, dir, u, acc)) : Array<U32> & List<&2, E.Edge>}
      ei_succ(p, dir, u, acc, j, d, t, hd, pf, hj, hm, acc2 => j2 => hj2 => hm2 => ed_inner_ok(p, dir, u, acc2, j2, d, t, hd, pf, hj2, hm2))

# ---- lists of blocks and the abstraction under snoc ----

def blocks_l(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}) -> {ST.blocks_ok(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      L.and_intro(ST.blk_ok(b), ST.blocks_ok(t), L.and_left(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h),
        blocks_l(t, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h)))

def blocks_r(+xs: List<&2, AR.Tree<U32>>, +ys: List<&2, AR.Tree<U32>>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, ys)) == True{} : Bool}) -> {ST.blocks_ok(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+b, +t}:
      blocks_r(t, ys, L.and_right(ST.blk_ok(b), ST.blocks_ok(SC.append(AR.Tree<U32>, t, ys)), h))

def blocks_last(+xs: List<&2, AR.Tree<U32>>, +b: AR.Tree<U32>, +h: {ST.blocks_ok(SC.append(AR.Tree<U32>, xs, Con{b, Nil{}})) == True{} : Bool}) -> {ST.blk_ok(b) == True{} : Bool}:
  L.and_left(ST.blk_ok(b), True{}, blocks_r(xs, Con{b, Nil{}}, h))

def amodel_snoc(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +k: U32, +b: AR.Tree<U32>, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {ST.amodel(SC.append(U32, ks, Con{k, Nil{}}), SC.append(AR.Tree<U32>, bs, Con{b, Nil{}})) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(ks, bs), Con{BE.Entry{k, ST.uset(ST.bents(b))}, Nil{}}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}:
  match ks bs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b0, bt}:
      Empty.absurd({ST.amodel(SC.append(U32, Nil{}, Con{k, Nil{}}), SC.append(AR.Tree<U32>, Con{b0, bt}, Con{b, Nil{}})) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Nil{}, Con{b0, bt}), Con{BE.Entry{k, ST.uset(ST.bents(b))}, Nil{}}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, N.zero_succ(SC.length(AR.Tree<U32>, bt), hlen))
    case Con{k0, kt} Nil{}:
      Empty.absurd({ST.amodel(SC.append(U32, Con{k0, kt}, Con{k, Nil{}}), SC.append(AR.Tree<U32>, Nil{}, Con{b, Nil{}})) == SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(Con{k0, kt}, Nil{}), Con{BE.Entry{k, ST.uset(ST.bents(b))}, Nil{}}) : List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>}, N.succ_zero(SC.length(U32, kt), hlen))
    case Con{+k0, +kt} Con{+b0, +bt}:
      Equal.cong(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, z => Con{BE.Entry{k0, ST.uset(ST.bents(b0))}, z},
        ST.amodel(SC.append(U32, kt, Con{k, Nil{}}), SC.append(AR.Tree<U32>, bt, Con{b, Nil{}})), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, ST.amodel(kt, bt), Con{BE.Entry{k, ST.uset(ST.bents(b))}, Nil{}}),
        amodel_snoc(kt, bt, k, b, N.succ_inj(SC.length(U32, kt), SC.length(AR.Tree<U32>, bt), hlen)))

# The edges of one entry: the out-edges of its block.
def all_one(+d: Bool, +k: U32, +b: AR.Tree<U32>) -> {GS.all_edges(d, Con{BE.Entry{k, ST.uset(ST.bents(b))}, Nil{}}) == GS.out_edges(d, k, ST.bents(b)) : List<&2, E.Edge>}:
  Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, GS.out_edges(d, k, GS.keys(Unit, ST.uset(ST.bents(b)))), Nil{}), GS.out_edges(d, k, GS.keys(Unit, ST.uset(ST.bents(b)))), GS.out_edges(d, k, ST.bents(b)),
    LL.append_nil(E.Edge, GS.out_edges(d, k, GS.keys(Unit, ST.uset(ST.bents(b))))),
    Equal.cong(List<&2, U32>, List<&2, E.Edge>, z => GS.out_edges(d, k, z), GS.keys(Unit, ST.uset(ST.bents(b))), ST.bents(b), NB.gkeys_uset(ST.bents(b))))

def win_one(-A: Data, +xs: List<&2, A>, +st: Nat, +y: A, +h: {SC.nth(A, xs, Nat.add(st, 0n)) == Some{y} : Maybe<&2, A>}) -> {ST.win(A, xs, st, 1n) == Con{y, Nil{}} : List<&2, A>}:
  Equal.trans(List<&2, A>, ST.win(A, xs, st, 1n), SC.append(A, ST.win(A, xs, st, 0n), Con{y, Nil{}}), Con{y, Nil{}},
    NB.win_snoc(A, xs, st, 0n, y, h),
    L.subst(List<&2, A>, z => {SC.append(A, z, Con{y, Nil{}}) == Con{y, Nil{}} : List<&2, A>}, Nil{}, ST.win(A, xs, st, 0n), Equal.sym(List<&2, A>, ST.win(A, xs, st, 0n), Nil{}, LL.sc_take_zero(A, SC.drop(A, xs, st))), {==}))

# ---- the outer mirror ----

def ro(m: Nat, +dir: Bool, +xs: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +j: Nat, acc: List<&2, E.Edge>) -> List<&2, E.Edge>:
  match m:
    case 0n:
      acc
    case 1n+p:
      ro(p, dir, xs, bs, Nat.sub(j, 1n), ri(ST.bdeg(ED.bnth(bs, j)), AR.slots(U32, ED.bnth(bs, j)), Nat.add(2n, ST.bdeg(ED.bnth(bs, j))), dir, SH.val_at(xs, j), acc))

def bsome(+bs: List<&2, AR.Tree<U32>>, +i: Nat, +hl: {Nat.is_lt(i, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}) -> {SC.nth(AR.Tree<U32>, bs, i) == Some{ED.bnth(bs, i)} : Maybe<&2, AR.Tree<U32>>}:
  ED.nth_some(AR.Tree<U32>, bs, i, BK.leaf0(), hl, SC.nth(AR.Tree<U32>, bs, i), {==})

def blk_facts_cap(+b: AR.Tree<U32>, +h: {ST.blk_ok(b) == True{} : Bool}) -> {Nat.is_le(Nat.add(3n, ST.bdeg(b)), SC.pow2(ST.blcap(b))) == True{} : Bool}:
  ED.bk_cap(b, h)

# Reading slots st+p, ..., st builds the edges of the window [st, st+1+p).
def ro_all(+dir: Bool, +xs: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +st: Nat, +p: Nat, +acc: List<&2, E.Edge>, +hxs: {Nat.is_le(Nat.add(st, 1n+p), SC.length(U32, xs)) == True{} : Bool}, +hbs: {Nat.is_le(Nat.add(st, 1n+p), SC.length(AR.Tree<U32>, bs)) == True{} : Bool}, +hb: {ST.blocks_ok(ST.win(AR.Tree<U32>, bs, st, 1n+p)) == True{} : Bool}) -> {ro(1n+p, dir, xs, bs, Nat.add(st, p), acc) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(ST.win(U32, xs, st, 1n+p), ST.win(AR.Tree<U32>, bs, st, 1n+p))), acc) : List<&2, E.Edge>}:
  match p:
    case 0n:
      +j = Nat.add(st, 0n)
      +x = SH.val_at(xs, j)
      +b = ED.bnth(bs, j)
      +hx1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(st, 1n), 1n+j, N.add_succ(st, 0n), hxs)
      +hb1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}, Nat.add(st, 1n), 1n+j, N.add_succ(st, 0n), hbs)
      +ewx = win_one(U32, xs, st, x, NB.val_some(xs, j, N.succ_le_lt(j, SC.length(U32, xs), hx1)))
      +ewb = win_one(AR.Tree<U32>, bs, st, b, bsome(bs, j, N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hb1)))
      +bk = L.and_left(ST.blk_ok(b), True{}, L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, ST.win(AR.Tree<U32>, bs, st, 1n), Con{b, Nil{}}, ewb, hb))
      %Equal.sym(List<&2, U32>, ST.win(U32, xs, st, 1n), Con{x, Nil{}}, ewx) : {ro(1n, dir, xs, bs, j, acc) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(_, ST.win(AR.Tree<U32>, bs, st, 1n))), acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, bs, st, 1n), Con{b, Nil{}}, ewb) : {ro(1n, dir, xs, bs, j, acc) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(Con{x, Nil{}}, _)), acc) : List<&2, E.Edge>}
      Equal.trans(List<&2, E.Edge>, ri(ST.bdeg(b), AR.slots(U32, b), Nat.add(2n, ST.bdeg(b)), dir, x, acc), SC.append(E.Edge, GS.out_edges(dir, x, ST.bents(b)), acc), SC.append(E.Edge, GS.all_edges(dir, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}}), acc),
        ri_blk(b, dir, x, acc, ED.bk_perfect(b, bk), ED.bk_cap(b, bk)),
        Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, z, acc), GS.out_edges(dir, x, ST.bents(b)), GS.all_edges(dir, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}}), Equal.sym(List<&2, E.Edge>, GS.all_edges(dir, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}}), GS.out_edges(dir, x, ST.bents(b)), all_one(dir, x, b))))
    case 1n+q:
      +j = Nat.add(st, 1n+q)
      +x = SH.val_at(xs, j)
      +b = ED.bnth(bs, j)
      +hx1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, xs)) == True{} : Bool}, Nat.add(st, 2n+q), 1n+j, N.add_succ(st, 1n+q), hxs)
      +hb1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}, Nat.add(st, 2n+q), 1n+j, N.add_succ(st, 1n+q), hbs)
      +hxq = N.le_trans(j, 1n+j, SC.length(U32, xs), N.lt_le(j, 1n+j, N.lt_succ(j)), hx1)
      +hbq = N.le_trans(j, 1n+j, SC.length(AR.Tree<U32>, bs), N.lt_le(j, 1n+j, N.lt_succ(j)), hb1)
      +ewx = NB.win_snoc(U32, xs, st, 1n+q, x, NB.val_some(xs, j, N.succ_le_lt(j, SC.length(U32, xs), hx1)))
      +ewb = NB.win_snoc(AR.Tree<U32>, bs, st, 1n+q, b, bsome(bs, j, N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hb1)))
      +wx = ST.win(U32, xs, st, 1n+q)
      +wb = ST.win(AR.Tree<U32>, bs, st, 1n+q)
      +hb2 = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, ST.win(AR.Tree<U32>, bs, st, 2n+q), SC.append(AR.Tree<U32>, wb, Con{b, Nil{}}), ewb, hb)
      +bk = blocks_last(wb, b, hb2)
      +hlen = Equal.trans(Nat, SC.length(U32, wx), 1n+q, SC.length(AR.Tree<U32>, wb), ED.win_len(U32, xs, st, 1n+q, hxq), Equal.sym(Nat, SC.length(AR.Tree<U32>, wb), 1n+q, ED.win_len(AR.Tree<U32>, bs, st, 1n+q, hbq)))
      +am = ST.amodel(wx, wb)
      +o = GS.out_edges(dir, x, ST.bents(b))
      +r = ri(ST.bdeg(b), AR.slots(U32, b), Nat.add(2n, ST.bdeg(b)), dir, x, acc)
      %Equal.sym(Nat, Nat.sub(j, 1n), Nat.add(st, q), NB.sub_one_add(st, q)) : {ro(1n+q, dir, xs, bs, _, r) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(ST.win(U32, xs, st, 2n+q), ST.win(AR.Tree<U32>, bs, st, 2n+q))), acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, U32>, ST.win(U32, xs, st, 2n+q), SC.append(U32, wx, Con{x, Nil{}}), ewx) : {ro(1n+q, dir, xs, bs, Nat.add(st, q), r) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(_, ST.win(AR.Tree<U32>, bs, st, 2n+q))), acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, bs, st, 2n+q), SC.append(AR.Tree<U32>, wb, Con{b, Nil{}}), ewb) : {ro(1n+q, dir, xs, bs, Nat.add(st, q), r) == SC.append(E.Edge, GS.all_edges(dir, ST.amodel(SC.append(U32, wx, Con{x, Nil{}}), _)), acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>>, ST.amodel(SC.append(U32, wx, Con{x, Nil{}}), SC.append(AR.Tree<U32>, wb, Con{b, Nil{}})), SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, am, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}}), amodel_snoc(wx, wb, x, b, hlen)) : {ro(1n+q, dir, xs, bs, Nat.add(st, q), r) == SC.append(E.Edge, GS.all_edges(dir, _), acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, E.Edge>, GS.all_edges(dir, SC.append(BE.Entry<U32, List<&2, BE.Entry<U32, Unit>>>, am, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}})), SC.append(E.Edge, GS.all_edges(dir, am), GS.all_edges(dir, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}})), all_app(dir, am, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}})) : {ro(1n+q, dir, xs, bs, Nat.add(st, q), r) == SC.append(E.Edge, _, acc) : List<&2, E.Edge>}
      %Equal.sym(List<&2, E.Edge>, GS.all_edges(dir, Con{BE.Entry{x, ST.uset(ST.bents(b))}, Nil{}}), o, all_one(dir, x, b)) : {ro(1n+q, dir, xs, bs, Nat.add(st, q), r) == SC.append(E.Edge, SC.append(E.Edge, GS.all_edges(dir, am), _), acc) : List<&2, E.Edge>}
      Equal.trans(List<&2, E.Edge>, ro(1n+q, dir, xs, bs, Nat.add(st, q), r), SC.append(E.Edge, GS.all_edges(dir, am), r), SC.append(E.Edge, SC.append(E.Edge, GS.all_edges(dir, am), o), acc),
        ro_all(dir, xs, bs, st, q, r, hxq, hbq, blocks_l(wb, Con{b, Nil{}}, hb2)),
        Equal.trans(List<&2, E.Edge>, SC.append(E.Edge, GS.all_edges(dir, am), r), SC.append(E.Edge, GS.all_edges(dir, am), SC.append(E.Edge, o, acc)), SC.append(E.Edge, SC.append(E.Edge, GS.all_edges(dir, am), o), acc),
          Equal.cong(List<&2, E.Edge>, List<&2, E.Edge>, z => SC.append(E.Edge, GS.all_edges(dir, am), z), r, SC.append(E.Edge, o, acc), ri_blk(b, dir, x, acc, ED.bk_perfect(b, bk), ED.bk_cap(b, bk))),
          Equal.sym(List<&2, E.Edge>, SC.append(E.Edge, SC.append(E.Edge, GS.all_edges(dir, am), o), acc), SC.append(E.Edge, GS.all_edges(dir, am), SC.append(E.Edge, o, acc)), LL.append_assoc(E.Edge, GS.all_edges(dir, am), o, acc))))

# ---- one step of the outer runtime loop ----

def ed_step_ok(+dir: Bool, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +acc: List<&2, E.Edge>, +j: Nat, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +pi: {AR.perfect(U32, depth, it) == True{} : Bool}, +pa: {AR.perfect(AR.Tree<U32>, depth, at) == True{} : Bool}, +hj: {Nat.is_lt(j, SC.pow2(depth)) == True{} : Bool}, +bk: {ST.blk_ok(ED.bnth(AR.slots(AR.Tree<U32>, at), j)) == True{} : Bool}) -> {G.ed_step(dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), acc, U32.from_nat(j)}) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ri(ST.bdeg(ED.bnth(AR.slots(AR.Tree<U32>, at), j)), AR.slots(U32, ED.bnth(AR.slots(AR.Tree<U32>, at), j)), Nat.add(2n, ST.bdeg(ED.bnth(AR.slots(AR.Tree<U32>, at), j))), dir, SH.val_at(AR.slots(U32, it), j), acc), U32.sub(U32.from_nat(j), 1)} : G.Ed}:
  +bs = AR.slots(AR.Tree<U32>, at)
  +bt = ED.bnth(bs, j)
  +u = SH.val_at(AR.slots(U32, it), j)
  +i = U32.from_nat(j)
  +lc = ST.blcap(bt)
  +dg = ST.bdeg(bt)
  +ej = U.to_nat_from_nat(j, depth, N.lt_le(depth, 32n, hd), hj)
  +hij = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(depth)) == True{} : Bool}, j, U32.to_nat(i), Equal.sym(Nat, U32.to_nat(i), j, ej), hj)
  +hl = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.pow2(depth), SC.length(AR.Tree<U32>, bs), Equal.sym(Nat, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pa)), hj)
  +hx = L.subst(Nat, z => {SC.nth(AR.Tree<U32>, bs, z) == Some{bt} : Maybe<&2, AR.Tree<U32>>}, j, U32.to_nat(i), Equal.sym(Nat, U32.to_nat(i), j, ej), bsome(bs, j, hl))
  +at1 = AR.upd(AR.Tree<U32>, depth, at, U32.to_nat(i), BK.leaf0())
  +bd = ED.bk_lt32(bt, bk)
  +bcap = ED.bk_cap(bt, bk)
  +bp = ED.bk_perfect(bt, bk)
  +h2 = N.lt_le_trans(Nat.add(2n, dg), Nat.add(3n, dg), SC.pow2(lc), N.lt_succ(Nat.add(2n, dg)), bcap)
  +e0 = BK.from_to(BK.v0(bt), lc, N.lt_le(lc, 32n, bd), N.lt_le_trans(dg, Nat.add(3n, dg), SC.pow2(lc), N.le_lt_trans(dg, Nat.add(2n, dg), Nat.add(3n, dg), BK.le_plus(2n, dg), N.lt_succ(Nat.add(2n, dg))), bcap))
  +el = Equal.cong(U32, U32, z => U32.inc(U32.inc(z)), U32.from_nat(dg), BK.v0(bt), e0)
  +r = ri(dg, AR.slots(U32, bt), Nat.add(2n, dg), dir, u, acc)
  %NB.get_at(j, depth, it, hd, pi, hj) : {G.ed_read(dir, A2.thaw2(at), acc, i, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(i, 1)} : G.Ed}
  %Equal.sym(Array<Array<U32>> & Array<U32>, Array.swap(Array<U32>, A2.thaw2(at), i, AR.thaw(U32, BK.leaf0())), (A2.thaw2(at1), AR.thaw(U32, bt)), A2.swap2(depth, at, i, BK.leaf0(), bt, hd, hij, hx, pa)) : {G.ed_blk(dir, AR.thaw(U32, it), acc, i, u, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(i, 1)} : G.Ed}
  %Equal.sym(G.Hdr, G.header(AR.thaw(U32, bt)), G.HD{AR.thaw(U32, bt), BK.v0(bt), BK.v1(bt), BK.v2(bt)}, BK.header_ok(bt, bd, ED.bk_two(bt, bk), bp)) : {G.ed_hdr(dir, AR.thaw(U32, it), A2.thaw2(at1), acc, i, u, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(i, 1)} : G.Ed}
  %el : {G.ed_fin(AR.thaw(U32, it), A2.thaw2(at1), i, G.ed_inner(dg, dir, u, acc, _, Array.get(U32, AR.thaw(U32, bt), _))) == G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(i, 1)} : G.Ed}
  %Equal.sym(Array<U32> & List<&2, E.Edge>, G.ed_inner(dg, dir, u, acc, U32.from_nat(Nat.add(2n, dg)), Array.get(U32, AR.thaw(U32, bt), U32.from_nat(Nat.add(2n, dg)))), (AR.thaw(U32, bt), r), ed_inner_ok(dg, dir, u, acc, Nat.add(2n, dg), lc, bt, bd, bp, h2, BK.le_plus(3n, dg))) : {G.ed_fin(AR.thaw(U32, it), A2.thaw2(at1), i, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(i, 1)} : G.Ed}
  Equal.cong(Array<Array<U32>>, G.Ed, z => G.ED{AR.thaw(U32, it), z, r, U32.sub(i, 1)}, Array.set(Array<U32>, A2.thaw2(at1), i, AR.thaw(U32, bt)), A2.thaw2(at), BK.swap_back(depth, at, i, bt, hd, hij, hx, pa))

# The index after m decrements (the last one may wrap: it is never read).
def ui(m: Nat, +i: U32) -> U32:
  match m:
    case 0n:
      i
    case 1n+p:
      ui(p, U32.sub(i, 1))

# ---- the outer runtime loop is ro ----

def ed_loop_ok(+p: Nat, +dir: Bool, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +st: Nat, +acc: List<&2, E.Edge>, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +pi: {AR.perfect(U32, depth, it) == True{} : Bool}, +pa: {AR.perfect(AR.Tree<U32>, depth, at) == True{} : Bool}, +hcap: {Nat.is_le(Nat.add(st, 1n+p), SC.pow2(depth)) == True{} : Bool}, +hb: {ST.blocks_ok(ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), st, 1n+p)) == True{} : Bool}) -> {G.ed_loop(1n+p, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), acc, U32.from_nat(Nat.add(st, p))}) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ro(1n+p, dir, AR.slots(U32, it), AR.slots(AR.Tree<U32>, at), Nat.add(st, p), acc), ui(1n+p, U32.from_nat(Nat.add(st, p)))} : G.Ed}:
  match p:
    case 0n:
      +bs = AR.slots(AR.Tree<U32>, at)
      +hlb = L.subst(Nat, z => {Nat.is_le(Nat.add(st, 1n+p), z) == True{} : Bool}, SC.pow2(depth), SC.length(AR.Tree<U32>, bs), Equal.sym(Nat, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pa)), hcap)
      +j = Nat.add(st, 0n)
      +hj1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}, Nat.add(st, 1n), 1n+j, N.add_succ(st, 0n), hlb)
      +ewb = win_one(AR.Tree<U32>, bs, st, ED.bnth(bs, j), bsome(bs, j, N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hj1)))
      +bk = L.and_left(ST.blk_ok(ED.bnth(bs, j)), True{}, L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, ST.win(AR.Tree<U32>, bs, st, 1n), Con{ED.bnth(bs, j), Nil{}}, ewb, hb))
      +hjd = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pa), N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hj1))
      %Equal.sym(G.Ed, G.ed_step(dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), acc, U32.from_nat(j)}), G.ED{AR.thaw(U32, it), A2.thaw2(at), ri(ST.bdeg(ED.bnth(bs, j)), AR.slots(U32, ED.bnth(bs, j)), Nat.add(2n, ST.bdeg(ED.bnth(bs, j))), dir, SH.val_at(AR.slots(U32, it), j), acc), U32.sub(U32.from_nat(j), 1)}, ed_step_ok(dir, depth, it, at, acc, j, hd, pi, pa, hjd, bk)) : {G.ed_loop(0n, dir, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ro(1n, dir, AR.slots(U32, it), bs, j, acc), ui(1n, U32.from_nat(j))} : G.Ed}
      {==}
    case 1n+q:
      +bs = AR.slots(AR.Tree<U32>, at)
      +hlb = L.subst(Nat, z => {Nat.is_le(Nat.add(st, 1n+p), z) == True{} : Bool}, SC.pow2(depth), SC.length(AR.Tree<U32>, bs), Equal.sym(Nat, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pa)), hcap)
      +j = Nat.add(st, 1n+q)
      +b = ED.bnth(bs, j)
      +hj1 = L.subst(Nat, z => {Nat.is_le(z, SC.length(AR.Tree<U32>, bs)) == True{} : Bool}, Nat.add(st, 2n+q), 1n+j, N.add_succ(st, 1n+q), hlb)
      +ewb = NB.win_snoc(AR.Tree<U32>, bs, st, 1n+q, b, bsome(bs, j, N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hj1)))
      +wb = ST.win(AR.Tree<U32>, bs, st, 1n+q)
      +hb2 = L.subst(List<&2, AR.Tree<U32>>, z => {ST.blocks_ok(z) == True{} : Bool}, ST.win(AR.Tree<U32>, bs, st, 2n+q), SC.append(AR.Tree<U32>, wb, Con{b, Nil{}}), ewb, hb)
      +bk = blocks_last(wb, b, hb2)
      +hjd = L.subst(Nat, z => {Nat.is_lt(j, z) == True{} : Bool}, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, pa), N.succ_le_lt(j, SC.length(AR.Tree<U32>, bs), hj1))
      +es = Equal.trans(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.sub(j, 1n)), U32.from_nat(Nat.add(st, q)),
        H.sub_bridge(j, 1n, depth, N.lt_le(depth, 32n, hd), hjd, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+Nat.add(st, q), j, Equal.sym(Nat, j, 1n+Nat.add(st, q), N.add_succ(st, q)), N.le_add_right(1n, Nat.add(st, q)))),
        Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(j, 1n), Nat.add(st, q), NB.sub_one_add(st, q)))
      +r = ri(ST.bdeg(b), AR.slots(U32, b), Nat.add(2n, ST.bdeg(b)), dir, SH.val_at(AR.slots(U32, it), j), acc)
      +hcq = N.le_trans(Nat.add(st, 1n+q), 1n+Nat.add(st, 1n+q), SC.pow2(depth), N.lt_le(Nat.add(st, 1n+q), 1n+Nat.add(st, 1n+q), N.lt_succ(Nat.add(st, 1n+q))), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(depth)) == True{} : Bool}, Nat.add(st, 2n+q), 1n+Nat.add(st, 1n+q), N.add_succ(st, 1n+q), hcap))
      %Equal.sym(G.Ed, G.ed_step(dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), acc, U32.from_nat(j)}), G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.sub(U32.from_nat(j), 1)}, ed_step_ok(dir, depth, it, at, acc, j, hd, pi, pa, hjd, bk)) : {G.ed_loop(1n+q, dir, _) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ro(2n+q, dir, AR.slots(U32, it), bs, j, acc), ui(2n+q, U32.from_nat(j))} : G.Ed}
      %Equal.sym(U32, U32.sub(U32.from_nat(j), 1), U32.from_nat(Nat.add(st, q)), es) : {G.ed_loop(1n+q, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), r, _}) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ro(2n+q, dir, AR.slots(U32, it), bs, j, acc), ui(1n+q, _)} : G.Ed}
      %Equal.sym(Nat, Nat.sub(j, 1n), Nat.add(st, q), NB.sub_one_add(st, q)) : {G.ed_loop(1n+q, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), r, U32.from_nat(Nat.add(st, q))}) == G.ED{AR.thaw(U32, it), A2.thaw2(at), ro(1n+q, dir, AR.slots(U32, it), bs, _, r), ui(1n+q, U32.from_nat(Nat.add(st, q)))} : G.Ed}
      ed_loop_ok(q, dir, depth, it, at, st, r, hd, pi, pa, hcq, blocks_l(wb, Con{b, Nil{}}, hb2))

# ---- edges ----

def span_nat(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))) == Nat.sub(hi, lo) : Nat}:
  +k = Nat.sub(hi, lo)
  +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
  +hb = N.lt_succ_le_succ(depth, 32n, hd)
  +hhi = N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), OP.g_cap(dir, lo, hi, depth, it, at, h), N.pow2_lt_succ(depth))
  Equal.trans(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), U32.to_nat(U32.from_nat(k)), k,
    Equal.cong(U32, Nat, z => U32.to_nat(z), U32.sub(U32.from_nat(hi), U32.from_nat(lo)), U32.from_nat(k), H.sub_bridge(hi, lo, 1n+depth, hb, hhi, OP.g_lohi(dir, lo, hi, depth, it, at, h))),
    U.to_nat_from_nat(k, 1n+depth, hb, N.le_lt_trans(k, hi, SC.pow2(1n+depth), H.sub_le(hi, lo), hhi)))

def last_u32(+lo: Nat, +hi: Nat, +depth: Nat, +p: Nat, +hd: {Nat.is_lt(depth, 32n) == True{} : Bool}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hcap: {Nat.is_le(hi, SC.pow2(depth)) == True{} : Bool}, +ek: {Nat.sub(hi, lo) == 1n+p : Nat}) -> {U32.sub(U32.from_nat(hi), 1) == U32.from_nat(Nat.add(lo, p)) : U32}:
  +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
  +h1 = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, Nat.add(lo, 1n+p), hi, eh, L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+Nat.add(lo, p), Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), 1n+Nat.add(lo, p), N.add_succ(lo, p)), N.le_add_right(1n, Nat.add(lo, p))))
  Equal.trans(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(Nat.sub(hi, 1n)), U32.from_nat(Nat.add(lo, p)),
    H.sub_bridge(hi, 1n, 1n+depth, N.lt_succ_le_succ(depth, 32n, hd), N.le_lt_trans(hi, SC.pow2(depth), SC.pow2(1n+depth), hcap, N.pow2_lt_succ(depth)), h1),
    Equal.cong(Nat, U32, z => U32.from_nat(z), Nat.sub(hi, 1n), Nat.add(lo, p), NB.last_idx(lo, hi, p, ek, hlo)))

def ed_case(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}, k: Nat, +ek: {Nat.sub(hi, lo) == k : Nat}) -> {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, G.ed_loop(k, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, U32.sub(U32.from_nat(hi), 1)})) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, k), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, k)))) : G.Graph & List<&2, E.Edge>}:
  match k:
    case 0n:
      %Equal.sym(List<&2, U32>, ST.win(U32, AR.slots(U32, it), lo, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, AR.slots(U32, it), lo))) : {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, U32.sub(U32.from_nat(hi), 1)}) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(_, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, 0n)))) : G.Graph & List<&2, E.Edge>}
      %Equal.sym(List<&2, AR.Tree<U32>>, ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, 0n), Nil{}, LL.sc_take_zero(AR.Tree<U32>, SC.drop(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo))) : {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, U32.sub(U32.from_nat(hi), 1)}) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(Nil{}, _))) : G.Graph & List<&2, E.Edge>}
      {==}
    case 1n+ +p:
      +xs = AR.slots(U32, it)
      +bs = AR.slots(AR.Tree<U32>, at)
      +hd = ED.dep32(dir, lo, hi, depth, it, at, h)
      +hlo = OP.g_lohi(dir, lo, hi, depth, it, at, h)
      +hcap = OP.g_cap(dir, lo, hi, depth, it, at, h)
      +eh = W.window_end(lo, hi, 1n+p, Equal.sym(Nat, Nat.sub(hi, lo), 1n+p, ek), hlo)
      +hc = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(depth)) == True{} : Bool}, hi, Nat.add(lo, 1n+p), Equal.sym(Nat, Nat.add(lo, 1n+p), hi, eh), hcap)
      +hxs = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+p), z) == True{} : Bool}, SC.pow2(depth), SC.length(U32, xs), Equal.sym(Nat, SC.length(U32, xs), SC.pow2(depth), AR.slots_length(U32, depth, it, OP.g_ids(dir, lo, hi, depth, it, at, h))), hc)
      +hbs = L.subst(Nat, z => {Nat.is_le(Nat.add(lo, 1n+p), z) == True{} : Bool}, SC.pow2(depth), SC.length(AR.Tree<U32>, bs), Equal.sym(Nat, SC.length(AR.Tree<U32>, bs), SC.pow2(depth), AR.slots_length(AR.Tree<U32>, depth, at, OP.g_adj(dir, lo, hi, depth, it, at, h))), hc)
      +hb = L.subst(Nat, z => {ST.blocks_ok(ST.win(AR.Tree<U32>, bs, lo, z)) == True{} : Bool}, Nat.sub(hi, lo), 1n+p, ek, OP.g_blocks(dir, lo, hi, depth, it, at, h))
      +r = ro(1n+p, dir, xs, bs, Nat.add(lo, p), Nil{})
      %Equal.sym(U32, U32.sub(U32.from_nat(hi), 1), U32.from_nat(Nat.add(lo, p)), last_u32(lo, hi, depth, p, hd, hlo, hcap, ek)) : {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, G.ed_loop(1n+p, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, _})) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p)))) : G.Graph & List<&2, E.Edge>}
      %Equal.sym(G.Ed, G.ed_loop(1n+p, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, U32.from_nat(Nat.add(lo, p))}), G.ED{AR.thaw(U32, it), A2.thaw2(at), r, ui(1n+p, U32.from_nat(Nat.add(lo, p)))}, ed_loop_ok(p, dir, depth, it, at, lo, Nil{}, hd, OP.g_ids(dir, lo, hi, depth, it, at, h), OP.g_adj(dir, lo, hi, depth, it, at, h), hc, hb)) : {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, _) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p)))) : G.Graph & List<&2, E.Edge>}
      Equal.cong(List<&2, E.Edge>, G.Graph & List<&2, E.Edge>, z => (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), z), r, GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p))),
        Equal.trans(List<&2, E.Edge>, r, SC.append(E.Edge, GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p))), Nil{}), GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p))),
          ro_all(dir, xs, bs, lo, p, Nil{}, hxs, hbs, hb),
          LL.append_nil(E.Edge, GS.all_edges(dir, ST.amodel(ST.win(U32, xs, lo, 1n+p), ST.win(AR.Tree<U32>, bs, lo, 1n+p))))))

# edges refines the specification and returns the state unchanged.
def edges_ok(+dir: Bool, +lo: Nat, +hi: Nat, +depth: Nat, +it: AR.Tree<U32>, +at: AR.Tree<AR.Tree<U32>>, +h: {ST.good(ST.Sh{dir, lo, hi, depth, it, at}) == True{} : Bool}) -> {G.edges(ST.real(ST.Sh{dir, lo, hi, depth, it, at})) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))) : G.Graph & List<&2, E.Edge>}:
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.from_nat(hi), U32.from_nat(lo))), Nat.sub(hi, lo), span_nat(dir, lo, hi, depth, it, at, h)) : {G.ed_done(dir, U32.from_nat(lo), U32.from_nat(hi), U.pow2u(depth), depth, G.ed_loop(_, dir, G.ED{AR.thaw(U32, it), A2.thaw2(at), Nil{}, U32.sub(U32.from_nat(hi), 1)})) == (ST.real(ST.Sh{dir, lo, hi, depth, it, at}), GS.all_edges(dir, ST.amodel(ST.win(U32, AR.slots(U32, it), lo, Nat.sub(hi, lo)), ST.win(AR.Tree<U32>, AR.slots(AR.Tree<U32>, at), lo, Nat.sub(hi, lo))))) : G.Graph & List<&2, E.Edge>}
  ed_case(dir, lo, hi, depth, it, at, h, Nat.sub(hi, lo), {==})
