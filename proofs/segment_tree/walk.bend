import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../lib/u32alg.bend as UA
import ../../spec/common.bend as SC
import ../../src/segment_tree.bend as SG
import ../../src/internal/vec.bend as V
import ./node.bend as TN
import ./arr.bend as AR
import ./model.bend as MD

# The flat layout of src/segment_tree.bend: which cells of the two arrays
# hold which part of the model tree, and that the index walks of the source
# are exactly the tree walks of node.bend.
#
#   * the value of index t is cells[2^d + t];
#   * the block [o, o + 2^p) (p >= 1) keeps its total in cells[o + 2^(p-1)]
#     and its lazy tag in tags[o + 2^(p-1)].
#
# proofs/lib/flat.bend has the interval arithmetic this layout rests on.

def vsc(k: Nat) -> {V.pow2(k) == SC.pow2(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, V.pow2(p), SC.pow2(p), vsc(p))

def vdec(q: Nat, +i: Nat, +hh: Nat, +ehh: {hh == FL.hof(q) : Nat}) -> {Nat.is_lt(i, hh) == V.dec(q, i) : Bool}:
  match q:
    case 0n:
      %Equal.sym(Nat, hh, FL.hof(0n), ehh) : {Nat.is_lt(i, _) == False{} : Bool}
      N.not_lt_zero(i)
    case 1n+ +r:
      %Equal.sym(Nat, hh, FL.hof(1n+r), ehh) : {Nat.is_lt(i, _) == Nat.is_lt(i, V.pow2(r)) : Bool}
      %Equal.sym(Nat, FL.hof(1n+r), SC.pow2(r), FL.hof_succ(r)) : {Nat.is_lt(i, _) == Nat.is_lt(i, V.pow2(r)) : Bool}
      %Equal.sym(Nat, V.pow2(r), SC.pow2(r), vsc(r)) : {Nat.is_lt(i, SC.pow2(r)) == Nat.is_lt(i, _) : Bool}
      {==}

# ---- the model tree the two arrays realise ----

def tree_of(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat) -> TN.Node:
  match p:
    case 0n:
      TN.SLeaf{FL.nthc(cl, Nat.add(SC.pow2(d), o))}
    case 1n+ +q:
      TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))}

# A block's total is the cell at its total index.
def total_at(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, q: Nat, +o: Nat, +hq: Nat, +ehq: {hq == FL.hof(q) : Nat}) -> {TN.total(tree_of(cl, gl, d, q, o)) == FL.nthc(cl, SG.cell_of(q, SC.pow2(d), hq, o)) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      %Equal.sym(Nat, hq, FL.hof(1n+r), ehq) : {FL.nthc(cl, Nat.add(o, SC.pow2(r))) == FL.nthc(cl, Nat.add(o, _)) : U32}
      %Equal.sym(Nat, FL.hof(1n+r), SC.pow2(r), FL.hof_succ(r)) : {FL.nthc(cl, Nat.add(o, SC.pow2(r))) == FL.nthc(cl, Nat.add(o, _)) : U32}
      {==}

def tree_perfect(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat) -> {MD.perfect(p, tree_of(cl, gl, d, p, o)) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      L.and_intro(MD.perfect(q, tree_of(cl, gl, d, q, o)), MD.perfect(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))),
        tree_perfect(cl, gl, d, q, o), tree_perfect(cl, gl, d, q, Nat.add(o, SC.pow2(q))))

# ---- one cell changed: when does the tree of a block not notice? ----

def frame_c_lo(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(j, o) == True{} : Bool}, +hjd: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, j, v), gl, d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc_other(cl, j, Nat.add(SC.pow2(d), o), v, N.is_eq_lt(j, Nat.add(SC.pow2(d), o), N.lt_le_trans(j, SC.pow2(d), Nat.add(SC.pow2(d), o), hjd, FL.base_le(d, o)))))
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc_other(cl, j, Nat.add(o, SC.pow2(q)), v, N.is_eq_lt(j, Nat.add(o, SC.pow2(q)), N.le_lt_trans(j, o, Nat.add(o, SC.pow2(q)), hj, FL.lt_split(o, q))))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(cl, gl, d, q, o),
            frame_c_lo(cl, gl, d, q, o, j, v, hj, hjd)),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_c_lo(cl, gl, d, q, Nat.add(o, SC.pow2(q)), j, v, N.le_trans(j, o, Nat.add(o, SC.pow2(q)), hj, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), hjd))))

def frame_c_hi(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(Nat.add(o, SC.pow2(p)), j) == True{} : Bool}, +hjd: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, j, v), gl, d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc_other(cl, j, Nat.add(SC.pow2(d), o), v, N.is_eq_lt(j, Nat.add(SC.pow2(d), o), N.lt_le_trans(j, SC.pow2(d), Nat.add(SC.pow2(d), o), hjd, FL.base_le(d, o)))))
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc_other(cl, j, Nat.add(o, SC.pow2(q)), v, FL.ne_gt(j, Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, FL.mid_lt(o, q), hj)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, j, v), gl, d, q, o), tree_of(cl, gl, d, q, o),
            frame_c_hi(cl, gl, d, q, o, j, v, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hj), hjd)),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(SC.update(U32, cl, j, v), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_c_hi(cl, gl, d, q, Nat.add(o, SC.pow2(q)), j, v, L.subst(Nat, k => {Nat.is_le(k, j) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hj), hjd))))

def frame_v_lo(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +t: Nat, +v: U32, +ht: {Nat.is_lt(t, o) == True{} : Bool}, +hblk: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), v, N.is_eq_lt(Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), N.lt_add_left(t, o, SC.pow2(d), ht))))
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), Nat.add(SC.pow2(d), t), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hblk), FL.base_le(d, t))))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(cl, gl, d, q, o),
            frame_v_lo(cl, gl, d, q, o, t, v, ht, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hblk))),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_v_lo(cl, gl, d, q, Nat.add(o, SC.pow2(q)), t, v, N.lt_le_trans(t, o, Nat.add(o, SC.pow2(q)), ht, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), L.subst(Nat, k => {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hblk)))))

def frame_v_hi(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +t: Nat, +v: U32, +ht: {Nat.is_le(Nat.add(o, SC.pow2(p)), t) == True{} : Bool}, +hblk: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), N.lt_add_left(o, t, SC.pow2(d), N.succ_le_lt(o, t, L.subst(Nat, k => {Nat.is_le(k, t) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), ht))))))
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), Nat.add(SC.pow2(d), t), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hblk), FL.base_le(d, t))))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, o), tree_of(cl, gl, d, q, o),
            frame_v_hi(cl, gl, d, q, o, t, v, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), t, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), ht), N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hblk))),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_v_hi(cl, gl, d, q, Nat.add(o, SC.pow2(q)), t, v, L.subst(Nat, k => {Nat.is_le(k, t) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), ht), L.subst(Nat, k => {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hblk)))))

def frame_g_lo(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(j, o) == True{} : Bool}) -> {tree_of(cl, SC.update(U32, gl, j, v), d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), {==})
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(SC.update(U32, gl, j, v), Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, gl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), FL.nthc_other(gl, j, Nat.add(o, SC.pow2(q)), v, N.is_eq_lt(j, Nat.add(o, SC.pow2(q)), N.le_lt_trans(j, o, Nat.add(o, SC.pow2(q)), hj, FL.lt_split(o, q))))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, gl, d, q, o),
            frame_g_lo(cl, gl, d, q, o, j, v, hj)),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_g_lo(cl, gl, d, q, Nat.add(o, SC.pow2(q)), j, v, N.le_trans(j, o, Nat.add(o, SC.pow2(q)), hj, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q)))))))

def frame_g_hi(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(Nat.add(o, SC.pow2(p)), j) == True{} : Bool}) -> {tree_of(cl, SC.update(U32, gl, j, v), d, p, o) == tree_of(cl, gl, d, p, o) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(cl, Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)), {==})
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(SC.update(U32, gl, j, v), Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.update(U32, gl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), FL.nthc_other(gl, j, Nat.add(o, SC.pow2(q)), v, FL.ne_gt(j, Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, FL.mid_lt(o, q), hj)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(cl, SC.update(U32, gl, j, v), d, q, o), tree_of(cl, gl, d, q, o),
            frame_g_hi(cl, gl, d, q, o, j, v, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hj))),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, o), z},
            tree_of(cl, SC.update(U32, gl, j, v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            frame_g_hi(cl, gl, d, q, Nat.add(o, SC.pow2(q)), j, v, L.subst(Nat, k => {Nat.is_le(k, j) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hj)))))

# ---- the walks of the source are the model's ----

# o + 2^q < 2^d for a block [o, o + 2^(1+q)) that fits
def node_lt_d(+o: Nat, +q: Nat, +d: Nat, +hw: {Nat.is_le(Nat.add(o, SC.pow2(1n+q)), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)

def get_ok(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {SG.get_go(p, SG.pre_t(p, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, h, o), base, h, hh, acc, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(p, tree_of(AR.cl(tc), AR.cl(tg), d, p, o), i, acc, left))) : Array<SG.Cel> & Array<SG.Cel> & U32}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.get_go(0n, SG.mk_c(Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(_, o))), A.thaw(SG.Cel, tg)), base, h, hh, acc, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(SC.pow2(d), o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))), AR.get_ok(1n+d, tc, Nat.add(SC.pow2(d), o), hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)) : {SG.get_go(0n, SG.mk_c(_, A.thaw(SG.Cel, tg)), base, h, hh, acc, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))), FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), AR.cval_cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))) : {(A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(_, acc))) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      {==}
    case 1n+ +q True{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.get_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc)), base, h, hh, acc, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{}))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.get_go(1n+q, SG.mk_g(_, A.thaw(SG.Cel, tc)), base, h, hh, acc, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{}))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, o), base, hh, Nat.div(hh, 2n), U32.add(acc, _), o, i, Nat.is_lt(i, hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, o), i, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, i)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(i, hh), V.dec(q, i), vdec(q, i, hh, ehq)) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, o), base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, _) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, o), i, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, i)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      get_ok(q, tc, tg, d, base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, V.dec(q, i), hd, hdg,
        N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc, pfg, eb, ehq, {==})
    case 1n+ +q False{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.get_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc)), base, h, hh, acc, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{}))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.get_go(1n+q, SG.mk_g(_, A.thaw(SG.Cel, tc)), base, h, hh, acc, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{}))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, Nat.add(o, _)), base, hh, Nat.div(hh, 2n), U32.add(acc, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q))))), Nat.add(o, _), Nat.sub(i, _), Nat.is_lt(Nat.sub(i, _), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{}))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Nat, V.pow2(q), SC.pow2(q), vsc(q)) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q))))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, _), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, _))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, _), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, SC.pow2(q)))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh), V.dec(q, Nat.sub(i, SC.pow2(q))), vdec(q, Nat.sub(i, SC.pow2(q)), hh, ehq)) : {SG.get_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), _) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), TN.get_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, SC.pow2(q)))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      get_ok(q, tc, tg, d, base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), V.dec(q, Nat.sub(i, SC.pow2(q))), hd, hdg,
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pfc, pfg, eb, ehq, {==})

# the cell holding a block's total is inside the cell array
def cell_lt(q: Nat, +o: Nat, +d: Nat, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o), SC.pow2(1n+d)) == True{} : Bool}:
  match q:
    case 0n:
      FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw))
    case 1n+ +r:
      %Equal.sym(Nat, Nat.div(SC.pow2(1n+r), 2n), SC.pow2(r), FL.hof_succ(r)) : {Nat.is_lt(Nat.add(o, _), SC.pow2(1n+d)) == True{} : Bool}
      N.lt_trans(Nat.add(o, SC.pow2(r)), SC.pow2(d), SC.pow2(1n+d),
        N.lt_le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), SC.pow2(d), FL.mid_lt(o, r), hw), FL.base_lt(d))

def sleaf(+x: U32, i: Nat) -> {SG.leaf_prefix(x, i) == TN.leaf_prefix(x, i) : U32}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

def prefix_ok(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +sum: U32, +o: Nat, +i: Nat, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {SG.prefix_go(p, SG.pre_p(p, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, h, o), base, h, hh, acc, sum, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(p, tree_of(AR.cl(tc), AR.cl(tg), d, p, o), i, acc, left)))) : Array<SG.Cel> & Array<SG.Cel> & U32}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.prefix_go(0n, SG.p4c(Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(_, o))), A.thaw(SG.Cel, tg)), base, h, hh, acc, sum, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(SC.pow2(d), o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))), AR.get_ok(1n+d, tc, Nat.add(SC.pow2(d), o), hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)) : {SG.prefix_go(0n, SG.p4c(_, A.thaw(SG.Cel, tg)), base, h, hh, acc, sum, o, i, left) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))), FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), AR.cval_cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))) : {(A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, SG.leaf_prefix(U32.add(_, acc), i)))) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.leaf_prefix(U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), acc), i), TN.leaf_prefix(U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), acc), i), sleaf(U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), acc), i)) : {(A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, _))) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(0n, tree_of(AR.cl(tc), AR.cl(tg), d, 0n, o), i, acc, left)))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      {==}
    case 1n+ +q True{}:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.prefix_go(1n+q, SG.p4g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, h))), A.thaw(SG.Cel, tc), _, Nat.div(h, 2n), o, q), _, h, hh, acc, sum, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.prefix_go(1n+q, SG.p4g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc), SC.pow2(d), Nat.div(_, 2n), o, q), SC.pow2(d), h, hh, acc, sum, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.prefix_go(1n+q, SG.p4g(_, A.thaw(SG.Cel, tc), SC.pow2(d), Nat.div(SC.pow2(q), 2n), o, q), SC.pow2(d), h, hh, acc, sum, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), AR.get_ok(1n+d, tc, SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o), hd, cell_lt(q, o, d, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw))), pfc)) : {SG.prefix_go(1n+q, SG.p4both(_, A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), SC.pow2(d), h, hh, acc, sum, o, i, True{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, True{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, o), SC.pow2(d), hh, Nat.div(hh, 2n), U32.add(acc, _), sum, o, i, Nat.is_lt(i, hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, o), i, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, i))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(i, hh), V.dec(q, i), vdec(q, i, hh, ehq)) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, o), SC.pow2(d), hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), sum, o, i, _) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, o), i, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), V.dec(q, i))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      prefix_ok(q, tc, tg, d, SC.pow2(d), hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), sum, o, i, V.dec(q, i), hd, hdg,
        N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc, pfg, {==}, ehq, {==})
    case 1n+ +q False{}:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.prefix_go(1n+q, SG.p4g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, h))), A.thaw(SG.Cel, tc), _, Nat.div(h, 2n), o, q), _, h, hh, acc, sum, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      +NEWACC = U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))))
      +NEWSUM = U32.add(sum, U32.add(TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), U32.shln(U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), q)))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.prefix_go(1n+q, SG.p4g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc), SC.pow2(d), Nat.div(_, 2n), o, q), SC.pow2(d), h, hh, acc, sum, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.prefix_go(1n+q, SG.p4g(_, A.thaw(SG.Cel, tc), SC.pow2(d), Nat.div(SC.pow2(q), 2n), o, q), SC.pow2(d), h, hh, acc, sum, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), AR.get_ok(1n+d, tc, SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o), hd, cell_lt(q, o, d, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw))), pfc)) : {SG.prefix_go(1n+q, SG.p4both(_, A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), SC.pow2(d), h, hh, acc, sum, o, i, False{}) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, _)), SC.pow2(d), hh, Nat.div(hh, 2n), U32.add(acc, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q))))), U32.add(sum, U32.add(SG.cval(AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), U32.shln(U32.add(acc, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q))))), q))), Nat.add(o, _), Nat.sub(i, _), Nat.is_lt(Nat.sub(i, _), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, SC.pow2(q))), SC.pow2(d), hh, Nat.div(hh, 2n), U32.add(acc, _), U32.add(sum, U32.add(SG.cval(AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), U32.shln(U32.add(acc, _), q))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), Equal.trans(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o))), FL.nthc(AR.cl(tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o)), TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), AR.cval_cels(A.slots(SG.Cel, tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o)), Equal.sym(U32, TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), FL.nthc(AR.cl(tc), SG.cell_of(q, SC.pow2(d), Nat.div(SC.pow2(q), 2n), o)), total_at(AR.cl(tc), AR.cl(tg), d, q, o, Nat.div(SC.pow2(q), 2n), {==})))) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, SC.pow2(q))), SC.pow2(d), hh, Nat.div(hh, 2n), NEWACC, U32.add(sum, U32.add(_, U32.shln(NEWACC, q))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, TN.prefix_go(1n+q, tree_of(AR.cl(tc), AR.cl(tg), d, 1n+q, o), i, acc, False{})))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Nat, V.pow2(q), SC.pow2(q), vsc(q)) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, SC.pow2(q))), SC.pow2(d), hh, Nat.div(hh, 2n), NEWACC, NEWSUM, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, U32.add(U32.add(TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), U32.shln(NEWACC, q)), TN.prefix_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, _), NEWACC, V.dec(q, Nat.sub(i, _))))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh), V.dec(q, Nat.sub(i, SC.pow2(q))), vdec(q, Nat.sub(i, SC.pow2(q)), hh, ehq)) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, SC.pow2(q))), SC.pow2(d), hh, Nat.div(hh, 2n), NEWACC, NEWSUM, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), _) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), U32.add(sum, U32.add(U32.add(TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), U32.shln(NEWACC, q)), TN.prefix_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), NEWACC, V.dec(q, Nat.sub(i, SC.pow2(q)))))))) : Array<SG.Cel> & Array<SG.Cel> & U32}
      %UA.assoc(sum, U32.add(TN.total(tree_of(AR.cl(tc), AR.cl(tg), d, q, o)), U32.shln(NEWACC, q)), TN.prefix_go(q, tree_of(AR.cl(tc), AR.cl(tg), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), NEWACC, V.dec(q, Nat.sub(i, SC.pow2(q))))) : {SG.prefix_go(q, SG.pre_p(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.add(o, SC.pow2(q))), SC.pow2(d), hh, Nat.div(hh, 2n), NEWACC, NEWSUM, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), V.dec(q, Nat.sub(i, SC.pow2(q)))) == (A.thaw(SG.Cel, tc), (A.thaw(SG.Cel, tg), _)) : Array<SG.Cel> & Array<SG.Cel> & U32}
      prefix_ok(q, tc, tg, d, SC.pow2(d), hh, Nat.div(hh, 2n), NEWACC, NEWSUM, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), V.dec(q, Nat.sub(i, SC.pow2(q))), hd, hdg,
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pfc, pfg, {==}, ehq, {==})

# ---- the set walk, at the level of cells ----
#
# `set` never writes a tag: it walks down accumulating them, writes the leaf
# and recomputes the sums of the blocks on the way back up.

def hq_of(+q: Nat) -> Nat:
  Nat.div(SC.pow2(q), 2n)

def cix(+q: Nat, +d: Nat, +o: Nat) -> Nat:
  SG.cell_of(q, SC.pow2(d), hq_of(q), o)

# the sum a block's cell must hold once its children are right
def upsum(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +q: Nat, +o: Nat) -> U32:
  U32.add(U32.add(FL.nthc(cl, cix(q, d, o)), FL.nthc(cl, cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q))

def fixc(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +q: Nat, +o: Nat) -> List<&2, U32>:
  SC.update(U32, cl, Nat.add(o, SC.pow2(q)), upsum(cl, gl, d, q, o))

def scells(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool) -> List<&2, U32>:
  match p left:
    case 0n _:
      SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.sub(v, acc))
    case 1n+ +q True{}:
      fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o)
    case 1n+ +q False{}:
      fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o)

def scells_length(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool) -> {SC.length(U32, scells(p, cl, gl, d, acc, o, i, v, left)) == SC.length(U32, cl) : Nat}:
  match p left:
    case 0n _:
      LL.length_update(U32, cl, Nat.add(SC.pow2(d), o), U32.sub(v, acc))
    case 1n+ +q True{}:
      Equal.trans(Nat,
        SC.length(U32, fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o)),
        SC.length(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))),
        SC.length(U32, cl),
        LL.length_update(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o)),
        scells_length(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)))
    case 1n+ +q False{}:
      Equal.trans(Nat,
        SC.length(U32, fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o)),
        SC.length(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
        SC.length(U32, cl),
        LL.length_update(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o)),
        scells_length(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))))

# A cell below the walked block never changes.
def scells_cell_lo(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(k, o) == True{} : Bool}, +hkd: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}) -> {FL.nthc(scells(p, cl, gl, d, acc, o, i, v, left), k) == FL.nthc(cl, k) : U32}:
  match p left:
    case 0n _:
      FL.nthc_other(cl, Nat.add(SC.pow2(d), o), k, U32.sub(v, acc),
        FL.ne_gt(Nat.add(SC.pow2(d), o), k, N.lt_le_trans(k, SC.pow2(d), Nat.add(SC.pow2(d), o), hkd, FL.base_le(d, o))))
    case 1n+ +q True{}:
      Equal.trans(U32, FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), k), FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), k), FL.nthc(cl, k),
        FL.nthc_other(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), k, upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
          FL.ne_gt(Nat.add(o, SC.pow2(q)), k, N.le_lt_trans(k, o, Nat.add(o, SC.pow2(q)), hk, FL.lt_split(o, q)))),
        scells_cell_lo(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), k, hk, hkd))
    case 1n+ +q False{}:
      Equal.trans(U32, FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), k), FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), k), FL.nthc(cl, k),
        FL.nthc_other(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), k, upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
          FL.ne_gt(Nat.add(o, SC.pow2(q)), k, N.le_lt_trans(k, o, Nat.add(o, SC.pow2(q)), hk, FL.lt_split(o, q)))),
        scells_cell_lo(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), k,
          N.le_trans(k, o, Nat.add(o, SC.pow2(q)), hk, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), hkd))

# A cell at or above the end of the walked block never changes.
def scells_cell_hi(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(Nat.add(o, SC.pow2(p)), k) == True{} : Bool}, +hkd: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}) -> {FL.nthc(scells(p, cl, gl, d, acc, o, i, v, left), k) == FL.nthc(cl, k) : U32}:
  match p left:
    case 0n _:
      FL.nthc_other(cl, Nat.add(SC.pow2(d), o), k, U32.sub(v, acc),
        FL.ne_gt(Nat.add(SC.pow2(d), o), k, N.lt_le_trans(k, SC.pow2(d), Nat.add(SC.pow2(d), o), hkd, FL.base_le(d, o))))
    case 1n+ +q True{}:
      Equal.trans(U32, FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), k), FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), k), FL.nthc(cl, k),
        FL.nthc_other(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), k, upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
          N.is_eq_lt(Nat.add(o, SC.pow2(q)), k, N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, FL.mid_lt(o, q), hk))),
        scells_cell_hi(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), k,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hk), hkd))
    case 1n+ +q False{}:
      Equal.trans(U32, FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), k), FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), k), FL.nthc(cl, k),
        FL.nthc_other(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), k, upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
          N.is_eq_lt(Nat.add(o, SC.pow2(q)), k, N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, FL.mid_lt(o, q), hk))),
        scells_cell_hi(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), k,
          L.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hk), hkd))

# The tree of a block the set walk stays out of does not change.
def scells_tree_hi(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o, SC.pow2(p)), o2) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(scells(p, cl, gl, d, acc, o, i, v, left), gl, d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match p left:
    case 0n _:
      frame_v_lo(cl, gl, d, p2, o2, o, U32.sub(v, acc),
        N.succ_le_lt(o, o2, L.subst(Nat, k => {Nat.is_le(k, o2) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), hsep)), hq)
    case 1n+ +q True{}:
      Equal.trans(TN.Node, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, p2, o2), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, p2, o2), tree_of(cl, gl, d, p2, o2),
        frame_c_lo(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          node_lt_d(o, q, d, hw)),
        scells_tree_hi(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), p2, o2,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq))
    case 1n+ +q False{}:
      Equal.trans(TN.Node, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, p2, o2), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, p2, o2), tree_of(cl, gl, d, p2, o2),
        frame_c_lo(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          node_lt_d(o, q, d, hw)),
        scells_tree_hi(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
          L.subst(Nat, z => {Nat.is_le(z, o2) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hsep),
          L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq))

def scells_tree_lo(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), o) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(scells(p, cl, gl, d, acc, o, i, v, left), gl, d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match p left:
    case 0n _:
      frame_v_hi(cl, gl, d, p2, o2, o, U32.sub(v, acc), hsep, hq)
    case 1n+ +q True{}:
      Equal.trans(TN.Node, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, p2, o2), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, p2, o2), tree_of(cl, gl, d, p2, o2),
        frame_c_hi(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          node_lt_d(o, q, d, hw)),
        scells_tree_lo(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), p2, o2, hsep,
          N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq))
    case 1n+ +q False{}:
      Equal.trans(TN.Node, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, p2, o2), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, p2, o2), tree_of(cl, gl, d, p2, o2),
        frame_c_hi(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          node_lt_d(o, q, d, hw)),
        scells_tree_lo(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq))

# ---- the set walk is the model's ----

def set_ok(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}) -> {tree_of(scells(p, cl, gl, d, acc, o, i, v, left), gl, d, p, o) == TN.set_go(p, tree_of(cl, gl, d, p, o), i, v, acc, left) : TN.Node}:
  match p left:
    case 0n _:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z},
        FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.sub(v, acc)), Nat.add(SC.pow2(d), o)), U32.sub(v, acc),
        FL.nthc_same(cl, Nat.add(SC.pow2(d), o), U32.sub(v, acc), FL.leaf_in_cells(cl, d, o, FL.blk_lo(o, 0n, d, hw), hlen)))
    case 1n+ +q True{}:
      +hm = node_lt_d(o, q, d, hw)
      +hwl = N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw)
      +hlen2 = Equal.trans(Nat, SC.length(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), SC.length(U32, cl), SC.pow2(1n+d), scells_length(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), hlen)
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.node(q, TN.set_go(q, tree_of(cl, gl, d, q, o), i, v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), Nat.add(o, SC.pow2(q))), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
            FL.nthc_same(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.in_cells(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), d, Nat.add(o, SC.pow2(q)), hm, hlen2))),
          Equal.trans(TN.Node,
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
              tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o),
              frame_c_hi(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), z},
              tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q))),
              frame_c_lo(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)))),
        %total_at(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o, hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(_, FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.set_go(q, tree_of(cl, gl, d, q, o), i, v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %total_at(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)), hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o)), _), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.set_go(q, tree_of(cl, gl, d, q, o), i, v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        Equal.trans(TN.Node,
          TN.SNode{U32.add(U32.add(TN.total(tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o)), TN.total(tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.node(q, tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, TN.set_go(q, tree_of(cl, gl, d, q, o), i, v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), z, FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            scells_tree_hi(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), q, Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q))), hwl, hwr)),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, z, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, o), i, v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, i)),
            set_ok(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), hwl, hlen))))
    case 1n+ +q False{}:
      +hm = node_lt_d(o, q, d, hw)
      +hwl = N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw)
      +hlen2 = Equal.trans(Nat, SC.length(U32, scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), SC.length(U32, cl), SC.pow2(1n+d), scells_length(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), hlen)
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)))},
        TN.node(q, tree_of(cl, gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            FL.nthc(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), Nat.add(o, SC.pow2(q))), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
            FL.nthc_same(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.in_cells(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, Nat.add(o, SC.pow2(q)), hm, hlen2))),
          Equal.trans(TN.Node,
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q)))},
              tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o),
              frame_c_hi(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o, Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), z},
              tree_of(fixc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), gl, d, q, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))),
              frame_c_lo(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(q)), upsum(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)))),
        %total_at(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o, hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(_, FL.nthc(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, tree_of(cl, gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %total_at(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)), hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o)), _), U32.shln(FL.nthc(gl, Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, tree_of(cl, gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %Equal.sym(Nat, V.pow2(q), SC.pow2(q), vsc(q)) : {TN.node(q, tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) == TN.node(q, tree_of(cl, gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, _), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, _))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        Equal.trans(TN.Node,
          TN.node(q, tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, tree_of(cl, gl, d, q, o), tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, tree_of(cl, gl, d, q, o), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, SC.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, z, tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, o), tree_of(cl, gl, d, q, o),
            scells_tree_lo(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), q, o, N.le_refl(Nat.add(o, SC.pow2(q))), hwr, hwl)),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, tree_of(cl, gl, d, q, o), z, FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(scells(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), gl, d, q, Nat.add(o, SC.pow2(q))), TN.set_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), V.dec(q, Nat.sub(i, SC.pow2(q)))),
            set_ok(q, cl, gl, d, U32.add(acc, FL.nthc(gl, Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), hwr, hlen))))

# ---- the lazy range-add walk, at the level of cells ----

def leafp(+cl: List<&2, U32>, +k: Nat, i: Nat, +v: U32) -> List<&2, U32>:
  match i:
    case 0n:
      cl
    case 1n+j:
      SC.update(U32, cl, k, U32.add(FL.nthc(cl, k), v))

# tagging a whole block: its sum grows by v * 2^q, its tag by v
def tcells(q: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +v: U32) -> List<&2, U32>:
  match q:
    case 0n:
      SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v))
    case 1n+ +r:
      SC.update(U32, cl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)))

def ttags(q: Nat, +gl: List<&2, U32>, +o: Nat, +v: U32) -> List<&2, U32>:
  match q:
    case 0n:
      gl
    case 1n+ +r:
      SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v))

def ptags(p: Nat, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> List<&2, U32>:
  match p left:
    case 0n _:
      gl
    case 1n+ +q True{}:
      ptags(q, gl, d, o, i, v, V.dec(q, i))
    case 1n+ +q False{}:
      ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))

def pcells(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> List<&2, U32>:
  match p left:
    case 0n _:
      leafp(cl, Nat.add(SC.pow2(d), o), i, v)
    case 1n+ +q True{}:
      fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o)
    case 1n+ +q False{}:
      fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)

def leafp_length(+cl: List<&2, U32>, +k: Nat, i: Nat, +v: U32) -> {SC.length(U32, leafp(cl, k, i, v)) == SC.length(U32, cl) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      LL.length_update(U32, cl, k, U32.add(FL.nthc(cl, k), v))

def tcells_length(q: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +v: U32) -> {SC.length(U32, tcells(q, cl, d, o, v)) == SC.length(U32, cl) : Nat}:
  match q:
    case 0n:
      LL.length_update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v))
    case 1n+ +r:
      LL.length_update(U32, cl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)))

def pcells_length(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> {SC.length(U32, pcells(p, cl, gl, d, o, i, v, left)) == SC.length(U32, cl) : Nat}:
  match p left:
    case 0n _:
      leafp_length(cl, Nat.add(SC.pow2(d), o), i, v)
    case 1n+ +q True{}:
      Equal.trans(Nat,
        SC.length(U32, fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o)),
        SC.length(U32, pcells(q, cl, gl, d, o, i, v, V.dec(q, i))),
        SC.length(U32, cl),
        LL.length_update(U32, pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o)),
        pcells_length(q, cl, gl, d, o, i, v, V.dec(q, i)))
    case 1n+ +q False{}:
      Equal.trans(Nat,
        SC.length(U32, fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)),
        SC.length(U32, pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
        SC.length(U32, cl),
        LL.length_update(U32, pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)),
        Equal.trans(Nat,
          SC.length(U32, pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
          SC.length(U32, tcells(q, cl, d, o, v)),
          SC.length(U32, cl),
          pcells_length(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
          tcells_length(q, cl, d, o, v)))

# ---- frames of the lazy walk ----

def ttags_cell_lo(q: Nat, +gl: List<&2, U32>, +o: Nat, +v: U32, +k: Nat, +hk: {Nat.is_le(k, o) == True{} : Bool}) -> {FL.nthc(ttags(q, gl, o, v), k) == FL.nthc(gl, k) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      FL.nthc_other(gl, Nat.add(o, SC.pow2(r)), k, U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v),
        FL.ne_gt(Nat.add(o, SC.pow2(r)), k, N.le_lt_trans(k, o, Nat.add(o, SC.pow2(r)), hk, FL.lt_split(o, r))))

def ttags_cell_hi(q: Nat, +gl: List<&2, U32>, +o: Nat, +v: U32, +k: Nat, +hk: {Nat.is_le(Nat.add(o, SC.pow2(q)), k) == True{} : Bool}) -> {FL.nthc(ttags(q, gl, o, v), k) == FL.nthc(gl, k) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      FL.nthc_other(gl, Nat.add(o, SC.pow2(r)), k, U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v),
        N.is_eq_lt(Nat.add(o, SC.pow2(r)), k, N.lt_le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), k, FL.mid_lt(o, r), hk)))

def ptags_cell_lo(p: Nat, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(k, o) == True{} : Bool}) -> {FL.nthc(ptags(p, gl, d, o, i, v, left), k) == FL.nthc(gl, k) : U32}:
  match p left:
    case 0n _:
      {==}
    case 1n+ +q True{}:
      ptags_cell_lo(q, gl, d, o, i, v, V.dec(q, i), k, hk)
    case 1n+ +q False{}:
      Equal.trans(U32, FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), k), FL.nthc(ttags(q, gl, o, v), k), FL.nthc(gl, k),
        ptags_cell_lo(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), k, N.le_trans(k, o, Nat.add(o, SC.pow2(q)), hk, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q)))),
        ttags_cell_lo(q, gl, o, v, k, hk))

def ptags_cell_hi(p: Nat, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(Nat.add(o, SC.pow2(p)), k) == True{} : Bool}) -> {FL.nthc(ptags(p, gl, d, o, i, v, left), k) == FL.nthc(gl, k) : U32}:
  match p left:
    case 0n _:
      {==}
    case 1n+ +q True{}:
      ptags_cell_hi(q, gl, d, o, i, v, V.dec(q, i), k,
        N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hk))
    case 1n+ +q False{}:
      Equal.trans(U32, FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), k), FL.nthc(ttags(q, gl, o, v), k), FL.nthc(gl, k),
        ptags_cell_hi(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), k,
          L.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hk)),
        ttags_cell_hi(q, gl, o, v, k, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hk)))

def leafp_frame_lo(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, i: Nat, +v: U32, +p2: Nat, +o2: Nat, +ht: {Nat.is_lt(o, o2) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(leafp(cl, Nat.add(SC.pow2(d), o), i, v), gl, d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      frame_v_lo(cl, gl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), ht, hq)

def leafp_frame_hi(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, i: Nat, +v: U32, +p2: Nat, +o2: Nat, +ht: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), o) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(leafp(cl, Nat.add(SC.pow2(d), o), i, v), gl, d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      frame_v_hi(cl, gl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), ht, hq)

# a tagall write disturbs no other block
def tag_frame_lo(q: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +v: U32, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o, SC.pow2(q)), o2) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match q:
    case 0n:
      frame_v_lo(cl, gl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        N.succ_le_lt(o, o2, L.subst(Nat, k => {Nat.is_le(k, o2) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), hsep)), hq)
    case 1n+ +r:
      Equal.trans(TN.Node,
        tree_of(SC.update(U32, cl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r))), SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2),
        tree_of(cl, SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_lo(cl, SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)),
          N.le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), o2, N.lt_le(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), FL.mid_lt(o, r)), hsep),
          N.lt_le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), SC.pow2(d), FL.mid_lt(o, r), hw)),
        frame_g_lo(cl, gl, d, p2, o2, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v),
          N.le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), o2, N.lt_le(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), FL.mid_lt(o, r)), hsep)))

def tag_frame_hi(q: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +v: U32, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), o) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match q:
    case 0n:
      frame_v_hi(cl, gl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), hsep, hq)
    case 1n+ +r:
      Equal.trans(TN.Node,
        tree_of(SC.update(U32, cl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r))), SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2),
        tree_of(cl, SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_hi(cl, SC.update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v)), d, p2, o2, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(r)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(r)), FL.lt_split(o, r))),
          N.lt_le_trans(Nat.add(o, SC.pow2(r)), Nat.add(o, SC.pow2(1n+r)), SC.pow2(d), FL.mid_lt(o, r), hw)),
        frame_g_hi(cl, gl, d, p2, o2, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(r)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(r)), FL.lt_split(o, r)))))

# the lazy walk leaves a disjoint block alone
def padd_tree_hi(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o, SC.pow2(p)), o2) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(pcells(p, cl, gl, d, o, i, v, left), ptags(p, gl, d, o, i, v, left), d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match p left:
    case 0n _:
      leafp_frame_lo(cl, gl, d, o, i, v, p2, o2, N.succ_le_lt(o, o2, L.subst(Nat, k => {Nat.is_le(k, o2) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), hsep)), hq)
    case 1n+ +q True{}:
      Equal.trans(TN.Node,
        tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2),
        tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_lo(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          node_lt_d(o, q, d, hw)),
        padd_tree_hi(q, cl, gl, d, o, i, v, V.dec(q, i), p2, o2,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq))
    case 1n+ +q False{}:
      Equal.trans(TN.Node,
        tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
        tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_lo(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          node_lt_d(o, q, d, hw)),
        Equal.trans(TN.Node,
          tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
          tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, p2, o2),
          tree_of(cl, gl, d, p2, o2),
          padd_tree_hi(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
            L.subst(Nat, z => {Nat.is_le(z, o2) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hsep),
            L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq),
          tag_frame_lo(q, cl, gl, d, o, v, p2, o2,
            N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
            N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq)))

def padd_tree_lo(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), o) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(pcells(p, cl, gl, d, o, i, v, left), ptags(p, gl, d, o, i, v, left), d, p2, o2) == tree_of(cl, gl, d, p2, o2) : TN.Node}:
  match p left:
    case 0n _:
      leafp_frame_hi(cl, gl, d, o, i, v, p2, o2, hsep, hq)
    case 1n+ +q True{}:
      Equal.trans(TN.Node,
        tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2),
        tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_hi(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          node_lt_d(o, q, d, hw)),
        padd_tree_lo(q, cl, gl, d, o, i, v, V.dec(q, i), p2, o2, hsep,
          N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq))
    case 1n+ +q False{}:
      Equal.trans(TN.Node,
        tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
        tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
        tree_of(cl, gl, d, p2, o2),
        frame_c_hi(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2, Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          node_lt_d(o, q, d, hw)),
        Equal.trans(TN.Node,
          tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, p2, o2),
          tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, p2, o2),
          tree_of(cl, gl, d, p2, o2),
          padd_tree_lo(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
            N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
            L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq),
          tag_frame_hi(q, cl, gl, d, o, v, p2, o2, hsep,
            N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), hq)))

# ---- tagging a block is the model's tagall ----

def tag_ok(q: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +v: U32, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}, +hlg: {SC.length(U32, gl) == SC.pow2(d) : Nat}) -> {tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, q, o) == TN.tagall(q, tree_of(cl, gl, d, q, o), v) : TN.Node}:
  match q:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z},
        FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v)), Nat.add(SC.pow2(d), o)),
        U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        FL.nthc_same(cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), FL.leaf_in_cells(cl, d, o, FL.blk_lo(o, 0n, d, hw), hlen)))
    case 1n+ +r:
      +MR = Nat.add(o, SC.pow2(r))
      +hmr = N.lt_le_trans(MR, Nat.add(o, SC.pow2(1n+r)), SC.pow2(d), FL.mid_lt(o, r), hw)
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(tcells(1n+r, cl, d, o, v), MR), FL.nthc(ttags(1n+r, gl, o, v), MR), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
        TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
        TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(cl, gl, d, r, o), tree_of(cl, gl, d, r, MR)},
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(tcells(1n+r, cl, d, o, v), MR), FL.nthc(ttags(1n+r, gl, o, v), MR), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
          TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), FL.nthc(ttags(1n+r, gl, o, v), MR), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
          TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
          Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(ttags(1n+r, gl, o, v), MR), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
            FL.nthc(tcells(1n+r, cl, d, o, v), MR), U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)),
            FL.nthc_same(cl, MR, U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), FL.in_cells(cl, d, MR, hmr, hlen))),
          Equal.cong(U32, TN.Node, z => TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), z, tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
            FL.nthc(ttags(1n+r, gl, o, v), MR), U32.add(FL.nthc(gl, MR), v),
            FL.nthc_same(gl, MR, U32.add(FL.nthc(gl, MR), v), L.subst(Nat, z => {Nat.is_lt(MR, z) == True{} : Bool}, SC.pow2(d), SC.length(U32, gl), Equal.sym(Nat, SC.length(U32, gl), SC.pow2(d), hlg), hmr)))),
        Equal.trans(TN.Node,
          TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
          TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(cl, gl, d, r, o), tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
          TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(cl, gl, d, r, o), tree_of(cl, gl, d, r, MR)},
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), z, tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR)},
            tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(cl, gl, d, r, o),
            Equal.trans(TN.Node, tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, o), tree_of(cl, ttags(1n+r, gl, o, v), d, r, o), tree_of(cl, gl, d, r, o),
              frame_c_hi(cl, ttags(1n+r, gl, o, v), d, r, o, MR, U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)), N.le_refl(MR), hmr),
              frame_g_hi(cl, gl, d, r, o, MR, U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v), N.le_refl(MR)))),
          Equal.cong(TN.Node, TN.Node, z => TN.SNode{U32.add(FL.nthc(cl, MR), U32.shln(v, 1n+r)), U32.add(FL.nthc(gl, MR), v), tree_of(cl, gl, d, r, o), z},
            tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR), tree_of(cl, gl, d, r, MR),
            Equal.trans(TN.Node, tree_of(tcells(1n+r, cl, d, o, v), ttags(1n+r, gl, o, v), d, r, MR), tree_of(cl, ttags(1n+r, gl, o, v), d, r, MR), tree_of(cl, gl, d, r, MR),
              frame_c_lo(cl, ttags(1n+r, gl, o, v), d, r, MR, MR, U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)), N.le_refl(MR), hmr),
              frame_g_lo(cl, gl, d, r, MR, MR, U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v), N.le_refl(MR))))))

def ttags_length(q: Nat, +gl: List<&2, U32>, +o: Nat, +v: U32) -> {SC.length(U32, ttags(q, gl, o, v)) == SC.length(U32, gl) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      LL.length_update(U32, gl, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(gl, Nat.add(o, SC.pow2(r))), v))

def ptags_length(p: Nat, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> {SC.length(U32, ptags(p, gl, d, o, i, v, left)) == SC.length(U32, gl) : Nat}:
  match p left:
    case 0n _:
      {==}
    case 1n+ +q True{}:
      ptags_length(q, gl, d, o, i, v, V.dec(q, i))
    case 1n+ +q False{}:
      Equal.trans(Nat, SC.length(U32, ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), SC.length(U32, ttags(q, gl, o, v)), SC.length(U32, gl),
        ptags_length(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
        ttags_length(q, gl, o, v))

def leafp_ok(+cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, i: Nat, +v: U32, +ho: {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}) -> {tree_of(leafp(cl, Nat.add(SC.pow2(d), o), i, v), gl, d, 0n, o) == TN.leaf_padd(FL.nthc(cl, Nat.add(SC.pow2(d), o)), i, v) : TN.Node}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z},
        FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v)), Nat.add(SC.pow2(d), o)),
        U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        FL.nthc_same(cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), FL.leaf_in_cells(cl, d, o, ho, hlen)))

# ---- the lazy range-add walk is the model's ----

def padd_ok(p: Nat, +cl: List<&2, U32>, +gl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}, +hlg: {SC.length(U32, gl) == SC.pow2(d) : Nat}) -> {tree_of(pcells(p, cl, gl, d, o, i, v, left), ptags(p, gl, d, o, i, v, left), d, p, o) == TN.padd_go(p, tree_of(cl, gl, d, p, o), i, v, left) : TN.Node}:
  match p left:
    case 0n _:
      leafp_ok(cl, gl, d, o, i, v, FL.blk_lo(o, 0n, d, hw), hlen)
    case 1n+ +q True{}:
      +hm = node_lt_d(o, q, d, hw)
      +hwl = N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw)
      +hlen2 = Equal.trans(Nat, SC.length(U32, pcells(q, cl, gl, d, o, i, v, V.dec(q, i))), SC.length(U32, cl), SC.pow2(1n+d), pcells_length(q, cl, gl, d, o, i, v, V.dec(q, i)), hlen)
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
        TN.node(q, TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
          Equal.trans(TN.Node,
            TN.SNode{FL.nthc(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
              FL.nthc(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), Nat.add(o, SC.pow2(q))), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o),
              FL.nthc_same(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.in_cells(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), d, Nat.add(o, SC.pow2(q)), hm, hlen2))),
            Equal.cong(U32, TN.Node, z => TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), z, tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
              FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))),
              ptags_cell_hi(q, gl, d, o, i, v, V.dec(q, i), Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q)))))),
          Equal.trans(TN.Node,
            TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))},
              tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o),
              frame_c_hi(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o, Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), z},
              tree_of(fixc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q))),
              frame_c_lo(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(q)), upsum(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)))),
        %total_at(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o, hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(_, FL.nthc(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %total_at(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)), hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o)), _), U32.shln(FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %Equal.sym(U32, FL.nthc(ptags(q, gl, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), ptags_cell_hi(q, gl, d, o, i, v, V.dec(q, i), Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q))))) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o)), TN.total(tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q))))), U32.shln(_, 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        Equal.trans(TN.Node,
          TN.node(q, tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), z, FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
            padd_tree_hi(q, cl, gl, d, o, i, v, V.dec(q, i), q, Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q))), hwl, hwr)),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, z, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(pcells(q, cl, gl, d, o, i, v, V.dec(q, i)), ptags(q, gl, d, o, i, v, V.dec(q, i)), d, q, o), TN.padd_go(q, tree_of(cl, gl, d, q, o), i, v, V.dec(q, i)),
            padd_ok(q, cl, gl, d, o, i, v, V.dec(q, i), hwl, hlen, hlg))))
    case 1n+ +q False{}:
      +hm = node_lt_d(o, q, d, hw)
      +hwl = N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw)
      +hlenT = Equal.trans(Nat, SC.length(U32, tcells(q, cl, d, o, v)), SC.length(U32, cl), SC.pow2(1n+d), tcells_length(q, cl, d, o, v), hlen)
      +hlgT = Equal.trans(Nat, SC.length(U32, ttags(q, gl, o, v)), SC.length(U32, gl), SC.pow2(d), ttags_length(q, gl, o, v), hlg)
      +hlen2 = Equal.trans(Nat, SC.length(U32, pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), SC.length(U32, tcells(q, cl, d, o, v)), SC.pow2(1n+d), pcells_length(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), hlenT)
      +egm = Equal.trans(U32, FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), FL.nthc(ttags(q, gl, o, v), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))),
        ptags_cell_lo(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q)))),
        ttags_cell_hi(q, gl, o, v, Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q)))))
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
        TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
        Equal.trans(TN.Node,
          TN.SNode{FL.nthc(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
          Equal.trans(TN.Node,
            TN.SNode{FL.nthc(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), Nat.add(o, SC.pow2(q))), FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
              FL.nthc(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), Nat.add(o, SC.pow2(q))), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
              FL.nthc_same(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.in_cells(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, Nat.add(o, SC.pow2(q)), hm, hlen2))),
            Equal.cong(U32, TN.Node, z => TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), z, tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
              FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), egm)),
          Equal.trans(TN.Node,
            TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), z, tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))},
              tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
              frame_c_hi(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o, Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), z},
              tree_of(fixc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))),
              frame_c_lo(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(q)), upsum(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), N.le_refl(Nat.add(o, SC.pow2(q))), hm)))),
        %total_at(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o, hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(_, FL.nthc(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %total_at(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)), hq_of(q), {==}) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)), _), U32.shln(FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %Equal.sym(U32, FL.nthc(ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q))), egm) : {TN.SNode{U32.add(U32.add(TN.total(tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)), TN.total(tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))))), U32.shln(_, 1n+q)), FL.nthc(gl, Nat.add(o, SC.pow2(q))), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q)))} == TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, V.pow2(q)), v, V.dec(q, Nat.sub(i, V.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        %Equal.sym(Nat, V.pow2(q), SC.pow2(q), vsc(q)) : {TN.node(q, tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) == TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, _), v, V.dec(q, Nat.sub(i, _))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))) : TN.Node}
        Equal.trans(TN.Node,
          TN.node(q, tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, z, tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), TN.tagall(q, tree_of(cl, gl, d, q, o), v),
            Equal.trans(TN.Node, tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o), tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, q, o), TN.tagall(q, tree_of(cl, gl, d, q, o), v),
              padd_tree_lo(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), q, o, N.le_refl(Nat.add(o, SC.pow2(q))), hwr, hwl),
              tag_ok(q, cl, gl, d, o, v, hwl, hlen, hlg))),
          Equal.cong(TN.Node, TN.Node, z => TN.node(q, TN.tagall(q, tree_of(cl, gl, d, q, o), v), z, FL.nthc(gl, Nat.add(o, SC.pow2(q)))),
            tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
            Equal.trans(TN.Node, tree_of(pcells(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, Nat.add(o, SC.pow2(q))), TN.padd_go(q, tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), TN.padd_go(q, tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
              padd_ok(q, tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), hwr, hlenT, hlgT),
              Equal.cong(TN.Node, TN.Node, z => TN.padd_go(q, z, Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
                tree_of(tcells(q, cl, d, o, v), ttags(q, gl, o, v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, gl, d, q, Nat.add(o, SC.pow2(q))),
                tag_frame_lo(q, cl, gl, d, o, v, q, Nat.add(o, SC.pow2(q)), N.le_refl(Nat.add(o, SC.pow2(q))), hwl, hwr))))))

# ---- the same walks on the mirror trees of the two arrays ----

def fix_thaw(+tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +q: Nat, +o: Nat, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(1n+q)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {SG.fix((A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg)), SC.pow2(d), SC.pow2(q), hq_of(q), o, q) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}:
  %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(cix(q, d, o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), cix(q, d, o))), AR.get_ok(1n+d, tc, cix(q, d, o), hd, cell_lt(q, o, d, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw))), pfc)) : {SG.fix1(_, A.thaw(SG.Cel, tg), SC.pow2(d), hq_of(q), Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(q)), q) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(cix(q, d, Nat.add(o, SC.pow2(q))))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), cix(q, d, Nat.add(o, SC.pow2(q))))), AR.get_ok(1n+d, tc, cix(q, d, Nat.add(o, SC.pow2(q))), hd, cell_lt(q, Nat.add(o, SC.pow2(q)), d, L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw)), pfc)) : {SG.fix2(_, A.thaw(SG.Cel, tg), Nat.add(o, SC.pow2(q)), q, SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, o)))) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.fix3(_, A.thaw(SG.Cel, tc), Nat.add(o, SC.pow2(q)), q, SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, o))), SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, Nat.add(o, SC.pow2(q)))))) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, o))), FL.nthc(AR.cl(tc), cix(q, d, o)), AR.cval_cels(A.slots(SG.Cel, tc), cix(q, d, o))) : {(SG.write(A.thaw(SG.Cel, tc), Nat.add(o, SC.pow2(q)), U32.add(U32.add(_, SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, Nat.add(o, SC.pow2(q)))))), U32.shln(SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), 1n+q))), A.thaw(SG.Cel, tg)) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tc), cix(q, d, Nat.add(o, SC.pow2(q))))), FL.nthc(AR.cl(tc), cix(q, d, Nat.add(o, SC.pow2(q)))), AR.cval_cels(A.slots(SG.Cel, tc), cix(q, d, Nat.add(o, SC.pow2(q))))) : {(SG.write(A.thaw(SG.Cel, tc), Nat.add(o, SC.pow2(q)), U32.add(U32.add(FL.nthc(AR.cl(tc), cix(q, d, o)), _), U32.shln(SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), 1n+q))), A.thaw(SG.Cel, tg)) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {(SG.write(A.thaw(SG.Cel, tc), Nat.add(o, SC.pow2(q)), U32.add(U32.add(FL.nthc(AR.cl(tc), cix(q, d, o)), FL.nthc(AR.cl(tc), cix(q, d, Nat.add(o, SC.pow2(q))))), U32.shln(_, 1n+q))), A.thaw(SG.Cel, tg)) == (A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
  Equal.cong(Array<SG.Cel>, Array<SG.Cel> & Array<SG.Cel>, z => (z, A.thaw(SG.Cel, tg)),
    SG.write(A.thaw(SG.Cel, tc), Nat.add(o, SC.pow2(q)), upsum(AR.cl(tc), AR.cl(tg), d, q, o)),
    A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(tc), AR.cl(tg), d, q, o)})),
    AR.write_ok(1n+d, tc, Nat.add(o, SC.pow2(q)), upsum(AR.cl(tc), AR.cl(tg), d, q, o), hd, N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, q, d, hw), FL.base_lt(d)), pfc))

def fixt(+t: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +q: Nat, +o: Nat) -> A.Tree<SG.Cel>:
  A.upd(SG.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(t), AR.cl(tg), d, q, o)})

def stree(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool) -> A.Tree<SG.Cel>:
  match p left:
    case 0n _:
      A.upd(SG.Cel, 1n+d, tc, Nat.add(SC.pow2(d), o), SG.CV{U32.sub(v, acc)})
    case 1n+ +q True{}:
      fixt(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), tg, d, q, o)
    case 1n+ +q False{}:
      fixt(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), tg, d, q, o)

def stree_perfect(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {A.perfect(SG.Cel, 1n+d, stree(p, tc, tg, d, acc, o, i, v, left)) == True{} : Bool}:
  match p left:
    case 0n _:
      A.upd_perfect(SG.Cel, 1n+d, tc, Nat.add(SC.pow2(d), o), SG.CV{U32.sub(v, acc)}, pfc)
    case 1n+ +q True{}:
      A.upd_perfect(SG.Cel, 1n+d, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), AR.cl(tg), d, q, o)},
        stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), pfc))
    case 1n+ +q False{}:
      A.upd_perfect(SG.Cel, 1n+d, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(tg), d, q, o)},
        stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), pfc))

def stree_cl(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {AR.cl(stree(p, tc, tg, d, acc, o, i, v, left)) == scells(p, AR.cl(tc), AR.cl(tg), d, acc, o, i, v, left) : List<&2, U32>}:
  match p left:
    case 0n _:
      AR.cl_upd(1n+d, tc, Nat.add(SC.pow2(d), o), U32.sub(v, acc), FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)
    case 1n+ +q True{}:
      Equal.trans(List<&2, U32>,
        AR.cl(fixt(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), tg, d, q, o)),
        SC.update(U32, AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), Nat.add(o, SC.pow2(q)), upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), AR.cl(tg), d, q, o)),
        fixc(scells(q, AR.cl(tc), AR.cl(tg), d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), AR.cl(tg), d, q, o),
        AR.cl_upd(1n+d, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), AR.cl(tg), d, q, o),
          N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, q, d, hw), FL.base_lt(d)),
          stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), pfc)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, Nat.add(o, SC.pow2(q)), upsum(z, AR.cl(tg), d, q, o)),
          AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), scells(q, AR.cl(tc), AR.cl(tg), d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)),
          stree_cl(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc)))
    case 1n+ +q False{}:
      Equal.trans(List<&2, U32>,
        AR.cl(fixt(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), tg, d, q, o)),
        SC.update(U32, AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), Nat.add(o, SC.pow2(q)), upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(tg), d, q, o)),
        fixc(scells(q, AR.cl(tc), AR.cl(tg), d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), AR.cl(tg), d, q, o),
        AR.cl_upd(1n+d, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(tg), d, q, o),
          N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, q, d, hw), FL.base_lt(d)),
          stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), pfc)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, Nat.add(o, SC.pow2(q)), upsum(z, AR.cl(tg), d, q, o)),
          AR.cl(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), scells(q, AR.cl(tc), AR.cl(tg), d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
          stree_cl(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pfc)))

def set_thaw(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat, +v: U32, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {SG.set_go(p, SG.pre_t(p, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, h, o), base, h, hh, acc, o, i, v, left) == (A.thaw(SG.Cel, stree(p, tc, tg, d, acc, o, i, v, left)), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.set_go(0n, SG.mk_c(Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(_, o))), A.thaw(SG.Cel, tg)), _, h, hh, acc, o, i, v, left) == (A.thaw(SG.Cel, stree(0n, tc, tg, d, acc, o, i, v, left)), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tc), U32.from_nat(Nat.add(SC.pow2(d), o))), (A.thaw(SG.Cel, tc), AR.cels(A.slots(SG.Cel, tc), Nat.add(SC.pow2(d), o))), AR.get_ok(1n+d, tc, Nat.add(SC.pow2(d), o), hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)) : {SG.set_go(0n, SG.mk_c(_, A.thaw(SG.Cel, tg)), SC.pow2(d), h, hh, acc, o, i, v, left) == (A.thaw(SG.Cel, stree(0n, tc, tg, d, acc, o, i, v, left)), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      Equal.cong(Array<SG.Cel>, Array<SG.Cel> & Array<SG.Cel>, z => (z, A.thaw(SG.Cel, tg)),
        SG.write(A.thaw(SG.Cel, tc), Nat.add(SC.pow2(d), o), U32.sub(v, acc)),
        A.thaw(SG.Cel, A.upd(SG.Cel, 1n+d, tc, Nat.add(SC.pow2(d), o), SG.CV{U32.sub(v, acc)})),
        AR.write_ok(1n+d, tc, Nat.add(SC.pow2(d), o), U32.sub(v, acc), hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc))
    case 1n+ +q True{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, h))), A.thaw(SG.Cel, tc)), _, h, hh, acc, o, i, v, True{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc)), SC.pow2(d), _, hh, acc, o, i, v, True{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, hh, FL.hof(q), ehq) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), A.thaw(SG.Cel, tc)), SC.pow2(d), SC.pow2(q), _, acc, o, i, v, True{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.set_go(1n+q, SG.mk_g(_, A.thaw(SG.Cel, tc)), SC.pow2(d), SC.pow2(q), FL.hof(q), acc, o, i, v, True{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.fix(SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), o), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, _), o, i, v, Nat.is_lt(i, FL.hof(q))), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Bool, Nat.is_lt(i, FL.hof(q)), V.dec(q, i), vdec(q, i, FL.hof(q), {==})) : {SG.fix(SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), o), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, _), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & Array<SG.Cel>, SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), o), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), (A.thaw(SG.Cel, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), A.thaw(SG.Cel, tg)), set_thaw(q, tc, tg, d, SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), hd, hdg, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc, pfg, {==}, {==}, {==})) : {SG.fix(_, SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, FL.hof(q), hq_of(q), {==}) : {SG.fix((A.thaw(SG.Cel, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i))), A.thaw(SG.Cel, tg)), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, True{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      fix_thaw(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i)), tg, d, q, o, hd, hdg, hw, stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), o, i, v, V.dec(q, i), pfc), pfg)
    case 1n+ +q False{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, h))), A.thaw(SG.Cel, tc)), _, h, hh, acc, o, i, v, False{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, _))), A.thaw(SG.Cel, tc)), SC.pow2(d), _, hh, acc, o, i, v, False{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, hh, FL.hof(q), ehq) : {SG.set_go(1n+q, SG.mk_g(Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), A.thaw(SG.Cel, tc)), SC.pow2(d), SC.pow2(q), _, acc, o, i, v, False{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & SG.Cel, Array.get(SG.Cel, A.thaw(SG.Cel, tg), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(SG.Cel, tg), AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), AR.get_ok(d, tg, Nat.add(o, SC.pow2(q)), hdg, node_lt_d(o, q, d, hw), pfg)) : {SG.set_go(1n+q, SG.mk_g(_, A.thaw(SG.Cel, tc)), SC.pow2(d), SC.pow2(q), FL.hof(q), acc, o, i, v, False{}) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(U32, SG.cval(AR.cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(SG.Cel, tg), Nat.add(o, SC.pow2(q)))) : {SG.fix(SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), Nat.add(o, SC.pow2(q))), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, _), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, Nat.is_lt(Nat.sub(i, SC.pow2(q)), FL.hof(q))), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), FL.hof(q)), V.dec(q, Nat.sub(i, SC.pow2(q))), vdec(q, Nat.sub(i, SC.pow2(q)), FL.hof(q), {==})) : {SG.fix(SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), Nat.add(o, SC.pow2(q))), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, _), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & Array<SG.Cel>, SG.set_go(q, SG.pre_t(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), Nat.add(o, SC.pow2(q))), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), (A.thaw(SG.Cel, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), A.thaw(SG.Cel, tg)), set_thaw(q, tc, tg, d, SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), hd, hdg, L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pfc, pfg, {==}, {==}, {==})) : {SG.fix(_, SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, FL.hof(q), hq_of(q), {==}) : {SG.fix((A.thaw(SG.Cel, stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), A.thaw(SG.Cel, tg)), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, stree(1n+q, tc, tg, d, acc, o, i, v, False{})), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}
      fix_thaw(stree(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), tg, d, q, o, hd, hdg, hw, stree_perfect(q, tc, tg, d, U32.add(acc, FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), pfc), pfg)

# ---- the lazy range-add walk on the mirror trees ----

def bmp(+dd: Nat, +t: A.Tree<SG.Cel>, +k: Nat, +v: U32) -> A.Tree<SG.Cel>:
  A.upd(SG.Cel, dd, t, k, SG.CV{U32.add(FL.nthc(AR.cl(t), k), v)})

def ltree(+tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, i: Nat, +v: U32) -> A.Tree<SG.Cel>:
  match i:
    case 0n:
      tc
    case 1n+j:
      bmp(1n+d, tc, Nat.add(SC.pow2(d), o), v)

def tgt_c(q: Nat, +tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32) -> A.Tree<SG.Cel>:
  match q:
    case 0n:
      bmp(1n+d, tc, Nat.add(SC.pow2(d), o), v)
    case 1n+ +r:
      bmp(1n+d, tc, Nat.add(o, SC.pow2(r)), U32.shln(v, 1n+r))

def tgt_g(q: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32) -> A.Tree<SG.Cel>:
  match q:
    case 0n:
      tg
    case 1n+ +r:
      bmp(d, tg, Nat.add(o, SC.pow2(r)), v)

def ptg(p: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> A.Tree<SG.Cel>:
  match p left:
    case 0n _:
      tg
    case 1n+ +q True{}:
      ptg(q, tg, d, o, i, v, V.dec(q, i))
    case 1n+ +q False{}:
      ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))

def ptc(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> A.Tree<SG.Cel>:
  match p left:
    case 0n _:
      ltree(tc, d, o, i, v)
    case 1n+ +q True{}:
      fixt(ptc(q, tc, tg, d, o, i, v, V.dec(q, i)), ptg(q, tg, d, o, i, v, V.dec(q, i)), d, q, o)
    case 1n+ +q False{}:
      fixt(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)

def tgt_c_perfect(q: Nat, +tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {A.perfect(SG.Cel, 1n+d, tgt_c(q, tc, d, o, v)) == True{} : Bool}:
  match q:
    case 0n:
      A.upd_perfect(SG.Cel, 1n+d, tc, Nat.add(SC.pow2(d), o), SG.CV{U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), v)}, pfc)
    case 1n+ +r:
      A.upd_perfect(SG.Cel, 1n+d, tc, Nat.add(o, SC.pow2(r)), SG.CV{U32.add(FL.nthc(AR.cl(tc), Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r))}, pfc)

def tgt_g_perfect(q: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {A.perfect(SG.Cel, d, tgt_g(q, tg, d, o, v)) == True{} : Bool}:
  match q:
    case 0n:
      pfg
    case 1n+ +r:
      A.upd_perfect(SG.Cel, d, tg, Nat.add(o, SC.pow2(r)), SG.CV{U32.add(FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(r))), v)}, pfg)

def ltree_perfect(+tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, i: Nat, +v: U32, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {A.perfect(SG.Cel, 1n+d, ltree(tc, d, o, i, v)) == True{} : Bool}:
  match i:
    case 0n:
      pfc
    case 1n+j:
      A.upd_perfect(SG.Cel, 1n+d, tc, Nat.add(SC.pow2(d), o), SG.CV{U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), v)}, pfc)

def ptg_perfect(p: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {A.perfect(SG.Cel, d, ptg(p, tg, d, o, i, v, left)) == True{} : Bool}:
  match p left:
    case 0n _:
      pfg
    case 1n+ +q True{}:
      ptg_perfect(q, tg, d, o, i, v, V.dec(q, i), pfg)
    case 1n+ +q False{}:
      ptg_perfect(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), tgt_g_perfect(q, tg, d, o, v, pfg))

def ptc_perfect(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {A.perfect(SG.Cel, 1n+d, ptc(p, tc, tg, d, o, i, v, left)) == True{} : Bool}:
  match p left:
    case 0n _:
      ltree_perfect(tc, d, o, i, v, pfc)
    case 1n+ +q True{}:
      A.upd_perfect(SG.Cel, 1n+d, ptc(q, tc, tg, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o)},
        ptc_perfect(q, tc, tg, d, o, i, v, V.dec(q, i), pfc))
    case 1n+ +q False{}:
      A.upd_perfect(SG.Cel, 1n+d, ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), SG.CV{upsum(AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o)},
        ptc_perfect(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), tgt_c_perfect(q, tc, d, o, v, pfc)))

def ltree_cl(+tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, i: Nat, +v: U32, +ho: {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {AR.cl(ltree(tc, d, o, i, v)) == leafp(AR.cl(tc), Nat.add(SC.pow2(d), o), i, v) : List<&2, U32>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      AR.cl_upd(1n+d, tc, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), v), FL.leaf_lt(d, o, ho), pfc)

def tgt_c_cl(q: Nat, +tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {AR.cl(tgt_c(q, tc, d, o, v)) == tcells(q, AR.cl(tc), d, o, v) : List<&2, U32>}:
  match q:
    case 0n:
      AR.cl_upd(1n+d, tc, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(AR.cl(tc), Nat.add(SC.pow2(d), o)), v), FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)
    case 1n+ +r:
      AR.cl_upd(1n+d, tc, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(AR.cl(tc), Nat.add(o, SC.pow2(r))), U32.shln(v, 1n+r)), N.lt_trans(Nat.add(o, SC.pow2(r)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, r, d, hw), FL.base_lt(d)), pfc)

def tgt_g_cl(q: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {AR.cl(tgt_g(q, tg, d, o, v)) == ttags(q, AR.cl(tg), o, v) : List<&2, U32>}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      AR.cl_upd(d, tg, Nat.add(o, SC.pow2(r)), U32.add(FL.nthc(AR.cl(tg), Nat.add(o, SC.pow2(r))), v), node_lt_d(o, r, d, hw), pfg)

def ptg_cl(p: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {AR.cl(ptg(p, tg, d, o, i, v, left)) == ptags(p, AR.cl(tg), d, o, i, v, left) : List<&2, U32>}:
  match p left:
    case 0n _:
      {==}
    case 1n+ +q True{}:
      ptg_cl(q, tg, d, o, i, v, V.dec(q, i), N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg)
    case 1n+ +q False{}:
      Equal.trans(List<&2, U32>,
        AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
        ptags(q, AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
        ptags(q, ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
        ptg_cl(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), tgt_g_perfect(q, tg, d, o, v, pfg)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => ptags(q, z, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
          AR.cl(tgt_g(q, tg, d, o, v)), ttags(q, AR.cl(tg), o, v), tgt_g_cl(q, tg, d, o, v, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg)))

def ptc_cl(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {AR.cl(ptc(p, tc, tg, d, o, i, v, left)) == pcells(p, AR.cl(tc), AR.cl(tg), d, o, i, v, left) : List<&2, U32>}:
  match p left:
    case 0n _:
      ltree_cl(tc, d, o, i, v, FL.blk_lo(o, 0n, d, hw), pfc)
    case 1n+ +q True{}:
      Equal.trans(List<&2, U32>,
        AR.cl(fixt(ptc(q, tc, tg, d, o, i, v, V.dec(q, i)), ptg(q, tg, d, o, i, v, V.dec(q, i)), d, q, o)),
        fixc(AR.cl(ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o),
        fixc(pcells(q, AR.cl(tc), AR.cl(tg), d, o, i, v, V.dec(q, i)), ptags(q, AR.cl(tg), d, o, i, v, V.dec(q, i)), d, q, o),
        AR.cl_upd(1n+d, ptc(q, tc, tg, d, o, i, v, V.dec(q, i)), Nat.add(o, SC.pow2(q)), upsum(AR.cl(ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o), N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, q, d, hw), FL.base_lt(d)),
          ptc_perfect(q, tc, tg, d, o, i, v, V.dec(q, i), pfc)),
        Equal.trans(List<&2, U32>,
          fixc(AR.cl(ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o),
          fixc(pcells(q, AR.cl(tc), AR.cl(tg), d, o, i, v, V.dec(q, i)), AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o),
          fixc(pcells(q, AR.cl(tc), AR.cl(tg), d, o, i, v, V.dec(q, i)), ptags(q, AR.cl(tg), d, o, i, v, V.dec(q, i)), d, q, o),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => fixc(z, AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), d, q, o),
            AR.cl(ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), pcells(q, AR.cl(tc), AR.cl(tg), d, o, i, v, V.dec(q, i)),
            ptc_cl(q, tc, tg, d, o, i, v, V.dec(q, i), N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc, pfg)),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => fixc(pcells(q, AR.cl(tc), AR.cl(tg), d, o, i, v, V.dec(q, i)), z, d, q, o),
            AR.cl(ptg(q, tg, d, o, i, v, V.dec(q, i))), ptags(q, AR.cl(tg), d, o, i, v, V.dec(q, i)),
            ptg_cl(q, tg, d, o, i, v, V.dec(q, i), N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg))))
    case 1n+ +q False{}:
      Equal.trans(List<&2, U32>,
        AR.cl(fixt(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o)),
        fixc(AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o),
        fixc(pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
        AR.cl_upd(1n+d, ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), upsum(AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o), N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, q, d, hw), FL.base_lt(d)),
          ptc_perfect(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), tgt_c_perfect(q, tc, d, o, v, pfc))),
        Equal.trans(List<&2, U32>,
          fixc(AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o),
          fixc(pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o),
          fixc(pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptags(q, ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => fixc(z, AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), d, q, o),
            AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
            Equal.trans(List<&2, U32>,
              AR.cl(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
              pcells(q, AR.cl(tgt_c(q, tc, d, o, v)), AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
              pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
              ptc_cl(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), tgt_c_perfect(q, tc, d, o, v, pfc), tgt_g_perfect(q, tg, d, o, v, pfg)),
              Equal.trans(List<&2, U32>,
                pcells(q, AR.cl(tgt_c(q, tc, d, o, v)), AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
                pcells(q, tcells(q, AR.cl(tc), d, o, v), AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
                pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
                Equal.cong(List<&2, U32>, List<&2, U32>, z => pcells(q, z, AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), AR.cl(tgt_c(q, tc, d, o, v)), tcells(q, AR.cl(tc), d, o, v), tgt_c_cl(q, tc, d, o, v, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc)),
                Equal.cong(List<&2, U32>, List<&2, U32>, z => pcells(q, tcells(q, AR.cl(tc), d, o, v), z, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), AR.cl(tgt_g(q, tg, d, o, v)), ttags(q, AR.cl(tg), o, v), tgt_g_cl(q, tg, d, o, v, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg))))),
          Equal.cong(List<&2, U32>, List<&2, U32>, z => fixc(pcells(q, tcells(q, AR.cl(tc), d, o, v), ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), z, d, q, o),
            AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), ptags(q, ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
            Equal.trans(List<&2, U32>,
              AR.cl(ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))),
              ptags(q, AR.cl(tgt_g(q, tg, d, o, v)), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
              ptags(q, ttags(q, AR.cl(tg), o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))),
              ptg_cl(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), tgt_g_perfect(q, tg, d, o, v, pfg)),
              Equal.cong(List<&2, U32>, List<&2, U32>, z => ptags(q, z, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), AR.cl(tgt_g(q, tg, d, o, v)), ttags(q, AR.cl(tg), o, v), tgt_g_cl(q, tg, d, o, v, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg))))))

def tag_c_thaw(q: Nat, +tc: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {SG.tag_c(q, A.thaw(SG.Cel, tc), SC.pow2(d), FL.hof(q), o, v) == A.thaw(SG.Cel, tgt_c(q, tc, d, o, v)) : Array<SG.Cel>}:
  match q:
    case 0n:
      AR.bump_ok(1n+d, tc, Nat.add(SC.pow2(d), o), v, hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pfc)
    case 1n+ +r:
      %Equal.sym(Nat, FL.hof(1n+r), SC.pow2(r), FL.hof_succ(r)) : {SG.bump(A.thaw(SG.Cel, tc), Nat.add(o, _), U32.shln(v, 1n+r)) == A.thaw(SG.Cel, tgt_c(1n+r, tc, d, o, v)) : Array<SG.Cel>}
      AR.bump_ok(1n+d, tc, Nat.add(o, SC.pow2(r)), U32.shln(v, 1n+r), hd, N.lt_trans(Nat.add(o, SC.pow2(r)), SC.pow2(d), SC.pow2(1n+d), node_lt_d(o, r, d, hw), FL.base_lt(d)), pfc)

def tag_g_thaw(q: Nat, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, +v: U32, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(q)), SC.pow2(d)) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}) -> {SG.tag_g(q, A.thaw(SG.Cel, tg), FL.hof(q), o, v) == A.thaw(SG.Cel, tgt_g(q, tg, d, o, v)) : Array<SG.Cel>}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      %Equal.sym(Nat, FL.hof(1n+r), SC.pow2(r), FL.hof_succ(r)) : {SG.bump(A.thaw(SG.Cel, tg), Nat.add(o, _), v) == A.thaw(SG.Cel, tgt_g(1n+r, tg, d, o, v)) : Array<SG.Cel>}
      AR.bump_ok(d, tg, Nat.add(o, SC.pow2(r)), v, hdg, node_lt_d(o, r, d, hw), pfg)

def leafp_thaw(+tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +o: Nat, i: Nat, +v: U32, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +ho: {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}) -> {(SG.leaf_padd(A.thaw(SG.Cel, tc), Nat.add(SC.pow2(d), o), i, v), A.thaw(SG.Cel, tg)) == (A.thaw(SG.Cel, ltree(tc, d, o, i, v)), A.thaw(SG.Cel, tg)) : Array<SG.Cel> & Array<SG.Cel>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Array<SG.Cel>, Array<SG.Cel> & Array<SG.Cel>, z => (z, A.thaw(SG.Cel, tg)),
        SG.bump(A.thaw(SG.Cel, tc), Nat.add(SC.pow2(d), o), v), A.thaw(SG.Cel, bmp(1n+d, tc, Nat.add(SC.pow2(d), o), v)),
        AR.bump_ok(1n+d, tc, Nat.add(SC.pow2(d), o), v, hd, FL.leaf_lt(d, o, ho), pfc))

def padd_thaw(p: Nat, +tc: A.Tree<SG.Cel>, +tg: A.Tree<SG.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hdg: {Nat.is_lt(d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pfc: {A.perfect(SG.Cel, 1n+d, tc) == True{} : Bool}, +pfg: {A.perfect(SG.Cel, d, tg) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {SG.padd_go(p, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), base, h, hh, o, i, v, left) == (A.thaw(SG.Cel, ptc(p, tc, tg, d, o, i, v, left)), A.thaw(SG.Cel, ptg(p, tg, d, o, i, v, left))) : Array<SG.Cel> & Array<SG.Cel>}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {(SG.leaf_padd(A.thaw(SG.Cel, tc), Nat.add(_, o), i, v), A.thaw(SG.Cel, tg)) == (A.thaw(SG.Cel, ptc(0n, tc, tg, d, o, i, v, left)), A.thaw(SG.Cel, ptg(0n, tg, d, o, i, v, left))) : Array<SG.Cel> & Array<SG.Cel>}
      leafp_thaw(tc, tg, d, o, i, v, hd, FL.blk_lo(o, 0n, d, hw), pfc)
    case 1n+ +q True{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), _, hh, Nat.div(hh, 2n), o, i, v, Nat.is_lt(i, hh)), _, h, hh, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), hh, Nat.div(hh, 2n), o, i, v, Nat.is_lt(i, hh)), SC.pow2(d), _, hh, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, hh, FL.hof(q), ehq) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), _, Nat.div(_, 2n), o, i, v, Nat.is_lt(i, _)), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Bool, Nat.is_lt(i, FL.hof(q)), V.dec(q, i), vdec(q, i, FL.hof(q), {==})) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), o, i, v, _), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & Array<SG.Cel>, SG.padd_go(q, A.thaw(SG.Cel, tc), A.thaw(SG.Cel, tg), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), o, i, v, V.dec(q, i)), (A.thaw(SG.Cel, ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), A.thaw(SG.Cel, ptg(q, tg, d, o, i, v, V.dec(q, i)))), padd_thaw(q, tc, tg, d, SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), o, i, v, V.dec(q, i), hd, hdg, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc, pfg, {==}, {==}, {==})) : {SG.fix(_, SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, FL.hof(q), hq_of(q), {==}) : {SG.fix((A.thaw(SG.Cel, ptc(q, tc, tg, d, o, i, v, V.dec(q, i))), A.thaw(SG.Cel, ptg(q, tg, d, o, i, v, V.dec(q, i)))), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, True{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, True{}))) : Array<SG.Cel> & Array<SG.Cel>}
      fix_thaw(ptc(q, tc, tg, d, o, i, v, V.dec(q, i)), ptg(q, tg, d, o, i, v, V.dec(q, i)), d, q, o, hd, hdg, hw,
        ptc_perfect(q, tc, tg, d, o, i, v, V.dec(q, i), pfc), ptg_perfect(q, tg, d, o, i, v, V.dec(q, i), pfg))
    case 1n+ +q False{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {SG.fix(SG.padd_go(q, SG.tag_c(q, A.thaw(SG.Cel, tc), _, hh, o, v), SG.tag_g(q, A.thaw(SG.Cel, tg), hh, o, v), _, hh, Nat.div(hh, 2n), Nat.add(o, h), Nat.sub(i, h), v, Nat.is_lt(Nat.sub(i, h), hh)), _, h, hh, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {SG.fix(SG.padd_go(q, SG.tag_c(q, A.thaw(SG.Cel, tc), SC.pow2(d), hh, o, v), SG.tag_g(q, A.thaw(SG.Cel, tg), hh, o, v), SC.pow2(d), hh, Nat.div(hh, 2n), Nat.add(o, _), Nat.sub(i, _), v, Nat.is_lt(Nat.sub(i, _), hh)), SC.pow2(d), _, hh, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, hh, FL.hof(q), ehq) : {SG.fix(SG.padd_go(q, SG.tag_c(q, A.thaw(SG.Cel, tc), SC.pow2(d), _, o, v), SG.tag_g(q, A.thaw(SG.Cel, tg), _, o, v), SC.pow2(d), _, Nat.div(_, 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, Nat.is_lt(Nat.sub(i, SC.pow2(q)), _)), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel>, SG.tag_c(q, A.thaw(SG.Cel, tc), SC.pow2(d), FL.hof(q), o, v), A.thaw(SG.Cel, tgt_c(q, tc, d, o, v)), tag_c_thaw(q, tc, d, o, v, hd, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfc)) : {SG.fix(SG.padd_go(q, _, SG.tag_g(q, A.thaw(SG.Cel, tg), FL.hof(q), o, v), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, Nat.is_lt(Nat.sub(i, SC.pow2(q)), FL.hof(q))), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel>, SG.tag_g(q, A.thaw(SG.Cel, tg), FL.hof(q), o, v), A.thaw(SG.Cel, tgt_g(q, tg, d, o, v)), tag_g_thaw(q, tg, d, o, v, hdg, N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), node_lt_d(o, q, d, hw)), pfg)) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tgt_c(q, tc, d, o, v)), _, SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, Nat.is_lt(Nat.sub(i, SC.pow2(q)), FL.hof(q))), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), FL.hof(q)), V.dec(q, Nat.sub(i, SC.pow2(q))), vdec(q, Nat.sub(i, SC.pow2(q)), FL.hof(q), {==})) : {SG.fix(SG.padd_go(q, A.thaw(SG.Cel, tgt_c(q, tc, d, o, v)), A.thaw(SG.Cel, tgt_g(q, tg, d, o, v)), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, _), SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Array<SG.Cel> & Array<SG.Cel>, SG.padd_go(q, A.thaw(SG.Cel, tgt_c(q, tc, d, o, v)), A.thaw(SG.Cel, tgt_g(q, tg, d, o, v)), SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), (A.thaw(SG.Cel, ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), A.thaw(SG.Cel, ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))))), padd_thaw(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, SC.pow2(d), FL.hof(q), Nat.div(FL.hof(q), 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), hd, hdg, L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), tgt_c_perfect(q, tc, d, o, v, pfc), tgt_g_perfect(q, tg, d, o, v, pfg), {==}, {==}, {==})) : {SG.fix(_, SC.pow2(d), SC.pow2(q), FL.hof(q), o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      %Equal.sym(Nat, FL.hof(q), hq_of(q), {==}) : {SG.fix((A.thaw(SG.Cel, ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))))), A.thaw(SG.Cel, ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))))), SC.pow2(d), SC.pow2(q), _, o, q) == (A.thaw(SG.Cel, ptc(1n+q, tc, tg, d, o, i, v, False{})), A.thaw(SG.Cel, ptg(1n+q, tg, d, o, i, v, False{}))) : Array<SG.Cel> & Array<SG.Cel>}
      fix_thaw(ptc(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), ptg(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q)))), d, q, o, hd, hdg, hw,
        ptc_perfect(q, tgt_c(q, tc, d, o, v), tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), tgt_c_perfect(q, tc, d, o, v, pfc)),
        ptg_perfect(q, tgt_g(q, tg, d, o, v), d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, V.dec(q, Nat.sub(i, SC.pow2(q))), tgt_g_perfect(q, tg, d, o, v, pfg)))

# ---- the source's own pow2 is the spec's; all-zero arrays ----

def fpow2(j: Nat) -> {SG.pow2(j) == SC.pow2(j) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, SG.pow2(p), SC.pow2(p), fpow2(p))

def tree_of_rep(+m: Nat, +k: Nat, +d: Nat, p: Nat, +o: Nat) -> {tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, p, o) == TN.zeros(p) : TN.Node}:
  match p:
    case 0n:
      Equal.cong(U32, TN.Node, z => TN.SLeaf{z}, FL.nthc(SC.replicate(U32, m, 0), Nat.add(SC.pow2(d), o)), 0, FL.nthc_rep(m, Nat.add(SC.pow2(d), o)))
    case 1n+ +q:
      Equal.trans(TN.Node,
        TN.SNode{FL.nthc(SC.replicate(U32, m, 0), Nat.add(o, SC.pow2(q))), FL.nthc(SC.replicate(U32, k, 0), Nat.add(o, SC.pow2(q))), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
        TN.SNode{0, FL.nthc(SC.replicate(U32, k, 0), Nat.add(o, SC.pow2(q))), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
        TN.zeros(1n+q),
        Equal.cong(U32, TN.Node, z => TN.SNode{z, FL.nthc(SC.replicate(U32, k, 0), Nat.add(o, SC.pow2(q))), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.replicate(U32, m, 0), Nat.add(o, SC.pow2(q))), 0, FL.nthc_rep(m, Nat.add(o, SC.pow2(q)))),
        Equal.trans(TN.Node,
          TN.SNode{0, FL.nthc(SC.replicate(U32, k, 0), Nat.add(o, SC.pow2(q))), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
          TN.SNode{0, 0, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
          TN.zeros(1n+q),
          Equal.cong(U32, TN.Node, z => TN.SNode{0, z, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))}, FL.nthc(SC.replicate(U32, k, 0), Nat.add(o, SC.pow2(q))), 0, FL.nthc_rep(k, Nat.add(o, SC.pow2(q)))),
          Equal.trans(TN.Node,
            TN.SNode{0, 0, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
            TN.SNode{0, 0, TN.zeros(q), tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))},
            TN.zeros(1n+q),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{0, 0, z, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q)))}, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, o), TN.zeros(q), tree_of_rep(m, k, d, q, o)),
            Equal.cong(TN.Node, TN.Node, z => TN.SNode{0, 0, TN.zeros(q), z}, tree_of(SC.replicate(U32, m, 0), SC.replicate(U32, k, 0), d, q, Nat.add(o, SC.pow2(q))), TN.zeros(q), tree_of_rep(m, k, d, q, Nat.add(o, SC.pow2(q)))))))
