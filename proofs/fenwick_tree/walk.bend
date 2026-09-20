import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../lib/flat.bend as FL
import ../../spec/common.bend as SC
import ../../src/fenwick_tree.bend as F
import ../../reference/lru/proofs/nat_algebra.bend as NA
import ../lib/u32alg.bend as UA
import ./model.bend as M
import ./arr.bend as AR
import ./tree.bend as T

# The flat layout: which cell of the array holds which part of the model
# tree, and that the index walks of src/fenwick_tree.bend are exactly the
# tree walks of model.bend.
#
#   * the value at index t is cell 2^d + t;
#   * the internal node covering the block [o, o + 2^p) of value indices
#     (p >= 1) is cell o + 2^(p-1), the block's split point.
#
# The cells an internal node of the block [o, o + 2^p) can occupy are exactly
# the indices o+1 .. o+2^p-1, so two sibling blocks never share a cell and a
# walk over one block leaves every cell of the other untouched. That is the
# whole frame argument, and it is plain interval arithmetic -- which is why
# the split-point layout is used here rather than the 2k/2k+1 one, where the
# cells of two sibling subtrees interleave.

# ---- small arithmetic ----

def tree_of(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat) -> M.Node:
  match p:
    case 0n:
      M.FLeaf{FL.nthc(cl, Nat.add(SC.pow2(d), o))}
    case 1n+ +q:
      M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))}

# ---- one cell changed: when does the tree of a block not notice? ----
#
# The internal cells of the block [o, o + 2^p) are the indices o+1 .. o+2^p-1
# and its value cells are 2^d+o .. 2^d+o+2^p-1, so a write anywhere else
# leaves the block's tree alone. `lo`/`hi` are the two sides.

def ne_of_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  N.is_eq_lt(a, b, h)

def frame_int_lo(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(j, o) == True{} : Bool}, +hjd: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, j, v), d, p, o) == tree_of(cl, d, p, o) : M.Node}:
  match p:
    case 0n:
      Equal.cong(U32, M.Node, z => M.FLeaf{z}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)),
        FL.nthc_other(cl, j, Nat.add(SC.pow2(d), o), v, N.is_eq_lt(j, Nat.add(SC.pow2(d), o), N.lt_le_trans(j, SC.pow2(d), Nat.add(SC.pow2(d), o), hjd, FL.base_le(d, o)))))
    case 1n+ +q:
      Equal.trans(M.Node,
        M.FNode{FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))),
          FL.nthc_other(cl, j, Nat.add(o, SC.pow2(q)), v, N.is_eq_lt(j, Nat.add(o, SC.pow2(q)), N.le_lt_trans(j, o, Nat.add(o, SC.pow2(q)), hj, FL.lt_split(o, q))))),
        Equal.trans(M.Node,
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(cl, d, q, o),
            frame_int_lo(cl, d, q, o, j, v, hj, hjd)),
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), z},
            tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, Nat.add(o, SC.pow2(q))),
            frame_int_lo(cl, d, q, Nat.add(o, SC.pow2(q)), j, v, N.le_trans(j, o, Nat.add(o, SC.pow2(q)), hj, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), hjd))))

# ---- a write above the block, and writes to values outside it ----

def frame_int_hi(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +j: Nat, +v: U32, +hj: {Nat.is_le(Nat.add(o, SC.pow2(p)), j) == True{} : Bool}, +hjd: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, j, v), d, p, o) == tree_of(cl, d, p, o) : M.Node}:
  match p:
    case 0n:
      Equal.cong(U32, M.Node, z => M.FLeaf{z}, FL.nthc(SC.update(U32, cl, j, v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)),
        FL.nthc_other(cl, j, Nat.add(SC.pow2(d), o), v, N.is_eq_lt(j, Nat.add(SC.pow2(d), o), N.lt_le_trans(j, SC.pow2(d), Nat.add(SC.pow2(d), o), hjd, FL.base_le(d, o)))))
    case 1n+ +q:
      Equal.trans(M.Node,
        M.FNode{FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          FL.nthc(SC.update(U32, cl, j, v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))),
          FL.nthc_other(cl, j, Nat.add(o, SC.pow2(q)), v, FL.ne_gt(j, Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, FL.mid_lt(o, q), hj)))),
        Equal.trans(M.Node,
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, j, v), d, q, o), tree_of(cl, d, q, o),
            frame_int_hi(cl, d, q, o, j, v, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), j, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hj), hjd)),
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), z},
            tree_of(SC.update(U32, cl, j, v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, Nat.add(o, SC.pow2(q))),
            frame_int_hi(cl, d, q, Nat.add(o, SC.pow2(q)), j, v, L.subst(Nat, k => {Nat.is_le(k, j) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hj), hjd))))

def frame_leaf_lo(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +t: Nat, +v: U32, +ht: {Nat.is_lt(t, o) == True{} : Bool}, +hblk: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, p, o) == tree_of(cl, d, p, o) : M.Node}:
  match p:
    case 0n:
      Equal.cong(U32, M.Node, z => M.FLeaf{z}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)),
        FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), v, N.is_eq_lt(Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), N.lt_add_left(t, o, SC.pow2(d), ht))))
    case 1n+ +q:
      Equal.trans(M.Node,
        M.FNode{FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))),
          FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), Nat.add(SC.pow2(d), t), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hblk), FL.base_le(d, t))))),
        Equal.trans(M.Node,
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(cl, d, q, o),
            frame_leaf_lo(cl, d, q, o, t, v, ht, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hblk))),
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), z},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, Nat.add(o, SC.pow2(q))),
            frame_leaf_lo(cl, d, q, Nat.add(o, SC.pow2(q)), t, v, N.lt_le_trans(t, o, Nat.add(o, SC.pow2(q)), ht, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), L.subst(Nat, k => {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hblk)))))

def frame_leaf_hi(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat, +t: Nat, +v: U32, +ht: {Nat.is_le(Nat.add(o, SC.pow2(p)), t) == True{} : Bool}, +hblk: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, p, o) == tree_of(cl, d, p, o) : M.Node}:
  match p:
    case 0n:
      Equal.cong(U32, M.Node, z => M.FLeaf{z}, FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(SC.pow2(d), o)), FL.nthc(cl, Nat.add(SC.pow2(d), o)),
        FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(SC.pow2(d), o), N.lt_add_left(o, t, SC.pow2(d), N.succ_le_lt(o, t, L.subst(Nat, k => {Nat.is_le(k, t) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), ht))))))
    case 1n+ +q:
      Equal.trans(M.Node,
        M.FNode{FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), Nat.add(o, SC.pow2(q))), FL.nthc(cl, Nat.add(o, SC.pow2(q))),
          FL.nthc_other(cl, Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), v, FL.ne_gt(Nat.add(SC.pow2(d), t), Nat.add(o, SC.pow2(q)), N.lt_le_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), Nat.add(SC.pow2(d), t), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hblk), FL.base_le(d, t))))),
        Equal.trans(M.Node,
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))},
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), z, tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, o), tree_of(cl, d, q, o),
            frame_leaf_hi(cl, d, q, o, t, v, N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), t, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), ht), N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hblk))),
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, o), z},
            tree_of(SC.update(U32, cl, Nat.add(SC.pow2(d), t), v), d, q, Nat.add(o, SC.pow2(q))), tree_of(cl, d, q, Nat.add(o, SC.pow2(q))),
            frame_leaf_hi(cl, d, q, Nat.add(o, SC.pow2(q)), t, v, L.subst(Nat, k => {Nat.is_le(k, t) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), ht), L.subst(Nat, k => {Nat.is_le(k, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hblk)))))

# ---- the walk of a point addition, at the level of cells ----

def acells(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> List<&2, U32>:
  match p left:
    case 0n _:
      SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v))
    case 1n+ +q True{}:
      acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i))
    case 1n+ +q False{}:
      acells(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))))

# A cell below the walked block never changes.
def acells_cell_lo(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(k, o) == True{} : Bool}, +hkd: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}) -> {FL.nthc(acells(p, cl, d, o, i, v, left), k) == FL.nthc(cl, k) : U32}:
  match p left:
    case 0n _:
      FL.nthc_other(cl, Nat.add(SC.pow2(d), o), k, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        FL.ne_gt(Nat.add(SC.pow2(d), o), k, N.lt_le_trans(k, SC.pow2(d), Nat.add(SC.pow2(d), o), hkd, FL.base_le(d, o))))
    case 1n+ +q True{}:
      Equal.trans(U32,
        FL.nthc(acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)), k),
        FL.nthc(SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), k),
        FL.nthc(cl, k),
        acells_cell_lo(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i), k, hk, hkd),
        FL.nthc_other(cl, Nat.add(o, SC.pow2(q)), k, U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v),
          FL.ne_gt(Nat.add(o, SC.pow2(q)), k, N.le_lt_trans(k, o, Nat.add(o, SC.pow2(q)), hk, FL.lt_split(o, q)))))
    case 1n+ +q False{}:
      acells_cell_lo(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), k,
        N.le_trans(k, o, Nat.add(o, SC.pow2(q)), hk, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))), hkd)

# A cell at or above the end of the walked block never changes.
def acells_cell_hi(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +k: Nat, +hk: {Nat.is_le(Nat.add(o, SC.pow2(p)), k) == True{} : Bool}, +hkd: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}) -> {FL.nthc(acells(p, cl, d, o, i, v, left), k) == FL.nthc(cl, k) : U32}:
  match p left:
    case 0n _:
      FL.nthc_other(cl, Nat.add(SC.pow2(d), o), k, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        FL.ne_gt(Nat.add(SC.pow2(d), o), k, N.lt_le_trans(k, SC.pow2(d), Nat.add(SC.pow2(d), o), hkd, FL.base_le(d, o))))
    case 1n+ +q True{}:
      Equal.trans(U32,
        FL.nthc(acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)), k),
        FL.nthc(SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), k),
        FL.nthc(cl, k),
        acells_cell_hi(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i), k,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hk), hkd),
        FL.nthc_other(cl, Nat.add(o, SC.pow2(q)), k, U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v),
          N.is_eq_lt(Nat.add(o, SC.pow2(q)), k, N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), k, FL.mid_lt(o, q), hk))))
    case 1n+ +q False{}:
      acells_cell_hi(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), k,
        L.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hk), hkd)

def acells_length(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> {SC.length(U32, acells(p, cl, d, o, i, v, left)) == SC.length(U32, cl) : Nat}:
  match p left:
    case 0n _:
      LL.length_update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v))
    case 1n+ +q True{}:
      Equal.trans(Nat,
        SC.length(U32, acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i))),
        SC.length(U32, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v))),
        SC.length(U32, cl),
        acells_length(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)),
        LL.length_update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)))
    case 1n+ +q False{}:
      acells_length(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))))

# The tree of a block the walk stays out of does not change.
def acells_tree_hi(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o, SC.pow2(p)), o2) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(acells(p, cl, d, o, i, v, left), d, p2, o2) == tree_of(cl, d, p2, o2) : M.Node}:
  match p left:
    case 0n _:
      frame_leaf_lo(cl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        N.succ_le_lt(o, o2, L.subst(Nat, k => {Nat.is_le(k, o2) == True{} : Bool}, Nat.add(o, 1n), 1n+o, FL.add_one(o), hsep)), hq)
    case 1n+ +q True{}:
      Equal.trans(M.Node,
        tree_of(acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)), d, p2, o2),
        tree_of(SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, p2, o2),
        tree_of(cl, d, p2, o2),
        acells_tree_hi(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i), p2, o2,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hw), hq),
        frame_int_lo(cl, d, p2, o2, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v),
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), o2, N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hsep),
          N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)))
    case 1n+ +q False{}:
      acells_tree_hi(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
        L.subst(Nat, z => {Nat.is_le(z, o2) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hsep),
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq)

def acells_tree_lo(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +p2: Nat, +o2: Nat, +hsep: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), o) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hq: {Nat.is_le(Nat.add(o2, SC.pow2(p2)), SC.pow2(d)) == True{} : Bool}) -> {tree_of(acells(p, cl, d, o, i, v, left), d, p2, o2) == tree_of(cl, d, p2, o2) : M.Node}:
  match p left:
    case 0n _:
      frame_leaf_hi(cl, d, p2, o2, o, U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), hsep, hq)
    case 1n+ +q True{}:
      Equal.trans(M.Node,
        tree_of(acells(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)), d, p2, o2),
        tree_of(SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, p2, o2),
        tree_of(cl, d, p2, o2),
        acells_tree_lo(q, SC.update(U32, cl, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i), p2, o2, hsep,
          N.le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), N.lt_le(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), FL.mid_lt(o, q)), hw), hq),
        frame_int_hi(cl, d, p2, o2, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(cl, Nat.add(o, SC.pow2(q))), v),
          N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
          N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)))
    case 1n+ +q False{}:
      acells_tree_lo(q, cl, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), p2, o2,
        N.le_trans(Nat.add(o2, SC.pow2(p2)), o, Nat.add(o, SC.pow2(q)), hsep, N.lt_le(o, Nat.add(o, SC.pow2(q)), FL.lt_split(o, q))),
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), hq)

def add_ok(p: Nat, +cl: List<&2, U32>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}) -> {tree_of(acells(p, cl, d, o, i, v, left), d, p, o) == M.add_go(p, tree_of(cl, d, p, o), i, v, left) : M.Node}:
  match p left:
    case 0n _:
      Equal.cong(U32, M.Node, z => M.FLeaf{z},
        FL.nthc(SC.update(U32, cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v)), Nat.add(SC.pow2(d), o)),
        U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v),
        FL.nthc_same(cl, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(cl, Nat.add(SC.pow2(d), o)), v), FL.leaf_in_cells(cl, d, o, FL.blk_lo(o, 0n, d, hw), hlen)))
    case 1n+ +q True{}:
      +m = Nat.add(o, SC.pow2(q))
      +S = U32.add(FL.nthc(cl, m), v)
      +cl2 = SC.update(U32, cl, m, S)
      +hm = N.lt_le_trans(m, Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)
      +hwl = N.lt_le(m, SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(m, SC.pow2(q)), FL.split_assoc(o, q), hw)
      +hlen2 = Equal.trans(Nat, SC.length(U32, cl2), SC.length(U32, cl), SC.pow2(1n+d), LL.length_update(U32, cl, m, S), hlen)
      Equal.trans(M.Node,
        M.FNode{FL.nthc(acells(q, cl2, d, o, i, v, M.dec(q, i)), m), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
        M.FNode{S, tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
        M.FNode{S, M.add_go(q, tree_of(cl, d, q, o), i, v, M.dec(q, i)), tree_of(cl, d, q, m)},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
          FL.nthc(acells(q, cl2, d, o, i, v, M.dec(q, i)), m), S,
          Equal.trans(U32, FL.nthc(acells(q, cl2, d, o, i, v, M.dec(q, i)), m), FL.nthc(cl2, m), S,
            acells_cell_hi(q, cl2, d, o, i, v, M.dec(q, i), m, N.le_refl(m), hm),
            FL.nthc_same(cl, m, S, FL.in_cells(cl, d, m, hm, hlen)))),
        Equal.trans(M.Node,
          M.FNode{S, tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
          M.FNode{S, M.add_go(q, tree_of(cl, d, q, o), i, v, M.dec(q, i)), tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
          M.FNode{S, M.add_go(q, tree_of(cl, d, q, o), i, v, M.dec(q, i)), tree_of(cl, d, q, m)},
          Equal.cong(M.Node, M.Node, z => M.FNode{S, z, tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m)},
            tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o), M.add_go(q, tree_of(cl, d, q, o), i, v, M.dec(q, i)),
            %frame_int_hi(cl, d, q, o, m, S, N.le_refl(m), hm) : {tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, o) == M.add_go(q, _, i, v, M.dec(q, i)) : M.Node}
            add_ok(q, cl2, d, o, i, v, M.dec(q, i), hwl, hlen2)),
          Equal.cong(M.Node, M.Node, z => M.FNode{S, M.add_go(q, tree_of(cl, d, q, o), i, v, M.dec(q, i)), z},
            tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m), tree_of(cl, d, q, m),
            Equal.trans(M.Node, tree_of(acells(q, cl2, d, o, i, v, M.dec(q, i)), d, q, m), tree_of(cl2, d, q, m), tree_of(cl, d, q, m),
              acells_tree_hi(q, cl2, d, o, i, v, M.dec(q, i), q, m, N.le_refl(m), hwl, hwr),
              frame_int_lo(cl, d, q, m, m, S, N.le_refl(m), hm)))))
    case 1n+ +q False{}:
      +m = Nat.add(o, SC.pow2(q))
      +hm = N.lt_le_trans(m, Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)
      +hwl = N.lt_le(m, SC.pow2(d), hm)
      +hwr = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(m, SC.pow2(q)), FL.split_assoc(o, q), hw)
      +j = Nat.sub(i, SC.pow2(q))
      Equal.trans(M.Node,
        M.FNode{FL.nthc(acells(q, cl, d, m, j, v, M.dec(q, j)), m), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, o), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
        M.FNode{FL.nthc(cl, m), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, o), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
        M.FNode{FL.nthc(cl, m), tree_of(cl, d, q, o), M.add_go(q, tree_of(cl, d, q, m), j, v, M.dec(q, j))},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, o), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
          FL.nthc(acells(q, cl, d, m, j, v, M.dec(q, j)), m), FL.nthc(cl, m),
          acells_cell_lo(q, cl, d, m, j, v, M.dec(q, j), m, N.le_refl(m), hm)),
        Equal.trans(M.Node,
          M.FNode{FL.nthc(cl, m), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, o), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
          M.FNode{FL.nthc(cl, m), tree_of(cl, d, q, o), tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
          M.FNode{FL.nthc(cl, m), tree_of(cl, d, q, o), M.add_go(q, tree_of(cl, d, q, m), j, v, M.dec(q, j))},
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, m), z, tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m)},
            tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, o), tree_of(cl, d, q, o),
            acells_tree_lo(q, cl, d, m, j, v, M.dec(q, j), q, o, N.le_refl(m), hwr, hwl)),
          Equal.cong(M.Node, M.Node, z => M.FNode{FL.nthc(cl, m), tree_of(cl, d, q, o), z},
            tree_of(acells(q, cl, d, m, j, v, M.dec(q, j)), d, q, m), M.add_go(q, tree_of(cl, d, q, m), j, v, M.dec(q, j)),
            add_ok(q, cl, d, m, j, v, M.dec(q, j), hwr, hlen))))

# ---- the source's own pow2/dec are the spec's ----

def fpow2(k: Nat) -> {F.pow2(k) == SC.pow2(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, F.pow2(p), SC.pow2(p), fpow2(p))

def fdec(d: Nat, +j: Nat) -> {F.dec(d, j) == M.dec(d, j) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Bool, z => Nat.is_lt(j, z), F.pow2(q), SC.pow2(q), fpow2(q))

def dec_h(q: Nat, +i: Nat, +hh: Nat, +ehh: {hh == FL.hof(q) : Nat}) -> {Nat.is_lt(i, hh) == M.dec(q, i) : Bool}:
  match q:
    case 0n:
      %Equal.sym(Nat, hh, FL.hof(0n), ehh) : {Nat.is_lt(i, _) == False{} : Bool}
      N.not_lt_zero(i)
    case 1n+r:
      %Equal.sym(Nat, hh, FL.hof(1n+r), ehh) : {Nat.is_lt(i, _) == Nat.is_lt(i, SC.pow2(r)) : Bool}
      %Equal.sym(Nat, FL.hof(1n+r), SC.pow2(r), FL.hof_succ(r)) : {Nat.is_lt(i, _) == Nat.is_lt(i, SC.pow2(r)) : Bool}
      {==}

def fleaf(+x: U32, i: Nat) -> {F.leaf_prefix(x, i) == M.leaf_prefix(x, i) : U32}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

def prefix_ok(p: Nat, +t: A.Tree<F.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +acc: U32, +o: Nat, +i: Nat, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {F.prefix_go(p, F.pre(p, A.thaw(F.Cel, t), base, h, o), base, h, hh, acc, o, i, left) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(p, tree_of(AR.cl(t), d, p, o), i, left))) : Array<F.Cel> & U32}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {F.prefix_go(0n, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(_, o))), base, h, hh, acc, o, i, left) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(0n, tree_of(AR.cl(t), d, 0n, o), i, left))) : Array<F.Cel> & U32}
      %Equal.sym(Array<F.Cel> & F.Cel, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(SC.pow2(d), o))), (A.thaw(F.Cel, t), AR.cels(A.slots(F.Cel, t), Nat.add(SC.pow2(d), o))), AR.get_ok(1n+d, t, Nat.add(SC.pow2(d), o), hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pf)) : {F.prefix_go(0n, _, base, h, hh, acc, o, i, left) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(0n, tree_of(AR.cl(t), d, 0n, o), i, left))) : Array<F.Cel> & U32}
      %Equal.sym(U32, F.cval(AR.cels(A.slots(F.Cel, t), Nat.add(SC.pow2(d), o))), FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), AR.cval_cels(A.slots(F.Cel, t), Nat.add(SC.pow2(d), o))) : {(A.thaw(F.Cel, t), U32.add(acc, F.leaf_prefix(_, i))) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(0n, tree_of(AR.cl(t), d, 0n, o), i, left))) : Array<F.Cel> & U32}
      %Equal.sym(U32, F.leaf_prefix(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), i), M.leaf_prefix(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), i), fleaf(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), i)) : {(A.thaw(F.Cel, t), U32.add(acc, _)) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(0n, tree_of(AR.cl(t), d, 0n, o), i, left))) : Array<F.Cel> & U32}
      {==}
    case 1n+ +q True{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {F.prefix_go(1n+q, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(o, _))), base, h, hh, acc, o, i, True{}) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, True{}))) : Array<F.Cel> & U32}
      %Equal.sym(Array<F.Cel> & F.Cel, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(F.Cel, t), AR.cels(A.slots(F.Cel, t), Nat.add(o, SC.pow2(q)))), AR.get_ok(1n+d, t, Nat.add(o, SC.pow2(q)), hd, FL.node_lt(o, q, d, hw), pf)) : {F.prefix_go(1n+q, _, base, h, hh, acc, o, i, True{}) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, True{}))) : Array<F.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(i, hh), M.dec(q, i), dec_h(q, i, hh, ehq)) : {F.prefix_go(q, F.pre(q, A.thaw(F.Cel, t), base, hh, o), base, hh, Nat.div(hh, 2n), acc, o, i, _) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(q, tree_of(AR.cl(t), d, q, o), i, M.dec(q, i)))) : Array<F.Cel> & U32}
      prefix_ok(q, t, d, base, hh, Nat.div(hh, 2n), acc, o, i, M.dec(q, i), hd,
        N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)), pf, eb, ehq, {==})
    case 1n+ +q False{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {F.prefix_go(1n+q, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(o, _))), base, h, hh, acc, o, i, False{}) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, False{}))) : Array<F.Cel> & U32}
      %Equal.sym(Array<F.Cel> & F.Cel, Array.get(F.Cel, A.thaw(F.Cel, t), U32.from_nat(Nat.add(o, SC.pow2(q)))), (A.thaw(F.Cel, t), AR.cels(A.slots(F.Cel, t), Nat.add(o, SC.pow2(q)))), AR.get_ok(1n+d, t, Nat.add(o, SC.pow2(q)), hd, FL.node_lt(o, q, d, hw), pf)) : {F.prefix_go(1n+q, _, base, h, hh, acc, o, i, False{}) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, False{}))) : Array<F.Cel> & U32}
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {F.prefix_go(q, F.pre(q, A.thaw(F.Cel, t), base, hh, Nat.add(o, _)), base, hh, Nat.div(hh, 2n), U32.add(acc, F.cval(AR.cels(A.slots(F.Cel, t), Nat.add(o, SC.pow2(q))))), Nat.add(o, _), Nat.sub(i, _), Nat.is_lt(Nat.sub(i, _), hh)) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, False{}))) : Array<F.Cel> & U32}
      %Equal.sym(U32, F.cval(AR.cels(A.slots(F.Cel, t), Nat.add(o, SC.pow2(q)))), FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), AR.cval_cels(A.slots(F.Cel, t), Nat.add(o, SC.pow2(q)))) : {F.prefix_go(q, F.pre(q, A.thaw(F.Cel, t), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, _), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh)) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, False{}))) : Array<F.Cel> & U32}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh), M.dec(q, Nat.sub(i, SC.pow2(q))), dec_h(q, Nat.sub(i, SC.pow2(q)), hh, ehq)) : {F.prefix_go(q, F.pre(q, A.thaw(F.Cel, t), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), _) == (A.thaw(F.Cel, t), U32.add(acc, M.prefix_go(1n+q, tree_of(AR.cl(t), d, 1n+q, o), i, False{}))) : Array<F.Cel> & U32}
      %UA.assoc(acc, FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), M.prefix_go(q, tree_of(AR.cl(t), d, q, Nat.add(o, SC.pow2(q))), Nat.sub(i, SC.pow2(q)), M.dec(q, Nat.sub(i, SC.pow2(q))))) : {F.prefix_go(q, F.pre(q, A.thaw(F.Cel, t), base, hh, Nat.add(o, SC.pow2(q))), base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), M.dec(q, Nat.sub(i, SC.pow2(q)))) == (A.thaw(F.Cel, t), _) : Array<F.Cel> & U32}
      prefix_ok(q, t, d, base, hh, Nat.div(hh, 2n), U32.add(acc, FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q)))), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), M.dec(q, Nat.sub(i, SC.pow2(q))), hd,
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pf, eb, ehq, {==})

# ---- the same walk on the mirror tree of the array ----

def atree(p: Nat, +t: A.Tree<F.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool) -> A.Tree<F.Cel>:
  match p left:
    case 0n _:
      A.upd(F.Cel, 1n+d, t, Nat.add(SC.pow2(d), o), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), v)})
    case 1n+ +q True{}:
      atree(q, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}), d, o, i, v, M.dec(q, i))
    case 1n+ +q False{}:
      atree(q, t, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))))

def atree_perfect(p: Nat, +t: A.Tree<F.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +pf: {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}) -> {A.perfect(F.Cel, 1n+d, atree(p, t, d, o, i, v, left)) == True{} : Bool}:
  match p left:
    case 0n _:
      A.upd_perfect(F.Cel, 1n+d, t, Nat.add(SC.pow2(d), o), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), v)}, pf)
    case 1n+ +q True{}:
      atree_perfect(q, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}), d, o, i, v, M.dec(q, i),
        A.upd_perfect(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}, pf))
    case 1n+ +q False{}:
      atree_perfect(q, t, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), pf)

def atree_cl(p: Nat, +t: A.Tree<F.Cel>, +d: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}) -> {AR.cl(atree(p, t, d, o, i, v, left)) == acells(p, AR.cl(t), d, o, i, v, left) : List<&2, U32>}:
  match p left:
    case 0n _:
      AR.cl_upd(1n+d, t, Nat.add(SC.pow2(d), o), U32.add(FL.nthc(AR.cl(t), Nat.add(SC.pow2(d), o)), v), FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pf)
    case 1n+ +q True{}:
      Equal.trans(List<&2, U32>,
        AR.cl(atree(q, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}), d, o, i, v, M.dec(q, i))),
        acells(q, AR.cl(A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)})), d, o, i, v, M.dec(q, i)),
        acells(q, SC.update(U32, AR.cl(t), Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)), d, o, i, v, M.dec(q, i)),
        atree_cl(q, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}), d, o, i, v, M.dec(q, i),
          N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)),
          A.upd_perfect(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}, pf)),
        Equal.cong(List<&2, U32>, List<&2, U32>, z => acells(q, z, d, o, i, v, M.dec(q, i)),
          AR.cl(A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)})),
          SC.update(U32, AR.cl(t), Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)),
          AR.cl_upd(1n+d, t, Nat.add(o, SC.pow2(q)), U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v), FL.node_lt(o, q, d, hw), pf)))
    case 1n+ +q False{}:
      atree_cl(q, t, d, Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))),
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pf)

def add_thaw(p: Nat, +t: A.Tree<F.Cel>, +d: Nat, +base: Nat, +h: Nat, +hh: Nat, +o: Nat, +i: Nat, +v: U32, left: Bool, +hd: {Nat.is_lt(1n+d, 32n) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}, +pf: {A.perfect(F.Cel, 1n+d, t) == True{} : Bool}, +eb: {base == SC.pow2(d) : Nat}, +eh: {h == FL.hof(p) : Nat}, +ehh: {hh == Nat.div(h, 2n) : Nat}) -> {F.add_go(p, A.thaw(F.Cel, t), base, h, hh, o, i, v, left) == A.thaw(F.Cel, atree(p, t, d, o, i, v, left)) : Array<F.Cel>}:
  match p left:
    case 0n _:
      %Equal.sym(Nat, base, SC.pow2(d), eb) : {F.bump(A.thaw(F.Cel, t), Nat.add(_, o), v) == A.thaw(F.Cel, atree(0n, t, d, o, i, v, left)) : Array<F.Cel>}
      AR.bump_ok(1n+d, t, Nat.add(SC.pow2(d), o), v, hd, FL.leaf_lt(d, o, FL.blk_lo(o, 0n, d, hw)), pf)
    case 1n+ +q True{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {F.add_go(q, F.bump(A.thaw(F.Cel, t), Nat.add(o, _), v), base, hh, Nat.div(hh, 2n), o, i, v, Nat.is_lt(i, hh)) == A.thaw(F.Cel, atree(1n+q, t, d, o, i, v, True{})) : Array<F.Cel>}
      %Equal.sym(Bool, Nat.is_lt(i, hh), M.dec(q, i), dec_h(q, i, hh, ehq)) : {F.add_go(q, F.bump(A.thaw(F.Cel, t), Nat.add(o, SC.pow2(q)), v), base, hh, Nat.div(hh, 2n), o, i, v, _) == A.thaw(F.Cel, atree(1n+q, t, d, o, i, v, True{})) : Array<F.Cel>}
      %Equal.sym(Array<F.Cel>, F.bump(A.thaw(F.Cel, t), Nat.add(o, SC.pow2(q)), v), A.thaw(F.Cel, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)})), AR.bump_ok(1n+d, t, Nat.add(o, SC.pow2(q)), v, hd, FL.node_lt(o, q, d, hw), pf)) : {F.add_go(q, _, base, hh, Nat.div(hh, 2n), o, i, v, M.dec(q, i)) == A.thaw(F.Cel, atree(1n+q, t, d, o, i, v, True{})) : Array<F.Cel>}
      add_thaw(q, A.upd(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}), d, base, hh, Nat.div(hh, 2n), o, i, v, M.dec(q, i), hd,
        N.lt_le(Nat.add(o, SC.pow2(q)), SC.pow2(d), N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), FL.mid_lt(o, q), hw)),
        A.upd_perfect(F.Cel, 1n+d, t, Nat.add(o, SC.pow2(q)), F.CV{U32.add(FL.nthc(AR.cl(t), Nat.add(o, SC.pow2(q))), v)}, pf), eb, ehq, {==})
    case 1n+ +q False{}:
      +eh2 = Equal.trans(Nat, h, FL.hof(1n+q), SC.pow2(q), eh, FL.hof_succ(q))
      +ehq = Equal.trans(Nat, hh, Nat.div(h, 2n), FL.hof(q), ehh, Equal.cong(Nat, Nat, z => Nat.div(z, 2n), h, SC.pow2(q), eh2))
      %Equal.sym(Nat, h, SC.pow2(q), eh2) : {F.add_go(q, A.thaw(F.Cel, t), base, hh, Nat.div(hh, 2n), Nat.add(o, _), Nat.sub(i, _), v, Nat.is_lt(Nat.sub(i, _), hh)) == A.thaw(F.Cel, atree(1n+q, t, d, o, i, v, False{})) : Array<F.Cel>}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(i, SC.pow2(q)), hh), M.dec(q, Nat.sub(i, SC.pow2(q))), dec_h(q, Nat.sub(i, SC.pow2(q)), hh, ehq)) : {F.add_go(q, A.thaw(F.Cel, t), base, hh, Nat.div(hh, 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, _) == A.thaw(F.Cel, atree(1n+q, t, d, o, i, v, False{})) : Array<F.Cel>}
      add_thaw(q, t, d, base, hh, Nat.div(hh, 2n), Nat.add(o, SC.pow2(q)), Nat.sub(i, SC.pow2(q)), v, M.dec(q, Nat.sub(i, SC.pow2(q))), hd,
        L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), FL.split_assoc(o, q), hw), pf, eb, ehq, {==})

# ---- shape of the tree the cells realise ----

def tree_perfect(+cl: List<&2, U32>, +d: Nat, p: Nat, +o: Nat) -> {T.perfect(p, tree_of(cl, d, p, o)) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      L.and_intro(T.perfect(q, tree_of(cl, d, q, o)), T.perfect(q, tree_of(cl, d, q, Nat.add(o, SC.pow2(q)))),
        tree_perfect(cl, d, q, o), tree_perfect(cl, d, q, Nat.add(o, SC.pow2(q))))

def tree_of_rep(+m: Nat, +d: Nat, p: Nat, +o: Nat) -> {tree_of(SC.replicate(U32, m, 0), d, p, o) == M.zeros(p) : M.Node}:
  match p:
    case 0n:
      Equal.cong(U32, M.Node, z => M.FLeaf{z}, FL.nthc(SC.replicate(U32, m, 0), Nat.add(SC.pow2(d), o)), 0, FL.nthc_rep(m, Nat.add(SC.pow2(d), o)))
    case 1n+ +q:
      Equal.trans(M.Node,
        M.FNode{FL.nthc(SC.replicate(U32, m, 0), Nat.add(o, SC.pow2(q))), tree_of(SC.replicate(U32, m, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{0, tree_of(SC.replicate(U32, m, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
        M.FNode{0, M.zeros(q), M.zeros(q)},
        Equal.cong(U32, M.Node, z => M.FNode{z, tree_of(SC.replicate(U32, m, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
          FL.nthc(SC.replicate(U32, m, 0), Nat.add(o, SC.pow2(q))), 0, FL.nthc_rep(m, Nat.add(o, SC.pow2(q)))),
        Equal.trans(M.Node,
          M.FNode{0, tree_of(SC.replicate(U32, m, 0), d, q, o), tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{0, M.zeros(q), tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
          M.FNode{0, M.zeros(q), M.zeros(q)},
          Equal.cong(M.Node, M.Node, z => M.FNode{0, z, tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q)))},
            tree_of(SC.replicate(U32, m, 0), d, q, o), M.zeros(q), tree_of_rep(m, d, q, o)),
          Equal.cong(M.Node, M.Node, z => M.FNode{0, M.zeros(q), z},
            tree_of(SC.replicate(U32, m, 0), d, q, Nat.add(o, SC.pow2(q))), M.zeros(q), tree_of_rep(m, d, q, Nat.add(o, SC.pow2(q))))))
