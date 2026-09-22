import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../reference/legacy_balanced_search_tree.bend as B
import ../../types/balanced_search_tree.bend as E
import ./sorted.bend as SO
import ./specops.bend as SP

# Red-black binary search trees.
#
#   io    the in-order entry list (the abstraction into the spec's model)
#   bh    the black height (number of black nodes on the leftmost path)
#   ok    every node: both subtrees ok, their black heights agree, and a red
#         node has no red child
#   bal   the red-black invariant of a whole tree: ok and a black root
#
# Insertion (Okasaki) refines the spec's sorted insertion and preserves the
# invariant; `ins` may leave one red-red edge at the very root, which
# `blacken` removes. Deletion (the conventional fixup, TD/UF) refines the
# spec's deletion and preserves the invariant as well.

def io(-K: Data, -V: Data, t: B.Tree<K, V>) -> List<&2, E.Entry<K, V>>:
  match t:
    case B.Leaf{}:
      Nil{}
    case B.Node{c, l, e, r}:
      SC.append(E.Entry<K, V>, io(K, V, l), Con{e, io(K, V, r)})

# The in-order list of a node with the given pieces.
def nio(-K: Data, -V: Data, l: B.Tree<K, V>, e: E.Entry<K, V>, r: B.Tree<K, V>) -> List<&2, E.Entry<K, V>>:
  SC.append(E.Entry<K, V>, io(K, V, l), Con{e, io(K, V, r)})

def iod(-K: Data, -V: Data, u: B.UpD<K, V>) -> List<&2, E.Entry<K, V>>:
  match u:
    case B.TD{t}:
      io(K, V, t)
    case B.UF{t}:
      io(K, V, t)

# ---- sortedness facts at a node (shared with insertion and deletion) ----

def s2_l(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +s: {SO.sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, l, Con{e, r})) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, l) == True{} : Bool}:
  SO.so_left(~K, ~cmp, V, l, Con{e, r}, s)

def s2_r(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +s: {SO.sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, l, Con{e, r})) == True{} : Bool}) -> {SO.sorted(~K, ~cmp, V, r) == True{} : Bool}:
  SO.so_tail(~K, ~cmp, V, e, r, SO.so_right(~K, ~cmp, V, l, Con{e, r}, s))

def s2_bl(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +s: {SO.sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, l, Con{e, r})) == True{} : Bool}) -> {SO.below(~K, ~cmp, V, l, E.key(K, V, e)) == True{} : Bool}:
  SO.so_below(~K, ~cmp, V, l, e, r, s)

def s2_ab(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +r: List<&2, E.Entry<K, V>>, +s: {SO.sorted(~K, ~cmp, V, SC.append(E.Entry<K, V>, l, Con{e, r})) == True{} : Bool}) -> {SO.above(~K, ~cmp, V, r, E.key(K, V, e)) == True{} : Bool}:
  SO.so_above(~K, ~cmp, V, e, r, SO.so_right(~K, ~cmp, V, l, Con{e, r}, s))

def eq_flip(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +a: K, +b: K, +h: {cmp(a, b) == EQ{} : Cmp}) -> {cmp(b, a) == EQ{} : Cmp}:
  %Equal.sym(Cmp, cmp(b, a), O.flipc(cmp(a, b)), O.flip(~K, ~cmp, o, a, b)) : {_ == EQ{} : Cmp}
  %Equal.sym(Cmp, cmp(a, b), EQ{}, h) : {O.flipc(_) == EQ{} : Cmp}
  {==}

def bl_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +k: K, +hb: {SO.below(~K, ~cmp, V, l, E.key(K, V, e)) == True{} : Bool}, +h: {cmp(k, E.key(K, V, e)) == EQ{} : Cmp}) -> {SO.below(~K, ~cmp, V, l, k) == True{} : Bool}:
  SO.below_eq(~K, ~cmp, ~o, V, l, E.key(K, V, e), k, hb, eq_flip(~K, ~cmp, ~o, k, E.key(K, V, e), h))

def bl_gt(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +l: List<&2, E.Entry<K, V>>, +e: E.Entry<K, V>, +k: K, +hb: {SO.below(~K, ~cmp, V, l, E.key(K, V, e)) == True{} : Bool}, +h: {cmp(k, E.key(K, V, e)) == GT{} : Cmp}) -> {SO.below(~K, ~cmp, V, l, k) == True{} : Bool}:
  SO.below_lt(~K, ~cmp, ~o, V, l, E.key(K, V, e), k, hb, SO.lt_of_gt(~K, ~cmp, ~o, k, E.key(K, V, e), h))

# ---- the in-order list is unchanged by `balance` ----
#
# Every rotation case reassociates the same entries; one use of
# append-associativity per case.

def rot_io(-K: Data, -V: Data, +a: List<&2, E.Entry<K, V>>, +x: E.Entry<K, V>, +b: List<&2, E.Entry<K, V>>, +y: E.Entry<K, V>, +cc: List<&2, E.Entry<K, V>>) -> {SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, a, Con{x, b}), Con{y, cc}) == SC.append(E.Entry<K, V>, a, Con{x, SC.append(E.Entry<K, V>, b, Con{y, cc})}) : List<&2, E.Entry<K, V>>}:
  LL.append_assoc(E.Entry<K, V>, a, Con{x, b}, Con{y, cc})

def bal_rc1_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cd: B.Color, +c1t: B.Tree<K, V>, +z: E.Entry<K, V>, +c2t: B.Tree<K, V>) -> {io(K, V, B.bal_rc1(K, V, l, e, b, y, cd, c1t, z, c2t)) == nio(K, V, l, e, B.Node{B.R{}, b, y, B.Node{cd, c1t, z, c2t}}) : List<&2, E.Entry<K, V>>}:
  match cd:
    case B.R{}:
      rot_io(K, V, io(K, V, l), e, io(K, V, b), y, SC.append(E.Entry<K, V>, io(K, V, c1t), Con{z, io(K, V, c2t)}))
    case B.B{}:
      {==}

def bal_rc_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {io(K, V, B.bal_rc(K, V, l, e, b, y, cc)) == nio(K, V, l, e, B.Node{B.R{}, b, y, cc}) : List<&2, E.Entry<K, V>>}:
  match cc:
    case B.Leaf{}:
      {==}
    case B.Node{+cd, +c1t, +z, +c2t}:
      bal_rc1_io(K, V, l, e, b, y, cd, c1t, z, c2t)

def bal_rb1_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cb: B.Color, +b1: B.Tree<K, V>, +w: E.Entry<K, V>, +b2: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {io(K, V, B.bal_rb1(K, V, l, e, cb, b1, w, b2, y, cc)) == nio(K, V, l, e, B.Node{B.R{}, B.Node{cb, b1, w, b2}, y, cc}) : List<&2, E.Entry<K, V>>}:
  match cb:
    case B.R{}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, SC.append(EE, io(K, V, l), Con{e, io(K, V, b1)}), Con{w, SC.append(EE, io(K, V, b2), Con{y, io(K, V, cc)})}),
        SC.append(EE, io(K, V, l), Con{e, SC.append(EE, io(K, V, b1), Con{w, SC.append(EE, io(K, V, b2), Con{y, io(K, V, cc)})})}),
        SC.append(EE, io(K, V, l), Con{e, SC.append(EE, SC.append(EE, io(K, V, b1), Con{w, io(K, V, b2)}), Con{y, io(K, V, cc)})}),
        rot_io(K, V, io(K, V, l), e, io(K, V, b1), w, SC.append(EE, io(K, V, b2), Con{y, io(K, V, cc)})),
        Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, io(K, V, l), Con{e, ys}),
          SC.append(EE, io(K, V, b1), Con{w, SC.append(EE, io(K, V, b2), Con{y, io(K, V, cc)})}),
          SC.append(EE, SC.append(EE, io(K, V, b1), Con{w, io(K, V, b2)}), Con{y, io(K, V, cc)}),
          Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, io(K, V, b1), Con{w, io(K, V, b2)}), Con{y, io(K, V, cc)}), SC.append(EE, io(K, V, b1), Con{w, SC.append(EE, io(K, V, b2), Con{y, io(K, V, cc)})}), rot_io(K, V, io(K, V, b1), w, io(K, V, b2), y, io(K, V, cc)))))
    case B.B{}:
      bal_rc_io(K, V, l, e, B.Node{B.B{}, b1, w, b2}, y, cc)

def bal_rb_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {io(K, V, B.bal_rb(K, V, l, e, b, y, cc)) == nio(K, V, l, e, B.Node{B.R{}, b, y, cc}) : List<&2, E.Entry<K, V>>}:
  match b:
    case B.Leaf{}:
      bal_rc_io(K, V, l, e, B.Leaf{}, y, cc)
    case B.Node{+cb, +b1, +w, +b2}:
      bal_rb1_io(K, V, l, e, cb, b1, w, b2, y, cc)

def bal_right1_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cr: B.Color, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>) -> {io(K, V, B.bal_right1(K, V, l, e, cr, rl, re, rr)) == nio(K, V, l, e, B.Node{cr, rl, re, rr}) : List<&2, E.Entry<K, V>>}:
  match cr:
    case B.R{}:
      bal_rb_io(K, V, l, e, rl, re, rr)
    case B.B{}:
      {==}

def bal_right_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_right(K, V, l, e, r)) == nio(K, V, l, e, r) : List<&2, E.Entry<K, V>>}:
  match r:
    case B.Leaf{}:
      {==}
    case B.Node{+cr, +rl, +re, +rr}:
      bal_right1_io(K, V, l, e, cr, rl, re, rr)

def bal_lb1_io(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +cb: B.Color, +b1: B.Tree<K, V>, +y: E.Entry<K, V>, +b2: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_lb1(K, V, a, x, cb, b1, y, b2, e, r)) == nio(K, V, B.Node{B.R{}, a, x, B.Node{cb, b1, y, b2}}, e, r) : List<&2, E.Entry<K, V>>}:
  match cb:
    case B.R{}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b1)}), Con{y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})}),
        SC.append(EE, io(K, V, a), Con{x, SC.append(EE, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)}), Con{e, io(K, V, r)})}),
        SC.append(EE, SC.append(EE, io(K, V, a), Con{x, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)})}), Con{e, io(K, V, r)}),
        Equal.trans(List<&2, EE>,
          SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b1)}), Con{y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})}),
          SC.append(EE, io(K, V, a), Con{x, SC.append(EE, io(K, V, b1), Con{y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})})}),
          SC.append(EE, io(K, V, a), Con{x, SC.append(EE, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)}), Con{e, io(K, V, r)})}),
          rot_io(K, V, io(K, V, a), x, io(K, V, b1), y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})),
          Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, io(K, V, a), Con{x, ys}),
            SC.append(EE, io(K, V, b1), Con{y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})}),
            SC.append(EE, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)}), Con{e, io(K, V, r)}),
            Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)}), Con{e, io(K, V, r)}), SC.append(EE, io(K, V, b1), Con{y, SC.append(EE, io(K, V, b2), Con{e, io(K, V, r)})}), rot_io(K, V, io(K, V, b1), y, io(K, V, b2), e, io(K, V, r))))),
        Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, io(K, V, a), Con{x, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)})}), Con{e, io(K, V, r)}), SC.append(EE, io(K, V, a), Con{x, SC.append(EE, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)}), Con{e, io(K, V, r)})}), LL.append_assoc(EE, io(K, V, a), Con{x, SC.append(EE, io(K, V, b1), Con{y, io(K, V, b2)})}, Con{e, io(K, V, r)})))
    case B.B{}:
      bal_right_io(K, V, B.Node{B.R{}, a, x, B.Node{B.B{}, b1, y, b2}}, e, r)

def bal_lb_io(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_lb(K, V, a, x, b, e, r)) == nio(K, V, B.Node{B.R{}, a, x, b}, e, r) : List<&2, E.Entry<K, V>>}:
  match b:
    case B.Leaf{}:
      bal_right_io(K, V, B.Node{B.R{}, a, x, B.Leaf{}}, e, r)
    case B.Node{+cb, +b1, +y, +b2}:
      bal_lb1_io(K, V, a, x, cb, b1, y, b2, e, r)

def bal_la_io(-K: Data, -V: Data, +ca: B.Color, +a1: B.Tree<K, V>, +y: E.Entry<K, V>, +a2: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_la(K, V, ca, a1, y, a2, x, b, e, r)) == nio(K, V, B.Node{B.R{}, B.Node{ca, a1, y, a2}, x, b}, e, r) : List<&2, E.Entry<K, V>>}:
  match ca:
    case B.R{}:
      -EE = E.Entry<K, V>
      Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, SC.append(EE, io(K, V, a1), Con{y, io(K, V, a2)}), Con{x, io(K, V, b)}), Con{e, io(K, V, r)}), SC.append(EE, SC.append(EE, io(K, V, a1), Con{y, io(K, V, a2)}), Con{x, SC.append(EE, io(K, V, b), Con{e, io(K, V, r)})}), LL.append_assoc(EE, SC.append(EE, io(K, V, a1), Con{y, io(K, V, a2)}), Con{x, io(K, V, b)}, Con{e, io(K, V, r)}))
    case B.B{}:
      bal_lb_io(K, V, B.Node{B.B{}, a1, y, a2}, x, b, e, r)

def bal_l_io(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_l(K, V, a, x, b, e, r)) == nio(K, V, B.Node{B.R{}, a, x, b}, e, r) : List<&2, E.Entry<K, V>>}:
  match a:
    case B.Leaf{}:
      bal_lb_io(K, V, B.Leaf{}, x, b, e, r)
    case B.Node{+ca, +a1, +y, +a2}:
      bal_la_io(K, V, ca, a1, y, a2, x, b, e, r)

def bal_left1_io(-K: Data, -V: Data, +cl: B.Color, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_left1(K, V, cl, ll, le, lr, e, r)) == nio(K, V, B.Node{cl, ll, le, lr}, e, r) : List<&2, E.Entry<K, V>>}:
  match cl:
    case B.R{}:
      bal_l_io(K, V, ll, le, lr, e, r)
    case B.B{}:
      bal_right_io(K, V, B.Node{B.B{}, ll, le, lr}, e, r)

def bal_black_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.bal_black(K, V, l, e, r)) == nio(K, V, l, e, r) : List<&2, E.Entry<K, V>>}:
  match l:
    case B.Leaf{}:
      bal_right_io(K, V, B.Leaf{}, e, r)
    case B.Node{+cl, +ll, +le, +lr}:
      bal_left1_io(K, V, cl, ll, le, lr, e, r)

def balance_io(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {io(K, V, B.balance(K, V, c, l, e, r)) == nio(K, V, l, e, r) : List<&2, E.Entry<K, V>>}:
  match c:
    case B.R{}:
      {==}
    case B.B{}:
      bal_black_io(K, V, l, e, r)

# ---- insertion refines the spec's sorted insertion ----

def ins_io(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, a: Cmp, +ea: {B.c1(~K, ~cmp, V, k, t) == a : Cmp}, +s: {SO.sorted(~K, ~cmp, V, io(K, V, t)) == True{} : Bool}) -> {io(K, V, B.ins(~K, ~cmp, V, t, k, v, a)) == S.ins(~K, ~cmp, V, k, v, io(K, V, t)) : List<&2, E.Entry<K, V>>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{+c, +l, +e, +r} LT{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +u = B.ins(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l))
      Equal.trans(LE, io(K, V, B.balance(K, V, c, u, e, r)), SC.append(EE, io(K, V, u), Con{e, io(K, V, r)}), S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
        balance_io(K, V, c, u, e, r),
        Equal.trans(LE, SC.append(EE, io(K, V, u), Con{e, io(K, V, r)}), SC.append(EE, S.ins(~K, ~cmp, V, k, v, io(K, V, l)), Con{e, io(K, V, r)}), S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
          Equal.cong(LE, LE, xs => SC.append(EE, xs, Con{e, io(K, V, r)}), io(K, V, u), S.ins(~K, ~cmp, V, k, v, io(K, V, l)), ins_io(~K, ~cmp, ~o, V, l, k, v, B.c1(~K, ~cmp, V, k, l), {==}, s2_l(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s))),
          Equal.sym(LE, S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, S.ins(~K, ~cmp, V, k, v, io(K, V, l)), Con{e, io(K, V, r)}), SP.ins_left(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), k, v, ea))))
    case B.Node{+c, +l, +e, +r} EQ{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +bl = bl_eq(~K, ~cmp, ~o, V, io(K, V, l), e, k, s2_bl(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ea)
      Equal.sym(LE, S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{E.Entry{k, v}, io(K, V, r)}),
        Equal.trans(LE, S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), S.ins(~K, ~cmp, V, k, v, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{E.Entry{k, v}, io(K, V, r)}),
          SP.ins_pass(~K, ~cmp, ~o, V, io(K, V, l), Con{e, io(K, V, r)}, k, v, bl),
          Equal.cong(LE, LE, ys => SC.append(EE, io(K, V, l), ys), S.ins(~K, ~cmp, V, k, v, Con{e, io(K, V, r)}), Con{E.Entry{k, v}, io(K, V, r)}, SP.ins_eq(~K, ~cmp, V, e, io(K, V, r), k, v, ea))))
    case B.Node{+c, +l, +e, +r} GT{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +u = B.ins(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r))
      +bl = bl_gt(~K, ~cmp, ~o, V, io(K, V, l), e, k, s2_bl(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ea)
      Equal.trans(LE, io(K, V, B.balance(K, V, c, l, e, u)), SC.append(EE, io(K, V, l), Con{e, io(K, V, u)}), S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
        balance_io(K, V, c, l, e, u),
        Equal.trans(LE, SC.append(EE, io(K, V, l), Con{e, io(K, V, u)}), SC.append(EE, io(K, V, l), Con{e, S.ins(~K, ~cmp, V, k, v, io(K, V, r))}), S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
          Equal.cong(LE, LE, xs => SC.append(EE, io(K, V, l), Con{e, xs}), io(K, V, u), S.ins(~K, ~cmp, V, k, v, io(K, V, r)), ins_io(~K, ~cmp, ~o, V, r, k, v, B.c1(~K, ~cmp, V, k, r), {==}, s2_r(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s))),
          Equal.sym(LE, S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{e, S.ins(~K, ~cmp, V, k, v, io(K, V, r))}),
            Equal.trans(LE, S.ins(~K, ~cmp, V, k, v, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), S.ins(~K, ~cmp, V, k, v, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{e, S.ins(~K, ~cmp, V, k, v, io(K, V, r))}),
              SP.ins_pass(~K, ~cmp, ~o, V, io(K, V, l), Con{e, io(K, V, r)}, k, v, bl),
              Equal.cong(LE, LE, ys => SC.append(EE, io(K, V, l), ys), S.ins(~K, ~cmp, V, k, v, Con{e, io(K, V, r)}), Con{e, S.ins(~K, ~cmp, V, k, v, io(K, V, r))}, SP.ins_gt(~K, ~cmp, V, e, io(K, V, r), k, v, ea))))))

def blacken_io(-K: Data, -V: Data, +t: B.Tree<K, V>) -> {io(K, V, B.blacken(K, V, t)) == io(K, V, t) : List<&2, E.Entry<K, V>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      {==}

def insert_io(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, +s: {SO.sorted(~K, ~cmp, V, io(K, V, t)) == True{} : Bool}) -> {io(K, V, B.insert_tree(~K, ~cmp, V, t, k, v)) == S.ins(~K, ~cmp, V, k, v, io(K, V, t)) : List<&2, E.Entry<K, V>>}:
  Equal.trans(List<&2, E.Entry<K, V>>, io(K, V, B.blacken(K, V, B.ins(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t)))), io(K, V, B.ins(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t))), S.ins(~K, ~cmp, V, k, v, io(K, V, t)),
    blacken_io(K, V, B.ins(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t))),
    ins_io(~K, ~cmp, ~o, V, t, k, v, B.c1(~K, ~cmp, V, k, t), {==}, s))

# ============================ the red-black invariant ======================

def bh_c(c: B.Color, +h: Nat) -> Nat:
  match c:
    case B.R{}:
      h
    case B.B{}:
      1n+h

# Black height: the number of black nodes on the leftmost path.
def bh(-K: Data, -V: Data, t: B.Tree<K, V>) -> Nat:
  match t:
    case B.Leaf{}:
      0n
    case B.Node{c, l, e, r}:
      bh_c(c, bh(K, V, l))

# A red node has no red child.
def nrr_c(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>) -> Bool:
  match c:
    case B.R{}:
      Bool.and(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)))
    case B.B{}:
      True{}

# Every node: both subtrees are ok, their black heights agree, and a red node
# has no red child.
def ok(-K: Data, -V: Data, t: B.Tree<K, V>) -> Bool:
  match t:
    case B.Leaf{}:
      True{}
    case B.Node{c, +l, e, +r}:
      Bool.and(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)))

# `ok` without the colour condition at the root: what an insertion may leave
# behind before the root is blackened.
def okt(-K: Data, -V: Data, t: B.Tree<K, V>) -> Bool:
  match t:
    case B.Leaf{}:
      True{}
    case B.Node{c, +l, e, +r}:
      Bool.and(Bool.and(ok(K, V, l), ok(K, V, r)), Nat.is_eq(bh(K, V, l), bh(K, V, r)))

# The whole-tree invariant: a black root and `ok`.
def bal(-K: Data, -V: Data, +t: B.Tree<K, V>) -> Bool:
  Bool.and(Bool.not(B.is_red(K, V, t)), ok(K, V, t))

# ---- accessors ----

def ok_l(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {ok(K, V, l) == True{} : Bool}:
  L.and_left(ok(K, V, l), ok(K, V, r), L.and_left(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)), h))

def ok_r(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {ok(K, V, r) == True{} : Bool}:
  L.and_right(ok(K, V, l), ok(K, V, r), L.and_left(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)), h))

def ok_h(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {bh(K, V, l) == bh(K, V, r) : Nat}:
  N.eq_from_is_eq(bh(K, V, l), bh(K, V, r), L.and_left(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r), L.and_right(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)), h)))

def ok_n(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {nrr_c(K, V, c, l, r) == True{} : Bool}:
  L.and_right(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r), L.and_right(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)), h))

def ok_mk(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +a: {ok(K, V, l) == True{} : Bool}, +b: {ok(K, V, r) == True{} : Bool}, +eh: {bh(K, V, l) == bh(K, V, r) : Nat}, +nn: {nrr_c(K, V, c, l, r) == True{} : Bool}) -> {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}:
  L.and_intro(Bool.and(ok(K, V, l), ok(K, V, r)), Bool.and(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r)),
    L.and_intro(ok(K, V, l), ok(K, V, r), a, b),
    L.and_intro(Nat.is_eq(bh(K, V, l), bh(K, V, r)), nrr_c(K, V, c, l, r), L.subst(Nat, x => {Nat.is_eq(bh(K, V, l), x) == True{} : Bool}, bh(K, V, l), bh(K, V, r), eh, N.is_eq_refl(bh(K, V, l))), nn))

def okt_l(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {okt(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {ok(K, V, l) == True{} : Bool}:
  L.and_left(ok(K, V, l), ok(K, V, r), L.and_left(Bool.and(ok(K, V, l), ok(K, V, r)), Nat.is_eq(bh(K, V, l), bh(K, V, r)), h))

def okt_r(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {okt(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {ok(K, V, r) == True{} : Bool}:
  L.and_right(ok(K, V, l), ok(K, V, r), L.and_left(Bool.and(ok(K, V, l), ok(K, V, r)), Nat.is_eq(bh(K, V, l), bh(K, V, r)), h))

def okt_h(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {okt(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> {bh(K, V, l) == bh(K, V, r) : Nat}:
  N.eq_from_is_eq(bh(K, V, l), bh(K, V, r), L.and_right(Bool.and(ok(K, V, l), ok(K, V, r)), Nat.is_eq(bh(K, V, l), bh(K, V, r)), h))

def okt_mk(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +a: {ok(K, V, l) == True{} : Bool}, +b: {ok(K, V, r) == True{} : Bool}, +eh: {bh(K, V, l) == bh(K, V, r) : Nat}) -> {okt(K, V, B.Node{c, l, e, r}) == True{} : Bool}:
  L.and_intro(Bool.and(ok(K, V, l), ok(K, V, r)), Nat.is_eq(bh(K, V, l), bh(K, V, r)),
    L.and_intro(ok(K, V, l), ok(K, V, r), a, b),
    L.subst(Nat, x => {Nat.is_eq(bh(K, V, l), x) == True{} : Bool}, bh(K, V, l), bh(K, V, r), eh, N.is_eq_refl(bh(K, V, l))))

# ok implies okt
def ok_okt(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {ok(K, V, t) == True{} : Bool}) -> {okt(K, V, t) == True{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      okt_mk(K, V, c, l, e, r, ok_l(K, V, c, l, e, r, h), ok_r(K, V, c, l, e, r, h), ok_h(K, V, c, l, e, r, h))

# a black root means `okt` already is `ok`
def okt_ok_b(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {okt(K, V, B.Node{B.B{}, l, e, r}) == True{} : Bool}) -> {ok(K, V, B.Node{B.B{}, l, e, r}) == True{} : Bool}:
  ok_mk(K, V, B.B{}, l, e, r, okt_l(K, V, B.B{}, l, e, r, h), okt_r(K, V, B.B{}, l, e, r, h), okt_h(K, V, B.B{}, l, e, r, h), {==})

def nrr_r(-K: Data, -V: Data, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +h: {nrr_c(K, V, B.R{}, l, r) == True{} : Bool}) -> {B.is_red(K, V, l) == False{} : Bool}:
  L.not_true(B.is_red(K, V, l), L.and_left(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), h))

def nrr_r2(-K: Data, -V: Data, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +h: {nrr_c(K, V, B.R{}, l, r) == True{} : Bool}) -> {B.is_red(K, V, r) == False{} : Bool}:
  L.not_true(B.is_red(K, V, r), L.and_right(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), h))

# ---- small equality shorthands ----

def nt(+a: Nat, +b: Nat, +c: Nat, +ab: {a == b : Nat}, +bc: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, ab, bc)

def ns(+a: Nat, +b: Nat, +ab: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, ab)

# a black node: the colour condition is vacuous
def mkB(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +a: {ok(K, V, l) == True{} : Bool}, +b: {ok(K, V, r) == True{} : Bool}, +eh: {bh(K, V, l) == bh(K, V, r) : Nat}) -> {ok(K, V, B.Node{B.B{}, l, e, r}) == True{} : Bool}:
  ok_mk(K, V, B.B{}, l, e, r, a, b, eh, {==})

# a red node whose two children are known not to be red
def mkR(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +a: {ok(K, V, l) == True{} : Bool}, +b: {ok(K, V, r) == True{} : Bool}, +eh: {bh(K, V, l) == bh(K, V, r) : Nat}, +hl: {B.is_red(K, V, l) == False{} : Bool}, +hr: {B.is_red(K, V, r) == False{} : Bool}) -> {ok(K, V, B.Node{B.R{}, l, e, r}) == True{} : Bool}:
  ok_mk(K, V, B.R{}, l, e, r, a, b, eh,
    L.and_intro(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), L.not_false(B.is_red(K, V, l), hl), L.not_false(B.is_red(K, V, r), hr)))

# ---- black height of the insertion balance helpers: always 1 + bh(left) ----

def brc1_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cd: B.Color, +c1t: B.Tree<K, V>, +z: E.Entry<K, V>, +c2t: B.Tree<K, V>) -> {bh(K, V, B.bal_rc1(K, V, l, e, b, y, cd, c1t, z, c2t)) == 1n+bh(K, V, l) : Nat}:
  match cd:
    case B.R{}:
      {==}
    case B.B{}:
      {==}

def brc_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {bh(K, V, B.bal_rc(K, V, l, e, b, y, cc)) == 1n+bh(K, V, l) : Nat}:
  match cc:
    case B.Leaf{}:
      {==}
    case B.Node{+cd, +c1t, +z, +c2t}:
      brc1_bh(K, V, l, e, b, y, cd, c1t, z, c2t)

def brb1_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cb: B.Color, +b1: B.Tree<K, V>, +w: E.Entry<K, V>, +b2: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {bh(K, V, B.bal_rb1(K, V, l, e, cb, b1, w, b2, y, cc)) == 1n+bh(K, V, l) : Nat}:
  match cb:
    case B.R{}:
      {==}
    case B.B{}:
      brc_bh(K, V, l, e, B.Node{B.B{}, b1, w, b2}, y, cc)

def brb_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>) -> {bh(K, V, B.bal_rb(K, V, l, e, b, y, cc)) == 1n+bh(K, V, l) : Nat}:
  match b:
    case B.Leaf{}:
      brc_bh(K, V, l, e, B.Leaf{}, y, cc)
    case B.Node{+cb, +b1, +w, +b2}:
      brb1_bh(K, V, l, e, cb, b1, w, b2, y, cc)

def br1_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cr: B.Color, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>) -> {bh(K, V, B.bal_right1(K, V, l, e, cr, rl, re, rr)) == 1n+bh(K, V, l) : Nat}:
  match cr:
    case B.R{}:
      brb_bh(K, V, l, e, rl, re, rr)
    case B.B{}:
      {==}

def br_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_right(K, V, l, e, r)) == 1n+bh(K, V, l) : Nat}:
  match r:
    case B.Leaf{}:
      {==}
    case B.Node{+cr, +rl, +re, +rr}:
      br1_bh(K, V, l, e, cr, rl, re, rr)

def blb_bh(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_lb(K, V, a, x, b, e, r)) == 1n+bh(K, V, a) : Nat}:
  match b:
    case B.Leaf{}:
      br_bh(K, V, B.Node{B.R{}, a, x, B.Leaf{}}, e, r)
    case B.Node{+cb, +b1, +y, +b2}:
      match cb:
        case B.R{}:
          {==}
        case B.B{}:
          br_bh(K, V, B.Node{B.R{}, a, x, B.Node{B.B{}, b1, y, b2}}, e, r)

def bla_bh(-K: Data, -V: Data, +ca: B.Color, +a1: B.Tree<K, V>, +y: E.Entry<K, V>, +a2: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_la(K, V, ca, a1, y, a2, x, b, e, r)) == 1n+bh(K, V, B.Node{ca, a1, y, a2}) : Nat}:
  match ca:
    case B.R{}:
      {==}
    case B.B{}:
      blb_bh(K, V, B.Node{B.B{}, a1, y, a2}, x, b, e, r)

def bl_bh(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_l(K, V, a, x, b, e, r)) == 1n+bh(K, V, a) : Nat}:
  match a:
    case B.Leaf{}:
      blb_bh(K, V, B.Leaf{}, x, b, e, r)
    case B.Node{+ca, +a1, +y, +a2}:
      bla_bh(K, V, ca, a1, y, a2, x, b, e, r)

def bl1_bh(-K: Data, -V: Data, +cl: B.Color, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_left1(K, V, cl, ll, le, lr, e, r)) == 1n+bh(K, V, B.Node{cl, ll, le, lr}) : Nat}:
  match cl:
    case B.R{}:
      bl_bh(K, V, ll, le, lr, e, r)
    case B.B{}:
      br_bh(K, V, B.Node{B.B{}, ll, le, lr}, e, r)

def bb_bh(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {bh(K, V, B.bal_black(K, V, l, e, r)) == 1n+bh(K, V, l) : Nat}:
  match l:
    case B.Leaf{}:
      br_bh(K, V, B.Leaf{}, e, r)
    case B.Node{+cl, +ll, +le, +lr}:
      bl1_bh(K, V, cl, ll, le, lr, e, r)

# ---- `ok` for the insertion balance helpers ----
#
# The right-hand chain repairs a red-red edge inside the right child. Its
# hypotheses are: the left child is a proper red-black tree, the right child
# is proper except possibly at its own root (okt), and the two black heights
# agree. The result is a proper red-black tree.

def brc1_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cd: B.Color, +c1t: B.Tree<K, V>, +z: E.Entry<K, V>, +c2t: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +okcc: {ok(K, V, B.Node{cd, c1t, z, c2t}) == True{} : Bool}, +hbc: {bh(K, V, b) == bh(K, V, B.Node{cd, c1t, z, c2t}) : Nat}, +hlb: {bh(K, V, l) == bh(K, V, b) : Nat}, +hnb: {B.is_red(K, V, b) == False{} : Bool}) -> {ok(K, V, B.bal_rc1(K, V, l, e, b, y, cd, c1t, z, c2t)) == True{} : Bool}:
  match cd:
    case B.R{}:
      mkR(K, V, B.Node{B.B{}, l, e, b}, y, B.Node{B.B{}, c1t, z, c2t},
        mkB(K, V, l, e, b, okl, okb, hlb),
        mkB(K, V, c1t, z, c2t, ok_l(K, V, B.R{}, c1t, z, c2t, okcc), ok_r(K, V, B.R{}, c1t, z, c2t, okcc), ok_h(K, V, B.R{}, c1t, z, c2t, okcc)),
        N.succ_cong(bh(K, V, l), bh(K, V, c1t), nt(bh(K, V, l), bh(K, V, b), bh(K, V, c1t), hlb, hbc)),
        {==}, {==})
    case B.B{}:
      mkB(K, V, l, e, B.Node{B.R{}, b, y, B.Node{B.B{}, c1t, z, c2t}},
        okl,
        mkR(K, V, b, y, B.Node{B.B{}, c1t, z, c2t}, okb, okcc, hbc, hnb, {==}),
        hlb)

def brc_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +okcc: {ok(K, V, cc) == True{} : Bool}, +hbc: {bh(K, V, b) == bh(K, V, cc) : Nat}, +hlb: {bh(K, V, l) == bh(K, V, b) : Nat}, +hnb: {B.is_red(K, V, b) == False{} : Bool}) -> {ok(K, V, B.bal_rc(K, V, l, e, b, y, cc)) == True{} : Bool}:
  match cc:
    case B.Leaf{}:
      mkB(K, V, l, e, B.Node{B.R{}, b, y, B.Leaf{}}, okl,
        mkR(K, V, b, y, B.Leaf{}, okb, {==}, hbc, hnb, {==}), hlb)
    case B.Node{+cd, +c1t, +z, +c2t}:
      brc1_ok(K, V, l, e, b, y, cd, c1t, z, c2t, okl, okb, okcc, hbc, hlb, hnb)

def brb1_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cb: B.Color, +b1: B.Tree<K, V>, +w: E.Entry<K, V>, +b2: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okb: {ok(K, V, B.Node{cb, b1, w, b2}) == True{} : Bool}, +okcc: {ok(K, V, cc) == True{} : Bool}, +hbc: {bh(K, V, B.Node{cb, b1, w, b2}) == bh(K, V, cc) : Nat}, +hlb: {bh(K, V, l) == bh(K, V, B.Node{cb, b1, w, b2}) : Nat}) -> {ok(K, V, B.bal_rb1(K, V, l, e, cb, b1, w, b2, y, cc)) == True{} : Bool}:
  match cb:
    case B.R{}:
      mkR(K, V, B.Node{B.B{}, l, e, b1}, w, B.Node{B.B{}, b2, y, cc},
        mkB(K, V, l, e, b1, okl, ok_l(K, V, B.R{}, b1, w, b2, okb), hlb),
        mkB(K, V, b2, y, cc, ok_r(K, V, B.R{}, b1, w, b2, okb), okcc,
          nt(bh(K, V, b2), bh(K, V, b1), bh(K, V, cc), ns(bh(K, V, b1), bh(K, V, b2), ok_h(K, V, B.R{}, b1, w, b2, okb)), hbc)),
        N.succ_cong(bh(K, V, l), bh(K, V, b2), nt(bh(K, V, l), bh(K, V, b1), bh(K, V, b2), hlb, ok_h(K, V, B.R{}, b1, w, b2, okb))),
        {==}, {==})
    case B.B{}:
      brc_ok(K, V, l, e, B.Node{B.B{}, b1, w, b2}, y, cc, okl, okb, okcc, hbc, hlb, {==})

def brb_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +b: B.Tree<K, V>, +y: E.Entry<K, V>, +cc: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +okcc: {ok(K, V, cc) == True{} : Bool}, +hbc: {bh(K, V, b) == bh(K, V, cc) : Nat}, +hlb: {bh(K, V, l) == bh(K, V, b) : Nat}) -> {ok(K, V, B.bal_rb(K, V, l, e, b, y, cc)) == True{} : Bool}:
  match b:
    case B.Leaf{}:
      brc_ok(K, V, l, e, B.Leaf{}, y, cc, okl, {==}, okcc, hbc, hlb, {==})
    case B.Node{+cb, +b1, +w, +b2}:
      brb1_ok(K, V, l, e, cb, b1, w, b2, y, cc, okl, okb, okcc, hbc, hlb)

def br1_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +cr: B.Color, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oktr: {okt(K, V, B.Node{cr, rl, re, rr}) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, B.Node{cr, rl, re, rr}) : Nat}) -> {ok(K, V, B.bal_right1(K, V, l, e, cr, rl, re, rr)) == True{} : Bool}:
  match cr:
    case B.R{}:
      brb_ok(K, V, l, e, rl, re, rr, okl,
        okt_l(K, V, B.R{}, rl, re, rr, oktr), okt_r(K, V, B.R{}, rl, re, rr, oktr),
        okt_h(K, V, B.R{}, rl, re, rr, oktr), hlr)
    case B.B{}:
      mkB(K, V, l, e, B.Node{B.B{}, rl, re, rr}, okl, okt_ok_b(K, V, rl, re, rr, oktr), hlr)

def br_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oktr: {okt(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_right(K, V, l, e, r)) == True{} : Bool}:
  match r:
    case B.Leaf{}:
      mkB(K, V, l, e, B.Leaf{}, okl, {==}, hlr)
    case B.Node{+cr, +rl, +re, +rr}:
      br1_ok(K, V, l, e, cr, rl, re, rr, okl, oktr, hlr)

# The left-hand chain repairs a red-red edge inside the left child: the left
# child is proper except possibly at its own root, the right child is proper.

def blb_ok(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oka: {ok(K, V, a) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +hab: {bh(K, V, a) == bh(K, V, b) : Nat}, +okr: {ok(K, V, r) == True{} : Bool}, +har: {bh(K, V, a) == bh(K, V, r) : Nat}, +hna: {B.is_red(K, V, a) == False{} : Bool}) -> {ok(K, V, B.bal_lb(K, V, a, x, b, e, r)) == True{} : Bool}:
  match b:
    case B.Leaf{}:
      br_ok(K, V, B.Node{B.R{}, a, x, B.Leaf{}}, e, r,
        mkR(K, V, a, x, B.Leaf{}, oka, {==}, hab, hna, {==}), ok_okt(K, V, r, okr), har)
    case B.Node{+cb, +b1, +y, +b2}:
      match cb:
        case B.R{}:
          mkR(K, V, B.Node{B.B{}, a, x, b1}, y, B.Node{B.B{}, b2, e, r},
            mkB(K, V, a, x, b1, oka, ok_l(K, V, B.R{}, b1, y, b2, okb), hab),
            mkB(K, V, b2, e, r, ok_r(K, V, B.R{}, b1, y, b2, okb), okr,
              nt(bh(K, V, b2), bh(K, V, a), bh(K, V, r),
                ns(bh(K, V, a), bh(K, V, b2), nt(bh(K, V, a), bh(K, V, b1), bh(K, V, b2), hab, ok_h(K, V, B.R{}, b1, y, b2, okb))), har)),
            N.succ_cong(bh(K, V, a), bh(K, V, b2), nt(bh(K, V, a), bh(K, V, b1), bh(K, V, b2), hab, ok_h(K, V, B.R{}, b1, y, b2, okb))),
            {==}, {==})
        case B.B{}:
          br_ok(K, V, B.Node{B.R{}, a, x, B.Node{B.B{}, b1, y, b2}}, e, r,
            mkR(K, V, a, x, B.Node{B.B{}, b1, y, b2}, oka, okb, hab, hna, {==}), ok_okt(K, V, r, okr), har)

def bla_ok(-K: Data, -V: Data, +ca: B.Color, +a1: B.Tree<K, V>, +y: E.Entry<K, V>, +a2: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oka: {ok(K, V, B.Node{ca, a1, y, a2}) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +hab: {bh(K, V, B.Node{ca, a1, y, a2}) == bh(K, V, b) : Nat}, +okr: {ok(K, V, r) == True{} : Bool}, +har: {bh(K, V, B.Node{ca, a1, y, a2}) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_la(K, V, ca, a1, y, a2, x, b, e, r)) == True{} : Bool}:
  match ca:
    case B.R{}:
      mkR(K, V, B.Node{B.B{}, a1, y, a2}, x, B.Node{B.B{}, b, e, r},
        mkB(K, V, a1, y, a2, ok_l(K, V, B.R{}, a1, y, a2, oka), ok_r(K, V, B.R{}, a1, y, a2, oka), ok_h(K, V, B.R{}, a1, y, a2, oka)),
        mkB(K, V, b, e, r, okb, okr, nt(bh(K, V, b), bh(K, V, a1), bh(K, V, r), ns(bh(K, V, a1), bh(K, V, b), hab), har)),
        N.succ_cong(bh(K, V, a1), bh(K, V, b), hab), {==}, {==})
    case B.B{}:
      blb_ok(K, V, B.Node{B.B{}, a1, y, a2}, x, b, e, r, oka, okb, hab, okr, har, {==})

def bl_ok(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oka: {ok(K, V, a) == True{} : Bool}, +okb: {ok(K, V, b) == True{} : Bool}, +hab: {bh(K, V, a) == bh(K, V, b) : Nat}, +okr: {ok(K, V, r) == True{} : Bool}, +har: {bh(K, V, a) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_l(K, V, a, x, b, e, r)) == True{} : Bool}:
  match a:
    case B.Leaf{}:
      blb_ok(K, V, B.Leaf{}, x, b, e, r, {==}, okb, hab, okr, har, {==})
    case B.Node{+ca, +a1, +y, +a2}:
      bla_ok(K, V, ca, a1, y, a2, x, b, e, r, oka, okb, hab, okr, har)

def bl1_ok(-K: Data, -V: Data, +cl: B.Color, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oktl: {okt(K, V, B.Node{cl, ll, le, lr}) == True{} : Bool}, +okr: {ok(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, B.Node{cl, ll, le, lr}) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_left1(K, V, cl, ll, le, lr, e, r)) == True{} : Bool}:
  match cl:
    case B.R{}:
      bl_ok(K, V, ll, le, lr, e, r, okt_l(K, V, B.R{}, ll, le, lr, oktl), okt_r(K, V, B.R{}, ll, le, lr, oktl), okt_h(K, V, B.R{}, ll, le, lr, oktl), okr, hlr)
    case B.B{}:
      br_ok(K, V, B.Node{B.B{}, ll, le, lr}, e, r, okt_ok_b(K, V, ll, le, lr, oktl), ok_okt(K, V, r, okr), hlr)

# insertion went left: the left child may have a red-red edge at its root
def balB_okl(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oktl: {okt(K, V, l) == True{} : Bool}, +okr: {ok(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_black(K, V, l, e, r)) == True{} : Bool}:
  match l:
    case B.Leaf{}:
      br_ok(K, V, B.Leaf{}, e, r, {==}, ok_okt(K, V, r, okr), hlr)
    case B.Node{+cl, +ll, +le, +lr}:
      bl1_ok(K, V, cl, ll, le, lr, e, r, oktl, okr, hlr)

# insertion went right: the left child is a proper tree, so the left-hand
# rotations of bal_black cannot fire (a red left child has no red child) and
# the chain reaches bal_right with the left child rebuilt unchanged.

def blbr_ok(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okl: {ok(K, V, B.Node{B.R{}, a, x, b}) == True{} : Bool}, +oktr: {okt(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, B.Node{B.R{}, a, x, b}) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_lb(K, V, a, x, b, e, r)) == True{} : Bool}:
  match b:
    case B.Leaf{}:
      br_ok(K, V, B.Node{B.R{}, a, x, B.Leaf{}}, e, r, okl, oktr, hlr)
    case B.Node{+cb, +b1, +y, +b2}:
      match cb:
        case B.R{}:
          Empty.absurd({ok(K, V, B.bal_lr(K, V, a, x, b1, y, b2, e, r)) == True{} : Bool},
            L.true_false(nrr_r2(K, V, a, B.Node{B.R{}, b1, y, b2}, ok_n(K, V, B.R{}, a, x, B.Node{B.R{}, b1, y, b2}, okl))))
        case B.B{}:
          br_ok(K, V, B.Node{B.R{}, a, x, B.Node{B.B{}, b1, y, b2}}, e, r, okl, oktr, hlr)

def blr_ok(-K: Data, -V: Data, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okl: {ok(K, V, B.Node{B.R{}, a, x, b}) == True{} : Bool}, +oktr: {okt(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, B.Node{B.R{}, a, x, b}) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_l(K, V, a, x, b, e, r)) == True{} : Bool}:
  match a:
    case B.Leaf{}:
      blbr_ok(K, V, B.Leaf{}, x, b, e, r, okl, oktr, hlr)
    case B.Node{+ca, +a1, +y, +a2}:
      match ca:
        case B.R{}:
          Empty.absurd({ok(K, V, B.bal_ll(K, V, a1, y, a2, x, b, e, r)) == True{} : Bool},
            L.true_false(nrr_r(K, V, B.Node{B.R{}, a1, y, a2}, b, ok_n(K, V, B.R{}, B.Node{B.R{}, a1, y, a2}, x, b, okl))))
        case B.B{}:
          blbr_ok(K, V, B.Node{B.B{}, a1, y, a2}, x, b, e, r, okl, oktr, hlr)

def balB_okr(-K: Data, -V: Data, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oktr: {okt(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}) -> {ok(K, V, B.bal_black(K, V, l, e, r)) == True{} : Bool}:
  match l:
    case B.Leaf{}:
      br_ok(K, V, B.Leaf{}, e, r, {==}, oktr, hlr)
    case B.Node{+cl, +ll, +le, +lr}:
      match cl:
        case B.R{}:
          blr_ok(K, V, ll, le, lr, e, r, okl, oktr, hlr)
        case B.B{}:
          br_ok(K, V, B.Node{B.B{}, ll, le, lr}, e, r, okl, oktr, hlr)

# ---- insertion preserves the invariant ----

def or_l_false(+x: Bool, +y: Bool, +hx: {x == False{} : Bool}, +h: {Bool.or(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  L.subst(Bool, z => {Bool.or(z, y) == True{} : Bool}, x, False{}, hx, h)

def or_r_true(x: Bool, +y: Bool, +hy: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      hy

# p or not x, and x or y, give p or y
def or_chain(p: Bool, +x: Bool, +y: Bool, +h1: {Bool.or(p, Bool.not(x)) == True{} : Bool}, +h2: {Bool.or(x, y) == True{} : Bool}) -> {Bool.or(p, y) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      or_l_false(x, y, L.not_true(x, h1), h2)

# a red parent has a non-red left (resp. right) child
def nrr_notred_l(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +nn: {nrr_c(K, V, c, l, r) == True{} : Bool}) -> {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, l))) == True{} : Bool}:
  match c:
    case B.R{}:
      L.and_left(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), nn)
    case B.B{}:
      {==}

def nrr_notred_r(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +nn: {nrr_c(K, V, c, l, r) == True{} : Bool}) -> {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, r))) == True{} : Bool}:
  match c:
    case B.R{}:
      L.and_right(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), nn)
    case B.B{}:
      {==}

# What `balance` guarantees about the node it builds.
def BalOK(-K: Data, -V: Data, +c: B.Color, +hl: Nat, +u: B.Tree<K, V>) -> Type:
  {bh(K, V, u) == bh_c(c, hl) : Nat} & ({okt(K, V, u) == True{} : Bool} & {Bool.or(B.red_c(c), ok(K, V, u)) == True{} : Bool})

# balance with a left child that may carry one red-red edge at its root; when
# the node being built is red the left child must already be proper.
def balance_okl(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +oktl: {okt(K, V, l) == True{} : Bool}, +okr: {ok(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}, +hred: {Bool.or(Bool.not(B.red_c(c)), ok(K, V, l)) == True{} : Bool}) -> BalOK(K, V, c, bh(K, V, l), B.balance(K, V, c, l, e, r)):
  match c:
    case B.R{}:
      ({==}, (okt_mk(K, V, B.R{}, l, e, r, or_l_false(Bool.not(B.red_c(B.R{})), ok(K, V, l), {==}, hred), okr, hlr), {==}))
    case B.B{}:
      +okres = balB_okl(K, V, l, e, r, oktl, okr, hlr)
      (bb_bh(K, V, l, e, r), (ok_okt(K, V, B.bal_black(K, V, l, e, r), okres), okres))

def balance_okr(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oktr: {okt(K, V, r) == True{} : Bool}, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}, +hred: {Bool.or(Bool.not(B.red_c(c)), ok(K, V, r)) == True{} : Bool}) -> BalOK(K, V, c, bh(K, V, l), B.balance(K, V, c, l, e, r)):
  match c:
    case B.R{}:
      ({==}, (okt_mk(K, V, B.R{}, l, e, r, okl, or_l_false(Bool.not(B.red_c(B.R{})), ok(K, V, r), {==}, hred), hlr), {==}))
    case B.B{}:
      +okres = balB_okr(K, V, l, e, r, okl, oktr, hlr)
      (bb_bh(K, V, l, e, r), (ok_okt(K, V, B.bal_black(K, V, l, e, r), okres), okres))

# What `ins` guarantees: the black height is unchanged, the result is proper
# except possibly for a red-red edge at its own root, and if the tree it was
# applied to was black then the result is fully proper.
def InsOK(-K: Data, -V: Data, +t: B.Tree<K, V>, +u: B.Tree<K, V>) -> Type:
  {bh(K, V, u) == bh(K, V, t) : Nat} & ({okt(K, V, u) == True{} : Bool} & {Bool.or(B.is_red(K, V, t), ok(K, V, u)) == True{} : Bool})

# the inductive step of ins_ok, with the recursive result as a parameter
def ins_lt_go(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +u: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, p: InsOK(K, V, l, u)) -> InsOK(K, V, B.Node{c, l, e, r}, B.balance(K, V, c, u, e, r)):
  (+hb, rest) = p
  (ho, hr) = rest
  L.subst(Nat, z => BalOK(K, V, c, z, B.balance(K, V, c, u, e, r)), bh(K, V, u), bh(K, V, l), hb,
    balance_okl(K, V, c, u, e, r, ho, ok_r(K, V, c, l, e, r, h),
      nt(bh(K, V, u), bh(K, V, l), bh(K, V, r), hb, ok_h(K, V, c, l, e, r, h)),
      or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, l), ok(K, V, u), nrr_notred_l(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), hr)))

def ins_gt_go(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +u: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, p: InsOK(K, V, r, u)) -> InsOK(K, V, B.Node{c, l, e, r}, B.balance(K, V, c, l, e, u)):
  (hb, rest) = p
  (ho, hr) = rest
  balance_okr(K, V, c, l, e, u, ok_l(K, V, c, l, e, r, h), ho,
    nt(bh(K, V, l), bh(K, V, r), bh(K, V, u), ok_h(K, V, c, l, e, r, h), ns(bh(K, V, u), bh(K, V, r), hb)),
    or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, r), ok(K, V, u), nrr_notred_r(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), hr))

def ins_ok(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, a: Cmp, +h: {ok(K, V, t) == True{} : Bool}) -> InsOK(K, V, t, B.ins(~K, ~cmp, V, t, k, v, a)):
  match t a:
    case B.Leaf{} _:
      ({==}, ({==}, {==}))
    case B.Node{+c, +l, e, +r} LT{}:
      ins_lt_go(K, V, c, l, e, r, B.ins(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l)), h,
        ins_ok(~K, ~cmp, V, l, k, v, B.c1(~K, ~cmp, V, k, l), ok_l(K, V, c, l, e, r, h)))
    case B.Node{+c, +l, e, +r} EQ{}:
      ({==}, (okt_mk(K, V, c, l, E.Entry{k, v}, r, ok_l(K, V, c, l, e, r, h), ok_r(K, V, c, l, e, r, h), ok_h(K, V, c, l, e, r, h)),
              or_r_true(B.red_c(c), ok(K, V, B.Node{c, l, E.Entry{k, v}, r}),
                ok_mk(K, V, c, l, E.Entry{k, v}, r, ok_l(K, V, c, l, e, r, h), ok_r(K, V, c, l, e, r, h), ok_h(K, V, c, l, e, r, h), ok_n(K, V, c, l, e, r, h)))))
    case B.Node{+c, +l, e, +r} GT{}:
      ins_gt_go(K, V, c, l, e, r, B.ins(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r)), h,
        ins_ok(~K, ~cmp, V, r, k, v, B.c1(~K, ~cmp, V, k, r), ok_r(K, V, c, l, e, r, h)))

# blackening the root turns the transient state into the full invariant
def blacken_bal(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {okt(K, V, t) == True{} : Bool}) -> {bal(K, V, B.blacken(K, V, t)) == True{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      L.and_intro(Bool.not(B.is_red(K, V, B.Node{B.B{}, l, e, r})), ok(K, V, B.Node{B.B{}, l, e, r}), {==},
        okt_ok_b(K, V, l, e, r, okt_mk(K, V, B.B{}, l, e, r, okt_l(K, V, c, l, e, r, h), okt_r(K, V, c, l, e, r, h), okt_h(K, V, c, l, e, r, h))))

def insert_bal_go(-K: Data, -V: Data, +t: B.Tree<K, V>, +u: B.Tree<K, V>, p: InsOK(K, V, t, u)) -> {bal(K, V, B.blacken(K, V, u)) == True{} : Bool}:
  (hb, rest) = p
  (ho, hr) = rest
  blacken_bal(K, V, u, ho)

def insert_bal(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +v: V, +h: {bal(K, V, t) == True{} : Bool}) -> {bal(K, V, B.insert_tree(~K, ~cmp, V, t, k, v)) == True{} : Bool}:
  insert_bal_go(K, V, t, B.ins(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t)),
    ins_ok(~K, ~cmp, V, t, k, v, B.c1(~K, ~cmp, V, k, t), L.and_right(Bool.not(B.is_red(K, V, t)), ok(K, V, t), h)))

# ---- deletion: the in-order list is the spec's deletion ----
#
# Every fixup helper rebuilds the same entries in the same order; the proofs
# are append-associativity chains over the two rotation shapes below.

# ((p ++ q:s) ++ t:(u ++ w:z))  ==  p ++ q:((s ++ t:u) ++ w:z)
def rot2_io(-K: Data, -V: Data, +p: List<&2, E.Entry<K, V>>, +q: E.Entry<K, V>, +s: List<&2, E.Entry<K, V>>, +t: E.Entry<K, V>, +u: List<&2, E.Entry<K, V>>, +w: E.Entry<K, V>, +z: List<&2, E.Entry<K, V>>) -> {SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, p, Con{q, s}), Con{t, SC.append(E.Entry<K, V>, u, Con{w, z})}) == SC.append(E.Entry<K, V>, p, Con{q, SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, s, Con{t, u}), Con{w, z})}) : List<&2, E.Entry<K, V>>}:
  -EE = E.Entry<K, V>
  Equal.trans(List<&2, EE>,
    SC.append(EE, SC.append(EE, p, Con{q, s}), Con{t, SC.append(EE, u, Con{w, z})}),
    SC.append(EE, p, Con{q, SC.append(EE, s, Con{t, SC.append(EE, u, Con{w, z})})}),
    SC.append(EE, p, Con{q, SC.append(EE, SC.append(EE, s, Con{t, u}), Con{w, z})}),
    rot_io(K, V, p, q, s, t, SC.append(EE, u, Con{w, z})),
    Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, p, Con{q, ys}),
      SC.append(EE, s, Con{t, SC.append(EE, u, Con{w, z})}),
      SC.append(EE, SC.append(EE, s, Con{t, u}), Con{w, z}),
      Equal.sym(List<&2, EE>, SC.append(EE, SC.append(EE, s, Con{t, u}), Con{w, z}), SC.append(EE, s, Con{t, SC.append(EE, u, Con{w, z})}), rot_io(K, V, s, t, u, w, z))))

# ((p ++ q:s) ++ t:(u ++ w:z))  ==  (p ++ q:(s ++ t:u)) ++ w:z
def rot3_io(-K: Data, -V: Data, +p: List<&2, E.Entry<K, V>>, +q: E.Entry<K, V>, +s: List<&2, E.Entry<K, V>>, +t: E.Entry<K, V>, +u: List<&2, E.Entry<K, V>>, +w: E.Entry<K, V>, +z: List<&2, E.Entry<K, V>>) -> {SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, p, Con{q, s}), Con{t, SC.append(E.Entry<K, V>, u, Con{w, z})}) == SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, p, Con{q, SC.append(E.Entry<K, V>, s, Con{t, u})}), Con{w, z}) : List<&2, E.Entry<K, V>>}:
  -EE = E.Entry<K, V>
  Equal.trans(List<&2, EE>,
    SC.append(EE, SC.append(EE, p, Con{q, s}), Con{t, SC.append(EE, u, Con{w, z})}),
    SC.append(EE, p, Con{q, SC.append(EE, SC.append(EE, s, Con{t, u}), Con{w, z})}),
    SC.append(EE, SC.append(EE, p, Con{q, SC.append(EE, s, Con{t, u})}), Con{w, z}),
    rot2_io(K, V, p, q, s, t, u, w, z),
    Equal.sym(List<&2, EE>,
      SC.append(EE, SC.append(EE, p, Con{q, SC.append(EE, s, Con{t, u})}), Con{w, z}),
      SC.append(EE, p, Con{q, SC.append(EE, SC.append(EE, s, Con{t, u}), Con{w, z})}),
      LL.append_assoc(EE, p, Con{q, SC.append(EE, s, Con{t, u})}, Con{w, z})))

def iod_upd(-K: Data, -V: Data, +u: B.UpD<K, V>) -> {io(K, V, B.upd_tree(K, V, u)) == iod(K, V, u) : List<&2, E.Entry<K, V>>}:
  match u:
    case B.TD{+t}:
      {==}
    case B.UF{+t}:
      {==}

# ---- a deficient LEFT child ----

def fl_b3_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_b3(K, V, sl, se, sr, cpar, l, e)) == nio(K, V, l, e, B.Node{B.B{}, sl, se, sr}) : List<&2, E.Entry<K, V>>}:
  match cpar:
    case B.R{}:
      {==}
    case B.B{}:
      {==}

def fl_b2c_io(-K: Data, -V: Data, +csl: B.Color, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_b2c(K, V, csl, a, x, b, se, sr, cpar, l, e)) == nio(K, V, l, e, B.Node{B.B{}, B.Node{csl, a, x, b}, se, sr}) : List<&2, E.Entry<K, V>>}:
  match csl:
    case B.R{}:
      rot2_io(K, V, io(K, V, l), e, io(K, V, a), x, io(K, V, b), se, io(K, V, sr))
    case B.B{}:
      fl_b3_io(K, V, B.Node{B.B{}, a, x, b}, se, sr, cpar, l, e)

def fl_b2_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_b2(K, V, sl, se, sr, cpar, l, e)) == nio(K, V, l, e, B.Node{B.B{}, sl, se, sr}) : List<&2, E.Entry<K, V>>}:
  match sl:
    case B.Leaf{}:
      fl_b3_io(K, V, B.Leaf{}, se, sr, cpar, l, e)
    case B.Node{+csl, +a, +x, +b}:
      fl_b2c_io(K, V, csl, a, x, b, se, sr, cpar, l, e)

def fl_b1_io(-K: Data, -V: Data, sr_red: Bool, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_b1(K, V, sr_red, sl, se, sr, cpar, l, e)) == nio(K, V, l, e, B.Node{B.B{}, sl, se, sr}) : List<&2, E.Entry<K, V>>}:
  match sr_red:
    case True{}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, SC.append(EE, io(K, V, l), Con{e, io(K, V, sl)}), Con{se, io(K, V, B.blacken(K, V, sr))}),
        SC.append(EE, SC.append(EE, io(K, V, l), Con{e, io(K, V, sl)}), Con{se, io(K, V, sr)}),
        SC.append(EE, io(K, V, l), Con{e, SC.append(EE, io(K, V, sl), Con{se, io(K, V, sr)})}),
        Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, SC.append(EE, io(K, V, l), Con{e, io(K, V, sl)}), Con{se, ys}),
          io(K, V, B.blacken(K, V, sr)), io(K, V, sr), blacken_io(K, V, sr)),
        rot_io(K, V, io(K, V, l), e, io(K, V, sl), se, io(K, V, sr)))
    case False{}:
      fl_b2_io(K, V, sl, se, sr, cpar, l, e)

def fl_black_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_black(K, V, sl, se, sr, cpar, l, e)) == nio(K, V, l, e, B.Node{B.B{}, sl, se, sr}) : List<&2, E.Entry<K, V>>}:
  fl_b1_io(K, V, B.is_red(K, V, sr), sl, se, sr, cpar, l, e)

def fl_red_io(-K: Data, -V: Data, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_red(K, V, rl, re, rr, l, e)) == nio(K, V, l, e, B.Node{B.R{}, rl, re, rr}) : List<&2, E.Entry<K, V>>}:
  match rl:
    case B.Leaf{}:
      rot_io(K, V, io(K, V, l), e, Nil{}, re, io(K, V, rr))
    case B.Node{+crl, +a, +x, +b}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, io(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))), Con{re, io(K, V, rr)}),
        SC.append(EE, SC.append(EE, io(K, V, l), Con{e, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}), Con{re, io(K, V, rr)}),
        SC.append(EE, io(K, V, l), Con{e, SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), Con{re, io(K, V, rr)})}),
        Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, ys, Con{re, io(K, V, rr)}),
          io(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))),
          SC.append(EE, io(K, V, l), Con{e, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}),
          Equal.trans(List<&2, EE>,
            io(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))),
            iod(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e)),
            SC.append(EE, io(K, V, l), Con{e, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}),
            iod_upd(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e)),
            fl_black_io(K, V, a, x, b, B.R{}, l, e))),
        rot_io(K, V, io(K, V, l), e, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), re, io(K, V, rr)))

def fl_c_io(-K: Data, -V: Data, +cr: B.Color, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_c(K, V, cr, rl, re, rr, c, l, e)) == nio(K, V, l, e, B.Node{cr, rl, re, rr}) : List<&2, E.Entry<K, V>>}:
  match cr:
    case B.B{}:
      fl_black_io(K, V, rl, re, rr, c, l, e)
    case B.R{}:
      fl_red_io(K, V, rl, re, rr, l, e)

def fl_u_io(-K: Data, -V: Data, +r: B.Tree<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fl_u(K, V, r, c, l, e)) == nio(K, V, l, e, r) : List<&2, E.Entry<K, V>>}:
  match r:
    case B.Leaf{}:
      {==}
    case B.Node{+cr, +rl, +re, +rr}:
      fl_c_io(K, V, cr, rl, re, rr, c, l, e)

def fix_left_io(-K: Data, -V: Data, +r: B.Tree<K, V>, +c: B.Color, +u: B.UpD<K, V>, +e: E.Entry<K, V>) -> {iod(K, V, B.fix_left(K, V, r, c, u, e)) == SC.append(E.Entry<K, V>, iod(K, V, u), Con{e, io(K, V, r)}) : List<&2, E.Entry<K, V>>}:
  match u:
    case B.TD{+l}:
      {==}
    case B.UF{+l}:
      fl_u_io(K, V, r, c, l, e)

# ---- a deficient RIGHT child (the mirror image) ----

def fr_b3_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_b3(K, V, sl, se, sr, cpar, e, r)) == nio(K, V, B.Node{B.B{}, sl, se, sr}, e, r) : List<&2, E.Entry<K, V>>}:
  match cpar:
    case B.R{}:
      {==}
    case B.B{}:
      {==}

def fr_b2c_io(-K: Data, -V: Data, +csr: B.Color, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_b2c(K, V, csr, a, x, b, sl, se, cpar, e, r)) == nio(K, V, B.Node{B.B{}, sl, se, B.Node{csr, a, x, b}}, e, r) : List<&2, E.Entry<K, V>>}:
  match csr:
    case B.R{}:
      rot3_io(K, V, io(K, V, sl), se, io(K, V, a), x, io(K, V, b), e, io(K, V, r))
    case B.B{}:
      fr_b3_io(K, V, sl, se, B.Node{B.B{}, a, x, b}, cpar, e, r)

def fr_b2_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_b2(K, V, sl, se, sr, cpar, e, r)) == nio(K, V, B.Node{B.B{}, sl, se, sr}, e, r) : List<&2, E.Entry<K, V>>}:
  match sr:
    case B.Leaf{}:
      fr_b3_io(K, V, sl, se, B.Leaf{}, cpar, e, r)
    case B.Node{+csr, +a, +x, +b}:
      fr_b2c_io(K, V, csr, a, x, b, sl, se, cpar, e, r)

def fr_b1_io(-K: Data, -V: Data, sl_red: Bool, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_b1(K, V, sl_red, sl, se, sr, cpar, e, r)) == nio(K, V, B.Node{B.B{}, sl, se, sr}, e, r) : List<&2, E.Entry<K, V>>}:
  match sl_red:
    case True{}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, io(K, V, B.blacken(K, V, sl)), Con{se, SC.append(EE, io(K, V, sr), Con{e, io(K, V, r)})}),
        SC.append(EE, io(K, V, sl), Con{se, SC.append(EE, io(K, V, sr), Con{e, io(K, V, r)})}),
        SC.append(EE, SC.append(EE, io(K, V, sl), Con{se, io(K, V, sr)}), Con{e, io(K, V, r)}),
        Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, ys, Con{se, SC.append(EE, io(K, V, sr), Con{e, io(K, V, r)})}),
          io(K, V, B.blacken(K, V, sl)), io(K, V, sl), blacken_io(K, V, sl)),
        Equal.sym(List<&2, EE>,
          SC.append(EE, SC.append(EE, io(K, V, sl), Con{se, io(K, V, sr)}), Con{e, io(K, V, r)}),
          SC.append(EE, io(K, V, sl), Con{se, SC.append(EE, io(K, V, sr), Con{e, io(K, V, r)})}),
          rot_io(K, V, io(K, V, sl), se, io(K, V, sr), e, io(K, V, r))))
    case False{}:
      fr_b2_io(K, V, sl, se, sr, cpar, e, r)

def fr_black_io(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_black(K, V, sl, se, sr, cpar, e, r)) == nio(K, V, B.Node{B.B{}, sl, se, sr}, e, r) : List<&2, E.Entry<K, V>>}:
  fr_b1_io(K, V, B.is_red(K, V, sl), sl, se, sr, cpar, e, r)

def fr_red_io(-K: Data, -V: Data, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_red(K, V, ll, le, lr, e, r)) == nio(K, V, B.Node{B.R{}, ll, le, lr}, e, r) : List<&2, E.Entry<K, V>>}:
  match lr:
    case B.Leaf{}:
      Equal.sym(List<&2, E.Entry<K, V>>,
        SC.append(E.Entry<K, V>, SC.append(E.Entry<K, V>, io(K, V, ll), Con{le, Nil{}}), Con{e, io(K, V, r)}),
        SC.append(E.Entry<K, V>, io(K, V, ll), Con{le, SC.append(E.Entry<K, V>, Nil{}, Con{e, io(K, V, r)})}),
        rot_io(K, V, io(K, V, ll), le, Nil{}, e, io(K, V, r)))
    case B.Node{+clr, +a, +x, +b}:
      -EE = E.Entry<K, V>
      Equal.trans(List<&2, EE>,
        SC.append(EE, io(K, V, ll), Con{le, io(K, V, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r)))}),
        SC.append(EE, io(K, V, ll), Con{le, SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), Con{e, io(K, V, r)})}),
        SC.append(EE, SC.append(EE, io(K, V, ll), Con{le, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}), Con{e, io(K, V, r)}),
        Equal.cong(List<&2, EE>, List<&2, EE>, ys => SC.append(EE, io(K, V, ll), Con{le, ys}),
          io(K, V, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r))),
          SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), Con{e, io(K, V, r)}),
          Equal.trans(List<&2, EE>,
            io(K, V, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r))),
            iod(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r)),
            SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), Con{e, io(K, V, r)}),
            iod_upd(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r)),
            fr_black_io(K, V, a, x, b, B.R{}, e, r))),
        Equal.sym(List<&2, EE>,
          SC.append(EE, SC.append(EE, io(K, V, ll), Con{le, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}), Con{e, io(K, V, r)}),
          SC.append(EE, io(K, V, ll), Con{le, SC.append(EE, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)}), Con{e, io(K, V, r)})}),
          LL.append_assoc(EE, io(K, V, ll), Con{le, SC.append(EE, io(K, V, a), Con{x, io(K, V, b)})}, Con{e, io(K, V, r)})))

def fr_c_io(-K: Data, -V: Data, +cl: B.Color, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_c(K, V, cl, ll, le, lr, c, e, r)) == nio(K, V, B.Node{cl, ll, le, lr}, e, r) : List<&2, E.Entry<K, V>>}:
  match cl:
    case B.B{}:
      fr_black_io(K, V, ll, le, lr, c, e, r)
    case B.R{}:
      fr_red_io(K, V, ll, le, lr, e, r)

def fr_u_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.fr_u(K, V, l, c, e, r)) == nio(K, V, l, e, r) : List<&2, E.Entry<K, V>>}:
  match l:
    case B.Leaf{}:
      {==}
    case B.Node{+cl, +ll, +le, +lr}:
      fr_c_io(K, V, cl, ll, le, lr, c, e, r)

def fix_right_io(-K: Data, -V: Data, +l: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, +u: B.UpD<K, V>) -> {iod(K, V, B.fix_right(K, V, l, c, e, u)) == SC.append(E.Entry<K, V>, io(K, V, l), Con{e, iod(K, V, u)}) : List<&2, E.Entry<K, V>>}:
  match u:
    case B.TD{+r}:
      {==}
    case B.UF{+r}:
      fr_u_io(K, V, l, c, e, r)

# ---- removing the node itself ----

def rm_leaf0_io(-K: Data, -V: Data, +c: B.Color) -> {iod(K, V, B.rm_leaf0(K, V, c)) == Nil{} : List<&2, E.Entry<K, V>>}:
  match c:
    case B.R{}:
      {==}
    case B.B{}:
      {==}

def rm_leaf_io(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>) -> {iod(K, V, B.rm_leaf(K, V, c, l)) == io(K, V, l) : List<&2, E.Entry<K, V>>}:
  match l:
    case B.Leaf{}:
      rm_leaf0_io(K, V, c)
    case B.Node{+cl, +a, +x, +b}:
      {==}

def rm_left_leaf_io(-K: Data, -V: Data, +c: B.Color, +r: B.Tree<K, V>) -> {iod(K, V, B.rm_left_leaf(K, V, c, r)) == io(K, V, r) : List<&2, E.Entry<K, V>>}:
  match r:
    case B.Leaf{}:
      rm_leaf0_io(K, V, c)
    case B.Node{+cr, +a, +x, +b}:
      {==}

# the in-order list of a split_min result: the minimum in front of the rest
def ios(-K: Data, -V: Data, s: B.SM<K, V>) -> List<&2, E.Entry<K, V>>:
  match s:
    case B.SMNone{}:
      Nil{}
    case B.SMSome{e, u}:
      Con{e, iod(K, V, u)}

def sm_pick_io(-K: Data, -V: Data, +s: B.SM<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +il: List<&2, E.Entry<K, V>>, +h: {ios(K, V, s) == il : List<&2, E.Entry<K, V>>}) -> {ios(K, V, B.sm_pick(K, V, s, c, e, r)) == SC.append(E.Entry<K, V>, il, Con{e, io(K, V, r)}) : List<&2, E.Entry<K, V>>}:
  match s:
    case B.SMNone{}:
      L.subst(List<&2, E.Entry<K, V>>, z => {Con{e, iod(K, V, B.rm_left_leaf(K, V, c, r))} == SC.append(E.Entry<K, V>, z, Con{e, io(K, V, r)}) : List<&2, E.Entry<K, V>>}, Nil{}, il, h,
        LL.cons_cong(E.Entry<K, V>, e, iod(K, V, B.rm_left_leaf(K, V, c, r)), io(K, V, r), rm_left_leaf_io(K, V, c, r)))
    case B.SMSome{+x, +u}:
      L.subst(List<&2, E.Entry<K, V>>, z => {Con{x, iod(K, V, B.fix_left(K, V, r, c, u, e))} == SC.append(E.Entry<K, V>, z, Con{e, io(K, V, r)}) : List<&2, E.Entry<K, V>>}, Con{x, iod(K, V, u)}, il, h,
        LL.cons_cong(E.Entry<K, V>, x, iod(K, V, B.fix_left(K, V, r, c, u, e)), SC.append(E.Entry<K, V>, iod(K, V, u), Con{e, io(K, V, r)}), fix_left_io(K, V, r, c, u, e)))

def split_min_io(-K: Data, -V: Data, +t: B.Tree<K, V>) -> {ios(K, V, B.split_min(K, V, t)) == io(K, V, t) : List<&2, E.Entry<K, V>>}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      sm_pick_io(K, V, B.split_min(K, V, l), c, e, r, io(K, V, l), split_min_io(K, V, l))

def dh_pick_io(-K: Data, -V: Data, +s: B.SM<K, V>, +c: B.Color, +l: B.Tree<K, V>, +il: List<&2, E.Entry<K, V>>, +h: {ios(K, V, s) == il : List<&2, E.Entry<K, V>>}) -> {iod(K, V, B.dh_pick(K, V, s, c, l)) == SC.append(E.Entry<K, V>, io(K, V, l), il) : List<&2, E.Entry<K, V>>}:
  match s:
    case B.SMNone{}:
      L.subst(List<&2, E.Entry<K, V>>, z => {io(K, V, l) == SC.append(E.Entry<K, V>, io(K, V, l), z) : List<&2, E.Entry<K, V>>}, Nil{}, il, h,
        Equal.sym(List<&2, E.Entry<K, V>>, SC.append(E.Entry<K, V>, io(K, V, l), Nil{}), io(K, V, l), LL.append_nil(E.Entry<K, V>, io(K, V, l))))
    case B.SMSome{+x, +u}:
      L.subst(List<&2, E.Entry<K, V>>, z => {iod(K, V, B.fix_right(K, V, l, c, x, u)) == SC.append(E.Entry<K, V>, io(K, V, l), z) : List<&2, E.Entry<K, V>>}, Con{x, iod(K, V, u)}, il, h,
        fix_right_io(K, V, l, c, x, u))

def del_here_io(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>) -> {iod(K, V, B.del_here(K, V, c, l, r)) == SC.append(E.Entry<K, V>, io(K, V, l), io(K, V, r)) : List<&2, E.Entry<K, V>>}:
  match r:
    case B.Leaf{}:
      Equal.trans(List<&2, E.Entry<K, V>>, iod(K, V, B.rm_leaf(K, V, c, l)), io(K, V, l), SC.append(E.Entry<K, V>, io(K, V, l), Nil{}),
        rm_leaf_io(K, V, c, l),
        Equal.sym(List<&2, E.Entry<K, V>>, SC.append(E.Entry<K, V>, io(K, V, l), Nil{}), io(K, V, l), LL.append_nil(E.Entry<K, V>, io(K, V, l))))
    case B.Node{+cr, +rl, +re, +rr}:
      dh_pick_io(K, V, B.split_min(K, V, B.Node{cr, rl, re, rr}), c, l, io(K, V, B.Node{cr, rl, re, rr}), split_min_io(K, V, B.Node{cr, rl, re, rr}))

# ---- `del` refines the spec's deletion ----

def del_io(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, a: Cmp, +ea: {B.c1(~K, ~cmp, V, k, t) == a : Cmp}, +s: {SO.sorted(~K, ~cmp, V, io(K, V, t)) == True{} : Bool}) -> {iod(K, V, B.del(~K, ~cmp, V, t, k, a)) == S.del(~K, ~cmp, V, k, io(K, V, t)) : List<&2, E.Entry<K, V>>}:
  match t a:
    case B.Leaf{} _:
      {==}
    case B.Node{+c, +l, +e, +r} LT{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +u = B.del(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l))
      +ab = SO.above_gt(~K, ~cmp, ~o, V, io(K, V, r), E.key(K, V, e), k, s2_ab(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ea)
      Equal.trans(LE, iod(K, V, B.fix_left(K, V, r, c, u, e)), SC.append(EE, iod(K, V, u), Con{e, io(K, V, r)}), S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
        fix_left_io(K, V, r, c, u, e),
        Equal.trans(LE, SC.append(EE, iod(K, V, u), Con{e, io(K, V, r)}), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), Con{e, io(K, V, r)}), S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
          Equal.cong(LE, LE, xs => SC.append(EE, xs, Con{e, io(K, V, r)}), iod(K, V, u), S.del(~K, ~cmp, V, k, io(K, V, l)),
            del_io(~K, ~cmp, ~o, V, l, k, B.c1(~K, ~cmp, V, k, l), {==}, s2_l(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s))),
          Equal.sym(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), Con{e, io(K, V, r)}),
            Equal.trans(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), Con{e, io(K, V, r)}),
              SP.del_app(~K, ~cmp, V, io(K, V, l), Con{e, io(K, V, r)}, k),
              Equal.cong(LE, LE, ys => SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), ys), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)}), Con{e, io(K, V, r)},
                Equal.trans(LE, S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)}), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}, Con{e, io(K, V, r)},
                  SP.del_lt(~K, ~cmp, V, e, io(K, V, r), k, ea),
                  LL.cons_cong(EE, e, S.del(~K, ~cmp, V, k, io(K, V, r)), io(K, V, r), SP.del_above(~K, ~cmp, V, io(K, V, r), k, ab))))))))
    case B.Node{+c, +l, +e, +r} EQ{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +ef = eq_flip(~K, ~cmp, ~o, k, E.key(K, V, e), ea)
      +bl = SO.below_eq(~K, ~cmp, ~o, V, io(K, V, l), E.key(K, V, e), k, s2_bl(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ef)
      +ab = SO.above_eq(~K, ~cmp, ~o, V, io(K, V, r), E.key(K, V, e), k, s2_ab(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ef)
      Equal.trans(LE, iod(K, V, B.del_here(K, V, c, l, r)), SC.append(EE, io(K, V, l), io(K, V, r)), S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
        del_here_io(K, V, c, l, r),
        Equal.sym(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), io(K, V, r)),
          Equal.trans(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), io(K, V, r)),
            SP.del_app(~K, ~cmp, V, io(K, V, l), Con{e, io(K, V, r)}, k),
            Equal.trans(LE, SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), io(K, V, r)),
              Equal.cong(LE, LE, xs => SC.append(EE, xs, S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), S.del(~K, ~cmp, V, k, io(K, V, l)), io(K, V, l), SP.del_below(~K, ~cmp, ~o, V, io(K, V, l), k, bl)),
              Equal.cong(LE, LE, ys => SC.append(EE, io(K, V, l), ys), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)}), io(K, V, r),
                Equal.trans(LE, S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)}), S.del(~K, ~cmp, V, k, io(K, V, r)), io(K, V, r),
                  SP.del_eq(~K, ~cmp, V, e, io(K, V, r), k, ea),
                  SP.del_above(~K, ~cmp, V, io(K, V, r), k, ab)))))))
    case B.Node{+c, +l, +e, +r} GT{}:
      -EE = E.Entry<K, V>
      -LE = List<&2, E.Entry<K, V>>
      +u = B.del(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r))
      +bl = bl_gt(~K, ~cmp, ~o, V, io(K, V, l), e, k, s2_bl(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s), ea)
      Equal.trans(LE, iod(K, V, B.fix_right(K, V, l, c, e, u)), SC.append(EE, io(K, V, l), Con{e, iod(K, V, u)}), S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
        fix_right_io(K, V, l, c, e, u),
        Equal.trans(LE, SC.append(EE, io(K, V, l), Con{e, iod(K, V, u)}), SC.append(EE, io(K, V, l), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}), S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})),
          Equal.cong(LE, LE, xs => SC.append(EE, io(K, V, l), Con{e, xs}), iod(K, V, u), S.del(~K, ~cmp, V, k, io(K, V, r)),
            del_io(~K, ~cmp, ~o, V, r, k, B.c1(~K, ~cmp, V, k, r), {==}, s2_r(~K, ~cmp, V, io(K, V, l), e, io(K, V, r), s))),
          Equal.sym(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}),
            Equal.trans(LE, S.del(~K, ~cmp, V, k, SC.append(EE, io(K, V, l), Con{e, io(K, V, r)})), SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}),
              SP.del_app(~K, ~cmp, V, io(K, V, l), Con{e, io(K, V, r)}, k),
              Equal.trans(LE, SC.append(EE, S.del(~K, ~cmp, V, k, io(K, V, l)), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), SC.append(EE, io(K, V, l), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}),
                Equal.cong(LE, LE, xs => SC.append(EE, xs, S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)})), S.del(~K, ~cmp, V, k, io(K, V, l)), io(K, V, l), SP.del_below(~K, ~cmp, ~o, V, io(K, V, l), k, bl)),
                Equal.cong(LE, LE, ys => SC.append(EE, io(K, V, l), ys), S.del(~K, ~cmp, V, k, Con{e, io(K, V, r)}), Con{e, S.del(~K, ~cmp, V, k, io(K, V, r))}, SP.del_gt(~K, ~cmp, V, e, io(K, V, r), k, ea)))))))

def remove_io(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), -V: Data, +t: B.Tree<K, V>, +k: K, +s: {SO.sorted(~K, ~cmp, V, io(K, V, t)) == True{} : Bool}) -> {io(K, V, B.remove_tree(~K, ~cmp, V, t, k)) == S.del(~K, ~cmp, V, k, io(K, V, t)) : List<&2, E.Entry<K, V>>}:
  -LE = List<&2, E.Entry<K, V>>
  +u = B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t))
  Equal.trans(LE, io(K, V, B.blacken(K, V, B.upd_tree(K, V, u))), io(K, V, B.upd_tree(K, V, u)), S.del(~K, ~cmp, V, k, io(K, V, t)),
    blacken_io(K, V, B.upd_tree(K, V, u)),
    Equal.trans(LE, io(K, V, B.upd_tree(K, V, u)), iod(K, V, u), S.del(~K, ~cmp, V, k, io(K, V, t)),
      iod_upd(K, V, u),
      del_io(~K, ~cmp, ~o, V, t, k, B.c1(~K, ~cmp, V, k, t), {==}, s)))

# ============ deletion preserves the red-black invariant ==================
#
# `del` returns TD (the subtree still has its black height) or UF (it is one
# black level short). `dbh` is the black height the parent should see, and the
# colour bookkeeping mirrors the insertion side: a result that replaces a
# black subtree is never red, and a fixup under a red parent never propagates
# a deficiency.

def is_td(-K: Data, -V: Data, u: B.UpD<K, V>) -> Bool:
  match u:
    case B.TD{t}:
      True{}
    case B.UF{t}:
      False{}

def dbh(-K: Data, -V: Data, u: B.UpD<K, V>) -> Nat:
  match u:
    case B.TD{+t}:
      bh(K, V, t)
    case B.UF{+t}:
      1n+bh(K, V, t)

def td_bh(-K: Data, -V: Data, +u: B.UpD<K, V>, +h: {is_td(K, V, u) == True{} : Bool}) -> {bh(K, V, B.upd_tree(K, V, u)) == dbh(K, V, u) : Nat}:
  match u:
    case B.TD{+t}:
      {==}
    case B.UF{+t}:
      Empty.absurd({bh(K, V, t) == 1n+bh(K, V, t) : Nat}, L.false_true(h))

def color_black(c: B.Color, +h: {B.red_c(c) == False{} : Bool}) -> {c == B.B{} : B.Color}:
  match c:
    case B.R{}:
      Empty.absurd({B.R{} == B.B{} : B.Color}, L.true_false(h))
    case B.B{}:
      {==}

def color_red(c: B.Color, +h: {B.red_c(c) == True{} : Bool}) -> {c == B.R{} : B.Color}:
  match c:
    case B.R{}:
      {==}
    case B.B{}:
      Empty.absurd({B.B{} == B.R{} : B.Color}, L.false_true(h))

def nrr_mk(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +hl: {B.is_red(K, V, l) == False{} : Bool}, +hr: {B.is_red(K, V, r) == False{} : Bool}) -> {nrr_c(K, V, c, l, r) == True{} : Bool}:
  match c:
    case B.R{}:
      L.and_intro(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)), L.not_false(B.is_red(K, V, l), hl), L.not_false(B.is_red(K, V, r), hr))
    case B.B{}:
      {==}

def or_not_self(c: B.Color) -> {Bool.or(B.red_c(c), Bool.not(B.red_c(c))) == True{} : Bool}:
  match c:
    case B.R{}:
      {==}
    case B.B{}:
      {==}

def blacken_notred(-K: Data, -V: Data, t: B.Tree<K, V>) -> {B.is_red(K, V, B.blacken(K, V, t)) == False{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{c, l, e, r}:
      {==}

def blacken_ok(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {ok(K, V, t) == True{} : Bool}) -> {ok(K, V, B.blacken(K, V, t)) == True{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      mkB(K, V, l, e, r, ok_l(K, V, c, l, e, r, h), ok_r(K, V, c, l, e, r, h), ok_h(K, V, c, l, e, r, h))

def blacken_bh_red(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {B.is_red(K, V, t) == True{} : Bool}) -> {bh(K, V, B.blacken(K, V, t)) == 1n+bh(K, V, t) : Nat}:
  match t:
    case B.Leaf{}:
      Empty.absurd({bh(K, V, B.Leaf{}) == 1n+bh(K, V, B.Leaf{}) : Nat}, L.false_true(h))
    case B.Node{+c, +l, +e, +r}:
      L.subst(B.Color, z => {bh(K, V, B.Node{B.B{}, l, e, r}) == 1n+bh_c(z, bh(K, V, l)) : Nat}, B.R{}, c,
        Equal.sym(B.Color, c, B.R{}, color_red(c, h)), {==})

# What a fixup of a deficient child produces, given the sibling's black height.
def FixOK(-K: Data, -V: Data, +c: B.Color, +hr: Nat, +w: B.UpD<K, V>) -> Type:
  {dbh(K, V, w) == bh_c(c, hr) : Nat} & ({ok(K, V, B.upd_tree(K, V, w)) == True{} : Bool} & ({Bool.or(B.red_c(c), Bool.not(B.is_red(K, V, B.upd_tree(K, V, w)))) == True{} : Bool} & {Bool.or(Bool.not(B.red_c(c)), is_td(K, V, w)) == True{} : Bool}))

# ---- a deficient LEFT child: the sibling is the black Node{B, sl, se, sr} ----

def fl_b3_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hls: {bh(K, V, l) == bh(K, V, sl) : Nat}, +hnsl: {B.is_red(K, V, sl) == False{} : Bool}, +hnsr: {B.is_red(K, V, sr) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fl_b3(K, V, sl, se, sr, cpar, l, e)):
  match cpar:
    case B.R{}:
      (N.succ_cong(bh(K, V, l), bh(K, V, sl), hls),
       (mkB(K, V, l, e, B.Node{B.R{}, sl, se, sr}, okl, mkR(K, V, sl, se, sr, oksl, oksr, hss, hnsl, hnsr), hls), ({==}, {==})))
    case B.B{}:
      (N.succ_cong(1n+bh(K, V, l), 1n+bh(K, V, sl), N.succ_cong(bh(K, V, l), bh(K, V, sl), hls)),
       (mkB(K, V, l, e, B.Node{B.R{}, sl, se, sr}, okl, mkR(K, V, sl, se, sr, oksl, oksr, hss, hnsl, hnsr), hls), ({==}, {==})))

def fl_b2c_ok(-K: Data, -V: Data, csl: B.Color, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oksl: {ok(K, V, B.Node{csl, a, x, b}) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, B.Node{csl, a, x, b}) == bh(K, V, sr) : Nat}, +hls: {bh(K, V, l) == bh(K, V, B.Node{csl, a, x, b}) : Nat}, +hnsr: {B.is_red(K, V, sr) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, B.Node{csl, a, x, b}), B.fl_b2c(K, V, csl, a, x, b, se, sr, cpar, l, e)):
  match csl:
    case B.R{}:
      (Equal.cong(Nat, Nat, z => bh_c(cpar, z), 1n+bh(K, V, l), 1n+bh(K, V, a), N.succ_cong(bh(K, V, l), bh(K, V, a), hls)),
       (ok_mk(K, V, cpar, B.Node{B.B{}, l, e, a}, x, B.Node{B.B{}, b, se, sr},
          mkB(K, V, l, e, a, okl, ok_l(K, V, B.R{}, a, x, b, oksl), hls),
          mkB(K, V, b, se, sr, ok_r(K, V, B.R{}, a, x, b, oksl), oksr,
            nt(bh(K, V, b), bh(K, V, a), bh(K, V, sr), ns(bh(K, V, a), bh(K, V, b), ok_h(K, V, B.R{}, a, x, b, oksl)), hss)),
          N.succ_cong(bh(K, V, l), bh(K, V, b), nt(bh(K, V, l), bh(K, V, a), bh(K, V, b), hls, ok_h(K, V, B.R{}, a, x, b, oksl))),
          nrr_mk(K, V, cpar, B.Node{B.B{}, l, e, a}, B.Node{B.B{}, b, se, sr}, {==}, {==})),
        (or_not_self(cpar), or_r_true(Bool.not(B.red_c(cpar)), True{}, {==}))))
    case B.B{}:
      fl_b3_ok(K, V, B.Node{B.B{}, a, x, b}, se, sr, cpar, l, e, okl, oksl, oksr, hss, hls, {==}, hnsr)

def fl_b2_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hls: {bh(K, V, l) == bh(K, V, sl) : Nat}, +hnsr: {B.is_red(K, V, sr) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fl_b2(K, V, sl, se, sr, cpar, l, e)):
  match sl:
    case B.Leaf{}:
      fl_b3_ok(K, V, B.Leaf{}, se, sr, cpar, l, e, okl, oksl, oksr, hss, hls, {==}, hnsr)
    case B.Node{+csl, +a, +x, +b}:
      fl_b2c_ok(K, V, csl, a, x, b, se, sr, cpar, l, e, okl, oksl, oksr, hss, hls, hnsr)

def fl_b1_ok(-K: Data, -V: Data, sr_red: Bool, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hls: {bh(K, V, l) == bh(K, V, sl) : Nat}, +hr: {B.is_red(K, V, sr) == sr_red : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fl_b1(K, V, sr_red, sl, se, sr, cpar, l, e)):
  match sr_red:
    case True{}:
      (Equal.cong(Nat, Nat, z => bh_c(cpar, z), 1n+bh(K, V, l), 1n+bh(K, V, sl), N.succ_cong(bh(K, V, l), bh(K, V, sl), hls)),
       (ok_mk(K, V, cpar, B.Node{B.B{}, l, e, sl}, se, B.blacken(K, V, sr),
          mkB(K, V, l, e, sl, okl, oksl, hls),
          blacken_ok(K, V, sr, oksr),
          nt(1n+bh(K, V, l), 1n+bh(K, V, sr), bh(K, V, B.blacken(K, V, sr)),
            N.succ_cong(bh(K, V, l), bh(K, V, sr), nt(bh(K, V, l), bh(K, V, sl), bh(K, V, sr), hls, hss)),
            ns(bh(K, V, B.blacken(K, V, sr)), 1n+bh(K, V, sr), blacken_bh_red(K, V, sr, hr))),
          nrr_mk(K, V, cpar, B.Node{B.B{}, l, e, sl}, B.blacken(K, V, sr), {==}, blacken_notred(K, V, sr))),
        (or_not_self(cpar), or_r_true(Bool.not(B.red_c(cpar)), True{}, {==}))))
    case False{}:
      fl_b2_ok(K, V, sl, se, sr, cpar, l, e, okl, oksl, oksr, hss, hls, hr)

def fl_black_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hls: {bh(K, V, l) == bh(K, V, sl) : Nat}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fl_black(K, V, sl, se, sr, cpar, l, e)):
  fl_b1_ok(K, V, B.is_red(K, V, sr), sl, se, sr, cpar, l, e, okl, oksl, oksr, hss, hls, {==})

def or_r_false(x: Bool, +h: {Bool.or(x, False{}) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))

def nrr_or(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +r: B.Tree<K, V>, +h1: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, l))) == True{} : Bool}, +h2: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, r))) == True{} : Bool}) -> {nrr_c(K, V, c, l, r) == True{} : Bool}:
  match c:
    case B.R{}:
      L.and_intro(Bool.not(B.is_red(K, V, l)), Bool.not(B.is_red(K, V, r)),
        or_l_false(Bool.not(B.red_c(B.R{})), Bool.not(B.is_red(K, V, l)), {==}, h1),
        or_l_false(Bool.not(B.red_c(B.R{})), Bool.not(B.is_red(K, V, r)), {==}, h2))
    case B.B{}:
      {==}

def bhB(-K: Data, -V: Data, +c: B.Color, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +cb: {c == B.B{} : B.Color}) -> {1n+bh(K, V, a) == bh(K, V, B.Node{c, a, x, b}) : Nat}:
  L.subst(B.Color, z => {1n+bh(K, V, a) == bh_c(z, bh(K, V, a)) : Nat}, B.B{}, c, Equal.sym(B.Color, c, B.B{}, cb), {==})

def fixok_ok(-K: Data, -V: Data, +c: B.Color, +hh: Nat, +w: B.UpD<K, V>, p: FixOK(K, V, c, hh, w)) -> {ok(K, V, B.upd_tree(K, V, w)) == True{} : Bool}:
  (h1, rest) = p
  (h2, rest2) = rest
  (h3, h4) = rest2
  h2

# under a red parent the fixup never propagates a deficiency
def fixok_rbh(-K: Data, -V: Data, +hh: Nat, +w: B.UpD<K, V>, p: FixOK(K, V, B.R{}, hh, w)) -> {bh(K, V, B.upd_tree(K, V, w)) == hh : Nat}:
  (h1, rest) = p
  (h2, rest2) = rest
  (h3, h4) = rest2
  nt(bh(K, V, B.upd_tree(K, V, w)), dbh(K, V, w), hh,
    td_bh(K, V, w, or_l_false(Bool.not(B.red_c(B.R{})), is_td(K, V, w), {==}, h4)), h1)

# The right sibling is red: rotate left and fix under the now-red parent.
def fl_red_ok(-K: Data, -V: Data, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okr: {ok(K, V, B.Node{B.R{}, rl, re, rr}) == True{} : Bool}, +hb: {1n+bh(K, V, l) == bh(K, V, B.Node{B.R{}, rl, re, rr}) : Nat}) -> FixOK(K, V, B.B{}, bh(K, V, B.Node{B.R{}, rl, re, rr}), B.fl_red(K, V, rl, re, rr, l, e)):
  match rl:
    case B.Leaf{}:
      Empty.absurd(FixOK(K, V, B.B{}, bh(K, V, B.Node{B.R{}, B.Leaf{}, re, rr}), B.fl_red(K, V, B.Leaf{}, re, rr, l, e)), N.succ_zero(bh(K, V, l), hb))
    case B.Node{+crl, +a, +x, +b}:
      +cb = color_black(crl, nrr_r(K, V, B.Node{crl, a, x, b}, rr, ok_n(K, V, B.R{}, B.Node{crl, a, x, b}, re, rr, okr)))
      +okrl = ok_l(K, V, B.R{}, B.Node{crl, a, x, b}, re, rr, okr)
      +hls = N.succ_inj(bh(K, V, l), bh(K, V, a),
        L.subst(B.Color, z => {1n+bh(K, V, l) == bh_c(z, bh(K, V, a)) : Nat}, crl, B.B{}, cb, hb))
      (N.succ_cong(bh(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))), bh(K, V, B.Node{crl, a, x, b}),
         nt(bh(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))), 1n+bh(K, V, a), bh(K, V, B.Node{crl, a, x, b}),
           fixok_rbh(K, V, 1n+bh(K, V, a), B.fl_black(K, V, a, x, b, B.R{}, l, e),
             fl_black_ok(K, V, a, x, b, B.R{}, l, e, okl, ok_l(K, V, crl, a, x, b, okrl), ok_r(K, V, crl, a, x, b, okrl), ok_h(K, V, crl, a, x, b, okrl), hls)),
           bhB(K, V, crl, a, x, b, cb))),
       (mkB(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e)), re, rr,
          fixok_ok(K, V, B.R{}, 1n+bh(K, V, a), B.fl_black(K, V, a, x, b, B.R{}, l, e),
            fl_black_ok(K, V, a, x, b, B.R{}, l, e, okl, ok_l(K, V, crl, a, x, b, okrl), ok_r(K, V, crl, a, x, b, okrl), ok_h(K, V, crl, a, x, b, okrl), hls)),
          ok_r(K, V, B.R{}, B.Node{crl, a, x, b}, re, rr, okr),
          nt(bh(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))), bh(K, V, B.Node{crl, a, x, b}), bh(K, V, rr),
            nt(bh(K, V, B.upd_tree(K, V, B.fl_black(K, V, a, x, b, B.R{}, l, e))), 1n+bh(K, V, a), bh(K, V, B.Node{crl, a, x, b}),
              fixok_rbh(K, V, 1n+bh(K, V, a), B.fl_black(K, V, a, x, b, B.R{}, l, e),
                fl_black_ok(K, V, a, x, b, B.R{}, l, e, okl, ok_l(K, V, crl, a, x, b, okrl), ok_r(K, V, crl, a, x, b, okrl), ok_h(K, V, crl, a, x, b, okrl), hls)),
              bhB(K, V, crl, a, x, b, cb)),
            ok_h(K, V, B.R{}, B.Node{crl, a, x, b}, re, rr, okr))),
        ({==}, {==})))

def fl_c_ok(-K: Data, -V: Data, cr: B.Color, +rl: B.Tree<K, V>, +re: E.Entry<K, V>, +rr: B.Tree<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okr: {ok(K, V, B.Node{cr, rl, re, rr}) == True{} : Bool}, +hb: {1n+bh(K, V, l) == bh(K, V, B.Node{cr, rl, re, rr}) : Nat}, +hcr: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, B.Node{cr, rl, re, rr}))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, B.Node{cr, rl, re, rr}), B.fl_c(K, V, cr, rl, re, rr, c, l, e)):
  match cr:
    case B.B{}:
      fl_black_ok(K, V, rl, re, rr, c, l, e, okl, ok_l(K, V, B.B{}, rl, re, rr, okr), ok_r(K, V, B.B{}, rl, re, rr, okr), ok_h(K, V, B.B{}, rl, re, rr, okr), N.succ_inj(bh(K, V, l), bh(K, V, rl), hb))
    case B.R{}:
      L.subst(B.Color, z => FixOK(K, V, z, bh(K, V, B.Node{B.R{}, rl, re, rr}), B.fl_red(K, V, rl, re, rr, l, e)), B.B{}, c,
        Equal.sym(B.Color, c, B.B{}, color_black(c, L.not_true(B.red_c(c), or_r_false(Bool.not(B.red_c(c)), hcr)))),
        fl_red_ok(K, V, rl, re, rr, l, e, okl, okr, hb))

def fl_u_ok(-K: Data, -V: Data, r: B.Tree<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +okr: {ok(K, V, r) == True{} : Bool}, +hb: {1n+bh(K, V, l) == bh(K, V, r) : Nat}, +hcr: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, r))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, r), B.fl_u(K, V, r, c, l, e)):
  match r:
    case B.Leaf{}:
      Empty.absurd(FixOK(K, V, c, bh(K, V, B.Leaf{}), B.fl_u(K, V, B.Leaf{}, c, l, e)), N.succ_zero(bh(K, V, l), hb))
    case B.Node{+cr, +rl, +re, +rr}:
      fl_c_ok(K, V, cr, rl, re, rr, c, l, e, okl, okr, hb, hcr)

def fix_left_ok(-K: Data, -V: Data, +r: B.Tree<K, V>, +c: B.Color, u: B.UpD<K, V>, +e: E.Entry<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +dk: {ok(K, V, B.upd_tree(K, V, u)) == True{} : Bool}, +hb: {dbh(K, V, u) == bh(K, V, r) : Nat}, +hcr: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, r))) == True{} : Bool}, +hcu: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u)))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, r), B.fix_left(K, V, r, c, u, e)):
  match u:
    case B.TD{+t}:
      (Equal.cong(Nat, Nat, z => bh_c(c, z), bh(K, V, t), bh(K, V, r), hb),
       (ok_mk(K, V, c, t, e, r, dk, okr, hb, nrr_or(K, V, c, t, r, hcu, hcr)),
        (or_not_self(c), or_r_true(Bool.not(B.red_c(c)), True{}, {==}))))
    case B.UF{+t}:
      fl_u_ok(K, V, r, c, t, e, dk, okr, hb, hcr)

# ---- a deficient RIGHT child: the sibling is the black Node{B, sl, se, sr} ----

def fr_b3_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hrs: {bh(K, V, r) == bh(K, V, sl) : Nat}, +hnsl: {B.is_red(K, V, sl) == False{} : Bool}, +hnsr: {B.is_red(K, V, sr) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fr_b3(K, V, sl, se, sr, cpar, e, r)):
  match cpar:
    case B.R{}:
      ({==},
       (mkB(K, V, B.Node{B.R{}, sl, se, sr}, e, r, mkR(K, V, sl, se, sr, oksl, oksr, hss, hnsl, hnsr), okr, ns(bh(K, V, r), bh(K, V, sl), hrs)), ({==}, {==})))
    case B.B{}:
      ({==},
       (mkB(K, V, B.Node{B.R{}, sl, se, sr}, e, r, mkR(K, V, sl, se, sr, oksl, oksr, hss, hnsl, hnsr), okr, ns(bh(K, V, r), bh(K, V, sl), hrs)), ({==}, {==})))

def fr_b2c_ok(-K: Data, -V: Data, csr: B.Color, +a: B.Tree<K, V>, +x: E.Entry<K, V>, +b: B.Tree<K, V>, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, B.Node{csr, a, x, b}) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, B.Node{csr, a, x, b}) : Nat}, +hrs: {bh(K, V, r) == bh(K, V, sl) : Nat}, +hnsl: {B.is_red(K, V, sl) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fr_b2c(K, V, csr, a, x, b, sl, se, cpar, e, r)):
  match csr:
    case B.R{}:
      ({==},
       (ok_mk(K, V, cpar, B.Node{B.B{}, sl, se, a}, x, B.Node{B.B{}, b, e, r},
          mkB(K, V, sl, se, a, oksl, ok_l(K, V, B.R{}, a, x, b, oksr), hss),
          mkB(K, V, b, e, r, ok_r(K, V, B.R{}, a, x, b, oksr), okr,
            nt(bh(K, V, b), bh(K, V, sl), bh(K, V, r),
              nt(bh(K, V, b), bh(K, V, a), bh(K, V, sl), ns(bh(K, V, a), bh(K, V, b), ok_h(K, V, B.R{}, a, x, b, oksr)), ns(bh(K, V, sl), bh(K, V, a), hss)),
              ns(bh(K, V, r), bh(K, V, sl), hrs))),
          N.succ_cong(bh(K, V, sl), bh(K, V, b), nt(bh(K, V, sl), bh(K, V, a), bh(K, V, b), hss, ok_h(K, V, B.R{}, a, x, b, oksr))),
          nrr_mk(K, V, cpar, B.Node{B.B{}, sl, se, a}, B.Node{B.B{}, b, e, r}, {==}, {==})),
        (or_not_self(cpar), or_r_true(Bool.not(B.red_c(cpar)), True{}, {==}))))
    case B.B{}:
      fr_b3_ok(K, V, sl, se, B.Node{B.B{}, a, x, b}, cpar, e, r, okr, oksl, oksr, hss, hrs, hnsl, {==})

def fr_b2_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hrs: {bh(K, V, r) == bh(K, V, sl) : Nat}, +hnsl: {B.is_red(K, V, sl) == False{} : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fr_b2(K, V, sl, se, sr, cpar, e, r)):
  match sr:
    case B.Leaf{}:
      fr_b3_ok(K, V, sl, se, B.Leaf{}, cpar, e, r, okr, oksl, oksr, hss, hrs, hnsl, {==})
    case B.Node{+csr, +a, +x, +b}:
      fr_b2c_ok(K, V, csr, a, x, b, sl, se, cpar, e, r, okr, oksl, oksr, hss, hrs, hnsl)

def fr_b1_ok(-K: Data, -V: Data, sl_red: Bool, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hrs: {bh(K, V, r) == bh(K, V, sl) : Nat}, +hl: {B.is_red(K, V, sl) == sl_red : Bool}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fr_b1(K, V, sl_red, sl, se, sr, cpar, e, r)):
  match sl_red:
    case True{}:
      (Equal.cong(Nat, Nat, z => bh_c(cpar, z), bh(K, V, B.blacken(K, V, sl)), 1n+bh(K, V, sl), blacken_bh_red(K, V, sl, hl)),
       (ok_mk(K, V, cpar, B.blacken(K, V, sl), se, B.Node{B.B{}, sr, e, r},
          blacken_ok(K, V, sl, oksl),
          mkB(K, V, sr, e, r, oksr, okr, nt(bh(K, V, sr), bh(K, V, sl), bh(K, V, r), ns(bh(K, V, sl), bh(K, V, sr), hss), ns(bh(K, V, r), bh(K, V, sl), hrs))),
          nt(bh(K, V, B.blacken(K, V, sl)), 1n+bh(K, V, sl), 1n+bh(K, V, sr), blacken_bh_red(K, V, sl, hl), N.succ_cong(bh(K, V, sl), bh(K, V, sr), hss)),
          nrr_mk(K, V, cpar, B.blacken(K, V, sl), B.Node{B.B{}, sr, e, r}, blacken_notred(K, V, sl), {==})),
        (or_not_self(cpar), or_r_true(Bool.not(B.red_c(cpar)), True{}, {==}))))
    case False{}:
      fr_b2_ok(K, V, sl, se, sr, cpar, e, r, okr, oksl, oksr, hss, hrs, hl)

def fr_black_ok(-K: Data, -V: Data, +sl: B.Tree<K, V>, +se: E.Entry<K, V>, +sr: B.Tree<K, V>, +cpar: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +oksl: {ok(K, V, sl) == True{} : Bool}, +oksr: {ok(K, V, sr) == True{} : Bool}, +hss: {bh(K, V, sl) == bh(K, V, sr) : Nat}, +hrs: {bh(K, V, r) == bh(K, V, sl) : Nat}) -> FixOK(K, V, cpar, 1n+bh(K, V, sl), B.fr_black(K, V, sl, se, sr, cpar, e, r)):
  fr_b1_ok(K, V, B.is_red(K, V, sl), sl, se, sr, cpar, e, r, okr, oksl, oksr, hss, hrs, {==})

def fr_red_ok(-K: Data, -V: Data, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +okl: {ok(K, V, B.Node{B.R{}, ll, le, lr}) == True{} : Bool}, +hb: {1n+bh(K, V, r) == bh(K, V, B.Node{B.R{}, ll, le, lr}) : Nat}) -> FixOK(K, V, B.B{}, bh(K, V, B.Node{B.R{}, ll, le, lr}), B.fr_red(K, V, ll, le, lr, e, r)):
  match lr:
    case B.Leaf{}:
      Empty.absurd(FixOK(K, V, B.B{}, bh(K, V, B.Node{B.R{}, ll, le, B.Leaf{}}), B.fr_red(K, V, ll, le, B.Leaf{}, e, r)),
        N.succ_zero(bh(K, V, r), nt(1n+bh(K, V, r), bh(K, V, ll), 0n, hb, ok_h(K, V, B.R{}, ll, le, B.Leaf{}, okl))))
    case B.Node{+clr, +a, +x, +b}:
      +cb = color_black(clr, nrr_r2(K, V, ll, B.Node{clr, a, x, b}, ok_n(K, V, B.R{}, ll, le, B.Node{clr, a, x, b}, okl)))
      +oklr = ok_r(K, V, B.R{}, ll, le, B.Node{clr, a, x, b}, okl)
      +hra = N.succ_inj(bh(K, V, r), bh(K, V, a),
        nt(1n+bh(K, V, r), bh(K, V, B.Node{clr, a, x, b}), 1n+bh(K, V, a),
          nt(1n+bh(K, V, r), bh(K, V, ll), bh(K, V, B.Node{clr, a, x, b}), hb, ok_h(K, V, B.R{}, ll, le, B.Node{clr, a, x, b}, okl)),
          ns(1n+bh(K, V, a), bh(K, V, B.Node{clr, a, x, b}), bhB(K, V, clr, a, x, b, cb))))
      ({==},
       (mkB(K, V, ll, le, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r)),
          ok_l(K, V, B.R{}, ll, le, B.Node{clr, a, x, b}, okl),
          fixok_ok(K, V, B.R{}, 1n+bh(K, V, a), B.fr_black(K, V, a, x, b, B.R{}, e, r),
            fr_black_ok(K, V, a, x, b, B.R{}, e, r, okr, ok_l(K, V, clr, a, x, b, oklr), ok_r(K, V, clr, a, x, b, oklr), ok_h(K, V, clr, a, x, b, oklr), hra)),
          nt(bh(K, V, ll), 1n+bh(K, V, a), bh(K, V, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r))),
            nt(bh(K, V, ll), bh(K, V, B.Node{clr, a, x, b}), 1n+bh(K, V, a),
              ok_h(K, V, B.R{}, ll, le, B.Node{clr, a, x, b}, okl),
              ns(1n+bh(K, V, a), bh(K, V, B.Node{clr, a, x, b}), bhB(K, V, clr, a, x, b, cb))),
            ns(bh(K, V, B.upd_tree(K, V, B.fr_black(K, V, a, x, b, B.R{}, e, r))), 1n+bh(K, V, a),
              fixok_rbh(K, V, 1n+bh(K, V, a), B.fr_black(K, V, a, x, b, B.R{}, e, r),
                fr_black_ok(K, V, a, x, b, B.R{}, e, r, okr, ok_l(K, V, clr, a, x, b, oklr), ok_r(K, V, clr, a, x, b, oklr), ok_h(K, V, clr, a, x, b, oklr), hra))))),
        ({==}, {==})))

def fr_c_ok(-K: Data, -V: Data, cl: B.Color, +ll: B.Tree<K, V>, +le: E.Entry<K, V>, +lr: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +okl: {ok(K, V, B.Node{cl, ll, le, lr}) == True{} : Bool}, +hb: {1n+bh(K, V, r) == bh(K, V, B.Node{cl, ll, le, lr}) : Nat}, +hcl: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, B.Node{cl, ll, le, lr}))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, B.Node{cl, ll, le, lr}), B.fr_c(K, V, cl, ll, le, lr, c, e, r)):
  match cl:
    case B.B{}:
      fr_black_ok(K, V, ll, le, lr, c, e, r, okr, ok_l(K, V, B.B{}, ll, le, lr, okl), ok_r(K, V, B.B{}, ll, le, lr, okl), ok_h(K, V, B.B{}, ll, le, lr, okl), N.succ_inj(bh(K, V, r), bh(K, V, ll), hb))
    case B.R{}:
      L.subst(B.Color, z => FixOK(K, V, z, bh(K, V, B.Node{B.R{}, ll, le, lr}), B.fr_red(K, V, ll, le, lr, e, r)), B.B{}, c,
        Equal.sym(B.Color, c, B.B{}, color_black(c, L.not_true(B.red_c(c), or_r_false(Bool.not(B.red_c(c)), hcl)))),
        fr_red_ok(K, V, ll, le, lr, e, r, okr, okl, hb))

def fr_u_ok(-K: Data, -V: Data, l: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +okr: {ok(K, V, r) == True{} : Bool}, +okl: {ok(K, V, l) == True{} : Bool}, +hb: {1n+bh(K, V, r) == bh(K, V, l) : Nat}, +hcl: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, l))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, l), B.fr_u(K, V, l, c, e, r)):
  match l:
    case B.Leaf{}:
      Empty.absurd(FixOK(K, V, c, bh(K, V, B.Leaf{}), B.fr_u(K, V, B.Leaf{}, c, e, r)), N.succ_zero(bh(K, V, r), hb))
    case B.Node{+cl, +ll, +le, +lr}:
      fr_c_ok(K, V, cl, ll, le, lr, c, e, r, okr, okl, hb, hcl)

def fix_right_ok(-K: Data, -V: Data, +l: B.Tree<K, V>, +c: B.Color, +e: E.Entry<K, V>, u: B.UpD<K, V>, +okl: {ok(K, V, l) == True{} : Bool}, +dk: {ok(K, V, B.upd_tree(K, V, u)) == True{} : Bool}, +hb: {dbh(K, V, u) == bh(K, V, l) : Nat}, +hcl: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, l))) == True{} : Bool}, +hcu: {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u)))) == True{} : Bool}) -> FixOK(K, V, c, bh(K, V, l), B.fix_right(K, V, l, c, e, u)):
  match u:
    case B.TD{+t}:
      ({==},
       (ok_mk(K, V, c, l, e, t, okl, dk, ns(bh(K, V, t), bh(K, V, l), hb), nrr_or(K, V, c, l, t, hcl, hcu)),
        (or_not_self(c), or_r_true(Bool.not(B.red_c(c)), True{}, {==}))))
    case B.UF{+t}:
      fr_u_ok(K, V, l, c, e, t, dk, okl, hb, hcl)

# ---- what `del` returns ----

def DelOK(-K: Data, -V: Data, +t: B.Tree<K, V>, +u: B.UpD<K, V>) -> Type:
  {dbh(K, V, u) == bh(K, V, t) : Nat} & ({ok(K, V, B.upd_tree(K, V, u)) == True{} : Bool} & ({Bool.or(B.is_red(K, V, t), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u)))) == True{} : Bool} & {Bool.or(Bool.not(B.is_red(K, V, t)), is_td(K, V, u)) == True{} : Bool}))

def fix_delok_l(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +w: B.UpD<K, V>, +hlr: {bh(K, V, l) == bh(K, V, r) : Nat}, p: FixOK(K, V, c, bh(K, V, r), w)) -> DelOK(K, V, B.Node{c, l, e, r}, w):
  (h1, rest) = p
  (h2, rest2) = rest
  (h3, h4) = rest2
  (nt(dbh(K, V, w), bh_c(c, bh(K, V, r)), bh_c(c, bh(K, V, l)), h1,
     Equal.cong(Nat, Nat, z => bh_c(c, z), bh(K, V, r), bh(K, V, l), ns(bh(K, V, l), bh(K, V, r), hlr))), (h2, (h3, h4)))

def fix_delok_r(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +w: B.UpD<K, V>, p: FixOK(K, V, c, bh(K, V, l), w)) -> DelOK(K, V, B.Node{c, l, e, r}, w):
  (h1, rest) = p
  (h2, rest2) = rest
  (h3, h4) = rest2
  (h1, (h2, (h3, h4)))

def bhc_zero(c: B.Color, +x: Nat, +h: {bh_c(c, x) == 0n : Nat}) -> {c == B.R{} : B.Color}:
  match c:
    case B.R{}:
      {==}
    case B.B{}:
      Empty.absurd({B.B{} == B.R{} : B.Color}, N.succ_zero(x, h))

def rm_leaf0_ok(-K: Data, -V: Data, c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +hl0: {bh(K, V, l) == 0n : Nat}) -> DelOK(K, V, B.Node{c, l, e, r}, B.rm_leaf0(K, V, c)):
  match c:
    case B.R{}:
      (ns(bh(K, V, l), 0n, hl0), ({==}, ({==}, {==})))
    case B.B{}:
      (N.succ_cong(0n, bh(K, V, l), ns(bh(K, V, l), 0n, hl0)), ({==}, ({==}, {==})))

def rm_leaf_ok(-K: Data, -V: Data, +c: B.Color, l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, +hr0: {bh(K, V, r) == 0n : Nat}) -> DelOK(K, V, B.Node{c, l, e, r}, B.rm_leaf(K, V, c, l)):
  match l:
    case B.Leaf{}:
      rm_leaf0_ok(K, V, c, B.Leaf{}, e, r, {==})
    case B.Node{+cl, +a, +x, +b}:
      +hl0 = nt(bh(K, V, B.Node{cl, a, x, b}), bh(K, V, r), 0n, ok_h(K, V, c, B.Node{cl, a, x, b}, e, r, h), hr0)
      +cr = bhc_zero(cl, bh(K, V, a), hl0)
      +cB = color_black(c, L.not_true(B.red_c(c), or_r_false(Bool.not(B.red_c(c)),
        L.subst(B.Color, z => {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.red_c(z))) == True{} : Bool}, cl, B.R{}, cr,
          nrr_notred_l(K, V, c, B.Node{cl, a, x, b}, r, ok_n(K, V, c, B.Node{cl, a, x, b}, e, r, h))))))
      (L.subst(B.Color, z => {1n+bh(K, V, a) == bh_c(c, bh_c(z, bh(K, V, a))) : Nat}, B.R{}, cl, Equal.sym(B.Color, cl, B.R{}, cr),
         L.subst(B.Color, z => {1n+bh(K, V, a) == bh_c(z, bh_c(B.R{}, bh(K, V, a))) : Nat}, B.B{}, c, Equal.sym(B.Color, c, B.B{}, cB), {==})),
       (mkB(K, V, a, x, b,
          ok_l(K, V, cl, a, x, b, ok_l(K, V, c, B.Node{cl, a, x, b}, e, r, h)),
          ok_r(K, V, cl, a, x, b, ok_l(K, V, c, B.Node{cl, a, x, b}, e, r, h)),
          ok_h(K, V, cl, a, x, b, ok_l(K, V, c, B.Node{cl, a, x, b}, e, r, h))),
        (or_r_true(B.red_c(c), True{}, {==}), or_r_true(Bool.not(B.red_c(c)), True{}, {==}))))

def rm_left_leaf_ok(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, +hl0: {bh(K, V, l) == 0n : Nat}) -> DelOK(K, V, B.Node{c, l, e, r}, B.rm_left_leaf(K, V, c, r)):
  match r:
    case B.Leaf{}:
      rm_leaf0_ok(K, V, c, l, e, B.Leaf{}, hl0)
    case B.Node{+cr, +a, +x, +b}:
      +hr0 = nt(bh(K, V, B.Node{cr, a, x, b}), bh(K, V, l), 0n, ns(bh(K, V, l), bh(K, V, B.Node{cr, a, x, b}), ok_h(K, V, c, l, e, B.Node{cr, a, x, b}, h)), hl0)
      +crR = bhc_zero(cr, bh(K, V, a), hr0)
      +ha0 = L.subst(B.Color, z => {bh_c(z, bh(K, V, a)) == 0n : Nat}, cr, B.R{}, crR, hr0)
      +cB = color_black(c, L.not_true(B.red_c(c), or_r_false(Bool.not(B.red_c(c)),
        L.subst(B.Color, z => {Bool.or(Bool.not(B.red_c(c)), Bool.not(B.red_c(z))) == True{} : Bool}, cr, B.R{}, crR,
          nrr_notred_r(K, V, c, l, B.Node{cr, a, x, b}, ok_n(K, V, c, l, e, B.Node{cr, a, x, b}, h))))))
      (L.subst(B.Color, z => {1n+bh(K, V, a) == bh_c(z, bh(K, V, l)) : Nat}, B.B{}, c, Equal.sym(B.Color, c, B.B{}, cB),
         N.succ_cong(bh(K, V, a), bh(K, V, l), nt(bh(K, V, a), 0n, bh(K, V, l), ha0, ns(bh(K, V, l), 0n, hl0)))),
       (mkB(K, V, a, x, b,
          ok_l(K, V, cr, a, x, b, ok_r(K, V, c, l, e, B.Node{cr, a, x, b}, h)),
          ok_r(K, V, cr, a, x, b, ok_r(K, V, c, l, e, B.Node{cr, a, x, b}, h)),
          ok_h(K, V, cr, a, x, b, ok_r(K, V, c, l, e, B.Node{cr, a, x, b}, h))),
        (or_r_true(B.red_c(c), True{}, {==}), or_r_true(Bool.not(B.red_c(c)), True{}, {==}))))

# ---- split_min ----

def sm_up(-K: Data, -V: Data, s: B.SM<K, V>) -> B.UpD<K, V>:
  match s:
    case B.SMNone{}:
      B.TD{B.Leaf{}}
    case B.SMSome{e, u}:
      u

def sm_none(-K: Data, -V: Data, s: B.SM<K, V>) -> Bool:
  match s:
    case B.SMNone{}:
      True{}
    case B.SMSome{e, u}:
      False{}

def sm_pick_some(-K: Data, -V: Data, s: B.SM<K, V>, +c: B.Color, +e: E.Entry<K, V>, +r: B.Tree<K, V>) -> {sm_none(K, V, B.sm_pick(K, V, s, c, e, r)) == False{} : Bool}:
  match s:
    case B.SMNone{}:
      {==}
    case B.SMSome{x, u}:
      {==}

def sm_pick_ok(-K: Data, -V: Data, s: B.SM<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, pl: DelOK(K, V, l, sm_up(K, V, s))) -> DelOK(K, V, B.Node{c, l, e, r}, sm_up(K, V, B.sm_pick(K, V, s, c, e, r))):
  match s:
    case B.SMNone{}:
      (q1, qr) = pl
      (q2, qr2) = qr
      (q3, q4) = qr2
      rm_left_leaf_ok(K, V, c, l, e, r, h, ns(0n, bh(K, V, l), q1))
    case B.SMSome{+x, +u}:
      (q1, qr) = pl
      (q2, qr2) = qr
      (q3, q4) = qr2
      fix_delok_l(K, V, c, l, e, r, B.fix_left(K, V, r, c, u, e), ok_h(K, V, c, l, e, r, h),
        fix_left_ok(K, V, r, c, u, e, ok_r(K, V, c, l, e, r, h), q2,
          nt(dbh(K, V, u), bh(K, V, l), bh(K, V, r), q1, ok_h(K, V, c, l, e, r, h)),
          nrr_notred_r(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)),
          or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, l), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u))),
            nrr_notred_l(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), q3)))

def split_min_ok(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {ok(K, V, t) == True{} : Bool}) -> DelOK(K, V, t, sm_up(K, V, B.split_min(K, V, t))):
  match t:
    case B.Leaf{}:
      ({==}, ({==}, ({==}, {==})))
    case B.Node{+c, +l, +e, +r}:
      sm_pick_ok(K, V, B.split_min(K, V, l), c, l, e, r, h, split_min_ok(K, V, l, ok_l(K, V, c, l, e, r, h)))

def dh_pick_ok(-K: Data, -V: Data, s: B.SM<K, V>, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, ps: DelOK(K, V, r, sm_up(K, V, s)), +hs: {sm_none(K, V, s) == False{} : Bool}) -> DelOK(K, V, B.Node{c, l, e, r}, B.dh_pick(K, V, s, c, l)):
  match s:
    case B.SMNone{}:
      (q1, qr) = ps
      (q2, qr2) = qr
      (q3, q4) = qr2
      Empty.absurd(DelOK(K, V, B.Node{c, l, e, r}, B.TD{l}), L.true_false(hs))
    case B.SMSome{+x, +u}:
      (q1, qr) = ps
      (q2, qr2) = qr
      (q3, q4) = qr2
      fix_delok_r(K, V, c, l, e, r, B.fix_right(K, V, l, c, x, u),
        fix_right_ok(K, V, l, c, x, u, ok_l(K, V, c, l, e, r, h), q2,
          nt(dbh(K, V, u), bh(K, V, r), bh(K, V, l), q1, ns(bh(K, V, l), bh(K, V, r), ok_h(K, V, c, l, e, r, h))),
          nrr_notred_l(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)),
          or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, r), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u))),
            nrr_notred_r(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), q3)))

def del_here_ok(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, r: B.Tree<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}) -> DelOK(K, V, B.Node{c, l, e, r}, B.del_here(K, V, c, l, r)):
  match r:
    case B.Leaf{}:
      rm_leaf_ok(K, V, c, l, e, B.Leaf{}, h, {==})
    case B.Node{+cr, +rl, +re, +rr}:
      dh_pick_ok(K, V, B.split_min(K, V, B.Node{cr, rl, re, rr}), c, l, e, B.Node{cr, rl, re, rr}, h,
        split_min_ok(K, V, B.Node{cr, rl, re, rr}, ok_r(K, V, c, l, e, B.Node{cr, rl, re, rr}, h)),
        sm_pick_some(K, V, B.split_min(K, V, rl), cr, re, rr))

# ---- `del` and `remove_tree` preserve the invariant ----

def del_lt_go(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +u: B.UpD<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, p: DelOK(K, V, l, u)) -> DelOK(K, V, B.Node{c, l, e, r}, B.fix_left(K, V, r, c, u, e)):
  (q1, qr) = p
  (q2, qr2) = qr
  (q3, q4) = qr2
  fix_delok_l(K, V, c, l, e, r, B.fix_left(K, V, r, c, u, e), ok_h(K, V, c, l, e, r, h),
    fix_left_ok(K, V, r, c, u, e, ok_r(K, V, c, l, e, r, h), q2,
      nt(dbh(K, V, u), bh(K, V, l), bh(K, V, r), q1, ok_h(K, V, c, l, e, r, h)),
      nrr_notred_r(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)),
      or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, l), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u))),
        nrr_notred_l(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), q3)))

def del_gt_go(-K: Data, -V: Data, +c: B.Color, +l: B.Tree<K, V>, +e: E.Entry<K, V>, +r: B.Tree<K, V>, +u: B.UpD<K, V>, +h: {ok(K, V, B.Node{c, l, e, r}) == True{} : Bool}, p: DelOK(K, V, r, u)) -> DelOK(K, V, B.Node{c, l, e, r}, B.fix_right(K, V, l, c, e, u)):
  (q1, qr) = p
  (q2, qr2) = qr
  (q3, q4) = qr2
  fix_delok_r(K, V, c, l, e, r, B.fix_right(K, V, l, c, e, u),
    fix_right_ok(K, V, l, c, e, u, ok_l(K, V, c, l, e, r, h), q2,
      nt(dbh(K, V, u), bh(K, V, r), bh(K, V, l), q1, ns(bh(K, V, l), bh(K, V, r), ok_h(K, V, c, l, e, r, h))),
      nrr_notred_l(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)),
      or_chain(Bool.not(B.red_c(c)), B.is_red(K, V, r), Bool.not(B.is_red(K, V, B.upd_tree(K, V, u))),
        nrr_notred_r(K, V, c, l, r, ok_n(K, V, c, l, e, r, h)), q3)))

def del_ok(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, a: Cmp, +h: {ok(K, V, t) == True{} : Bool}) -> DelOK(K, V, t, B.del(~K, ~cmp, V, t, k, a)):
  match t a:
    case B.Leaf{} _:
      ({==}, ({==}, ({==}, {==})))
    case B.Node{+c, +l, +e, +r} LT{}:
      del_lt_go(K, V, c, l, e, r, B.del(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l)), h,
        del_ok(~K, ~cmp, V, l, k, B.c1(~K, ~cmp, V, k, l), ok_l(K, V, c, l, e, r, h)))
    case B.Node{+c, +l, +e, +r} EQ{}:
      del_here_ok(K, V, c, l, e, r, h)
    case B.Node{+c, +l, +e, +r} GT{}:
      del_gt_go(K, V, c, l, e, r, B.del(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r)), h,
        del_ok(~K, ~cmp, V, r, k, B.c1(~K, ~cmp, V, k, r), ok_r(K, V, c, l, e, r, h)))

def remove_bal_go(-K: Data, -V: Data, +t: B.Tree<K, V>, +u: B.UpD<K, V>, p: DelOK(K, V, t, u)) -> {bal(K, V, B.blacken(K, V, B.upd_tree(K, V, u))) == True{} : Bool}:
  (q1, qr) = p
  (q2, qr2) = qr
  (q3, q4) = qr2
  blacken_bal(K, V, B.upd_tree(K, V, u), ok_okt(K, V, B.upd_tree(K, V, u), q2))

def remove_bal(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: B.Tree<K, V>, +k: K, +h: {bal(K, V, t) == True{} : Bool}) -> {bal(K, V, B.remove_tree(~K, ~cmp, V, t, k)) == True{} : Bool}:
  remove_bal_go(K, V, t, B.del(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t)),
    del_ok(~K, ~cmp, V, t, k, B.c1(~K, ~cmp, V, k, t), L.and_right(Bool.not(B.is_red(K, V, t)), ok(K, V, t), h)))

# ---- the empty tree ----

def new_bal(-K: Data, -V: Data) -> {bal(K, V, B.Leaf{}) == True{} : Bool}:
  {==}

# ============ the red-black properties, stated one by one ================
#
# `ok` is a compact recursive predicate; the definitions below restate its
# consequences in the textbook form, so the public laws do not have to be
# read through `ok`.

# no red node has a red child, anywhere in the tree
def nrr_all(-K: Data, -V: Data, t: B.Tree<K, V>) -> Bool:
  match t:
    case B.Leaf{}:
      True{}
    case B.Node{c, +l, e, +r}:
      Bool.and(Bool.and(nrr_all(K, V, l), nrr_all(K, V, r)), nrr_c(K, V, c, l, r))

def ok_nrr(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {ok(K, V, t) == True{} : Bool}) -> {nrr_all(K, V, t) == True{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      L.and_intro(Bool.and(nrr_all(K, V, l), nrr_all(K, V, r)), nrr_c(K, V, c, l, r),
        L.and_intro(nrr_all(K, V, l), nrr_all(K, V, r),
          ok_nrr(K, V, l, ok_l(K, V, c, l, e, r, h)), ok_nrr(K, V, r, ok_r(K, V, c, l, e, r, h))),
        ok_n(K, V, c, l, e, r, h))

# the number of black nodes on each root-to-leaf path, one entry per path
def bump(+c: B.Color, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{bh_c(c, x), bump(c, t)}

def paths(-K: Data, -V: Data, t: B.Tree<K, V>) -> List<&2, Nat>:
  match t:
    case B.Leaf{}:
      Con{0n, Nil{}}
    case B.Node{c, l, e, r}:
      bump(c, SC.append(Nat, paths(K, V, l), paths(K, V, r)))

def all_eq(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Nat.is_eq(n, x), all_eq(n, t))

def all_eq_app(+n: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +h1: {all_eq(n, xs) == True{} : Bool}, +h2: {all_eq(n, ys) == True{} : Bool}) -> {all_eq(n, SC.append(Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h2
    case Con{+x, +t}:
      L.and_intro(Nat.is_eq(n, x), all_eq(n, SC.append(Nat, t, ys)),
        L.and_left(Nat.is_eq(n, x), all_eq(n, t), h1),
        all_eq_app(n, t, ys, L.and_right(Nat.is_eq(n, x), all_eq(n, t), h1), h2))

def all_eq_bump(+n: Nat, +c: B.Color, xs: List<&2, Nat>, +h: {all_eq(n, xs) == True{} : Bool}) -> {all_eq(bh_c(c, n), bump(c, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.and_intro(Nat.is_eq(bh_c(c, n), bh_c(c, x)), all_eq(bh_c(c, n), bump(c, t)),
        L.subst(Nat, z => {Nat.is_eq(bh_c(c, n), bh_c(c, z)) == True{} : Bool}, n, x,
          N.eq_from_is_eq(n, x, L.and_left(Nat.is_eq(n, x), all_eq(n, t), h)), N.is_eq_refl(bh_c(c, n))),
        all_eq_bump(n, c, t, L.and_right(Nat.is_eq(n, x), all_eq(n, t), h)))

# every root-to-leaf path carries exactly `bh t` black nodes
def ok_paths(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {ok(K, V, t) == True{} : Bool}) -> {all_eq(bh(K, V, t), paths(K, V, t)) == True{} : Bool}:
  match t:
    case B.Leaf{}:
      {==}
    case B.Node{+c, +l, +e, +r}:
      all_eq_bump(bh(K, V, l), c, SC.append(Nat, paths(K, V, l), paths(K, V, r)),
        all_eq_app(bh(K, V, l), paths(K, V, l), paths(K, V, r),
          ok_paths(K, V, l, ok_l(K, V, c, l, e, r, h)),
          L.subst(Nat, z => {all_eq(z, paths(K, V, r)) == True{} : Bool}, bh(K, V, r), bh(K, V, l),
            ns(bh(K, V, l), bh(K, V, r), ok_h(K, V, c, l, e, r, h)),
            ok_paths(K, V, r, ok_r(K, V, c, l, e, r, h)))))

# the root of a balanced tree is black, and the empty leaves are black
def bal_root_black(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {bal(K, V, t) == True{} : Bool}) -> {B.is_red(K, V, t) == False{} : Bool}:
  L.not_true(B.is_red(K, V, t), L.and_left(Bool.not(B.is_red(K, V, t)), ok(K, V, t), h))

def leaf_black(-K: Data, -V: Data) -> {B.is_red(K, V, B.Leaf{}) == False{} : Bool}:
  {==}

def bal_ok(-K: Data, -V: Data, +t: B.Tree<K, V>, +h: {bal(K, V, t) == True{} : Bool}) -> {ok(K, V, t) == True{} : Bool}:
  L.and_right(Bool.not(B.is_red(K, V, t)), ok(K, V, t), h)
