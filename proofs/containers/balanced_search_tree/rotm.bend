import Base
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./setters.bend as SE

# The mirror's attach and rotations as functions of the node list and the
# root: attach links a child under a parent (or makes it the root), a
# rotation relinks the node, its child, the child's inner subtree and the
# parent. (source: tools/generators/tm_hand/rotm.src)


def rootq(+q: Nat, +root: Nat, +y: Nat) -> Nat:
  match q:
    case 0n:
      y
    case 1n+j:
      root

def attn(-K: Data, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool) -> List<&2, M.Node<K>>:
  match q:
    case 0n:
      nl
    case 1n+j:
      match dir:
        case True{}:
          SE.setl(K, nl, 1n+j, y)
        case False{}:
          SE.setr(K, nl, 1n+j, y)

def attach_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +q: Nat, +y: Nat, +dir: Bool) -> {MI.attach(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, q, y, dir) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, nl, q, y, dir), y, q), pl, tg, fl} : ST.Sh<K, V>}:
  match q dir:
    case 0n True{}:
      SE.set_parent_m(~K, ~V, ~cmp, n, y, lo, hi, free, l, d, nl, pl, tg, fl, y, 0n)
    case 0n False{}:
      SE.set_parent_m(~K, ~V, ~cmp, n, y, lo, hi, free, l, d, nl, pl, tg, fl, y, 0n)
    case 1n+j True{}:
      %Equal.sym(ST.Sh<K, V>, MI.set_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, 1n+j, y), ST.SH{n, root, lo, hi, free, l, d, SE.setl(K, nl, 1n+j, y), pl, tg, fl}, SE.set_left_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, 1n+j, y)) : {MI.set_parent(~K, ~V, ~cmp, _, y, 1n+j) == ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setl(K, nl, 1n+j, y), y, 1n+j), pl, tg, fl} : ST.Sh<K, V>}
      SE.set_parent_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setl(K, nl, 1n+j, y), pl, tg, fl, y, 1n+j)
    case 1n+j False{}:
      %Equal.sym(ST.Sh<K, V>, MI.set_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, 1n+j, y), ST.SH{n, root, lo, hi, free, l, d, SE.setr(K, nl, 1n+j, y), pl, tg, fl}, SE.set_right_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, 1n+j, y)) : {MI.set_parent(~K, ~V, ~cmp, _, y, 1n+j) == ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setr(K, nl, 1n+j, y), y, 1n+j), pl, tg, fl} : ST.Sh<K, V>}
      SE.set_parent_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setr(K, nl, 1n+j, y), pl, tg, fl, y, 1n+j)


# the left rotation's writes: x's right := b, b's parent := x, the parent's
# child (or the root) := y, y's parent := q, y's left := x, x's parent := y
def rotl_nl(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> List<&2, M.Node<K>>:
  SE.setp(K, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y)

def rotl_body(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {MI.set_parent(~K, ~V, ~cmp, MI.set_left(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, MI.set_parent(~K, ~V, ~cmp, MI.set_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x, b), b, x), q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, rotl_nl(K, nl, x, y, b, q, dir), pl, tg, fl} : ST.Sh<K, V>}:
  %Equal.sym(ST.Sh<K, V>, MI.set_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x, b), ST.SH{n, root, lo, hi, free, l, d, SE.setr(K, nl, x, b), pl, tg, fl}, SE.set_right_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, b)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_left(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, MI.set_parent(~K, ~V, ~cmp, _, b, x), q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.set_parent(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, SE.setr(K, nl, x, b), pl, tg, fl}, b, x), ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl, tg, fl}, SE.set_parent_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setr(K, nl, x, b), pl, tg, fl, b, x)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_left(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, _, q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.attach(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl, tg, fl}, q, y, dir), ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl}, attach_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl, tg, fl, q, y, dir)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_left(~K, ~V, ~cmp, _, y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.set_left(~K, ~V, ~cmp, ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl}, y, x), ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, tg, fl}, SE.set_left_m(~K, ~V, ~cmp, n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl, y, x)) : {MI.set_parent(~K, ~V, ~cmp, _, x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  SE.set_parent_m(~K, ~V, ~cmp, n, rootq(q, root, y), lo, hi, free, l, d, SE.setl(K, SE.setp(K, attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, tg, fl, x, y)


# the right rotation: x's left := b, b's parent := x, the parent's child (or
# the root) := y, y's parent := q, y's right := x, x's parent := y
def rotr_nl(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> List<&2, M.Node<K>>:
  SE.setp(K, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y)

def rotr_body(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {MI.set_parent(~K, ~V, ~cmp, MI.set_right(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, MI.set_parent(~K, ~V, ~cmp, MI.set_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x, b), b, x), q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, rotr_nl(K, nl, x, y, b, q, dir), pl, tg, fl} : ST.Sh<K, V>}:
  %Equal.sym(ST.Sh<K, V>, MI.set_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x, b), ST.SH{n, root, lo, hi, free, l, d, SE.setl(K, nl, x, b), pl, tg, fl}, SE.set_left_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, b)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_right(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, MI.set_parent(~K, ~V, ~cmp, _, b, x), q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.set_parent(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, SE.setl(K, nl, x, b), pl, tg, fl}, b, x), ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl, tg, fl}, SE.set_parent_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setl(K, nl, x, b), pl, tg, fl, b, x)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_right(~K, ~V, ~cmp, MI.attach(~K, ~V, ~cmp, _, q, y, dir), y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.attach(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl, tg, fl}, q, y, dir), ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl}, attach_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl, tg, fl, q, y, dir)) : {MI.set_parent(~K, ~V, ~cmp, MI.set_right(~K, ~V, ~cmp, _, y, x), x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  %Equal.sym(ST.Sh<K, V>, MI.set_right(~K, ~V, ~cmp, ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl}, y, x), ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, tg, fl}, SE.set_right_m(~K, ~V, ~cmp, n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl, tg, fl, y, x)) : {MI.set_parent(~K, ~V, ~cmp, _, x, y) == ST.SH{n, rootq(q, root, y), lo, hi, free, l, d, SE.setp(K, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl, tg, fl} : ST.Sh<K, V>}
  SE.set_parent_m(~K, ~V, ~cmp, n, rootq(q, root, y), lo, hi, free, l, d, SE.setr(K, SE.setp(K, attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, tg, fl, x, y)

# the mirror's rotations over nodes read from the list
def rotate_left_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +x: Nat) -> {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, rootq(M.node_parent(~K, ST.nd(K, nl, x)), root, M.node_right(~K, ST.nd(K, nl, x))), lo, hi, free, l, d, rotl_nl(K, nl, x, M.node_right(~K, ST.nd(K, nl, x)), M.node_left(~K, ST.nd(K, nl, M.node_right(~K, ST.nd(K, nl, x)))), M.node_parent(~K, ST.nd(K, nl, x)), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, M.node_parent(~K, ST.nd(K, nl, x)))), x)), pl, tg, fl} : ST.Sh<K, V>}:
  rotl_body(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, M.node_right(~K, ST.nd(K, nl, x)), M.node_left(~K, ST.nd(K, nl, M.node_right(~K, ST.nd(K, nl, x)))), M.node_parent(~K, ST.nd(K, nl, x)), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, M.node_parent(~K, ST.nd(K, nl, x)))), x))

def rotate_right_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +x: Nat) -> {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, rootq(M.node_parent(~K, ST.nd(K, nl, x)), root, M.node_left(~K, ST.nd(K, nl, x))), lo, hi, free, l, d, rotr_nl(K, nl, x, M.node_left(~K, ST.nd(K, nl, x)), M.node_right(~K, ST.nd(K, nl, M.node_left(~K, ST.nd(K, nl, x)))), M.node_parent(~K, ST.nd(K, nl, x)), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, M.node_parent(~K, ST.nd(K, nl, x)))), x)), pl, tg, fl} : ST.Sh<K, V>}:
  rotr_body(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x, M.node_left(~K, ST.nd(K, nl, x)), M.node_right(~K, ST.nd(K, nl, M.node_left(~K, ST.nd(K, nl, x)))), M.node_parent(~K, ST.nd(K, nl, x)), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, M.node_parent(~K, ST.nd(K, nl, x)))), x))
