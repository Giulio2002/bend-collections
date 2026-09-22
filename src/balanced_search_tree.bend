import Base
import ../types/balanced_search_tree.bend as E

# Ordered map with a comparator ~cmp (a total order, see proofs/lib/order),
# implemented as a RED-BLACK BINARY search tree: every node has exactly two
# children and a colour, the root and the empty leaves are black, no red node
# has a red child, and every root-to-leaf path contains the same number of
# black nodes. The height is therefore at most 2*log2(n + 1).
#
# Insertion is Okasaki's: the new node is red, and `balance` repairs the one
# red-red edge a recursive insertion can create by rotating/recolouring the
# four classic cases; the root is blackened afterwards. Deletion is the
# conventional CLRS fixup in functional form: `del` returns TD (the black
# height is unchanged) or UF (the subtree lost one black level), and
# fix_left / fix_right repair a UF child by borrowing from or recolouring the
# sibling (red sibling -> rotate; black sibling with a red child -> rotate and
# recolour; black sibling with two black children -> recolour the sibling red
# and propagate). A deleted internal node is replaced by the minimum of its
# right subtree (split_min).
#
# The comparison of the searched key with a node's key is computed by the
# caller and passed down (`a`), so every recursive call is on a subtree.
#
# Errors never change the state: remove/lookup of a missing key give
# KeyNotFound; min/max of an empty map give EmptyTree; lower_bound with no
# key >= k gives KeyNotFound.
#
# Cost (n entries, comparisons): insert/remove/lookup/contains/lower_bound/
# min/max O(log n); range O(log n + m) for m results; to_list O(n);
# length O(1). The tree is persistent: an update rebuilds the O(log n) nodes
# on the path and shares everything else.
#
# Checked instances: keys U32 (U32.cmp) and String (String.order); values
# are an erased type parameter.

type Color is Data:
  R{}
  B{}

type Tree<-K: Data, -V: Data> is Data:
  Leaf{}
  Node{color: Color, l: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>}

# Result of deleting inside a subtree: same black height, or one less.
type UpD<-K: Data, -V: Data> is Data:
  TD{t: Tree<K, V>}
  UF{t: Tree<K, V>}

# The minimum entry of a subtree and what is left of it.
type SM<-K: Data, -V: Data> is Data:
  SMNone{}
  SMSome{e: E.Entry<K, V>, rest: UpD<K, V>}

type OrdMap<-K: Data, -V: Data> is Data:
  BST{size: Nat, root: Tree<K, V>}

# cmp(k, the key at the root of t); EQ on a leaf (the leaf case ignores it).
def c1(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, t: Tree<K, V>) -> Cmp:
  match t:
    case Leaf{}:
      EQ{}
    case Node{c, l, e, r}:
      cmp(k, E.key(K, V, e))

# cmp(the key at the root of t, k).
def d1(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +k: K, t: Tree<K, V>) -> Cmp:
  match t:
    case Leaf{}:
      EQ{}
    case Node{c, l, e, r}:
      cmp(E.key(K, V, e), k)

def red_c(c: Color) -> Bool:
  match c:
    case R{}:
      True{}
    case B{}:
      False{}

def is_red(-K: Data, -V: Data, t: Tree<K, V>) -> Bool:
  match t:
    case Leaf{}:
      False{}
    case Node{c, l, e, r}:
      red_c(c)

def blacken(-K: Data, -V: Data, t: Tree<K, V>) -> Tree<K, V>:
  match t:
    case Leaf{}:
      Leaf{}
    case Node{c, l, e, r}:
      Node{B{}, l, e, r}

def upd_tree(-K: Data, -V: Data, u: UpD<K, V>) -> Tree<K, V>:
  match u:
    case TD{t}:
      t
    case UF{t}:
      t

# ---- insertion: Okasaki's balance ----
#
# balance(c, l, e, r) builds a node of colour c, repairing the single red-red
# edge that a recursive insertion may have created in l or r. The repair only
# applies below a black node; a red node is rebuilt unchanged and its parent
# deals with the red-red edge.

# l = Node{R, Node{R, a, x, b}, y, cc}: rotate right.
def bal_ll(-K: Data, -V: Data, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  Node{R{}, Node{B{}, a, x, b}, y, Node{B{}, cc, e, r}}

# l = Node{R, a, x, Node{R, b, y, cc}}: rotate left then right.
def bal_lr(-K: Data, -V: Data, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  Node{R{}, Node{B{}, a, x, b}, y, Node{B{}, cc, e, r}}

# r = Node{R, Node{R, b, y, cc}, z, d}: rotate right then left.
def bal_rl(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>, z: E.Entry<K, V>, d: Tree<K, V>) -> Tree<K, V>:
  Node{R{}, Node{B{}, l, e, b}, y, Node{B{}, cc, z, d}}

# r = Node{R, b, y, Node{R, cc, z, d}}: rotate left.
def bal_rr(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>, z: E.Entry<K, V>, d: Tree<K, V>) -> Tree<K, V>:
  Node{R{}, Node{B{}, l, e, b}, y, Node{B{}, cc, z, d}}

# no repair applies: a plain black node
def bal_none(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  Node{B{}, l, e, r}

# ---- the right child of the black node being built ----

# cc (the right child of the red right child) is red -> rotate left
def bal_rc1(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cd: Color, c1t: Tree<K, V>, z: E.Entry<K, V>, c2t: Tree<K, V>) -> Tree<K, V>:
  match cd:
    case R{}:
      bal_rr(K, V, l, e, b, y, c1t, z, c2t)
    case B{}:
      bal_none(K, V, l, e, Node{R{}, b, y, Node{B{}, c1t, z, c2t}})

def bal_rc(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>) -> Tree<K, V>:
  match cc:
    case Leaf{}:
      bal_none(K, V, l, e, Node{R{}, b, y, Leaf{}})
    case Node{cd, c1t, z, c2t}:
      bal_rc1(K, V, l, e, b, y, cd, c1t, z, c2t)

# b (the left child of the red right child) is red -> rotate right then left
def bal_rb1(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, cb: Color, b1: Tree<K, V>, w: E.Entry<K, V>, b2: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>) -> Tree<K, V>:
  match cb:
    case R{}:
      bal_rl(K, V, l, e, b1, w, b2, y, cc)
    case B{}:
      bal_rc(K, V, l, e, Node{B{}, b1, w, b2}, y, cc)

def bal_rb(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, b: Tree<K, V>, y: E.Entry<K, V>, cc: Tree<K, V>) -> Tree<K, V>:
  match b:
    case Leaf{}:
      bal_rc(K, V, l, e, Leaf{}, y, cc)
    case Node{cb, b1, w, b2}:
      bal_rb1(K, V, l, e, cb, b1, w, b2, y, cc)

def bal_right1(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, cr: Color, rl: Tree<K, V>, re: E.Entry<K, V>, rr: Tree<K, V>) -> Tree<K, V>:
  match cr:
    case R{}:
      bal_rb(K, V, l, e, rl, re, rr)
    case B{}:
      bal_none(K, V, l, e, Node{B{}, rl, re, rr})

def bal_right(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match r:
    case Leaf{}:
      bal_none(K, V, l, e, Leaf{})
    case Node{cr, rl, re, rr}:
      bal_right1(K, V, l, e, cr, rl, re, rr)

# ---- the left child of the black node being built ----

def bal_lb1(-K: Data, -V: Data, a: Tree<K, V>, x: E.Entry<K, V>, cb: Color, b1: Tree<K, V>, y: E.Entry<K, V>, b2: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match cb:
    case R{}:
      bal_lr(K, V, a, x, b1, y, b2, e, r)
    case B{}:
      bal_right(K, V, Node{R{}, a, x, Node{B{}, b1, y, b2}}, e, r)

def bal_lb(-K: Data, -V: Data, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match b:
    case Leaf{}:
      bal_right(K, V, Node{R{}, a, x, Leaf{}}, e, r)
    case Node{cb, b1, y, b2}:
      bal_lb1(K, V, a, x, cb, b1, y, b2, e, r)

def bal_la(-K: Data, -V: Data, ca: Color, a1: Tree<K, V>, y: E.Entry<K, V>, a2: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match ca:
    case R{}:
      bal_ll(K, V, a1, y, a2, x, b, e, r)
    case B{}:
      bal_lb(K, V, Node{B{}, a1, y, a2}, x, b, e, r)

def bal_l(-K: Data, -V: Data, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match a:
    case Leaf{}:
      bal_lb(K, V, Leaf{}, x, b, e, r)
    case Node{ca, a1, y, a2}:
      bal_la(K, V, ca, a1, y, a2, x, b, e, r)

def bal_left1(-K: Data, -V: Data, cl: Color, ll: Tree<K, V>, le: E.Entry<K, V>, lr: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match cl:
    case R{}:
      bal_l(K, V, ll, le, lr, e, r)
    case B{}:
      bal_right(K, V, Node{B{}, ll, le, lr}, e, r)

def bal_black(-K: Data, -V: Data, l: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match l:
    case Leaf{}:
      bal_right(K, V, Leaf{}, e, r)
    case Node{cl, ll, le, lr}:
      bal_left1(K, V, cl, ll, le, lr, e, r)

# Build a node of colour c, repairing a red-red edge just below a black node.
def balance(-K: Data, -V: Data, c: Color, l: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> Tree<K, V>:
  match c:
    case R{}:
      Node{R{}, l, e, r}
    case B{}:
      bal_black(K, V, l, e, r)

# a = cmp(k, key at the root of t)
def ins(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, +v: V, a: Cmp) -> Tree<K, V>:
  match t a:
    case Leaf{} _:
      Node{R{}, Leaf{}, E.Entry{k, v}, Leaf{}}
    case Node{c, +l, e, r} LT{}:
      balance(K, V, c, ins(~K, ~cmp, V, l, k, v, c1(~K, ~cmp, V, k, l)), e, r)
    case Node{c, l, e, r} EQ{}:
      Node{c, l, E.Entry{k, v}, r}
    case Node{c, l, e, +r} GT{}:
      balance(K, V, c, l, e, ins(~K, ~cmp, V, r, k, v, c1(~K, ~cmp, V, k, r)))

def insert_tree(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: Tree<K, V>, +k: K, +v: V) -> Tree<K, V>:
  blacken(K, V, ins(~K, ~cmp, V, t, k, v, c1(~K, ~cmp, V, k, t)))

# ---- deletion ----
#
# The sibling of the deficient subtree is black with two black children:
# recolour it red. A red parent absorbs the missing black (TD), a black one
# propagates the deficiency (UF).
def fl_b3(-K: Data, -V: Data, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match cpar:
    case R{}:
      TD{Node{B{}, l, e, Node{R{}, sl, se, sr}}}
    case B{}:
      UF{Node{B{}, l, e, Node{R{}, sl, se, sr}}}

# sl (the sibling's left child) is red: rotate right then left.
def fl_b2c(-K: Data, -V: Data, csl: Color, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match csl:
    case R{}:
      TD{Node{cpar, Node{B{}, l, e, a}, x, Node{B{}, b, se, sr}}}
    case B{}:
      fl_b3(K, V, Node{B{}, a, x, b}, se, sr, cpar, l, e)

def fl_b2(-K: Data, -V: Data, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match sl:
    case Leaf{}:
      fl_b3(K, V, Leaf{}, se, sr, cpar, l, e)
    case Node{csl, a, x, b}:
      fl_b2c(K, V, csl, a, x, b, se, sr, cpar, l, e)

# sr (the sibling's right child) is red: rotate left.
def fl_b1(-K: Data, -V: Data, sr_red: Bool, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match sr_red:
    case True{}:
      TD{Node{cpar, Node{B{}, l, e, sl}, se, blacken(K, V, sr)}}
    case False{}:
      fl_b2(K, V, sl, se, sr, cpar, l, e)

# The right sibling is the black node Node{B, sl, se, sr}.
def fl_black(-K: Data, -V: Data, sl: Tree<K, V>, se: E.Entry<K, V>, +sr: Tree<K, V>, cpar: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  fl_b1(K, V, is_red(K, V, sr), sl, se, sr, cpar, l, e)

# The right sibling is red (so the parent is black and the sibling's children
# are black): rotate left, then fix the deficiency under the now-red parent.
def fl_red(-K: Data, -V: Data, rl: Tree<K, V>, re: E.Entry<K, V>, rr: Tree<K, V>, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match rl:
    case Leaf{}:
      TD{Node{B{}, Node{R{}, l, e, Leaf{}}, re, rr}}
    case Node{crl, a, x, b}:
      TD{Node{B{}, upd_tree(K, V, fl_black(K, V, a, x, b, R{}, l, e)), re, rr}}

def fl_c(-K: Data, -V: Data, cr: Color, rl: Tree<K, V>, re: E.Entry<K, V>, rr: Tree<K, V>, c: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match cr:
    case B{}:
      fl_black(K, V, rl, re, rr, c, l, e)
    case R{}:
      fl_red(K, V, rl, re, rr, l, e)

def fl_u(-K: Data, -V: Data, r: Tree<K, V>, c: Color, l: Tree<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match r:
    case Leaf{}:
      UF{Node{c, l, e, Leaf{}}}
    case Node{cr, rl, re, rr}:
      fl_c(K, V, cr, rl, re, rr, c, l, e)

# The LEFT child of Node{c, _, e, r} came back as u.
def fix_left(-K: Data, -V: Data, r: Tree<K, V>, c: Color, u: UpD<K, V>, e: E.Entry<K, V>) -> UpD<K, V>:
  match u:
    case TD{l}:
      TD{Node{c, l, e, r}}
    case UF{l}:
      fl_u(K, V, r, c, l, e)

# ---- the mirror image, for a deficient RIGHT child ----

def fr_b3(-K: Data, -V: Data, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match cpar:
    case R{}:
      TD{Node{B{}, Node{R{}, sl, se, sr}, e, r}}
    case B{}:
      UF{Node{B{}, Node{R{}, sl, se, sr}, e, r}}

def fr_b2c(-K: Data, -V: Data, csr: Color, a: Tree<K, V>, x: E.Entry<K, V>, b: Tree<K, V>, sl: Tree<K, V>, se: E.Entry<K, V>, cpar: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match csr:
    case R{}:
      TD{Node{cpar, Node{B{}, sl, se, a}, x, Node{B{}, b, e, r}}}
    case B{}:
      fr_b3(K, V, sl, se, Node{B{}, a, x, b}, cpar, e, r)

def fr_b2(-K: Data, -V: Data, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match sr:
    case Leaf{}:
      fr_b3(K, V, sl, se, Leaf{}, cpar, e, r)
    case Node{csr, a, x, b}:
      fr_b2c(K, V, csr, a, x, b, sl, se, cpar, e, r)

def fr_b1(-K: Data, -V: Data, sl_red: Bool, sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match sl_red:
    case True{}:
      TD{Node{cpar, blacken(K, V, sl), se, Node{B{}, sr, e, r}}}
    case False{}:
      fr_b2(K, V, sl, se, sr, cpar, e, r)

def fr_black(-K: Data, -V: Data, +sl: Tree<K, V>, se: E.Entry<K, V>, sr: Tree<K, V>, cpar: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  fr_b1(K, V, is_red(K, V, sl), sl, se, sr, cpar, e, r)

def fr_red(-K: Data, -V: Data, ll: Tree<K, V>, le: E.Entry<K, V>, lr: Tree<K, V>, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match lr:
    case Leaf{}:
      TD{Node{B{}, ll, le, Node{R{}, Leaf{}, e, r}}}
    case Node{clr, a, x, b}:
      TD{Node{B{}, ll, le, upd_tree(K, V, fr_black(K, V, a, x, b, R{}, e, r))}}

def fr_c(-K: Data, -V: Data, cl: Color, ll: Tree<K, V>, le: E.Entry<K, V>, lr: Tree<K, V>, c: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match cl:
    case B{}:
      fr_black(K, V, ll, le, lr, c, e, r)
    case R{}:
      fr_red(K, V, ll, le, lr, e, r)

def fr_u(-K: Data, -V: Data, l: Tree<K, V>, c: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match l:
    case Leaf{}:
      UF{Node{c, Leaf{}, e, r}}
    case Node{cl, ll, le, lr}:
      fr_c(K, V, cl, ll, le, lr, c, e, r)

# The RIGHT child of Node{c, l, e, _} came back as u.
def fix_right(-K: Data, -V: Data, l: Tree<K, V>, c: Color, e: E.Entry<K, V>, u: UpD<K, V>) -> UpD<K, V>:
  match u:
    case TD{r}:
      TD{Node{c, l, e, r}}
    case UF{r}:
      fr_u(K, V, l, c, e, r)

# ---- removing the node itself ----

def rm_leaf0(-K: Data, -V: Data, c: Color) -> UpD<K, V>:
  match c:
    case R{}:
      TD{Leaf{}}
    case B{}:
      UF{Leaf{}}

# The node's RIGHT child is a leaf: it is replaced by its left child.
def rm_leaf(-K: Data, -V: Data, c: Color, l: Tree<K, V>) -> UpD<K, V>:
  match l:
    case Leaf{}:
      rm_leaf0(K, V, c)
    case Node{cl, a, x, b}:
      TD{Node{B{}, a, x, b}}

# The node's LEFT child is a leaf: it is replaced by its right child.
def rm_left_leaf(-K: Data, -V: Data, c: Color, r: Tree<K, V>) -> UpD<K, V>:
  match r:
    case Leaf{}:
      rm_leaf0(K, V, c)
    case Node{cr, a, x, b}:
      TD{Node{B{}, a, x, b}}

def sm_pick(-K: Data, -V: Data, s: SM<K, V>, c: Color, e: E.Entry<K, V>, r: Tree<K, V>) -> SM<K, V>:
  match s:
    case SMNone{}:
      SMSome{e, rm_left_leaf(K, V, c, r)}
    case SMSome{x, u}:
      SMSome{x, fix_left(K, V, r, c, u, e)}

# The smallest entry of t and what is left of t.
def split_min(-K: Data, -V: Data, t: Tree<K, V>) -> SM<K, V>:
  match t:
    case Leaf{}:
      SMNone{}
    case Node{c, l, e, r}:
      sm_pick(K, V, split_min(K, V, l), c, e, r)

def dh_pick(-K: Data, -V: Data, s: SM<K, V>, c: Color, l: Tree<K, V>) -> UpD<K, V>:
  match s:
    case SMNone{}:
      TD{l}
    case SMSome{x, u}:
      fix_right(K, V, l, c, x, u)

# Delete the node Node{c, l, _, r} itself.
def del_here(-K: Data, -V: Data, c: Color, l: Tree<K, V>, r: Tree<K, V>) -> UpD<K, V>:
  match r:
    case Leaf{}:
      rm_leaf(K, V, c, l)
    case Node{cr, rl, re, rr}:
      dh_pick(K, V, split_min(K, V, Node{cr, rl, re, rr}), c, l)

# a = cmp(k, key at the root of t)
def del(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, a: Cmp) -> UpD<K, V>:
  match t a:
    case Leaf{} _:
      TD{Leaf{}}
    case Node{c, +l, e, r} LT{}:
      fix_left(K, V, r, c, del(~K, ~cmp, V, l, k, c1(~K, ~cmp, V, k, l)), e)
    case Node{c, l, e, r} EQ{}:
      del_here(K, V, c, l, r)
    case Node{c, l, e, +r} GT{}:
      fix_right(K, V, l, c, e, del(~K, ~cmp, V, r, k, c1(~K, ~cmp, V, k, r)))

def remove_tree(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: Tree<K, V>, +k: K) -> Tree<K, V>:
  blacken(K, V, upd_tree(K, V, del(~K, ~cmp, V, t, k, c1(~K, ~cmp, V, k, t))))

# ---- queries ----

def find(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, a: Cmp) -> Maybe<&2, V>:
  match t a:
    case Leaf{} _:
      None{}
    case Node{c, +l, e, r} LT{}:
      find(~K, ~cmp, V, l, k, c1(~K, ~cmp, V, k, l))
    case Node{c, l, e, r} EQ{}:
      Some{E.val(K, V, e)}
    case Node{c, l, e, +r} GT{}:
      find(~K, ~cmp, V, r, k, c1(~K, ~cmp, V, k, r))

def lookup_tree(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: Tree<K, V>, +k: K) -> Maybe<&2, V>:
  find(~K, ~cmp, V, t, k, c1(~K, ~cmp, V, k, t))

def orelse(-K: Data, -V: Data, m: Maybe<&2, E.Entry<K, V>>, e: E.Entry<K, V>) -> Maybe<&2, E.Entry<K, V>>:
  match m:
    case None{}:
      Some{e}
    case Some{x}:
      Some{x}

def min_go(-K: Data, -V: Data, t: Tree<K, V>) -> Maybe<&2, E.Entry<K, V>>:
  match t:
    case Leaf{}:
      None{}
    case Node{c, Leaf{}, e, r}:
      Some{e}
    case Node{c, Node{cc, ll, ee, rr}, e, r}:
      min_go(K, V, Node{cc, ll, ee, rr})

def max_go(-K: Data, -V: Data, t: Tree<K, V>) -> Maybe<&2, E.Entry<K, V>>:
  match t:
    case Leaf{}:
      None{}
    case Node{c, l, e, Leaf{}}:
      Some{e}
    case Node{c, l, e, Node{cc, ll, ee, rr}}:
      max_go(K, V, Node{cc, ll, ee, rr})

# a = cmp(key at the root of t, k): the first entry with key >= k
def lb(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, a: Cmp) -> Maybe<&2, E.Entry<K, V>>:
  match t a:
    case Leaf{} _:
      None{}
    case Node{c, l, e, +r} LT{}:
      lb(~K, ~cmp, V, r, k, d1(~K, ~cmp, V, k, r))
    case Node{c, l, e, r} EQ{}:
      Some{e}
    case Node{c, +l, e, r} GT{}:
      orelse(K, V, lb(~K, ~cmp, V, l, k, d1(~K, ~cmp, V, k, l)), e)

def lower_tree(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +t: Tree<K, V>, +k: K) -> Maybe<&2, E.Entry<K, V>>:
  lb(~K, ~cmp, V, t, k, d1(~K, ~cmp, V, k, t))

def in_range(~K: Data, ~cmp: K -> K -> Cmp, +lo: K, +hi: K, +k: K) -> Bool:
  Bool.and(Bool.not(Cmp.is_gt(cmp(lo, k))), Cmp.is_lt(cmp(k, hi)))

def cons_if(-K: Data, -V: Data, b: Bool, e: E.Entry<K, V>, rest: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match b:
    case True{}:
      Con{e, rest}
    case False{}:
      rest

# Entries of t with lo <= key < hi (in order), followed by acc; go = False
# skips a subtree that cannot contain such keys.
def rng(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +lo: K, +hi: K, acc: List<&2, E.Entry<K, V>>, go: Bool) -> List<&2, E.Entry<K, V>>:
  match t go:
    case _ False{}:
      acc
    case Leaf{} True{}:
      acc
    case Node{c, l, +e, r} True{}:
      rng(~K, ~cmp, V, l, lo, hi, cons_if(K, V, in_range(~K, ~cmp, lo, hi, E.key(K, V, e)), e, rng(~K, ~cmp, V, r, lo, hi, acc, Cmp.is_lt(cmp(E.key(K, V, e), hi)))), Cmp.is_lt(cmp(lo, E.key(K, V, e))))

# In-order entries followed by acc.
def entries(-K: Data, -V: Data, t: Tree<K, V>, acc: List<&2, E.Entry<K, V>>) -> List<&2, E.Entry<K, V>>:
  match t:
    case Leaf{}:
      acc
    case Node{c, l, e, r}:
      entries(K, V, l, Con{e, entries(K, V, r, acc)})

# ---- public API ----

def new(-K: Data, -V: Data) -> OrdMap<K, V>:
  BST{0n, Leaf{}}

def length(-K: Data, -V: Data, s: OrdMap<K, V>) -> Nat:
  match s:
    case BST{n, t}:
      n

def grow(-V: Data, m: Maybe<&2, V>, +n: Nat) -> Nat:
  match m:
    case None{}:
      1n+n
    case Some{v}:
      n

# Insert and return the old binding in the same descent. The old binding
# determines whether the cached size grows; no preliminary lookup is needed.
def ins_left(-K: Data, -V: Data, c: Color, e: E.Entry<K, V>, r: Tree<K, V>, result: Tree<K, V> & Maybe<&2, V>) -> Tree<K, V> & Maybe<&2, V>:
  (l, old) = result
  (balance(K, V, c, l, e, r), old)

def ins_right(-K: Data, -V: Data, c: Color, l: Tree<K, V>, e: E.Entry<K, V>, result: Tree<K, V> & Maybe<&2, V>) -> Tree<K, V> & Maybe<&2, V>:
  (r, old) = result
  (balance(K, V, c, l, e, r), old)

def ins_found(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, +v: V, a: Cmp) -> Tree<K, V> & Maybe<&2, V>:
  match t a:
    case Leaf{} _:
      (Node{R{}, Leaf{}, E.Entry{k, v}, Leaf{}}, None{})
    case Node{c, +l, e, r} LT{}:
      ins_left(K, V, c, e, r, ins_found(~K, ~cmp, V, l, k, v, c1(~K, ~cmp, V, k, l)))
    case Node{c, l, e, r} EQ{}:
      (Node{c, l, E.Entry{k, v}, r}, Some{E.val(K, V, e)})
    case Node{c, l, e, +r} GT{}:
      ins_right(K, V, c, l, e, ins_found(~K, ~cmp, V, r, k, v, c1(~K, ~cmp, V, k, r)))

def insert_finish(-K: Data, -V: Data, n: Nat, result: Tree<K, V> & Maybe<&2, V>) -> OrdMap<K, V>:
  (t, old) = result
  BST{grow(V, old, n), blacken(K, V, t)}

# Map k to v (replacing any previous value).
def insert(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K, +v: V) -> OrdMap<K, V>:
  match s:
    case BST{n, +t}:
      insert_finish(K, V, n, ins_found(~K, ~cmp, V, t, k, v, c1(~K, ~cmp, V, k, t)))

def remove_at(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, m: Maybe<&2, V>, +n: Nat, +t: Tree<K, V>, +k: K) -> OrdMap<K, V> & Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      (BST{n, t}, Fail{E.KeyNotFound{}})
    case Some{v}:
      (BST{Nat.sub(n, 1n), remove_tree(~K, ~cmp, V, t, k)}, Done{v})

def del_left_found(-K: Data, -V: Data, r: Tree<K, V>, c: Color, e: E.Entry<K, V>, result: UpD<K, V> & Maybe<&2, V>) -> UpD<K, V> & Maybe<&2, V>:
  (u, old) = result
  (fix_left(K, V, r, c, u, e), old)

def del_right_found(-K: Data, -V: Data, l: Tree<K, V>, c: Color, e: E.Entry<K, V>, result: UpD<K, V> & Maybe<&2, V>) -> UpD<K, V> & Maybe<&2, V>:
  (u, old) = result
  (fix_right(K, V, l, c, e, u), old)

def del_found(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, t: Tree<K, V>, +k: K, a: Cmp) -> UpD<K, V> & Maybe<&2, V>:
  match t a:
    case Leaf{} _:
      (TD{Leaf{}}, None{})
    case Node{c, +l, e, r} LT{}:
      del_left_found(K, V, r, c, e, del_found(~K, ~cmp, V, l, k, c1(~K, ~cmp, V, k, l)))
    case Node{c, l, e, r} EQ{}:
      (del_here(K, V, c, l, r), Some{E.val(K, V, e)})
    case Node{c, l, e, +r} GT{}:
      del_right_found(K, V, l, c, e, del_found(~K, ~cmp, V, r, k, c1(~K, ~cmp, V, k, r)))

def remove_finish(-K: Data, -V: Data, n: Nat, result: UpD<K, V> & Maybe<&2, V>) -> OrdMap<K, V> & Result<&2, &2, E.Error, V>:
  match result:
    case Tuple{u, None{}}:
      (BST{n, upd_tree(K, V, u)}, Fail{E.KeyNotFound{}})
    case Tuple{u, Some{v}}:
      (BST{Nat.sub(n, 1n), blacken(K, V, upd_tree(K, V, u))}, Done{v})

# Find the removed binding during deletion, without a preliminary search.
def remove(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> OrdMap<K, V> & Result<&2, &2, E.Error, V>:
  match s:
    case BST{n, +t}:
      remove_finish(K, V, n, del_found(~K, ~cmp, V, t, k, c1(~K, ~cmp, V, k, t)))

def result(-V: Data, m: Maybe<&2, V>) -> Result<&2, &2, E.Error, V>:
  match m:
    case None{}:
      Fail{E.KeyNotFound{}}
    case Some{v}:
      Done{v}

def lookup(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Result<&2, &2, E.Error, V>:
  match s:
    case BST{n, +t}:
      result(V, lookup_tree(~K, ~cmp, V, t, k))

# The value stored at k, if any (Maybe form of lookup, for client structures).
def get(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Maybe<&2, V>:
  match s:
    case BST{n, +t}:
      lookup_tree(~K, ~cmp, V, t, k)

def present(-V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def contains(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Bool:
  match s:
    case BST{n, +t}:
      present(V, lookup_tree(~K, ~cmp, V, t, k))

def entry(-K: Data, -V: Data, m: Maybe<&2, E.Entry<K, V>>, err: E.Error) -> Result<&2, &2, E.Error, E.Entry<K, V>>:
  match m:
    case None{}:
      Fail{err}
    case Some{e}:
      Done{e}

def min(-K: Data, -V: Data, s: OrdMap<K, V>) -> Result<&2, &2, E.Error, E.Entry<K, V>>:
  match s:
    case BST{n, t}:
      entry(K, V, min_go(K, V, t), E.EmptyTree{})

def max(-K: Data, -V: Data, s: OrdMap<K, V>) -> Result<&2, &2, E.Error, E.Entry<K, V>>:
  match s:
    case BST{n, t}:
      entry(K, V, max_go(K, V, t), E.EmptyTree{})

# First entry with key >= k.
def lower_bound(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +k: K) -> Result<&2, &2, E.Error, E.Entry<K, V>>:
  match s:
    case BST{n, +t}:
      entry(K, V, lower_tree(~K, ~cmp, V, t, k), E.KeyNotFound{})

# Entries with lo <= key < hi, in key order.
def range(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, s: OrdMap<K, V>, +lo: K, +hi: K) -> List<&2, E.Entry<K, V>>:
  match s:
    case BST{n, t}:
      rng(~K, ~cmp, V, t, lo, hi, Nil{}, True{})

def to_list(-K: Data, -V: Data, s: OrdMap<K, V>) -> List<&2, E.Entry<K, V>>:
  match s:
    case BST{n, t}:
      entries(K, V, t, Nil{})

# ---- operation traces ----

def obs_val(-K: Data, -V: Data, r: OrdMap<K, V> & Result<&2, &2, E.Error, V>) -> OrdMap<K, V> & E.Obs<K, V>:
  (s, x) = r
  (s, E.OVal{x})

def step(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, +s: OrdMap<K, V>, op: E.Op<K, V>) -> OrdMap<K, V> & E.Obs<K, V>:
  match op:
    case E.Length{}:
      (s, E.ONat{length(K, V, s)})
    case E.Insert{k, v}:
      (insert(~K, ~cmp, V, s, k, v), E.OUnit{})
    case E.Remove{k}:
      obs_val(K, V, remove(~K, ~cmp, V, s, k))
    case E.Lookup{k}:
      (s, E.OVal{lookup(~K, ~cmp, V, s, k)})
    case E.Contains{k}:
      (s, E.OBool{contains(~K, ~cmp, V, s, k)})
    case E.Min{}:
      (s, E.OEntry{min(K, V, s)})
    case E.Max{}:
      (s, E.OEntry{max(K, V, s)})
    case E.LowerBound{k}:
      (s, E.OEntry{lower_bound(~K, ~cmp, V, s, k)})
    case E.Range{lo, hi}:
      (s, E.OList{range(~K, ~cmp, V, s, lo, hi)})
    case E.ToList{}:
      (s, E.OList{to_list(K, V, s)})

def record(-K: Data, -V: Data, acc: List<&2, E.Obs<K, V>>, r: OrdMap<K, V> & E.Obs<K, V>) -> OrdMap<K, V> & List<&2, E.Obs<K, V>>:
  (s, o) = r
  (s, Con{o, acc})

def step_acc(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, op: E.Op<K, V>, st: OrdMap<K, V> & List<&2, E.Obs<K, V>>) -> OrdMap<K, V> & List<&2, E.Obs<K, V>>:
  (s, acc) = st
  record(K, V, acc, step(~K, ~cmp, V, s, op))

def run_acc(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, ops: List<&2, E.Op<K, V>>, st: OrdMap<K, V> & List<&2, E.Obs<K, V>>) -> OrdMap<K, V> & List<&2, E.Obs<K, V>>:
  match ops:
    case Nil{}:
      st
    case Con{op, rest}:
      run_acc(~K, ~cmp, V, rest, step_acc(~K, ~cmp, V, op, st))

def finish(-K: Data, -V: Data, st: OrdMap<K, V> & List<&2, E.Obs<K, V>>) -> OrdMap<K, V> & List<&2, E.Obs<K, V>>:
  (s, acc) = st
  (s, List.reverse(&2, E.Obs<K, V>, acc))

def run(~K: Data, ~cmp: K -> K -> Cmp, -V: Data, ops: List<&2, E.Op<K, V>>, s: OrdMap<K, V>) -> OrdMap<K, V> & List<&2, E.Obs<K, V>>:
  finish(K, V, run_acc(~K, ~cmp, V, ops, (s, Nil{})))

# ---- checked instances (proofs/balanced_search_tree.bend) ----

def run_u32(-V: Data, ops: List<&2, E.Op<U32, V>>, s: OrdMap<U32, V>) -> OrdMap<U32, V> & List<&2, E.Obs<U32, V>>:
  run(~U32, ~U32.cmp, V, ops, s)

def run_string(-V: Data, ops: List<&2, E.Op<String, V>>, s: OrdMap<String, V>) -> OrdMap<String, V> & List<&2, E.Obs<String, V>>:
  run(~String, ~String.order, V, ops, s)
