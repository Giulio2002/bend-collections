import Base
import ./logic.bend as L
import ./nat.bend as N
import ./spec_common.bend as SC
import ./lemmas/proofs/nat_algebra.bend as NA

# Shared arithmetic and list facts for the FLAT SPLIT-POINT LAYOUT that the
# array-backed trees of this project use (src/fenwick_tree.bend and
# flat indexed structures):
#
#   * the value of index t lives at cell 2^d + t;
#   * the block [o, o + 2^p) of value indices (p >= 1) keeps its own cell at
#     the block's split point o + 2^(p-1);
#   * the cells a block can occupy are therefore exactly o+1 .. o+2^p-1, so
#     two sibling blocks never share one and a walk over one block leaves
#     every cell of the other untouched. That frame argument is plain
#     interval arithmetic, which is why this layout is used rather than the
#     2k/2k+1 one, where the cells of two sibling subtrees interleave.
#
# `hof(p)` is the half size a walk carries at remaining depth p (2^(p-1), and
# 0 at a leaf, where it is unused): one machine division steps from one level
# to the next, so no walk ever recomputes a power of two.

def nthc(xs: List<&2, U32>, q: Nat) -> U32:
  match xs q:
    case Nil{} _:
      0
    case Con{x, t} 0n:
      x
    case Con{x, t} 1n+p:
      nthc(t, p)

def nthc_nth(xs: List<&2, U32>, q: Nat, +h: {Nat.is_lt(q, SC.length(U32, xs)) == True{} : Bool}) -> {SC.nth(U32, xs, q) == Some{nthc(xs, q)} : Maybe<&2, U32>}:
  match xs q:
    case Nil{} _:
      Empty.absurd({SC.nth(U32, Nil{}, q) == Some{nthc(Nil{}, q)} : Maybe<&2, U32>}, N.lt_zero_absurd(q, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      nthc_nth(t, p, h)


def add_one(+o: Nat) -> {Nat.add(o, 1n) == 1n+o : Nat}:
  %Equal.sym(Nat, Nat.add(o, 1n), 1n+Nat.add(o, 0n), N.add_succ(o, 0n)) : {_ == 1n+o : Nat}
  N.succ_cong(Nat.add(o, 0n), o, N.add_zero(o))

def pow2_split(+q: Nat) -> {SC.pow2(1n+q) == Nat.add(SC.pow2(q), SC.pow2(q)) : Nat}:
  NA.double_self(SC.pow2(q))

# o < o + 2^q
# o < o + 2^q
def lt_split(+o: Nat, +q: Nat) -> {Nat.is_lt(o, Nat.add(o, SC.pow2(q))) == True{} : Bool}:
  N.succ_le_lt(o, Nat.add(o, SC.pow2(q)),
    %add_one(o) : {Nat.is_le(_, Nat.add(o, SC.pow2(q))) == True{} : Bool}
    N.le_add_left(1n, SC.pow2(q), o, N.pow2_pos(q)))

# o + 2^(1+q) == (o + 2^q) + 2^q
# o + 2^(1+q) == (o + 2^q) + 2^q
def split_assoc(+o: Nat, +q: Nat) -> {Nat.add(o, SC.pow2(1n+q)) == Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)) : Nat}:
  %Equal.sym(Nat, SC.pow2(1n+q), Nat.add(SC.pow2(q), SC.pow2(q)), pow2_split(q)) : {Nat.add(o, _) == Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), Nat.add(o, Nat.add(SC.pow2(q), SC.pow2(q))), N.add_assoc(o, SC.pow2(q), SC.pow2(q)))

# o + 2^q < o + 2^(1+q)
# o + 2^q < o + 2^(1+q)
def mid_lt(+o: Nat, +q: Nat) -> {Nat.is_lt(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(o, SC.pow2(1n+q)), Nat.add(Nat.add(o, SC.pow2(q)), SC.pow2(q)), split_assoc(o, q)) : {Nat.is_lt(Nat.add(o, SC.pow2(q)), _) == True{} : Bool}
  lt_split(Nat.add(o, SC.pow2(q)), q)

# ---- the model tree the cells realise ----

def is_eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      is_eq_sym(x, y)

def ne_gt(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(a, b), Nat.is_eq(b, a), is_eq_sym(a, b)) : {_ == False{} : Bool}
  N.is_eq_lt(b, a, h)

# 2^d <= 2^d + t
# 2^d <= 2^d + t
def base_le(+d: Nat, +t: Nat) -> {Nat.is_le(SC.pow2(d), Nat.add(SC.pow2(d), t)) == True{} : Bool}:
  N.le_add_right(SC.pow2(d), t)

# ---- a write below the block ----

def nthc_other(cl: List<&2, U32>, j: Nat, k: Nat, +v: U32, +ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {nthc(SC.update(U32, cl, j, v), k) == nthc(cl, k) : U32}:
  match cl j k:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      Empty.absurd({nthc(Con{v, t}, 0n) == nthc(Con{x, t}, 0n) : U32}, L.false_true(Equal.sym(Bool, True{}, False{}, ne)))
    case Con{x, t} 0n 1n+b:
      {==}
    case Con{x, t} 1n+a 0n:
      {==}
    case Con{x, t} 1n+a 1n+b:
      nthc_other(t, a, b, v, ne)

def nthc_same(cl: List<&2, U32>, j: Nat, +v: U32, +h: {Nat.is_lt(j, SC.length(U32, cl)) == True{} : Bool}) -> {nthc(SC.update(U32, cl, j, v), j) == v : U32}:
  match cl j:
    case Nil{} _:
      Empty.absurd({nthc(Nil{}, j) == v : U32}, N.lt_zero_absurd(j, h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+a:
      nthc_same(t, a, v, h)

# 2^d < 2^(d+1)
def base_lt(+d: Nat) -> {Nat.is_lt(SC.pow2(d), SC.pow2(1n+d)) == True{} : Bool}:
  N.pow2_lt_succ(d)

def in_cells(+cl: List<&2, U32>, +d: Nat, +k: Nat, +hk: {Nat.is_lt(k, SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}) -> {Nat.is_lt(k, SC.length(U32, cl)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(k, z) == True{} : Bool}, SC.pow2(1n+d), SC.length(U32, cl), Equal.sym(Nat, SC.length(U32, cl), SC.pow2(1n+d), hlen),
    N.lt_trans(k, SC.pow2(d), SC.pow2(1n+d), hk, base_lt(d)))

def leaf_in_cells(+cl: List<&2, U32>, +d: Nat, +o: Nat, +ho: {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}, +hlen: {SC.length(U32, cl) == SC.pow2(1n+d) : Nat}) -> {Nat.is_lt(Nat.add(SC.pow2(d), o), SC.length(U32, cl)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(SC.pow2(d), o), z) == True{} : Bool}, SC.pow2(1n+d), SC.length(U32, cl), Equal.sym(Nat, SC.length(U32, cl), SC.pow2(1n+d), hlen),
    %Equal.sym(Nat, SC.pow2(1n+d), Nat.add(SC.pow2(d), SC.pow2(d)), pow2_split(d)) : {Nat.is_lt(Nat.add(SC.pow2(d), o), _) == True{} : Bool}
    N.lt_add_left(o, SC.pow2(d), SC.pow2(d), ho))

# o < 2^d when the block [o, o+2^p) fits
# o < 2^d when the block [o, o+2^p) fits
def blk_lo(+o: Nat, +p: Nat, +d: Nat, +hw: {Nat.is_le(Nat.add(o, SC.pow2(p)), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}:
  N.lt_le_trans(o, Nat.add(o, SC.pow2(p)), SC.pow2(d), lt_split(o, p), hw)

# ---- the point addition walk is the model's ----

# 2^d + o < 2^(d+1) and o + 2^q < 2^(d+1)
def leaf_lt(+d: Nat, +o: Nat, +ho: {Nat.is_lt(o, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(SC.pow2(d), o), SC.pow2(1n+d)) == True{} : Bool}:
  %Equal.sym(Nat, SC.pow2(1n+d), Nat.add(SC.pow2(d), SC.pow2(d)), pow2_split(d)) : {Nat.is_lt(Nat.add(SC.pow2(d), o), _) == True{} : Bool}
  N.lt_add_left(o, SC.pow2(d), SC.pow2(d), ho)

def node_lt(+o: Nat, +q: Nat, +d: Nat, +hw: {Nat.is_le(Nat.add(o, SC.pow2(1n+q)), SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(o, SC.pow2(q)), SC.pow2(1n+d)) == True{} : Bool}:
  N.lt_trans(Nat.add(o, SC.pow2(q)), SC.pow2(d), SC.pow2(1n+d),
    N.lt_le_trans(Nat.add(o, SC.pow2(q)), Nat.add(o, SC.pow2(1n+q)), SC.pow2(d), mid_lt(o, q), hw), base_lt(d))

# ---- the prefix walk is the model's ----

# The half size a walk carries at remaining depth p: 2^(p-1), and 0 at a
# leaf (where it is unused). One machine division steps from one level to the
# next, so no walk ever recomputes a power of two.
def hof(p: Nat) -> Nat:
  Nat.div(SC.pow2(p), 2n)

def hof_succ(+q: Nat) -> {hof(1n+q) == SC.pow2(q) : Nat}:
  N.div2_pow2(q)

# The comparison the source makes against the carried half size is exactly
# the model's branch decision.
def nthc_rep(m: Nat, k: Nat) -> {nthc(SC.replicate(U32, m, 0), k) == 0 : U32}:
  match m k:
    case 0n _:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      nthc_rep(a, b)

