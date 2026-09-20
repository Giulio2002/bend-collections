import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32alg.bend as UA
import ../lib/u32seq.bend as QS
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ./node.bend as T
import ../../src/internal/vec.bend as V
import ../../reference/lru/proofs/nat_algebra.bend as NA

# Meaning of a segment tree: vals(t) lists its values (excluding tags of
# ancestors); a node's tag is added to every value below it. The invariant
# says every node stores the sum of vals of its subtree.

def vals(t: T.Node) -> List<&2, U32>:
  match t:
    case T.SLeaf{x}:
      Con{x, Nil{}}
    case T.SNode{s, z, l, r}:
      Q.add_each(SC.append(U32, vals(l), vals(r)), z)

def perfect(+d: Nat, t: T.Node) -> Bool:
  match d t:
    case 0n T.SLeaf{x}:
      True{}
    case 0n T.SNode{s, z, l, r}:
      False{}
    case 1n+p T.SLeaf{x}:
      False{}
    case 1n+p T.SNode{s, z, l, r}:
      Bool.and(perfect(p, l), perfect(p, r))

def goods(t: T.Node) -> Bool:
  match t:
    case T.SLeaf{x}:
      True{}
    case T.SNode{s, +z, +l, +r}:
      Bool.and(U32.is_eq(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z))), Bool.and(goods(l), goods(r)))

# v added to the first i values.
def addfirst(xs: List<&2, U32>, i: Nat, +v: U32) -> List<&2, U32>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{h, t}
    case Con{h, t} 1n+j:
      Con{U32.add(h, v), addfirst(t, j, v)}

# k copies of a, added.
def times(+a: U32, k: Nat) -> U32:
  match k:
    case 0n:
      0
    case 1n+j:
      U32.add(a, times(a, j))

# ---- U32 rearrangements ----

def rot(+h: U32, +v: U32, +z: U32) -> {U32.add(U32.add(h, v), z) == U32.add(U32.add(h, z), v) : U32}:
  %Equal.sym(U32, U32.add(U32.add(h, v), z), U32.add(h, U32.add(v, z)), UA.assoc(h, v, z)) : {_ == U32.add(U32.add(h, z), v) : U32}
  %Equal.sym(U32, U32.add(U32.add(h, z), v), U32.add(h, U32.add(z, v)), UA.assoc(h, z, v)) : {U32.add(h, U32.add(v, z)) == _ : U32}
  %U32.add_comm(v, z) : {U32.add(h, U32.add(v, z)) == U32.add(h, _) : U32}
  {==}

def swap4(+h: U32, +a: U32, +s: U32, +t: U32) -> {U32.add(U32.add(h, a), U32.add(s, t)) == U32.add(U32.add(h, s), U32.add(a, t)) : U32}:
  %Equal.sym(U32, U32.add(U32.add(h, a), U32.add(s, t)), U32.add(h, U32.add(a, U32.add(s, t))), UA.assoc(h, a, U32.add(s, t))) : {_ == U32.add(U32.add(h, s), U32.add(a, t)) : U32}
  %Equal.sym(U32, U32.add(U32.add(h, s), U32.add(a, t)), U32.add(h, U32.add(s, U32.add(a, t))), UA.assoc(h, s, U32.add(a, t))) : {U32.add(h, U32.add(a, U32.add(s, t))) == _ : U32}
  %Equal.sym(U32, U32.add(a, U32.add(s, t)), U32.add(s, U32.add(a, t)), UA.swap(a, s, t)) : {U32.add(h, _) == U32.add(h, U32.add(s, U32.add(a, t))) : U32}
  {==}

def cancel(+h: U32, +v: U32) -> {U32.add(U32.add(h, v), U32.sub(0, v)) == h : U32}:
  %Equal.sym(U32, U32.add(U32.add(h, v), U32.sub(0, v)), U32.add(h, U32.add(v, U32.sub(0, v))), UA.assoc(h, v, U32.sub(0, v))) : {_ == h : U32}
  %U32.add_comm(U32.sub(0, v), v) : {U32.add(h, _) == h : U32}
  %Equal.sym(U32, U32.add(U32.sub(0, v), v), 0, UA.sub_add(0, v)) : {U32.add(h, _) == h : U32}
  UA.add_zero(h)

# ---- add_each ----

def each_zero(+xs: List<&2, U32>) -> {Q.add_each(xs, 0) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(U32, U32.add(h, 0), h, UA.add_zero(h)) : {Con{_, Q.add_each(t, 0)} == Con{h, t} : List<&2, U32>}
      LL.cons_cong(U32, h, Q.add_each(t, 0), t, each_zero(t))

def each_each(+xs: List<&2, U32>, +a: U32, +b: U32) -> {Q.add_each(Q.add_each(xs, a), b) == Q.add_each(xs, U32.add(a, b)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(U32, U32.add(U32.add(h, a), b), U32.add(h, U32.add(a, b)), UA.assoc(h, a, b)) : {Con{_, Q.add_each(Q.add_each(t, a), b)} == Con{U32.add(h, U32.add(a, b)), Q.add_each(t, U32.add(a, b))} : List<&2, U32>}
      LL.cons_cong(U32, U32.add(h, U32.add(a, b)), Q.add_each(Q.add_each(t, a), b), Q.add_each(t, U32.add(a, b)), each_each(t, a, b))

def each_append(+xs: List<&2, U32>, +ys: List<&2, U32>, +a: U32) -> {Q.add_each(SC.append(U32, xs, ys), a) == SC.append(U32, Q.add_each(xs, a), Q.add_each(ys, a)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      LL.cons_cong(U32, U32.add(h, a), Q.add_each(SC.append(U32, t, ys), a), SC.append(U32, Q.add_each(t, a), Q.add_each(ys, a)), each_append(t, ys, a))

def each_length(+xs: List<&2, U32>, +a: U32) -> {SC.length(U32, Q.add_each(xs, a)) == SC.length(U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      N.succ_cong(SC.length(U32, Q.add_each(t, a)), SC.length(U32, t), each_length(t, a))

def times_add(+a: U32, +m: Nat, +k: Nat) -> {times(a, Nat.add(m, k)) == U32.add(times(a, m), times(a, k)) : U32}:
  match m:
    case 0n:
      Equal.sym(U32, U32.add(0, times(a, k)), times(a, k), UA.zero_add(times(a, k)))
    case 1n+j:
      %Equal.sym(U32, times(a, Nat.add(j, k)), U32.add(times(a, j), times(a, k)), times_add(a, j, k)) : {U32.add(a, _) == U32.add(U32.add(a, times(a, j)), times(a, k)) : U32}
      Equal.sym(U32, U32.add(U32.add(a, times(a, j)), times(a, k)), U32.add(a, U32.add(times(a, j), times(a, k))), UA.assoc(a, times(a, j), times(a, k)))

# 2^d copies of a is a shifted left d times.
def times_pow(+a: U32, +d: Nat) -> {times(a, V.pow2(d)) == U32.shln(a, d) : U32}:
  match d:
    case 0n:
      UA.add_zero(a)
    case 1n+p:
      %Equal.sym(Nat, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p))) : {times(a, _) == U32.shl(U32.shln(a, p)) : U32}
      %Equal.sym(U32, times(a, Nat.add(V.pow2(p), V.pow2(p))), U32.add(times(a, V.pow2(p)), times(a, V.pow2(p))), times_add(a, V.pow2(p), V.pow2(p))) : {_ == U32.shl(U32.shln(a, p)) : U32}
      %Equal.sym(U32, times(a, V.pow2(p)), U32.shln(a, p), times_pow(a, p)) : {U32.add(_, _) == U32.shl(U32.shln(a, p)) : U32}
      Equal.sym(U32, U32.shl(U32.shln(a, p)), U32.add(U32.shln(a, p), U32.shln(a, p)), UA.shl_add(U32.shln(a, p)))

def sum_each(+xs: List<&2, U32>, +a: U32) -> {Q.sum(Q.add_each(xs, a)) == U32.add(Q.sum(xs), times(a, SC.length(U32, xs))) : U32}:
  match xs:
    case Nil{}:
      Equal.sym(U32, U32.add(0, 0), 0, UA.zero_add(0))
    case Con{h, t}:
      %Equal.sym(U32, Q.sum(Q.add_each(t, a)), U32.add(Q.sum(t), times(a, SC.length(U32, t))), sum_each(t, a)) : {U32.add(U32.add(h, a), _) == U32.add(U32.add(h, Q.sum(t)), U32.add(a, times(a, SC.length(U32, t)))) : U32}
      swap4(h, a, Q.sum(t), times(a, SC.length(U32, t)))

# ---- addfirst ----

def addfirst_all(+xs: List<&2, U32>, +i: Nat, +v: U32, +h: {Nat.is_le(SC.length(U32, xs), i) == True{} : Bool}) -> {addfirst(xs, i, v) == Q.add_each(xs, v) : List<&2, U32>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({Con{x, t} == Q.add_each(Con{x, t}, v) : List<&2, U32>}, L.false_true(h))
    case Con{x, t} 1n+j:
      LL.cons_cong(U32, U32.add(x, v), addfirst(t, j, v), Q.add_each(t, v), addfirst_all(t, j, v, h))

def addfirst_zero(+xs: List<&2, U32>, +v: U32) -> {addfirst(xs, 0n, v) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def addfirst_append(+xs: List<&2, U32>, +ys: List<&2, U32>, +i: Nat, +v: U32) -> {addfirst(SC.append(U32, xs, ys), i, v) == SC.append(U32, addfirst(xs, i, v), addfirst(ys, Nat.sub(i, SC.length(U32, xs)), v)) : List<&2, U32>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{x, t} 0n:
      Equal.sym(List<&2, U32>, SC.append(U32, Con{x, t}, addfirst(ys, 0n, v)), SC.append(U32, Con{x, t}, ys), Equal.cong(List<&2, U32>, List<&2, U32>, q => SC.append(U32, Con{x, t}, q), addfirst(ys, 0n, v), ys, addfirst_zero(ys, v)))
    case Con{x, t} 1n+j:
      LL.cons_cong(U32, U32.add(x, v), addfirst(SC.append(U32, t, ys), j, v), SC.append(U32, addfirst(t, j, v), addfirst(ys, Nat.sub(j, SC.length(U32, t)), v)), addfirst_append(t, ys, j, v))

def each_addfirst(+xs: List<&2, U32>, +i: Nat, +v: U32, +z: U32) -> {Q.add_each(addfirst(xs, i, v), z) == addfirst(Q.add_each(xs, z), i, v) : List<&2, U32>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      %Equal.sym(U32, U32.add(U32.add(x, v), z), U32.add(U32.add(x, z), v), rot(x, v, z)) : {Con{_, Q.add_each(addfirst(t, j, v), z)} == Con{U32.add(U32.add(x, z), v), addfirst(Q.add_each(t, z), j, v)} : List<&2, U32>}
      LL.cons_cong(U32, U32.add(U32.add(x, z), v), Q.add_each(addfirst(t, j, v), z), addfirst(Q.add_each(t, z), j, v), each_addfirst(t, j, v, z))

def take_addfirst(+xs: List<&2, U32>, +i: Nat, +v: U32, +n: Nat) -> {SC.take(U32, addfirst(xs, i, v), n) == addfirst(SC.take(U32, xs, n), i, v) : List<&2, U32>}:
  match xs i n:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 1n+j 0n:
      {==}
    case Con{x, t} 0n 1n+m:
      {==}
    case Con{x, t} 1n+j 1n+m:
      LL.cons_cong(U32, U32.add(x, v), SC.take(U32, addfirst(t, j, v), m), addfirst(SC.take(U32, t, m), j, v), take_addfirst(t, j, v, m))

# addfirst over the whole prefix, then undo on a shorter prefix: range addition.
def split_first(+t: List<&2, U32>, +r: Nat, +v: U32) -> {addfirst(t, r, v) == SC.append(U32, Q.add_each(SC.take(U32, t, r), v), SC.drop(U32, t, r)) : List<&2, U32>}:
  match t r:
    case Nil{} _:
      {==}
    case Con{x, u} 0n:
      {==}
    case Con{x, u} 1n+j:
      LL.cons_cong(U32, U32.add(x, v), addfirst(u, j, v), SC.append(U32, Q.add_each(SC.take(U32, u, j), v), SC.drop(U32, u, j)), split_first(u, j, v))

def range_add(+xs: List<&2, U32>, +l: Nat, +r: Nat, +v: U32, +h: {Nat.is_le(l, r) == True{} : Bool}) -> {addfirst(addfirst(xs, r, v), l, U32.sub(0, v)) == SC.append(U32, SC.take(U32, xs, l), SC.append(U32, Q.add_each(Q.slice(xs, l, r), v), SC.drop(U32, xs, r))) : List<&2, U32>}:
  match xs l r:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 0n 1n+j:
      %Equal.sym(Nat, Nat.sub(1n+j, 0n), 1n+j, N.sub_zero(1n+j)) : {addfirst(addfirst(Con{x, t}, 1n+j, v), 0n, U32.sub(0, v)) == SC.append(U32, Q.add_each(SC.take(U32, Con{x, t}, _), v), SC.drop(U32, Con{x, t}, 1n+j)) : List<&2, U32>}
      LL.cons_cong(U32, U32.add(x, v), addfirst(t, j, v), SC.append(U32, Q.add_each(SC.take(U32, t, j), v), SC.drop(U32, t, j)), split_first(t, j, v))
    case Con{x, t} 1n+k 0n:
      Empty.absurd({addfirst(addfirst(Con{x, t}, 0n, v), 1n+k, U32.sub(0, v)) == SC.append(U32, SC.take(U32, Con{x, t}, 1n+k), SC.append(U32, Q.add_each(Q.slice(Con{x, t}, 1n+k, 0n), v), SC.drop(U32, Con{x, t}, 0n))) : List<&2, U32>}, L.false_true(h))
    case Con{x, t} 1n+k 1n+j:
      %Equal.sym(U32, U32.add(U32.add(x, v), U32.sub(0, v)), x, cancel(x, v)) : {Con{_, addfirst(addfirst(t, j, v), k, U32.sub(0, v))} == Con{x, SC.append(U32, SC.take(U32, t, k), SC.append(U32, Q.add_each(Q.slice(t, k, j), v), SC.drop(U32, t, j)))} : List<&2, U32>}
      LL.cons_cong(U32, x, addfirst(addfirst(t, j, v), k, U32.sub(0, v)), SC.append(U32, SC.take(U32, t, k), SC.append(U32, Q.add_each(Q.slice(t, k, j), v), SC.drop(U32, t, j))), range_add(t, k, j, v, h))

# ---- trees ----

def pf_l(+p: Nat, +s: U32, +z: U32, +l: T.Node, +r: T.Node, +pf: {perfect(1n+p, T.SNode{s, z, l, r}) == True{} : Bool}) -> {perfect(p, l) == True{} : Bool}:
  L.and_left(perfect(p, l), perfect(p, r), pf)

def pf_r(+p: Nat, +s: U32, +z: U32, +l: T.Node, +r: T.Node, +pf: {perfect(1n+p, T.SNode{s, z, l, r}) == True{} : Bool}) -> {perfect(p, r) == True{} : Bool}:
  L.and_right(perfect(p, l), perfect(p, r), pf)

def g_s(+s: U32, +z: U32, +l: T.Node, +r: T.Node, +g: {goods(T.SNode{s, z, l, r}) == True{} : Bool}) -> {s == Q.sum(vals(T.SNode{s, z, l, r})) : U32}:
  UA.eq_of(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), L.and_left(U32.is_eq(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z))), Bool.and(goods(l), goods(r)), g))

def g_l(+s: U32, +z: U32, +l: T.Node, +r: T.Node, +g: {goods(T.SNode{s, z, l, r}) == True{} : Bool}) -> {goods(l) == True{} : Bool}:
  L.and_left(goods(l), goods(r), L.and_right(U32.is_eq(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z))), Bool.and(goods(l), goods(r)), g))

def g_r(+s: U32, +z: U32, +l: T.Node, +r: T.Node, +g: {goods(T.SNode{s, z, l, r}) == True{} : Bool}) -> {goods(r) == True{} : Bool}:
  L.and_right(goods(l), goods(r), L.and_right(U32.is_eq(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z))), Bool.and(goods(l), goods(r)), g))

def g_mk(+s: U32, +z: U32, +l: T.Node, +r: T.Node, +a: {s == Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)) : U32}, +b: {goods(l) == True{} : Bool}, +c: {goods(r) == True{} : Bool}) -> {goods(T.SNode{s, z, l, r}) == True{} : Bool}:
  L.and_intro(U32.is_eq(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z))), Bool.and(goods(l), goods(r)), UA.eq_true(s, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), a), L.and_intro(goods(l), goods(r), b, c))

def vals_length(+d: Nat, +t: T.Node, +pf: {perfect(d, t) == True{} : Bool}) -> {SC.length(U32, vals(t)) == V.pow2(d) : Nat}:
  match d t:
    case 0n T.SLeaf{x}:
      {==}
    case 0n T.SNode{s, z, l, r}:
      Empty.absurd({SC.length(U32, vals(T.SNode{s, z, l, r})) == 1n : Nat}, L.false_true(pf))
    case 1n+p T.SLeaf{x}:
      Empty.absurd({1n == Nat.double(V.pow2(p)) : Nat}, L.false_true(pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r}:
      %Equal.sym(Nat, SC.length(U32, Q.add_each(SC.append(U32, vals(l), vals(r)), z)), SC.length(U32, SC.append(U32, vals(l), vals(r))), each_length(SC.append(U32, vals(l), vals(r)), z)) : {_ == Nat.double(V.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(U32, SC.append(U32, vals(l), vals(r))), Nat.add(SC.length(U32, vals(l)), SC.length(U32, vals(r))), LL.length_append(U32, vals(l), vals(r))) : {_ == Nat.double(V.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(U32, vals(l)), V.pow2(p), vals_length(p, l, pf_l(p, s, z, l, r, pf))) : {Nat.add(_, SC.length(U32, vals(r))) == Nat.double(V.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(U32, vals(r)), V.pow2(p), vals_length(p, r, pf_r(p, s, z, l, r, pf))) : {Nat.add(V.pow2(p), _) == Nat.double(V.pow2(p)) : Nat}
      Equal.sym(Nat, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p)))

def total_eq(+t: T.Node, +g: {goods(t) == True{} : Bool}) -> {T.total(t) == Q.sum(vals(t)) : U32}:
  match t:
    case T.SLeaf{x}:
      Equal.sym(U32, U32.add(x, 0), x, UA.add_zero(x))
    case T.SNode{s, z, l, r}:
      g_s(s, z, l, r, g)

# The node builder stores the right sum.
def node_good(+p: Nat, +l: T.Node, +r: T.Node, +z: U32, +pl: {perfect(p, l) == True{} : Bool}, +pr: {perfect(p, r) == True{} : Bool}, +gl: {goods(l) == True{} : Bool}, +gr: {goods(r) == True{} : Bool}) -> {goods(T.node(p, l, r, z)) == True{} : Bool}:
  +len = Equal.trans(Nat, SC.length(U32, SC.append(U32, vals(l), vals(r))), Nat.add(SC.length(U32, vals(l)), SC.length(U32, vals(r))), V.pow2(1n+p), LL.length_append(U32, vals(l), vals(r)),
    %Equal.sym(Nat, SC.length(U32, vals(l)), V.pow2(p), vals_length(p, l, pl)) : {Nat.add(_, SC.length(U32, vals(r))) == Nat.double(V.pow2(p)) : Nat}
    %Equal.sym(Nat, SC.length(U32, vals(r)), V.pow2(p), vals_length(p, r, pr)) : {Nat.add(V.pow2(p), _) == Nat.double(V.pow2(p)) : Nat}
    Equal.sym(Nat, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p))))
  g_mk(U32.add(U32.add(T.total(l), T.total(r)), U32.shln(z, 1n+p)), z, l, r,
    %Equal.sym(U32, Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), U32.add(Q.sum(SC.append(U32, vals(l), vals(r))), times(z, SC.length(U32, SC.append(U32, vals(l), vals(r))))), sum_each(SC.append(U32, vals(l), vals(r)), z)) : {U32.add(U32.add(T.total(l), T.total(r)), U32.shln(z, 1n+p)) == _ : U32}
    %Equal.sym(U32, Q.sum(SC.append(U32, vals(l), vals(r))), U32.add(Q.sum(vals(l)), Q.sum(vals(r))), QS.sum_append(vals(l), vals(r))) : {U32.add(U32.add(T.total(l), T.total(r)), U32.shln(z, 1n+p)) == U32.add(_, times(z, SC.length(U32, SC.append(U32, vals(l), vals(r))))) : U32}
    %Equal.sym(Nat, SC.length(U32, SC.append(U32, vals(l), vals(r))), V.pow2(1n+p), len) : {U32.add(U32.add(T.total(l), T.total(r)), U32.shln(z, 1n+p)) == U32.add(U32.add(Q.sum(vals(l)), Q.sum(vals(r))), times(z, _)) : U32}
    %Equal.sym(U32, times(z, V.pow2(1n+p)), U32.shln(z, 1n+p), times_pow(z, 1n+p)) : {U32.add(U32.add(T.total(l), T.total(r)), U32.shln(z, 1n+p)) == U32.add(U32.add(Q.sum(vals(l)), Q.sum(vals(r))), _) : U32}
    %Equal.sym(U32, T.total(l), Q.sum(vals(l)), total_eq(l, gl)) : {U32.add(U32.add(_, T.total(r)), U32.shln(z, 1n+p)) == U32.add(U32.add(Q.sum(vals(l)), Q.sum(vals(r))), U32.shln(z, 1n+p)) : U32}
    %Equal.sym(U32, T.total(r), Q.sum(vals(r)), total_eq(r, gr)) : {U32.add(U32.add(Q.sum(vals(l)), _), U32.shln(z, 1n+p)) == U32.add(U32.add(Q.sum(vals(l)), Q.sum(vals(r))), U32.shln(z, 1n+p)) : U32}
    {==},
    gl, gr)

def node_perfect(+p: Nat, +l: T.Node, +r: T.Node, +z: U32, +pl: {perfect(p, l) == True{} : Bool}, +pr: {perfect(p, r) == True{} : Bool}) -> {perfect(1n+p, T.node(p, l, r, z)) == True{} : Bool}:
  L.and_intro(perfect(p, l), perfect(p, r), pl, pr)

# Tagging a whole subtree adds v to all its values.
def tag_vals(+d: Nat, +t: T.Node, +v: U32, +pf: {perfect(d, t) == True{} : Bool}) -> {vals(T.tagall(d, t, v)) == Q.add_each(vals(t), v) : List<&2, U32>}:
  match d t:
    case 0n T.SLeaf{x}:
      {==}
    case 0n T.SNode{s, z, l, r}:
      Empty.absurd({vals(T.SNode{s, z, l, r}) == Q.add_each(vals(T.SNode{s, z, l, r}), v) : List<&2, U32>}, L.false_true(pf))
    case 1n+p T.SLeaf{x}:
      Empty.absurd({Con{x, Nil{}} == Q.add_each(Con{x, Nil{}}, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+p T.SNode{s, z, l, r}:
      Equal.sym(List<&2, U32>, Q.add_each(Q.add_each(SC.append(U32, vals(l), vals(r)), z), v), Q.add_each(SC.append(U32, vals(l), vals(r)), U32.add(z, v)), each_each(SC.append(U32, vals(l), vals(r)), z, v))

def tag_perfect(+d: Nat, +t: T.Node, +v: U32, +pf: {perfect(d, t) == True{} : Bool}) -> {perfect(d, T.tagall(d, t, v)) == True{} : Bool}:
  match d t:
    case 0n T.SLeaf{x}:
      {==}
    case 0n T.SNode{s, z, l, r}:
      pf
    case 1n+p T.SLeaf{x}:
      pf
    case 1n+p T.SNode{s, z, l, r}:
      pf

def tag_good(+d: Nat, +t: T.Node, +v: U32, +pf: {perfect(d, t) == True{} : Bool}, +g: {goods(t) == True{} : Bool}) -> {goods(T.tagall(d, t, v)) == True{} : Bool}:
  match d t:
    case 0n T.SLeaf{x}:
      {==}
    case 0n T.SNode{s, z, l, r}:
      g
    case 1n+p T.SLeaf{x}:
      g
    case 1n+ +p T.SNode{+s, +z, +l, +r}:
      +len = Equal.trans(Nat, SC.length(U32, Q.add_each(SC.append(U32, vals(l), vals(r)), z)), SC.length(U32, vals(T.SNode{s, z, l, r})), V.pow2(1n+p), {==}, vals_length(1n+p, T.SNode{s, z, l, r}, pf))
      g_mk(U32.add(s, U32.shln(v, 1n+p)), U32.add(z, v), l, r,
        %each_each(SC.append(U32, vals(l), vals(r)), z, v) : {U32.add(s, U32.shln(v, 1n+p)) == Q.sum(_) : U32}
        %Equal.sym(U32, Q.sum(Q.add_each(Q.add_each(SC.append(U32, vals(l), vals(r)), z), v)), U32.add(Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), times(v, SC.length(U32, Q.add_each(SC.append(U32, vals(l), vals(r)), z)))), sum_each(Q.add_each(SC.append(U32, vals(l), vals(r)), z), v)) : {U32.add(s, U32.shln(v, 1n+p)) == _ : U32}
        %Equal.sym(Nat, SC.length(U32, Q.add_each(SC.append(U32, vals(l), vals(r)), z)), V.pow2(1n+p), len) : {U32.add(s, U32.shln(v, 1n+p)) == U32.add(Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), times(v, _)) : U32}
        %Equal.sym(U32, times(v, V.pow2(1n+p)), U32.shln(v, 1n+p), times_pow(v, 1n+p)) : {U32.add(s, U32.shln(v, 1n+p)) == U32.add(Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), _) : U32}
        %Equal.sym(U32, s, Q.sum(vals(T.SNode{s, z, l, r})), g_s(s, z, l, r, g)) : {U32.add(_, U32.shln(v, 1n+p)) == U32.add(Q.sum(Q.add_each(SC.append(U32, vals(l), vals(r)), z)), U32.shln(v, 1n+p)) : U32}
        {==},
        g_l(s, z, l, r, g), g_r(s, z, l, r, g))

# ---- zero trees ----

def zeros_perfect(+d: Nat) -> {perfect(d, T.zeros(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(perfect(p, T.zeros(p)), perfect(p, T.zeros(p)), zeros_perfect(p), zeros_perfect(p))

def zeros_vals(+d: Nat) -> {vals(T.zeros(d)) == Q.zeros(V.pow2(d)) : List<&2, U32>}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(List<&2, U32>, vals(T.zeros(p)), Q.zeros(V.pow2(p)), zeros_vals(p)) : {Q.add_each(SC.append(U32, _, _), 0) == Q.zeros(Nat.double(V.pow2(p))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Q.add_each(SC.append(U32, Q.zeros(V.pow2(p)), Q.zeros(V.pow2(p))), 0), SC.append(U32, Q.zeros(V.pow2(p)), Q.zeros(V.pow2(p))), each_zero(SC.append(U32, Q.zeros(V.pow2(p)), Q.zeros(V.pow2(p))))) : {_ == Q.zeros(Nat.double(V.pow2(p))) : List<&2, U32>}
      %Equal.sym(Nat, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p))) : {SC.append(U32, Q.zeros(V.pow2(p)), Q.zeros(V.pow2(p))) == Q.zeros(_) : List<&2, U32>}
      LL.replicate_add(U32, V.pow2(p), V.pow2(p), 0)

def zeros_good(+d: Nat) -> {goods(T.zeros(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      g_mk(0, 0, T.zeros(p), T.zeros(p),
        %Equal.sym(List<&2, U32>, Q.add_each(SC.append(U32, vals(T.zeros(p)), vals(T.zeros(p))), 0), vals(T.zeros(1n+p)), {==}) : {0 == Q.sum(_) : U32}
        %Equal.sym(List<&2, U32>, vals(T.zeros(1n+p)), Q.zeros(V.pow2(1n+p)), zeros_vals(1n+p)) : {0 == Q.sum(_) : U32}
        Equal.sym(U32, Q.sum(Q.zeros(V.pow2(1n+p))), 0, QS.sum_zeros(V.pow2(1n+p))),
        zeros_good(p), zeros_good(p))
