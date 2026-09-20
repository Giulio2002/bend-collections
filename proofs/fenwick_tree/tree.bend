import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32alg.bend as UA
import ../lib/u32seq.bend as QS
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ./model.bend as M
import ../../reference/lru/proofs/nat_algebra.bend as NA

# The Fenwick tree of partial sums: its leaves are the values; every
# internal node's stored sum equals the sum of its left subtree's leaves.

def leaves(t: M.Node) -> List<&2, U32>:
  match t:
    case M.FLeaf{x}:
      Con{x, Nil{}}
    case M.FNode{s, l, r}:
      SC.append(U32, leaves(l), leaves(r))

def perfect(+d: Nat, t: M.Node) -> Bool:
  match d t:
    case 0n M.FLeaf{x}:
      True{}
    case 0n M.FNode{s, l, r}:
      False{}
    case 1n+p M.FLeaf{x}:
      False{}
    case 1n+p M.FNode{s, l, r}:
      Bool.and(perfect(p, l), perfect(p, r))

def goodf(t: M.Node) -> Bool:
  match t:
    case M.FLeaf{x}:
      True{}
    case M.FNode{s, +l, r}:
      Bool.and(U32.is_eq(s, Q.sum(leaves(l))), Bool.and(goodf(l), goodf(r)))

def pf_l(+p: Nat, +s: U32, +l: M.Node, +r: M.Node, +pf: {perfect(1n+p, M.FNode{s, l, r}) == True{} : Bool}) -> {perfect(p, l) == True{} : Bool}:
  L.and_left(perfect(p, l), perfect(p, r), pf)

def pf_r(+p: Nat, +s: U32, +l: M.Node, +r: M.Node, +pf: {perfect(1n+p, M.FNode{s, l, r}) == True{} : Bool}) -> {perfect(p, r) == True{} : Bool}:
  L.and_right(perfect(p, l), perfect(p, r), pf)

def g_s(+s: U32, +l: M.Node, +r: M.Node, +g: {goodf(M.FNode{s, l, r}) == True{} : Bool}) -> {s == Q.sum(leaves(l)) : U32}:
  UA.eq_of(s, Q.sum(leaves(l)), L.and_left(U32.is_eq(s, Q.sum(leaves(l))), Bool.and(goodf(l), goodf(r)), g))

def g_l(+s: U32, +l: M.Node, +r: M.Node, +g: {goodf(M.FNode{s, l, r}) == True{} : Bool}) -> {goodf(l) == True{} : Bool}:
  L.and_left(goodf(l), goodf(r), L.and_right(U32.is_eq(s, Q.sum(leaves(l))), Bool.and(goodf(l), goodf(r)), g))

def g_r(+s: U32, +l: M.Node, +r: M.Node, +g: {goodf(M.FNode{s, l, r}) == True{} : Bool}) -> {goodf(r) == True{} : Bool}:
  L.and_right(goodf(l), goodf(r), L.and_right(U32.is_eq(s, Q.sum(leaves(l))), Bool.and(goodf(l), goodf(r)), g))

def g_mk(+s: U32, +l: M.Node, +r: M.Node, +a: {s == Q.sum(leaves(l)) : U32}, +b: {goodf(l) == True{} : Bool}, +c: {goodf(r) == True{} : Bool}) -> {goodf(M.FNode{s, l, r}) == True{} : Bool}:
  L.and_intro(U32.is_eq(s, Q.sum(leaves(l))), Bool.and(goodf(l), goodf(r)), UA.eq_true(s, Q.sum(leaves(l)), a), L.and_intro(goodf(l), goodf(r), b, c))

def leaves_length(+d: Nat, +t: M.Node, +pf: {perfect(d, t) == True{} : Bool}) -> {SC.length(U32, leaves(t)) == SC.pow2(d) : Nat}:
  match d t:
    case 0n M.FLeaf{x}:
      {==}
    case 0n M.FNode{s, l, r}:
      Empty.absurd({SC.length(U32, leaves(M.FNode{s, l, r})) == 1n : Nat}, L.false_true(pf))
    case 1n+p M.FLeaf{x}:
      Empty.absurd({1n == Nat.double(SC.pow2(p)) : Nat}, L.false_true(pf))
    case 1n+ +p M.FNode{+s, +l, +r}:
      %Equal.sym(Nat, SC.length(U32, SC.append(U32, leaves(l), leaves(r))), Nat.add(SC.length(U32, leaves(l)), SC.length(U32, leaves(r))), LL.length_append(U32, leaves(l), leaves(r))) : {_ == Nat.double(SC.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(U32, leaves(l)), SC.pow2(p), leaves_length(p, l, pf_l(p, s, l, r, pf))) : {Nat.add(_, SC.length(U32, leaves(r))) == Nat.double(SC.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(U32, leaves(r)), SC.pow2(p), leaves_length(p, r, pf_r(p, s, l, r, pf))) : {Nat.add(SC.pow2(p), _) == Nat.double(SC.pow2(p)) : Nat}
      Equal.sym(Nat, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), SC.pow2(p)), NA.double_self(SC.pow2(p)))

def left_len(+p: Nat, +l: M.Node, +pl: {perfect(p, l) == True{} : Bool}) -> {SC.pow2(p) == SC.length(U32, leaves(l)) : Nat}:
  Equal.sym(Nat, SC.length(U32, leaves(l)), SC.pow2(p), leaves_length(p, l, pl))

# ---- point addition ----

def add_perfect(+d: Nat, +t: M.Node, +i: Nat, +v: U32, +b: Bool, +pf: {perfect(d, t) == True{} : Bool}) -> {perfect(d, M.add_go(d, t, i, v, b)) == True{} : Bool}:
  match d t b:
    case 0n M.FLeaf{x} _:
      {==}
    case 0n M.FNode{s, l, r} _:
      pf
    case 1n+p M.FLeaf{x} _:
      pf
    case 1n+ +p M.FNode{+s, +l, +r} True{}:
      L.and_intro(perfect(p, M.add_go(p, l, i, v, M.dec(p, i))), perfect(p, r), add_perfect(p, l, i, v, M.dec(p, i), pf_l(p, s, l, r, pf)), pf_r(p, s, l, r, pf))
    case 1n+ +p M.FNode{+s, +l, +r} False{}:
      L.and_intro(perfect(p, l), perfect(p, M.add_go(p, r, Nat.sub(i, SC.pow2(p)), v, M.dec(p, Nat.sub(i, SC.pow2(p))))), pf_l(p, s, l, r, pf), add_perfect(p, r, Nat.sub(i, SC.pow2(p)), v, M.dec(p, Nat.sub(i, SC.pow2(p))), pf_r(p, s, l, r, pf)))

def add_leaves(+d: Nat, +t: M.Node, +i: Nat, +v: U32, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {M.dec(d, i) == b : Bool}, +pf: {perfect(d, t) == True{} : Bool}) -> {leaves(M.add_go(d, t, i, v, b)) == QS.addat(leaves(t), i, v) : List<&2, U32>}:
  match d t b:
    case 0n M.FLeaf{x} _:
      match i:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Con{U32.add(x, v), Nil{}} == Con{x, Nil{}} : List<&2, U32>}, N.lt_zero_absurd(q, hi))
    case 0n M.FNode{s, l, r} _:
      Empty.absurd({leaves(M.FNode{s, l, r}) == QS.addat(leaves(M.FNode{s, l, r}), i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+p M.FLeaf{x} _:
      Empty.absurd({Con{x, Nil{}} == QS.addat(Con{x, Nil{}}, i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+ +p M.FNode{+s, +l, +r} True{}:
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pf_l(p, s, l, r, pf)), eb)
      Equal.trans(List<&2, U32>, SC.append(U32, leaves(M.add_go(p, l, i, v, M.dec(p, i))), leaves(r)), SC.append(U32, QS.addat(leaves(l), i, v), leaves(r)), QS.addat(SC.append(U32, leaves(l), leaves(r)), i, v),
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => SC.append(U32, xs, leaves(r)), leaves(M.add_go(p, l, i, v, M.dec(p, i))), QS.addat(leaves(l), i, v), add_leaves(p, l, i, v, eb, M.dec(p, i), {==}, pf_l(p, s, l, r, pf))),
        Equal.sym(List<&2, U32>, QS.addat(SC.append(U32, leaves(l), leaves(r)), i, v), SC.append(U32, QS.addat(leaves(l), i, v), leaves(r)), QS.addat_left(leaves(l), leaves(r), i, v, hl)))
    case 1n+ +p M.FNode{+s, +l, +r} False{}:
      +k = Nat.sub(i, SC.pow2(p))
      +le = N.not_lt_le(i, SC.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pf_l(p, s, l, r, pf)), le)
      Equal.trans(List<&2, U32>, SC.append(U32, leaves(l), leaves(M.add_go(p, r, k, v, M.dec(p, k)))), SC.append(U32, leaves(l), QS.addat(leaves(r), k, v)), QS.addat(SC.append(U32, leaves(l), leaves(r)), i, v),
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => SC.append(U32, leaves(l), xs), leaves(M.add_go(p, r, k, v, M.dec(p, k))), QS.addat(leaves(r), k, v), add_leaves(p, r, k, v, A.upper_lt(i, p, hi, le), M.dec(p, k), {==}, pf_r(p, s, l, r, pf))),
        Equal.sym(List<&2, U32>, QS.addat(SC.append(U32, leaves(l), leaves(r)), i, v), SC.append(U32, leaves(l), QS.addat(leaves(r), k, v)),
          %Equal.sym(Nat, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pf_l(p, s, l, r, pf))) : {QS.addat(SC.append(U32, leaves(l), leaves(r)), i, v) == SC.append(U32, leaves(l), QS.addat(leaves(r), Nat.sub(i, _), v)) : List<&2, U32>}
          QS.addat_right(leaves(l), leaves(r), i, v, hr)))

def add_good(+d: Nat, +t: M.Node, +i: Nat, +v: U32, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {M.dec(d, i) == b : Bool}, +pf: {perfect(d, t) == True{} : Bool}, +g: {goodf(t) == True{} : Bool}) -> {goodf(M.add_go(d, t, i, v, b)) == True{} : Bool}:
  match d t b:
    case 0n M.FLeaf{x} _:
      {==}
    case 0n M.FNode{s, l, r} _:
      g
    case 1n+p M.FLeaf{x} _:
      {==}
    case 1n+ +p M.FNode{+s, +l, +r} True{}:
      +pl = pf_l(p, s, l, r, pf)
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pl), eb)
      +es = Equal.trans(U32, U32.add(s, v), U32.add(Q.sum(leaves(l)), v), Q.sum(leaves(M.add_go(p, l, i, v, M.dec(p, i)))),
        Equal.cong(U32, U32, z => U32.add(z, v), s, Q.sum(leaves(l)), g_s(s, l, r, g)),
        %Equal.sym(List<&2, U32>, leaves(M.add_go(p, l, i, v, M.dec(p, i))), QS.addat(leaves(l), i, v), add_leaves(p, l, i, v, eb, M.dec(p, i), {==}, pl)) : {U32.add(Q.sum(leaves(l)), v) == Q.sum(_) : U32}
        Equal.sym(U32, Q.sum(QS.addat(leaves(l), i, v)), U32.add(Q.sum(leaves(l)), v), QS.sum_addat(leaves(l), i, v, hl)))
      g_mk(U32.add(s, v), M.add_go(p, l, i, v, M.dec(p, i)), r, es, add_good(p, l, i, v, eb, M.dec(p, i), {==}, pl, g_l(s, l, r, g)), g_r(s, l, r, g))
    case 1n+ +p M.FNode{+s, +l, +r} False{}:
      +k = Nat.sub(i, SC.pow2(p))
      +le = N.not_lt_le(i, SC.pow2(p), eb)
      g_mk(s, l, M.add_go(p, r, k, v, M.dec(p, k)), g_s(s, l, r, g), g_l(s, l, r, g), add_good(p, r, k, v, A.upper_lt(i, p, hi, le), M.dec(p, k), {==}, pf_r(p, s, l, r, pf), g_r(s, l, r, g)))

# ---- prefix sums ----

def leaf_ok(+x: U32, +i: Nat, +hi: {Nat.is_le(i, 1n) == True{} : Bool}) -> {M.leaf_prefix(x, i) == Q.sum(SC.take(U32, Con{x, Nil{}}, i)) : U32}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      Equal.sym(U32, U32.add(x, Q.sum(SC.take(U32, Nil{}, j))), x, UA.add_zero(x))

def dbl_succ(+m: Nat) -> {1n+Nat.double(m) == Nat.add(m, 1n+m) : Nat}:
  %Equal.sym(Nat, Nat.add(m, 1n+m), 1n+Nat.add(m, m), N.add_succ(m, m)) : {1n+Nat.double(m) == _ : Nat}
  N.succ_cong(Nat.double(m), Nat.add(m, m), NA.double_self(m))

def hk_fix(+i: Nat, +p: Nat, +hi: {Nat.is_le(i, SC.pow2(1n+p)) == True{} : Bool}, +le: {Nat.is_le(SC.pow2(p), i) == True{} : Bool}) -> {Nat.is_le(Nat.sub(i, SC.pow2(p)), SC.pow2(p)) == True{} : Bool}:
  N.lt_succ_le(Nat.sub(i, SC.pow2(p)), SC.pow2(p), N.sub_lt(i, SC.pow2(p), 1n+SC.pow2(p), le, L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, 1n+Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), 1n+SC.pow2(p)), dbl_succ(SC.pow2(p)), N.le_lt_succ(i, Nat.double(SC.pow2(p)), hi))))

def hi_lt(+i: Nat, +p: Nat, +hi: {Nat.is_le(i, SC.pow2(1n+p)) == True{} : Bool}) -> {Nat.is_lt(i, 1n+SC.pow2(1n+p)) == True{} : Bool}:
  N.le_lt_succ(i, SC.pow2(1n+p), hi)

def prefix_ok(+d: Nat, +t: M.Node, +i: Nat, +hi: {Nat.is_le(i, SC.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {M.dec(d, i) == b : Bool}, +pf: {perfect(d, t) == True{} : Bool}, +g: {goodf(t) == True{} : Bool}) -> {M.prefix_go(d, t, i, b) == Q.sum(SC.take(U32, leaves(t), i)) : U32}:
  match d t b:
    case 0n M.FLeaf{x} _:
      leaf_ok(x, i, hi)
    case 0n M.FNode{s, l, r} _:
      Empty.absurd({0 == Q.sum(SC.take(U32, leaves(M.FNode{s, l, r}), i)) : U32}, L.false_true(pf))
    case 1n+p M.FLeaf{x} _:
      Empty.absurd({0 == Q.sum(SC.take(U32, Con{x, Nil{}}, i)) : U32}, L.false_true(pf))
    case 1n+ +p M.FNode{+s, +l, +r} True{}:
      +pl = pf_l(p, s, l, r, pf)
      +hl = L.subst(Nat, k => {Nat.is_le(i, k) == True{} : Bool}, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pl), N.lt_le(i, SC.pow2(p), eb))
      Equal.trans(U32, M.prefix_go(p, l, i, M.dec(p, i)), Q.sum(SC.take(U32, leaves(l), i)), Q.sum(SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i)),
        prefix_ok(p, l, i, N.lt_le(i, SC.pow2(p), eb), M.dec(p, i), {==}, pl, g_l(s, l, r, g)),
        Equal.cong(List<&2, U32>, U32, xs => Q.sum(xs), SC.take(U32, leaves(l), i), SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i), Equal.sym(List<&2, U32>, SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i), SC.take(U32, leaves(l), i), LL.sc_take_append_left(U32, leaves(l), leaves(r), i, hl))))
    case 1n+ +p M.FNode{+s, +l, +r} False{}:
      +pl = pf_l(p, s, l, r, pf)
      +k = Nat.sub(i, SC.pow2(p))
      +le = N.not_lt_le(i, SC.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, SC.pow2(p), SC.length(U32, leaves(l)), left_len(p, l, pl), le)
      %Equal.sym(U32, M.prefix_go(p, r, k, M.dec(p, k)), Q.sum(SC.take(U32, leaves(r), k)), prefix_ok(p, r, k, hk_fix(i, p, hi, le), M.dec(p, k), {==}, pf_r(p, s, l, r, pf), g_r(s, l, r, g))) : {U32.add(s, _) == Q.sum(SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i)) : U32}
      %Equal.sym(U32, s, Q.sum(leaves(l)), g_s(s, l, r, g)) : {U32.add(_, Q.sum(SC.take(U32, leaves(r), k))) == Q.sum(SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i)) : U32}
      %Equal.sym(List<&2, U32>, SC.take(U32, SC.append(U32, leaves(l), leaves(r)), i), SC.append(U32, leaves(l), SC.take(U32, leaves(r), Nat.sub(i, SC.length(U32, leaves(l))))), LL.sc_take_append_right(U32, leaves(l), leaves(r), i, hr)) : {U32.add(Q.sum(leaves(l)), Q.sum(SC.take(U32, leaves(r), k))) == Q.sum(_) : U32}
      %left_len(p, l, pl) : {U32.add(Q.sum(leaves(l)), Q.sum(SC.take(U32, leaves(r), k))) == Q.sum(SC.append(U32, leaves(l), SC.take(U32, leaves(r), Nat.sub(i, _)))) : U32}
      Equal.sym(U32, Q.sum(SC.append(U32, leaves(l), SC.take(U32, leaves(r), k))), U32.add(Q.sum(leaves(l)), Q.sum(SC.take(U32, leaves(r), k))), QS.sum_append(leaves(l), SC.take(U32, leaves(r), k)))

# i <= 2^(p+1) with 2^p <= i gives i - 2^p <= 2^p
# ---- zero trees ----

def zeros_perfect(+d: Nat) -> {perfect(d, M.zeros(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      L.and_intro(perfect(p, M.zeros(p)), perfect(p, M.zeros(p)), zeros_perfect(p), zeros_perfect(p))

def zeros_leaves(+d: Nat) -> {leaves(M.zeros(d)) == Q.zeros(SC.pow2(d)) : List<&2, U32>}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(List<&2, U32>, leaves(M.zeros(p)), Q.zeros(SC.pow2(p)), zeros_leaves(p)) : {SC.append(U32, _, _) == Q.zeros(Nat.double(SC.pow2(p))) : List<&2, U32>}
      %Equal.sym(Nat, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), SC.pow2(p)), NA.double_self(SC.pow2(p))) : {SC.append(U32, Q.zeros(SC.pow2(p)), Q.zeros(SC.pow2(p))) == Q.zeros(_) : List<&2, U32>}
      LL.replicate_add(U32, SC.pow2(p), SC.pow2(p), 0)

def zeros_good(+d: Nat) -> {goodf(M.zeros(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      g_mk(0, M.zeros(p), M.zeros(p),
        %Equal.sym(List<&2, U32>, leaves(M.zeros(p)), Q.zeros(SC.pow2(p)), zeros_leaves(p)) : {0 == Q.sum(_) : U32}
        Equal.sym(U32, Q.sum(Q.zeros(SC.pow2(p))), 0, QS.sum_zeros(SC.pow2(p))),
        zeros_good(p), zeros_good(p))
