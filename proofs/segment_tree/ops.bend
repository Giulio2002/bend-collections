import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/u32alg.bend as UA
import ../lib/u32seq.bend as QS
import ../lib/vec.bend as VL
import ../../reference/lru/proofs/nat_algebra.bend as NA
import ../../spec/common.bend as SC
import ../../spec/u32seq.bend as Q
import ./node.bend as T
import ../../src/internal/vec.bend as V
import ./model.bend as M

# Tree walks of src/segment_tree against vals: with the tags of the
# ancestors summed into a, the subtree's true values are add_each(vals t, a).

# The true values of a node split into its children's, carrying the tag.
# `hk_fix` used to be borrowed from proofs/fenwick_tree/tree.bend; that module
# now states its arithmetic over spec/common's pow2 (the Fenwick tree moved to
# a flat Base.Array), so the V.pow2 flavour segment_tree still needs lives
# here until segment_tree is migrated too.
def dbl_succ(+m: Nat) -> {1n+Nat.double(m) == Nat.add(m, 1n+m) : Nat}:
  %Equal.sym(Nat, Nat.add(m, 1n+m), 1n+Nat.add(m, m), N.add_succ(m, m)) : {1n+Nat.double(m) == _ : Nat}
  N.succ_cong(Nat.double(m), Nat.add(m, m), NA.double_self(m))

def hk_fix(+i: Nat, +p: Nat, +hi: {Nat.is_le(i, V.pow2(1n+p)) == True{} : Bool}, +le: {Nat.is_le(V.pow2(p), i) == True{} : Bool}) -> {Nat.is_le(Nat.sub(i, V.pow2(p)), V.pow2(p)) == True{} : Bool}:
  N.lt_succ_le(Nat.sub(i, V.pow2(p)), V.pow2(p), N.sub_lt(i, V.pow2(p), 1n+V.pow2(p), le, L.subst(Nat, q => {Nat.is_lt(i, q) == True{} : Bool}, 1n+Nat.double(V.pow2(p)), Nat.add(V.pow2(p), 1n+V.pow2(p)), dbl_succ(V.pow2(p)), N.le_lt_succ(i, Nat.double(V.pow2(p)), hi))))

def split_each(+s: U32, +z: U32, +l: T.Node, +r: T.Node, +a: U32) -> {Q.add_each(M.vals(T.SNode{s, z, l, r}), a) == SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Q.add_each(Q.add_each(SC.append(U32, M.vals(l), M.vals(r)), z), a), Q.add_each(SC.append(U32, M.vals(l), M.vals(r)), U32.add(z, a)), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))),
    M.each_each(SC.append(U32, M.vals(l), M.vals(r)), z, a),
    Equal.trans(List<&2, U32>, Q.add_each(SC.append(U32, M.vals(l), M.vals(r)), U32.add(z, a)), Q.add_each(SC.append(U32, M.vals(l), M.vals(r)), U32.add(a, z)), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))),
      Equal.cong(U32, List<&2, U32>, q => Q.add_each(SC.append(U32, M.vals(l), M.vals(r)), q), U32.add(z, a), U32.add(a, z), U32.add_comm(z, a)),
      M.each_append(M.vals(l), M.vals(r), U32.add(a, z))))

def len_each(+p: Nat, +t: T.Node, +a: U32, +pf: {M.perfect(p, t) == True{} : Bool}) -> {V.pow2(p) == SC.length(U32, Q.add_each(M.vals(t), a)) : Nat}:
  Equal.sym(Nat, SC.length(U32, Q.add_each(M.vals(t), a)), V.pow2(p), Equal.trans(Nat, SC.length(U32, Q.add_each(M.vals(t), a)), SC.length(U32, M.vals(t)), V.pow2(p), M.each_length(M.vals(t), a), M.vals_length(p, t, pf)))

# ---- get ----

def get_ok(+d: Nat, +t: T.Node, +i: Nat, +a: U32, +hi: {Nat.is_lt(i, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, i) == b : Bool}, +pf: {M.perfect(d, t) == True{} : Bool}) -> {Some{T.get_go(d, t, i, a, b)} == SC.nth(U32, Q.add_each(M.vals(t), a), i) : Maybe<&2, U32>}:
  match d t b:
    case 0n T.SLeaf{x} _:
      match i:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Some{U32.add(x, a)} == None{} : Maybe<&2, U32>}, N.lt_zero_absurd(q, hi))
    case 0n T.SNode{s, z, l, r} _:
      Empty.absurd({Some{0} == SC.nth(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i) : Maybe<&2, U32>}, L.false_true(pf))
    case 1n+p T.SLeaf{x} _:
      Empty.absurd({Some{0} == SC.nth(U32, Q.add_each(Con{x, Nil{}}, a), i) : Maybe<&2, U32>}, L.false_true(pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, V.pow2(p), SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z))), len_each(p, l, U32.add(a, z), pl), eb)
      Equal.trans(Maybe<&2, U32>, Some{T.get_go(p, l, i, U32.add(a, z), V.dec(p, i))}, SC.nth(U32, Q.add_each(M.vals(l), U32.add(a, z)), i), SC.nth(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i),
        get_ok(p, l, i, U32.add(a, z), eb, V.dec(p, i), {==}, pl),
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), split_each(s, z, l, r, a)) : {SC.nth(U32, Q.add_each(M.vals(l), U32.add(a, z)), i) == SC.nth(U32, _, i) : Maybe<&2, U32>}
        Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), i), SC.nth(U32, Q.add_each(M.vals(l), U32.add(a, z)), i), LL.nth_append_left(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z)), i, hl)))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +k = Nat.sub(i, V.pow2(p))
      +le = N.not_lt_le(i, V.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, V.pow2(p), SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z))), len_each(p, l, U32.add(a, z), pl), le)
      Equal.trans(Maybe<&2, U32>, Some{T.get_go(p, r, k, U32.add(a, z), V.dec(p, k))}, SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), k), SC.nth(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i),
        get_ok(p, r, k, U32.add(a, z), VL.upper_lt(i, p, hi, le), V.dec(p, k), {==}, M.pf_r(p, s, z, l, r, pf)),
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), split_each(s, z, l, r, a)) : {SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), k) == SC.nth(U32, _, i) : Maybe<&2, U32>}
        %Equal.sym(Maybe<&2, U32>, SC.nth(U32, SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), i), SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), Nat.sub(i, SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z))))), LL.nth_append_right(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z)), i, hr)) : {SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), k) == _ : Maybe<&2, U32>}
        %len_each(p, l, U32.add(a, z), pl) : {SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), k) == SC.nth(U32, Q.add_each(M.vals(r), U32.add(a, z)), Nat.sub(i, _)) : Maybe<&2, U32>}
        {==})

# ---- set ----

def set_perfect(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +a: U32, +b: Bool, +pf: {M.perfect(d, t) == True{} : Bool}) -> {M.perfect(d, T.set_go(d, t, i, v, a, b)) == True{} : Bool}:
  match d t b:
    case 0n T.SLeaf{x} _:
      {==}
    case 0n T.SNode{s, z, l, r} _:
      pf
    case 1n+p T.SLeaf{x} _:
      pf
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      M.node_perfect(p, T.set_go(p, l, i, v, U32.add(a, z), V.dec(p, i)), r, z, set_perfect(p, l, i, v, U32.add(a, z), V.dec(p, i), M.pf_l(p, s, z, l, r, pf)), M.pf_r(p, s, z, l, r, pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      M.node_perfect(p, l, T.set_go(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p)))), z, M.pf_l(p, s, z, l, r, pf), set_perfect(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf)))

def set_good(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +a: U32, +b: Bool, +pf: {M.perfect(d, t) == True{} : Bool}, +g: {M.goods(t) == True{} : Bool}) -> {M.goods(T.set_go(d, t, i, v, a, b)) == True{} : Bool}:
  match d t b:
    case 0n T.SLeaf{x} _:
      {==}
    case 0n T.SNode{s, z, l, r} _:
      g
    case 1n+p T.SLeaf{x} _:
      g
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      M.node_good(p, T.set_go(p, l, i, v, U32.add(a, z), V.dec(p, i)), r, z, set_perfect(p, l, i, v, U32.add(a, z), V.dec(p, i), M.pf_l(p, s, z, l, r, pf)), M.pf_r(p, s, z, l, r, pf), set_good(p, l, i, v, U32.add(a, z), V.dec(p, i), M.pf_l(p, s, z, l, r, pf), M.g_l(s, z, l, r, g)), M.g_r(s, z, l, r, g))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      M.node_good(p, l, T.set_go(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p)))), z, M.pf_l(p, s, z, l, r, pf), set_perfect(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf)), M.g_l(s, z, l, r, g), set_good(p, r, Nat.sub(i, V.pow2(p)), v, U32.add(a, z), V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf), M.g_r(s, z, l, r, g)))

def set_ok(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +a: U32, +hi: {Nat.is_lt(i, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, i) == b : Bool}, +pf: {M.perfect(d, t) == True{} : Bool}) -> {Q.add_each(M.vals(T.set_go(d, t, i, v, a, b)), a) == SC.update(U32, Q.add_each(M.vals(t), a), i, v) : List<&2, U32>}:
  match d t b:
    case 0n T.SLeaf{x} _:
      match i:
        case 0n:
          Equal.cong(U32, List<&2, U32>, q => Con{q, Nil{}}, U32.add(U32.sub(v, a), a), v, UA.sub_add(v, a))
        case 1n+q:
          Empty.absurd({Con{U32.add(U32.sub(v, a), a), Nil{}} == Con{U32.add(x, a), Nil{}} : List<&2, U32>}, N.lt_zero_absurd(q, hi))
    case 0n T.SNode{s, z, l, r} _:
      Empty.absurd({Q.add_each(M.vals(T.SNode{s, z, l, r}), a) == SC.update(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+p T.SLeaf{x} _:
      Empty.absurd({Q.add_each(Con{x, Nil{}}, a) == SC.update(U32, Q.add_each(Con{x, Nil{}}, a), i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +l2 = T.set_go(p, l, i, v, U32.add(a, z), V.dec(p, i))
      +hl = L.subst(Nat, k => {Nat.is_lt(i, k) == True{} : Bool}, V.pow2(p), SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z))), len_each(p, l, U32.add(a, z), pl), eb)
      Equal.trans(List<&2, U32>, Q.add_each(M.vals(T.node(p, l2, r, z)), a), SC.append(U32, SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), Q.add_each(M.vals(r), U32.add(a, z))), SC.update(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i, v),
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.node(p, l2, r, z)), a), SC.append(U32, Q.add_each(M.vals(l2), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), split_each(U32.add(U32.add(T.total(l2), T.total(r)), U32.shln(z, 1n+p)), z, l2, r, a)) : {_ == SC.append(U32, SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), Q.add_each(M.vals(r), U32.add(a, z))) : List<&2, U32>}
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(l2), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), set_ok(p, l, i, v, U32.add(a, z), eb, V.dec(p, i), {==}, pl)) : {SC.append(U32, _, Q.add_each(M.vals(r), U32.add(a, z))) == SC.append(U32, SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), Q.add_each(M.vals(r), U32.add(a, z))) : List<&2, U32>}
        {==},
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), split_each(s, z, l, r, a)) : {SC.append(U32, SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), Q.add_each(M.vals(r), U32.add(a, z))) == SC.update(U32, _, i, v) : List<&2, U32>}
        Equal.sym(List<&2, U32>, SC.update(U32, SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), i, v), SC.append(U32, SC.update(U32, Q.add_each(M.vals(l), U32.add(a, z)), i, v), Q.add_each(M.vals(r), U32.add(a, z))), LL.update_append_left(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z)), i, v, hl)))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +k = Nat.sub(i, V.pow2(p))
      +le = N.not_lt_le(i, V.pow2(p), eb)
      +r2 = T.set_go(p, r, k, v, U32.add(a, z), V.dec(p, k))
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, V.pow2(p), SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z))), len_each(p, l, U32.add(a, z), pl), le)
      Equal.trans(List<&2, U32>, Q.add_each(M.vals(T.node(p, l, r2, z)), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)), SC.update(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i, v),
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.node(p, l, r2, z)), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r2), U32.add(a, z))), split_each(U32.add(U32.add(T.total(l), T.total(r2)), U32.shln(z, 1n+p)), z, l, r2, a)) : {_ == SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)) : List<&2, U32>}
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(r2), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v), set_ok(p, r, k, v, U32.add(a, z), VL.upper_lt(i, p, hi, le), V.dec(p, k), {==}, M.pf_r(p, s, z, l, r, pf))) : {SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), _) == SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)) : List<&2, U32>}
        {==},
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), split_each(s, z, l, r, a)) : {SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)) == SC.update(U32, _, i, v) : List<&2, U32>}
        %Equal.sym(List<&2, U32>, SC.update(U32, SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z))), i, v), SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), Nat.sub(i, SC.length(U32, Q.add_each(M.vals(l), U32.add(a, z)))), v)), LL.update_append_right(U32, Q.add_each(M.vals(l), U32.add(a, z)), Q.add_each(M.vals(r), U32.add(a, z)), i, v, hr)) : {SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)) == _ : List<&2, U32>}
        %len_each(p, l, U32.add(a, z), pl) : {SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), k, v)) == SC.append(U32, Q.add_each(M.vals(l), U32.add(a, z)), SC.update(U32, Q.add_each(M.vals(r), U32.add(a, z)), Nat.sub(i, _), v)) : List<&2, U32>}
        {==})

# ---- prefix sums ----

def leaf_pre(+y: U32, +i: Nat, +hi: {Nat.is_le(i, 1n) == True{} : Bool}) -> {T.leaf_prefix(y, i) == Q.sum(SC.take(U32, Con{y, Nil{}}, i)) : U32}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      Equal.sym(U32, U32.add(y, Q.sum(SC.take(U32, Nil{}, j))), y, UA.add_zero(y))

def prefix_ok(+d: Nat, +t: T.Node, +i: Nat, +a: U32, +hi: {Nat.is_le(i, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, i) == b : Bool}, +pf: {M.perfect(d, t) == True{} : Bool}, +g: {M.goods(t) == True{} : Bool}) -> {T.prefix_go(d, t, i, a, b) == Q.sum(SC.take(U32, Q.add_each(M.vals(t), a), i)) : U32}:
  match d t b:
    case 0n T.SLeaf{x} _:
      leaf_pre(U32.add(x, a), i, hi)
    case 0n T.SNode{s, z, l, r} _:
      Empty.absurd({0 == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}, L.false_true(pf))
    case 1n+p T.SLeaf{x} _:
      Empty.absurd({0 == Q.sum(SC.take(U32, Q.add_each(Con{x, Nil{}}, a), i)) : U32}, L.false_true(pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +EL = Q.add_each(M.vals(l), U32.add(a, z))
      +ER = Q.add_each(M.vals(r), U32.add(a, z))
      +hl = L.subst(Nat, k => {Nat.is_le(i, k) == True{} : Bool}, V.pow2(p), SC.length(U32, EL), len_each(p, l, U32.add(a, z), pl), N.lt_le(i, V.pow2(p), eb))
      Equal.trans(U32, T.prefix_go(p, l, i, U32.add(a, z), V.dec(p, i)), Q.sum(SC.take(U32, EL, i)), Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)),
        prefix_ok(p, l, i, U32.add(a, z), N.lt_le(i, V.pow2(p), eb), V.dec(p, i), {==}, pl, M.g_l(s, z, l, r, g)),
        %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, EL, ER), split_each(s, z, l, r, a)) : {Q.sum(SC.take(U32, EL, i)) == Q.sum(SC.take(U32, _, i)) : U32}
        %Equal.sym(List<&2, U32>, SC.take(U32, SC.append(U32, EL, ER), i), SC.take(U32, EL, i), LL.sc_take_append_left(U32, EL, ER, i, hl)) : {Q.sum(SC.take(U32, EL, i)) == Q.sum(_) : U32}
        {==})
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +a2 = U32.add(a, z)
      +EL = Q.add_each(M.vals(l), U32.add(a, z))
      +ER = Q.add_each(M.vals(r), U32.add(a, z))
      +k = Nat.sub(i, V.pow2(p))
      +le = N.not_lt_le(i, V.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, V.pow2(p), SC.length(U32, EL), len_each(p, l, U32.add(a, z), pl), le)
      %Equal.sym(U32, T.prefix_go(p, r, k, a2, V.dec(p, k)), Q.sum(SC.take(U32, ER, k)), prefix_ok(p, r, k, a2, hk_fix(i, p, hi, le), V.dec(p, k), {==}, M.pf_r(p, s, z, l, r, pf), M.g_r(s, z, l, r, g))) : {U32.add(U32.add(T.total(l), U32.shln(a2, p)), _) == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}
      %Equal.sym(U32, T.total(l), Q.sum(M.vals(l)), M.total_eq(l, M.g_l(s, z, l, r, g))) : {U32.add(U32.add(_, U32.shln(a2, p)), Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}
      %M.times_pow(a2, p) : {U32.add(U32.add(Q.sum(M.vals(l)), _), Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}
      %M.vals_length(p, l, pl) : {U32.add(U32.add(Q.sum(M.vals(l)), M.times(a2, _)), Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}
      %M.sum_each(M.vals(l), a2) : {U32.add(_, Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.take(U32, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), i)) : U32}
      %Equal.sym(List<&2, U32>, Q.add_each(M.vals(T.SNode{s, z, l, r}), a), SC.append(U32, EL, ER), split_each(s, z, l, r, a)) : {U32.add(Q.sum(EL), Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.take(U32, _, i)) : U32}
      %Equal.sym(List<&2, U32>, SC.take(U32, SC.append(U32, EL, ER), i), SC.append(U32, EL, SC.take(U32, ER, Nat.sub(i, SC.length(U32, EL)))), LL.sc_take_append_right(U32, EL, ER, i, hr)) : {U32.add(Q.sum(EL), Q.sum(SC.take(U32, ER, k))) == Q.sum(_) : U32}
      %len_each(p, l, U32.add(a, z), pl) : {U32.add(Q.sum(EL), Q.sum(SC.take(U32, ER, k))) == Q.sum(SC.append(U32, EL, SC.take(U32, ER, Nat.sub(i, _)))) : U32}
      Equal.sym(U32, Q.sum(SC.append(U32, EL, SC.take(U32, ER, k))), U32.add(Q.sum(EL), Q.sum(SC.take(U32, ER, k))), QS.sum_append(EL, SC.take(U32, ER, k)))

# ---- adding to a prefix ----

def sub_eq_zero(+i: Nat, +m: Nat, +h: {Nat.is_le(i, m) == True{} : Bool}) -> {Nat.sub(i, m) == 0n : Nat}:
  match i m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+j 0n:
      Empty.absurd({1n+j == 0n : Nat}, L.false_true(h))
    case 1n+j 1n+q:
      sub_eq_zero(j, q, h)

def leaf_pv(+x: U32, +i: Nat, +v: U32) -> {M.vals(T.leaf_padd(x, i, v)) == M.addfirst(Con{x, Nil{}}, i, v) : List<&2, U32>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

def leaf_pp(+x: U32, +i: Nat, +v: U32) -> {M.perfect(0n, T.leaf_padd(x, i, v)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

def leaf_pg(+x: U32, +i: Nat, +v: U32) -> {M.goods(T.leaf_padd(x, i, v)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      {==}

def padd_perfect(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +b: Bool, +pf: {M.perfect(d, t) == True{} : Bool}) -> {M.perfect(d, T.padd_go(d, t, i, v, b)) == True{} : Bool}:
  match d t b:
    case 0n T.SLeaf{x} _:
      leaf_pp(x, i, v)
    case 0n T.SNode{s, z, l, r} _:
      pf
    case 1n+p T.SLeaf{x} _:
      pf
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      M.node_perfect(p, T.padd_go(p, l, i, v, V.dec(p, i)), r, z, padd_perfect(p, l, i, v, V.dec(p, i), M.pf_l(p, s, z, l, r, pf)), M.pf_r(p, s, z, l, r, pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      M.node_perfect(p, T.tagall(p, l, v), T.padd_go(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p)))), z, M.tag_perfect(p, l, v, M.pf_l(p, s, z, l, r, pf)), padd_perfect(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf)))

def padd_good(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +b: Bool, +pf: {M.perfect(d, t) == True{} : Bool}, +g: {M.goods(t) == True{} : Bool}) -> {M.goods(T.padd_go(d, t, i, v, b)) == True{} : Bool}:
  match d t b:
    case 0n T.SLeaf{x} _:
      leaf_pg(x, i, v)
    case 0n T.SNode{s, z, l, r} _:
      g
    case 1n+p T.SLeaf{x} _:
      g
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      M.node_good(p, T.padd_go(p, l, i, v, V.dec(p, i)), r, z, padd_perfect(p, l, i, v, V.dec(p, i), M.pf_l(p, s, z, l, r, pf)), M.pf_r(p, s, z, l, r, pf), padd_good(p, l, i, v, V.dec(p, i), M.pf_l(p, s, z, l, r, pf), M.g_l(s, z, l, r, g)), M.g_r(s, z, l, r, g))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      M.node_good(p, T.tagall(p, l, v), T.padd_go(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p)))), z, M.tag_perfect(p, l, v, M.pf_l(p, s, z, l, r, pf)), padd_perfect(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf)), M.tag_good(p, l, v, M.pf_l(p, s, z, l, r, pf), M.g_l(s, z, l, r, g)), padd_good(p, r, Nat.sub(i, V.pow2(p)), v, V.dec(p, Nat.sub(i, V.pow2(p))), M.pf_r(p, s, z, l, r, pf), M.g_r(s, z, l, r, g)))

def padd_vals(+d: Nat, +t: T.Node, +i: Nat, +v: U32, +hi: {Nat.is_le(i, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, i) == b : Bool}, +pf: {M.perfect(d, t) == True{} : Bool}) -> {M.vals(T.padd_go(d, t, i, v, b)) == M.addfirst(M.vals(t), i, v) : List<&2, U32>}:
  match d t b:
    case 0n T.SLeaf{x} _:
      leaf_pv(x, i, v)
    case 0n T.SNode{s, z, l, r} _:
      Empty.absurd({M.vals(T.SNode{s, z, l, r}) == M.addfirst(M.vals(T.SNode{s, z, l, r}), i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+p T.SLeaf{x} _:
      Empty.absurd({Con{x, Nil{}} == M.addfirst(Con{x, Nil{}}, i, v) : List<&2, U32>}, L.false_true(pf))
    case 1n+ +p T.SNode{+s, +z, +l, +r} True{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +Lv = M.vals(l)
      +Rv = M.vals(r)
      +l2 = T.padd_go(p, l, i, v, V.dec(p, i))
      +hl = L.subst(Nat, q => {Nat.is_le(i, q) == True{} : Bool}, V.pow2(p), SC.length(U32, Lv), Equal.sym(Nat, SC.length(U32, Lv), V.pow2(p), M.vals_length(p, l, pl)), N.lt_le(i, V.pow2(p), eb))
      +mid = Equal.trans(List<&2, U32>, SC.append(U32, M.addfirst(Lv, i, v), Rv), SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, SC.length(U32, Lv)), v)), M.addfirst(SC.append(U32, Lv, Rv), i, v),
        %Equal.sym(Nat, Nat.sub(i, SC.length(U32, Lv)), 0n, sub_eq_zero(i, SC.length(U32, Lv), hl)) : {SC.append(U32, M.addfirst(Lv, i, v), Rv) == SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, _, v)) : List<&2, U32>}
        %Equal.sym(List<&2, U32>, M.addfirst(Rv, 0n, v), Rv, M.addfirst_zero(Rv, v)) : {SC.append(U32, M.addfirst(Lv, i, v), Rv) == SC.append(U32, M.addfirst(Lv, i, v), _) : List<&2, U32>}
        {==},
        Equal.sym(List<&2, U32>, M.addfirst(SC.append(U32, Lv, Rv), i, v), SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, SC.length(U32, Lv)), v)), M.addfirst_append(Lv, Rv, i, v)))
      Equal.trans(List<&2, U32>, Q.add_each(SC.append(U32, M.vals(l2), Rv), z), Q.add_each(M.addfirst(SC.append(U32, Lv, Rv), i, v), z), M.addfirst(Q.add_each(SC.append(U32, Lv, Rv), z), i, v),
        %Equal.sym(List<&2, U32>, M.vals(l2), M.addfirst(Lv, i, v), padd_vals(p, l, i, v, N.lt_le(i, V.pow2(p), eb), V.dec(p, i), {==}, pl)) : {Q.add_each(SC.append(U32, _, Rv), z) == Q.add_each(M.addfirst(SC.append(U32, Lv, Rv), i, v), z) : List<&2, U32>}
        Equal.cong(List<&2, U32>, List<&2, U32>, q => Q.add_each(q, z), SC.append(U32, M.addfirst(Lv, i, v), Rv), M.addfirst(SC.append(U32, Lv, Rv), i, v), mid),
        M.each_addfirst(SC.append(U32, Lv, Rv), i, v, z))
    case 1n+ +p T.SNode{+s, +z, +l, +r} False{}:
      +pl = M.pf_l(p, s, z, l, r, pf)
      +Lv = M.vals(l)
      +Rv = M.vals(r)
      +k = Nat.sub(i, V.pow2(p))
      +le = N.not_lt_le(i, V.pow2(p), eb)
      +r2 = T.padd_go(p, r, k, v, V.dec(p, k))
      +hr = L.subst(Nat, q => {Nat.is_le(q, i) == True{} : Bool}, V.pow2(p), SC.length(U32, Lv), Equal.sym(Nat, SC.length(U32, Lv), V.pow2(p), M.vals_length(p, l, pl)), le)
      +mid = Equal.trans(List<&2, U32>, SC.append(U32, Q.add_each(Lv, v), M.addfirst(Rv, k, v)), SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, SC.length(U32, Lv)), v)), M.addfirst(SC.append(U32, Lv, Rv), i, v),
        %M.addfirst_all(Lv, i, v, hr) : {SC.append(U32, _, M.addfirst(Rv, k, v)) == SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, SC.length(U32, Lv)), v)) : List<&2, U32>}
        %Equal.sym(Nat, SC.length(U32, Lv), V.pow2(p), M.vals_length(p, l, pl)) : {SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, k, v)) == SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, _), v)) : List<&2, U32>}
        {==},
        Equal.sym(List<&2, U32>, M.addfirst(SC.append(U32, Lv, Rv), i, v), SC.append(U32, M.addfirst(Lv, i, v), M.addfirst(Rv, Nat.sub(i, SC.length(U32, Lv)), v)), M.addfirst_append(Lv, Rv, i, v)))
      Equal.trans(List<&2, U32>, Q.add_each(SC.append(U32, M.vals(T.tagall(p, l, v)), M.vals(r2)), z), Q.add_each(M.addfirst(SC.append(U32, Lv, Rv), i, v), z), M.addfirst(Q.add_each(SC.append(U32, Lv, Rv), z), i, v),
        %Equal.sym(List<&2, U32>, M.vals(T.tagall(p, l, v)), Q.add_each(Lv, v), M.tag_vals(p, l, v, pl)) : {Q.add_each(SC.append(U32, _, M.vals(r2)), z) == Q.add_each(M.addfirst(SC.append(U32, Lv, Rv), i, v), z) : List<&2, U32>}
        %Equal.sym(List<&2, U32>, M.vals(r2), M.addfirst(Rv, k, v), padd_vals(p, r, k, v, hk_fix(i, p, hi, le), V.dec(p, k), {==}, M.pf_r(p, s, z, l, r, pf))) : {Q.add_each(SC.append(U32, Q.add_each(Lv, v), _), z) == Q.add_each(M.addfirst(SC.append(U32, Lv, Rv), i, v), z) : List<&2, U32>}
        Equal.cong(List<&2, U32>, List<&2, U32>, q => Q.add_each(q, z), SC.append(U32, Q.add_each(Lv, v), M.addfirst(Rv, k, v)), M.addfirst(SC.append(U32, Lv, Rv), i, v), mid),
        M.each_addfirst(SC.append(U32, Lv, Rv), i, v, z))
