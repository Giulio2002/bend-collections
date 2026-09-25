import Base
import ./logic.bend as L
import ./nat.bend as N
import ./u32.bend as U
import ./list.bend as LL
import ../../spec/lib/common.bend as SC
import ./lemmas/proofs/nat_algebra.bend as NA

# Functional correctness of the installed Base.Array get/swap/set/new
# algorithms (base.bend 2142-2272), proved against their actual definitions.
#
# Arrays are linear, so every statement is about thaw(t): the array built from a
# Data mirror tree t of identical shape. This keeps arrays out of live proof
# terms. The meaning of a tree is its in-order slot list; indices are U32 below
# the Base size 2^d (d < 32), so Base index masking is the identity.

type Tree<-T: Data> is Data:
  TLeaf{value: T}
  TNode{lo: Tree<T>, hi: Tree<T>}

def thaw(-T: Data, t: Tree<T>) -> Array<T>:
  match t:
    case TLeaf{x}:
      ALeaf{x}
    case TNode{l, r}:
      ANode{thaw(T, l), thaw(T, r)}

def freeze(-T: Data, a: Array<T>) -> Tree<T>:
  match a:
    case ALeaf{+x}:
      TLeaf{x}
    case ANode{xs, ys}:
      TNode{freeze(T, xs), freeze(T, ys)}

def slots(-T: Data, t: Tree<T>) -> List<&2, T>:
  match t:
    case TLeaf{x}:
      Con{x, Nil{}}
    case TNode{l, r}:
      SC.append(T, slots(T, l), slots(T, r))

def perfect(-T: Data, +d: Nat, t: Tree<T>) -> Bool:
  match d t:
    case 0n TLeaf{x}:
      True{}
    case 0n TNode{l, r}:
      False{}
    case 1n+p TLeaf{x}:
      False{}
    case 1n+p TNode{l, r}:
      Bool.and(perfect(T, p, l), perfect(T, p, r))

# Mirror of an update at a Nat index (proof-level description of the new tree).
# `left` is this node's branch decision (see ndec); passing it as a parameter
# avoids matching on a computed value.
def ndec(d: Nat, +j: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+q:
      Nat.is_lt(j, SC.pow2(q))

def tupd(-T: Data, d: Nat, t: Tree<T>, +j: Nat, +v: T, left: Bool) -> Tree<T>:
  match d t left:
    case 0n TLeaf{x} _:
      TLeaf{v}
    case 0n TNode{l, r} _:
      TNode{l, r}
    case 1n+p TLeaf{x} _:
      TLeaf{x}
    case 1n+ +p TNode{l, r} True{}:
      TNode{tupd(T, p, l, j, v, ndec(p, j)), r}
    case 1n+ +p TNode{l, r} False{}:
      TNode{l, tupd(T, p, r, Nat.sub(j, SC.pow2(p)), v, ndec(p, Nat.sub(j, SC.pow2(p))))}

def upd(-T: Data, +d: Nat, t: Tree<T>, +j: Nat, +v: T) -> Tree<T>:
  tupd(T, d, t, j, v, ndec(d, j))

def trep(-T: Data, +d: Nat, +v: T) -> Tree<T>:
  match d:
    case 0n:
      TLeaf{v}
    case 1n+p:
      TNode{trep(T, p, v), trep(T, p, v)}

# ---- pure tree facts ----

def freeze_thaw(-T: Data, +t: Tree<T>) -> {freeze(T, thaw(T, t)) == t : Tree<T>}:
  match t:
    case TLeaf{x}:
      {==}
    case TNode{+l, +r}:
      %Equal.sym(Tree<T>, freeze(T, thaw(T, l)), l, freeze_thaw(T, l)) : {TNode{_, freeze(T, thaw(T, r))} == TNode{l, r} : Tree<T>}
      %Equal.sym(Tree<T>, freeze(T, thaw(T, r)), r, freeze_thaw(T, r)) : {TNode{l, _} == TNode{l, r} : Tree<T>}
      {==}

def pf_left(-T: Data, +p: Nat, +l: Tree<T>, +r: Tree<T>, +pf: {perfect(T, 1n+p, TNode{l, r}) == True{} : Bool}) -> {perfect(T, p, l) == True{} : Bool}:
  L.and_left(perfect(T, p, l), perfect(T, p, r), pf)

def pf_right(-T: Data, +p: Nat, +l: Tree<T>, +r: Tree<T>, +pf: {perfect(T, 1n+p, TNode{l, r}) == True{} : Bool}) -> {perfect(T, p, r) == True{} : Bool}:
  L.and_right(perfect(T, p, l), perfect(T, p, r), pf)

def slots_length(-T: Data, +d: Nat, +t: Tree<T>, +pf: {perfect(T, d, t) == True{} : Bool}) -> {SC.length(T, slots(T, t)) == SC.pow2(d) : Nat}:
  match d t:
    case 0n TLeaf{x}:
      {==}
    case 0n TNode{l, r}:
      Empty.absurd({SC.length(T, slots(T, TNode{l, r})) == 1n : Nat}, L.false_true(pf))
    case 1n+p TLeaf{x}:
      Empty.absurd({1n == Nat.double(SC.pow2(p)) : Nat}, L.false_true(pf))
    case 1n+ +p TNode{+l, +r}:
      %Equal.sym(Nat, SC.length(T, SC.append(T, slots(T, l), slots(T, r))), Nat.add(SC.length(T, slots(T, l)), SC.length(T, slots(T, r))), LL.length_append(T, slots(T, l), slots(T, r))) : {_ == Nat.double(SC.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(T, slots(T, l)), SC.pow2(p), slots_length(T, p, l, pf_left(T, p, l, r, pf))) : {Nat.add(_, SC.length(T, slots(T, r))) == Nat.double(SC.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(T, slots(T, r)), SC.pow2(p), slots_length(T, p, r, pf_right(T, p, l, r, pf))) : {Nat.add(SC.pow2(p), _) == Nat.double(SC.pow2(p)) : Nat}
      Equal.sym(Nat, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), SC.pow2(p)), NA.double_self(SC.pow2(p)))

def trep_perfect(-T: Data, +d: Nat, +v: T) -> {perfect(T, d, trep(T, d, v)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      L.and_intro(perfect(T, p, trep(T, p, v)), perfect(T, p, trep(T, p, v)), trep_perfect(T, p, v), trep_perfect(T, p, v))

def trep_slots(-T: Data, +d: Nat, +v: T) -> {slots(T, trep(T, d, v)) == SC.replicate(T, SC.pow2(d), v) : List<&2, T>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, T>, slots(T, trep(T, p, v)), SC.replicate(T, SC.pow2(p), v), trep_slots(T, p, v)) : {SC.append(T, _, _) == SC.replicate(T, Nat.double(SC.pow2(p)), v) : List<&2, T>}
      %Equal.sym(Nat, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), SC.pow2(p)), NA.double_self(SC.pow2(p))) : {SC.append(T, SC.replicate(T, SC.pow2(p), v), SC.replicate(T, SC.pow2(p), v)) == SC.replicate(T, _, v) : List<&2, T>}
      LL.replicate_add(T, SC.pow2(p), SC.pow2(p), v)

# ---- index helpers ----

def leaf_update(-T: Data, +x: T, +v: T, +j: Nat, +hj: {Nat.is_lt(j, 1n) == True{} : Bool}) -> {Con{v, Nil{}} == SC.update(T, Con{x, Nil{}}, j, v) : List<&2, T>}:
  match j:
    case 0n:
      {==}
    case 1n+q:
      Empty.absurd({Con{v, Nil{}} == Con{x, Nil{}} : List<&2, T>}, N.lt_zero_absurd(q, hj))

def leaf_value(-T: Data, +y: T, +j: Nat, +x: T, +hj: {Nat.is_lt(j, 1n) == True{} : Bool}, +hx: {SC.nth(T, Con{y, Nil{}}, j) == Some{x} : Maybe<&2, T>}) -> {y == x : T}:
  match j:
    case 0n:
      L.some_inj(T, y, x, hx)
    case 1n+q:
      Empty.absurd({y == x : T}, N.lt_zero_absurd(q, hj))

def len_lt(-T: Data, +p: Nat, +l: Tree<T>, +j: Nat, +pl: {perfect(T, p, l) == True{} : Bool}, +h: {Nat.is_lt(j, SC.pow2(p)) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(T, slots(T, l))) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(T, slots(T, l)), SC.pow2(p), slots_length(T, p, l, pl)) : {Nat.is_lt(j, _) == True{} : Bool}
  h

def len_le(-T: Data, +p: Nat, +l: Tree<T>, +j: Nat, +pl: {perfect(T, p, l) == True{} : Bool}, +h: {Nat.is_le(SC.pow2(p), j) == True{} : Bool}) -> {Nat.is_le(SC.length(T, slots(T, l)), j) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(T, slots(T, l)), SC.pow2(p), slots_length(T, p, l, pl)) : {Nat.is_le(_, j) == True{} : Bool}
  h

def upper_lt(+j: Nat, +p: Nat, +hj: {Nat.is_lt(j, SC.pow2(1n+p)) == True{} : Bool}, +le: {Nat.is_le(SC.pow2(p), j) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(j, SC.pow2(p)), SC.pow2(p)) == True{} : Bool}:
  N.sub_lt(j, SC.pow2(p), SC.pow2(p), le, L.subst(Nat, n => {Nat.is_lt(j, n) == True{} : Bool}, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), SC.pow2(p)), NA.double_self(SC.pow2(p)), hj))

def right_update(-T: Data, +p: Nat, +l: Tree<T>, +r: Tree<T>, +j: Nat, +v: T, +pl: {perfect(T, p, l) == True{} : Bool}, +le: {Nat.is_le(SC.pow2(p), j) == True{} : Bool}) -> {SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v) == SC.append(T, slots(T, l), SC.update(T, slots(T, r), Nat.sub(j, SC.pow2(p)), v)) : List<&2, T>}:
  %slots_length(T, p, l, pl) : {SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v) == SC.append(T, slots(T, l), SC.update(T, slots(T, r), Nat.sub(j, _), v)) : List<&2, T>}
  LL.update_append_right(T, slots(T, l), slots(T, r), j, v, len_le(T, p, l, j, pl, le))

def right_nth(-T: Data, +p: Nat, +l: Tree<T>, +r: Tree<T>, +j: Nat, +pl: {perfect(T, p, l) == True{} : Bool}, +le: {Nat.is_le(SC.pow2(p), j) == True{} : Bool}) -> {SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j) == SC.nth(T, slots(T, r), Nat.sub(j, SC.pow2(p))) : Maybe<&2, T>}:
  %slots_length(T, p, l, pl) : {SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j) == SC.nth(T, slots(T, r), Nat.sub(j, _)) : Maybe<&2, T>}
  LL.nth_append_right(T, slots(T, l), slots(T, r), j, len_le(T, p, l, j, pl, le))

# ---- the Nat mirror of an update ----

def tupd_perfect(-T: Data, +d: Nat, +t: Tree<T>, +j: Nat, +v: T, +b: Bool, +pf: {perfect(T, d, t) == True{} : Bool}) -> {perfect(T, d, tupd(T, d, t, j, v, b)) == True{} : Bool}:
  match d t b:
    case 0n TLeaf{x} _:
      {==}
    case 0n TNode{l, r} _:
      pf
    case 1n+p TLeaf{x} _:
      pf
    case 1n+ +p TNode{+l, +r} True{}:
      L.and_intro(perfect(T, p, tupd(T, p, l, j, v, ndec(p, j))), perfect(T, p, r), tupd_perfect(T, p, l, j, v, ndec(p, j), pf_left(T, p, l, r, pf)), pf_right(T, p, l, r, pf))
    case 1n+ +p TNode{+l, +r} False{}:
      L.and_intro(perfect(T, p, l), perfect(T, p, tupd(T, p, r, Nat.sub(j, SC.pow2(p)), v, ndec(p, Nat.sub(j, SC.pow2(p))))), pf_left(T, p, l, r, pf), tupd_perfect(T, p, r, Nat.sub(j, SC.pow2(p)), v, ndec(p, Nat.sub(j, SC.pow2(p))), pf_right(T, p, l, r, pf)))

def tupd_slots(-T: Data, +d: Nat, +t: Tree<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {ndec(d, j) == b : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {slots(T, tupd(T, d, t, j, v, b)) == SC.update(T, slots(T, t), j, v) : List<&2, T>}:
  match d t b:
    case 0n TLeaf{x} _:
      leaf_update(T, x, v, j, hj)
    case 0n TNode{l, r} _:
      Empty.absurd({slots(T, TNode{l, r}) == SC.update(T, slots(T, TNode{l, r}), j, v) : List<&2, T>}, L.false_true(pf))
    case 1n+p TLeaf{x} _:
      Empty.absurd({Con{x, Nil{}} == SC.update(T, Con{x, Nil{}}, j, v) : List<&2, T>}, L.false_true(pf))
    case 1n+ +p TNode{+l, +r} True{}:
      Equal.trans(List<&2, T>, SC.append(T, slots(T, tupd(T, p, l, j, v, ndec(p, j))), slots(T, r)), SC.append(T, SC.update(T, slots(T, l), j, v), slots(T, r)), SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v),
        Equal.cong(List<&2, T>, List<&2, T>, xs => SC.append(T, xs, slots(T, r)), slots(T, tupd(T, p, l, j, v, ndec(p, j))), SC.update(T, slots(T, l), j, v), tupd_slots(T, p, l, j, v, eb, ndec(p, j), {==}, pf_left(T, p, l, r, pf))),
        Equal.sym(List<&2, T>, SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v), SC.append(T, SC.update(T, slots(T, l), j, v), slots(T, r)), LL.update_append_left(T, slots(T, l), slots(T, r), j, v, len_lt(T, p, l, j, pf_left(T, p, l, r, pf), eb))))
    case 1n+ +p TNode{+l, +r} False{}:
      +k = Nat.sub(j, SC.pow2(p))
      +le = N.not_lt_le(j, SC.pow2(p), eb)
      Equal.trans(List<&2, T>, SC.append(T, slots(T, l), slots(T, tupd(T, p, r, k, v, ndec(p, k)))), SC.append(T, slots(T, l), SC.update(T, slots(T, r), k, v)), SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v),
        Equal.cong(List<&2, T>, List<&2, T>, xs => SC.append(T, slots(T, l), xs), slots(T, tupd(T, p, r, k, v, ndec(p, k))), SC.update(T, slots(T, r), k, v), tupd_slots(T, p, r, k, v, upper_lt(j, p, hj, le), ndec(p, k), {==}, pf_right(T, p, l, r, pf))),
        Equal.sym(List<&2, T>, SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v), SC.append(T, slots(T, l), SC.update(T, slots(T, r), k, v)), right_update(T, p, l, r, j, v, pf_left(T, p, l, r, pf), le)))

def upd_perfect(-T: Data, +d: Nat, +t: Tree<T>, +j: Nat, +v: T, +pf: {perfect(T, d, t) == True{} : Bool}) -> {perfect(T, d, upd(T, d, t, j, v)) == True{} : Bool}:
  tupd_perfect(T, d, t, j, v, ndec(d, j), pf)

def upd_slots(-T: Data, +d: Nat, +t: Tree<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {slots(T, upd(T, d, t, j, v)) == SC.update(T, slots(T, t), j, v) : List<&2, T>}:
  tupd_slots(T, d, t, j, v, hj, ndec(d, j), {==}, pf)

# ---- U32 index bridges ----

def lt_bridge(+i: U32, +p: Nat, +hp: {Nat.is_lt(p, 32n) == True{} : Bool}, +b: Bool, +eb: {U32.is_lt(i, U.pow2u(p)) == b : Bool}) -> {Nat.is_lt(U32.to_nat(i), SC.pow2(p)) == b : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), SC.pow2(p)), Nat.is_lt(U32.to_nat(i), U32.to_nat(U.pow2u(p))), b,
    Equal.cong(Nat, Bool, n => Nat.is_lt(U32.to_nat(i), n), SC.pow2(p), U32.to_nat(U.pow2u(p)), Equal.sym(Nat, U32.to_nat(U.pow2u(p)), SC.pow2(p), U.pow2u_value(p, hp))),
    Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), U32.to_nat(U.pow2u(p))), U32.is_lt(i, U.pow2u(p)), b, Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), Nat.is_lt(U32.to_nat(i), U32.to_nat(U.pow2u(p))), U.is_lt_nat(i, U.pow2u(p))), eb))

def sub_bridge(+i: U32, +p: Nat, +hp: {Nat.is_lt(p, 32n) == True{} : Bool}, +le: {Nat.is_le(SC.pow2(p), U32.to_nat(i)) == True{} : Bool}) -> {U32.to_nat(U32.sub(i, U.pow2u(p))) == Nat.sub(U32.to_nat(i), SC.pow2(p)) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.sub(i, U.pow2u(p))), Nat.sub(U32.to_nat(i), U32.to_nat(U.pow2u(p))), Nat.sub(U32.to_nat(i), SC.pow2(p)),
    U.sub_nat(i, U.pow2u(p), L.subst(Nat, n => {Nat.is_le(n, U32.to_nat(i)) == True{} : Bool}, SC.pow2(p), U32.to_nat(U.pow2u(p)), Equal.sym(Nat, U32.to_nat(U.pow2u(p)), SC.pow2(p), U.pow2u_value(p, hp)), le)),
    Equal.cong(Nat, Nat, n => Nat.sub(U32.to_nat(i), n), U32.to_nat(U.pow2u(p)), SC.pow2(p), U.pow2u_value(p, hp)))

# ---- Base.Array.size / get / swap / set / new ----

def size_thaw(-T: Data, +d: Nat, +t: Tree<T>, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.size(T, thaw(T, t)) == (thaw(T, t), U.pow2u(d)) : Array<T> & U32}:
  match d t:
    case 0n TLeaf{x}:
      {==}
    case 0n TNode{l, r}:
      Empty.absurd({Array.size(T, thaw(T, TNode{l, r})) == (thaw(T, TNode{l, r}), 1) : Array<T> & U32}, L.false_true(pf))
    case 1n+p TLeaf{x}:
      Empty.absurd({Array.size(T, ALeaf{x}) == (ALeaf{x}, U.pow2u(1n+p)) : Array<T> & U32}, L.false_true(pf))
    case 1n+ +p TNode{+l, +r}:
      %Equal.sym(Array<T> & U32, Array.size(T, thaw(T, l)), (thaw(T, l), U.pow2u(p)), size_thaw(T, p, l, pf_left(T, p, l, r, pf))) : {Array.size.node(T, thaw(T, r), _) == (ANode{thaw(T, l), thaw(T, r)}, U32.shl(U.pow2u(p))) : Array<T> & U32}
      {==}

def get_go(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +b: Bool, +eb: {U32.is_lt(i, U.pow2u(N.pred(d))) == b : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.get.go(T, thaw(T, t), U.pow2u(d), i) == (thaw(T, t), x) : Array<T> & T}:
  match d t b:
    case 0n TLeaf{+y} _:
      %leaf_value(T, y, U32.to_nat(i), x, hi, hx) : {(ALeaf{y}, y) == (ALeaf{y}, _) : Array<T> & T}
      {==}
    case 0n TNode{l, r} _:
      Empty.absurd({Array.get.go(T, thaw(T, TNode{l, r}), 1, i) == (thaw(T, TNode{l, r}), x) : Array<T> & T}, L.false_true(pf))
    case 1n+p TLeaf{y} _:
      Empty.absurd({Array.get.go(T, ALeaf{y}, U.pow2u(1n+p), i) == (ALeaf{y}, x) : Array<T> & T}, L.false_true(pf))
    case 1n+ +p TNode{+l, +r} True{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = pf_left(T, p, l, r, pf)
      +hil = lt_bridge(i, p, hp, True{}, eb)
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.get.if(T, thaw(T, l), thaw(T, r), _, i, U32.is_lt(i, _)) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), True{}, eb) : {Array.get.if(T, thaw(T, l), thaw(T, r), U.pow2u(p), i, _) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      %Equal.sym(Array<T> & T, Array.get.go(T, thaw(T, l), U.pow2u(p), i), (thaw(T, l), x), get_go(T, p, l, i, x, hp, hil, Equal.trans(Maybe<&2, T>, SC.nth(T, slots(T, l), U32.to_nat(i)), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), U32.to_nat(i)), Some{x}, Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), U32.to_nat(i)), SC.nth(T, slots(T, l), U32.to_nat(i)), LL.nth_append_left(T, slots(T, l), slots(T, r), U32.to_nat(i), len_lt(T, p, l, U32.to_nat(i), pl, hil))), hx), U32.is_lt(i, U.pow2u(N.pred(p))), {==}, pl)) : {Array.swap.lo(T, thaw(T, r), _) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      {==}
    case 1n+ +p TNode{+l, +r} False{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = pf_left(T, p, l, r, pf)
      +le = N.not_lt_le(U32.to_nat(i), SC.pow2(p), lt_bridge(i, p, hp, False{}, eb))
      +j = U32.sub(i, U.pow2u(p))
      +ej = sub_bridge(i, p, hp, le)
      +hir = L.subst(Nat, n => {Nat.is_lt(n, SC.pow2(p)) == True{} : Bool}, Nat.sub(U32.to_nat(i), SC.pow2(p)), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), Nat.sub(U32.to_nat(i), SC.pow2(p)), ej), upper_lt(U32.to_nat(i), p, hi, le))
      +hxr = L.subst(Nat, n => {SC.nth(T, slots(T, r), n) == Some{x} : Maybe<&2, T>}, Nat.sub(U32.to_nat(i), SC.pow2(p)), U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), Nat.sub(U32.to_nat(i), SC.pow2(p)), ej), Equal.trans(Maybe<&2, T>, SC.nth(T, slots(T, r), Nat.sub(U32.to_nat(i), SC.pow2(p))), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), U32.to_nat(i)), Some{x}, Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), U32.to_nat(i)), SC.nth(T, slots(T, r), Nat.sub(U32.to_nat(i), SC.pow2(p))), right_nth(T, p, l, r, U32.to_nat(i), pl, le)), hx))
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.get.if(T, thaw(T, l), thaw(T, r), _, i, U32.is_lt(i, _)) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), False{}, eb) : {Array.get.if(T, thaw(T, l), thaw(T, r), U.pow2u(p), i, _) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      %Equal.sym(Array<T> & T, Array.get.go(T, thaw(T, r), U.pow2u(p), j), (thaw(T, r), x), get_go(T, p, r, j, x, hp, hir, hxr, U32.is_lt(j, U.pow2u(N.pred(p))), {==}, pf_right(T, p, l, r, pf))) : {Array.swap.hi(T, thaw(T, l), _) == (ANode{thaw(T, l), thaw(T, r)}, x) : Array<T> & T}
      {==}

def swap_go(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +v: T, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +b: Bool, +eb: {U32.is_lt(i, U.pow2u(N.pred(d))) == b : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.swap.go(T, thaw(T, t), U.pow2u(d), i, v) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), x) : Array<T> & T}:
  match d t b:
    case 0n TLeaf{+y} _:
      %leaf_value(T, y, U32.to_nat(i), x, hi, hx) : {(ALeaf{v}, y) == (ALeaf{v}, _) : Array<T> & T}
      {==}
    case 0n TNode{l, r} _:
      Empty.absurd({Array.swap.go(T, thaw(T, TNode{l, r}), 1, i, v) == (thaw(T, upd(T, 0n, TNode{l, r}, U32.to_nat(i), v)), x) : Array<T> & T}, L.false_true(pf))
    case 1n+p TLeaf{y} _:
      Empty.absurd({Array.swap.go(T, ALeaf{y}, U.pow2u(1n+p), i, v) == (thaw(T, upd(T, 1n+p, TLeaf{y}, U32.to_nat(i), v)), x) : Array<T> & T}, L.false_true(pf))
    case 1n+ +p TNode{+l, +r} True{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = pf_left(T, p, l, r, pf)
      +hil = lt_bridge(i, p, hp, True{}, eb)
      +ti = U32.to_nat(i)
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.swap.if(T, thaw(T, l), thaw(T, r), _, i, v, U32.is_lt(i, _)) == (thaw(T, upd(T, 1n+p, TNode{l, r}, ti, v)), x) : Array<T> & T}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), True{}, eb) : {Array.swap.if(T, thaw(T, l), thaw(T, r), U.pow2u(p), i, v, _) == (thaw(T, upd(T, 1n+p, TNode{l, r}, ti, v)), x) : Array<T> & T}
      %Equal.sym(Bool, Nat.is_lt(ti, SC.pow2(p)), True{}, hil) : {Array.swap.lo(T, thaw(T, r), Array.swap.go(T, thaw(T, l), U.pow2u(p), i, v)) == (thaw(T, tupd(T, 1n+p, TNode{l, r}, ti, v, _)), x) : Array<T> & T}
      %Equal.sym(Array<T> & T, Array.swap.go(T, thaw(T, l), U.pow2u(p), i, v), (thaw(T, upd(T, p, l, ti, v)), x), swap_go(T, p, l, i, v, x, hp, hil, Equal.trans(Maybe<&2, T>, SC.nth(T, slots(T, l), ti), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), ti), Some{x}, Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), ti), SC.nth(T, slots(T, l), ti), LL.nth_append_left(T, slots(T, l), slots(T, r), ti, len_lt(T, p, l, ti, pl, hil))), hx), U32.is_lt(i, U.pow2u(N.pred(p))), {==}, pl)) : {Array.swap.lo(T, thaw(T, r), _) == (thaw(T, TNode{tupd(T, p, l, ti, v, ndec(p, ti)), r}), x) : Array<T> & T}
      {==}
    case 1n+ +p TNode{+l, +r} False{}:
      +hp = N.lt_trans(p, 1n+p, 32n, N.lt_succ(p), hd)
      +pl = pf_left(T, p, l, r, pf)
      +ti = U32.to_nat(i)
      +nb = lt_bridge(i, p, hp, False{}, eb)
      +le = N.not_lt_le(ti, SC.pow2(p), nb)
      +j = U32.sub(i, U.pow2u(p))
      +k = Nat.sub(ti, SC.pow2(p))
      +ej = sub_bridge(i, p, hp, le)
      +hir = L.subst(Nat, n => {Nat.is_lt(n, SC.pow2(p)) == True{} : Bool}, k, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), k, ej), upper_lt(ti, p, hi, le))
      +hxr = L.subst(Nat, n => {SC.nth(T, slots(T, r), n) == Some{x} : Maybe<&2, T>}, k, U32.to_nat(j), Equal.sym(Nat, U32.to_nat(j), k, ej), Equal.trans(Maybe<&2, T>, SC.nth(T, slots(T, r), k), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), ti), Some{x}, Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), ti), SC.nth(T, slots(T, r), k), right_nth(T, p, l, r, ti, pl, le)), hx))
      +ih = swap_go(T, p, r, j, v, x, hp, hir, hxr, U32.is_lt(j, U.pow2u(N.pred(p))), {==}, pf_right(T, p, l, r, pf))
      +ih2 = L.subst(Nat, n => {Array.swap.go(T, thaw(T, r), U.pow2u(p), j, v) == (thaw(T, upd(T, p, r, n, v)), x) : Array<T> & T}, U32.to_nat(j), k, ej, ih)
      %Equal.sym(U32, U32.shr(U.pow2u(1n+p)), U.pow2u(p), U.shr_pow2u(p, hd)) : {Array.swap.if(T, thaw(T, l), thaw(T, r), _, i, v, U32.is_lt(i, _)) == (thaw(T, upd(T, 1n+p, TNode{l, r}, ti, v)), x) : Array<T> & T}
      %Equal.sym(Bool, U32.is_lt(i, U.pow2u(p)), False{}, eb) : {Array.swap.if(T, thaw(T, l), thaw(T, r), U.pow2u(p), i, v, _) == (thaw(T, upd(T, 1n+p, TNode{l, r}, ti, v)), x) : Array<T> & T}
      %Equal.sym(Bool, Nat.is_lt(ti, SC.pow2(p)), False{}, nb) : {Array.swap.hi(T, thaw(T, l), Array.swap.go(T, thaw(T, r), U.pow2u(p), j, v)) == (thaw(T, tupd(T, 1n+p, TNode{l, r}, ti, v, _)), x) : Array<T> & T}
      %Equal.sym(Array<T> & T, Array.swap.go(T, thaw(T, r), U.pow2u(p), j, v), (thaw(T, upd(T, p, r, k, v)), x), ih2) : {Array.swap.hi(T, thaw(T, l), _) == (thaw(T, TNode{l, tupd(T, p, r, k, v, ndec(p, k))}), x) : Array<T> & T}
      {==}

# Public Base entry points. Premises: the tree is perfect of depth d < 32 and
# the index is below 2^d; x is the value currently stored at that index.
def get(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.get(T, thaw(T, t), i) == (thaw(T, t), x) : Array<T> & T}:
  %Equal.sym(Array<T> & U32, Array.size(T, thaw(T, t)), (thaw(T, t), U.pow2u(d)), size_thaw(T, d, t, pf)) : {Array.get.at(T, i, _) == (thaw(T, t), x) : Array<T> & T}
  %Equal.sym(U32, U32.and(i, U32.sub(U.pow2u(d), 1)), i, U.mask_pow2u(i, d, hd, hi)) : {Array.get.go(T, thaw(T, t), U.pow2u(d), _) == (thaw(T, t), x) : Array<T> & T}
  get_go(T, d, t, i, x, hd, hi, hx, U32.is_lt(i, U.pow2u(N.pred(d))), {==}, pf)

def swap(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +v: T, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.swap(T, thaw(T, t), i, v) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), x) : Array<T> & T}:
  %Equal.sym(Array<T> & U32, Array.size(T, thaw(T, t)), (thaw(T, t), U.pow2u(d)), size_thaw(T, d, t, pf)) : {Array.swap.at(T, i, v, _) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), x) : Array<T> & T}
  %Equal.sym(U32, U32.and(i, U32.sub(U.pow2u(d), 1)), i, U.mask_pow2u(i, d, hd, hi)) : {Array.swap.go(T, thaw(T, t), U.pow2u(d), _, v) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), x) : Array<T> & T}
  swap_go(T, d, t, i, v, x, hd, hi, hx, U32.is_lt(i, U.pow2u(N.pred(d))), {==}, pf)

def set(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +v: T, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.set(T, thaw(T, t), i, v) == thaw(T, upd(T, d, t, U32.to_nat(i), v)) : Array<T>}:
  %Equal.sym(Array<T> & T, Array.swap(T, thaw(T, t), i, v), (thaw(T, upd(T, d, t, U32.to_nat(i), v)), x), swap(T, d, t, i, v, x, hd, hi, hx, pf)) : {Array.set.fin(T, _) == thaw(T, upd(T, d, t, U32.to_nat(i), v)) : Array<T>}
  {==}

def new(-T: Data, +d: Nat, +v: T) -> {Array.new(T, d, v) == thaw(T, trep(T, d, v)) : Array<T>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<T>, Array.new(T, p, v), thaw(T, trep(T, p, v)), new(T, p, v)) : {ANode{_, _} == ANode{thaw(T, trep(T, p, v)), thaw(T, trep(T, p, v))} : Array<T>}
      {==}

def clone(-T: Data, +t: Tree<T>) -> {Array.clone(T, thaw(T, t)) == (thaw(T, t), thaw(T, t)) : Array<T> & Array<T>}:
  match t:
    case TLeaf{x}:
      {==}
    case TNode{+l, +r}:
      %Equal.sym(Array<T> & Array<T>, Array.clone(T, thaw(T, l)), (thaw(T, l), thaw(T, l)), clone(T, l)) : {Array.clone.node(T, _, Array.clone(T, thaw(T, r))) == (ANode{thaw(T, l), thaw(T, r)}, ANode{thaw(T, l), thaw(T, r)}) : Array<T> & Array<T>}
      %Equal.sym(Array<T> & Array<T>, Array.clone(T, thaw(T, r)), (thaw(T, r), thaw(T, r)), clone(T, r)) : {Array.clone.node(T, (thaw(T, l), thaw(T, l)), _) == (ANode{thaw(T, l), thaw(T, r)}, ANode{thaw(T, l), thaw(T, r)}) : Array<T> & Array<T>}
      {==}

# ---- get after set (Base.Array.set then Base.Array.get) ----

def get_set_same(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +v: T, +x: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.get(T, Array.set(T, thaw(T, t), i, v), i) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), v) : Array<T> & T}:
  +t2 = upd(T, d, t, U32.to_nat(i), v)
  %Equal.sym(Array<T>, Array.set(T, thaw(T, t), i, v), thaw(T, t2), set(T, d, t, i, v, x, hd, hi, hx, pf)) : {Array.get(T, _, i) == (thaw(T, t2), v) : Array<T> & T}
  get(T, d, t2, i, v, hd, hi,
    L.subst(List<&2, T>, ys => {SC.nth(T, ys, U32.to_nat(i)) == Some{v} : Maybe<&2, T>}, SC.update(T, slots(T, t), U32.to_nat(i), v), slots(T, t2), Equal.sym(List<&2, T>, slots(T, t2), SC.update(T, slots(T, t), U32.to_nat(i), v), upd_slots(T, d, t, U32.to_nat(i), v, hi, pf)), LL.nth_update_same(T, slots(T, t), U32.to_nat(i), v, LL.nth_lt_length(T, slots(T, t), U32.to_nat(i), x, hx))),
    upd_perfect(T, d, t, U32.to_nat(i), v, pf))

def get_set_other(-T: Data, +d: Nat, +t: Tree<T>, +i: U32, +j: U32, +v: T, +x: T, +y: T, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), SC.pow2(d)) == True{} : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), SC.pow2(d)) == True{} : Bool}, +ne: {Nat.is_eq(U32.to_nat(i), U32.to_nat(j)) == False{} : Bool}, +hx: {SC.nth(T, slots(T, t), U32.to_nat(i)) == Some{x} : Maybe<&2, T>}, +hy: {SC.nth(T, slots(T, t), U32.to_nat(j)) == Some{y} : Maybe<&2, T>}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {Array.get(T, Array.set(T, thaw(T, t), i, v), j) == (thaw(T, upd(T, d, t, U32.to_nat(i), v)), y) : Array<T> & T}:
  +t2 = upd(T, d, t, U32.to_nat(i), v)
  %Equal.sym(Array<T>, Array.set(T, thaw(T, t), i, v), thaw(T, t2), set(T, d, t, i, v, x, hd, hi, hx, pf)) : {Array.get(T, _, j) == (thaw(T, t2), y) : Array<T> & T}
  get(T, d, t2, j, y, hd, hj,
    L.subst(List<&2, T>, ys => {SC.nth(T, ys, U32.to_nat(j)) == Some{y} : Maybe<&2, T>}, SC.update(T, slots(T, t), U32.to_nat(i), v), slots(T, t2), Equal.sym(List<&2, T>, slots(T, t2), SC.update(T, slots(T, t), U32.to_nat(i), v), upd_slots(T, d, t, U32.to_nat(i), v, hi, pf)), Equal.trans(Maybe<&2, T>, SC.nth(T, SC.update(T, slots(T, t), U32.to_nat(i), v), U32.to_nat(j)), SC.nth(T, slots(T, t), U32.to_nat(j)), Some{y}, LL.nth_update_other(T, slots(T, t), U32.to_nat(i), U32.to_nat(j), v, ne), hy)),
    upd_perfect(T, d, t, U32.to_nat(i), v, pf))
