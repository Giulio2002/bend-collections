import Base
import ./logic.bend as L
import ./nat.bend as N
import ./list.bend as LL
import ./spec_common.bend as SC
import ../../src/containers/internal/vec.bend as V
import ./lemmas/proofs/nat_algebra.bend as NA

# Functional correctness of the persistent vector src/internal/vec.bend:
# a perfect tree of depth d means its in-order slot list (length 2^d);
# get reads, set updates that list.

def slots(-T: Data, t: V.Vec<T>) -> List<&2, T>:
  match t:
    case V.VLeaf{x}:
      Con{x, Nil{}}
    case V.VNode{l, r}:
      SC.append(T, slots(T, l), slots(T, r))

def perfect(-T: Data, +d: Nat, t: V.Vec<T>) -> Bool:
  match d t:
    case 0n V.VLeaf{x}:
      True{}
    case 0n V.VNode{l, r}:
      False{}
    case 1n+p V.VLeaf{x}:
      False{}
    case 1n+p V.VNode{l, r}:
      Bool.and(perfect(T, p, l), perfect(T, p, r))

def pf_left(-T: Data, +p: Nat, +l: V.Vec<T>, +r: V.Vec<T>, +pf: {perfect(T, 1n+p, V.VNode{l, r}) == True{} : Bool}) -> {perfect(T, p, l) == True{} : Bool}:
  L.and_left(perfect(T, p, l), perfect(T, p, r), pf)

def pf_right(-T: Data, +p: Nat, +l: V.Vec<T>, +r: V.Vec<T>, +pf: {perfect(T, 1n+p, V.VNode{l, r}) == True{} : Bool}) -> {perfect(T, p, r) == True{} : Bool}:
  L.and_right(perfect(T, p, l), perfect(T, p, r), pf)

def slots_length(-T: Data, +d: Nat, +t: V.Vec<T>, +pf: {perfect(T, d, t) == True{} : Bool}) -> {SC.length(T, slots(T, t)) == V.pow2(d) : Nat}:
  match d t:
    case 0n V.VLeaf{x}:
      {==}
    case 0n V.VNode{l, r}:
      Empty.absurd({SC.length(T, slots(T, V.VNode{l, r})) == 1n : Nat}, L.false_true(pf))
    case 1n+p V.VLeaf{x}:
      Empty.absurd({1n == Nat.double(V.pow2(p)) : Nat}, L.false_true(pf))
    case 1n+ +p V.VNode{+l, +r}:
      %Equal.sym(Nat, SC.length(T, SC.append(T, slots(T, l), slots(T, r))), Nat.add(SC.length(T, slots(T, l)), SC.length(T, slots(T, r))), LL.length_append(T, slots(T, l), slots(T, r))) : {_ == Nat.double(V.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(T, slots(T, l)), V.pow2(p), slots_length(T, p, l, pf_left(T, p, l, r, pf))) : {Nat.add(_, SC.length(T, slots(T, r))) == Nat.double(V.pow2(p)) : Nat}
      %Equal.sym(Nat, SC.length(T, slots(T, r)), V.pow2(p), slots_length(T, p, r, pf_right(T, p, l, r, pf))) : {Nat.add(V.pow2(p), _) == Nat.double(V.pow2(p)) : Nat}
      Equal.sym(Nat, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p)))

def upper_lt(+j: Nat, +p: Nat, +hj: {Nat.is_lt(j, V.pow2(1n+p)) == True{} : Bool}, +le: {Nat.is_le(V.pow2(p), j) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(j, V.pow2(p)), V.pow2(p)) == True{} : Bool}:
  N.sub_lt(j, V.pow2(p), V.pow2(p), le, L.subst(Nat, n => {Nat.is_lt(j, n) == True{} : Bool}, Nat.double(V.pow2(p)), Nat.add(V.pow2(p), V.pow2(p)), NA.double_self(V.pow2(p)), hj))

def left_len(-T: Data, +p: Nat, +l: V.Vec<T>, +pl: {perfect(T, p, l) == True{} : Bool}) -> {V.pow2(p) == SC.length(T, slots(T, l)) : Nat}:
  Equal.sym(Nat, SC.length(T, slots(T, l)), V.pow2(p), slots_length(T, p, l, pl))

# ---- get ----

def get_go(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +hj: {Nat.is_lt(j, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, j) == b : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {V.get_go(T, d, t, j, b) == SC.nth(T, slots(T, t), j) : Maybe<&2, T>}:
  match d t b:
    case 0n V.VLeaf{x} _:
      match j:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Some{x} == SC.nth(T, Con{x, Nil{}}, 1n+q) : Maybe<&2, T>}, N.lt_zero_absurd(q, hj))
    case 0n V.VNode{l, r} _:
      Empty.absurd({None{} == SC.nth(T, slots(T, V.VNode{l, r}), j) : Maybe<&2, T>}, L.false_true(pf))
    case 1n+p V.VLeaf{x} _:
      Empty.absurd({None{} == SC.nth(T, Con{x, Nil{}}, j) : Maybe<&2, T>}, L.false_true(pf))
    case 1n+ +p V.VNode{+l, +r} True{}:
      +hl = L.subst(Nat, k => {Nat.is_lt(j, k) == True{} : Bool}, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf)), eb)
      Equal.trans(Maybe<&2, T>, V.get_go(T, p, l, j, V.dec(p, j)), SC.nth(T, slots(T, l), j), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j),
        get_go(T, p, l, j, eb, V.dec(p, j), {==}, pf_left(T, p, l, r, pf)),
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j), SC.nth(T, slots(T, l), j), LL.nth_append_left(T, slots(T, l), slots(T, r), j, hl)))
    case 1n+ +p V.VNode{+l, +r} False{}:
      +k = Nat.sub(j, V.pow2(p))
      +le = N.not_lt_le(j, V.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, j) == True{} : Bool}, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf)), le)
      Equal.trans(Maybe<&2, T>, V.get_go(T, p, r, k, V.dec(p, k)), SC.nth(T, slots(T, r), k), SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j),
        get_go(T, p, r, k, upper_lt(j, p, hj, le), V.dec(p, k), {==}, pf_right(T, p, l, r, pf)),
        Equal.sym(Maybe<&2, T>, SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j), SC.nth(T, slots(T, r), k),
          %Equal.sym(Nat, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf))) : {SC.nth(T, SC.append(T, slots(T, l), slots(T, r)), j) == SC.nth(T, slots(T, r), Nat.sub(j, _)) : Maybe<&2, T>}
          LL.nth_append_right(T, slots(T, l), slots(T, r), j, hr)))

def get(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +hj: {Nat.is_lt(j, V.pow2(d)) == True{} : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {V.get(T, d, t, j) == SC.nth(T, slots(T, t), j) : Maybe<&2, T>}:
  get_go(T, d, t, j, hj, V.dec(d, j), {==}, pf)

# ---- set ----

def set_go_perfect(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +v: T, +b: Bool, +pf: {perfect(T, d, t) == True{} : Bool}) -> {perfect(T, d, V.set_go(T, d, t, j, v, b)) == True{} : Bool}:
  match d t b:
    case 0n V.VLeaf{x} _:
      {==}
    case 0n V.VNode{l, r} _:
      pf
    case 1n+p V.VLeaf{x} _:
      pf
    case 1n+ +p V.VNode{+l, +r} True{}:
      L.and_intro(perfect(T, p, V.set_go(T, p, l, j, v, V.dec(p, j))), perfect(T, p, r), set_go_perfect(T, p, l, j, v, V.dec(p, j), pf_left(T, p, l, r, pf)), pf_right(T, p, l, r, pf))
    case 1n+ +p V.VNode{+l, +r} False{}:
      L.and_intro(perfect(T, p, l), perfect(T, p, V.set_go(T, p, r, Nat.sub(j, V.pow2(p)), v, V.dec(p, Nat.sub(j, V.pow2(p))))), pf_left(T, p, l, r, pf), set_go_perfect(T, p, r, Nat.sub(j, V.pow2(p)), v, V.dec(p, Nat.sub(j, V.pow2(p))), pf_right(T, p, l, r, pf)))

def set_perfect(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +v: T, +pf: {perfect(T, d, t) == True{} : Bool}) -> {perfect(T, d, V.set(T, d, t, j, v)) == True{} : Bool}:
  set_go_perfect(T, d, t, j, v, V.dec(d, j), pf)

def set_go_slots(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, V.pow2(d)) == True{} : Bool}, +b: Bool, +eb: {V.dec(d, j) == b : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {slots(T, V.set_go(T, d, t, j, v, b)) == SC.update(T, slots(T, t), j, v) : List<&2, T>}:
  match d t b:
    case 0n V.VLeaf{x} _:
      match j:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Con{v, Nil{}} == SC.update(T, Con{x, Nil{}}, 1n+q, v) : List<&2, T>}, N.lt_zero_absurd(q, hj))
    case 0n V.VNode{l, r} _:
      Empty.absurd({slots(T, V.VNode{l, r}) == SC.update(T, slots(T, V.VNode{l, r}), j, v) : List<&2, T>}, L.false_true(pf))
    case 1n+p V.VLeaf{x} _:
      Empty.absurd({Con{x, Nil{}} == SC.update(T, Con{x, Nil{}}, j, v) : List<&2, T>}, L.false_true(pf))
    case 1n+ +p V.VNode{+l, +r} True{}:
      +hl = L.subst(Nat, k => {Nat.is_lt(j, k) == True{} : Bool}, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf)), eb)
      Equal.trans(List<&2, T>, SC.append(T, slots(T, V.set_go(T, p, l, j, v, V.dec(p, j))), slots(T, r)), SC.append(T, SC.update(T, slots(T, l), j, v), slots(T, r)), SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v),
        Equal.cong(List<&2, T>, List<&2, T>, xs => SC.append(T, xs, slots(T, r)), slots(T, V.set_go(T, p, l, j, v, V.dec(p, j))), SC.update(T, slots(T, l), j, v), set_go_slots(T, p, l, j, v, eb, V.dec(p, j), {==}, pf_left(T, p, l, r, pf))),
        Equal.sym(List<&2, T>, SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v), SC.append(T, SC.update(T, slots(T, l), j, v), slots(T, r)), LL.update_append_left(T, slots(T, l), slots(T, r), j, v, hl)))
    case 1n+ +p V.VNode{+l, +r} False{}:
      +k = Nat.sub(j, V.pow2(p))
      +le = N.not_lt_le(j, V.pow2(p), eb)
      +hr = L.subst(Nat, q => {Nat.is_le(q, j) == True{} : Bool}, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf)), le)
      Equal.trans(List<&2, T>, SC.append(T, slots(T, l), slots(T, V.set_go(T, p, r, k, v, V.dec(p, k)))), SC.append(T, slots(T, l), SC.update(T, slots(T, r), k, v)), SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v),
        Equal.cong(List<&2, T>, List<&2, T>, xs => SC.append(T, slots(T, l), xs), slots(T, V.set_go(T, p, r, k, v, V.dec(p, k))), SC.update(T, slots(T, r), k, v), set_go_slots(T, p, r, k, v, upper_lt(j, p, hj, le), V.dec(p, k), {==}, pf_right(T, p, l, r, pf))),
        Equal.sym(List<&2, T>, SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v), SC.append(T, slots(T, l), SC.update(T, slots(T, r), k, v)),
          %Equal.sym(Nat, V.pow2(p), SC.length(T, slots(T, l)), left_len(T, p, l, pf_left(T, p, l, r, pf))) : {SC.update(T, SC.append(T, slots(T, l), slots(T, r)), j, v) == SC.append(T, slots(T, l), SC.update(T, slots(T, r), Nat.sub(j, _), v)) : List<&2, T>}
          LL.update_append_right(T, slots(T, l), slots(T, r), j, v, hr)))

def set(-T: Data, +d: Nat, +t: V.Vec<T>, +j: Nat, +v: T, +hj: {Nat.is_lt(j, V.pow2(d)) == True{} : Bool}, +pf: {perfect(T, d, t) == True{} : Bool}) -> {slots(T, V.set(T, d, t, j, v)) == SC.update(T, slots(T, t), j, v) : List<&2, T>}:
  set_go_slots(T, d, t, j, v, hj, V.dec(d, j), {==}, pf)

# ---- capacity chosen by depth_for ----

def pow2_pos(+d: Nat) -> {Nat.is_le(1n, V.pow2(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      N.le_trans(1n, V.pow2(p), Nat.double(V.pow2(p)), pow2_pos(p), N.double_self_le(V.pow2(p)))

# n + 2^d <= 2^(depth_go n d room) + room, for room <= 2^d.
def arr(+p: Nat, +a: Nat, +c: Nat) -> {Nat.add(p, Nat.add(Nat.add(1n, a), c)) == Nat.add(Nat.add(1n+p, c), a) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(1n, a), c), Nat.add(1n, Nat.add(a, c)), N.add_assoc(1n, a, c)) : {Nat.add(p, _) == Nat.add(Nat.add(1n+p, c), a) : Nat}
  %Equal.sym(Nat, Nat.add(p, 1n+Nat.add(a, c)), 1n+Nat.add(p, Nat.add(a, c)), N.add_succ(p, Nat.add(a, c))) : {_ == Nat.add(Nat.add(1n+p, c), a) : Nat}
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {1n+Nat.add(p, _) == Nat.add(Nat.add(1n+p, c), a) : Nat}
  %N.add_assoc(p, c, a) : {1n+_ == Nat.add(Nat.add(1n+p, c), a) : Nat}
  {==}

def le_add_cancel(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match c:
    case 0n:
      L.subst(Nat, q => {Nat.is_le(q, b) == True{} : Bool}, Nat.add(a, 0n), a, N.add_zero(a), L.subst(Nat, q => {Nat.is_le(Nat.add(a, 0n), q) == True{} : Bool}, Nat.add(b, 0n), b, N.add_zero(b), h))
    case 1n+k:
      le_add_cancel(a, b, k, L.subst(Nat, q => {Nat.is_le(q, Nat.add(b, k)) == True{} : Bool}, Nat.add(a, k), Nat.add(a, k), {==},
        L.subst(Nat, q => {Nat.is_le(1n+Nat.add(a, k), q) == True{} : Bool}, Nat.add(b, 1n+k), 1n+Nat.add(b, k), N.add_succ(b, k),
          L.subst(Nat, q => {Nat.is_le(q, Nat.add(b, 1n+k)) == True{} : Bool}, Nat.add(a, 1n+k), 1n+Nat.add(a, k), N.add_succ(a, k), h))))

def depth_go_cap(+n: Nat, +d: Nat, +room: Nat, +h: {Nat.is_le(room, V.pow2(d)) == True{} : Bool}) -> {Nat.is_le(Nat.add(n, V.pow2(d)), Nat.add(V.pow2(V.depth_go(n, d, room)), room)) == True{} : Bool}:
  match n room:
    case 0n _:
      N.le_add_right(V.pow2(d), room)
    case 1n+p 0n:
      +c = V.pow2(d)
      +c1 = Nat.sub(c, 1n)
      +pos = pow2_pos(d)
      +e1 = N.sub_add(c, 1n, pos)
      +R = V.pow2(V.depth_go(p, 1n+d, c1))
      +ih = depth_go_cap(p, 1n+d, c1, N.le_trans(c1, c, Nat.double(c), L.subst(Nat, q => {Nat.is_le(c1, q) == True{} : Bool}, Nat.add(1n, c1), c, e1, N.le_succ(c1)), N.double_self_le(c)))
      # ih : p + 2c <= R + (c - 1); with 2c = (1 + (c - 1)) + c this is 1 + p + c <= R.
      +e2 = Equal.trans(Nat, Nat.double(c), Nat.add(c, c), Nat.add(Nat.add(1n, c1), c), NA.double_self(c), Equal.cong(Nat, Nat, q => Nat.add(q, c), c, Nat.add(1n, c1), Equal.sym(Nat, Nat.add(1n, c1), c, e1)))
      +ih2 = L.subst(Nat, q => {Nat.is_le(Nat.add(p, q), Nat.add(R, c1)) == True{} : Bool}, Nat.double(c), Nat.add(Nat.add(1n, c1), c), e2, ih)
      # rearrange: p + ((1 + c1) + c) == (1 + p + c) + c1  and  R + c1
      +e3 = arr(p, c1, c)
      +ih3 = L.subst(Nat, q => {Nat.is_le(q, Nat.add(R, c1)) == True{} : Bool}, Nat.add(p, Nat.add(Nat.add(1n, c1), c)), Nat.add(Nat.add(1n+p, c), c1), e3, ih2)
      %Equal.sym(Nat, Nat.add(R, 0n), R, N.add_zero(R)) : {Nat.is_le(Nat.add(1n+p, c), _) == True{} : Bool}
      le_add_cancel(Nat.add(1n+p, c), R, c1, ih3)
    case 1n+p 1n+r:
      +ih = depth_go_cap(p, d, r, N.le_trans(r, 1n+r, V.pow2(d), N.le_succ(r), h))
      %Equal.sym(Nat, Nat.add(V.pow2(V.depth_go(p, d, r)), 1n+r), 1n+Nat.add(V.pow2(V.depth_go(p, d, r)), r), N.add_succ(V.pow2(V.depth_go(p, d, r)), r)) : {Nat.is_le(Nat.add(1n+p, V.pow2(d)), _) == True{} : Bool}
      ih

# p + ((1 + a) + c) == ((1 + p) + c) + a
# a + c <= b + c  implies  a <= b
def depth_for(+n: Nat) -> {Nat.is_le(n, V.pow2(V.depth_for(n))) == True{} : Bool}:
  +h = depth_go_cap(n, 0n, 1n, {==})
  %Equal.sym(Nat, Nat.add(n, 1n), 1n+n, N.add_comm(n, 1n)) : {Nat.is_le(n, V.pow2(V.depth_for(n))) == True{} : Bool}
  le_add_cancel(n, V.pow2(V.depth_for(n)), 1n, h)
