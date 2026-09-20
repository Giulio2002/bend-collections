import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC

# Heap index arithmetic: the shape of an array heap IS its index arithmetic.
# Element i has children 2i+1 and 2i+2 and, for i >= 1, parent (i - 1) / 2.
# Halving carries a flag because Bend patterns only take 0n and 1n+p and
# definitions may not be mutually recursive.

def kidl(+i: Nat) -> Nat:
  1n+Nat.double(i)

def kidr(+i: Nat) -> Nat:
  2n+Nat.double(i)

def half_go(n: Nat, odd: Bool) -> Nat:
  match n odd:
    case 0n _:
      0n
    case 1n+p False{}:
      half_go(p, True{})
    case 1n+p True{}:
      1n+half_go(p, False{})

def half(n: Nat) -> Nat:
  half_go(n, False{})

def par(+j: Nat) -> Nat:
  half(Nat.sub(j, 1n))

# ---- halving ----

def hg_false(+i: Nat) -> {half_go(Nat.double(i), False{}) == i : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      N.succ_cong(half_go(Nat.double(p), False{}), p, hg_false(p))

def hg_true(+i: Nat) -> {half_go(Nat.double(i), True{}) == i : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      N.succ_cong(half_go(Nat.double(p), True{}), p, hg_true(p))

def half_double(+i: Nat) -> {half(Nat.double(i)) == i : Nat}:
  hg_false(i)

def half_succ_double(+i: Nat) -> {half(1n+Nat.double(i)) == i : Nat}:
  hg_true(i)

def sub0(+n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n))

# ---- the parent of a child ----

def par_kidl(+i: Nat) -> {par(kidl(i)) == i : Nat}:
  %sub0(Nat.double(i)) : {half(_) == i : Nat}
  half_double(i)

def par_kidr(+i: Nat) -> {par(kidr(i)) == i : Nat}:
  %sub0(1n+Nat.double(i)) : {half(_) == i : Nat}
  half_succ_double(i)

# ---- j = 2 * half(j) or 1 + 2 * half(j) ----

# p = 2h  =>  1 + p = 1 + 2 * half(1 + p), because half(1 + 2h) = h
def half_even_succ(+p: Nat, +ep: {p == Nat.double(half(p)) : Nat}) -> {Nat.is_eq(1n+p, 1n+Nat.double(half(1n+p))) == True{} : Bool}:
  +h = half(p)
  %Equal.sym(Nat, p, Nat.double(h), ep) : {Nat.is_eq(1n+_, 1n+Nat.double(half(1n+_))) == True{} : Bool}
  %Equal.sym(Nat, half(1n+Nat.double(h)), h, half_succ_double(h)) : {Nat.is_eq(1n+Nat.double(h), 1n+Nat.double(_)) == True{} : Bool}
  N.is_eq_refl(1n+Nat.double(h))

# p = 1 + 2h  =>  1 + p = 2 * half(1 + p), because half(2 + 2h) = 1 + h
def half_odd_succ(+p: Nat, +ep: {p == 1n+Nat.double(half(p)) : Nat}) -> {Nat.is_eq(1n+p, Nat.double(half(1n+p))) == True{} : Bool}:
  +h = half(p)
  %Equal.sym(Nat, p, 1n+Nat.double(h), ep) : {Nat.is_eq(1n+_, Nat.double(half(1n+_))) == True{} : Bool}
  %Equal.sym(Nat, half(Nat.double(1n+h)), 1n+h, half_double(1n+h)) : {Nat.is_eq(2n+Nat.double(h), Nat.double(_)) == True{} : Bool}
  N.is_eq_refl(2n+Nat.double(h))

def half_split_succ(+p: Nat, e: {Nat.is_eq(p, Nat.double(half(p))) == True{} : Bool} | {Nat.is_eq(p, 1n+Nat.double(half(p))) == True{} : Bool}) -> {Nat.is_eq(1n+p, Nat.double(half(1n+p))) == True{} : Bool} | {Nat.is_eq(1n+p, 1n+Nat.double(half(1n+p))) == True{} : Bool}:
  match e:
    case Inl{ep}:
      Inr{half_even_succ(p, N.eq_from_is_eq(p, Nat.double(half(p)), ep))}
    case Inr{ep}:
      Inl{half_odd_succ(p, N.eq_from_is_eq(p, 1n+Nat.double(half(p)), ep))}

def half_split(+j: Nat) -> {Nat.is_eq(j, Nat.double(half(j))) == True{} : Bool} | {Nat.is_eq(j, 1n+Nat.double(half(j))) == True{} : Bool}:
  match j:
    case 0n:
      Inl{{==}}
    case 1n+p:
      half_split_succ(p, half_split(p))

# ---- every index >= 1 is the left or the right child of its parent ----

def kid_left(+p: Nat, +ep: {p == Nat.double(half(p)) : Nat}) -> {1n+p == kidl(par(1n+p)) : Nat}:
  %sub0(p) : {1n+p == kidl(half(_)) : Nat}
  N.succ_cong(p, Nat.double(half(p)), ep)

def kid_right(+p: Nat, +ep: {p == 1n+Nat.double(half(p)) : Nat}) -> {1n+p == kidr(par(1n+p)) : Nat}:
  %sub0(p) : {1n+p == kidr(half(_)) : Nat}
  N.succ_cong(p, 1n+Nat.double(half(p)), ep)

def kid_split_succ(+p: Nat, e: {Nat.is_eq(p, Nat.double(half(p))) == True{} : Bool} | {Nat.is_eq(p, 1n+Nat.double(half(p))) == True{} : Bool}) -> {1n+p == kidl(par(1n+p)) : Nat} | {1n+p == kidr(par(1n+p)) : Nat}:
  match e:
    case Inl{ep}:
      Inl{kid_left(p, N.eq_from_is_eq(p, Nat.double(half(p)), ep))}
    case Inr{ep}:
      Inr{kid_right(p, N.eq_from_is_eq(p, 1n+Nat.double(half(p)), ep))}

def kid_split(+j: Nat, +hj: {Nat.is_lt(0n, j) == True{} : Bool}) -> {j == kidl(par(j)) : Nat} | {j == kidr(par(j)) : Nat}:
  match j:
    case 0n:
      Empty.absurd({0n == kidl(par(0n)) : Nat} | {0n == kidr(par(0n)) : Nat}, L.true_not_false(Nat.is_lt(0n, 0n), hj, N.lt_irrefl(0n)))
    case 1n+p:
      kid_split_succ(p, half_split(p))

# ---- a parent index is smaller than its child index ----

def double_le(+i: Nat) -> {Nat.is_le(i, Nat.double(i)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      N.le_trans(p, Nat.double(p), 1n+Nat.double(p), double_le(p), N.le_succ(Nat.double(p)))

def kidl_gt(+i: Nat) -> {Nat.is_lt(i, kidl(i)) == True{} : Bool}:
  N.le_lt_succ(i, Nat.double(i), double_le(i))

def kidr_gt(+i: Nat) -> {Nat.is_lt(i, kidr(i)) == True{} : Bool}:
  N.lt_trans(i, kidl(i), kidr(i), kidl_gt(i), N.lt_succ(kidl(i)))

def kidl_pos(+i: Nat) -> {Nat.is_lt(0n, kidl(i)) == True{} : Bool}:
  N.le_lt_succ(0n, Nat.double(i), N.zero_le(Nat.double(i)))

def kidr_pos(+i: Nat) -> {Nat.is_lt(0n, kidr(i)) == True{} : Bool}:
  N.le_lt_succ(0n, 1n+Nat.double(i), N.zero_le(1n+Nat.double(i)))

def par_lt_of(+j: Nat, e: {j == kidl(par(j)) : Nat} | {j == kidr(par(j)) : Nat}) -> {Nat.is_lt(par(j), j) == True{} : Bool}:
  match e:
    case Inl{ej}:
      L.subst(Nat, z => {Nat.is_lt(par(j), z) == True{} : Bool}, kidl(par(j)), j, Equal.sym(Nat, j, kidl(par(j)), ej), kidl_gt(par(j)))
    case Inr{ej}:
      L.subst(Nat, z => {Nat.is_lt(par(j), z) == True{} : Bool}, kidr(par(j)), j, Equal.sym(Nat, j, kidr(par(j)), ej), kidr_gt(par(j)))

def par_lt(+j: Nat, +hj: {Nat.is_lt(0n, j) == True{} : Bool}) -> {Nat.is_lt(par(j), j) == True{} : Bool}:
  par_lt_of(j, kid_split(j, hj))

def kidl_pos1(+y: Nat) -> {Nat.is_le(1n, kidl(y)) == True{} : Bool}:
  N.zero_le(Nat.double(y))

def kidr_pos1(+y: Nat) -> {Nat.is_le(1n, kidr(y)) == True{} : Bool}:
  N.zero_le(1n+Nat.double(y))

# ---- halving a bound ----

def double_le_of(+j: Nat, e: {Nat.is_eq(j, Nat.double(half(j))) == True{} : Bool} | {Nat.is_eq(j, 1n+Nat.double(half(j))) == True{} : Bool}) -> {Nat.is_le(Nat.double(half(j)), j) == True{} : Bool}:
  match e:
    case Inl{ej}:
      N.eq_le(Nat.double(half(j)), j, Equal.sym(Nat, j, Nat.double(half(j)), N.eq_from_is_eq(j, Nat.double(half(j)), ej)))
    case Inr{ej}:
      L.subst(Nat, z => {Nat.is_le(Nat.double(half(j)), z) == True{} : Bool}, 1n+Nat.double(half(j)), j, Equal.sym(Nat, j, 1n+Nat.double(half(j)), N.eq_from_is_eq(j, 1n+Nat.double(half(j)), ej)), N.le_succ(Nat.double(half(j))))

def double_le_self(+j: Nat) -> {Nat.is_le(Nat.double(half(j)), j) == True{} : Bool}:
  double_le_of(j, half_split(j))

def double_lt_inj(+a: Nat, +b: Nat, +h: {Nat.is_lt(Nat.double(a), Nat.double(b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, N.lt_zero_absurd(Nat.double(a), h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      double_lt_inj(p, q, h)

def sub_le_self(+j: Nat) -> {Nat.is_le(Nat.sub(j, 1n), j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, N.sub_zero(k)) : {Nat.is_le(_, 1n+k) == True{} : Bool}
      N.le_succ(k)

# the parent of an index below 2^(k+1) is below 2^k
def par_bound(+i: Nat, +k: Nat, +h: {Nat.is_lt(i, SC.pow2(1n+k)) == True{} : Bool}) -> {Nat.is_lt(par(i), SC.pow2(k)) == True{} : Bool}:
  double_lt_inj(half(Nat.sub(i, 1n)), SC.pow2(k),
    N.le_lt_trans(Nat.double(half(Nat.sub(i, 1n))), Nat.sub(i, 1n), Nat.double(SC.pow2(k)), double_le_self(Nat.sub(i, 1n)),
      N.le_lt_trans(Nat.sub(i, 1n), i, Nat.double(SC.pow2(k)), sub_le_self(i), h)))

def double_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.double(a), 0n) == True{} : Bool}, N.lt_zero_absurd(a, h))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      double_lt(p, q, h)

# one more than an even number below an even number is still below it
def double_lt_succ(+a: Nat, +q: Nat, +h: {Nat.is_lt(Nat.double(a), Nat.double(q)) == True{} : Bool}) -> {Nat.is_lt(1n+Nat.double(a), Nat.double(q)) == True{} : Bool}:
  match a q:
    case _ 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(a), 0n) == True{} : Bool}, N.lt_zero_absurd(Nat.double(a), h))
    case 0n 1n+r:
      {==}
    case 1n+p 1n+r:
      double_lt_succ(p, r, h)

# a child index of an index below 2^d is below 2^(d+1)
def kidl_bound(+i: Nat, +d: Nat, +h: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(kidl(i), SC.pow2(1n+d)) == True{} : Bool}:
  double_lt_succ(i, SC.pow2(d), double_lt(i, SC.pow2(d), h))

# l + 1 < n is l < n - 1
def succ_lt_sub(+l: Nat, +n: Nat) -> {Nat.is_lt(1n+l, n) == Nat.is_lt(l, Nat.sub(n, 1n)) : Bool}:
  match n:
    case 0n:
      Equal.sym(Bool, Nat.is_lt(l, 0n), False{}, N.not_lt_zero(l))
    case 1n+m:
      %Equal.sym(Nat, Nat.sub(m, 0n), m, N.sub_zero(m)) : {Nat.is_lt(1n+l, 1n+m) == Nat.is_lt(l, _) : Bool}
      {==}

# ---- how much room a sift-down still has ----
#
# `scale(f, m)` is m * 2^f, written by structural recursion so that no
# multiplication appears. The sift-down invariant is `n <= scale(fuel, i + 1)`:
# the hole index at least doubles at every step, so the loop cannot run out of
# fuel before it runs out of children.

def scale(f: Nat, m: Nat) -> Nat:
  match f:
    case 0n:
      m
    case 1n+g:
      scale(g, Nat.double(m))

def double_le_mono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case 0n _:
      N.zero_le(Nat.double(b))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.double(1n+p), 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      double_le_mono(p, q, h)

def scale_mono(f: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(scale(f, a), scale(f, b)) == True{} : Bool}:
  match f:
    case 0n:
      h
    case 1n+g:
      scale_mono(g, Nat.double(a), Nat.double(b), double_le_mono(a, b, h))

def kid_double_of(+i: Nat, +c: Nat, +ep: {par(c) == i : Nat}, e: {c == kidl(par(c)) : Nat} | {c == kidr(par(c)) : Nat}) -> {Nat.is_le(Nat.double(1n+i), 1n+c) == True{} : Bool}:
  match e:
    case Inl{ec}:
      L.subst(Nat, z => {Nat.is_le(Nat.double(1n+i), 1n+z) == True{} : Bool}, kidl(i), c, Equal.sym(Nat, c, kidl(i), L.subst(Nat, z => {c == kidl(z) : Nat}, par(c), i, ep, ec)), N.le_refl(2n+Nat.double(i)))
    case Inr{ec}:
      L.subst(Nat, z => {Nat.is_le(Nat.double(1n+i), 1n+z) == True{} : Bool}, kidr(i), c, Equal.sym(Nat, c, kidr(i), L.subst(Nat, z => {c == kidr(z) : Nat}, par(c), i, ep, ec)), N.le_succ(2n+Nat.double(i)))

# a child index is at least twice the parent's, so 1 + kid >= 2 * (1 + i)
def kid_double(+i: Nat, +c: Nat, +ep: {par(c) == i : Nat}, +hcpos: {Nat.is_le(1n, c) == True{} : Bool}) -> {Nat.is_le(Nat.double(1n+i), 1n+c) == True{} : Bool}:
  kid_double_of(i, c, ep, kid_split(c, N.succ_le_lt(0n, c, hcpos)))
