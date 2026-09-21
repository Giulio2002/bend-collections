import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../../reference/lru/proofs/nat_algebra.bend as NA
import ../graph/zip.bend as ZP
import ../binary_heap/budget.bend as HB
import ./state.bend as ST

# The capacity budget of the deque. A push doubles the block when the window
# touches the block's end on its side (not only when the block is full), so
# the window can drift and the depth is NOT bounded by the size. It is
# bounded by the number of pushes: with P the pushes performed so far,
# R = lo + len and cap = 2^depth, the representation keeps
#
#   (A) 1 + 2R <= cap + 2P      (B) cap <= 1 + 2(P + lo)      (D) len <= P
#
# At a back doubling R = cap, so (A) gives cap + 1 <= 2P; at a front doubling
# lo = 0, so (B) gives cap <= 1 + 2P. Hence 1 + 2P < 2^q with q <= 31 keeps
# every doubled block within 2^31 slots, and a trace needs only
# 1 + 2(P + pushes(ops)) < 2^q -- no bound on its length.

def budg(+d: Nat, +lo: Nat, +n: Nat, +P: Nat) -> Bool:
  Bool.and(Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))),
    Bool.and(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P)))

def bud(-T: Data, sh: ST.Shadow<T>, +P: Nat) -> Bool:
  match sh:
    case ST.Sh{+d, +lo, +n, t}:
      budg(d, lo, n, P)

def ba(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}) -> {Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))) == True{} : Bool}:
  L.and_left(Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))), Bool.and(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P)), h)

def bb(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}) -> {Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))) == True{} : Bool}:
  L.and_left(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P), L.and_right(Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))), Bool.and(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P)), h))

def bd(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}) -> {Nat.is_le(n, P) == True{} : Bool}:
  L.and_right(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P), L.and_right(Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))), Bool.and(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P)), h))

def bmk(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +ha: {Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))) == True{} : Bool}, +hb: {Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))) == True{} : Bool}, +hd: {Nat.is_le(n, P) == True{} : Bool}) -> {budg(d, lo, n, P) == True{} : Bool}:
  L.and_intro(Nat.is_le(1n+Nat.double(Nat.add(lo, n)), Nat.add(SC.pow2(d), Nat.double(P))), Bool.and(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P)), ha,
    L.and_intro(Nat.is_le(SC.pow2(d), 1n+Nat.double(Nat.add(P, lo))), Nat.is_le(n, P), hb, hd))

# ---- small arithmetic ----

def le2(+a: Nat) -> {Nat.is_le(a, 2n+a) == True{} : Bool}:
  N.le_trans(a, 1n+a, 2n+a, N.le_succ(a), N.le_succ(1n+a))

def add2(+c: Nat, +x: Nat) -> {Nat.add(c, 2n+x) == 2n+Nat.add(c, x) : Nat}:
  Equal.trans(Nat, Nat.add(c, 2n+x), 1n+Nat.add(c, 1n+x), 2n+Nat.add(c, x), N.add_succ(c, 1n+x), N.succ_cong(Nat.add(c, 1n+x), 1n+Nat.add(c, x), N.add_succ(c, x)))

def add1(+P: Nat) -> {Nat.add(P, 1n) == 1n+P : Nat}:
  Equal.trans(Nat, Nat.add(P, 1n), 1n+Nat.add(P, 0n), 1n+P, N.add_succ(P, 0n), N.succ_cong(Nat.add(P, 0n), P, N.add_zero(P)))

def add_le_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(a, c), Nat.add(c, a), N.add_comm(a, c)) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  N.le_add_left(a, b, c, h)

def succ_dec1(+x: Nat, +h: {Nat.is_le(1n, x) == True{} : Bool}) -> {x == 1n+DQ.dec1(x) : Nat}:
  match x:
    case 0n:
      Empty.absurd({0n == 1n+DQ.dec1(0n) : Nat}, L.false_true(h))
    case 1n+p:
      {==}

# ---- transfers ----

def bud_zero(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}) -> {budg(d, lo, n, Nat.add(P, 0n)) == True{} : Bool}:
  L.subst(Nat, z => {budg(d, lo, n, z) == True{} : Bool}, P, Nat.add(P, 0n), Equal.sym(Nat, Nat.add(P, 0n), P, N.add_zero(P)), h)

def bud_one(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, 1n+P) == True{} : Bool}) -> {budg(d, lo, n, Nat.add(P, 1n)) == True{} : Bool}:
  L.subst(Nat, z => {budg(d, lo, n, z) == True{} : Bool}, 1n+P, Nat.add(P, 1n), Equal.sym(Nat, Nat.add(P, 1n), 1n+P, add1(P)), h)

# back push with room
def t_pb_room(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}) -> {budg(d, lo, 1n+n, 1n+P) == True{} : Bool}:
  +R = Nat.add(lo, n)
  +X = Nat.add(SC.pow2(d), Nat.double(P))
  +Y = Nat.double(Nat.add(P, lo))
  bmk(d, lo, 1n+n, 1n+P,
    %Equal.sym(Nat, Nat.add(lo, 1n+n), 1n+R, N.add_succ(lo, n)) : {Nat.is_le(1n+Nat.double(_), Nat.add(SC.pow2(d), Nat.double(1n+P))) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(SC.pow2(d), 2n+Nat.double(P)), 2n+X, add2(SC.pow2(d), Nat.double(P))) : {Nat.is_le(1n+Nat.double(1n+R), _) == True{} : Bool}
    ba(d, lo, n, P, h),
    N.le_trans(SC.pow2(d), 1n+Y, 3n+Y, bb(d, lo, n, P, h), le2(1n+Y)),
    bd(d, lo, n, P, h))

# back push that doubles the block (the window reaches its end)
def t_pb_grow(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +h: {budg(d, lo, n, P) == True{} : Bool}, +hfull: {Nat.is_le(SC.pow2(d), Nat.add(lo, n)) == True{} : Bool}, +hw: {Nat.is_le(Nat.add(lo, n), SC.pow2(d)) == True{} : Bool}) -> {budg(1n+d, lo, 1n+n, 1n+P) == True{} : Bool}:
  +R = Nat.add(lo, n)
  +c = SC.pow2(d)
  +DP = Nat.double(P)
  +h1 = N.le_trans(1n+Nat.double(R), Nat.add(c, DP), Nat.add(R, DP), ba(d, lo, n, P, h), add_le_r(c, R, DP, hfull))
  +h2 = L.subst(Nat, z => {Nat.is_le(1n+z, Nat.add(R, DP)) == True{} : Bool}, Nat.double(R), Nat.add(R, R), NA.double_self(R), h1)
  +h3 = ZP.le_cancel(R, 1n+R, DP, L.subst(Nat, z => {Nat.is_le(z, Nat.add(R, DP)) == True{} : Bool}, 1n+Nat.add(R, R), Nat.add(R, 1n+R), Equal.sym(Nat, Nat.add(R, 1n+R), 1n+Nat.add(R, R), N.add_succ(R, R)), h2))
  +h4 = N.le_trans(1n, 1n+R, DP, N.zero_le(R), h3)
  +hA = N.le_trans(1n+Nat.double(R), 1n+Nat.double(c), Nat.add(Nat.double(c), DP), N.double_le(R, c, hw),
    L.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.double(c), DP)) == True{} : Bool}, Nat.add(Nat.double(c), 1n), 1n+Nat.double(c), add1(Nat.double(c)), N.le_add_left(1n, DP, Nat.double(c), h4)))
  +hle = N.le_trans(c, R, Nat.add(P, lo), hfull, L.subst(Nat, z => {Nat.is_le(R, z) == True{} : Bool}, Nat.add(lo, P), Nat.add(P, lo), N.add_comm(lo, P), N.le_add_left(n, P, lo, bd(d, lo, n, P, h))))
  bmk(1n+d, lo, 1n+n, 1n+P,
    %Equal.sym(Nat, Nat.add(lo, 1n+n), 1n+R, N.add_succ(lo, n)) : {Nat.is_le(1n+Nat.double(_), Nat.add(SC.pow2(1n+d), Nat.double(1n+P))) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(Nat.double(c), 2n+DP), 2n+Nat.add(Nat.double(c), DP), add2(Nat.double(c), DP)) : {Nat.is_le(1n+Nat.double(1n+R), _) == True{} : Bool}
    hA,
    N.le_trans(Nat.double(c), Nat.double(Nat.add(P, lo)), 3n+Nat.double(Nat.add(P, lo)), N.double_le(c, Nat.add(P, lo), hle), N.le_trans(Nat.double(Nat.add(P, lo)), 1n+Nat.double(Nat.add(P, lo)), 3n+Nat.double(Nat.add(P, lo)), N.le_succ(Nat.double(Nat.add(P, lo))), le2(1n+Nat.double(Nat.add(P, lo))))),
    bd(d, lo, n, P, h))

# front push with room (lo = 1 + k)
def t_pf_room(+d: Nat, +k: Nat, +n: Nat, +P: Nat, +h: {budg(d, 1n+k, n, P) == True{} : Bool}) -> {budg(d, k, 1n+n, 1n+P) == True{} : Bool}:
  +R = Nat.add(1n+k, n)
  +X = Nat.add(SC.pow2(d), Nat.double(P))
  bmk(d, k, 1n+n, 1n+P,
    %Equal.sym(Nat, Nat.add(k, 1n+n), 1n+Nat.add(k, n), N.add_succ(k, n)) : {Nat.is_le(1n+Nat.double(_), Nat.add(SC.pow2(d), Nat.double(1n+P))) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(SC.pow2(d), 2n+Nat.double(P)), 2n+X, add2(SC.pow2(d), Nat.double(P))) : {Nat.is_le(1n+Nat.double(1n+Nat.add(k, n)), _) == True{} : Bool}
    N.le_trans(1n+Nat.double(R), X, 2n+X, ba(d, 1n+k, n, P, h), le2(X)),
    L.subst(Nat, z => {Nat.is_le(SC.pow2(d), 1n+Nat.double(z)) == True{} : Bool}, Nat.add(P, 1n+k), 1n+Nat.add(P, k), N.add_succ(P, k), bb(d, 1n+k, n, P, h)),
    bd(d, 1n+k, n, P, h))

# front push that doubles the block (lo = 0; the new window starts at 2^d - 1)
def t_pf_grow(+d: Nat, +n: Nat, +P: Nat, +h: {budg(d, 0n, n, P) == True{} : Bool}) -> {budg(1n+d, DQ.dec1(SC.pow2(d)), 1n+n, 1n+P) == True{} : Bool}:
  +c = SC.pow2(d)
  +j = DQ.dec1(c)
  +DP = Nat.double(P)
  +hj = succ_dec1(c, N.pow2_pos(d))
  +hA0 = N.le_trans(1n+Nat.add(Nat.double(c), Nat.double(n)), 1n+Nat.add(Nat.double(c), DP), 2n+Nat.add(Nat.double(c), DP), N.le_add_left(Nat.double(n), DP, Nat.double(c), N.double_le(n, P, bd(d, 0n, n, P, h))), N.le_succ(1n+Nat.add(Nat.double(c), DP)))
  +hA1 = L.subst(Nat, z => {Nat.is_le(1n+z, 2n+Nat.add(Nat.double(c), DP)) == True{} : Bool}, Nat.add(Nat.double(c), Nat.double(n)), Nat.double(Nat.add(c, n)), N.add_double(c, n), hA0)
  +hA2 = L.subst(Nat, z => {Nat.is_le(1n+Nat.double(Nat.add(z, n)), 2n+Nat.add(Nat.double(c), DP)) == True{} : Bool}, c, 1n+j, hj, hA1)
  +hB0 = N.le_trans(Nat.double(j), Nat.double(Nat.add(P, j)), 1n+Nat.double(Nat.add(P, j)), N.double_le(j, Nat.add(P, j), L.subst(Nat, z => {Nat.is_le(j, z) == True{} : Bool}, Nat.add(j, P), Nat.add(P, j), N.add_comm(j, P), N.le_add_right(j, P))), N.le_succ(Nat.double(Nat.add(P, j))))
  +hB1 = L.subst(Nat, z => {Nat.is_le(Nat.double(z), 3n+Nat.double(Nat.add(P, j))) == True{} : Bool}, 1n+j, c, Equal.sym(Nat, c, 1n+j, hj), hB0)
  bmk(1n+d, j, 1n+n, 1n+P,
    %Equal.sym(Nat, Nat.add(j, 1n+n), 1n+Nat.add(j, n), N.add_succ(j, n)) : {Nat.is_le(1n+Nat.double(_), Nat.add(SC.pow2(1n+d), Nat.double(1n+P))) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(Nat.double(c), 2n+DP), 2n+Nat.add(Nat.double(c), DP), add2(Nat.double(c), DP)) : {Nat.is_le(1n+Nat.double(1n+Nat.add(j, n)), _) == True{} : Bool}
    hA2,
    hB1,
    bd(d, 0n, n, P, h))

# pops (the window shrinks at one end)
def t_popf(+d: Nat, +lo: Nat, +m: Nat, +P: Nat, +h: {budg(d, lo, 1n+m, P) == True{} : Bool}) -> {budg(d, 1n+lo, m, P) == True{} : Bool}:
  +Y = Nat.double(Nat.add(P, lo))
  bmk(d, 1n+lo, m, P,
    L.subst(Nat, z => {Nat.is_le(1n+Nat.double(z), Nat.add(SC.pow2(d), Nat.double(P))) == True{} : Bool}, Nat.add(lo, 1n+m), 1n+Nat.add(lo, m), N.add_succ(lo, m), ba(d, lo, 1n+m, P, h)),
    %Equal.sym(Nat, Nat.add(P, 1n+lo), 1n+Nat.add(P, lo), N.add_succ(P, lo)) : {Nat.is_le(SC.pow2(d), 1n+Nat.double(_)) == True{} : Bool}
    N.le_trans(SC.pow2(d), 1n+Y, 3n+Y, bb(d, lo, 1n+m, P, h), le2(1n+Y)),
    N.le_trans(m, 1n+m, P, N.le_succ(m), bd(d, lo, 1n+m, P, h)))

def t_popb(+d: Nat, +lo: Nat, +m: Nat, +P: Nat, +h: {budg(d, lo, 1n+m, P) == True{} : Bool}) -> {budg(d, lo, m, P) == True{} : Bool}:
  bmk(d, lo, m, P,
    N.le_trans(1n+Nat.double(Nat.add(lo, m)), 1n+Nat.double(Nat.add(lo, 1n+m)), Nat.add(SC.pow2(d), Nat.double(P)), N.double_le(Nat.add(lo, m), Nat.add(lo, 1n+m), N.le_add_left(m, 1n+m, lo, N.le_succ(m))), ba(d, lo, 1n+m, P, h)),
    bb(d, lo, 1n+m, P, h),
    N.le_trans(m, 1n+m, P, N.le_succ(m), bd(d, lo, 1n+m, P, h)))

# ---- the doubling premises, from 1 + 2P < 2^q (q <= 31) ----

def cap_room(+d: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hc: {Nat.is_lt(SC.pow2(d), SC.pow2(q)) == True{} : Bool}) -> {Nat.is_le(1n+d, 31n) == True{} : Bool}:
  N.lt_succ_le_succ(d, 31n, N.lt_le_trans(d, q, 31n, HB.pow2_inv(d, q, hc), hq))

def pb_or_c(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +h: {budg(d, lo, n, P) == True{} : Bool}, +hP: {Nat.is_lt(1n+Nat.double(P), SC.pow2(q)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(Nat.add(lo, n), SC.pow2(d)) == b : Bool}) -> {Bool.or(Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), Nat.is_le(1n+d, 31n)) == True{} : Bool}:
  match b:
    case True{}:
      L.subst(Bool, z => {Bool.or(z, Nat.is_le(1n+d, 31n)) == True{} : Bool}, True{}, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), True{}, eb), {==})
    case False{}:
      +R = Nat.add(lo, n)
      +c = SC.pow2(d)
      +DP = Nat.double(P)
      +hfull = N.not_lt_le(R, c, eb)
      +h1 = N.le_trans(1n+Nat.double(R), Nat.add(c, DP), Nat.add(R, DP), ba(d, lo, n, P, h), add_le_r(c, R, DP, hfull))
      +h2 = L.subst(Nat, z => {Nat.is_le(1n+z, Nat.add(R, DP)) == True{} : Bool}, Nat.double(R), Nat.add(R, R), NA.double_self(R), h1)
      +h3 = ZP.le_cancel(R, 1n+R, DP, L.subst(Nat, z => {Nat.is_le(z, Nat.add(R, DP)) == True{} : Bool}, 1n+Nat.add(R, R), Nat.add(R, 1n+R), Equal.sym(Nat, Nat.add(R, 1n+R), 1n+Nat.add(R, R), N.add_succ(R, R)), h2))
      +hc = N.le_lt_trans(c, R, SC.pow2(q), hfull, N.lt_le_trans(R, 1n+R, SC.pow2(q), N.lt_succ(R), N.le_trans(1n+R, DP, SC.pow2(q), h3, N.lt_le(DP, SC.pow2(q), N.le_lt_trans(DP, 1n+DP, SC.pow2(q), N.le_succ(DP), hP)))))
      L.subst(Bool, z => {Bool.or(z, Nat.is_le(1n+d, 31n)) == True{} : Bool}, False{}, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), Equal.sym(Bool, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), False{}, eb), cap_room(d, q, hq, hc))

def pb_or(+d: Nat, +lo: Nat, +n: Nat, +P: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +h: {budg(d, lo, n, P) == True{} : Bool}, +hP: {Nat.is_lt(1n+Nat.double(P), SC.pow2(q)) == True{} : Bool}) -> {Bool.or(Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), Nat.is_le(1n+d, 31n)) == True{} : Bool}:
  pb_or_c(d, lo, n, P, q, hq, h, hP, Nat.is_lt(Nat.add(lo, n), SC.pow2(d)), {==})

def pf_or(+d: Nat, lo: Nat, +n: Nat, +P: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +h: {budg(d, lo, n, P) == True{} : Bool}, +hP: {Nat.is_lt(1n+Nat.double(P), SC.pow2(q)) == True{} : Bool}) -> {Bool.or(Nat.is_lt(0n, lo), Nat.is_le(1n+d, 31n)) == True{} : Bool}:
  match lo:
    case 0n:
      cap_room(d, q, hq, N.le_lt_trans(SC.pow2(d), 1n+Nat.double(P), SC.pow2(q), L.subst(Nat, z => {Nat.is_le(SC.pow2(d), 1n+Nat.double(z)) == True{} : Bool}, Nat.add(P, 0n), P, N.add_zero(P), bb(d, 0n, n, P, h)), hP))
    case 1n+k:
      {==}
