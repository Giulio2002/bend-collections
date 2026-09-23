import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as A
import ../../lib/word.bend as WD
import ../../lib/arith.bend as AR
import ../../lib/u32div.bend as UD
import ../../math/u64/u64div.bend as UV
import ../../../src/containers/hash_table.bend as H
import ../../lib/words32.bend as W32

# Bucket indices of a table of N = 2^k buckets (mask = 2^k - 1, k <= 30):
#   and_mod    x & mask == x mod N
#   next       bnext(i) == (i + 1) mod N
#   dist       (b - a) & mask == (b + N - a) mod N  (the cyclic distance a -> b)
# Bounds are over the symbolic `one` (see proofs/math/word.bend).

def msk(+k: Nat) -> U32:
  U32{WD.mask(32n, k)}

# x & (2^k - 1) is x mod 2^k
def and_mod(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +x: U32) -> {UD.v(U32.and(x, msk(k))) == Nat.mod(UD.v(x), WD.sc(k, one)) : Nat}:
  +a = UD.v(U32.and(x, msk(k)))
  +hp = UV.hp32(k, x)
  +split = UV.and32(k, x, msk(k), {==})
  +lt = UV.and32_lt(k, one, h1, x, msk(k), {==})
  +e = Equal.trans(Nat, UD.v(x), Nat.add(a, WD.sc(k, hp)), Nat.add(Nat.mul(hp, WD.sc(k, one)), a), split,
    Equal.trans(Nat, Nat.add(a, WD.sc(k, hp)), Nat.add(WD.sc(k, hp), a), Nat.add(Nat.mul(hp, WD.sc(k, one)), a), N.add_comm(a, WD.sc(k, hp)), Equal.cong(Nat, Nat, z => Nat.add(z, a), WD.sc(k, hp), Nat.mul(hp, WD.sc(k, one)), Equal.sym(Nat, Nat.mul(hp, WD.sc(k, one)), WD.sc(k, hp), AR.mul_sc1(k, one, h1, hp)))))
  Equal.sym(Nat, Nat.mod(UD.v(x), WD.sc(k, one)), a, Equal.trans(Nat, Nat.mod(UD.v(x), WD.sc(k, one)), Nat.mod(Nat.add(Nat.mul(hp, WD.sc(k, one)), a), WD.sc(k, one)), a, Equal.cong(Nat, Nat, z => Nat.mod(z, WD.sc(k, one)), UD.v(x), Nat.add(Nat.mul(hp, WD.sc(k, one)), a), e), UD.mod_identify(hp, WD.sc(k, one), a, lt)))


# the next bucket, cyclically
def next_val(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +i: U32, +hk: {Nat.is_lt(WD.sc(k, one), WD.sc(32n, one)) == True{} : Bool}, +hi: {Nat.is_lt(UD.v(i), WD.sc(k, one)) == True{} : Bool}) -> {UD.v(H.bnext(i, msk(k))) == Nat.mod(1n+UD.v(i), WD.sc(k, one)) : Nat}:
  +hin = W32.inc_val(one, h1, i, N.le_lt_trans(1n+UD.v(i), WD.sc(k, one), WD.sc(32n, one), N.lt_succ_le_succ(UD.v(i), WD.sc(k, one), hi), hk))
  Equal.trans(Nat, UD.v(U32.and(U32.inc(i), msk(k))), Nat.mod(UD.v(U32.inc(i)), WD.sc(k, one)), Nat.mod(1n+UD.v(i), WD.sc(k, one)), and_mod(one, h1, k, U32.inc(i)), Equal.cong(Nat, Nat, z => Nat.mod(z, WD.sc(k, one)), UD.v(U32.inc(i)), 1n+UD.v(i), hin))

# ---- cyclic distance ----

def sub_split(+a: Nat, +n: Nat, +m: Nat, +ha: {Nat.is_le(a, n) == True{} : Bool}, +hn: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.sub(m, a) == Nat.add(Nat.sub(n, a), Nat.sub(m, n)) : Nat}:
  +e1 = N.sub_add(n, a, ha)
  +e2 = N.sub_add(m, n, hn)
  # m == a + ((n - a) + (m - n))
  +e3 = Equal.trans(Nat, m, Nat.add(n, Nat.sub(m, n)), Nat.add(a, Nat.add(Nat.sub(n, a), Nat.sub(m, n))), Equal.sym(Nat, Nat.add(n, Nat.sub(m, n)), m, e2),
    Equal.trans(Nat, Nat.add(n, Nat.sub(m, n)), Nat.add(Nat.add(a, Nat.sub(n, a)), Nat.sub(m, n)), Nat.add(a, Nat.add(Nat.sub(n, a), Nat.sub(m, n))), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(m, n)), n, Nat.add(a, Nat.sub(n, a)), Equal.sym(Nat, Nat.add(a, Nat.sub(n, a)), n, e1)), N.add_assoc(a, Nat.sub(n, a), Nat.sub(m, n))))
  %Equal.sym(Nat, m, Nat.add(a, Nat.add(Nat.sub(n, a), Nat.sub(m, n))), e3) : {Nat.sub(_, a) == Nat.add(Nat.sub(n, a), Nat.sub(m, n)) : Nat}
  N.add_sub_cancel(a, Nat.add(Nat.sub(n, a), Nat.sub(m, n)))

# (N + r) mod N == r for r < N
def mod_plus(+n: Nat, +r: Nat, +h: {Nat.is_lt(r, n) == True{} : Bool}) -> {Nat.mod(Nat.add(n, r), n) == r : Nat}:
  +e = Equal.cong(Nat, Nat, z => Nat.add(z, r), n, Nat.mul(1n, n), Equal.sym(Nat, Nat.mul(1n, n), n, N.add_zero(n)))
  Equal.trans(Nat, Nat.mod(Nat.add(n, r), n), Nat.mod(Nat.add(Nat.mul(1n, n), r), n), r, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(n, r), Nat.add(Nat.mul(1n, n), r), e), UD.mod_identify(1n, n, r, h))

def mod_small(+n: Nat, +r: Nat, +h: {Nat.is_lt(r, n) == True{} : Bool}) -> {Nat.mod(r, n) == r : Nat}:
  UD.mod_identify(0n, n, r, h)

def lt_add_r(+a: Nat, +b: Nat, +x: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, x), Nat.add(b, x)) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(z, Nat.add(b, x)) == True{} : Bool}, Nat.add(x, a), Nat.add(a, x), N.add_comm(x, a), L.subst(Nat, z => {Nat.is_lt(Nat.add(x, a), z) == True{} : Bool}, Nat.add(x, b), Nat.add(b, x), N.add_comm(x, b), N.lt_add_left(a, b, x, h)))

# b + (n - a) == n + (b - a) when a <= b and a <= n
def wrap_free(+a: Nat, +b: Nat, +n: Nat, +hab: {Nat.is_le(a, b) == True{} : Bool}, +han: {Nat.is_le(a, n) == True{} : Bool}) -> {Nat.add(b, Nat.sub(n, a)) == Nat.add(n, Nat.sub(b, a)) : Nat}:
  +x = Nat.sub(b, a)
  +y = Nat.sub(n, a)
  +e1 = Equal.cong(Nat, Nat, z => Nat.add(z, y), b, Nat.add(a, x), Equal.sym(Nat, Nat.add(a, x), b, N.sub_add(b, a, hab)))
  +e2 = Equal.trans(Nat, Nat.add(Nat.add(a, x), y), Nat.add(Nat.add(a, y), x), Nat.add(n, x), A.add_rot(a, x, y), Equal.cong(Nat, Nat, z => Nat.add(z, x), Nat.add(a, y), n, N.sub_add(n, a, han)))
  Equal.trans(Nat, Nat.add(b, y), Nat.add(Nat.add(a, x), y), Nat.add(n, x), e1, e2)

def dist_le(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +a: U32, +b: U32, +hb: {Nat.is_lt(UD.v(b), WD.sc(k, one)) == True{} : Bool}, +han: {Nat.is_le(UD.v(a), WD.sc(k, one)) == True{} : Bool}, +hab: {Nat.is_le(UD.v(a), UD.v(b)) == True{} : Bool}) -> {Nat.mod(UD.v(U32.sub(b, a)), WD.sc(k, one)) == Nat.mod(Nat.add(UD.v(b), Nat.sub(WD.sc(k, one), UD.v(a))), WD.sc(k, one)) : Nat}:
  +n = WD.sc(k, one)
  +d = Nat.sub(UD.v(b), UD.v(a))
  +hd = N.le_lt_trans(d, UD.v(b), n, AR.sub_le2(UD.v(b), UD.v(a)), hb)
  +l = Equal.trans(Nat, Nat.mod(UD.v(U32.sub(b, a)), n), Nat.mod(d, n), d, Equal.cong(Nat, Nat, z => Nat.mod(z, n), UD.v(U32.sub(b, a)), d, U.sub_nat(b, a, hab)), mod_small(n, d, hd))
  +r = Equal.trans(Nat, Nat.mod(Nat.add(UD.v(b), Nat.sub(n, UD.v(a))), n), Nat.mod(Nat.add(n, d), n), d, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(UD.v(b), Nat.sub(n, UD.v(a))), Nat.add(n, d), wrap_free(UD.v(a), UD.v(b), n, hab, han)), mod_plus(n, d, hd))
  Equal.trans(Nat, Nat.mod(UD.v(U32.sub(b, a)), n), d, Nat.mod(Nat.add(UD.v(b), Nat.sub(n, UD.v(a))), n), l, Equal.sym(Nat, Nat.mod(Nat.add(UD.v(b), Nat.sub(n, UD.v(a))), n), d, r))

def dist_gt(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +j: Nat, +hkj: {Nat.add(k, j) == 32n : Nat}, +a: U32, +b: U32, +ha: {Nat.is_lt(UD.v(a), WD.sc(k, one)) == True{} : Bool}, +hba: {Nat.is_lt(UD.v(b), UD.v(a)) == True{} : Bool}) -> {Nat.mod(UD.v(U32.sub(b, a)), WD.sc(k, one)) == Nat.mod(Nat.add(UD.v(b), Nat.sub(WD.sc(k, one), UD.v(a))), WD.sc(k, one)) : Nat}:
  +n = WD.sc(k, one)
  +kk = WD.sc(32n, one)
  +av = UD.v(a)
  +bv = UD.v(b)
  +m = Nat.sub(WD.sc(j, one), one)
  +hk = Equal.trans(Nat, kk, WD.sc(Nat.add(k, j), one), WD.sc(k, WD.sc(j, one)), Equal.cong(Nat, Nat, z => WD.sc(z, one), 32n, Nat.add(k, j), Equal.sym(Nat, Nat.add(k, j), 32n, hkj)), AR.sc_idx(k, j, one))
  +hnk = L.subst(Nat, z => {Nat.is_le(n, z) == True{} : Bool}, WD.sc(k, WD.sc(j, one)), kk, Equal.sym(Nat, kk, WD.sc(k, WD.sc(j, one)), hk), AR.sc_le(k, one, WD.sc(j, one), AR.le_sc(j, one)))
  +han = N.lt_le(av, n, ha)
  +hak = N.le_trans(av, n, kk, han, hnk)
  +d = Nat.add(bv, Nat.sub(kk, av))
  +r = Nat.add(bv, Nat.sub(n, av))
  # the machine difference is b + (2^32 - a)
  +e = Equal.trans(Nat, Nat.add(bv, kk), Nat.add(bv, Nat.add(Nat.sub(kk, av), av)), Nat.add(d, av),
    Equal.cong(Nat, Nat, z => Nat.add(bv, z), kk, Nat.add(Nat.sub(kk, av), av), Equal.sym(Nat, Nat.add(Nat.sub(kk, av), av), kk, Equal.trans(Nat, Nat.add(Nat.sub(kk, av), av), Nat.add(av, Nat.sub(kk, av)), kk, N.add_comm(Nat.sub(kk, av), av), N.sub_add(kk, av, hak)))),
    Equal.sym(Nat, Nat.add(d, av), Nat.add(bv, Nat.add(Nat.sub(kk, av), av)), N.add_assoc(bv, Nat.sub(kk, av), av)))
  +hd = L.subst(Nat, z => {Nat.is_lt(d, z) == True{} : Bool}, Nat.add(av, Nat.sub(kk, av)), kk, N.sub_add(kk, av, hak), lt_add_r(bv, av, Nat.sub(kk, av), hba))
  +hsub = UD.sub32(one, h1, b, a, d, e, hd)
  +hr = L.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, Nat.add(av, Nat.sub(n, av)), n, N.sub_add(n, av, han), lt_add_r(bv, av, Nat.sub(n, av), hba))
  # d == mul(m, n) + r
  +ekn = Equal.trans(Nat, Nat.sub(kk, n), Nat.sub(WD.sc(k, WD.sc(j, one)), n), Nat.mul(m, n), Equal.cong(Nat, Nat, z => Nat.sub(z, n), kk, WD.sc(k, WD.sc(j, one)), hk),
    Equal.trans(Nat, Nat.sub(WD.sc(k, WD.sc(j, one)), n), WD.sc(k, m), Nat.mul(m, n), Equal.sym(Nat, WD.sc(k, m), Nat.sub(WD.sc(k, WD.sc(j, one)), n), AR.sc_sub(k, WD.sc(j, one), one)), Equal.sym(Nat, Nat.mul(m, n), WD.sc(k, m), AR.mul_sc1(k, one, h1, m))))
  +ed = Equal.trans(Nat, d, Nat.add(bv, Nat.add(Nat.sub(n, av), Nat.sub(kk, n))), Nat.add(Nat.mul(m, n), r),
    Equal.cong(Nat, Nat, z => Nat.add(bv, z), Nat.sub(kk, av), Nat.add(Nat.sub(n, av), Nat.sub(kk, n)), sub_split(av, n, kk, han, hnk)),
    Equal.trans(Nat, Nat.add(bv, Nat.add(Nat.sub(n, av), Nat.sub(kk, n))), Nat.add(r, Nat.sub(kk, n)), Nat.add(Nat.mul(m, n), r),
      Equal.sym(Nat, Nat.add(r, Nat.sub(kk, n)), Nat.add(bv, Nat.add(Nat.sub(n, av), Nat.sub(kk, n))), N.add_assoc(bv, Nat.sub(n, av), Nat.sub(kk, n))),
      Equal.trans(Nat, Nat.add(r, Nat.sub(kk, n)), Nat.add(r, Nat.mul(m, n)), Nat.add(Nat.mul(m, n), r), Equal.cong(Nat, Nat, z => Nat.add(r, z), Nat.sub(kk, n), Nat.mul(m, n), ekn), N.add_comm(r, Nat.mul(m, n)))))
  +l = Equal.trans(Nat, Nat.mod(UD.v(U32.sub(b, a)), n), Nat.mod(Nat.add(Nat.mul(m, n), r), n), r, Equal.cong(Nat, Nat, z => Nat.mod(z, n), UD.v(U32.sub(b, a)), Nat.add(Nat.mul(m, n), r), Equal.trans(Nat, UD.v(U32.sub(b, a)), d, Nat.add(Nat.mul(m, n), r), hsub, ed)), UD.mod_identify(m, n, r, hr))
  Equal.trans(Nat, Nat.mod(UD.v(U32.sub(b, a)), n), r, Nat.mod(r, n), l, Equal.sym(Nat, Nat.mod(r, n), r, mod_small(n, r, hr)))

def dist_g(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +j: Nat, +hkj: {Nat.add(k, j) == 32n : Nat}, +a: U32, +b: U32, +ha: {Nat.is_lt(UD.v(a), WD.sc(k, one)) == True{} : Bool}, +hb: {Nat.is_lt(UD.v(b), WD.sc(k, one)) == True{} : Bool}, +c: Bool, +hc: {Nat.is_le(UD.v(a), UD.v(b)) == c : Bool}) -> {Nat.mod(UD.v(U32.sub(b, a)), WD.sc(k, one)) == Nat.mod(Nat.add(UD.v(b), Nat.sub(WD.sc(k, one), UD.v(a))), WD.sc(k, one)) : Nat}:
  match c:
    case True{}:
      dist_le(one, h1, k, a, b, hb, N.lt_le(UD.v(a), WD.sc(k, one), ha), hc)
    case False{}:
      dist_gt(one, h1, k, j, hkj, a, b, ha, N.not_le_lt(UD.v(a), UD.v(b), hc))

# THEOREM: (b - a) & mask is the cyclic distance from a to b.
def dist(+one: Nat, +h1: {one == 1n : Nat}, +k: Nat, +j: Nat, +hkj: {Nat.add(k, j) == 32n : Nat}, +a: U32, +b: U32, +ha: {Nat.is_lt(UD.v(a), WD.sc(k, one)) == True{} : Bool}, +hb: {Nat.is_lt(UD.v(b), WD.sc(k, one)) == True{} : Bool}) -> {UD.v(U32.and(U32.sub(b, a), msk(k))) == Nat.mod(Nat.add(UD.v(b), Nat.sub(WD.sc(k, one), UD.v(a))), WD.sc(k, one)) : Nat}:
  Equal.trans(Nat, UD.v(U32.and(U32.sub(b, a), msk(k))), Nat.mod(UD.v(U32.sub(b, a)), WD.sc(k, one)), Nat.mod(Nat.add(UD.v(b), Nat.sub(WD.sc(k, one), UD.v(a))), WD.sc(k, one)), and_mod(one, h1, k, U32.sub(b, a)), dist_g(one, h1, k, j, hkj, a, b, ha, hb, Nat.is_le(UD.v(a), UD.v(b)), {==}))
