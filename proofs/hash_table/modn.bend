import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as A
import ../lemmas/proofs/nat_algebra.bend as NA
import ../lemmas/proofs/word_value.bend as WV
import ../math/u32div.bend as UD
import ./cyc.bend as CY

# Offsets around a ring of n buckets (n > 0):
#   pos(n, h, t)  == (h + t) mod n   the bucket t steps after h
#   dist(n, h, j) == (j + n - h) mod n   the steps from h to j
# and they are inverse.

def pos(+n: Nat, +h: Nat, +t: Nat) -> Nat:
  Nat.mod(Nat.add(h, t), n)

def dist(+n: Nat, +h: Nat, +j: Nat) -> Nat:
  Nat.mod(Nat.add(j, Nat.sub(n, h)), n)

def dm_e2(+bp: Nat, +v: Nat, g: WV.go_equation(bp, v, bp, 0n, 0n)) -> {v == Nat.add(Nat.mul(Nat.div(v, 1n+bp), 1n+bp), Nat.mod(v, 1n+bp)) : Nat}:
  (e, l) = g
  e

def dm_l2(+bp: Nat, +v: Nat, g: WV.go_equation(bp, v, bp, 0n, 0n)) -> {Nat.is_lt(Nat.mod(v, 1n+bp), 1n+bp) == True{} : Bool}:
  (e, l) = g
  N.le_lt_succ(Nat.mod(v, 1n+bp), bp, l)

# v == (v / n) n + v mod n, and v mod n < n
def dm_eq(+bp: Nat, +v: Nat) -> {v == Nat.add(Nat.mul(Nat.div(v, 1n+bp), 1n+bp), Nat.mod(v, 1n+bp)) : Nat}:
  dm_e2(bp, v, WV.go(bp, v, bp, 0n, 0n, N.add_zero(bp)))

def dm_lt(+bp: Nat, +v: Nat) -> {Nat.is_lt(Nat.mod(v, 1n+bp), 1n+bp) == True{} : Bool}:
  dm_l2(bp, v, WV.go(bp, v, bp, 0n, 0n, N.add_zero(bp)))

# (q n + r) mod n == r mod n
def absorb(+bp: Nat, +q: Nat, +r: Nat) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == Nat.mod(r, 1n+bp) : Nat}:
  +n = {1n+bp : Nat}
  +qr = Nat.div(r, n)
  +m = Nat.mod(r, n)
  +e = Equal.trans(Nat, Nat.add(Nat.mul(q, n), r), Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), Nat.add(Nat.mul(Nat.add(q, qr), n), m),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(q, n), z), r, Nat.add(Nat.mul(qr, n), m), dm_eq(bp, r)),
    Equal.trans(Nat, Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), Nat.add(Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), m), Nat.add(Nat.mul(Nat.add(q, qr), n), m),
      Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), m), Nat.add(Nat.mul(q, n), Nat.add(Nat.mul(qr, n), m)), N.add_assoc(Nat.mul(q, n), Nat.mul(qr, n), m)),
      Equal.cong(Nat, Nat, z => Nat.add(z, m), Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), Nat.mul(Nat.add(q, qr), n), Equal.sym(Nat, Nat.mul(Nat.add(q, qr), n), Nat.add(Nat.mul(q, n), Nat.mul(qr, n)), NA.mul_add_right(q, qr, n)))))
  Equal.trans(Nat, Nat.mod(Nat.add(Nat.mul(q, n), r), n), Nat.mod(Nat.add(Nat.mul(Nat.add(q, qr), n), m), n), m, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(Nat.mul(q, n), r), Nat.add(Nat.mul(Nat.add(q, qr), n), m), e), UD.mod_identify(Nat.add(q, qr), n, m, dm_lt(bp, r)))

# x + (y mod n) and x + y agree mod n
def mod_inner(+bp: Nat, +x: Nat, +y: Nat) -> {Nat.mod(Nat.add(x, Nat.mod(y, 1n+bp)), 1n+bp) == Nat.mod(Nat.add(x, y), 1n+bp) : Nat}:
  +n = {1n+bp : Nat}
  +qy = Nat.div(y, n)
  +my = Nat.mod(y, n)
  +e = Equal.trans(Nat, Nat.add(x, y), Nat.add(x, Nat.add(Nat.mul(qy, n), my)), Nat.add(Nat.mul(qy, n), Nat.add(x, my)),
    Equal.cong(Nat, Nat, z => Nat.add(x, z), y, Nat.add(Nat.mul(qy, n), my), dm_eq(bp, y)),
    NA.add_swap(x, Nat.mul(qy, n), my))
  Equal.sym(Nat, Nat.mod(Nat.add(x, y), n), Nat.mod(Nat.add(x, my), n), Equal.trans(Nat, Nat.mod(Nat.add(x, y), n), Nat.mod(Nat.add(Nat.mul(qy, n), Nat.add(x, my)), n), Nat.mod(Nat.add(x, my), n), Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(x, y), Nat.add(Nat.mul(qy, n), Nat.add(x, my)), e), absorb(bp, qy, Nat.add(x, my))))

def pos_lt(+bp: Nat, +h: Nat, +t: Nat) -> {Nat.is_lt(pos(1n+bp, h, t), 1n+bp) == True{} : Bool}:
  dm_lt(bp, Nat.add(h, t))

def dist_lt(+bp: Nat, +h: Nat, +j: Nat) -> {Nat.is_lt(dist(1n+bp, h, j), 1n+bp) == True{} : Bool}:
  dm_lt(bp, Nat.add(j, Nat.sub(1n+bp, h)))

# walking dist(h, j) steps from h reaches j
def pos_dist(+bp: Nat, +h: Nat, +j: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}) -> {pos(1n+bp, h, dist(1n+bp, h, j)) == j : Nat}:
  +n = {1n+bp : Nat}
  +s = Nat.add(j, Nat.sub(n, h))
  +e = Equal.trans(Nat, Nat.add(h, s), Nat.add(j, Nat.add(h, Nat.sub(n, h))), Nat.add(n, j), NA.add_swap(h, j, Nat.sub(n, h)),
    Equal.trans(Nat, Nat.add(j, Nat.add(h, Nat.sub(n, h))), Nat.add(j, n), Nat.add(n, j), Equal.cong(Nat, Nat, z => Nat.add(j, z), Nat.add(h, Nat.sub(n, h)), n, N.sub_add(n, h, N.lt_le(h, n, hh))), N.add_comm(j, n)))
  Equal.trans(Nat, Nat.mod(Nat.add(h, Nat.mod(s, n)), n), Nat.mod(Nat.add(h, s), n), j, mod_inner(bp, h, s),
    Equal.trans(Nat, Nat.mod(Nat.add(h, s), n), Nat.mod(Nat.add(n, j), n), j, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(h, s), Nat.add(n, j), e), CY.mod_plus(n, j, hj)))

# the distance from h to the bucket t < n steps after h is t
def dist_pos(+bp: Nat, +h: Nat, +t: Nat, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}) -> {dist(1n+bp, h, pos(1n+bp, h, t)) == t : Nat}:
  +n = {1n+bp : Nat}
  +d = Nat.sub(n, h)
  +x = Nat.mod(Nat.add(h, t), n)
  +e1 = Equal.trans(Nat, Nat.mod(Nat.add(x, d), n), Nat.mod(Nat.add(d, x), n), Nat.mod(Nat.add(d, Nat.add(h, t)), n), Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(x, d), Nat.add(d, x), N.add_comm(x, d)), mod_inner(bp, d, Nat.add(h, t)))
  +e2 = Equal.trans(Nat, Nat.add(d, Nat.add(h, t)), Nat.add(Nat.add(d, h), t), Nat.add(n, t), Equal.sym(Nat, Nat.add(Nat.add(d, h), t), Nat.add(d, Nat.add(h, t)), N.add_assoc(d, h, t)),
    Equal.cong(Nat, Nat, z => Nat.add(z, t), Nat.add(d, h), n, Equal.trans(Nat, Nat.add(d, h), Nat.add(h, d), n, N.add_comm(d, h), N.sub_add(n, h, N.lt_le(h, n, hh)))))
  Equal.trans(Nat, Nat.mod(Nat.add(x, d), n), Nat.mod(Nat.add(d, Nat.add(h, t)), n), t, e1, Equal.trans(Nat, Nat.mod(Nat.add(d, Nat.add(h, t)), n), Nat.mod(Nat.add(n, t), n), t, Equal.cong(Nat, Nat, z => Nat.mod(z, n), Nat.add(d, Nat.add(h, t)), Nat.add(n, t), e2), CY.mod_plus(n, t, ht)))

# the bucket after pos(h, t) is pos(h, t + 1)
def pos_next(+bp: Nat, +h: Nat, +t: Nat) -> {Nat.mod(1n+pos(1n+bp, h, t), 1n+bp) == pos(1n+bp, h, 1n+t) : Nat}:
  +n = {1n+bp : Nat}
  Equal.trans(Nat, Nat.mod(Nat.add(1n, Nat.mod(Nat.add(h, t), n)), n), Nat.mod(Nat.add(1n, Nat.add(h, t)), n), Nat.mod(Nat.add(h, 1n+t), n), mod_inner(bp, 1n, Nat.add(h, t)), Equal.cong(Nat, Nat, z => Nat.mod(z, n), 1n+Nat.add(h, t), Nat.add(h, 1n+t), Equal.sym(Nat, Nat.add(h, 1n+t), 1n+Nat.add(h, t), N.add_succ(h, t))))
