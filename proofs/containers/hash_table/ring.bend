import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../spec/lib/common.bend as SC
import ./buckets.bend as B
import ./modn.bend as M
import ./inv.bend as IV
import ./insm.bend as IM
import ./insert.bend as IS

# Offsets around the ring of buckets, and rewriting two buckets of a list.


def mod_n(+bp: Nat, +r: Nat) -> {Nat.mod(Nat.add(1n+bp, r), 1n+bp) == Nat.mod(r, 1n+bp) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.add(1n+bp, r), 1n+bp), Nat.mod(Nat.add(Nat.mul(1n, 1n+bp), r), 1n+bp), Nat.mod(r, 1n+bp), Equal.cong(Nat, Nat, z => Nat.mod(Nat.add(z, r), 1n+bp), 1n+bp, Nat.mul(1n, 1n+bp), Equal.sym(Nat, Nat.mul(1n, 1n+bp), 1n+bp, Equal.trans(Nat, Nat.mul(1n, 1n+bp), Nat.mul(1n+bp, 1n), 1n+bp, NA.mul_comm(1n, 1n+bp), NA.mul_one(1n+bp)))), M.absorb(bp, 1n, r))

# walking x then y steps is walking x + y steps
def pos_add(+bp: Nat, +a: Nat, +x: Nat, +y: Nat) -> {M.pos(1n+bp, M.pos(1n+bp, a, x), y) == M.pos(1n+bp, a, Nat.add(x, y)) : Nat}:
  +p = Nat.mod(Nat.add(a, x), 1n+bp)
  Equal.trans(Nat, Nat.mod(Nat.add(p, y), 1n+bp), Nat.mod(Nat.add(y, p), 1n+bp), M.pos(1n+bp, a, Nat.add(x, y)), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.add(p, y), Nat.add(y, p), N.add_comm(p, y)),
    Equal.trans(Nat, Nat.mod(Nat.add(y, p), 1n+bp), Nat.mod(Nat.add(y, Nat.add(a, x)), 1n+bp), M.pos(1n+bp, a, Nat.add(x, y)), M.mod_inner(bp, y, Nat.add(a, x)),
      Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.add(y, Nat.add(a, x)), Nat.add(a, Nat.add(x, y)), Equal.trans(Nat, Nat.add(y, Nat.add(a, x)), Nat.add(a, Nat.add(y, x)), Nat.add(a, Nat.add(x, y)), NA.add_swap(y, a, x), Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(y, x), Nat.add(x, y), N.add_comm(y, x))))))

# walking n more steps comes back
def pos_wrap(+bp: Nat, +a: Nat, +t: Nat) -> {M.pos(1n+bp, a, Nat.add(1n+bp, t)) == M.pos(1n+bp, a, t) : Nat}:
  Equal.trans(Nat, Nat.mod(Nat.add(a, Nat.add(1n+bp, t)), 1n+bp), Nat.mod(Nat.add(1n+bp, Nat.add(a, t)), 1n+bp), M.pos(1n+bp, a, t), Equal.cong(Nat, Nat, z => Nat.mod(z, 1n+bp), Nat.add(a, Nat.add(1n+bp, t)), Nat.add(1n+bp, Nat.add(a, t)), NA.add_swap(a, 1n+bp, t)), mod_n(bp, Nat.add(a, t)))

def dist_self(+bp: Nat, +a: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}) -> {M.dist(1n+bp, a, a) == 0n : Nat}:
  L.subst(Nat, z => {M.dist(1n+bp, a, z) == 0n : Nat}, M.pos(1n+bp, a, 0n), a, IV.pos0(bp, a, ha), M.dist_pos(bp, a, 0n, ha, N.succ_le_lt(0n, 1n+bp, N.zero_le(bp))))

def eq_of_dist0(+bp: Nat, +a: Nat, +j: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +h: {M.dist(1n+bp, a, j) == 0n : Nat}) -> {a == j : Nat}:
  Equal.trans(Nat, a, M.pos(1n+bp, a, 0n), j, Equal.sym(Nat, M.pos(1n+bp, a, 0n), a, IV.pos0(bp, a, ha)), Equal.trans(Nat, M.pos(1n+bp, a, 0n), M.pos(1n+bp, a, M.dist(1n+bp, a, j)), j, Equal.cong(Nat, Nat, z => M.pos(1n+bp, a, z), 0n, M.dist(1n+bp, a, j), Equal.sym(Nat, M.dist(1n+bp, a, j), 0n, h)), M.pos_dist(bp, a, j, ha, hj)))

def pn_c(+bp: Nat, +a: Nat, +t: Nat, +h: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hne: {Nat.is_eq(t, M.dist(1n+bp, a, h)) == False{} : Bool}, +c: Bool, +hc: {Nat.is_eq(M.pos(1n+bp, a, t), h) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e = Equal.trans(Nat, t, M.dist(1n+bp, a, M.pos(1n+bp, a, t)), M.dist(1n+bp, a, h), Equal.sym(Nat, M.dist(1n+bp, a, M.pos(1n+bp, a, t)), t, M.dist_pos(bp, a, t, ha, ht)), Equal.cong(Nat, Nat, z => M.dist(1n+bp, a, z), M.pos(1n+bp, a, t), h, N.eq_from_is_eq(M.pos(1n+bp, a, t), h, hc)))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(t, M.dist(1n+bp, a, h)), False{}, Equal.sym(Bool, Nat.is_eq(t, M.dist(1n+bp, a, h)), True{}, IS.eq_is_eq(t, M.dist(1n+bp, a, h), e)), hne)))

# the step t < n of a path is at h only when t = dist(a, h)
def pos_ne(+bp: Nat, +a: Nat, +t: Nat, +h: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +ht: {Nat.is_lt(t, 1n+bp) == True{} : Bool}, +hne: {Nat.is_eq(t, M.dist(1n+bp, a, h)) == False{} : Bool}) -> {Nat.is_eq(M.pos(1n+bp, a, t), h) == False{} : Bool}:
  pn_c(bp, a, t, h, ha, ht, hne, Nat.is_eq(M.pos(1n+bp, a, t), h), {==})

# x + z < x + y: z < y
def zy_lt(+x: Nat, +y: Nat, +z: Nat, +h: {Nat.is_lt(Nat.add(x, z), Nat.add(x, y)) == True{} : Bool}) -> {Nat.is_lt(z, y) == True{} : Bool}:
  match x:
    case 0n:
      h
    case 1n+p:
      zy_lt(p, y, z, h)

def ds_c(+bp: Nat, +a: Nat, +h: Nat, +j: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hle: {Nat.is_le(M.dist(1n+bp, h, j), M.dist(1n+bp, a, j)) == True{} : Bool}, +pj: {M.pos(1n+bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j))) == j : Nat}, +c: Bool, +hc: {Nat.is_lt(Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), 1n+bp) == c : Bool}) -> {Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)) == M.dist(1n+bp, a, j) : Nat}:
  match c:
    case True{}:
      Equal.trans(Nat, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), M.dist(1n+bp, a, M.pos(1n+bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)))), M.dist(1n+bp, a, j), Equal.sym(Nat, M.dist(1n+bp, a, M.pos(1n+bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)))), Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), M.dist_pos(bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), ha, hc)), Equal.cong(Nat, Nat, z => M.dist(1n+bp, a, z), M.pos(1n+bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j))), j, pj))
    case False{}:
      +z = Nat.sub(Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), 1n+bp)
      +enz = N.sub_add(Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), 1n+bp, N.not_lt_le(Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), 1n+bp, hc))
      +pz = Equal.trans(Nat, M.pos(1n+bp, a, z), M.pos(1n+bp, a, Nat.add(1n+bp, z)), j, Equal.sym(Nat, M.pos(1n+bp, a, Nat.add(1n+bp, z)), M.pos(1n+bp, a, z), pos_wrap(bp, a, z)), Equal.trans(Nat, M.pos(1n+bp, a, Nat.add(1n+bp, z)), M.pos(1n+bp, a, Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j))), j, Equal.cong(Nat, Nat, w => M.pos(1n+bp, a, w), Nat.add(1n+bp, z), Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), enz), pj))
      +hxz = L.subst(Nat, w => {Nat.is_lt(Nat.add(M.dist(1n+bp, a, h), z), w) == True{} : Bool}, Nat.add(1n+bp, z), Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)), enz, N.lt_add_r2(M.dist(1n+bp, a, h), 1n+bp, z, M.dist_lt(bp, a, h)))
      +hzn = N.lt_trans(z, M.dist(1n+bp, h, j), 1n+bp, zy_lt(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j), z, hxz), M.dist_lt(bp, h, j))
      +dz = Equal.trans(Nat, M.dist(1n+bp, a, j), M.dist(1n+bp, a, M.pos(1n+bp, a, z)), z, Equal.cong(Nat, Nat, w => M.dist(1n+bp, a, w), j, M.pos(1n+bp, a, z), Equal.sym(Nat, M.pos(1n+bp, a, z), j, pz)), M.dist_pos(bp, a, z, ha, hzn))
      +hyz = L.subst(Nat, w => {Nat.is_le(M.dist(1n+bp, h, j), w) == True{} : Bool}, M.dist(1n+bp, a, j), z, dz, hle)
      Empty.absurd({Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)) == M.dist(1n+bp, a, j) : Nat}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(M.dist(1n+bp, h, j), z), False{}, Equal.sym(Bool, Nat.is_le(M.dist(1n+bp, h, j), z), True{}, hyz), N.lt_not_le(z, M.dist(1n+bp, h, j), zy_lt(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j), z, hxz)))))

# THEOREM: when h lies no further from j than a does, the path a -> j goes through h
def dist_split(+bp: Nat, +a: Nat, +h: Nat, +j: Nat, +ha: {Nat.is_lt(a, 1n+bp) == True{} : Bool}, +hh: {Nat.is_lt(h, 1n+bp) == True{} : Bool}, +hj: {Nat.is_lt(j, 1n+bp) == True{} : Bool}, +hle: {Nat.is_le(M.dist(1n+bp, h, j), M.dist(1n+bp, a, j)) == True{} : Bool}) -> {Nat.add(M.dist(1n+bp, a, h), M.dist(1n+bp, h, j)) == M.dist(1n+bp, a, j) : Nat}:
  +x = M.dist(1n+bp, a, h)
  +y = M.dist(1n+bp, h, j)
  +pj = Equal.trans(Nat, M.pos(1n+bp, a, Nat.add(x, y)), M.pos(1n+bp, M.pos(1n+bp, a, x), y), j, Equal.sym(Nat, M.pos(1n+bp, M.pos(1n+bp, a, x), y), M.pos(1n+bp, a, Nat.add(x, y)), pos_add(bp, a, x, y)), Equal.trans(Nat, M.pos(1n+bp, M.pos(1n+bp, a, x), y), M.pos(1n+bp, h, y), j, Equal.cong(Nat, Nat, w => M.pos(1n+bp, w, y), M.pos(1n+bp, a, x), h, M.pos_dist(bp, a, h, ha, hh)), M.pos_dist(bp, h, j, hh, hj)))
  ds_c(bp, a, h, j, ha, hh, hj, hle, pj, Nat.is_lt(Nat.add(x, y), 1n+bp), {==})

# ---- two writes into a bucket list ----

def bupd_over(+xs: List<&2, B.Bk>, +a: Nat, +u: B.Bk, +v: B.Bk) -> {IM.bupd(IM.bupd(xs, a, u), a, v) == IM.bupd(xs, a, v) : List<&2, B.Bk>}:
  match xs a:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+p:
      Equal.cong(List<&2, B.Bk>, List<&2, B.Bk>, z => Con{c, z}, IM.bupd(IM.bupd(t, p, u), p, v), IM.bupd(t, p, v), bupd_over(t, p, u, v))

def bupd_comm(+xs: List<&2, B.Bk>, +a: Nat, +b: Nat, +u: B.Bk, +v: B.Bk, +hne: {Nat.is_eq(a, b) == False{} : Bool}) -> {IM.bupd(IM.bupd(xs, a, u), b, v) == IM.bupd(IM.bupd(xs, b, v), a, u) : List<&2, B.Bk>}:
  match xs a b:
    case Nil{} _ _:
      {==}
    case Con{c, t} 0n 0n:
      Empty.absurd({IM.bupd(IM.bupd(Con{c, t}, 0n, u), 0n, v) == IM.bupd(IM.bupd(Con{c, t}, 0n, v), 0n, u) : List<&2, B.Bk>}, L.true_false(hne))
    case Con{c, t} 0n 1n+q:
      {==}
    case Con{c, t} 1n+p 0n:
      {==}
    case Con{c, t} 1n+p 1n+q:
      Equal.cong(List<&2, B.Bk>, List<&2, B.Bk>, z => Con{c, z}, IM.bupd(IM.bupd(t, p, u), q, v), IM.bupd(IM.bupd(t, q, v), p, u), bupd_comm(t, p, q, u, v, hne))

def len_bupd(+xs: List<&2, B.Bk>, +a: Nat, +u: B.Bk) -> {SC.length(B.Bk, IM.bupd(xs, a, u)) == SC.length(B.Bk, xs) : Nat}:
  match xs a:
    case Nil{} _:
      {==}
    case Con{c, t} 0n:
      {==}
    case Con{c, t} 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, SC.length(B.Bk, IM.bupd(t, p, u)), SC.length(B.Bk, t), len_bupd(t, p, u))
