import Base
import ./map_index.bend as Index
import ./native_map.bend as N

# Complete one period of the existing Base countdown division. The remaining
# input n is arbitrary; this does not enumerate durations or replace division.
def period(m: Nat, +n: Nat, +q: Nat, +r: Nat) -> {Nat.divmod.go(Nat.add(1n+m, n), m, q, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+q, 0n) : Nat & Nat}:
  match m:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(1n+p, n), p, q, 1n+r), Nat.divmod.go(n, Nat.add(p, 1n+r), 1n+q, 0n), Nat.divmod.go(n, 1n+Nat.add(p, r), 1n+q, 0n), period(p, n, q, 1n+r), Equal.cong(Nat, Nat & Nat, k => Nat.divmod.go(n, k, 1n+q, 0n), Nat.add(p, 1n+r), 1n+Nat.add(p, r), Index.add_right_successor(p, r)))

def stride(+d: Nat, +n: Nat) -> {Nat.divmod(Nat.add(1n+d, n), 1n+d) == Index.next_quotient(Nat.divmod(n, 1n+d)) : Nat & Nat}:
  Equal.trans(Nat & Nat, Nat.divmod(Nat.add(1n+d, n), 1n+d), Nat.divmod.go(n, Nat.add(d, 0n), 1n, 0n), Index.next_quotient(Nat.divmod(n, 1n+d)), period(d, n, 0n, 0n), Equal.trans(Nat & Nat, Nat.divmod.go(n, Nat.add(d, 0n), 1n, 0n), Nat.divmod.go(n, d, 1n, 0n), Index.next_quotient(Nat.divmod(n, 1n+d)), Equal.cong(Nat, Nat & Nat, k => Nat.divmod.go(n, k, 1n, 0n), Nat.add(d, 0n), d, N.natural_add_right_zero(d)), Index.quotient_translation(n, d, 0n, 0n)))

def small(+r: Nat, +d: Nat, bound: {Nat.is_le(r, d) == True{} : Bool}) -> {Nat.divmod(r, 1n+d) == (0n, r) : Nat & Nat}:
  Equal.trans(Nat & Nat, Nat.divmod(r, 1n+d), (0n, Nat.add(r, 0n)), (0n, r), Index.division_no_wrap(r, d, 0n, 0n, bound), Equal.cong(Nat, Nat & Nat, n => (0n, n), Nat.add(r, 0n), r, N.natural_add_right_zero(r)))

# Euclidean decomposition is recognized by actual Base Nat.divmod for every
# positive divisor and arbitrary quotient, from the mathematical remainder bound.
def decomposition(q: Nat, +d: Nat, +r: Nat, bound: {Nat.is_le(r, d) == True{} : Bool}) -> {Nat.divmod(Nat.add(Nat.mul(q, 1n+d), r), 1n+d) == (q, r) : Nat & Nat}:
  match q:
    case 0n:
      small(r, d, bound)
    case 1n+ +p:
      %N.natural_add_associative(1n+d, Nat.mul(p, 1n+d), r) : {Nat.divmod(_, 1n+d) == (1n+p, r) : Nat & Nat}
      Equal.trans(Nat & Nat, Nat.divmod(Nat.add(1n+d, Nat.add(Nat.mul(p, 1n+d), r)), 1n+d), Index.next_quotient(Nat.divmod(Nat.add(Nat.mul(p, 1n+d), r), 1n+d)), (1n+p, r), stride(d, Nat.add(Nat.mul(p, 1n+d), r)), Equal.cong(Nat & Nat, Nat & Nat, Index.next_quotient, Nat.divmod(Nat.add(Nat.mul(p, 1n+d), r), 1n+d), (p, r), decomposition(p, d, r, bound)))

# Quotient and remainder projections used by the independent duration model.
def quotient(+q: Nat, +d: Nat, +r: Nat, bound: {Nat.is_le(r, d) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(q, 1n+d), r), 1n+d) == q : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.div.fin, Nat.divmod(Nat.add(Nat.mul(q, 1n+d), r), 1n+d), (q, r), decomposition(q, d, r, bound))

def remainder(+q: Nat, +d: Nat, +r: Nat, bound: {Nat.is_le(r, d) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+d), r), 1n+d) == r : Nat}:
  Equal.cong(Nat & Nat, Nat, Nat.mod.fin, Nat.divmod(Nat.add(Nat.mul(q, 1n+d), r), 1n+d), (q, r), decomposition(q, d, r, bound))
