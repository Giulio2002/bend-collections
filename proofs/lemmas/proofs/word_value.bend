import Base
import ../spec/numeric.bend as S
import ./nat_algebra.bend as A
import ./map_routing.bend as Routing

# Every natural below 2^n is represented exactly by from_nat(n, v): its
# unsigned value is v. Built on the actual Base Nat.divmod definition.
def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+p: le_refl(p)

def le_succ(r: Nat, x: Nat, h: {Nat.is_le(r, x) == True{} : Bool}) -> {Nat.is_le(r, 1n+x) == True{} : Bool}:
  match r x:
    case 0n x0: {==}
    case 1n+rp 0n: Empty.absurd({Nat.is_le(1n+rp, 1n) == True{} : Bool}, Routing.false_true(h))
    case 1n+rp 1n+xp: le_succ(rp, xp, h)

def le_add(m: Nat, +r: Nat) -> {Nat.is_le(r, Nat.add(m, r)) == True{} : Bool}:
  match m:
    case 0n: le_refl(r)
    case 1n++p: le_succ(r, Nat.add(p, r), le_add(p, r))

# (M + r) + (1 + n) == (M + (1 + r)) + n
def shift_count(+m: Nat, +r: Nat, +n: Nat) -> {Nat.add(Nat.add(m, r), 1n+n) == Nat.add(Nat.add(m, 1n+r), n) : Nat}:
  %Equal.sym(Nat, Nat.add(m, 1n+r), 1n+Nat.add(m, r), A.add_succ(m, r)) : {Nat.add(Nat.add(m, r), 1n+n) == Nat.add(_, n) : Nat}
  A.add_succ(Nat.add(m, r), n)

# (M + r) + (1 + n) == ((1+bp) + M + 0) + n when r == bp
def shift_carry(+bp: Nat, +n: Nat, +m: Nat, +r: Nat, inv: {Nat.add(0n, r) == bp : Nat}) -> {Nat.add(Nat.add(m, r), 1n+n) == Nat.add(Nat.add(Nat.add(1n+bp, m), 0n), n) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(1n+bp, m), 0n), Nat.add(1n+bp, m), A.add_zero(Nat.add(1n+bp, m))) : {Nat.add(Nat.add(m, r), 1n+n) == Nat.add(_, n) : Nat}
  %Equal.sym(Nat, Nat.add(0n, r), bp, inv) : {Nat.add(Nat.add(m, _), 1n+n) == 1n+Nat.add(Nat.add(bp, m), n) : Nat}
  %A.add_comm(m, bp) : {Nat.add(Nat.add(m, bp), 1n+n) == 1n+Nat.add(_, n) : Nat}
  A.add_succ(Nat.add(m, bp), n)

def go_equation(bp: Nat, n: Nat, m: Nat, d: Nat, r: Nat) -> Type:
  {Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), n) == Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+bp), Nat.mod.fin(Nat.divmod.go(n, m, d, r))) : Nat} & {Nat.is_le(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), bp) == True{} : Bool}

def bound_zero(+bp: Nat, +m: Nat, +r: Nat, inv: {Nat.add(m, r) == bp : Nat}) -> {Nat.is_le(r, bp) == True{} : Bool}:
  %inv : {Nat.is_le(r, _) == True{} : Bool}
  le_add(m, r)

def extend(+a: Nat, +b: Nat, +c: Nat, -L: Type, pre: {a == b : Nat}, ih: {b == c : Nat} & L) -> {a == c : Nat} & L:
  (eq, le) = ih
  (Equal.trans(Nat, a, b, c, pre, eq), le)

# Invariant of the actual division loop: remaining countdown m plus the running
# remainder r is the divisor minus one.
def go(+bp: Nat, n: Nat, m: Nat, +d: Nat, +r: Nat, +inv: {Nat.add(m, r) == bp : Nat}) -> go_equation(bp, n, m, d, r):
  match n:
    case 0n:
      (A.add_zero(Nat.add(Nat.mul(d, 1n+bp), r)), bound_zero(bp, m, r, inv))
    case 1n++np:
      match m:
        case 0n:
          extend(Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 1n+np), Nat.add(Nat.add(Nat.mul(1n+d, 1n+bp), 0n), np), Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))), {Nat.is_le(Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n)), bp) == True{} : Bool}, shift_carry(bp, np, Nat.mul(d, 1n+bp), r, inv), go(bp, np, r, 1n+d, 0n, Equal.trans(Nat, Nat.add(r, 0n), r, bp, A.add_zero(r), inv)))
        case 1n++mp:
          extend(Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 1n+np), Nat.add(Nat.add(Nat.mul(d, 1n+bp), 1n+r), np), Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Nat.mod.fin(Nat.divmod.go(np, mp, d, 1n+r))), {Nat.is_le(Nat.mod.fin(Nat.divmod.go(np, mp, d, 1n+r)), bp) == True{} : Bool}, shift_count(Nat.mul(d, 1n+bp), r, np), go(bp, np, mp, d, 1n+r, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, A.add_succ(mp, r), inv)))

# v == 2*(v/2) + v%2 and v%2 <= 1, for the actual Nat.divmod.
def half(+v: Nat) -> {Nat.add(Nat.add(Nat.mul(0n, 2n), 0n), v) == Nat.add(Nat.mul(Nat.div(v, 2n), 2n), Nat.mod(v, 2n)) : Nat} & {Nat.is_le(Nat.mod(v, 2n), 1n) == True{} : Bool}:
  go(1n, v, 1n, 0n, 0n, {==})

def remainder_bit(r: Nat, le: {Nat.is_le(r, 1n) == True{} : Bool}) -> {S.bit_value(Nat.is_eq(r, 1n)) == r : Nat}:
  match r:
    case 0n: {==}
    case 1n+x:
      match x:
        case 0n: {==}
        case 1n+y: Empty.absurd({S.bit_value(Nat.is_eq(2n+y, 1n)) == 2n+y : Nat}, Routing.false_true(le))

def not_below_zero(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+p: {==}

def lt_double(q: Nat, x: Nat, +r: Nat, h: {Nat.is_lt(Nat.add(Nat.double(q), r), Nat.double(x)) == True{} : Bool}) -> {Nat.is_lt(q, x) == True{} : Bool}:
  match q x:
    case q0 0n: Empty.absurd({Nat.is_lt(q0, 0n) == True{} : Bool}, Routing.false_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(Nat.double(q0), r), 0n), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.double(q0), r), 0n), False{}, not_below_zero(Nat.add(Nat.double(q0), r))), h)))
    case 0n 1n+xp: {==}
    case 1n+qp 1n+xp: lt_double(qp, xp, r, h)

def two_times(+q: Nat) -> {Nat.mul(q, 2n) == Nat.double(q) : Nat}:
  Equal.trans(Nat, Nat.mul(q, 2n), Nat.mul(2n, q), Nat.double(q), A.mul_comm(q, 2n), Equal.sym(Nat, Nat.double(q), Nat.mul(2n, q), A.double_mul(q)))

# v < 2 * 2^p, rewritten as 2*(v/2) + v%2 < double(2^p)
def rescale(+p: Nat, +v: Nat, eq: {v == Nat.add(Nat.mul(Nat.div(v, 2n), 2n), Nat.mod(v, 2n)) : Nat}, bound: {Nat.is_lt(v, Nat.mul(2n, Nat.pow(2n, p))) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.double(Nat.div(v, 2n)), Nat.mod(v, 2n)), Nat.double(Nat.pow(2n, p))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.double(Nat.pow(2n, p)), Nat.mul(2n, Nat.pow(2n, p)), A.double_mul(Nat.pow(2n, p))) : {Nat.is_lt(Nat.add(Nat.double(Nat.div(v, 2n)), Nat.mod(v, 2n)), _) == True{} : Bool}
  %two_times(Nat.div(v, 2n)) : {Nat.is_lt(Nat.add(_, Nat.mod(v, 2n)), Nat.mul(2n, Nat.pow(2n, p))) == True{} : Bool}
  %eq : {Nat.is_lt(_, Nat.mul(2n, Nat.pow(2n, p))) == True{} : Bool}
  bound

def from_nat_step(+p: Nat, +v: Nat, parts: {v == Nat.add(Nat.mul(Nat.div(v, 2n), 2n), Nat.mod(v, 2n)) : Nat} & {Nat.is_le(Nat.mod(v, 2n), 1n) == True{} : Bool}, bound: {Nat.is_lt(v, Nat.mul(2n, Nat.pow(2n, p))) == True{} : Bool}, ih: @+q: Nat -> @hq: {Nat.is_lt(q, Nat.pow(2n, p)) == True{} : Bool} -> {S.unsigned(p, S.from_nat(p, q)) == q : Nat}) -> {S.unsigned(1n+p, S.from_nat(1n+p, v)) == v : Nat}:
  (+eq, le) = parts
  %Equal.sym(Nat, S.unsigned(p, S.from_nat(p, Nat.div(v, 2n))), Nat.div(v, 2n), ih(Nat.div(v, 2n), lt_double(Nat.div(v, 2n), Nat.pow(2n, p), Nat.mod(v, 2n), rescale(p, v, eq, bound)))) : {Nat.add(S.bit_value(Nat.is_eq(Nat.mod(v, 2n), 1n)), Nat.double(_)) == v : Nat}
  %Equal.sym(Nat, S.bit_value(Nat.is_eq(Nat.mod(v, 2n), 1n)), Nat.mod(v, 2n), remainder_bit(Nat.mod(v, 2n), le)) : {Nat.add(_, Nat.double(Nat.div(v, 2n))) == v : Nat}
  %Equal.sym(Nat, v, Nat.add(Nat.mul(Nat.div(v, 2n), 2n), Nat.mod(v, 2n)), eq) : {Nat.add(Nat.mod(v, 2n), Nat.double(Nat.div(v, 2n))) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.div(v, 2n), 2n), Nat.double(Nat.div(v, 2n)), two_times(Nat.div(v, 2n))) : {Nat.add(Nat.mod(v, 2n), Nat.double(Nat.div(v, 2n))) == Nat.add(_, Nat.mod(v, 2n)) : Nat}
  A.add_comm(Nat.mod(v, 2n), Nat.double(Nat.div(v, 2n)))

def below_one(v: Nat, h: {Nat.is_lt(v, 1n) == True{} : Bool}) -> {0n == v : Nat}:
  match v:
    case 0n: {==}
    case 1n+x:
      match x:
        case 0n: Empty.absurd({0n == 1n : Nat}, Routing.false_true(h))
        case 1n+y: Empty.absurd({0n == 2n+y : Nat}, Routing.false_true(h))

def half_parts(+v: Nat) -> {v == Nat.add(Nat.mul(Nat.div(v, 2n), 2n), Nat.mod(v, 2n)) : Nat} & {Nat.is_le(Nat.mod(v, 2n), 1n) == True{} : Bool}:
  half(v)

def from_nat_value(n: Nat, +v: Nat, h: {Nat.is_lt(v, Nat.pow(2n, n)) == True{} : Bool}) -> {S.unsigned(n, S.from_nat(n, v)) == v : Nat}:
  match n:
    case 0n: below_one(v, h)
    case 1n++p: from_nat_step(p, v, half_parts(v), h, q => hq => from_nat_value(p, q, hq))
