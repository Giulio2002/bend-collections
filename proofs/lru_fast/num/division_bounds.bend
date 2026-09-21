import Base
# Ported from reference/lru/proofs/division_bounds.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../spec/lru_numeric.bend as S
import ./word_bounds.bend as WordBounds
import ../../../reference/lru/proofs/map_routing.bend as Logic
import ../../../reference/lru/proofs/map_difference_order.bend as Order
import ../../../reference/lru/proofs/map_index.bend as Index

# A long-division candidate is less than twice the divisor for either input bit.
def candidate(+r: Nat, +d: Nat, +bit: Bool, bound: {Nat.is_lt(r, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(r)), Nat.double(d)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(Nat.add(S.bit_value(bit), Nat.double(r)), Nat.double(d)), Nat.is_lt(r, d), True{}, WordBounds.doubled_bound(r, d, bit), bound)

def cancel_less(a: Nat, +b: Nat, +c: Nat) -> {Nat.is_lt(Nat.add(a, b), Nat.add(a, c)) == Nat.is_lt(b, c) : Bool}:
  match a:
    case 0n: {==}
    case 1n+p: cancel_less(p, b, c)

def ge_reverse(a: Nat, b: Nat) -> {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p 0n: {==}
    case 1n+p 1n+q: ge_reverse(p, q)

def not_ge(a: Nat, b: Nat, e: {Nat.is_ge(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(Equal.sym(Bool, True{}, False{}, e)))
    case 0n 1n+p: {==}
    case 1n+p 0n: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(Equal.sym(Bool, True{}, False{}, e)))
    case 1n+p 1n+q: not_ge(p, q, e)

# Subtracting the divisor once restores the strict remainder bound.
def subtract_bound(+r: Nat, +d: Nat, inside: {Nat.is_lt(r, Nat.add(d, d)) == True{} : Bool}, enough: {Nat.is_le(d, r) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(r, d), d) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(Nat.sub(r, d), d), Nat.is_lt(Nat.add(d, Nat.sub(r, d)), Nat.add(d, d)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(d, Nat.sub(r, d)), Nat.add(d, d)), Nat.is_lt(Nat.sub(r, d), d), cancel_less(d, Nat.sub(r, d), d)), Equal.trans(Bool, Nat.is_lt(Nat.add(d, Nat.sub(r, d)), Nat.add(d, d)), Nat.is_lt(r, Nat.add(d, d)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.add(d, d)), Nat.add(d, Nat.sub(r, d)), r, Order.add_complement(r, d, enough)), inside))
