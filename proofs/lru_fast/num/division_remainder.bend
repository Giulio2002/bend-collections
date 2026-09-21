import Base
# Ported from reference/lru/proofs/division_remainder.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../reference/lru/proofs/map_difference_order.bend as Order
import ../../../src/lru/wide.bend as W
import ./division_no_overflow.bend as Overflow
import ./word_comparison.bend as Compare
import ./subtraction_bounds.bend as Sub
import ./division_bounds.bend as Bounds
import ./natural_products.bend as Product

# General U32 subtraction branch; comparison and decoded subtraction are both
# justified by the actual Base definitions, and the input range is explicit.
def subtract(+r: U32, +d: U32, above: {U32.is_ge(r, d) == True{} : Bool}, below: {Nat.is_lt(U32.to_nat(r), Nat.double(U32.to_nat(d))) == True{} : Bool}) -> {U32.is_lt(U32.sub(r, d), d) == True{} : Bool}:
  +enough = Equal.trans(Bool, Nat.is_le(U32.to_nat(d), U32.to_nat(r)), Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), True{}, Equal.sym(Bool, Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), Nat.is_le(U32.to_nat(d), U32.to_nat(r)), Bounds.ge_reverse(U32.to_nat(r), U32.to_nat(d))), Equal.trans(Bool, Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), U32.is_ge(r, d), True{}, Equal.sym(Bool, U32.is_ge(r, d), Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), Compare.u32_ge(r, d)), above))
  inside = Equal.trans(Bool, Nat.is_lt(U32.to_nat(r), Nat.add(U32.to_nat(d), U32.to_nat(d))), Nat.is_lt(U32.to_nat(r), Nat.double(U32.to_nat(d))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(U32.to_nat(r), x), Nat.add(U32.to_nat(d), U32.to_nat(d)), Nat.double(U32.to_nat(d)), Equal.sym(Nat, Nat.double(U32.to_nat(d)), Nat.add(U32.to_nat(d), U32.to_nat(d)), Product.double_sum(U32.to_nat(d)))), below)
  Equal.trans(Bool, U32.is_lt(U32.sub(r, d), d), Nat.is_lt(U32.to_nat(U32.sub(r, d)), U32.to_nat(d)), True{}, Compare.u32_lt(U32.sub(r, d), d), Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(r, d)), U32.to_nat(d)), Nat.is_lt(Nat.sub(U32.to_nat(r), U32.to_nat(d)), U32.to_nat(d)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, U32.to_nat(d)), U32.to_nat(U32.sub(r, d)), Nat.sub(U32.to_nat(r), U32.to_nat(d)), Sub.u32_exact(r, d, enough)), Bounds.subtract_bound(U32.to_nat(r), U32.to_nat(d), inside, enough)))

def subtract_native(+r: U32, +d: U32, high: {W.last(32n, Overflow.bits(d)) == False{} : Bool}, above: {U32.is_ge(r, d) == True{} : Bool}, below: {U32.is_lt(r, U32.shl(d)) == True{} : Bool}) -> {U32.is_lt(U32.sub(r, d), d) == True{} : Bool}:
  subtract(r, d, above, Equal.trans(Bool, Nat.is_lt(U32.to_nat(r), Nat.double(U32.to_nat(d))), Nat.is_lt(U32.to_nat(r), U32.to_nat(U32.shl(d))), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(U32.to_nat(r), x), Nat.double(U32.to_nat(d)), U32.to_nat(U32.shl(d)), Equal.sym(Nat, U32.to_nat(U32.shl(d)), Nat.double(U32.to_nat(d)), Overflow.double_value(d, high))), Equal.trans(Bool, Nat.is_lt(U32.to_nat(r), U32.to_nat(U32.shl(d))), U32.is_lt(r, U32.shl(d)), True{}, Equal.sym(Bool, U32.is_lt(r, U32.shl(d)), Nat.is_lt(U32.to_nat(r), U32.to_nat(U32.shl(d))), Compare.u32_lt(r, U32.shl(d))), below)))

# Concrete executed subtraction restores the native remainder bound.
def million(+r: U32, above: {U32.is_ge(r, 1000000) == True{} : Bool}, below: {U32.is_lt(r, 2000000) == True{} : Bool}) -> {U32.is_lt(U32.sub(r, 1000000), 1000000) == True{} : Bool}:
  subtract_native(r, 1000000, {==}, above, below)

def subtraction_conservation(+r: U32, +d: U32, above: {U32.is_ge(r, d) == True{} : Bool}) -> {U32.to_nat(r) == Nat.add(U32.to_nat(d), U32.to_nat(U32.sub(r, d))) : Nat}:
  +enough = Equal.trans(Bool, Nat.is_le(U32.to_nat(d), U32.to_nat(r)), Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), True{}, Equal.sym(Bool, Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), Nat.is_le(U32.to_nat(d), U32.to_nat(r)), Bounds.ge_reverse(U32.to_nat(r), U32.to_nat(d))), Equal.trans(Bool, Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), U32.is_ge(r, d), True{}, Equal.sym(Bool, U32.is_ge(r, d), Nat.is_ge(U32.to_nat(r), U32.to_nat(d)), Compare.u32_ge(r, d)), above))
  Equal.trans(Nat, U32.to_nat(r), Nat.add(U32.to_nat(d), Nat.sub(U32.to_nat(r), U32.to_nat(d))), Nat.add(U32.to_nat(d), U32.to_nat(U32.sub(r, d))), Equal.sym(Nat, Nat.add(U32.to_nat(d), Nat.sub(U32.to_nat(r), U32.to_nat(d))), U32.to_nat(r), Order.add_complement(U32.to_nat(r), U32.to_nat(d), enough)), Equal.cong(Nat, Nat, x => Nat.add(U32.to_nat(d), x), Nat.sub(U32.to_nat(r), U32.to_nat(d)), U32.to_nat(U32.sub(r, d)), Equal.sym(Nat, U32.to_nat(U32.sub(r, d)), Nat.sub(U32.to_nat(r), U32.to_nat(d)), Sub.u32_exact(r, d, enough))))
