import Base
# Ported from reference/lru/proofs/division_value.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../src/lru/wide.bend as W
import ../../../spec/lru_numeric.bend as S
import ./division_remainder.bend as Rem
import ./division_no_overflow.bend as Overflow
import ./division_invariant.bend as Inv
import ./division_candidate_bound.bend as Bound
import ./natural_products.bend as P
import ../../../reference/lru/proofs/native_map.bend as Natural
import ./numeric.bend as Numeric
import ../../../reference/lru/proofs/map_index.bend as Index

# A mathematical observation of the actual returned quotient and remainder.
def value(+n: Nat, result: W.Division<n>, d: U32) -> Nat:
  W.Div{q, r} = result
  Nat.add(Nat.mul(S.unsigned(n, q), U32.to_nat(d)), U32.to_nat(r))

def selected(+r: U32, d: U32, flag: Bool) -> U32:
  match flag:
    case False{}: r
    case True{}: U32.sub(r, d)

def selection_value(+r: U32, +d: U32, flag: Bool, chosen: {U32.is_ge(r, d) == flag : Bool}) -> {U32.to_nat(r) == Nat.add(Nat.mul(S.bit_value(flag), U32.to_nat(d)), U32.to_nat(selected(r, d, flag))) : Nat}:
  match flag:
    case False{}: {==}
    case True{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(d), 0n), U32.to_nat(d), Natural.natural_add_right_zero(U32.to_nat(d))) : {U32.to_nat(r) == Nat.add(_, U32.to_nat(U32.sub(r, d))) : Nat}
      Rem.subtraction_conservation(r, d, chosen)

# Normal form of the actual helper; the denominator identity is explicit.
def result_form(+p: Nat, +q: Word(p), +r: U32, +d: U32, flag: Bool, same: {d == 1000000 : U32}) -> {W.digit_result(p, q, r, flag) == W.Div{WCon{flag, q}, selected(r, d, flag)} : W.Division<1n+p>}:
  match flag:
    case False{}: {==}
    case True{}:
      Equal.cong(U32, W.Division<1n+p>, x => W.Div{WCon{True{}, q}, U32.sub(r, x)}, 1000000, d, Equal.sym(U32, d, 1000000, same))

def weight_step(+q: Nat, +d: Nat, +r: Nat, flag: Bool) -> {Nat.add(Nat.mul(Nat.add(S.bit_value(flag), Nat.double(q)), d), r) == Nat.add(Nat.mul(Nat.double(q), d), Nat.add(Nat.mul(S.bit_value(flag), d), r)) : Nat}:
  match flag:
    case False{}: {==}
    case True{}:
      %Equal.sym(Nat, Nat.add(d, 0n), d, Natural.natural_add_right_zero(d)) : {Nat.add(Nat.add(d, Nat.mul(Nat.double(q), d)), r) == Nat.add(Nat.mul(Nat.double(q), d), Nat.add(_, r)) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(d, Nat.mul(Nat.double(q), d)), r), Nat.add(d, Nat.add(Nat.mul(Nat.double(q), d), r)), Nat.add(Nat.mul(Nat.double(q), d), Nat.add(d, r)), Equal.sym(Nat, Nat.add(d, Nat.add(Nat.mul(Nat.double(q), d), r)), Nat.add(Nat.add(d, Nat.mul(Nat.double(q), d)), r), Natural.natural_add_associative(d, Nat.mul(Nat.double(q), d), r)), P.interchange(d, Nat.mul(Nat.double(q), d), r))

def result_value(+p: Nat, +q: Word(p), +r: U32, +d: U32, +flag: Bool, +same: {d == 1000000 : U32}, chosen: {U32.is_ge(r, 1000000) == flag : Bool}) -> {value(1n+p, W.digit_result(p, q, r, flag), d) == Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), U32.to_nat(r)) : Nat}:
  decision = Equal.trans(Bool, U32.is_ge(r, d), U32.is_ge(r, 1000000), flag, Equal.cong(U32, Bool, x => U32.is_ge(r, x), d, 1000000, same), chosen)
  Equal.trans(Nat, value(1n+p, W.digit_result(p, q, r, flag), d), Nat.add(Nat.mul(Nat.add(S.bit_value(flag), Nat.double(S.unsigned(p, q))), U32.to_nat(d)), U32.to_nat(selected(r, d, flag))), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), U32.to_nat(r)), Equal.cong(W.Division<1n+p>, Nat, x => value(1n+p, x, d), W.digit_result(p, q, r, flag), W.Div{WCon{flag, q}, selected(r, d, flag)}, result_form(p, q, r, d, flag, same)), Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(S.bit_value(flag), Nat.double(S.unsigned(p, q))), U32.to_nat(d)), U32.to_nat(selected(r, d, flag))), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), Nat.add(Nat.mul(S.bit_value(flag), U32.to_nat(d)), U32.to_nat(selected(r, d, flag)))), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), U32.to_nat(r)), weight_step(S.unsigned(p, q), U32.to_nat(d), U32.to_nat(selected(r, d, flag)), flag), Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), x), Nat.add(Nat.mul(S.bit_value(flag), U32.to_nat(d)), U32.to_nat(selected(r, d, flag))), U32.to_nat(r), Equal.sym(Nat, U32.to_nat(r), Nat.add(Nat.mul(S.bit_value(flag), U32.to_nat(d)), U32.to_nat(selected(r, d, flag))), selection_value(r, d, flag, decision)))))

def gather(+q: Nat, +r: Nat, bit: Bool) -> {Nat.add(Nat.double(q), Nat.add(S.bit_value(bit), Nat.double(r))) == Nat.add(S.bit_value(bit), Nat.double(Nat.add(q, r))) : Nat}:
  match bit:
    case False{}:
      Equal.sym(Nat, Nat.double(Nat.add(q, r)), Nat.add(Nat.double(q), Nat.double(r)), Numeric.double_add(q, r))
    case True{}:
      Equal.trans(Nat, Nat.add(Nat.double(q), 1n+Nat.double(r)), 1n+Nat.add(Nat.double(q), Nat.double(r)), 1n+Nat.double(Nat.add(q, r)), Index.add_right_successor(Nat.double(q), Nat.double(r)), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.double(q), Nat.double(r)), Nat.double(Nat.add(q, r)), Equal.sym(Nat, Nat.double(Nat.add(q, r)), Nat.add(Nat.double(q), Nat.double(r)), Numeric.double_add(q, r))))

def digit(+p: Nat, +bit: Bool, prior: W.Division<p>, +d: U32, same: {d == 1000000 : U32}, bound: {U32.is_lt(Inv.remainder(p, prior), 1000000) == True{} : Bool}) -> {value(1n+p, W.digit(p, bit, prior), d) == Nat.add(S.bit_value(bit), Nat.double(value(p, prior, d))) : Nat}:
  match prior:
    case W.Div{+q, +r}:
      Equal.trans(Nat, value(1n+p, W.digit(p, bit, W.Div{q, r}), d), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit)))), Nat.add(S.bit_value(bit), Nat.double(Nat.add(Nat.mul(S.unsigned(p, q), U32.to_nat(d)), U32.to_nat(r)))), result_value(p, q, U32.add(U32.mul(r, 2), W.bit_u32(bit)), d, U32.is_ge(U32.add(U32.mul(r, 2), W.bit_u32(bit)), 1000000), same, {==}), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit)))), Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r)))), Nat.add(S.bit_value(bit), Nat.double(Nat.add(Nat.mul(S.unsigned(p, q), U32.to_nat(d)), U32.to_nat(r)))), Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), x), U32.to_nat(U32.add(U32.mul(r, 2), W.bit_u32(bit))), Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r))), Overflow.candidate_value(r, bit, Bound.lt_le(U32.cmp(r, 1000000), bound))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r)))), Nat.add(Nat.double(Nat.mul(S.unsigned(p, q), U32.to_nat(d))), Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r)))), Nat.add(S.bit_value(bit), Nat.double(Nat.add(Nat.mul(S.unsigned(p, q), U32.to_nat(d)), U32.to_nat(r)))), Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(S.bit_value(bit), Nat.double(U32.to_nat(r)))), Nat.mul(Nat.double(S.unsigned(p, q)), U32.to_nat(d)), Nat.double(Nat.mul(S.unsigned(p, q), U32.to_nat(d))), P.double_product(S.unsigned(p, q), U32.to_nat(d))), gather(Nat.mul(S.unsigned(p, q), U32.to_nat(d)), U32.to_nat(r), bit))))

# The denominator is a symbolic U32 identified with the actual fixed divisor;
# the proof observes the actual execution and discharges each recursive bound.
def conservation(+n: Nat, word: Word(n), +d: U32, +same: {d == 1000000 : U32}) -> {value(n, W.div_million(n, word), d) == S.unsigned(n, word) : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          Equal.trans(Nat, value(1n+p, W.digit(p, bit, W.div_million(p, tail)), d), Nat.add(S.bit_value(bit), Nat.double(value(p, W.div_million(p, tail), d))), Nat.add(S.bit_value(bit), Nat.double(S.unsigned(p, tail))), digit(p, bit, W.div_million(p, tail), d, same, Inv.bounded(p, tail)), Equal.cong(Nat, Nat, x => Nat.add(S.bit_value(bit), Nat.double(x)), value(p, W.div_million(p, tail), d), S.unsigned(p, tail), conservation(p, tail, d, same)))

# Public native divisor identity is discharged here, with no external premise.
def actual(+n: Nat, word: Word(n)) -> {value(n, W.div_million(n, word), 1000000) == S.unsigned(n, word) : Nat}:
  conservation(n, word, 1000000, {==})
