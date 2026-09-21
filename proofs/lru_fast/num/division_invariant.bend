import Base
# Ported from reference/lru/proofs/division_invariant.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../src/lru/wide.bend as W
import ./division_candidate_bound.bend as Candidate
import ./division_remainder.bend as Remainder
import ../../../reference/lru/proofs/map_routing.bend as Logic

def remainder(-n: Nat, result: W.Division<n>) -> U32:
  W.Div{q, r} = result
  r

def not_ge(c: Cmp, e: {Cmp.is_ge(c) == False{} : Bool}) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}: {==}
    case EQ{}: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(Equal.sym(Bool, True{}, False{}, e)))
    case GT{}: Empty.absurd({False{} == True{} : Bool}, Logic.false_true(Equal.sym(Bool, True{}, False{}, e)))

# Both branches refer to actual wide.digit_result, not a proof-side divider.
def result(+p: Nat, q: Word(p), +r: U32, flag: Bool, chosen: {U32.is_ge(r, 1000000) == flag : Bool}, bound: {U32.is_lt(r, 2000000) == True{} : Bool}) -> {U32.is_lt(remainder(1n+p, W.digit_result(p, q, r, flag)), 1000000) == True{} : Bool}:
  match flag:
    case False{}:
      not_ge(U32.cmp(r, 1000000), chosen)
    case True{}:
      Remainder.million(r, chosen, bound)

def compare(+p: Nat, +q: Word(p), +r: U32, bound: {U32.is_lt(r, 2000000) == True{} : Bool}) -> {U32.is_lt(remainder(1n+p, W.digit_compare(p, q, r)), 1000000) == True{} : Bool}:
  result(p, q, r, U32.is_ge(r, 1000000), {==}, bound)

def digit(+p: Nat, +bit: Bool, prior: W.Division<p>, bound: {U32.is_lt(remainder(p, prior), 1000000) == True{} : Bool}) -> {U32.is_lt(remainder(1n+p, W.digit(p, bit, prior)), 1000000) == True{} : Bool}:
  match prior:
    case W.Div{q, +r}:
      compare(p, q, U32.add(U32.mul(r, 2), W.bit_u32(bit)), Candidate.million(r, bit, bound))

# Every recursively reached remainder of the executed divider is strictly below
# the divisor, for arbitrary widths and inputs. No reachable-range premise.
def bounded(+n: Nat, word: Word(n)) -> {U32.is_lt(remainder(n, W.div_million(n, word)), 1000000) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match word:
        case WCon{+bit, +tail}:
          digit(p, bit, W.div_million(p, tail), bounded(p, tail))
