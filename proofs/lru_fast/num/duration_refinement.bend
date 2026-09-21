import Base
# Ported from reference/lru/proofs/duration_refinement.bend (unchanged proof text; imports retargeted to
# the natively compilable copies src/lru/{wide,time}.bend, types/lru_model.bend
# and spec/lru_{numeric,unsigned_division}.bend).
import ../../../src/lru/wide.bend as W
import ../../../src/lru/time.bend as Time
import ../../../spec/lru_numeric.bend as S
import ../../../types/lru_model.bend as T
import ./signed_division.bend as Signed
import ./numeric.bend as Numeric
import ./modular_addition.bend as Addition

def milliseconds(ns: T.Int64) -> {Time.milliseconds(ns) == S.milliseconds(ns) : T.Int64}:
  match ns:
    case T.I64{+word}:
      %Equal.sym(Bool, S.negative(word), W.last(64n, word), Numeric.sign_threshold_correspondence(63n, word)) : {T.I64{W.milliseconds(word)} == T.I64{S.quotient_signed(word, _)} : T.Int64}
      Equal.cong(Word(64n), T.Int64, w => T.I64{w}, W.milliseconds(word), S.quotient_signed(word, W.last(64n, word)), Signed.branch(word, W.last(64n, word), {==}))

def choose(+now: T.Int64, +ns: T.Int64, immortal: Bool) -> {Time.deadline_choose(now, ns, immortal) == S.expiry_choose(now, ns, immortal) : T.Int64}:
  match immortal:
    case True{}: {==}
    case False{}:
      Equal.trans(T.Int64, Time.add(now, Time.milliseconds(ns)), S.add(now, Time.milliseconds(ns)), S.add(now, S.milliseconds(ns)), Addition.time_add_refines(now, Time.milliseconds(ns)), Equal.cong(T.Int64, T.Int64, duration => S.add(now, duration), Time.milliseconds(ns), S.milliseconds(ns), milliseconds(ns)))

# All 64-bit durations and samples, including minimum signed duration, wrapped
# sums, sub-millisecond truncation, and the original zero sentinel. No bounds or
# successful-conversion premises are imposed on native bit-pattern inputs.
def deadline(+now: T.Int64, ns: T.Int64) -> {Time.deadline(now, ns) == S.deadline(now, ns) : T.Int64}:
  match ns:
    case T.I64{+word}:
      %Equal.sym(Bool, S.zero(word), W.is_zero(64n, word), Numeric.zero_comparison_correspondence(64n, word)) : {Time.deadline(now, T.I64{word}) == S.expiry_choose(now, T.I64{word}, _) : T.Int64}
      choose(now, T.I64{word}, W.is_zero(64n, word))
