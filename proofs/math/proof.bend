import Base
import ../../src/math/u64.bend as U
import ../../src/math/hash.bend as HS
import ../../src/math/pow2.bend as PW
import ../lib/lemmas/spec/numeric.bend as S
import ../lib/lemmas/types/model.bend as T
import ../../spec/lib/common.bend as SC
import ./pow2/pow2.bend as P2
import ./u64/u64.bend as P
import ./u64/u64div.bend as PD
import ../lib/u32div.bend as UD
import ./hash/hash.bend as PH
import ../lib/word.bend as WD
import ../lib/lemmas/proofs/word_addition.bend as WA

# Gate for src/math. Every theorem is against the independent specification
# in proofs/lemmas/spec/numeric.bend (64-bit words, Nat interpretation) or
# against Nat arithmetic; none assumes a hole or an axiom.

# U32 long division (Base's U32.div / U32.mod), every nonzero divisor
def u32_div(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {U32.to_nat(U32.div(a, b)) == Nat.div(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  UD.div_nat(a, b, hb)

def u32_mod(+a: U32, +b: U32, +hb: {U32.is_zero(b) == False{} : Bool}) -> {U32.to_nat(U32.mod(a, b)) == Nat.mod(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  UD.mod_nat(a, b, hb)

# u64
def u64_is_zero(+a: U.U64) -> {U.is_zero(a) == S.zero(P.bits(a)) : Bool}:
  P.is_zero(a)

def u64_le_signed(+a: U.U64, +b: U.U64) -> {U.le_signed(a, b) == S.order(P.bits(a), P.bits(b), S.negative(P.bits(a)), S.negative(P.bits(b))) : Bool}:
  P.le_signed(a, b)

def u64_add(+a: U.U64, +b: U.U64) -> {P.bits(U.add(a, b)) == Word.add(64n, P.bits(a), P.bits(b)) : Word(64n)}:
  P.add(a, b)

def u64_add_spec(+a: U.U64, +b: U.U64) -> {T.I64{P.bits(U.add(a, b))} == S.add(T.I64{P.bits(a)}, T.I64{P.bits(b)}) : T.Int64}:
  Equal.cong(Word(64n), T.Int64, z => T.I64{z}, P.bits(U.add(a, b)), S.from_nat(64n, Nat.add(S.unsigned(64n, P.bits(a)), S.unsigned(64n, P.bits(b)))), Equal.trans(Word(64n), P.bits(U.add(a, b)), Word.add(64n, P.bits(a), P.bits(b)), S.from_nat(64n, Nat.add(S.unsigned(64n, P.bits(a)), S.unsigned(64n, P.bits(b)))), P.add(a, b), WA.refines(64n, P.bits(a), P.bits(b))))

def u64_neg(+a: U.U64) -> {P.bits(U.neg(a)) == Word.inc(64n, Word.not(64n, P.bits(a))) : Word(64n)}:
  P.neg(a)

def u64_div_small(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> {P.bits(U.div_small(a, d)) == S.unsigned_quotient(64n, P.bits(a), d) : Word(64n)}:
  PD.div_bits(a, d, hd0, hle)

def u64_div_small_signed(+a: U.U64, +d: U32, +hd0: {U32.is_zero(d) == False{} : Bool}, +hle: {U32.is_le(d, 1048576) == True{} : Bool}) -> {P.bits(U.div_small_signed(a, d)) == PD.qs(P.bits(a), S.negative(P.bits(a)), d) : Word(64n)}:
  PD.div_signed(a, d, hd0, hle)

def u64_milliseconds(+a: U.U64) -> {T.I64{P.bits(U.div_small_signed(a, 1000000))} == S.milliseconds(T.I64{P.bits(a)}) : T.Int64}:
  PD.milliseconds(a)

# hash
def hash_bucket_le(+w: U32, +mask: U32) -> {Nat.is_le(U32.to_nat(HS.bucket(w, mask)), U32.to_nat(mask)) == True{} : Bool}:
  PH.bucket_le(w, mask)

def hash_bucket_lt(+w: U32, +k: Nat, +mask: U32, +hm: {mask == U32{WD.mask(32n, k)} : U32}) -> {Nat.is_lt(U32.to_nat(HS.bucket(w, mask)), S.scale_binary(k, 1n)) == True{} : Bool}:
  PH.bucket_lt(w, k, mask, hm)

# pow2
def pow2(+d: Nat) -> {PW.pow2t(d) == SC.pow2(d) : Nat}:
  P2.same(d)
