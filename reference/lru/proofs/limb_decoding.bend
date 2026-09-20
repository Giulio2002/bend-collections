import Base
import ../src/wide.bend as W
import ../spec/numeric.bend as S
import ./numeric.bend as N

# Mathematical interpretation of the two primitive U32 values returned by the
# actual decoder. This does not assume or model JavaScript BigInt conversion.
def repack(pair: U32 & U32) -> Word(64n):
  (low, high) = pair
  W.pack(low, high)

def value(pair: U32 & U32) -> Nat:
  (low, high) = pair
  Nat.add(U32.to_nat(low), S.scale_binary(32n, U32.to_nat(high)))

def repack_parts(parts: W.Parts<32n, 32n>) -> {repack(W.limbs(parts)) == N.rejoin(32n, 32n, parts) : Word(64n)}:
  W.Split{low, high} = parts
  {==}

# Both directions of the native limb conversion now hold for all 64-bit words.
def decode_encode(+word: Word(64n)) -> {repack(W.unpack(word)) == word : Word(64n)}:
  Equal.trans(Word(64n), repack(W.unpack(word)), N.rejoin(32n, 32n, W.split(32n, 32n, word)), word, repack_parts(W.split(32n, 32n, word)), N.join_split(32n, 32n, word))

def repack_value(pair: U32 & U32) -> {S.unsigned(64n, repack(pair)) == value(pair) : Nat}:
  (low, high) = pair
  N.pack_interpretation(low, high)

def decoded_value(+word: Word(64n)) -> {value(W.unpack(word)) == S.unsigned(64n, word) : Nat}:
  Equal.trans(Nat, value(W.unpack(word)), S.unsigned(64n, repack(W.unpack(word))), S.unsigned(64n, word), Equal.sym(Nat, S.unsigned(64n, repack(W.unpack(word))), value(W.unpack(word)), repack_value(W.unpack(word))), Equal.cong(Word(64n), Nat, w => S.unsigned(64n, w), repack(W.unpack(word)), word, decode_encode(word)))

# Decoder equality cannot collapse distinct native words.
def decode_injective(+a: Word(64n), +b: Word(64n), same: {W.unpack(a) == W.unpack(b) : U32 & U32}) -> {a == b : Word(64n)}:
  Equal.trans(Word(64n), a, repack(W.unpack(a)), b, Equal.sym(Word(64n), repack(W.unpack(a)), a, decode_encode(a)), Equal.trans(Word(64n), repack(W.unpack(a)), repack(W.unpack(b)), b, Equal.cong(U32 & U32, Word(64n), repack, W.unpack(a), W.unpack(b), same), decode_encode(b)))
