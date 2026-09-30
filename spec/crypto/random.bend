import Base
import ../../src/math/u64.bend as W
import ../../src/math/w64.bend as X
import ../../src/math/random/chacha8.bend as C8
import ../../src/math/random/chacha8/block.bend as B
import ../../src/math/random/rand.bend as R
import ../../src/crypto/random.bend as CR
import ../math/w64.bend as SW
import ../math/random/source.bend as SRC
import ../math/random/chacha8rand.bend as SC
import ../math/random/rand.bend as SR
import ../math/random.bend as SRM

# The contract of src/crypto/random.bend: the ChaCha8Rand generator of
# math/random (C2SP chacha8rand) with Go's ChaCha8.Read byte order, each
# clause proved for every input in proofs/crypto/random/proof.bend.
#
#   Random.stream       the 64-bit outputs of the generator keyed by eight
#                       words are C2SP's stream keyed by them
#   Random.seeded       new(seed) is None unless the seed is 32 bytes below
#                       256, and otherwise outputs the stream of its words
#   Random.bytes        bytes(g, n) are the first n of: the pending bytes,
#                       then the little-endian bytes of the next outputs
#                       (Go's binary.LittleEndian.PutUint64, as ChaCha8.Read)
#   Random.bytes_lt     every byte is below 256 (when the pending ones are)
#   Random.uint_below   uint_below(g, n) < n for n > 0
#   Random.shuffle      shuffle(g, items) is a permutation of items
#
# Security properties (indistinguishability from uniform, forward secrecy)
# are properties of ChaCha8 and of the C2SP key erasure, not of this code;
# see the module header and docs/CRYPTO_CONTRACTS.md.

# Go's byte(v >> k)
def byte_of(+w: U32, +k: Nat) -> U32:
  U32.and(U32.shrn(w, k), 255)

# Go's binary.LittleEndian.PutUint64
def le_bytes(x: W.U64) -> List<&2, U32>:
  match x:
    case W.U64{+l, +h}:
      [byte_of(l, 0n), byte_of(l, 8n), byte_of(l, 16n), byte_of(l, 24n), byte_of(h, 0n), byte_of(h, 8n), byte_of(h, 16n), byte_of(h, 24n)]

def append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      Con{x, append(rest, ys)}

# the bytes of consecutive outputs
def flat(xs: List<&2, W.U64>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      append(le_bytes(x), flat(rest))

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      []
    case 1n+p Nil{}:
      []
    case 1n+p Con{x, rest}:
      Con{x, take(p, rest)}

def below256(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(U32.is_lt(x, 256), below256(rest))

def fst_bytes(-G: Data, r: List<&2, U32> & G) -> List<&2, U32>:
  (bs, g) = r
  bs

def map_outputs(+n: Nat, m: Maybe<&2, CR.Gen>) -> Maybe<&2, List<&2, W.U64>>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{SRC.outputs(~CR.Gen, ~CR.next, n, g)}

def Random.stream(+n: Nat, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32) -> Type:
  {SRC.outputs(~CR.Gen, ~CR.next, n, CR.of_words(k0, k1, k2, k3, k4, k5, k6, k7)) == SC.stream(n, [k0, k1, k2, k3, k4, k5, k6, k7]) : List<&2, W.U64>}

def Random.seeded(+n: Nat, +seed: List<&2, U32>) -> Type:
  {map_outputs(n, CR.new(seed)) == SRM.map_stream(n, SC.key_of_seed(seed)) : Maybe<&2, List<&2, W.U64>>}

def Random.bytes(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>) -> Type:
  {fst_bytes(CR.Gen, CR.bytes(CR.G{c, p}, n)) == take(n, append(p, flat(SRC.outputs(~C8.ChaCha8, ~C8.next, n, c)))) : List<&2, U32>}

def Random.bytes_lt(+n: Nat, +c: C8.ChaCha8, +p: List<&2, U32>, +hp: {below256(p) == True{} : Bool}) -> Type:
  {below256(fst_bytes(CR.Gen, CR.bytes(CR.G{c, p}, n))) == True{} : Bool}

def Random.uint_below(+g: CR.Gen, +n: W.U64, +hn: {X.is_zero(n) == False{} : Bool}) -> Type:
  {Nat.is_lt(SW.value(R.fst(W.U64, CR.Gen, CR.uint_below(g, n))), SW.value(n)) == True{} : Bool}

def Random.shuffle(~A: Data, ~V: Data, ~rel: A -> V -> Bool, +g: CR.Gen, +items: List<&2, A>, +v: V) -> Type:
  {SR.occurrences(~A, ~V, ~rel, v, R.fst(List<&2, A>, CR.Gen, CR.shuffle(~A, g, items))) == SR.occurrences(~A, ~V, ~rel, v, items) : Nat}
