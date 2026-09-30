import Base
import ../../src/crypto/hash.bend as Hash
import ../../src/crypto/subtle.bend as Subtle
import ../../src/crypto/sha/sha256.bend as S256
import ../../src/crypto/sha/packed/sha256.bend as P256
import ../../src/crypto/sha512/sha512.bend as S512
import ../../src/crypto/sha3/sha3_256.bend as S3
import ../../src/crypto/keccak/keccak.bend as KK
import ../../src/crypto/keccak/hex.bend as KKH
import ../../src/crypto/blake/blake2b/blake2b.bend as B2B
import ../../src/crypto/blake/blake2b/hex.bend as B2BH
import ../../src/crypto/blake/blake2s/blake2s.bend as B2S
import ../../src/crypto/blake/blake2s/hex.bend as B2SH
import ../../src/crypto/blake/blake3/blake3.bend as B3
import ../../src/crypto/blake/blake3/hex.bend as B3H
import ../../src/crypto/mac.bend as MAC
import ../../src/crypto/kdf.bend as KDF
import ../crypto/bytes.bend as B
import ../support/text.bend as X
import ./lib.bend as L

# Backend-differential driver (tools/backend_diff.py): hashes, subtle, MAC
# and KDF. Every argv token "code:field:..." prints one line; byte strings
# are lower-case hex. No expected value enters here: the harness runs the
# same tokens through every Bend execution path and compares the lines.
#
#   0:msg                 SHA-256 (byte-list API), hex of the digest words
#   1:msg                 SHA-512
#   2:msg                 SHA3-256
#   3:alg:c1.c2.c3        the hash facade, incremental over the chunks, then
#                         one-shot over their concatenation (alg 0 SHA-256,
#                         1 SHA-512, 2 SHA3-256)
#   4:a:b                 subtle.eq
#   5:depth:len:bytes     packed SHA-256 over an array of 2^depth words
#   6:depth:len:bytes     Keccak-256          7: BLAKE2b
#   8:depth:len:bytes     BLAKE2s             9: BLAKE3
#   10:key:msg            HMAC-SHA256 sign    11:key:msg:tag  verify
#   12:salt:ikm:info:L    HKDF                13:prk:info:L   expand
#   14:salt:ikm           extract

def word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

# little-endian words into slots i, i + 1, ...; a trailing partial word is dropped
def fill(bs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match bs:
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      fill(t, U32.inc(i), Array.set(U32, a, i, word(b0, b1, b2, b3)))
    case _:
      a

def arr(+p: List<&2, String>) -> Array<U32>:
  fill(L.hexf(p, 3n), 0, Array.new(U32, X.nat_field(p, 1n), 0))

def show_p(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{d}:
      P256.hex(d)

def show_kk(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{d}:
      KKH.hex(d)

def show_b2b(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{d}:
      B2BH.hex(d)

def show_b2s(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{d}:
      B2SH.hex(d)

def show_b3(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{}:
      "invalid"
    case Some{d}:
      B3H.hex(d)

def kdf(r: Result<&2, &2, KDF.KdfError, List<&2, U32>>) -> String:
  match r:
    case Fail{e}:
      "LengthTooLarge"
    case Done{okm}:
      B.hex(okm)

def chunks(xs: List<&2, String>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{B.unhex(h), chunks(t)}

def hasher(n: Nat) -> Hash.Hasher:
  match n:
    case 0n:
      Hash.new_sha256()
    case 1n:
      Hash.new_sha512()
    case 2n+x:
      Hash.new_sha3_256()

def oneshot(n: Nat, msg: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Hash.sha256(msg)
    case 1n:
      Hash.sha512(msg)
    case 2n+x:
      Hash.sha3_256(msg)

def inc(+n: Nat, +cs: List<&2, List<&2, U32>>) -> String:
  B.hex(Hash.digest(Hash.update_all(hasher(n), cs))) ++ " " ++ B.hex(oneshot(n, List.concat(&2, U32, cs)))

def run(code: Nat, +p: List<&2, String>) -> String:
  match code:
    case 0n:
      S256.hex(S256.sha256(L.hexf(p, 1n)))
    case 1n:
      S512.hex(S512.sha512(L.hexf(p, 1n)))
    case 2n:
      B.hex(S3.sha3_256(L.hexf(p, 1n)))
    case 3n:
      inc(X.nat_field(p, 1n), chunks(String.split(X.field(p, 2n), '.')))
    case 4n:
      L.bool(Subtle.eq(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 5n:
      show_p(P256.sha256(arr(p), X.nat_field(p, 2n)))
    case 6n:
      show_kk(KK.keccak256(arr(p), X.nat_field(p, 2n)))
    case 7n:
      show_b2b(B2B.blake2b(arr(p), X.nat_field(p, 2n)))
    case 8n:
      show_b2s(B2S.blake2s(arr(p), X.nat_field(p, 2n)))
    case 9n:
      show_b3(B3.blake3(arr(p), X.nat_field(p, 2n)))
    case 10n:
      B.hex(MAC.sign(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 11n:
      L.bool(MAC.verify(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 12n:
      kdf(KDF.hkdf(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n), X.nat_field(p, 4n)))
    case 13n:
      kdf(KDF.expand(L.hexf(p, 1n), L.hexf(p, 2n), X.nat_field(p, 3n)))
    case 14n:
      B.hex(KDF.extract(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 15n+x:
      "?"

def line(s: String) -> String:
  +p = X.fields(s)
  run(X.nat_field(p, 0n), p)

def all(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{line(h), all(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.print_lines(all(X.program_args(args)))
