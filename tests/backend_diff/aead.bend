import Base
import ../../src/crypto/aead.bend as A
import ../../src/crypto/chacha/chacha20.bend as C
import ../../src/crypto/poly1305/poly1305.bend as P
import ../../src/crypto/aes/aes.bend as AES
import ../crypto/bytes.bend as B
import ../support/text.bend as X
import ./lib.bend as L

# Backend-differential driver (tools/backend_diff.py): the AEAD facade (all
# four algorithms), ChaCha20 / HChaCha20 / XChaCha20 and Poly1305. Every argv
# token "code:field:..." prints one line; byte strings are lower-case hex.
# alg: 0 ChaCha20-Poly1305, 1 XChaCha20-Poly1305, 2 AES-128-GCM, 3 AES-256-GCM.
#
#   0:alg:key:nonce:aad:pt     encrypt        1:alg:key:nonce:aad:data  decrypt
#   2:alg:key:nonce:aad:pt     encrypt, then decrypt what it returned
#   3:alg:key:nonce:aad:pt     seal           4:alg:key:nonce:aad:data  open
#   5:key:ctr:nonce:pt         chacha20       6:key:ctr:nonce:pt        xchacha20
#   7:key:nonce                hchacha20      8:key:ctr:nonce           chacha20_block
#   9:key:msg                  poly1305       10:key:msg:tag            poly1305 verify
#   11:alg:key:nonce           key_size, nonce_size, tag_size, valid
#   12:key:block               AES block encryption (FIPS 197; 16, 24 or 32 key bytes)

def alg(n: Nat) -> A.Alg:
  match n:
    case 0n:
      A.CHACHA20_POLY1305{}
    case 1n:
      A.XCHACHA20_POLY1305{}
    case 2n:
      A.AES_128_GCM{}
    case 3n+x:
      A.AES_256_GCM{}

def trip(+a: Nat, +k: List<&2, U32>, +n: List<&2, U32>, +aad: List<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}:
      "none"
    case Some{+ct}:
      B.hex(ct) ++ " " ++ L.opt(A.decrypt(alg(a), k, n, aad, ct))

def sizes(+a: Nat, +p: List<&2, String>) -> String:
  Nat.show(A.key_size(alg(a))) ++ " " ++ Nat.show(A.nonce_size(alg(a))) ++ " " ++ Nat.show(A.tag_size()) ++ " " ++ L.bool(A.valid(alg(a), L.hexf(p, 2n), L.hexf(p, 3n)))

def aes(m: Maybe<&2, AES.Schedule>, block: List<&2, U32>) -> String:
  match m:
    case None{}:
      "badkey"
    case Some{s}:
      L.opt(AES.encrypt_block(s, block))

def run(code: Nat, +p: List<&2, String>) -> String:
  match code:
    case 0n:
      L.opt(A.encrypt(alg(X.nat_field(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), L.hexf(p, 5n)))
    case 1n:
      L.opt(A.decrypt(alg(X.nat_field(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), L.hexf(p, 5n)))
    case 2n:
      trip(X.nat_field(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), A.encrypt(alg(X.nat_field(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), L.hexf(p, 5n)))
    case 3n:
      L.opt(A.seal(alg(X.nat_field(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), L.hexf(p, 5n)))
    case 4n:
      L.opt(A.open(alg(X.nat_field(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n), L.hexf(p, 5n)))
    case 5n:
      L.opt(C.chacha20(L.hexf(p, 1n), X.u32_field(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n)))
    case 6n:
      L.opt(C.xchacha20(L.hexf(p, 1n), X.u32_field(p, 2n), L.hexf(p, 3n), L.hexf(p, 4n)))
    case 7n:
      L.opt(C.hchacha20(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 8n:
      L.opt(C.chacha20_block(L.hexf(p, 1n), X.u32_field(p, 2n), L.hexf(p, 3n)))
    case 9n:
      L.opt(P.poly1305(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 10n:
      L.bool(P.verify(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 11n:
      sizes(X.nat_field(p, 1n), p)
    case 12n:
      aes(AES.expand_key(L.hexf(p, 1n)), L.hexf(p, 2n))
    case 13n+x:
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
