import Base
import ../../src/crypto/secp256k1.bend as K
import ../crypto/bytes.bend as B
import ../support/text.bend as X
import ./lib.bend as L

# Backend-differential driver (tools/backend_diff.py): src/crypto/secp256k1.bend.
# Every argv token "code:field:..." prints one line; byte strings are
# lower-case hex.
#
#   0:sk:hash         sign_compact (r || s || v)   1:pk:hash:sig   verify
#   2:pk:hash:sig     verify_strict                3:hash:sig      recover
#   4:sk:flag         public_key (flag 1: compressed)
#   5:pk              eth_address                  6:sk:msg:aux    schnorr_sign
#   7:pk:msg:sig      schnorr_verify               8:sk            schnorr_pubkey
#   9:input           ecrecover                    10:seed         generate_keypair
#   11:sk:msg:aux     schnorr_keypair, its public key, and a signature with it

def flag(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

def pair(r: Maybe<&2, K.Keypair>) -> String:
  match r:
    case None{}:
      "none"
    case Some{K.Keypair{s, q}}:
      B.hex(s) ++ " " ++ B.hex(q)

def run(code: Nat, +p: List<&2, String>) -> String:
  match code:
    case 0n:
      L.opt(K.sign_compact(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 1n:
      L.bool(K.verify(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 2n:
      L.bool(K.verify_strict(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 3n:
      L.opt(K.recover(L.hexf(p, 1n), L.hexf(p, 2n)))
    case 4n:
      L.opt(K.public_key(L.hexf(p, 1n), flag(X.nat_field(p, 2n))))
    case 5n:
      L.opt(K.eth_address(L.hexf(p, 1n)))
    case 6n:
      L.opt(K.schnorr_sign(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 7n:
      L.bool(K.schnorr_verify(L.hexf(p, 1n), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 8n:
      L.opt(K.schnorr_pubkey(L.hexf(p, 1n)))
    case 9n:
      L.opt(K.ecrecover(L.hexf(p, 1n)))
    case 10n:
      pair(K.generate_keypair(L.hexf(p, 1n)))
    case 11n:
      L.opt(K.schnorr_keypair_pubkey(K.schnorr_keypair(L.hexf(p, 1n)))) ++ " " ++ L.opt(K.schnorr_sign_keypair(K.schnorr_keypair(L.hexf(p, 1n)), L.hexf(p, 2n), L.hexf(p, 3n)))
    case 12n+x:
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
