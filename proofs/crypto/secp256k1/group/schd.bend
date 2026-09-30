import Base
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/schnorr.bend as SS

# The values BIP-340 signing computes (spec/crypto/secp256k1/schnorr.bend,
# sign_p / sign_r), named so that the clauses of laws_schnorr_group.bend can
# speak of them: the public point P = d' G, the key d with even y, the
# public key bytes, the nonce k', the point R = k' G, the challenge e and
# the signature bytes(x(R)) || bytes((k + e d) mod n).

def pub_a(+one: Nat, +sk: List<&2, U32>) -> CS.SAffine:
  CS.to_affine(SS.p(one), CS.pmul(SS.p(one), CS.os2ip(sk), CS.g(one)))

def key(+one: Nat, +sk: List<&2, U32>) -> Nat:
  SS.even(SS.n(one), CS.aff_y(pub_a(one, sk)), CS.os2ip(sk))

def pkb(+one: Nat, +sk: List<&2, U32>) -> List<&2, U32>:
  SS.bytes32(CS.aff_x(pub_a(one, sk)))

# A tagged hash that looks at its message before anything else (its value
# is SS.tagged(tag, x) in both cases: schp.bend tg_eq), so that the proof
# checker keeps the hash of an unknown message folded instead of running
# SHA-256 on the tag at every comparison.
def tg(+tag: List<&2, U32>, x: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Nil{}:
      SS.tagged(tag, Nil{})
    case h <> r:
      SS.tagged(tag, h <> r)

# k' = int(hash_nonce(t || bytes(P) || m)) mod n, t = bytes(d) xor hash_aux(a)
def nonce(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Nat:
  Nat.mod(CS.os2ip(tg(SS.tag_nonce(), SS.cat(SS.xor_bytes(SS.bytes32(key(one, sk)), tg(SS.tag_aux(), aux)), SS.cat(pkb(one, sk), m)))), SS.n(one))

def r_a(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> CS.SAffine:
  CS.to_affine(SS.p(one), CS.pmul(SS.p(one), nonce(one, sk, m, aux), CS.g(one)))

# e = int(hash_challenge(bytes(R) || bytes(P) || m)) mod n
def chal(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Nat:
  Nat.mod(CS.os2ip(tg(SS.tag_challenge(), SS.cat(SS.bytes32(CS.aff_x(r_a(one, sk, m, aux))), SS.cat(pkb(one, sk), m)))), SS.n(one))

def sval(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> Nat:
  FS.madd(SS.n(one), SS.even(SS.n(one), CS.aff_y(r_a(one, sk, m, aux)), nonce(one, sk, m, aux)), FS.mmul(SS.n(one), chal(one, sk, m, aux), key(one, sk)))

def sigv(+one: Nat, +sk: List<&2, U32>, +m: List<&2, U32>, +aux: List<&2, U32>) -> List<&2, U32>:
  SS.cat(SS.bytes32(CS.aff_x(r_a(one, sk, m, aux))), SS.bytes32(sval(one, sk, m, aux)))
