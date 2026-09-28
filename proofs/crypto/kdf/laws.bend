import Base
import ../../../src/crypto/kdf.bend as KDF
import ../../../spec/crypto/hkdf.bend as Spec

# The clauses of src/crypto/kdf.bend (HKDF-SHA256), proved in proof.bend.
# Every clause is for every salt, key material, info and length.

# The specification's partial expand, as the implementation's result type.
def as_result(m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, KDF.KdfError, List<&2, U32>>:
  match m:
    case None{}:
      Fail{KDF.LengthTooLarge{}}
    case Some{okm}:
      Done{okm}

# extract is RFC 5869 section 2.2 (HMAC-SHA256(salt, IKM)).
law Extract.correct:
  for +salt: List<&2, U32>
  for +ikm: List<&2, U32>
  {KDF.extract(salt, ikm) == Spec.extract(salt, ikm) : List<&2, U32>}

# expand is RFC 5869 section 2.3, and fails exactly where it is undefined.
law Expand.correct:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  {KDF.expand(prk, info, len) == as_result(Spec.expand(prk, info, len)) : Result<&2, &2, KDF.KdfError, List<&2, U32>>}

law Expand.done:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  for +h: {Nat.is_le(len, 8160n) == True{} : Bool}
  {KDF.expand(prk, info, len) == Done{Spec.okm(prk, info, len)} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}

law Expand.too_long:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  for +h: {Nat.is_le(len, 8160n) == False{} : Bool}
  {KDF.expand(prk, info, len) == Fail{KDF.LengthTooLarge{}} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}

# The output has the requested length.
law Expand.length:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  for +out: List<&2, U32>
  for +h: {KDF.expand(prk, info, len) == Done{out} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  {List.length(&2, U32, out) == len : Nat}

# A shorter output is a prefix of a longer one (same key and info).
law Expand.prefix:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +a: Nat
  for +b: Nat
  for +out: List<&2, U32>
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  for +h: {KDF.expand(prk, info, b) == Done{out} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  {KDF.expand(prk, info, a) == Done{List.take(&2, U32, out, a)} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}

# hkdf is extract then expand.
law Hkdf.correct:
  for +salt: List<&2, U32>
  for +ikm: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  {KDF.hkdf(salt, ikm, info, len) == as_result(Spec.hkdf(salt, ikm, info, len)) : Result<&2, &2, KDF.KdfError, List<&2, U32>>}

# The specification's OKM (any length): L bytes, and prefixes of each other.
law Okm.length:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +len: Nat
  {List.length(&2, U32, Spec.okm(prk, info, len)) == len : Nat}

law Okm.prefix:
  for +prk: List<&2, U32>
  for +info: List<&2, U32>
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Spec.okm(prk, info, a) == List.take(&2, U32, Spec.okm(prk, info, b), a) : List<&2, U32>}
