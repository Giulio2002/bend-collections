import Base
import ../../../src/crypto/mac.bend as MAC
import ../../../src/crypto/sha/sha256.bend as SHA
import ../../../spec/crypto/hmac.bend as Spec
import ../../../spec/crypto/sha.bend as FIPS
import ../sha/laws.bend as ShaLaws
import ../sha/correctness.bend as ShaCorrect
import ../../lib/logic.bend as L

# HMAC-SHA256: the implementation src/crypto/mac.bend equals the RFC 2104 /
# FIPS 198-1 specification spec/crypto/hmac.bend for every key and message
# (the functional-correctness statement of HACL*'s Hacl.HMAC against
# Spec.HMAC, and of the VST HMAC proof of Beringer, Petcher, Ye and Appel
# 2015 against its FIPS 198-1 functional model). SHA-256 enters only through
# its proved refinement ShaLaws.sha256_bytes_correct.

# ---- SHA-256 facts ----

def fips_len(+bytes: List<&2, U32>) -> {List.length(&2, U32, FIPS.sha256_bytes(bytes)) == 32n : Nat}:
  ShaCorrect.digest_octets_length(FIPS.blocks(FIPS.prepare(bytes, 48n), FIPS.constants())(FIPS.initial()))

def le_of_len(+xs: List<&2, U32>, +n: Nat, +k: Nat, +e: {List.length(&2, U32, xs) == n : Nat}, +h: {Nat.is_le(n, k) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, xs), k) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, xs), n, e) : {Nat.is_le(_, k) == True{} : Bool}
  h

# ---- the key block ----

# fits(key, n) looks at most n+1 bytes, and says length(key) <= n.
def fits_len(+key: List<&2, U32>, +n: Nat) -> {MAC.fits(key, n) == Nat.is_le(List.length(&2, U32, key), n) : Bool}:
  match key n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case k <> rest 0n:
      {==}
    case k <> rest 1n+ +p:
      fits_len(rest, p)

# Past the end of the key, mask emits 0 XOR pad.
def mask_nil(+n: Nat, +pad: U32, +hp: {U32.xor(0, pad) == pad : U32}) -> {MAC.mask(Nil{}, n, pad) == Spec.xor_pad(List.replicate(U32, n, 0), pad) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %hp : {_ <> MAC.mask(Nil{}, p, pad) == U32.xor(0, pad) <> Spec.xor_pad(List.replicate(U32, p, 0), pad) : List<&2, U32>}
      %mask_nil(p, pad, hp) : {U32.xor(0, pad) <> MAC.mask(Nil{}, p, pad) == U32.xor(0, pad) <> _ : List<&2, U32>}
      {==}

# mask is zero padding to n bytes followed by the byte-wise XOR.
def mask_pad(+key: List<&2, U32>, +n: Nat, +pad: U32, +hp: {U32.xor(0, pad) == pad : U32}, +h: {Nat.is_le(List.length(&2, U32, key), n) == True{} : Bool}) -> {MAC.mask(key, n, pad) == Spec.xor_pad(List.append(&2, U32, key, List.replicate(U32, Nat.sub(n, List.length(&2, U32, key)), 0)), pad) : List<&2, U32>}:
  match key n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+ +p:
      mask_nil(1n+p, pad, hp)
    case k <> rest 0n:
      Empty.absurd({MAC.mask(k <> rest, 0n, pad) == Spec.xor_pad(List.append(&2, U32, k <> rest, List.replicate(U32, Nat.sub(0n, List.length(&2, U32, k <> rest)), 0)), pad) : List<&2, U32>}, L.false_true(h))
    case +k <> +rest 1n+ +p:
      %mask_pad(rest, p, pad, hp, h) : {U32.xor(k, pad) <> MAC.mask(rest, p, pad) == U32.xor(k, pad) <> _ : List<&2, U32>}
      {==}

def block_mask_if(+key: List<&2, U32>, +pad: U32, +hp: {U32.xor(0, pad) == pad : U32}, +b: Bool, +eb: {Nat.is_le(List.length(&2, U32, key), 64n) == b : Bool}) -> {MAC.mask(MAC.block_key_if(key, b), 64n, pad) == Spec.xor_pad(Spec.zero_pad(Spec.shorten_if(key, b)), pad) : List<&2, U32>}:
  match b:
    case True{}:
      mask_pad(key, 64n, pad, hp, eb)
    case False{}:
      %Equal.sym(List<&2, U32>, SHA.sha256_bytes(key), FIPS.sha256_bytes(key), ShaLaws.sha256_bytes_correct(key)) : {MAC.mask(_, 64n, pad) == Spec.xor_pad(Spec.zero_pad(FIPS.sha256_bytes(key)), pad) : List<&2, U32>}
      mask_pad(FIPS.sha256_bytes(key), 64n, pad, hp, le_of_len(FIPS.sha256_bytes(key), 32n, 64n, fips_len(key), {==}))

# The masked key block of the implementation is (K0 XOR pad) of FIPS 198-1.
def block_mask(+key: List<&2, U32>, +pad: U32, +hp: {U32.xor(0, pad) == pad : U32}) -> {MAC.mask(MAC.block_key(key), 64n, pad) == Spec.xor_pad(Spec.k0(key), pad) : List<&2, U32>}:
  %Equal.sym(Bool, MAC.fits(key, 64n), Nat.is_le(List.length(&2, U32, key), 64n), fits_len(key, 64n)) : {MAC.mask(MAC.block_key_if(key, _), 64n, pad) == Spec.xor_pad(Spec.zero_pad(Spec.shorten_if(key, Nat.is_le(List.length(&2, U32, key), 64n))), pad) : List<&2, U32>}
  block_mask_if(key, pad, hp, Nat.is_le(List.length(&2, U32, key), 64n), {==})

# ---- HMAC ----

def inner(+key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Spec.xor_pad(Spec.k0(key), 54), msg)

def outer(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, Spec.xor_pad(Spec.k0(key), 92), FIPS.sha256_bytes(inner(key, msg)))

def sign_correct(+key: List<&2, U32>, +msg: List<&2, U32>) -> {MAC.sign(key, msg) == Spec.hmac(key, msg) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, MAC.mask(MAC.block_key(key), 64n, 92), Spec.xor_pad(Spec.k0(key), 92), block_mask(key, 92, {==})) : {SHA.sha256_bytes(List.append(&2, U32, _, SHA.sha256_bytes(List.append(&2, U32, MAC.mask(MAC.block_key(key), 64n, 54), msg)))) == FIPS.sha256_bytes(outer(key, msg)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, MAC.mask(MAC.block_key(key), 64n, 54), Spec.xor_pad(Spec.k0(key), 54), block_mask(key, 54, {==})) : {SHA.sha256_bytes(List.append(&2, U32, Spec.xor_pad(Spec.k0(key), 92), SHA.sha256_bytes(List.append(&2, U32, _, msg)))) == FIPS.sha256_bytes(outer(key, msg)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, SHA.sha256_bytes(inner(key, msg)), FIPS.sha256_bytes(inner(key, msg)), ShaLaws.sha256_bytes_correct(inner(key, msg))) : {SHA.sha256_bytes(List.append(&2, U32, Spec.xor_pad(Spec.k0(key), 92), _)) == FIPS.sha256_bytes(outer(key, msg)) : List<&2, U32>}
  ShaLaws.sha256_bytes_correct(outer(key, msg))

# Every tag is 32 bytes.
def hmac_len(+key: List<&2, U32>, +msg: List<&2, U32>) -> {List.length(&2, U32, Spec.hmac(key, msg)) == 32n : Nat}:
  fips_len(outer(key, msg))

def sign_len(+key: List<&2, U32>, +msg: List<&2, U32>) -> {List.length(&2, U32, MAC.sign(key, msg)) == 32n : Nat}:
  %Equal.sym(List<&2, U32>, MAC.sign(key, msg), Spec.hmac(key, msg), sign_correct(key, msg)) : {List.length(&2, U32, _) == 32n : Nat}
  hmac_len(key, msg)
