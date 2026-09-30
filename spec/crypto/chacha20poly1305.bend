import Base
import ./chacha.bend as CH
import ./poly1305.bend as PS
import ./subtle.bend as EQ

# Specification of the ChaCha20-Poly1305 AEAD (RFC 8439 sections 2.6 and
# 2.8) and of XChaCha20-Poly1305 (draft-irtf-cfrg-xchacha-03 section 2),
# composed from the ChaCha20 and Poly1305 specifications (as HACL*'s
# Spec.Chacha20Poly1305). The sealed message is the ciphertext followed by
# the 16-byte tag (the layout of RFC 5116 and of Go's and Python's AEAD
# APIs). Opening returns None when the input is shorter than a tag or the
# tag is not the one computed over the ciphertext (compared as lists).

# 2.6 poly1305_key_gen: the first 32 bytes of the block with counter 0.
def poly_key(+key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  CH.prefix(32n, CH.block(key, 0, nonce))

# pad16(x): zero bytes up to a multiple of 16, i.e. (16 - len(x) % 16) % 16
# of them ("if (len(x) % 16) == 0 then NULL else copies(0, 16 - len % 16)").
def pad16(+xs: List<&2, U32>) -> List<&2, U32>:
  List.replicate(U32, Nat.mod(Nat.sub(16n, Nat.mod(List.length(&2, U32, xs), 16n)), 16n), 0)

# num_to_8_le_bytes
def le8(n: Nat, +x: Nat) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: U32.from_nat(Nat.mod(x, 256n)) <> le8(k, Nat.div(x, 256n))

# mac_data = aad | pad16(aad) | ciphertext | pad16(ciphertext)
#            | num_to_8_le_bytes(aad.length) | num_to_8_le_bytes(ciphertext.length)
def mac_data(+aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, aad, List.append(&2, U32, pad16(aad), List.append(&2, U32, ct,
    List.append(&2, U32, pad16(ct), List.append(&2, U32, le8(8n, List.length(&2, U32, aad)), le8(8n, List.length(&2, U32, ct)))))))

def tag(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  PS.mac(poly_key(key, nonce), mac_data(aad, ct))

# 2.8 chacha20_aead_encrypt: ciphertext = chacha20_encrypt(key, 1, nonce,
# plaintext), then the tag over aad and ciphertext.
def seal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  +ct = CH.encrypt(key, 1, nonce, pt)
  List.append(&2, U32, ct, tag(key, nonce, aad, ct))

# Decryption: the tag is recomputed over the received ciphertext and the
# plaintext released only when it matches.
def open_tag(ok: Bool, +key: List<&2, U32>, +nonce: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{CH.encrypt(key, 1, nonce, ct)}
    case False{}: None{}

def open_split(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>, +t: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open_tag(EQ.equal(t, tag(key, nonce, aad, ct)), key, nonce, ct)

def open_len(short: Bool, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match short:
    case True{}: None{}
    case False{}:
      +n = Nat.sub(List.length(&2, U32, data), 16n)
      open_split(key, nonce, aad, CH.prefix(n, data), CH.suffix(n, data))

def open(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open_len(Nat.is_lt(List.length(&2, U32, data), 16n), key, nonce, aad, data)

# XChaCha20-Poly1305: ChaCha20-Poly1305 under the HChaCha20 subkey of the
# first 16 nonce bytes, with the nonce 0x00000000 || nonce[16..24].
def xseal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  seal(CH.xsubkey(key, nonce), CH.xnonce(nonce), aad, pt)

def xopen(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  open(CH.xsubkey(key, nonce), CH.xnonce(nonce), aad, data)
