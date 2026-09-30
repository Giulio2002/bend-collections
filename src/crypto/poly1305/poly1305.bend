import Base
import ./limbs.bend as L
import ../subtle.bend as Subtle

# Poly1305 (RFC 8439 section 2.5) over byte lists, on five radix-2^26
# natural-number limbs (src/crypto/poly1305/limbs.bend). A byte is the low 8
# bits of a U32. The key is r || s (32 bytes); mac reads missing key bytes
# as zero bytes (so any key list works), the checked poly1305 returns None
# unless the key has exactly 32 bytes. proofs/crypto/poly1305/ proves mac
# equal to spec/crypto/poly1305.bend for every key and message, and
# mac_aead equal to the RFC 8439 2.8 tag over aad and ciphertext.
#
# The radix constants 2^13 and 2^26 = 2^13 * 2^13 are passed to the limb
# functions as parameters (see limbs.bend); 2^13 is written here, once, as
# a literal (2^26 is its square, so no proof ever meets it as a literal).

def b13() -> Nat:
  8192n

def w26() -> Nat:
  Nat.mul(b13(), b13())

# ---- message blocks ----

def hd(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}: 0n
    case x <> t: L.byte(x)

def tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}: Nil{}
    case x <> t: t

# The first 16 bytes of ys (zeros past its end) and pb at 2^128, as limbs.
def load16(+ys: List<&2, U32>, pb: Nat) -> L.F:
  +y1 = tl(ys)
  +y2 = tl(y1)
  +y3 = tl(y2)
  +y4 = tl(y3)
  +y5 = tl(y4)
  +y6 = tl(y5)
  +y7 = tl(y6)
  +y8 = tl(y7)
  +y9 = tl(y8)
  +y10 = tl(y9)
  +y11 = tl(y10)
  +y12 = tl(y11)
  +y13 = tl(y12)
  +y14 = tl(y13)
  +y15 = tl(y14)
  L.load(hd(ys), hd(y1), hd(y2), hd(y3), hd(y4), hd(y5), hd(y6), hd(y7), hd(y8), hd(y9), hd(y10), hd(y11), hd(y12), hd(y13), hd(y14), hd(y15), pb)

# The accumulator over the message's 16-byte blocks, each with its 0x01
# byte (at 2^128 for a full block); a last block of 1..15 bytes gets the
# 0x01 byte right after its bytes.
def absorb(+w: Nat, +b: Nat, msg: List<&2, U32>, +k: L.K, h: L.F) -> L.F:
  match msg:
    case Nil{}: h
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      absorb(w, b, rest, k, L.block(w, b, k, h, L.load(L.byte(x0), L.byte(x1), L.byte(x2), L.byte(x3), L.byte(x4), L.byte(x5), L.byte(x6), L.byte(x7), L.byte(x8), L.byte(x9), L.byte(x10), L.byte(x11), L.byte(x12), L.byte(x13), L.byte(x14), L.byte(x15), 1n)))
    case x <> rest: L.block(w, b, k, h, load16(List.append(&2, U32, x <> rest, [1]), 0n))

# The accumulator and the byte count.
type A is Data:
  A{h: L.F, n: Nat}

# The same over msg zero-padded to a multiple of 16 bytes (RFC 8439 2.8's
# msg | pad16(msg)): the last block, zero-padded, is a full block. Also
# counts the bytes onto n.
def absorb_pad(+w: Nat, +b: Nat, msg: List<&2, U32>, +k: L.K, h: L.F, n: Nat) -> A:
  match msg:
    case Nil{}: A{h, n}
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      absorb_pad(w, b, rest, k, L.block(w, b, k, h, L.load(L.byte(x0), L.byte(x1), L.byte(x2), L.byte(x3), L.byte(x4), L.byte(x5), L.byte(x6), L.byte(x7), L.byte(x8), L.byte(x9), L.byte(x10), L.byte(x11), L.byte(x12), L.byte(x13), L.byte(x14), L.byte(x15), 1n)), Nat.add(n, 16n))
    case +x <> +rest: A{L.block(w, b, k, h, load16(x <> rest, 1n)), Nat.add(n, List.length(&2, U32, x <> rest))}

# ---- keys ----

# r = clamp(key[0..16]) (r &= 0x0ffffffc0ffffffc0ffffffc0fffffff) and
# s = key[16..32], as limbs.
def r_of(+k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32, +k8: U32, +k9: U32, +k10: U32, +k11: U32, +k12: U32, +k13: U32, +k14: U32, +k15: U32) -> L.F:
  L.load(L.byte(U32.and(k0, 255)), L.byte(U32.and(k1, 255)), L.byte(U32.and(k2, 255)), L.byte(U32.and(k3, 15)), L.byte(U32.and(k4, 252)), L.byte(U32.and(k5, 255)), L.byte(U32.and(k6, 255)), L.byte(U32.and(k7, 15)), L.byte(U32.and(k8, 252)), L.byte(U32.and(k9, 255)), L.byte(U32.and(k10, 255)), L.byte(U32.and(k11, 15)), L.byte(U32.and(k12, 252)), L.byte(U32.and(k13, 255)), L.byte(U32.and(k14, 255)), L.byte(U32.and(k15, 15)), 0n)

def s_of(+k16: U32, +k17: U32, +k18: U32, +k19: U32, +k20: U32, +k21: U32, +k22: U32, +k23: U32, +k24: U32, +k25: U32, +k26: U32, +k27: U32, +k28: U32, +k29: U32, +k30: U32, +k31: U32) -> L.F:
  L.load(L.byte(k16), L.byte(k17), L.byte(k18), L.byte(k19), L.byte(k20), L.byte(k21), L.byte(k22), L.byte(k23), L.byte(k24), L.byte(k25), L.byte(k26), L.byte(k27), L.byte(k28), L.byte(k29), L.byte(k30), L.byte(k31), 0n)

# Key byte i (0 past the end), for keys that are not 32 bytes long.
def kb(i: Nat, xs: List<&2, U32>) -> U32:
  match i xs:
    case _ Nil{}: 0
    case 0n x <> t: x
    case 1n+j x <> t: kb(j, t)

# ---- the tag ----

def tag(+w: Nat, +b: Nat, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32, +k8: U32, +k9: U32, +k10: U32, +k11: U32, +k12: U32, +k13: U32, +k14: U32, +k15: U32, +k16: U32, +k17: U32, +k18: U32, +k19: U32, +k20: U32, +k21: U32, +k22: U32, +k23: U32, +k24: U32, +k25: U32, +k26: U32, +k27: U32, +k28: U32, +k29: U32, +k30: U32, +k31: U32, msg: List<&2, U32>) -> List<&2, U32>:
  +k = L.key(b, r_of(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15))
  L.fin(w, absorb(w, b, msg, k, L.zero()), s_of(k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31))

def mac_w(+w: Nat, +b: Nat, +key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  match key:
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> k15 <> k16 <> k17 <> k18 <> k19 <> k20 <> k21 <> k22 <> k23 <> k24 <> k25 <> k26 <> k27 <> k28 <> k29 <> k30 <> k31 <> rest:
      tag(w, b, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, msg)
    case _:
      tag(w, b, kb(0n, key), kb(1n, key), kb(2n, key), kb(3n, key), kb(4n, key), kb(5n, key), kb(6n, key), kb(7n, key), kb(8n, key), kb(9n, key), kb(10n, key), kb(11n, key), kb(12n, key), kb(13n, key), kb(14n, key), kb(15n, key), kb(16n, key), kb(17n, key), kb(18n, key), kb(19n, key), kb(20n, key), kb(21n, key), kb(22n, key), kb(23n, key), kb(24n, key), kb(25n, key), kb(26n, key), kb(27n, key), kb(28n, key), kb(29n, key), kb(30n, key), kb(31n, key), msg)

# The 16-byte tag of msg under key = r || s.
def mac(+key: List<&2, U32>, msg: List<&2, U32>) -> List<&2, U32>:
  mac_w(w26(), b13(), key, msg)

def has_key(+key: List<&2, U32>) -> Bool:
  Nat.is_eq(List.length(&2, U32, key), 32n)

def when(ok: Bool, x: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}: Some{x}
    case False{}: None{}

def poly1305_w(+w: Nat, +b: Nat, key: List<&2, U32>, msg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match key:
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> k15 <> k16 <> k17 <> k18 <> k19 <> k20 <> k21 <> k22 <> k23 <> k24 <> k25 <> k26 <> k27 <> k28 <> k29 <> k30 <> k31 <> Nil{}:
      Some{tag(w, b, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, msg)}
    case _:
      None{}

# The tag, or None unless the key has 32 bytes.
def poly1305(key: List<&2, U32>, msg: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  poly1305_w(w26(), b13(), key, msg)

# True exactly when the key has 32 bytes and tag is the tag of msg; the tags
# are compared in constant time (src/crypto/subtle.bend).
def verify(+key: List<&2, U32>, +msg: List<&2, U32>, +tag: List<&2, U32>) -> Bool:
  Bool.and(has_key(key), Subtle.eq(mac(key, msg), tag))

# ---- the AEAD tag (RFC 8439 2.8) ----

# num_to_8_le_bytes
def le8(n: Nat, +x: Nat) -> List<&2, U32>:
  match n:
    case 0n: Nil{}
    case 1n+k: U32.from_nat(Nat.mod(x, 256n)) <> le8(k, Nat.div(x, 256n))

def tag_len(+w: Nat, +b: Nat, +k: L.K, s: L.F, la: Nat, a: A) -> List<&2, U32>:
  match a:
    case A{h, lc}: L.fin(w, absorb(w, b, List.append(&2, U32, le8(8n, la), le8(8n, lc)), k, h), s)

def tag_ct(+w: Nat, +b: Nat, +k: L.K, s: L.F, a: A, ct: List<&2, U32>) -> List<&2, U32>:
  match a:
    case A{h, la}: tag_len(w, b, k, s, la, absorb_pad(w, b, ct, k, h, 0n))

def tag2(+w: Nat, +b: Nat, +k0: U32, +k1: U32, +k2: U32, +k3: U32, +k4: U32, +k5: U32, +k6: U32, +k7: U32, +k8: U32, +k9: U32, +k10: U32, +k11: U32, +k12: U32, +k13: U32, +k14: U32, +k15: U32, +k16: U32, +k17: U32, +k18: U32, +k19: U32, +k20: U32, +k21: U32, +k22: U32, +k23: U32, +k24: U32, +k25: U32, +k26: U32, +k27: U32, +k28: U32, +k29: U32, +k30: U32, +k31: U32, aad: List<&2, U32>, ct: List<&2, U32>) -> List<&2, U32>:
  +k = L.key(b, r_of(k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15))
  tag_ct(w, b, k, s_of(k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31), absorb_pad(w, b, aad, k, L.zero(), 0n), ct)

def mac_aead_w(+w: Nat, +b: Nat, +key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> List<&2, U32>:
  match key:
    case k0 <> k1 <> k2 <> k3 <> k4 <> k5 <> k6 <> k7 <> k8 <> k9 <> k10 <> k11 <> k12 <> k13 <> k14 <> k15 <> k16 <> k17 <> k18 <> k19 <> k20 <> k21 <> k22 <> k23 <> k24 <> k25 <> k26 <> k27 <> k28 <> k29 <> k30 <> k31 <> rest:
      tag2(w, b, k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, aad, ct)
    case _:
      tag2(w, b, kb(0n, key), kb(1n, key), kb(2n, key), kb(3n, key), kb(4n, key), kb(5n, key), kb(6n, key), kb(7n, key), kb(8n, key), kb(9n, key), kb(10n, key), kb(11n, key), kb(12n, key), kb(13n, key), kb(14n, key), kb(15n, key), kb(16n, key), kb(17n, key), kb(18n, key), kb(19n, key), kb(20n, key), kb(21n, key), kb(22n, key), kb(23n, key), kb(24n, key), kb(25n, key), kb(26n, key), kb(27n, key), kb(28n, key), kb(29n, key), kb(30n, key), kb(31n, key), aad, ct)

# The RFC 8439 2.8 tag: Poly1305 under key over
# aad | pad16(aad) | ct | pad16(ct) | le64(len aad) | le64(len ct),
# without building that list.
def mac_aead(+key: List<&2, U32>, aad: List<&2, U32>, ct: List<&2, U32>) -> List<&2, U32>:
  mac_aead_w(w26(), b13(), key, aad, ct)
