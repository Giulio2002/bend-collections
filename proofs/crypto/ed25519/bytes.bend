import Base
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/sha512.bend as SHA
import ../../../src/crypto/hash.bend as H
import ../../../src/crypto/sha512/types.bend as T512
import ../../../src/crypto/sha512/core.bend as C512
import ../../../src/crypto/curve25519/field.bend as F
import ../../../src/crypto/curve25519/x25519.bend as X
import ../../../src/crypto/ed25519/ed25519.bend as E
import ../../lib/logic.bend as L
import ../../math/hash/hash.bend as HH
import ../sha512/conformance.bend as S512
import ../sha512/stream.bend as P512
import ../curve25519/limbs.bend as LM

# Byte-string facts for Ed25519: the implementation's take / drop / cat are
# the spec's first / rest / cat; a SHA-512 digest is 64 bytes, each below
# 256, and equals FIPS 180-4's (proofs/crypto/sha512/conformance.bend).

def v(+x: U32) -> Nat:
  U32.to_nat(x)

# ---- take, drop, cat ----

def take_eq(+n: Nat, +xs: List<&2, U32>) -> {F.take(n, xs) == SE.first(n, xs) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, F.take(m, xt), SE.first(m, xt), take_eq(m, xt))

def drop_eq(+n: Nat, +xs: List<&2, U32>) -> {F.drop(n, xs) == SE.rest(n, xs) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          drop_eq(m, xt)

def cat_eq(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {E.cat(xs, ys) == SE.cat(xs, ys) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, E.cat(xt, ys), SE.cat(xt, ys), cat_eq(xt, ys))

# n + m, by recursion on n
def pl(n: Nat, +m: Nat) -> Nat:
  match n:
    case 0n:
      m
    case 1n+k:
      1n+pl(k, m)

def take_okb(+n: Nat, +m: Nat, +xs: List<&2, U32>, +b: Nat, +e: {LM.okb(pl(n, m), xs, b) == True{} : Bool}) -> {LM.okb(n, F.take(n, xs), b) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +k:
      match xs:
        case Nil{}:
          e
        case Con{+x, +xt}:
          L.and_intro(Nat.is_le(v(x), b), LM.okb(k, F.take(k, xt), b), L.and_left(Nat.is_le(v(x), b), LM.okb(pl(k, m), xt, b), e), take_okb(k, m, xt, b, L.and_right(Nat.is_le(v(x), b), LM.okb(pl(k, m), xt, b), e)))

def drop_okb(+n: Nat, +m: Nat, +xs: List<&2, U32>, +b: Nat, +e: {LM.okb(pl(n, m), xs, b) == True{} : Bool}) -> {LM.okb(m, F.drop(n, xs), b) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+ +k:
      match xs:
        case Nil{}:
          Empty.absurd({LM.okb(m, Nil{}, b) == True{} : Bool}, L.true_false(Equal.sym(Bool, False{}, True{}, e)))
        case Con{+x, +xt}:
          drop_okb(k, m, xt, b, L.and_right(Nat.is_le(v(x), b), LM.okb(pl(k, m), xt, b), e))

# 8 n
def e8(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      Nat.add(8n, e8(k))

def bitlen_okb(+n: Nat, +xs: List<&2, U32>, +b: Nat, +e: {LM.okb(n, xs, b) == True{} : Bool}) -> {X.bitlen(xs) == e8(n) : Nat}:
  match n xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xt}:
      Empty.absurd({X.bitlen(Con{x, xt}) == 0n : Nat}, L.true_false(Equal.sym(Bool, False{}, True{}, e)))
    case 1n+k Nil{}:
      Empty.absurd({0n == e8(1n+k) : Nat}, L.true_false(Equal.sym(Bool, False{}, True{}, e)))
    case 1n+ +k Con{+x, +xt}:
      Equal.cong(Nat, Nat, z => Nat.add(8n, z), X.bitlen(xt), e8(k), bitlen_okb(k, xt, b, L.and_right(Nat.is_le(v(x), b), LM.okb(k, xt, b), e)))

def bitlen_256(+xs: List<&2, U32>, +e: {LM.okb(32n, xs, 255n) == True{} : Bool}) -> {X.bitlen(xs) == 256n : Nat}:
  bitlen_okb(32n, xs, 255n, e)

# ---- SHA-512 ----

def sha_eq(+bytes: List<&2, U32>) -> {H.sha512(bytes) == SHA.sha512_bytes(bytes) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, H.sha512(bytes), C512.sha512(bytes), SHA.sha512_bytes(bytes),
    P512.hash_correct(bytes), S512.sha512_correct(bytes))

def byte_and(+x: U32) -> {Nat.is_le(v(U32.and(x, 255)), 255n) == True{} : Bool}:
  HH.and_le32(x, 255)

def okb_con(+n: Nat, +x: U32, +t: List<&2, U32>, +hx: {Nat.is_le(v(x), 255n) == True{} : Bool}, +ht: {LM.okb(n, t, 255n) == True{} : Bool}) -> {LM.okb(1n+n, Con{x, t}, 255n) == True{} : Bool}:
  L.and_intro(Nat.is_le(v(x), 255n), LM.okb(n, t, 255n), hx, ht)

def octets_okb(+n: Nat, +x: U32, +t: List<&2, U32>, +ht: {LM.okb(n, t, 255n) == True{} : Bool}) -> {LM.okb(4n+n, C512.octets(x, t), 255n) == True{} : Bool}:
  +b0 = U32.and(x, 255)
  +b1 = U32.and(U32.shrn(x, 8n), 255)
  +b2 = U32.and(U32.shrn(x, 16n), 255)
  +b3 = U32.and(U32.shrn(x, 24n), 255)
  +l0 = okb_con(n, b0, t, byte_and(x), ht)
  +l1 = okb_con(1n+n, b1, Con{b0, t}, byte_and(U32.shrn(x, 8n)), l0)
  +l2 = okb_con(2n+n, b2, Con{b1, Con{b0, t}}, byte_and(U32.shrn(x, 16n)), l1)
  okb_con(3n+n, b3, Con{b2, Con{b1, Con{b0, t}}}, byte_and(U32.shrn(x, 24n)), l2)

def lane_okb(+n: Nat, +l: T512.Lane, +t: List<&2, U32>, +ht: {LM.okb(n, t, 255n) == True{} : Bool}) -> {LM.okb(8n+n, C512.lane_octets(l, t), 255n) == True{} : Bool}:
  match l:
    case T512.W{+hi, +lo}:
      octets_okb(4n+n, hi, C512.octets(lo, t), octets_okb(n, lo, t, ht))

def digest_okb(+s: T512.State) -> {LM.okb(64n, C512.digest_bytes(s), 255n) == True{} : Bool}:
  match s:
    case T512.H{+a, +b, +c, +d, +e, +f, +g, +h}:
      +th = C512.lane_octets(h, Nil{})
      +tg = C512.lane_octets(g, th)
      +tf = C512.lane_octets(f, tg)
      +te = C512.lane_octets(e, tf)
      +td = C512.lane_octets(d, te)
      +tc = C512.lane_octets(c, td)
      +tb = C512.lane_octets(b, tc)
      lane_okb(56n, a, tb, lane_okb(48n, b, tc, lane_okb(40n, c, td, lane_okb(32n, d, te, lane_okb(24n, e, tf, lane_okb(16n, f, tg, lane_okb(8n, g, th, lane_okb(0n, h, Nil{}, {==}))))))))

# a digest: 64 bytes, each below 256
def sha_okb(+bytes: List<&2, U32>) -> {LM.okb(64n, H.sha512(bytes), 255n) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, H.sha512(bytes), C512.sha512(bytes), P512.hash_correct(bytes)) :
    {LM.okb(64n, _, 255n) == True{} : Bool}
  digest_okb(C512.blocks(C512.lanes(List.append(&2, U32, bytes, C512.suffix(List.length(&2, U32, bytes)))), 64n, C512.round_constants(), C512.initial()))

def sha_lea(+bytes: List<&2, U32>) -> {LM.lea(H.sha512(bytes), 255n) == True{} : Bool}:
  LM.okb_lea(64n, H.sha512(bytes), 255n, sha_okb(bytes))
