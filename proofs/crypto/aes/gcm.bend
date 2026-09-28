import Base
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as I
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ../../../spec/crypto/subtle.bend as Eq
import ../subtle/laws.bend as EqLaws
import ../subtle/proof.bend as EqProof
import ./ghash_defs.bend as D
import ./ghash_bits.bend as B
import ./ghash.bend as H
import ./cipher.bend as C

# The implementation's GCM equals SP 800-38D's GCM-AE / GCM-AD over the FIPS
# 197 cipher, for every key schedule (any Nk, Nr), 96-bit nonce, AAD and
# message.

# The counter block nonce || [c]_32.
def cb(q0: T.Quad, q1: T.Quad, q2: T.Quad, +c: U32) -> List<&2, U32>:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c)]

# The 96-bit nonce.
def nonce(q0: T.Quad, q1: T.Quad, q2: T.Quad) -> List<&2, U32>:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]

def bytes_of_ok(+st: T.State) -> {A.bytes_of(st) == S.bytes_of(st) : List<&2, U32>}:
  match st:
    case T.S{T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, T.W{a12, a13, a14, a15}}:
      {==}

def xor_ok(+xs: List<&2, U32>, +ks: List<&2, U32>) -> {I.xor_bytes(xs, ks) == G.xor_bytes(xs, ks) : List<&2, U32>}:
  match xs ks:
    case x <> xt k <> kt:
      %xor_ok(xt, kt) : {U32.xor(x, k) <> I.xor_bytes(xt, kt) == U32.xor(x, k) <> _ : List<&2, U32>}
      {==}
    case Nil{} _:
      {==}
    case x <> xt Nil{}:
      {==}

def keystream_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +c: U32) -> {I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c) == G.ciph(nk, nr, key, cb(q0, q1, q2, c)) : List<&2, U32>}:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      %C.encrypt_ok(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c)) : {A.bytes_of(A.encrypt(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c))) == S.bytes_of(_) : List<&2, U32>}
      bytes_of_ok(A.encrypt(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c)))

def inc_ok(+q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +c: U32) -> {G.inc32(cb(q0, q1, q2, c)) == cb(q0, q1, q2, U32.inc(c)) : List<&2, U32>}:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      %Equal.sym(U32, G.int32(U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c)), c, B.int32_ctr(c)) : {List.append(&2, U32, [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], G.str32(U32.inc(_))) == cb(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, U32.inc(c)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, G.str32(U32.inc(c)), [U32.and(255, U32.shrn(U32.inc(c), 24n)), U32.and(255, U32.shrn(U32.inc(c), 16n)), U32.and(255, U32.shrn(U32.inc(c), 8n)), U32.and(255, U32.inc(c))], B.str32_ctr(U32.inc(c))) : {List.append(&2, U32, [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _) == cb(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, U32.inc(c)) : List<&2, U32>}
      {==}

# Counter mode from counter c (a whole block per counter; a last partial
# block uses the leftmost bytes of its keystream block).
def gctr_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +xs: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +c: U32) -> {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.gctr(nk, nr, key, xs, cb(q0, q1, q2, c)) : List<&2, U32>}:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      %Equal.sym(List<&2, U32>, G.inc32(cb(q0, q1, q2, c)), cb(q0, q1, q2, U32.inc(c)), inc_ok(q0, q1, q2, c)) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == List.append(&2, U32, G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], G.ciph(nk, nr, key, cb(q0, q1, q2, c))), G.gctr(nk, nr, key, rest, _)) : List<&2, U32>}
      %gctr_ok(nk, nr, key, rest, q0, q1, q2, U32.inc(c)) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == List.append(&2, U32, G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], G.ciph(nk, nr, key, cb(q0, q1, q2, c))), _) : List<&2, U32>}
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == List.append(&2, U32, G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], _), I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, rest, q0, q1, q2, U32.inc(c))) : List<&2, U32>}
      %xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c)) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == List.append(&2, U32, _, I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, rest, q0, q1, q2, U32.inc(c))) : List<&2, U32>}
      {==}
    case Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([], _) : List<&2, U32>}
      xor_ok([], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0], _) : List<&2, U32>}
      xor_ok([x0], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1], _) : List<&2, U32>}
      xor_ok([x0, x1], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2], _) : List<&2, U32>}
      xor_ok([x0, x1, x2], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> Nil{}:
      %keystream_ok(nk, nr, key, q0, q1, q2, c) : {I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, xs, q0, q1, q2, c) == G.xor_bytes([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14], _) : List<&2, U32>}
      xor_ok([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14], I.keystream(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, c))

def hash_key_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>) -> {D.R(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)})) == G.hash_key(nk, nr, key) : Word(128n)}:
  %C.encrypt_ok(nk, nr, key, T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}) : {D.R(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)})) == G.block(S.bytes_of(_)) : Word(128n)}
  H.pack_ok(A.encrypt(nk, nr, key, T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}))

# The tag: GCTR from J0 over GHASH of A, C and their lengths.
def tag_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +aad: List<&2, U32>, +c: List<&2, U32>) -> {I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, aad, c) == G.tag(nk, nr, key, nonce(q0, q1, q2), aad, c) : List<&2, U32>}:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      %hash_key_ok(nk, nr, key) : {I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c) == G.gctr(nk, nr, key, G.block_bytes(G.ghash(_, List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n))), G.j0([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])) : List<&2, U32>}
      %Equal.sym(Word(128n), G.ghash(D.R(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)})), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n)), D.R(I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), I.lengths(aad, c), I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), c, I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, I.zero())))), H.ghash_all_ok(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, c)) : {I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c) == G.gctr(nk, nr, key, G.block_bytes(_), G.j0([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, G.block_bytes(D.R(I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), I.lengths(aad, c), I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), c, I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, I.zero()))))), I.unpack(I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), I.lengths(aad, c), I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), c, I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, I.zero())))), B.bb_ok(I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), I.lengths(aad, c), I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), c, I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, I.zero()))))) : {I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c) == G.gctr(nk, nr, key, _, G.j0([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])) : List<&2, U32>}
      gctr_ok(nk, nr, key, I.unpack(I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), I.lengths(aad, c), I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), c, I.ghash(I.hash_key(A.Schedule{nr, A.expand(nk, nr, key)}), aad, I.zero())))), T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 1)

# GCM-AE: C = GCTR(inc32(J0), P), T = the tag of C.
def seal_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {I.seal_core(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, aad, pt) == G.seal(nk, nr, key, nonce(q0, q1, q2), aad, pt) : List<&2, U32>}:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      %gctr_ok(nk, nr, key, pt, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2) : {I.seal_core(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, pt) == List.append(&2, U32, _, G.tag(nk, nr, key, [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], aad, _)) : List<&2, U32>}
      %tag_ok(nk, nr, key, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, pt, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2)) : {I.seal_core(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, pt) == List.append(&2, U32, I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, pt, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2), _) : List<&2, U32>}
      {==}

def accept_ok(+ok: Bool, +p: List<&2, U32>) -> {I.accept(ok, p) == G.accept(ok, p) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# GCM-AD with the tag compared by subtle.eq (equal to list equality).
def open_checked_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +aad: List<&2, U32>, +c: List<&2, U32>, +t: List<&2, U32>) -> {I.open_checked(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, aad, c, t) == G.open_checked(nk, nr, key, nonce(q0, q1, q2), aad, c, t) : Maybe<&2, List<&2, U32>>}:
  match q0 q1 q2:
    case T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}:
      %gctr_ok(nk, nr, key, c, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2) : {I.open_checked(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c, t) == G.accept(Eq.equal(t, G.tag(nk, nr, key, [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], aad, c)), _) : Maybe<&2, List<&2, U32>>}
      %tag_ok(nk, nr, key, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c) : {I.open_checked(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c, t) == G.accept(Eq.equal(t, _), I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, c, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2)) : Maybe<&2, List<&2, U32>>}
      %EqLaws.Eq.value(t, I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c)) : {I.open_checked(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c, t) == G.accept(_, I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, c, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2)) : Maybe<&2, List<&2, U32>>}
      accept_ok(Subtle.eq(t, I.tag(A.Schedule{nr, A.expand(nk, nr, key)}, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, aad, c)), I.gctr(A.Schedule{nr, A.expand(nk, nr, key)}, c, T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, 2))

def open_split_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +aad: List<&2, U32>, +input: List<&2, U32>, +n: Nat, +short: Bool) -> {I.open_split(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, aad, input, n, short) == G.open_split(nk, nr, key, nonce(q0, q1, q2), aad, input, n, short) : Maybe<&2, List<&2, U32>>}:
  match short:
    case True{}:
      {==}
    case False{}:
      open_checked_ok(nk, nr, key, q0, q1, q2, aad, List.take(&2, U32, input, Nat.sub(n, 16n)), List.drop(&2, U32, input, Nat.sub(n, 16n)))

def open_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +q0: T.Quad, +q1: T.Quad, +q2: T.Quad, +aad: List<&2, U32>, +input: List<&2, U32>) -> {I.open_core(A.Schedule{nr, A.expand(nk, nr, key)}, q0, q1, q2, aad, input) == G.open(nk, nr, key, nonce(q0, q1, q2), aad, input) : Maybe<&2, List<&2, U32>>}:
  open_split_ok(nk, nr, key, q0, q1, q2, aad, input, List.length(&2, U32, input), Nat.is_lt(List.length(&2, U32, input), 16n))
