#!/usr/bin/env python3
"""Generate src/crypto/aes/fast.bend: the fast AES-GCM path.

  python3 tools/generators/aes/fast.py
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
X32 = ['x%d' % i for i in range(32)]
PW = ['p%d' % i for i in range(128)]   # V_(32j+i).w_k is p(4i+k)
KS = ['a0', 'a1', 'a2', 'a3', 'b0', 'b1', 'b2', 'b3']
KB = ['k%d' % i for i in range(16)]   # last round key bytes, column-major


def ks_byte(t):
    """keystream byte t (0..31) from the planes-ortho words a0..a3, b0..b3 and
    the last round key bytes k0..k15"""
    w = KS[t // 4]
    r = t % 4
    e = 'U32.and(255, %s)' % w if r == 0 else 'U32.and(255, U32.shrn(%s, %dn))' % (w, 8 * r)
    return 'U32.xor(%s, %s)' % (e, KB[t % 16])


OUT_PAT = 'Out{X.Q8{+a0, +b0, +a1, +b1, +a2, +b2, +a3, +b3}, T.S{T.W{+k0, +k1, +k2, +k3}, T.W{+k4, +k5, +k6, +k7}, T.W{+k8, +k9, +k10, +k11}, T.W{+k12, +k13, +k14, +k15}}}'


def word_mul():
    out = ['# Algorithm 1 of SP 800-38D over the 32 bits of four bytes b0..b3 of X, the',
           '# most significant first: Z ^= V & (0 - x_i), V = V * x (the steps of',
           '# gcm.bend, unrolled).',
           'def word_mul(+b0: U32, +b1: U32, +b2: U32, +b3: U32, a: G.Acc) -> G.Acc:',
           '  match a:',
           '    case G.Acc{G.B{z0, z1, z2, z3}, G.B{+v0, +v1, +v2, +v3}}:']
    z = ['z0', 'z1', 'z2', 'z3']
    v = ['v0', 'v1', 'v2', 'v3']
    for i in range(32):
        byte, k = i // 8, 7 - i % 8
        bit = 'U32.and(1, b%d)' % byte if k == 0 else 'U32.and(1, U32.shrn(b%d, %dn))' % (byte, k)
        out.append('      +m%d = U32.sub(0, %s)' % (i, bit))
        nz = ['z%d_%d' % (kk, i) for kk in range(4)]
        for kk in range(4):
            out.append('      %s%s = U32.xor(%s, U32.and(m%d, %s))' % ('' if i == 31 else '+', nz[kk], z[kk], i, v[kk]))
        nv = ['v%d_%d' % (kk, i) for kk in range(4)]
        a_, b_, c_, d_ = v
        out.append('      +%s = U32.xor(U32.and(3774873600, U32.sub(0, U32.and(1, %s))), U32.shrn(%s, 1n))' % (nv[0], d_, a_))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (nv[1], a_, b_))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (nv[2], b_, c_))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (nv[3], c_, d_))
        z, v = nz, nv
    out.append('      G.Acc{G.B{%s}, G.B{%s}}' % (', '.join(z), ', '.join(v)))
    return out


def powers():
    out = ['# The 32 powers V, V*x, ..., V*x^31, and V*x^32 (G.mulx, inlined).',
           'def powers32(v: G.Block) -> PowStep:',
           '  match v:',
           '    case G.B{+a0, +b0, +c0, +d0}:']
    cur = ['a0', 'b0', 'c0', 'd0']
    fields = []
    for i in range(32):
        fields += cur
        n = ['a%d' % (i + 1), 'b%d' % (i + 1), 'c%d' % (i + 1), 'd%d' % (i + 1)]
        a, b, c, d = cur
        out.append('      +%s = U32.xor(U32.and(3774873600, U32.sub(0, U32.and(1, %s))), U32.shrn(%s, 1n))' % (n[0], d, a))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (n[1], a, b))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (n[2], b, c))
        out.append('      +%s = U32.or(U32.shln(%s, 31n), U32.shrn(%s, 1n))' % (n[3], c, d))
        cur = n
    out.append('      PowStep{PW{%s}, G.B{%s}}' % (', '.join(fields), ', '.join(cur)))
    return out


def seal_body():
    L = ['# The ciphertext of the rest of the message, then the tag: o is the',
         '# encryption of counters c and c + 1, y the GHASH state so far.',
         'def seal_body(+x: Ctx, +xs: List<&2, U32>, +c: U32, y: G.Block, o: Out) -> List<&2, U32>:',
         '  match xs o:',
         '    case %s <> rest %s:' % (' <> '.join(X32), OUT_PAT)]
    for t in range(32):
        L.append('      +e%d = U32.xor(x%d, %s)' % (t, t, ks_byte(t)))
    L.append('      +y2 = absorb(ctx_pw(x), absorb(ctx_pw(x), y, %s), %s)' % (', '.join('e%d' % t for t in range(16)), ', '.join('e%d' % t for t in range(16, 32))))
    L.append('      %s <> seal_body(x, rest, U32.inc(U32.inc(c)), y2, ctr2(ctx_keys(x), ctx_nonce(x), U32.inc(U32.inc(c))))' % ' <> '.join('e%d' % t for t in range(32)))
    L += ['    case Nil{} _:', '      finish(x, y)',
          '    case _ _:', '      seal_tail(x, xor_into(xs, stream(o), Nil{}), y)']
    return L


def open_body():
    F32 = ['f%d' % i for i in range(32)]
    L = ['type Opened is Data:', '  Opened{pt: List<&2, U32>, ok: Bool}', '',
         'def prepend32(%s, o: Opened) -> Opened:' % ', '.join('%s: U32' % f for f in F32),
         '  match o:', '    case Opened{ps, ok}:', '      Opened{%s <> ps, ok}' % ' <> '.join(F32), '',
         '# The last ciphertext bytes (fewer than 32), then the received tag t.',
         'def open_tail(+x: Ctx, +ct: List<&2, U32>, t: List<&2, U32>, y: G.Block, o: Out) -> Opened:',
         '  Opened{xor_into(ct, stream(o), Nil{}), Subtle.eq(t, finish(x, ghash(ctx_pw(x), ct, y)))}', '',
         '# The plaintext of the first m bytes of xs (the ciphertext left), and',
         '# whether the bytes after them are the tag.',
         'def open_body(+x: Ctx, +m: Nat, +xs: List<&2, U32>, +c: U32, y: G.Block, o: Out) -> Opened:',
         '  match m xs o:',
         '    case 32n+p %s <> rest %s:' % (' <> '.join('+' + v for v in X32), OUT_PAT)]
    for t in range(32):
        L.append('      +f%d = U32.xor(x%d, %s)' % (t, t, ks_byte(t)))
    L.append('      +y2 = absorb(ctx_pw(x), absorb(ctx_pw(x), y, %s), %s)' % (', '.join('x%d' % t for t in range(16)), ', '.join('x%d' % t for t in range(16, 32))))
    L.append('      prepend32(%s, open_body(x, p, rest, U32.inc(U32.inc(c)), y2, ctr2(ctx_keys(x), ctx_nonce(x), U32.inc(U32.inc(c)))))' % ', '.join(F32))
    L += ['    case _ _ _:', '      open_tail(x, List.take(&2, U32, xs, m), List.drop(&2, U32, xs, m), y, o)']
    return L


HEAD = '''import Base
import ./types.bend as T
import ./aes.bend as A
import ./gcm.bend as G
import ./bitslice.bend as X
import ../subtle.bend as Subtle

# Generated by tools/generators/aes/fast.py.
#
# AES-GCM, the fast path of aesgcm.bend: the counter blocks are encrypted two
# at a time with the bitsliced AES of bitslice.bend; GHASH multiplies by H
# with Algorithm 1 of SP 800-38D over the precomputed powers H * x^i
# (i < 128, once per message), unrolled over each 32-bit word; encryption
# and GHASH run in one pass over the message. No table is indexed by data,
# no branch depends on data. Proved equal to gcm.bend (and so to SP 800-38D)
# for every input (proofs/crypto/aes/fast*.bend).

# ---- bytes and words ----

def le32(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.and(255, b0), U32.or(U32.shln(U32.and(255, b1), 8n), U32.or(U32.shln(U32.and(255, b2), 16n), U32.shln(U32.and(255, b3), 24n))))

# The big-endian word of four bytes (the formula of gcm.bend's word).
def be32(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.shln(U32.and(255, b0), 24n), U32.or(U32.shln(U32.and(255, b1), 16n),
    U32.or(U32.shln(U32.and(255, b2), 8n), U32.and(255, b3))))

# The bytes of a counter c as a little-endian word: be32's byte order reversed.
def bswap(+c: U32) -> U32:
  le32(U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c))

def quad_word(q: T.Quad) -> U32:
  match q:
    case T.W{a, b, c, d}: le32(a, b, c, d)

# A round key in bit planes (both blocks get the same key).
def plane_key(k: T.State) -> X.Q8:
  match k:
    case T.S{c0, c1, c2, c3}:
      +w0 = quad_word(c0)
      +w1 = quad_word(c1)
      +w2 = quad_word(c2)
      +w3 = quad_word(c3)
      X.ortho(X.Q8{w0, w0, w1, w1, w2, w2, w3, w3})

# A round key in bit planes and as bytes (the last one is added to the
# output bytes).
type KP is Data:
  KP{plane: X.Q8, bytes: T.State}

def key_planes(ks: List<&2, T.State>) -> List<&2, KP>:
  match ks:
    case Nil{}: Nil{}
    case +k <> rest: KP{plane_key(k), k} <> key_planes(rest)

type Keys is Data:
  Keys{rounds: Nat, kps: List<&2, KP>}

def keys_of(s: A.Schedule) -> Keys:
  match s:
    case A.Schedule{nr, ks}: Keys{nr, key_planes(ks)}

# The planes after the last ShiftRows and the last round key.
type Out is Data:
  Out{q: X.Q8, k: T.State}

def zero_state() -> T.State:
  T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}

# n full rounds, then the last one (its AddRoundKey left to the bytes).
def rounds(n: Nat, q: X.Q8, ks: List<&2, KP>) -> Out:
  match n ks:
    case 0n KP{p, kb} <> rest:
      Out{X.shift_rows(X.sub_bytes(q)), kb}
    case 1n+m KP{p, kb} <> rest:
      rounds(m, X.round(q, p), rest)
    case _ _:
      Out{q, zero_state()}

def cipher(+nr: Nat, q: X.Q8, ks: List<&2, KP>) -> Out:
  match ks:
    case KP{p, kb} <> rest:
      rounds(Nat.sub(nr, 1n), X.add_round_key(q, p), rest)
    case Nil{}:
      Out{q, zero_state()}

def unplane(o: Out) -> Out:
  match o:
    case Out{q, k}: Out{X.ortho(q), k}

# Two blocks, as little-endian words a0..a3 and b0..b3.
def encrypt2(k: Keys, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32) -> Out:
  match k:
    case Keys{nr, ks}:
      unplane(cipher(nr, X.ortho(X.Q8{a0, b0, a1, b1, a2, b2, a3, b3}), ks))

# The 32 output bytes (the first block, then the second).
def stream(o: Out) -> List<&2, U32>:
  match o:
    case %s:
      [%s]

type Nonce is Data:
  N{n0: U32, n1: U32, n2: U32}

# The counter blocks nonce || c and nonce || c + 1.
def ctr2(+k: Keys, n: Nonce, +c: U32) -> Out:
  match n:
    case N{+n0, +n1, +n2}:
      encrypt2(k, n0, n1, n2, bswap(c), n0, n1, n2, bswap(U32.inc(c)))

def xor_into(xs: List<&2, U32>, ks: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match xs ks:
    case x <> xt k <> kt:
      U32.xor(x, k) <> xor_into(xt, kt, rest)
    case _ _:
      rest

# ---- GHASH ----

''' % (OUT_PAT, ', '.join(ks_byte(t) for t in range(32)))

MID = '''
def step_pw(s: PowStep) -> PW:
  match s:
    case PowStep{p, v}: p

def step_next(s: PowStep) -> G.Block:
  match s:
    case PowStep{p, v}: v

# H * x^i for i < 128.
def pows(h: G.Block) -> Pows:
  +s0 = powers32(h)
  +s1 = powers32(step_next(s0))
  +s2 = powers32(step_next(s1))
  Pows{step_pw(s0), step_pw(s1), step_pw(s2), step_pw(powers32(step_next(s2)))}
'''

GH = '''
# (Y xor X) * H for the 16 bytes x0..x15 of X.
def absorb(+h: G.Block, y: G.Block, +x0: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +x8: U32, +x9: U32, +x10: U32, +x11: U32, +x12: U32, +x13: U32, +x14: U32, +x15: U32) -> G.Block:
  match y:
    case G.B{+y0, +y1, +y2, +y3}:
      G.acc_z(word_mul(U32.xor(U32.and(255, U32.shrn(y3, 24n)), x12), U32.xor(U32.and(255, U32.shrn(y3, 16n)), x13), U32.xor(U32.and(255, U32.shrn(y3, 8n)), x14), U32.xor(U32.and(255, y3), x15), word_mul(U32.xor(U32.and(255, U32.shrn(y2, 24n)), x8), U32.xor(U32.and(255, U32.shrn(y2, 16n)), x9), U32.xor(U32.and(255, U32.shrn(y2, 8n)), x10), U32.xor(U32.and(255, y2), x11), word_mul(U32.xor(U32.and(255, U32.shrn(y1, 24n)), x4), U32.xor(U32.and(255, U32.shrn(y1, 16n)), x5), U32.xor(U32.and(255, U32.shrn(y1, 8n)), x6), U32.xor(U32.and(255, y1), x7), word_mul(U32.xor(U32.and(255, U32.shrn(y0, 24n)), x0), U32.xor(U32.and(255, U32.shrn(y0, 16n)), x1), U32.xor(U32.and(255, U32.shrn(y0, 8n)), x2), U32.xor(U32.and(255, y0), x3), G.Acc{G.zero(), h})))))

def absorb16(+pw: G.Block, y: G.Block, xs: List<&2, U32>) -> G.Block:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      absorb(pw, y, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15)
    case _:
      y

# GHASH over the bytes, a last partial block padded with zero bytes.
def ghash(+pw: G.Block, +xs: List<&2, U32>, y: G.Block) -> G.Block:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      ghash(pw, rest, absorb(pw, y, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15))
    case Nil{}:
      y
    case _:
      absorb16(pw, y, List.append(&2, U32, xs, G.zeros(Nat.sub(16n, List.length(&2, U32, xs)))))

# ---- GCM ----

# H = E(K, 0^128) (the first 16 bytes), as big-endian words.
def hash_key(bs: List<&2, U32>) -> G.Block:
  match bs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest:
      G.B{be32(x0, x1, x2, x3), be32(x4, x5, x6, x7), be32(x8, x9, x10, x11), be32(x12, x13, x14, x15)}
    case _:
      G.zero()

# Everything the message loop needs: the keys, the nonce, the powers of H,
# the last GHASH input (the lengths) and the tag mask E(K, J0).
type Ctx is Data:
  Ctx{keys: Keys, nonce: Nonce, pw: G.Block, lens: List<&2, U32>, j0: List<&2, U32>}

def ctx_keys(x: Ctx) -> Keys:
  match x:
    case Ctx{k, n, pw, l, j}: k

def ctx_nonce(x: Ctx) -> Nonce:
  match x:
    case Ctx{k, n, pw, l, j}: n

def ctx_pw(x: Ctx) -> G.Block:
  match x:
    case Ctx{k, n, pw, l, j}: pw

# The tag from the GHASH state after A || 0^v || C || 0^u.
def finish(+x: Ctx, y: G.Block) -> List<&2, U32>:
  match x:
    case Ctx{k, n, pw, lens, j0}: xor_into(G.unpack(ghash(pw, lens, y)), j0, Nil{})

# [len(A)]_64 || [len(C)]_64, in bits, C having m bytes.
def lengths(+aad: List<&2, U32>, +m: Nat) -> List<&2, U32>:
  List.append(&2, U32, G.octets(8n, Nat.mul(8n, List.length(&2, U32, aad))), G.octets(8n, Nat.mul(8n, m)))

def context(+k: Keys, +n: Nonce, +aad: List<&2, U32>, +m: Nat) -> Ctx:
  Ctx{k, n, hash_key(stream(encrypt2(k, 0, 0, 0, 0, 0, 0, 0, 0))), lengths(aad, m), List.take(&2, U32, stream(ctr2(k, n, 1)), 16n)}

# The last ciphertext bytes (fewer than 32) and the tag.
def seal_tail(+x: Ctx, +ct: List<&2, U32>, y: G.Block) -> List<&2, U32>:
  List.append(&2, U32, ct, finish(x, ghash(ctx_pw(x), ct, y)))
''' 

TAIL = '''
def accept(o: Opened) -> Maybe<&2, List<&2, U32>>:
  match o:
    case Opened{ps, ok}: G.accept(ok, ps)

# GCM-AE: C || T.
def seal(+k: Keys, +n: Nonce, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  +x = context(k, n, aad, List.length(&2, U32, pt))
  seal_body(x, pt, 2, ghash(ctx_pw(x), aad, G.zero()), ctr2(k, n, 2))

def open_split(+k: Keys, +n: Nonce, +aad: List<&2, U32>, +input: List<&2, U32>, +m: Nat, short: Bool) -> Maybe<&2, List<&2, U32>>:
  match short:
    case True{}:
      None{}
    case False{}:
      +x = context(k, n, aad, m)
      accept(open_body(x, m, input, 2, ghash(ctx_pw(x), aad, G.zero()), ctr2(k, n, 2)))

# GCM-AD on C || T: the plaintext, or None when T is not the tag of C.
def open(+k: Keys, +n: Nonce, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +len = List.length(&2, U32, input)
  open_split(k, n, aad, input, Nat.sub(len, 16n), Nat.is_lt(len, 16n))

# ---- the byte API (see aesgcm.bend) ----

# The key schedule has the 2 + (Nr - 1) round keys the cipher reads.
def well_formed(s: A.Schedule) -> Bool:
  match s:
    case A.Schedule{nr, ks}: Nat.is_eq(List.length(&2, T.State, ks), 2n+Nat.sub(nr, 1n))

def seal_nonce(+s: A.Schedule, nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nonce:
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      Some{seal(keys_of(s), N{le32(n0, n1, n2, n3), le32(n4, n5, n6, n7), le32(n8, n9, n10, n11)}, aad, pt)}
    case _:
      None{}

def open_nonce(+s: A.Schedule, nonce: List<&2, U32>, +aad: List<&2, U32>, +input: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match nonce:
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      open(keys_of(s), N{le32(n0, n1, n2, n3), le32(n4, n5, n6, n7), le32(n8, n9, n10, n11)}, aad, input)
    case _:
      None{}

'''


def main():
    s = HEAD.split('\n') + word_mul() + GH.split('\n') + seal_body() + [''] + open_body() + TAIL.split('\n')
    (ROOT / 'src/crypto/aes/fast.bend').write_text('\n'.join(s))


if __name__ == '__main__':
    main()
