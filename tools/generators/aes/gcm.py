#!/usr/bin/env python3
"""Generate proofs/crypto/aes/gcm.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

xs=['x%d'%i for i in range(16)]
L=lambda v: '[%s]' % ', '.join(v)
Q='q0, q1, q2'
QT='+q0: T.Quad, +q1: T.Quad, +q2: T.Quad'
QD='T.W{a0, a1, a2, a3} T.W{a4, a5, a6, a7} T.W{a8, a9, a10, a11}'
IV='[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]'
SCH='A.Schedule{nr, A.expand(nk, nr, key)}'
out = '''import Base
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
    case %s:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c)]

# The 96-bit nonce.
def nonce(q0: T.Quad, q1: T.Quad, q2: T.Quad) -> List<&2, U32>:
  match q0 q1 q2:
    case %s:
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]

def bytes_of_ok(+st: T.State) -> {A.bytes_of(st) == S.bytes_of(st) : List<&2, U32>}:
  match st:
    case T.S{T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, T.W{a12, a13, a14, a15}}:
      {==}

def xor_ok(+xs: List<&2, U32>, +ks: List<&2, U32>) -> {I.xor_bytes(xs, ks) == G.xor_bytes(xs, ks) : List<&2, U32>}:
  match xs ks:
    case x <> xt k <> kt:
      %%xor_ok(xt, kt) : {U32.xor(x, k) <> I.xor_bytes(xt, kt) == U32.xor(x, k) <> _ : List<&2, U32>}
      {==}
    case Nil{} _:
      {==}
    case x <> xt Nil{}:
      {==}

def keystream_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, %s, +c: U32) -> {I.keystream(%s, %s, c) == G.ciph(nk, nr, key, cb(%s, c)) : List<&2, U32>}:
  match q0 q1 q2:
    case %s:
      %%C.encrypt_ok(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c)) : {A.bytes_of(A.encrypt(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c))) == S.bytes_of(_) : List<&2, U32>}
      bytes_of_ok(A.encrypt(nk, nr, key, I.counter(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, c)))

def inc_ok(%s, +c: U32) -> {G.inc32(cb(%s, c)) == cb(%s, U32.inc(c)) : List<&2, U32>}:
  match q0 q1 q2:
    case %s:
      %%Equal.sym(U32, G.int32(U32.and(255, U32.shrn(c, 24n)), U32.and(255, U32.shrn(c, 16n)), U32.and(255, U32.shrn(c, 8n)), U32.and(255, c)), c, B.int32_ctr(c)) : {List.append(&2, U32, %s, G.str32(U32.inc(_))) == cb(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, U32.inc(c)) : List<&2, U32>}
      %%Equal.sym(List<&2, U32>, G.str32(U32.inc(c)), [U32.and(255, U32.shrn(U32.inc(c), 24n)), U32.and(255, U32.shrn(U32.inc(c), 16n)), U32.and(255, U32.shrn(U32.inc(c), 8n)), U32.and(255, U32.inc(c))], B.str32_ctr(U32.inc(c))) : {List.append(&2, U32, %s, _) == cb(T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, U32.inc(c)) : List<&2, U32>}
      {==}

''' % (QD, QD, QT, SCH, Q, Q, QD, QT, Q, Q, QD, IV, IV)
# gctr_ok
cases=[]
full='x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> rest'
cases.append('''    case %s:
      %%Equal.sym(List<&2, U32>, G.inc32(cb(%s, c)), cb(%s, U32.inc(c)), inc_ok(%s, c)) : {I.gctr(%s, xs, %s, c) == List.append(&2, U32, G.xor_bytes(%s, G.ciph(nk, nr, key, cb(%s, c))), G.gctr(nk, nr, key, rest, _)) : List<&2, U32>}
      %%gctr_ok(nk, nr, key, rest, %s, U32.inc(c)) : {I.gctr(%s, xs, %s, c) == List.append(&2, U32, G.xor_bytes(%s, G.ciph(nk, nr, key, cb(%s, c))), _) : List<&2, U32>}
      %%keystream_ok(nk, nr, key, %s, c) : {I.gctr(%s, xs, %s, c) == List.append(&2, U32, G.xor_bytes(%s, _), I.gctr(%s, rest, %s, U32.inc(c))) : List<&2, U32>}
      %%xor_ok(%s, I.keystream(%s, %s, c)) : {I.gctr(%s, xs, %s, c) == List.append(&2, U32, _, I.gctr(%s, rest, %s, U32.inc(c))) : List<&2, U32>}
      {==}''' % (full, Q, Q, Q, SCH, Q, L(xs), Q,
                 Q, SCH, Q, L(xs), Q,
                 Q, SCH, Q, L(xs), SCH, Q,
                 L(xs), SCH, Q, SCH, Q, SCH, Q))
for k in range(0,16):
    pat = 'Nil{}' if k == 0 else ' <> '.join(xs[:k]) + ' <> Nil{}'
    lst = L(xs[:k])
    cases.append('''    case %s:
      %%keystream_ok(nk, nr, key, %s, c) : {I.gctr(%s, xs, %s, c) == G.xor_bytes(%s, _) : List<&2, U32>}
      xor_ok(%s, I.keystream(%s, %s, c))''' % (pat, Q, SCH, Q, lst, lst, SCH, Q))
out += '''# Counter mode from counter c (a whole block per counter; a last partial
# block uses the leftmost bytes of its keystream block).
def gctr_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +xs: List<&2, U32>, %s, +c: U32) -> {I.gctr(%s, xs, %s, c) == G.gctr(nk, nr, key, xs, cb(%s, c)) : List<&2, U32>}:
  match xs:
%s

''' % (QT, SCH, Q, Q, '\n'.join(cases))
Y='I.ghash(I.hash_key(%s), I.lengths(aad, c), I.ghash(I.hash_key(%s), c, I.ghash(I.hash_key(%s), aad, I.zero())))' % (SCH, SCH, SCH)
GH='G.ghash(G.hash_key(nk, nr, key), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n))'
GHR='G.ghash(D.R(I.hash_key(%s)), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n))' % SCH
QW='T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}'
ITAG='I.tag(%s, %s, aad, c)' % (SCH, QW)
out += '''def hash_key_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>) -> {D.R(I.hash_key(%s)) == G.hash_key(nk, nr, key) : Word(128n)}:
  %%C.encrypt_ok(nk, nr, key, T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}) : {D.R(I.hash_key(%s)) == G.block(S.bytes_of(_)) : Word(128n)}
  H.pack_ok(A.encrypt(nk, nr, key, T.S{T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}, T.W{0, 0, 0, 0}}))

# The tag: GCTR from J0 over GHASH of A, C and their lengths.
def tag_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, %s, +aad: List<&2, U32>, +c: List<&2, U32>) -> {I.tag(%s, %s, aad, c) == G.tag(nk, nr, key, nonce(%s), aad, c) : List<&2, U32>}:
  match q0 q1 q2:
    case %s:
      %%hash_key_ok(nk, nr, key) : {%s == G.gctr(nk, nr, key, G.block_bytes(G.ghash(_, List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n))), G.j0(%s)) : List<&2, U32>}
      %%Equal.sym(Word(128n), %s, D.R(%s), H.ghash_all_ok(I.hash_key(%s), aad, c)) : {%s == G.gctr(nk, nr, key, G.block_bytes(_), G.j0(%s)) : List<&2, U32>}
      %%Equal.sym(List<&2, U32>, G.block_bytes(D.R(%s)), I.unpack(%s), B.bb_ok(%s)) : {%s == G.gctr(nk, nr, key, _, G.j0(%s)) : List<&2, U32>}
      gctr_ok(nk, nr, key, I.unpack(%s), %s, 1)

''' % (SCH, SCH, QT, SCH, Q, Q, QD, ITAG, IV,
       GHR, Y, SCH, ITAG, IV,
       Y, Y, Y, ITAG, IV,
       Y, QW)
open('proofs/crypto/aes/gcm.bend','w').write(out)
def fill(t):
    for k, v in [('@QT@', QT), ('@SCH@', SCH), ('@QD@', QD), ('@QW@', QW), ('@IV@', IV), ('@Q@', Q)]:
        t = t.replace(k, v)
    return t
out2 = fill('''# GCM-AE: C = GCTR(inc32(J0), P), T = the tag of C.
def seal_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, @QT@, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {I.seal_core(@SCH@, @Q@, aad, pt) == G.seal(nk, nr, key, nonce(@Q@), aad, pt) : List<&2, U32>}:
  match q0 q1 q2:
    case @QD@:
      %gctr_ok(nk, nr, key, pt, @QW@, 2) : {I.seal_core(@SCH@, @QW@, aad, pt) == List.append(&2, U32, _, G.tag(nk, nr, key, @IV@, aad, _)) : List<&2, U32>}
      %tag_ok(nk, nr, key, @QW@, aad, I.gctr(@SCH@, pt, @QW@, 2)) : {I.seal_core(@SCH@, @QW@, aad, pt) == List.append(&2, U32, I.gctr(@SCH@, pt, @QW@, 2), _) : List<&2, U32>}
      {==}

def accept_ok(+ok: Bool, +p: List<&2, U32>) -> {I.accept(ok, p) == G.accept(ok, p) : Maybe<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# GCM-AD with the tag compared by subtle.eq (equal to list equality).
def open_checked_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, @QT@, +aad: List<&2, U32>, +c: List<&2, U32>, +t: List<&2, U32>) -> {I.open_checked(@SCH@, @Q@, aad, c, t) == G.open_checked(nk, nr, key, nonce(@Q@), aad, c, t) : Maybe<&2, List<&2, U32>>}:
  match q0 q1 q2:
    case @QD@:
      %gctr_ok(nk, nr, key, c, @QW@, 2) : {I.open_checked(@SCH@, @QW@, aad, c, t) == G.accept(Eq.equal(t, G.tag(nk, nr, key, @IV@, aad, c)), _) : Maybe<&2, List<&2, U32>>}
      %tag_ok(nk, nr, key, @QW@, aad, c) : {I.open_checked(@SCH@, @QW@, aad, c, t) == G.accept(Eq.equal(t, _), I.gctr(@SCH@, c, @QW@, 2)) : Maybe<&2, List<&2, U32>>}
      %EqLaws.Eq.value(t, I.tag(@SCH@, @QW@, aad, c)) : {I.open_checked(@SCH@, @QW@, aad, c, t) == G.accept(_, I.gctr(@SCH@, c, @QW@, 2)) : Maybe<&2, List<&2, U32>>}
      accept_ok(Subtle.eq(t, I.tag(@SCH@, @QW@, aad, c)), I.gctr(@SCH@, c, @QW@, 2))

def open_split_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, @QT@, +aad: List<&2, U32>, +input: List<&2, U32>, +n: Nat, +short: Bool) -> {I.open_split(@SCH@, @Q@, aad, input, n, short) == G.open_split(nk, nr, key, nonce(@Q@), aad, input, n, short) : Maybe<&2, List<&2, U32>>}:
  match short:
    case True{}:
      {==}
    case False{}:
      open_checked_ok(nk, nr, key, @Q@, aad, List.take(&2, U32, input, Nat.sub(n, 16n)), List.drop(&2, U32, input, Nat.sub(n, 16n)))

def open_ok(+nk: Nat, +nr: Nat, +key: List<&2, U32>, @QT@, +aad: List<&2, U32>, +input: List<&2, U32>) -> {I.open_core(@SCH@, @Q@, aad, input) == G.open(nk, nr, key, nonce(@Q@), aad, input) : Maybe<&2, List<&2, U32>>}:
  open_split_ok(nk, nr, key, @Q@, aad, input, List.length(&2, U32, input), Nat.is_lt(List.length(&2, U32, input), 16n))
''')
open('proofs/crypto/aes/gcm.bend','a').write(out2)

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/gcm.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/gcm.py.')
_out.write_text('\n'.join(_lines))
