#!/usr/bin/env python3
"""Generate proofs/crypto/aes/aead.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

xs=['x%d'%i for i in range(16)]
ts=['t%d'%i for i in range(16)]
L=lambda v: '[%s]' % ', '.join(v)
K='nk, nr, key'
KT='+nk: Nat, +nr: Nat, +key: List<&2, U32>'
def ks(cb, i): return 'kb(nk, nr, key, %s, %dn)' % (cb, i)
def cons(items, tail): return ' <> '.join(items + [tail])
ST='S.encrypt(nk, nr, key, S.state_of(cb))'
EXPL=L(['S.nth_byte(S.bytes_of(%s), %dn)' % (ST, i) for i in range(16)])
out = ['''import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ../../../spec/crypto/subtle.bend as Eq
import ../subtle/laws.bend as EqLaws
import ../subtle/proof.bend as EqProof

# AEAD correctness of the specification (SP 800-38D GCM over FIPS 197):
# opening a sealed message gives the message back, and opening C || T with
# a T other than the tag of C gives None. The implementation equals the
# specification (gcm.bend), so both carry over to it (laws.bend).

def bxor_inv(+x: Bool, +y: Bool) -> {Bool.xor(Bool.xor(x, y), y) == x : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def word_xor_inv(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}:
  match n a b:
    case 0n WNil{} WNil{}:
      {==}
    case 1n+p WCon{x, s} WCon{y, t}:
      %%word_xor_inv(p, s, t) : {WCon{Bool.xor(Bool.xor(x, y), y), Word.xor(p, Word.xor(p, s, t), t)} == WCon{x, _} : Word(1n+p)}
      %%bxor_inv(x, y) : {WCon{Bool.xor(Bool.xor(x, y), y), Word.xor(p, Word.xor(p, s, t), t)} == WCon{_, Word.xor(p, Word.xor(p, s, t), t)} : Word(1n+p)}
      {==}

def xor_inv(+x: U32, +k: U32) -> {U32.xor(U32.xor(x, k), k) == x : U32}:
  match x k:
    case U32{a} U32{b}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.xor(32n, Word.xor(32n, a, b), b), a, word_xor_inv(32n, a, b))

def ks_ok(+st: T.State) -> {S.bytes_of(st) == %s : List<&2, U32>}:
  match st:
    case T.S{T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, T.W{a12, a13, a14, a15}}:
      {==}
''' % L(['S.nth_byte(S.bytes_of(st), %dn)' % i for i in range(16)])]

out.append("""# Byte i of the keystream block of counter block cb, and the block as a list.
def kb(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +cb: List<&2, U32>, +i: Nat) -> U32:
  S.nth_byte(G.ciph(nk, nr, key, cb), i)

def kl(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +cb: List<&2, U32>) -> List<&2, U32>:
  %s

def ciph_kl(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +cb: List<&2, U32>) -> {G.ciph(nk, nr, key, cb) == kl(nk, nr, key, cb) : List<&2, U32>}:
  ks_ok(%s)
""" % (L([ks('cb', i) for i in range(16)]), ST))
out.append('''# x is no longer than k.
def fits(x: List<&2, U32>, k: List<&2, U32>) -> Bool:
  match x:
    case Nil{}:
      True{}
    case a <> xs:
      match k:
        case Nil{}:
          False{}
        case b <> ks:
          fits(xs, ks)

# (x xor k) xor k == x, byte by byte.
def xb_inv(+x: List<&2, U32>, +k: List<&2, U32>, +h: {fits(x, k) == True{} : Bool}) -> {G.xor_bytes(G.xor_bytes(x, k), k) == x : List<&2, U32>}:
  match x:
    case Nil{}:
      match k:
        case Nil{}:
          {==}
        case b <> ks:
          {==}
    case a <> xs:
      match k:
        case Nil{}:
          Empty.absurd({G.xor_bytes(G.xor_bytes(a <> xs, Nil{}), Nil{}) == a <> xs : List<&2, U32>}, L.false_true(h))
        case b <> ks:
          %Equal.sym(U32, U32.xor(U32.xor(a, b), b), a, xor_inv(a, b)) : {_ <> G.xor_bytes(G.xor_bytes(xs, ks), ks) == a <> xs : List<&2, U32>}
          %Equal.sym(List<&2, U32>, G.xor_bytes(G.xor_bytes(xs, ks), ks), xs, xb_inv(xs, ks, h)) : {a <> _ == a <> xs : List<&2, U32>}
          {==}
''')
X16 = L(xs)
out.append('''# One whole block of counter mode, and a last partial one, with the keystream as kl.
def gctr_full(%s, %s, +rest: List<&2, U32>, +cb: List<&2, U32>) -> {List.append(&2, U32, G.xor_bytes(%s, kl(nk, nr, key, cb)), G.gctr(nk, nr, key, rest, G.inc32(cb))) == G.gctr(nk, nr, key, %s, cb) : List<&2, U32>}:
  %%ciph_kl(nk, nr, key, cb) : {List.append(&2, U32, G.xor_bytes(%s, _), G.gctr(nk, nr, key, rest, G.inc32(cb))) == G.gctr(nk, nr, key, %s, cb) : List<&2, U32>}
  {==}

def gctr_short(%s, +x: List<&2, U32>, +cb: List<&2, U32>, +e: {G.gctr(nk, nr, key, x, cb) == G.xor_bytes(x, G.ciph(nk, nr, key, cb)) : List<&2, U32>}) -> {G.xor_bytes(x, kl(nk, nr, key, cb)) == G.gctr(nk, nr, key, x, cb) : List<&2, U32>}:
  %%ciph_kl(nk, nr, key, cb) : {G.xor_bytes(x, _) == G.gctr(nk, nr, key, x, cb) : List<&2, U32>}
  Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, x, cb), G.xor_bytes(x, G.ciph(nk, nr, key, cb)), e)
''' % (KT, ', '.join('+%s: U32' % x for x in xs), X16, cons(xs, 'rest'), X16, cons(xs, 'rest'), KT))
full = cons(xs, 'rest')
Y = ['U32.xor(%s, %s)' % (xs[i], ks('cb', i)) for i in range(16)]
RR = 'G.gctr(nk, nr, key, G.gctr(nk, nr, key, rest, G.inc32(cb)), G.inc32(cb))'
cases = ['    case %s:' % full,
         '      %%gctr_full(nk, nr, key, %s, rest, cb) : {G.gctr(nk, nr, key, _, cb) == %s : List<&2, U32>}' % (', '.join(xs), full),
         '      %%gctr_full(nk, nr, key, %s, G.gctr(nk, nr, key, rest, G.inc32(cb)), cb) : {_ == %s : List<&2, U32>}' % (', '.join(Y), full),
         '      %%Equal.sym(List<&2, U32>, %s, rest, gctr_inv(nk, nr, key, rest, G.inc32(cb))) : {List.append(&2, U32, G.xor_bytes(%s, kl(nk, nr, key, cb)), _) == %s : List<&2, U32>}' % (RR, L(Y), full),
         '      Equal.cong(List<&2, U32>, List<&2, U32>, z => List.append(&2, U32, z, rest), G.xor_bytes(G.xor_bytes(%s, kl(nk, nr, key, cb)), kl(nk, nr, key, cb)), %s, xb_inv(%s, kl(nk, nr, key, cb), {==}))' % (X16, X16, X16),
         '    case Nil{}:', '      {==}']
for k in range(1, 16):
    v = L(xs[:k])
    yk = L(Y[:k])
    cases += ['    case %s:' % cons(xs[:k], 'Nil{}'),
              '      %%gctr_short(nk, nr, key, %s, cb, {==}) : {G.gctr(nk, nr, key, _, cb) == %s : List<&2, U32>}' % (v, v),
              '      %%gctr_short(nk, nr, key, %s, cb, {==}) : {_ == %s : List<&2, U32>}' % (yk, v),
              '      xb_inv(%s, kl(nk, nr, key, cb), {==})' % v]
out.append('''# Counter mode is an involution (the keystream is XORed twice).
def gctr_inv(%s, +xs: List<&2, U32>, +cb: List<&2, U32>) -> {G.gctr(nk, nr, key, G.gctr(nk, nr, key, xs, cb), cb) == xs : List<&2, U32>}:
  match xs:
%s
''' % (KT, '\n'.join(cases)))
# bb16
B=['w%d' % i for i in range(128)]
wpat = 'WNil{}'
for n in reversed(B): wpat = 'WCon{%s, %s}' % (n, wpat)
out.append('''def bb16(+w: Word(128n)) -> {G.block_bytes(w) == %s : List<&2, U32>}:
  match w:
    case %s:
      {==}
''' % (L(['S.nth_byte(G.block_bytes(w), %dn)' % i for i in range(16)]), wpat))
# tag16
W='G.ghash(G.hash_key(nk, nr, key), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n))'
BB='hb(nk, nr, key, aad, c)'
bb=['S.nth_byte(%s, %dn)' % (BB, i) for i in range(16)]
TT=L(['tb(nk, nr, key, iv, aad, c, %dn)' % i for i in range(16)])
out.append('''# The GHASH block of the tag, as bytes, and byte i of the tag.
def hb(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> List<&2, U32>:
  G.block_bytes(%s)

def tb(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>, +i: Nat) -> U32:
  U32.xor(S.nth_byte(hb(nk, nr, key, aad, c), i), kb(nk, nr, key, G.j0(iv), i))
''' % W)
BW = ['S.nth_byte(G.block_bytes(w), %dn)' % i for i in range(16)]
G16 = L(['U32.xor(%s, %s)' % (BW[i], ks('cb', i)) for i in range(16)])
out.append('''# Counter mode on one 16-byte block of a 128-bit word.
def gctr16(%s, +w: Word(128n), +cb: List<&2, U32>) -> {G.gctr(nk, nr, key, G.block_bytes(w), cb) == %s : List<&2, U32>}:
  %%Equal.sym(List<&2, U32>, G.block_bytes(w), %s, bb16(w)) : {G.gctr(nk, nr, key, _, cb) == %s : List<&2, U32>}
  %%gctr_full(nk, nr, key, %s, Nil{}, cb) : {_ == %s : List<&2, U32>}
  {==}

# The tag is a 16-byte list.
def tag16(%s, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> {G.tag(nk, nr, key, iv, aad, c) == %s : List<&2, U32>}:
  gctr16(nk, nr, key, %s, G.j0(iv))
''' % (KT, G16, L(BW), G16, ', '.join(BW), G16, KT, TT, W))
T16 = L(ts)
TP = ', '.join('+%s: U32' % t for t in ts)
out.append('''# Splitting C || T (T of 16 bytes) back into C and T.
def not_short(+c: List<&2, U32>, %s) -> {Nat.is_lt(List.length(&2, U32, List.append(&2, U32, c, %s)), 16n) == False{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case x <> r:
      N.le_not_lt(1n+List.length(&2, U32, List.append(&2, U32, r, %s)), 16n,
        N.le_trans(16n, List.length(&2, U32, List.append(&2, U32, r, %s)), 1n+List.length(&2, U32, List.append(&2, U32, r, %s)),
          N.not_lt_le(List.length(&2, U32, List.append(&2, U32, r, %s)), 16n, not_short(r, %s)),
          N.le_succ(List.length(&2, U32, List.append(&2, U32, r, %s)))))

def sub16(+c: List<&2, U32>, %s) -> {Nat.sub(List.length(&2, U32, List.append(&2, U32, c, %s)), 16n) == List.length(&2, U32, c) : Nat}:
  match c:
    case Nil{}:
      {==}
    case x <> r:
      %%Equal.sym(Nat, Nat.sub(1n+List.length(&2, U32, List.append(&2, U32, r, %s)), 16n), 1n+Nat.sub(List.length(&2, U32, List.append(&2, U32, r, %s)), 16n), N.sub_succ_left(List.length(&2, U32, List.append(&2, U32, r, %s)), 16n, N.not_lt_le(List.length(&2, U32, List.append(&2, U32, r, %s)), 16n, not_short(r, %s)))) : {_ == 1n+List.length(&2, U32, r) : Nat}
      %%sub16(r, %s) : {1n+Nat.sub(List.length(&2, U32, List.append(&2, U32, r, %s)), 16n) == 1n+_ : Nat}
      {==}

def take_app(+c: List<&2, U32>, %s) -> {List.take(&2, U32, List.append(&2, U32, c, %s), List.length(&2, U32, c)) == c : List<&2, U32>}:
  match c:
    case Nil{}:
      {==}
    case x <> r:
      %%take_app(r, %s) : {x <> List.take(&2, U32, List.append(&2, U32, r, %s), List.length(&2, U32, r)) == x <> _ : List<&2, U32>}
      {==}

def drop_app(+c: List<&2, U32>, %s) -> {List.drop(&2, U32, List.append(&2, U32, c, %s), List.length(&2, U32, c)) == %s : List<&2, U32>}:
  match c:
    case Nil{}:
      {==}
    case x <> r:
      drop_app(r, %s)
''' % (TP, T16, T16, T16, T16, T16, ', '.join(ts), T16,
       TP, T16, T16, T16, T16, T16, ', '.join(ts), ', '.join(ts), T16,
       TP, T16, ', '.join(ts), T16,
       TP, T16, T16, ', '.join(ts)))
IN='List.append(&2, U32, c, %s)' % T16
N_='List.length(&2, U32, %s)' % IN
out.append('''def open_append(%s, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>, %s) -> {G.open(nk, nr, key, iv, aad, %s) == G.open_checked(nk, nr, key, iv, aad, c, %s) : Maybe<&2, List<&2, U32>>}:
  %%Equal.sym(Bool, Nat.is_lt(%s, 16n), False{}, not_short(c, %s)) : {G.open_split(nk, nr, key, iv, aad, %s, %s, _) == G.open_checked(nk, nr, key, iv, aad, c, %s) : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Nat, Nat.sub(%s, 16n), List.length(&2, U32, c), sub16(c, %s)) : {G.open_checked(nk, nr, key, iv, aad, List.take(&2, U32, %s, _), List.drop(&2, U32, %s, _)) == G.open_checked(nk, nr, key, iv, aad, c, %s) : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(List<&2, U32>, List.take(&2, U32, %s, List.length(&2, U32, c)), c, take_app(c, %s)) : {G.open_checked(nk, nr, key, iv, aad, _, List.drop(&2, U32, %s, List.length(&2, U32, c))) == G.open_checked(nk, nr, key, iv, aad, c, %s) : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(List<&2, U32>, List.drop(&2, U32, %s, List.length(&2, U32, c)), %s, drop_app(c, %s)) : {G.open_checked(nk, nr, key, iv, aad, c, _) == G.open_checked(nk, nr, key, iv, aad, c, %s) : Maybe<&2, List<&2, U32>>}
  {==}

def equal_refl(+xs: List<&2, U32>) -> {Eq.equal(xs, xs) == True{} : Bool}:
  Equal.trans(Bool, Eq.equal(xs, xs), Subtle.eq(xs, xs), True{}, Equal.sym(Bool, Subtle.eq(xs, xs), Eq.equal(xs, xs), EqLaws.Eq.value(xs, xs)), EqLaws.Eq.refl(xs))

def false_of(+b: Bool, f: {b == True{} : Bool} -> Empty) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}))
    case False{}:
      {==}

def equal_false(+a: List<&2, U32>, +b: List<&2, U32>, ne: {a != b : List<&2, U32>}) -> {Eq.equal(a, b) == False{} : Bool}:
  false_of(Eq.equal(a, b), e => ne(EqLaws.Eq.sound(a, b, Equal.trans(Bool, Subtle.eq(a, b), Eq.equal(a, b), True{}, EqLaws.Eq.value(a, b), e))))
''' % (KT, TP, IN, T16,
       N_, ', '.join(ts), IN, N_, T16,
       N_, ', '.join(ts), IN, IN, T16,
       IN, ', '.join(ts), IN, T16,
       IN, T16, ', '.join(ts), T16))
C='G.gctr(nk, nr, key, pt, G.inc32(G.j0(iv)))'
tt2=['tb(nk, nr, key, iv, aad, %s, %dn)' % (C, i) for i in range(16)]
TT2=L(tt2)
out.append('''# Opening what seal produced gives the plaintext back.
def roundtrip(%s, +iv: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {G.open(nk, nr, key, iv, aad, G.seal(nk, nr, key, iv, aad, pt)) == Some{pt} : Maybe<&2, List<&2, U32>>}:
  %%Equal.sym(List<&2, U32>, G.tag(nk, nr, key, iv, aad, %s), %s, tag16(nk, nr, key, iv, aad, %s)) : {G.open(nk, nr, key, iv, aad, List.append(&2, U32, %s, _)) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Maybe<&2, List<&2, U32>>, G.open(nk, nr, key, iv, aad, List.append(&2, U32, %s, %s)), G.open_checked(nk, nr, key, iv, aad, %s, %s), open_append(nk, nr, key, iv, aad, %s, %s)) : {_ == Some{pt} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(List<&2, U32>, G.tag(nk, nr, key, iv, aad, %s), %s, tag16(nk, nr, key, iv, aad, %s)) : {G.accept(Eq.equal(%s, _), G.gctr(nk, nr, key, %s, G.inc32(G.j0(iv)))) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Bool, Eq.equal(%s, %s), True{}, equal_refl(%s)) : {G.accept(_, G.gctr(nk, nr, key, %s, G.inc32(G.j0(iv)))) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %%gctr_inv(nk, nr, key, pt, G.inc32(G.j0(iv))) : {Some{G.gctr(nk, nr, key, %s, G.inc32(G.j0(iv)))} == Some{_} : Maybe<&2, List<&2, U32>>}
  {==}

# Opening C || T with T other than the tag of C gives None.
def forgery(%s, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>, %s, ne: {%s != G.tag(nk, nr, key, iv, aad, c) : List<&2, U32>}) -> {G.open(nk, nr, key, iv, aad, List.append(&2, U32, c, %s)) == None{} : Maybe<&2, List<&2, U32>>}:
  %%Equal.sym(Maybe<&2, List<&2, U32>>, G.open(nk, nr, key, iv, aad, List.append(&2, U32, c, %s)), G.open_checked(nk, nr, key, iv, aad, c, %s), open_append(nk, nr, key, iv, aad, c, %s)) : {_ == None{} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Bool, Eq.equal(%s, G.tag(nk, nr, key, iv, aad, c)), False{}, equal_false(%s, G.tag(nk, nr, key, iv, aad, c), ne)) : {G.accept(_, G.gctr(nk, nr, key, c, G.inc32(G.j0(iv)))) == None{} : Maybe<&2, List<&2, U32>>}
  {==}
''' % (KT, C, TT2, C, C,
       C, TT2, C, TT2, C, ', '.join(tt2),
       C, TT2, C, TT2, C,
       TT2, TT2, TT2, C,
       C,
       KT, TP, T16, T16,
       T16, T16, ', '.join(ts),
       T16, T16))
open('proofs/crypto/aes/aead.bend','w').write('\n'.join(out))

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/aead.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/aead.py.')
_out.write_text('\n'.join(_lines))
