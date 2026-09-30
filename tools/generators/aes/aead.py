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

ks_names = ['k%d' % i for i in range(16)]
out.append("""# Byte i of the keystream block of counter block cb.
def kb(+nk: Nat, +nr: Nat, +key: List<&2, U32>, +cb: List<&2, U32>, +i: Nat) -> U32:
  S.nth_byte(G.ciph(nk, nr, key, cb), i)
""")
def cancel_lemma(n, tail):
    xv, kv = xs[:n], ks_names[:n]
    items = ['U32.xor(U32.xor(%s, %s), %s)' % (xv[i], kv[i], kv[i]) for i in range(n)]
    params = ', '.join('+%s: U32' % v for v in xv + kv)
    if tail:
        lhs, rhs = cons(items, 'r1'), cons(xv, 'r2')
        head = 'def cancel%d(%s, +r1: List<&2, U32>, +r2: List<&2, U32>, +e: {r1 == r2 : List<&2, U32>}) -> {%s == %s : List<&2, U32>}:' % (n, params, lhs, rhs)
        lines = [head, '  %%e : {%s == %s : List<&2, U32>}' % (lhs, cons(xv, '_'))]
        for i in range(n):
            lines.append('  %%xor_inv(%s, %s) : {%s == %s : List<&2, U32>}' % (xv[i], kv[i], lhs, cons(items[:i] + ['_'] + xv[i + 1:], 'r1')))
    else:
        lhs, rhs = L(items), L(xv)
        head = 'def cancel%d(%s) -> {%s == %s : List<&2, U32>}:' % (n, params, lhs, rhs)
        lines = [head]
        for i in range(n):
            lines.append('  %%xor_inv(%s, %s) : {%s == %s : List<&2, U32>}' % (xv[i], kv[i], lhs, L(items[:i] + ['_'] + xv[i + 1:])))
    lines.append('  {==}')
    return '\n'.join(lines) + '\n'
out.append('# (x xor k) xor k == x, position by position.')
out.append(cancel_lemma(16, True))
for n in range(1, 16):
    out.append(cancel_lemma(n, False))
# gctr_block
rhs = cons(['U32.xor(%s, %s)' % (xs[i], ks('cb', i)) for i in range(16)], 'G.gctr(nk, nr, key, rest, G.inc32(cb))')
out.append('''# One whole block of counter mode.
def gctr_block(%s, %s, +rest: List<&2, U32>, +cb: List<&2, U32>) -> {G.gctr(nk, nr, key, %s, cb) == %s : List<&2, U32>}:
  %%Equal.sym(List<&2, U32>, S.bytes_of(%s), %s, ks_ok(%s)) : {List.append(&2, U32, G.xor_bytes(%s, _), G.gctr(nk, nr, key, rest, G.inc32(cb))) == %s : List<&2, U32>}
  {==}
''' % (KT, ', '.join('+%s: U32' % x for x in xs), cons(xs, 'rest'), rhs, ST, EXPL, ST, L(xs), rhs))
# gctr_part_k
for k in range(1, 16):
    v = xs[:k]
    rhs = L(['U32.xor(%s, %s)' % (v[i], ks('cb', i)) for i in range(k)])
    out.append('''def gctr_part%d(%s, %s, +cb: List<&2, U32>) -> {G.gctr(nk, nr, key, %s, cb) == %s : List<&2, U32>}:
  %%Equal.sym(List<&2, U32>, S.bytes_of(%s), %s, ks_ok(%s)) : {G.xor_bytes(%s, _) == %s : List<&2, U32>}
  {==}
''' % (k, KT, ', '.join('+%s: U32' % x for x in v), L(v), rhs, ST, EXPL, ST, L(v), rhs))
# gctr_inv
cases = []
full = cons(xs, 'rest')
E1 = cons(['U32.xor(%s, %s)' % (xs[i], ks('cb', i)) for i in range(16)], 'G.gctr(nk, nr, key, rest, G.inc32(cb))')
E1args = ', '.join(['U32.xor(%s, %s)' % (xs[i], ks('cb', i)) for i in range(16)])
E2items = ['U32.xor(U32.xor(%s, %s), %s)' % (xs[i], ks('cb', i), ks('cb', i)) for i in range(16)]
E2 = cons(E2items, 'G.gctr(nk, nr, key, G.gctr(nk, nr, key, rest, G.inc32(cb)), G.inc32(cb))')
lines = ['    case %s:' % full,
         '      %%Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, %s, cb), %s, gctr_block(nk, nr, key, %s, rest, cb)) : {G.gctr(nk, nr, key, _, cb) == %s : List<&2, U32>}' % (full, E1, ', '.join(xs), full),
         '      %%Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, %s, cb), %s, gctr_block(nk, nr, key, %s, G.gctr(nk, nr, key, rest, G.inc32(cb)), cb)) : {_ == %s : List<&2, U32>}' % (E1, E2, E1args, full)]
lines.append('      cancel16(%s, %s, G.gctr(nk, nr, key, G.gctr(nk, nr, key, rest, G.inc32(cb)), G.inc32(cb)), rest, gctr_inv(nk, nr, key, rest, G.inc32(cb)))' % (', '.join(xs), ', '.join(ks('cb', i) for i in range(16))))
cases.append('\n'.join(lines))
cases.append('    case Nil{}:\n      {==}')
for k in range(1, 16):
    v = xs[:k]
    e1 = L(['U32.xor(%s, %s)' % (v[i], ks('cb', i)) for i in range(k)])
    e2items = ['U32.xor(U32.xor(%s, %s), %s)' % (v[i], ks('cb', i), ks('cb', i)) for i in range(k)]
    lines = ['    case %s:' % cons(v, 'Nil{}'),
             '      %%Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, %s, cb), %s, gctr_part%d(nk, nr, key, %s, cb)) : {G.gctr(nk, nr, key, _, cb) == %s : List<&2, U32>}' % (L(v), e1, k, ', '.join(v), L(v)),
             '      %%Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, %s, cb), %s, gctr_part%d(nk, nr, key, %s, cb)) : {_ == %s : List<&2, U32>}' % (e1, L(e2items), k, ', '.join('U32.xor(%s, %s)' % (v[i], ks('cb', i)) for i in range(k)), L(v))]
    lines.append('      cancel%d(%s, %s)' % (k, ', '.join(v), ', '.join(ks('cb', i) for i in range(k))))
    cases.append('\n'.join(lines))
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
out.append('''# The tag is a 16-byte list.
def tag16(%s, +iv: List<&2, U32>, +aad: List<&2, U32>, +c: List<&2, U32>) -> {G.tag(nk, nr, key, iv, aad, c) == %s : List<&2, U32>}:
  %%Equal.sym(List<&2, U32>, %s, %s, bb16(%s)) : {G.gctr(nk, nr, key, _, G.j0(iv)) == %s : List<&2, U32>}
  %%Equal.sym(List<&2, U32>, G.gctr(nk, nr, key, %s, G.j0(iv)), %s, gctr_block(nk, nr, key, %s, Nil{}, G.j0(iv))) : {_ == %s : List<&2, U32>}
  {==}
''' % (KT, TT, BB, L(bb), W, TT, cons(bb, 'Nil{}'),
       cons(['U32.xor(%s, %s)' % (bb[i], ks('G.j0(iv)', i)) for i in range(16)], 'G.gctr(nk, nr, key, Nil{}, G.inc32(G.j0(iv)))'),
       ', '.join(bb), TT))
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
