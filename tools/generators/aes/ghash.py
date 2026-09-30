#!/usr/bin/env python3
"""Generate proofs/crypto/aes/ghash.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

xs=['x%d'%i for i in range(16)]
L=lambda v: '[%s]' % ', '.join(v)
head = '''import Base
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as I
import ../../../spec/crypto/aes/poly.bend as P
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ./gf.bend as GF
import ./ghash_defs.bend as D
import ./ghash_bits.bend as B

# The implementation's GHASH (Algorithm 1 on four U32 words, bit by bit)
# equals SP 800-38D's GHASH over the field GF(2^128), block by block.

# One bit of Algorithm 1: Z += c*V, V = V*x.
def step_ok(+c: Bool, +z: I.Block, +v: I.Block, +rest: List<&2, Bool>) -> {D.F(I.Acc{z, v}, c <> rest) == D.F(I.step(D.bit(c), I.Acc{z, v}), rest) : Word(128n)}:
  %B.zstep_ok(c, z, v) : {GF.sa(128n, G.low(), rest, _, P.times_x(128n, G.low(), D.R(v))) == D.F(I.step(D.bit(c), I.Acc{z, v}), rest) : Word(128n)}
  %B.mulx_ok(v) : {GF.sa(128n, G.low(), rest, D.R(I.add_masked(D.bit(c), z, v)), _) == D.F(I.step(D.bit(c), I.Acc{z, v}), rest) : Word(128n)}
  {==}

def steps_ok(+cs: List<&2, Bool>, +acc: I.Acc, +rest: List<&2, Bool>) -> {D.F(acc, List.append(&2, Bool, cs, rest)) == D.F(D.steps(cs, acc), rest) : Word(128n)}:
  match cs:
    case Nil{}:
      {==}
    case c <> r:
      match acc:
        case I.Acc{z, v}:
          Equal.trans(Word(128n), D.F(I.Acc{z, v}, c <> List.append(&2, Bool, r, rest)), D.F(I.step(D.bit(c), I.Acc{z, v}), List.append(&2, Bool, r, rest)), D.F(D.steps(r, I.step(D.bit(c), I.Acc{z, v})), rest),
            step_ok(c, z, v, List.append(&2, Bool, r, rest)), steps_ok(r, I.step(D.bit(c), I.Acc{z, v}), rest))

def steps_append(+l1: List<&2, Bool>, +l2: List<&2, Bool>, +acc: I.Acc) -> {D.steps(List.append(&2, Bool, l1, l2), acc) == D.steps(l2, D.steps(l1, acc)) : I.Acc}:
  match l1:
    case Nil{}:
      {==}
    case c <> r:
      steps_append(r, l2, I.step(D.bit(c), acc))

def mul_bytes_steps(+xs: List<&2, U32>, +acc: I.Acc) -> {I.mul_bytes(xs, acc) == D.steps(G.string_bits(xs), acc) : I.Acc}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %Equal.sym(I.Acc, D.steps(List.append(&2, Bool, G.byte_bits(x), G.string_bits(rest)), acc), D.steps(G.string_bits(rest), D.steps(G.byte_bits(x), acc)), steps_append(G.byte_bits(x), G.string_bits(rest), acc)) : {I.mul_bytes(rest, I.mul_byte(x, acc)) == _ : I.Acc}
      %B.mul_byte_steps(x, acc) : {I.mul_bytes(rest, I.mul_byte(x, acc)) == D.steps(G.string_bits(rest), _) : I.Acc}
      mul_bytes_steps(rest, I.mul_byte(x, acc))

def append_nil(+l: List<&2, Bool>) -> {List.append(&2, Bool, l, Nil{}) == l : List<&2, Bool>}:
  match l:
    case Nil{}:
      {==}
    case c <> r:
      %append_nil(r) : {c <> List.append(&2, Bool, r, Nil{}) == c <> _ : List<&2, Bool>}
      {==}

def f_nil(+acc: I.Acc) -> {D.F(acc, Nil{}) == D.R(I.acc_z(acc)) : Word(128n)}:
  match acc:
    case I.Acc{z, v}:
      {==}

'''
# absorb_ok
ys='I.B{y0, y1, y2, y3}'
X='I.xor_bytes(I.unpack(%s), %s)' % (ys, L(xs))
SB='G.string_bits(%s)' % X
A0='I.Acc{I.zero(), h}'
W='Word.xor(128n, D.R(%s), G.block(%s))' % (ys, L(xs))
LHS='D.R(I.acc_z(I.mul_bytes(%s, %s)))' % (X, A0)
params=', '.join('+%s: U32' % x for x in xs)
absorb = '''# (Y xor X) * H for one 16-byte block.
def absorb_ok(+h: I.Block, +y: I.Block, %s) -> {D.R(I.absorb(h, y, %s)) == G.mul(Word.xor(128n, D.R(y), G.block(%s)), D.R(h)) : Word(128n)}:
  match y:
    case I.B{y0, y1, y2, y3}:
      %%Equal.sym(Word(128n), G.mul(%s, D.R(h)), GF.sa(128n, G.low(), P.coefficients(128n, %s), Word.zero(128n), D.R(h)), GF.mul_sa(128n, G.low(), %s, D.R(h))) : {%s == _ : Word(128n)}
      %%Equal.sym(List<&2, Bool>, P.coefficients(128n, %s), %s, B.block_xor_ok(y0, y1, y2, y3, %s)) : {%s == GF.sa(128n, G.low(), _, Word.zero(128n), D.R(h)) : Word(128n)}
      %%Equal.cong(List<&2, Bool>, Word(128n), l => D.F(%s, l), List.append(&2, Bool, %s, Nil{}), %s, append_nil(%s)) : {%s == _ : Word(128n)}
      %%Equal.sym(Word(128n), D.F(%s, List.append(&2, Bool, %s, Nil{})), D.F(D.steps(%s, %s), Nil{}), steps_ok(%s, %s, Nil{})) : {%s == _ : Word(128n)}
      %%Equal.sym(Word(128n), D.F(D.steps(%s, %s), Nil{}), D.R(I.acc_z(D.steps(%s, %s))), f_nil(D.steps(%s, %s))) : {%s == _ : Word(128n)}
      %%mul_bytes_steps(%s, %s) : {%s == D.R(I.acc_z(_)) : Word(128n)}
      {==}

''' % (params, L(xs), L(xs),
       W, W, W, LHS,
       W, SB, ', '.join(xs), LHS,
       A0, SB, SB, SB, LHS,
       A0, SB, SB, A0, SB, A0, LHS,
       SB, A0, SB, A0, SB, A0, LHS,
       X, A0, LHS)
# ghash_ok
cases=[]
cases.append('''    case %s <> xr:
      %%absorb_ok(h, y, %s) : {G.ghash(D.R(h), List.append(&2, U32, G.pad(xr), rest), _) == G.ghash(D.R(h), rest, D.R(I.ghash(h, xr, I.absorb(h, y, %s)))) : Word(128n)}
      ghash_ok(h, xr, rest, I.absorb(h, y, %s))''' % (' <> '.join(xs), ', '.join(xs), L(xs), L(xs)))
cases.append('    case Nil{}:\n      {==}')
for k in range(1,16):
    full = xs[:k] + ['0']*(16-k)
    cases.append('''    case %s <> Nil{}:
      %%absorb_ok(h, y, %s) : {G.ghash(D.R(h), rest, _) == G.ghash(D.R(h), rest, D.R(I.absorb(h, y, %s))) : Word(128n)}
      {==}''' % (' <> '.join(xs[:k]), ', '.join(full), L(full)))
ghash = '''# GHASH over X || 0^v (then more blocks) is the implementation's GHASH over X.
def ghash_ok(+h: I.Block, +xs: List<&2, U32>, +rest: List<&2, U32>, +y: I.Block) -> {G.ghash(D.R(h), List.append(&2, U32, G.pad(xs), rest), D.R(y)) == G.ghash(D.R(h), rest, D.R(I.ghash(h, xs, y))) : Word(128n)}:
  match xs:
%s

''' % '\n'.join(cases)
tail = '''# GHASH_H(A || 0^v || C || 0^u || [len(A)]_64 || [len(C)]_64).
def ghash_all_ok(+h: I.Block, +aad: List<&2, U32>, +c: List<&2, U32>) -> {G.ghash(D.R(h), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), Word.zero(128n)) == D.R(I.ghash(h, I.lengths(aad, c), I.ghash(h, c, I.ghash(h, aad, I.zero())))) : Word(128n)}:
  Equal.trans(Word(128n),
    G.ghash(D.R(h), List.append(&2, U32, G.pad(aad), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c)))), D.R(I.zero())),
    G.ghash(D.R(h), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c))), D.R(I.ghash(h, aad, I.zero()))),
    D.R(I.ghash(h, I.lengths(aad, c), I.ghash(h, c, I.ghash(h, aad, I.zero())))),
    ghash_ok(h, aad, List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c))), I.zero()),
    Equal.trans(Word(128n),
      G.ghash(D.R(h), List.append(&2, U32, G.pad(c), List.append(&2, U32, G.len64(aad), G.len64(c))), D.R(I.ghash(h, aad, I.zero()))),
      G.ghash(D.R(h), List.append(&2, U32, G.len64(aad), G.len64(c)), D.R(I.ghash(h, c, I.ghash(h, aad, I.zero())))),
      D.R(I.ghash(h, I.lengths(aad, c), I.ghash(h, c, I.ghash(h, aad, I.zero())))),
      ghash_ok(h, c, List.append(&2, U32, G.len64(aad), G.len64(c)), I.ghash(h, aad, I.zero())),
      ghash_ok(h, I.lengths(aad, c), Nil{}, I.ghash(h, c, I.ghash(h, aad, I.zero())))))

# The hash subkey: the implementation packs E_K(0^128) into words.
def pack_ok(+st: T.State) -> {D.R(I.pack(st)) == G.block(S.bytes_of(st)) : Word(128n)}:
  match st:
    case T.S{T.W{a0, a1, a2, a3}, T.W{a4, a5, a6, a7}, T.W{a8, a9, a10, a11}, T.W{a12, a13, a14, a15}}:
      %Equal.sym(U32, I.word(T.W{a0, a1, a2, a3}), G.int32(a0, a1, a2, a3), B.word_ok(a0, a1, a2, a3)) : {D.R(I.B{_, I.word(T.W{a4, a5, a6, a7}), I.word(T.W{a8, a9, a10, a11}), I.word(T.W{a12, a13, a14, a15})}) == G.block([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : Word(128n)}
      %Equal.sym(U32, I.word(T.W{a4, a5, a6, a7}), G.int32(a4, a5, a6, a7), B.word_ok(a4, a5, a6, a7)) : {D.R(I.B{G.int32(a0, a1, a2, a3), _, I.word(T.W{a8, a9, a10, a11}), I.word(T.W{a12, a13, a14, a15})}) == G.block([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : Word(128n)}
      %Equal.sym(U32, I.word(T.W{a8, a9, a10, a11}), G.int32(a8, a9, a10, a11), B.word_ok(a8, a9, a10, a11)) : {D.R(I.B{G.int32(a0, a1, a2, a3), G.int32(a4, a5, a6, a7), _, I.word(T.W{a12, a13, a14, a15})}) == G.block([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : Word(128n)}
      %Equal.sym(U32, I.word(T.W{a12, a13, a14, a15}), G.int32(a12, a13, a14, a15), B.word_ok(a12, a13, a14, a15)) : {D.R(I.B{G.int32(a0, a1, a2, a3), G.int32(a4, a5, a6, a7), G.int32(a8, a9, a10, a11), _}) == G.block([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : Word(128n)}
      B.pack_int(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15)
'''
open('proofs/crypto/aes/ghash.bend','w').write(head+absorb+ghash+tail)

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/ghash.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/ghash.py.')
_out.write_text('\n'.join(_lines))
