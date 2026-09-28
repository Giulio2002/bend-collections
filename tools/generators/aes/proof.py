#!/usr/bin/env python3
"""Generate proofs/crypto/aes/proof.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

ns=['n%d'%i for i in range(12)]
bs=['b%d'%i for i in range(16)]
ts=['t%d'%i for i in range(16)]
L=lambda v: '[%s]' % ', '.join(v)
NL=L(ns)
NW='T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}'
ST='T.S{T.W{b0, b1, b2, b3}, T.W{b4, b5, b6, b7}, T.W{b8, b9, b10, b11}, T.W{b12, b13, b14, b15}}'
out = '''import Base
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as GI
import ../../../src/crypto/aesgcm.bend as GCM
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ./laws.bend as Laws
import ./sbox.bend as SB
import ./cipher.bend as C
import ./gcm.bend as GP
import ./aead.bend as AD
import ../../lib/logic.bend as L

# Gate for AES and AES-GCM: `bend proofs/crypto/aes/proof.bend` checks every
# clause of laws.bend, for every input:
#   sbox.bend    the S-box circuit and the doublings, on all 256 bytes
#   cipher.bend  SubBytes .. AddRoundKey, the rounds, KeyExpansion, Cipher
#   gf.bend      polynomial product mod m == Algorithm 1 (any modulus)
#   ghash*.bend  the word-level GHASH == SP 800-38D's GHASH
#   gcm.bend     GCTR, the tag, GCM-AE and GCM-AD == SP 800-38D
#   aead.bend    open(seal(x)) == Some(x); a wrong tag gives None

# A nonce that is not 12 bytes long: None.
def seal_nonce_bad(+sched: A.Schedule, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GI.seal_nonce(sched, nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}:
  match nonce:
    case Nil{}:
      {==}
    case n0 <> Nil{}:
      {==}
    case n0 <> n1 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      Empty.absurd({GI.seal_nonce(sched, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, pt) == None{} : Maybe<&2, List<&2, U32>>}, L.true_false(h))
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> n12 <> rest:
      {==}

def open_nonce_bad(+sched: A.Schedule, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GI.open_nonce(sched, nonce, aad, ct) == None{} : Maybe<&2, List<&2, U32>>}:
  match nonce:
    case Nil{}:
      {==}
    case n0 <> Nil{}:
      {==}
    case n0 <> n1 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> Nil{}:
      {==}
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> Nil{}:
      Empty.absurd({GI.open_nonce(sched, [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11], aad, ct) == None{} : Maybe<&2, List<&2, U32>>}, L.true_false(h))
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> n8 <> n9 <> n10 <> n11 <> n12 <> rest:
      {==}

def seal_key_bad(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GI.seal_key(m, nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      seal_nonce_bad(s, nonce, h, aad, pt)

def open_key_bad(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GI.open_key(m, nonce, aad, ct) == None{} : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      open_nonce_bad(s, nonce, h, aad, ct)

def Laws.Sbox.value(x):
  SB.sbox_ok(x)

def Laws.Cipher.value(nk, nr, key, s):
  C.encrypt_ok(nk, nr, key, s)

'''
for (w, nk, nr, name) in [(16, 4, 10, '128'), (32, 8, 14, '256')]:
    out += '''def Laws.Block.aes%s(key, h, %s):
  %%Equal.sym(Nat, List.length(&2, U32, key), %dn, h) : {Laws.block_with(A.schedule_for(_, key), %s) == Some{S.bytes_of(S.aes%s(key, S.state_of(%s)))} : Maybe<&2, List<&2, U32>>}
  %%C.encrypt_ok(%dn, %dn, key, %s) : {Laws.block_with(A.schedule_for(%dn, key), %s) == Some{S.bytes_of(_)} : Maybe<&2, List<&2, U32>>}
  %%GP.bytes_of_ok(A.encrypt(%dn, %dn, key, %s)) : {Laws.block_with(A.schedule_for(%dn, key), %s) == Some{_} : Maybe<&2, List<&2, U32>>}
  {==}

''' % (name, ', '.join(bs), w, L(bs), name, L(bs), nk, nr, ST, w, L(bs), nk, nr, ST, w, L(bs))
out += '''def Laws.Gcm.seal(nk, nr, key, %s, aad, pt):
  GP.seal_ok(nk, nr, key, %s, aad, pt)

def Laws.Gcm.open(nk, nr, key, %s, aad, input):
  GP.open_ok(nk, nr, key, %s, aad, input)

def Laws.Aead.roundtrip(nk, nr, key, iv, aad, pt):
  AD.roundtrip(nk, nr, key, iv, aad, pt)

def Laws.Aead.forgery(nk, nr, key, iv, aad, c, %s, ne):
  AD.forgery(nk, nr, key, iv, aad, c, %s, ne)

''' % (', '.join(ns), NW, ', '.join(ns), NW, ', '.join(ts), ', '.join(ts))
for (w, nk, nr, name) in [(16, 4, 10, '128'), (32, 8, 14, '256')]:
    SCH = 'A.Schedule{%dn, A.expand(%dn, %dn, key)}' % (nr, nk, nr)
    out += '''def Laws.Api%s.encrypt(key, h, %s, aad, pt):
  %%Equal.sym(Nat, List.length(&2, U32, key), %dn, h) : {GI.seal_key(GI.schedule_if(Nat.is_eq(_, %dn), key), %s, aad, pt) == Some{G.seal(%dn, %dn, key, %s, aad, pt)} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Nat, List.length(&2, U32, key), %dn, h) : {GI.seal_key(A.schedule_for(_, key), %s, aad, pt) == Some{G.seal(%dn, %dn, key, %s, aad, pt)} : Maybe<&2, List<&2, U32>>}
  %%GP.seal_ok(%dn, %dn, key, %s, aad, pt) : {Some{GI.seal_core(%s, %s, aad, pt)} == Some{_} : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.Api%s.decrypt(key, h, %s, aad, ct):
  %%Equal.sym(Nat, List.length(&2, U32, key), %dn, h) : {GI.open_key(GI.schedule_if(Nat.is_eq(_, %dn), key), %s, aad, ct) == G.open(%dn, %dn, key, %s, aad, ct) : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Nat, List.length(&2, U32, key), %dn, h) : {GI.open_key(A.schedule_for(_, key), %s, aad, ct) == G.open(%dn, %dn, key, %s, aad, ct) : Maybe<&2, List<&2, U32>>}
  GP.open_ok(%dn, %dn, key, %s, aad, ct)

def Laws.Api%s.roundtrip(key, h, %s, aad, pt):
  %%Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes%s_gcm_encrypt(key, %s, aad, pt), Some{G.seal(%dn, %dn, key, %s, aad, pt)}, Laws.Api%s.encrypt(key, h, %s, aad, pt)) : {Laws.open%s(key, %s, aad, _) == Some{pt} : Maybe<&2, List<&2, U32>>}
  %%Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes%s_gcm_decrypt(key, %s, aad, G.seal(%dn, %dn, key, %s, aad, pt)), G.open(%dn, %dn, key, %s, aad, G.seal(%dn, %dn, key, %s, aad, pt)), Laws.Api%s.decrypt(key, h, %s, aad, G.seal(%dn, %dn, key, %s, aad, pt))) : {_ == Some{pt} : Maybe<&2, List<&2, U32>>}
  AD.roundtrip(%dn, %dn, key, %s, aad, pt)

def Laws.Api%s.forgery(key, h, %s, aad, c, %s, ne):
  %%Equal.sym(Maybe<&2, List<&2, U32>>, GCM.aes%s_gcm_decrypt(key, %s, aad, List.append(&2, U32, c, %s)), G.open(%dn, %dn, key, %s, aad, List.append(&2, U32, c, %s)), Laws.Api%s.decrypt(key, h, %s, aad, List.append(&2, U32, c, %s))) : {_ == None{} : Maybe<&2, List<&2, U32>>}
  AD.forgery(%dn, %dn, key, %s, aad, c, %s, ne)

def Laws.Api%s.bad_key(key, h, nonce, aad, pt):
  %%Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, key), %dn), False{}, h) : {GI.seal_key(GI.schedule_if(_, key), nonce, aad, pt) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.Api%s.bad_key_open(key, h, nonce, aad, ct):
  %%Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, key), %dn), False{}, h) : {GI.open_key(GI.schedule_if(_, key), nonce, aad, ct) == None{} : Maybe<&2, List<&2, U32>>}
  {==}

def Laws.Api%s.bad_nonce(key, nonce, h, aad, pt):
  seal_key_bad(GI.schedule_of(%dn, key), nonce, h, aad, pt)

def Laws.Api%s.bad_nonce_open(key, nonce, h, aad, ct):
  open_key_bad(GI.schedule_of(%dn, key), nonce, h, aad, ct)

''' % (name, ', '.join(ns), w, w, NL, nk, nr, NL, w, NL, nk, nr, NL, nk, nr, NW, SCH, NW,
       name, ', '.join(ns), w, w, NL, nk, nr, NL, w, NL, nk, nr, NL, nk, nr, NW,
       name, ', '.join(ns), name, NL, nk, nr, NL, name, ', '.join(ns), name, NL,
       name, NL, nk, nr, NL, nk, nr, NL, nk, nr, NL, name, ', '.join(ns), nk, nr, NL,
       nk, nr, NL,
       name, ', '.join(ns), ', '.join(ts), name, NL, L(ts), nk, nr, NL, L(ts), name, ', '.join(ns), L(ts), nk, nr, NL, ', '.join(ts),
       name, w, name, w, name, w, name, w)
open('proofs/crypto/aes/proof.bend','w').write(out)

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/proof.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/proof.py.')
_out.write_text('\n'.join(_lines))
