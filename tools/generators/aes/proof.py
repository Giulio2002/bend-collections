#!/usr/bin/env python3
"""Generate proofs/crypto/aes/proof.bend (run from anywhere; see gen.py)."""
import os
from pathlib import Path
os.chdir(Path(__file__).resolve().parents[3])

ns = ['n%d' % i for i in range(13)]
bs = ['b%d' % i for i in range(16)]
ts = ['t%d' % i for i in range(16)]
L = lambda v: '[%s]' % ', '.join(v)
NL = L(ns[:12])
NA = ', '.join(ns[:12])
NW = 'T.W{n0, n1, n2, n3}, T.W{n4, n5, n6, n7}, T.W{n8, n9, n10, n11}'
ST = 'T.S{T.W{b0, b1, b2, b3}, T.W{b4, b5, b6, b7}, T.W{b8, b9, b10, b11}, T.W{b12, b13, b14, b15}}'
NK = 'Nat.div(List.length(&2, U32, key), 4n)'
SCH = 'A.Schedule{S.nr(key), A.expand(S.nk(key), S.nr(key), key)}'
M = 'Maybe<&2, List<&2, U32>>'


def fill(t, **kw):
    for k, v in kw.items():
        t = t.replace('@%s@' % k, v)
    return t


def nonce_cases(kind, last):
    out = []
    for k in range(12):
        pat = 'Nil{}' if k == 0 else ' <> '.join(ns[:k]) + ' <> Nil{}'
        out.append('    case %s:\n      {==}' % pat)
    goal = '{GI.%s(sched, %s, aad, %s) == None{} : %s}' % (kind, NL, last, M)
    out.append('    case %s <> Nil{}:\n      Empty.absurd(%s, L.true_false(h))' % (' <> '.join(ns[:12]), goal))
    out.append('    case %s <> rest:\n      {==}' % ' <> '.join(ns[:13]))
    return '\n'.join(out)


out = fill('''import Base
import ../../lib/logic.bend as L
import ../../../src/crypto/aes/types.bend as T
import ../../../src/crypto/aes/aes.bend as A
import ../../../src/crypto/aes/gcm.bend as GI
import ../../../src/crypto/aesgcm.bend as GCM
import ../../../spec/crypto/aes/aes.bend as S
import ../../../spec/crypto/aes/gcm.bend as G
import ./laws.bend as Laws
import ./sbox.bend as SB
import ./inverse.bend as INV
import ./cipher.bend as C
import ./gcm.bend as GP
import ./aead.bend as AD
import ./api.bend as API

# Gate for AES and AES-GCM: `bend proofs/crypto/aes/proof.bend` checks every
# clause of laws.bend, for every input:
#   sbox.bend    the S-box circuit and the doublings, on all 256 bytes
#   cipher.bend  SubBytes .. AddRoundKey, the rounds, KeyExpansion, Cipher
#   gf.bend      polynomial product mod m == Algorithm 1 (any modulus)
#   ghash*.bend  the word-level GHASH == SP 800-38D's GHASH
#   gcm.bend     GCTR, the tag, GCM-AE and GCM-AD == SP 800-38D
#   aead.bend    open(seal(x)) == Some(x); a wrong tag gives None
# The key size stays symbolic (Nk = length/4) so that no key expansion is
# ever unfolded at a concrete size.

# A nonce that is not 12 bytes long: None.
def seal_nonce_bad(+sched: A.Schedule, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GI.seal_nonce(sched, nonce, aad, pt) == None{} : @M@}:
  match nonce:
@SEAL@

def open_nonce_bad(+sched: A.Schedule, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GI.open_nonce(sched, nonce, aad, ct) == None{} : @M@}:
  match nonce:
@OPEN@

def seal_key_bad(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +pt: List<&2, U32>) -> {GI.seal_key(m, nonce, aad, pt) == None{} : @M@}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      seal_nonce_bad(s, nonce, h, aad, pt)

def open_key_bad(+m: Maybe<&2, A.Schedule>, +nonce: List<&2, U32>, +h: {Nat.is_eq(List.length(&2, U32, nonce), 12n) == False{} : Bool}, +aad: List<&2, U32>, +ct: List<&2, U32>) -> {GI.open_key(m, nonce, aad, ct) == None{} : @M@}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      open_nonce_bad(s, nonce, h, aad, ct)

# A key of w bytes, w one of 16, 24, 32, passes the length check.
def valid_of(+key: List<&2, U32>, +w: Nat, +h: {List.length(&2, U32, key) == w : Nat}, +v: {A.valid_length(w) == True{} : Bool}) -> {A.valid_length(List.length(&2, U32, key)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, key), w, h) : {A.valid_length(_) == True{} : Bool}
  v

def Laws.Sbox.value(x):
  SB.sbox_ok(x)

def Laws.Inverse.unit(x, h):
  INV.inverse_unit(x, h)

def Laws.Inverse.zero():
  INV.inverse_zero()

def Laws.Cipher.value(nk, nr, key, s):
  C.encrypt_ok(nk, nr, key, s)

def Laws.Block.value(key, h, @BA@):
  %Equal.sym(Bool, A.valid_length(List.length(&2, U32, key)), True{}, h) : {Laws.block_with(A.schedule_if(_, @NK@, key), @BL@) == Some{S.bytes_of(S.aes(key, S.state_of(@BL@)))} : @M@}
  %C.encrypt_ok(S.nk(key), S.nr(key), key, @ST@) : {Laws.block_with(A.schedule_if(True{}, @NK@, key), @BL@) == Some{S.bytes_of(_)} : @M@}
  %GP.bytes_of_ok(A.encrypt(S.nk(key), S.nr(key), key, @ST@)) : {Laws.block_with(A.schedule_if(True{}, @NK@, key), @BL@) == Some{_} : @M@}
  {==}

def Laws.Block.aes128(key, h):
  %Equal.sym(Nat, List.length(&2, U32, key), 16n, h) : {Nat.div(_, 4n) == 4n : Nat}
  {==}

def Laws.Block.aes192(key, h):
  %Equal.sym(Nat, List.length(&2, U32, key), 24n, h) : {Nat.div(_, 4n) == 6n : Nat}
  {==}

def Laws.Block.aes256(key, h):
  %Equal.sym(Nat, List.length(&2, U32, key), 32n, h) : {Nat.div(_, 4n) == 8n : Nat}
  {==}

def Laws.Gcm.seal(nk, nr, key, @NA@, aad, pt):
  GP.seal_ok(nk, nr, key, @NW@, aad, pt)

def Laws.Gcm.open(nk, nr, key, @NA@, aad, input):
  GP.open_ok(nk, nr, key, @NW@, aad, input)

def Laws.Aead.roundtrip(nk, nr, key, iv, aad, pt):
  AD.roundtrip(nk, nr, key, iv, aad, pt)

def Laws.Aead.forgery(nk, nr, key, iv, aad, c, @TA@, ne):
  AD.forgery(nk, nr, key, iv, aad, c, @TA@, ne)

''', M=M, SEAL=nonce_cases('seal_nonce', 'pt'), OPEN=nonce_cases('open_nonce', 'ct'),
     BA=', '.join(bs), BL=L(bs), ST=ST, NK=NK, NA=NA, NW=NW, TA=', '.join(ts))

for (w, name) in [(16, '128'), (32, '256')]:
    out += fill('''def Laws.Api@N@.encrypt(key, h, @NA@, aad, pt):
  API.aes@N@_encrypt(key, h, @NA@, aad, pt)

def Laws.Api@N@.decrypt(key, h, @NA@, aad, ct):
  API.aes@N@_decrypt(key, h, @NA@, aad, ct)

law open@N@_same:
  for +key: List<&2, U32>
  for +nonce: List<&2, U32>
  for +aad: List<&2, U32>
  for +m: Maybe<&2, List<&2, U32>>
  {Laws.open@N@(key, nonce, aad, m) == API.open@N@(key, nonce, aad, m) : @M@}

def open@N@_same(key, nonce, aad, m):
  match m:
    case None{}: {==}
    case Some{c}: {==}

def Laws.Api@N@.roundtrip(key, h, @NA@, aad, pt):
  +m = GCM.aes@N@_gcm_encrypt(key, @NL@, aad, pt)
  Equal.trans(@M@, Laws.open@N@(key, @NL@, aad, m), API.open@N@(key, @NL@, aad, m), Some{pt}, open@N@_same(key, @NL@, aad, m), API.aes@N@_roundtrip(key, h, @NA@, aad, pt))

def Laws.Api@N@.forgery(key, h, @NA@, aad, c, @TA@, ne):
  API.aes@N@_forgery(key, h, @NA@, aad, c, @TA@, ne)

def Laws.Api@N@.bad_key(key, h, nonce, aad, pt):
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, key), @W@n), False{}, h) : {GI.seal_key(GI.schedule_if(_, key), nonce, aad, pt) == None{} : @M@}
  {==}

def Laws.Api@N@.bad_key_open(key, h, nonce, aad, ct):
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, U32, key), @W@n), False{}, h) : {GI.open_key(GI.schedule_if(_, key), nonce, aad, ct) == None{} : @M@}
  {==}

def Laws.Api@N@.bad_nonce(key, nonce, h, aad, pt):
  seal_key_bad(GI.schedule_of(@W@n, key), nonce, h, aad, pt)

def Laws.Api@N@.bad_nonce_open(key, nonce, h, aad, ct):
  open_key_bad(GI.schedule_of(@W@n, key), nonce, h, aad, ct)

''', N=name, W=str(w), NA=NA, NL=NL, NW=NW, NK=NK, SCH=SCH, M=M, TA=', '.join(ts), TL=L(ts))

Path('proofs/crypto/aes/proof.bend').write_text(out)

# Mark the output as generated, after its imports.
_out = Path('proofs/crypto/aes/proof.bend')
_lines = _out.read_text().split('\n')
_last = max(i for i, l in enumerate(_lines) if l.startswith('import '))
_lines.insert(_last + 1, '\n# Generated by tools/generators/aes/proof.py.')
_out.write_text('\n'.join(_lines))
