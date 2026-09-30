#!/usr/bin/env python3
"""Regenerate the generated AES / AES-GCM sources and proofs.

  python3 tools/generators/aes/gen.py

  bitslice.py    src/crypto/aes/bitslice.bend  bitsliced AES (two blocks, eight U32 planes)
  fast.py        src/crypto/aes/fast.bend      the fast GCM path (bitsliced AES, unrolled GHASH, one pass)
  sbox.py        proofs/crypto/aes/sbox.bend       the byte functions on all 256 inputs
  ghash_bits.py  proofs/crypto/aes/ghash_bits.bend the bit-level GHASH word lemmas
  ghash.py       proofs/crypto/aes/ghash.bend      the word-level GHASH == SP 800-38D GHASH
  gcm.py         proofs/crypto/aes/gcm.bend        GCTR, the tag, GCM-AE / GCM-AD
  aead.py        proofs/crypto/aes/aead.bend       open(seal(x)) == Some(x), forgeries rejected
  bsproof.py     proofs/crypto/aes/bs/{defs,words,bytes,mix,layers}.bend  bitsliced AES == aes.bend
  fastproof.py   proofs/crypto/aes/fast/ghash.bend  the fast GHASH == gcm.bend's
  fastgcm.py     proofs/crypto/aes/fast/gcm.bend    the fast GCM == gcm.bend's
  laws.py        proofs/crypto/aes/laws.bend       the public clauses
  proof.py       proofs/crypto/aes/proof.bend      the gate proving every clause

cipher.bend, gf.bend, api.bend, bs/cipher.bend and fast/api.bend are written by hand.
"""
import runpy, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
for name in ['bitslice', 'fast', 'sbox', 'ghash_bits', 'ghash', 'gcm', 'aead', 'bsproof', 'fastproof', 'fastgcm', 'laws', 'proof']:
    runpy.run_path(str(HERE / (name + '.py')), run_name='__main__')
