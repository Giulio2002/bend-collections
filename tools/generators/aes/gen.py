#!/usr/bin/env python3
"""Regenerate the generated AES / AES-GCM proof files in proofs/crypto/aes/.

  python3 tools/generators/aes/gen.py

  sbox.py        sbox.bend       the byte functions on all 256 inputs
  ghash_bits.py  ghash_bits.bend the bit-level GHASH word lemmas
  ghash.py       ghash.bend      the word-level GHASH == SP 800-38D GHASH
  gcm.py         gcm.bend        GCTR, the tag, GCM-AE / GCM-AD
  aead.py        aead.bend       open(seal(x)) == Some(x), forgeries rejected
  laws.py        laws.bend       the public clauses
  proof.py       proof.bend      the gate proving every clause

cipher.bend and gf.bend are written by hand.
"""
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
for name in ['sbox', 'ghash_bits', 'ghash', 'gcm', 'aead', 'laws', 'proof']:
    runpy.run_path(str(HERE / (name + '.py')), run_name='__main__')
