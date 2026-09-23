#!/usr/bin/env python3
"""Differential fuzzing of the hash functions against independent references.

  python3 tests/crypto/fuzz.py                       every algorithm, 2000 cases each
  python3 tests/crypto/fuzz.py keccak256 -n 5000 --seed 7

For each algorithm a small Bend driver (written to build/fuzz/) reads a file of
random records and prints one hex digest (or "invalid") per record. For the
packed-array APIs every record is a whole array: a random capacity (2^depth
words), random content everywhere, including the bytes past the message that
must not matter, and a byte length that is usually within the capacity and
sometimes beyond it (which must be rejected). Lengths are drawn around every
block and chunk boundary as well as uniformly. References: hashlib (SHA-256,
BLAKE2b, BLAKE2s), pycryptodome (Keccak-256), the official BLAKE3 C
(benchmarks/native/blake, portable build).
"""
import argparse, hashlib, os, random, shutil, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'build' / 'fuzz'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
CC = os.environ.get('CC', 'cc')

# algorithm: (API module, function, hex module, block/chunk sizes, reference)
ARRAY = {
    'keccak256': ('src/crypto/keccak/keccak.bend', 'keccak256', 'src/crypto/keccak/hex.bend', [136]),
    'blake2b': ('src/crypto/blake/blake2b/blake2b.bend', 'blake2b', 'src/crypto/blake/blake2b/hex.bend', [128]),
    'blake2s': ('src/crypto/blake/blake2s/blake2s.bend', 'blake2s', 'src/crypto/blake/blake2s/hex.bend', [64]),
    'blake3': ('src/crypto/blake/blake3/blake3.bend', 'blake3', 'src/crypto/blake/blake3/hex.bend', [64, 1024]),
}

ARRAY_DRIVER = '''import Base
import {api} as K
import {hexm} as H

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def w3(+b0: U32, +b1: U32, +b2: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, b1, b2, 0), Nil{{}})
    case h <> t: (pack(b0, b1, b2, h), t)

def w2(+b0: U32, +b1: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, b1, 0, 0), Nil{{}})
    case h <> t: w3(b0, b1, h, t)

def w1(+b0: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, 0, 0, 0), Nil{{}})
    case h <> t: w2(b0, h, t)

def word(bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (0, Nil{{}})
    case h <> t: w1(h, t)

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{{}}: 0n
    case Some{{n}}: n

# n >= 1 words, the next one already read
def fill(n: Nat, +i: U32, a: Array<U32>, pair: U32 & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match n:
    case 1n:
      (w, rest) = pair
      (Array.set(U32, a, i, w), rest)
    case 2n+p:
      (w, rest) = pair
      fill(1n+p, U32.inc(i), Array.set(U32, a, i, w), word(rest))
    case 0n:
      (w, rest) = pair
      (a, rest)

def show(r: Maybe<&1, Array<U32>>) -> String:
  match r:
    case None{{}}: "invalid"
    case Some{{d}}: H.hex(d)

def hashed(+len: U32, pair: Array<U32> & List<&2, U32>) -> String & List<&2, U32>:
  (a, rest) = pair
  (show(K.{fn}(a, U32.to_nat(len))), rest)

def sized(+depth: Nat, pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (len, rest) = pair
  hashed(len, fill(Nat.pow(2n, depth), 0, Array.new(U32, depth, 0), word(rest)))

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  match bs:
    case Nil{{}}: ("", Nil{{}})
    case d <> t: sized(U32.to_nat(d), word(t))

# n >= 1 records, the next one already hashed
def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 1n:
      (s, rest) = pair
      IO.print(s)
    case 2n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(1n+p, one(rest))
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{{}})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FUZZ_INPUT"))
    nt : String <- IO.try(String, IO.get_env("FUZZ_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), one(bytes))
'''

SHA_DRIVER = '''import Base
import ../../src/crypto/sha/sha256.bend as SHA

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def w3(+b0: U32, +b1: U32, +b2: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, b1, b2, 0), Nil{})
    case h <> t: (pack(b0, b1, b2, h), t)

def w2(+b0: U32, +b1: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, b1, 0, 0), Nil{})
    case h <> t: w3(b0, b1, h, t)

def w1(+b0: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (pack(b0, 0, 0, 0), Nil{})
    case h <> t: w2(b0, h, t)

def word(bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{}: (0, Nil{})
    case h <> t: w1(h, t)

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{}: 0n
    case Some{n}: n

def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{}: (List.reverse(&2, U32, acc), Nil{})
    case 1n+p h <> t: take(p, t, h <> acc)

def hashed(pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = pair
  (SHA.hex(SHA.sha256(msg)), rest)

def one(pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (len, rest) = pair
  hashed(take(U32.to_nat(len), rest, Nil{}))

def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 1n:
      (s, rest) = pair
      IO.print(s)
    case 2n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(1n+p, one(word(rest)))
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("FUZZ_INPUT"))
    nt : String <- IO.try(String, IO.get_env("FUZZ_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), one(word(bytes)))
'''

BLAKE3_REF = r'''#include <stdio.h>
#include <stdlib.h>
#include "blake3.h"
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); unsigned char len4[4]; static unsigned char buf[1 << 24];
  while (fread(len4, 1, 4, f) == 4) {
    size_t n = len4[0] | len4[1] << 8 | len4[2] << 16 | (size_t)len4[3] << 24;
    if (fread(buf, 1, n, f) != n) return 1;
    blake3_hasher h; blake3_hasher_init(&h); blake3_hasher_update(&h, buf, n);
    unsigned char out[32]; blake3_hasher_finalize(&h, out, 32);
    for (int i = 0; i < 32; i++) printf("%02x", out[i]); printf("\n");
  }
  return 0;
}
'''


def lengths(rng, blocks, n):
    """message lengths: around every boundary of the block and chunk sizes, plus uniform"""
    out = []
    edges = [0, 1, 2, 3, 4, 5]
    for b in blocks:
        for k in range(1, 9):
            edges += [k * b - 1, k * b, k * b + 1]
    edges += [16384, 65535, 65536, 65537]
    for i in range(n):
        r = rng.random()
        if r < 0.35:
            out.append(rng.choice(edges))
        elif r < 0.85:
            out.append(rng.randrange(0, 4 * max(blocks) + 64))
        else:
            out.append(rng.randrange(0, 70000))
    return out


def reference(algo, msgs):
    if algo == 'sha256':
        return [hashlib.sha256(m).hexdigest() for m in msgs]
    if algo == 'blake2b':
        return [hashlib.blake2b(m).hexdigest() for m in msgs]
    if algo == 'blake2s':
        return [hashlib.blake2s(m).hexdigest() for m in msgs]
    if algo == 'keccak256':
        from Crypto.Hash import keccak
        return [keccak.new(digest_bits=256, data=m).hexdigest() for m in msgs]
    if algo == 'blake3':
        ref = OUT / 'blake3_ref'
        if not ref.exists():
            (OUT / 'blake3_ref.c').write_text(BLAKE3_REF)
            d = 'benchmarks/native/blake'
            subprocess.run([CC, '-O2', '-I' + d, '-DBLAKE3_NO_SSE2', '-DBLAKE3_NO_SSE41', '-DBLAKE3_NO_AVX2',
                            '-DBLAKE3_NO_AVX512', '-DBLAKE3_USE_NEON=0', str(OUT / 'blake3_ref.c'),
                            d + '/blake3.c', d + '/blake3_dispatch.c', d + '/blake3_portable.c', '-o', str(ref)],
                           cwd=ROOT, check=True)
        p = OUT / 'blake3_ref.in'
        p.write_bytes(b''.join(struct.pack('<I', len(m)) + m for m in msgs))
        return subprocess.run([str(ref), str(p)], capture_output=True, text=True, check=True).stdout.split()
    raise SystemExit('unknown ' + algo)


def fuzz(algo, n, seed):
    OUT.mkdir(parents=True, exist_ok=True)
    rng = random.Random('%s-%d' % (algo, seed))
    drv = OUT / ('fuzz_%s.bend' % algo)
    if algo == 'sha256':
        drv.write_text(SHA_DRIVER)
        blocks = [64]
    else:
        api, fn, hexm, blocks = ARRAY[algo]
        rel = lambda p: os.path.relpath(ROOT / p, OUT)
        drv.write_text(ARRAY_DRIVER.format(api=rel(api), hexm=rel(hexm), fn=fn))
    binary = OUT / ('fuzz_%s' % algo)
    b = subprocess.run([BEND, str(drv.relative_to(ROOT)), '-o', str(binary.relative_to(ROOT))], cwd=ROOT, capture_output=True, text=True)
    if b.returncode:
        raise SystemExit('%s: driver did not build\n%s%s' % (algo, b.stdout[-2000:], b.stderr[-2000:]))
    recs, msgs, expect_invalid = [], [], []
    for L in lengths(rng, blocks, n):
        if algo == 'sha256':
            m = rng.randbytes(L)
            recs.append(struct.pack('<I', L) + m)
            msgs.append(m)
            expect_invalid.append(False)
            continue
        need = max(1, (L + 3) // 4)
        depth = max(0, (need - 1).bit_length()) + rng.choice([0, 0, 0, 1, 2])
        cap = 4 * (1 << depth)
        content = rng.randbytes(cap)                    # garbage past the message included
        length = L if rng.random() > 0.05 else cap + rng.randrange(1, 64)   # sometimes too long
        recs.append(bytes([depth]) + struct.pack('<I', length) + content)
        msgs.append(content[:length])
        expect_invalid.append(length > cap)
    inp = OUT / ('fuzz_%s.in' % algo)
    inp.write_bytes(b''.join(recs))
    r = subprocess.run([str(binary), '--threads', '1'], env={**os.environ, 'FUZZ_INPUT': str(inp), 'FUZZ_COUNT': str(len(recs))},
                       capture_output=True, text=True)
    got = r.stdout.split()
    if r.returncode or len(got) != len(recs):
        raise SystemExit('%s: driver failed (%d of %d outputs)\n%s' % (algo, len(got), len(recs), r.stderr[-1000:]))
    valid = [m for m, bad in zip(msgs, expect_invalid) if not bad]
    refs = iter(reference(algo, valid))
    bad = 0
    for i, (g, inv, m) in enumerate(zip(got, expect_invalid, msgs)):
        want = 'invalid' if inv else next(refs)
        if g != want:
            bad += 1
            if bad <= 5:
                print('  MISMATCH %s case %d: length %d, got %s, want %s' % (algo, i, len(m), g[:16], want[:16]))
    lens = [len(m) for m in msgs]
    print('%-10s %s  %d cases (%d rejected), lengths 0..%d, seed %d' % (algo, 'ok  ' if not bad else 'FAIL', len(recs), sum(expect_invalid), max(lens), seed), flush=True)
    return bad == 0


def main():
    ap = argparse.ArgumentParser(description='Differential fuzzing of the hash functions.')
    ap.add_argument('algorithms', nargs='*', default=['sha256', 'keccak256', 'blake2b', 'blake2s', 'blake3'])
    ap.add_argument('-n', type=int, default=2000)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    ok = all([fuzz(x, a.n, a.seed) for x in a.algorithms])
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
