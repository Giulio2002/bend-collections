#!/usr/bin/env python3
"""Differential check of Poly1305 (src/crypto/poly1305/poly1305.bend).

  python3 tools/check_poly1305.py            2000 random cases, seed 1305
  python3 tools/check_poly1305.py -n 5000 --seed 7

1. A Bend driver (written to build/poly1305/) reads a file of records
   (key length, key, message length, message) and prints, per record, the
   checked tag P.poly1305(key, msg) in hex, or "none"; it is compared with
   the `cryptography` package's Poly1305 (and "none" exactly when the key is
   not 32 bytes). Message lengths cluster around every 16-byte block
   boundary; keys include all-zero, all-0xff and r values that clamp to
   limits.
2. spec/crypto/poly1305.bend cannot run natively (its accumulator is a Nat of
   130 bits; Bend's native Nat stops at 2^48), so a line-by-line Python mirror
   of it (mirror_mac below, with the same modp) is compared with
   `cryptography` on the same cases.

Exit status 0 exactly when every case agrees.
"""
import argparse, os, random, shutil, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'poly1305'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')

DRIVER = '''import Base
import ../../src/crypto/poly1305/poly1305.bend as P

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{}: 0n
    case Some{n}: n

def digit_if(small: Bool, x: U32) -> Char:
  match small:
    case True{}: Chr{U32.add(48, x)}
    case False{}: Chr{U32.add(87, x)}

def hex_digit(+x: U32) -> Char:
  digit_if(U32.is_lt(x, 10), x)

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}: ""
    case +b <> t: SCon{hex_digit(U32.shrn(b, 4n)), SCon{hex_digit(U32.and(b, 15)), hex(t)}}

def show(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}: "none"
    case Some{x}: hex(x)

# the first n bytes, and the rest
def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{}: (List.reverse(&2, U32, acc), Nil{})
    case 1n+p h <> t: take(p, t, h <> acc)

# a length byte pair (little-endian 16 bits), then the bytes
def field(bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match bs:
    case lo <> hi <> rest: take(U32.to_nat(U32.or(lo, U32.shln(hi, 8n))), rest, Nil{})
    case _: (Nil{}, Nil{})

def tagged(key: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = pair
  (show(P.poly1305(key, msg)), rest)

def keyed(pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (key, rest) = pair
  tagged(key, field(rest))

# n >= 1 records, the next one already computed
def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 1n:
      (s, rest) = pair
      IO.print(s)
    case 2n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(1n+p, keyed(field(rest)))
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("POLY_INPUT"))
    nt : String <- IO.try(String, IO.get_env("POLY_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), keyed(field(bytes)))
'''

# ---- a line-by-line mirror of spec/crypto/poly1305.bend ----

def low(k, n):
    return n % (1 << k)

def high(k, n):
    return n >> k

def fits(k, n):
    return high(k, n) == 0

def fold(x):
    return low(130, x) + high(130, x) * 5

def folds(n, x):
    # folds(n, x) applies fold n times; fold is the identity once x fits 130
    # bits, so stopping there is the same function
    for _ in range(n):
        y = fold(x)
        if y == x:
            break
        x = y
    return x

def pick(b, x, y):
    return x if b else y

def canon(y):
    if y == 0:
        return 0
    return pick(fits(130, y + 5), y, low(130, y + 5))

def modp(x):
    return canon(folds(x, x))

def le_num(bs):
    n = 0
    for b in reversed(bs):
        n = (b & 255) + (n << 8)
    return n

def le_bytes(n, x):
    out = []
    for _ in range(n):
        out.append(low(8, x))
        x = high(8, x)
    return out

def clamp_mask(i):
    return {3: 15, 7: 15, 11: 15, 15: 15, 4: 252, 8: 252, 12: 252}.get(i, 255)

def clamp(r):
    return [b & clamp_mask(i) for i, b in enumerate(r)]

def blocks(msg):
    return [msg[i:i + 16] for i in range(0, len(msg), 16)]

def absorb(bs, r, a):
    for b in bs:
        n = le_num(b + [1])
        a = modp(r * (a + n))
    return a

def mirror_mac(key, msg):
    r = le_num(clamp(key[:16]))
    s = le_num(key[16:32])
    return le_bytes(16, absorb(blocks(msg), r, 0) + s)

# ---- cases ----

def cases(rng, n):
    edges = [0, 1, 2, 15, 16, 17, 31, 32, 33, 47, 48, 49, 63, 64, 65, 127, 128, 129, 255, 256, 257, 1000]
    keys = [bytes(32), b'\xff' * 32, bytes([0xff] * 16 + [0] * 16), bytes([0] * 16 + [0xff] * 16),
            bytes([3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] + [0xff] * 16)]
    out = []
    for i in range(n):
        u = rng.random()
        if i < len(keys) * 3:
            key = keys[i % len(keys)]
        elif u < 0.05:
            key = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 16, 31, 33, 40])))
        else:
            key = bytes(rng.randrange(256) for _ in range(32))
        m = rng.choice(edges) if rng.random() < 0.5 else rng.randrange(0, 300)
        if rng.random() < 0.1:
            msg = bytes([0xff] * m)
        else:
            msg = bytes(rng.randrange(256) for _ in range(m))
        out.append((key, msg))
    return out

def reference(key, msg):
    if len(key) != 32:
        return 'none'
    from cryptography.hazmat.primitives.poly1305 import Poly1305
    return Poly1305.generate_tag(key, msg).hex()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('-n', type=int, default=2000)
    ap.add_argument('--seed', type=int, default=1305)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    cs = cases(rng, a.n)
    want = [reference(k, m) for k, m in cs]
    failures = 0
    # 2. the spec mirror
    for (k, m), w in zip(cs, want):
        if len(k) == 32 and bytes(mirror_mac(list(k), list(m))).hex() != w:
            failures += 1
            print('FAIL spec mirror: key %s msg %s' % (k.hex(), m.hex()))
    # 1. the implementation
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'driver.bend').write_text(DRIVER)
    binary = OUT / 'driver'
    p = subprocess.run([BEND, str((OUT / 'driver.bend').relative_to(ROOT)), '-o', str(binary.relative_to(ROOT))], cwd=ROOT, capture_output=True, text=True)
    if not binary.exists():
        print(p.stdout + p.stderr)
        return 1
    data = OUT / 'input.bin'
    data.write_bytes(b''.join(struct.pack('<H', len(k)) + k + struct.pack('<H', len(m)) + m for k, m in cs))
    env = dict(os.environ, POLY_INPUT=str(data), POLY_COUNT=str(len(cs)))
    got = subprocess.run([str(binary)], capture_output=True, text=True, env=env).stdout.split()
    if len(got) != len(cs):
        print('FAIL driver printed %d lines for %d cases' % (len(got), len(cs)))
        return 1
    for (k, m), g, w in zip(cs, got, want):
        if g != w:
            failures += 1
            print('FAIL impl: key %s msg %s got %s want %s' % (k.hex(), m.hex(), g, w))
    print('poly1305: %d cases (seed %d), implementation and spec mirror vs cryptography: %d failures' % (len(cs), a.seed, failures))
    return 1 if failures else 0

if __name__ == '__main__':
    sys.exit(main())
