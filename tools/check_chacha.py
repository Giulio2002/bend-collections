#!/usr/bin/env python3
"""Differential test of ChaCha20, HChaCha20, XChaCha20 and the
ChaCha20-Poly1305 / XChaCha20-Poly1305 AEADs against Python references.

  python3 tools/check_chacha.py            2000 random cases per operation
  python3 tools/check_chacha.py -n 300 --seed 7

A Bend driver (written to build/check_chacha/) reads a file of records and
prints one line per record: the hex of the result, or "invalid" for None.
References: the `cryptography` package (ChaCha20Poly1305; ChaCha20 where the
32-bit block counter does not wrap), a Python ChaCha20 block function for
HChaCha20 and for counter wrap-around, and XChaCha20(-Poly1305) composed from
HChaCha20 as draft-irtf-cfrg-xchacha-03 specifies. Inputs: random keys,
nonces, counters, aad and messages with lengths around the 16- and 64-byte
boundaries, wrong key/nonce lengths (rejected), and for decryption correctly
sealed messages, messages with one flipped bit (in ciphertext, tag or aad),
and inputs shorter than a tag.
"""
import argparse
import os
import random
import shutil
import struct
import subprocess
import sys
from pathlib import Path

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'check_chacha'
BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')
MASK = 0xffffffff

DRIVER = '''import Base
import ../../src/crypto/chacha/chacha20.bend as CH
import ../../src/crypto/aead.bend as A

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}: Chr{(48 + x : U32)}
    case False{}: Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}: ""
    case +b <> t: SCon{hex_digit(U32.and(U32.shrn(b, 4n), 15)), SCon{hex_digit(U32.and(b, 15)), hex(t)}}

def show(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}: "invalid"
    case Some{bs}: hex(bs)

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def u32(bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case b0 <> b1 <> b2 <> b3 <> rest: (pack(b0, b1, b2, b3), rest)
    case _: (0, Nil{})

def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{}: (List.reverse(&2, U32, acc), Nil{})
    case 1n+p h <> t: take(p, t, h <> acc)

def field(pair: U32 & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (n, rest) = pair
  take(U32.to_nat(n), rest, Nil{})

def run_n(op: Nat, counter: U32, key: List<&2, U32>, nonce: List<&2, U32>, aad: List<&2, U32>, msg: List<&2, U32>) -> String:
  match op:
    case 0n: show(CH.chacha20(key, counter, nonce, msg))
    case 1n: show(CH.hchacha20(key, nonce))
    case 2n: show(CH.xchacha20(key, counter, nonce, msg))
    case 3n: show(A.encrypt(A.CHACHA20_POLY1305{}, key, nonce, aad, msg))
    case 4n: show(A.decrypt(A.CHACHA20_POLY1305{}, key, nonce, aad, msg))
    case 5n: show(A.encrypt(A.XCHACHA20_POLY1305{}, key, nonce, aad, msg))
    case 6n: show(A.decrypt(A.XCHACHA20_POLY1305{}, key, nonce, aad, msg))
    case _: "bad op"

def run(op: U32, counter: U32, key: List<&2, U32>, nonce: List<&2, U32>, aad: List<&2, U32>, msg: List<&2, U32>) -> String:
  run_n(U32.to_nat(op), counter, key, nonce, aad, msg)

def r4(op: U32, counter: U32, key: List<&2, U32>, nonce: List<&2, U32>, aad: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = pair
  (run(op, counter, key, nonce, aad, msg), rest)

def r3(op: U32, counter: U32, key: List<&2, U32>, nonce: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (aad, rest) = pair
  r4(op, counter, key, nonce, aad, field(u32(rest)))

def r2(op: U32, counter: U32, key: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (nonce, rest) = pair
  r3(op, counter, key, nonce, field(u32(rest)))

def r1(op: U32, counter: U32, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (key, rest) = pair
  r2(op, counter, key, field(u32(rest)))

def r0(op: U32, pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (counter, rest) = pair
  r1(op, counter, field(u32(rest)))

def one(pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (op, rest) = pair
  r0(op, u32(rest))

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{}: 0n
    case Some{n}: n

def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 1n:
      (s, rest) = pair
      IO.print(s)
    case 2n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(1n+p, one(u32(rest)))
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("CHECK_INPUT"))
    nt : String <- IO.try(String, IO.get_env("CHECK_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), one(u32(bytes)))
'''


# ---------------------------------------------------------------- references

def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & MASK


def qr(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 7)


def rounds(s):
    s = list(s)
    for _ in range(10):
        qr(s, 0, 4, 8, 12); qr(s, 1, 5, 9, 13); qr(s, 2, 6, 10, 14); qr(s, 3, 7, 11, 15)
        qr(s, 0, 5, 10, 15); qr(s, 1, 6, 11, 12); qr(s, 2, 7, 8, 13); qr(s, 3, 4, 9, 14)
    return s


CONST = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]


def block(key, counter, nonce):
    s = CONST + list(struct.unpack('<8I', key)) + [counter] + list(struct.unpack('<3I', nonce))
    w = rounds(s)
    return struct.pack('<16I', *[(a + b) & MASK for a, b in zip(s, w)])


def chacha20(key, counter, nonce, data):
    out = bytearray()
    for j in range(0, len(data), 64):
        ks = block(key, (counter + j // 64) & MASK, nonce)
        out += bytes(a ^ b for a, b in zip(data[j:j + 64], ks))
    return bytes(out)


def hchacha20(key, nonce16):
    s = rounds(CONST + list(struct.unpack('<8I', key)) + list(struct.unpack('<4I', nonce16)))
    return struct.pack('<8I', *(s[0:4] + s[12:16]))


def ref(op, counter, key, nonce, aad, msg):
    if len(key) != 32:
        return 'invalid'
    if op == 0:
        return chacha20(key, counter, nonce, msg).hex() if len(nonce) == 12 else 'invalid'
    if op == 1:
        return hchacha20(key, nonce).hex() if len(nonce) == 16 else 'invalid'
    if op == 2:
        if len(nonce) != 24:
            return 'invalid'
        return chacha20(hchacha20(key, nonce[:16]), counter, bytes(4) + nonce[16:], msg).hex()
    if op in (5, 6):
        if len(nonce) != 24:
            return 'invalid'
        key, nonce, op = hchacha20(key, nonce[:16]), bytes(4) + nonce[16:], op - 2
    if len(nonce) != 12:
        return 'invalid'
    aead = ChaCha20Poly1305(key)
    if op == 3:
        return aead.encrypt(nonce, msg, aad).hex()
    try:
        return aead.decrypt(nonce, msg, aad).hex()
    except InvalidTag:
        return 'invalid'


# ---------------------------------------------------------------- cases

def rbytes(rng, n):
    return bytes(rng.getrandbits(8) for _ in range(n))


def length(rng, edges):
    r = rng.random()
    if r < 0.4:
        return rng.choice(edges)
    return rng.randrange(0, 300)


EDGES = [0, 1, 2, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 191, 192, 193, 255, 256, 257]


def cases(rng, n, ops):
    out = []
    for op in ops:
        for i in range(n):
            nlen = {0: 12, 1: 16, 2: 24, 3: 12, 4: 12, 5: 24, 6: 24}[op]
            klen = 32
            r = rng.random()
            if r < 0.03:
                klen = rng.choice([0, 16, 31, 33])
            elif r < 0.06:
                nlen = rng.choice([0, 8, 11, 13, 16, 23, 25])
            key, nonce = rbytes(rng, klen), rbytes(rng, nlen)
            counter = rng.choice([0, 1, 2, rng.getrandbits(32), MASK, MASK - 1]) if op in (0, 2) else 0
            aad = rbytes(rng, length(rng, EDGES)) if op >= 3 else b''
            msg = rbytes(rng, length(rng, EDGES))
            if op in (4, 6):
                # a sealed message under the same parameters (when they are valid), then maybe damaged
                good = ref(op - 1, 0, key, nonce, aad, msg)
                data = bytes.fromhex(good) if good != 'invalid' else msg
                t = rng.random()
                if t < 0.25 and data:
                    k = rng.randrange(len(data) * 8)
                    data = bytearray(data); data[k // 8] ^= 1 << (k % 8); data = bytes(data)
                elif t < 0.35 and aad:
                    k = rng.randrange(len(aad) * 8)
                    aad = bytearray(aad); aad[k // 8] ^= 1 << (k % 8); aad = bytes(aad)
                elif t < 0.4:
                    data = data[:rng.randrange(0, 16)]
                msg = data
            out.append((op, counter, key, nonce, aad, msg))
    return out


def encode(cs):
    b = bytearray()
    for op, counter, key, nonce, aad, msg in cs:
        b += struct.pack('<II', op, counter)
        for f in (key, nonce, aad, msg):
            b += struct.pack('<I', len(f)) + f
    return bytes(b)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('-n', type=int, default=2000, help='cases per operation')
    ap.add_argument('--seed', type=int, default=8439)
    ap.add_argument('--ops', default='0,1,2,3,4,5,6', help='operations to test (0-6)')
    a = ap.parse_args()
    rng = random.Random(a.seed)
    # the references themselves against the published vectors
    k = bytes(range(32))
    assert block(k, 1, bytes.fromhex('000000090000004a00000000'))[:4].hex() == '10f1e7e4'
    assert hchacha20(k, bytes.fromhex('000000090000004a0000000031415927')).hex() == \
        '82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc'
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'driver.bend').write_text(DRIVER)
    binary = OUT / 'driver'
    p = subprocess.run([BEND, str((OUT / 'driver.bend').relative_to(ROOT)), '-o', str(binary.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True)
    if not binary.exists():
        print(p.stdout + p.stderr)
        return 1
    ops = [int(x) for x in a.ops.split(',')]
    cs = cases(rng, a.n, ops)
    inp = OUT / 'input.bin'
    inp.write_bytes(encode(cs))
    env = dict(os.environ, CHECK_INPUT=str(inp), CHECK_COUNT=str(len(cs)))
    run = subprocess.run([str(binary)], capture_output=True, text=True, env=env, timeout=3600)
    got = run.stdout.split('\n')
    names = ['chacha20', 'hchacha20', 'xchacha20', 'chacha20poly1305.encrypt', 'chacha20poly1305.decrypt',
             'xchacha20poly1305.encrypt', 'xchacha20poly1305.decrypt']
    fails = {}
    rejected = {}
    for i, c in enumerate(cs):
        want = ref(*c)
        g = got[i] if i < len(got) else '<missing>'
        if want == 'invalid':
            rejected[c[0]] = rejected.get(c[0], 0) + 1
        if g != want:
            fails[c[0]] = fails.get(c[0], 0) + 1
            if fails[c[0]] <= 3:
                print('FAIL %s case %d: got %s want %s' % (names[c[0]], i, g[:80], want[:80]))
    for op, name in enumerate(names):
        if op not in ops:
            continue
        print('%-28s %5d cases, %4d rejected, %d failures' % (name, a.n, rejected.get(op, 0), fails.get(op, 0)))
    total = sum(fails.values())
    print('check_chacha: %d cases, %d failures (seed %d)' % (len(cs), total, a.seed))
    return 1 if total or run.returncode != 0 else 0


if __name__ == '__main__':
    sys.exit(main())
