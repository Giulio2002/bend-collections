#!/usr/bin/env python3
"""Tests of AES (src/crypto/aes/aes.bend) and AES-GCM (src/crypto/aesgcm.bend).

  python3 tools/check_aes.py                every check
  python3 tools/check_aes.py -n 500         500 random cases per random check

A Bend driver (written to build/aes/, compiled with the pinned Bend) reads a
file of records (operation, key, nonce, AAD, data) and prints one line per
record: the hex output, "-" for an empty output, "none" for None. The lines
are compared with:

  fips197   the FIPS 197 Appendix C example vectors (AES-128/192/256)
  nist      the NIST CAVP GCM vectors in tests/crypto/aes/gcm_nist.txt
            (gcmEncryptExtIV / gcmDecrypt, 96-bit IV, 128-bit tag, including
            the FAIL cases, which must decrypt to None)
  block     random blocks under random 16/24/32-byte keys against the
            `cryptography` package's AES (ECB, one block), plus keys and
            blocks of other lengths (None)
  gcm       random AES-128-GCM and AES-256-GCM against `cryptography`'s
            AESGCM: encryption (plaintext and AAD lengths around every block
            boundary), decryption of the result, decryption after flipping
            one bit of the ciphertext, the tag or the AAD (None), and keys and
            nonces of the wrong length (None)

Exit status 0 exactly when every case agrees.
"""
import argparse, os, random, shutil, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'aes'
sys.path.insert(0, str(ROOT / 'tools'))
try:
    from toolchain import BEND  # noqa: E402
except Exception:  # pragma: no cover
    BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes  # noqa: E402
from cryptography.hazmat.primitives.ciphers.aead import AESGCM  # noqa: E402
from cryptography.exceptions import InvalidTag  # noqa: E402

DRIVER = '''import Base
import ../../src/crypto/aes/aes.bend as AES
import ../../src/crypto/aesgcm.bend as GCM

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

def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{}: (List.reverse(&2, U32, acc), Nil{})
    case 1n+p h <> t: take(p, t, h <> acc)

def field_go(pair: U32 & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (n, rest) = pair
  take(U32.to_nat(n), rest, Nil{})

def field(bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  field_go(word(bs))

def shown(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}: "-"
    case +h <> t: AES.hex(h <> t)

def show(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}: "none"
    case Some{bs}: shown(bs)

def block_with(m: Maybe<&2, AES.Schedule>, block: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}: None{}
    case Some{s}: AES.encrypt_block(s, block)

def apply(op: Nat, +key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +data: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match op:
    case 0n: block_with(AES.expand_key(key), data)
    case 1n: GCM.aes128_gcm_encrypt(key, nonce, aad, data)
    case 2n: GCM.aes128_gcm_decrypt(key, nonce, aad, data)
    case 3n: GCM.aes256_gcm_encrypt(key, nonce, aad, data)
    case 4n+p: GCM.aes256_gcm_decrypt(key, nonce, aad, data)

def rec5(+op: U32, key: List<&2, U32>, nonce: List<&2, U32>, aad: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (data, rest) = pair
  (show(apply(U32.to_nat(op), key, nonce, aad, data)), rest)

def rec4(+op: U32, key: List<&2, U32>, nonce: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (aad, rest) = pair
  rec5(op, key, nonce, aad, field(rest))

def rec3(+op: U32, key: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (nonce, rest) = pair
  rec4(op, key, nonce, field(rest))

def rec2(+op: U32, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (key, rest) = pair
  rec3(op, key, field(rest))

def rec1(pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (op, rest) = pair
  rec2(op, field(rest))

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  rec1(word(bs))

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
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{})
    case 1n+p:
      (s, rest) = pair
      do IO<Unit>:
        IO.print(s)
        records(p, one(rest))

def main() -> IO(Unit):
  do IO<Unit>:
    path : String <- IO.try(String, IO.get_env("CHECK_INPUT"))
    nt : String <- IO.try(String, IO.get_env("CHECK_COUNT"))
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(file, 268435456)
    bytes : List<&2, U32> <- loaded(pair)
    records(count(Nat.read(nt)), one(bytes))
'''

BLOCK, ENC128, DEC128, ENC256, DEC256 = range(5)


def u32(n):
    return struct.pack('<I', n)


def record(op, key=b'', nonce=b'', aad=b'', data=b''):
    return u32(op) + b''.join(u32(len(f)) + f for f in (key, nonce, aad, data))


def show(b):
    return 'none' if b is None else (b.hex() if b else '-')


def ref_block(key, block):
    if len(key) not in (16, 24, 32) or len(block) != 16:
        return None
    e = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return e.update(block) + e.finalize()


def ref_gcm(op, key, nonce, aad, data):
    width = 16 if op in (ENC128, DEC128) else 32
    if len(key) != width or len(nonce) != 12:
        return None
    g = AESGCM(key)
    if op in (ENC128, ENC256):
        return g.encrypt(nonce, data, aad)
    try:
        return g.decrypt(nonce, data, aad)
    except (InvalidTag, ValueError):
        return None


def reference(op, key, nonce, aad, data):
    return ref_block(key, data) if op == BLOCK else ref_gcm(op, key, nonce, aad, data)


def build():
    OUT.mkdir(parents=True, exist_ok=True)
    drv = OUT / 'check_aes.bend'
    drv.write_text(DRIVER)
    binary = OUT / 'check_aes'
    b = subprocess.run([BEND, str(drv.relative_to(ROOT)), '-o', str(binary.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True)
    if b.returncode or not binary.exists():
        raise SystemExit('driver did not build\n%s%s' % (b.stdout[-3000:], b.stderr[-3000:]))
    return binary


def run(binary, name, cases):
    inp = OUT / ('check_%s.in' % name)
    inp.write_bytes(b''.join(record(*c[:5]) for c in cases))
    r = subprocess.run([str(binary), '--threads', '1'],
                       env={**os.environ, 'CHECK_INPUT': str(inp), 'CHECK_COUNT': str(len(cases))},
                       capture_output=True, text=True)
    got = r.stdout.splitlines()
    if r.returncode or len(got) != len(cases):
        raise SystemExit('%s: driver failed (%d of %d outputs)\n%s' % (name, len(got), len(cases), r.stderr[-2000:]))
    return got


def report(name, got, cases):
    bad = [(i, g, c) for i, (g, c) in enumerate(zip(got, cases)) if g != c[5]]
    for i, g, c in bad[:5]:
        print('  MISMATCH %s case %d (%s): got %s, want %s' % (name, i, c[6], g[:48], c[5][:48]))
    print('%-8s %s  %d cases, %d failures' % (name, 'ok  ' if not bad else 'FAIL', len(got), len(bad)), flush=True)
    return not bad


def case(op, key, nonce, aad, data, want, what):
    return (op, key, nonce, aad, data, want, what)


def fips197():
    pt = bytes.fromhex('00112233445566778899aabbccddeeff')
    out = []
    for k, ct in [('000102030405060708090a0b0c0d0e0f', '69c4e0d86a7b0430d8cdb78070b4c55a'),
                  ('000102030405060708090a0b0c0d0e0f1011121314151617', 'dda97ca4864cdfe06eaf70a0ec0d7191'),
                  ('000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f', '8ea2b7ca516745bfeafc49904b496089')]:
        key = bytes.fromhex(k)
        assert ref_block(key, pt).hex() == ct
        out.append(case(BLOCK, key, b'', b'', pt, ct, 'FIPS 197 C, %d-bit key' % (8 * len(key))))
    return out


def nist():
    out = []
    un = lambda s: b'' if s == '-' else bytes.fromhex(s)
    for line in (ROOT / 'tests/crypto/aes/gcm_nist.txt').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        f = line.split()
        bits = int(f[0][1:])
        key, iv, aad = un(f[1]), un(f[2]), un(f[3])
        if f[0][0] == 'E':
            pt, ct, tag = un(f[4]), un(f[5]), un(f[6])
            op = ENC128 if bits == 128 else ENC256
            out.append(case(op, key, iv, aad, pt, show(ct + tag), 'NIST %s len(P)=%d len(A)=%d' % (f[0], len(pt), len(aad))))
            assert reference(op, key, iv, aad, pt) == ct + tag
        else:
            ct, tag = un(f[4]), un(f[5])
            want = None if f[6] == 'FAIL' else un(f[6])
            op = DEC128 if bits == 128 else DEC256
            out.append(case(op, key, iv, aad, ct + tag, show(want), 'NIST %s len(C)=%d %s' % (f[0], len(ct), 'FAIL' if want is None else 'pass')))
            assert reference(op, key, iv, aad, ct + tag) == want
    return out


def lengths(rng):
    edges = [0, 1, 15, 16, 17, 31, 32, 33, 47, 48, 64, 65]
    return rng.choice(edges) if rng.random() < 0.5 else rng.randrange(0, 100)


def block_cases(rng, n):
    out = []
    for i in range(n):
        klen = rng.choice([16, 24, 32, 16, 24, 32, 0, 15, 17, 31, 33])
        blen = 16 if rng.random() < 0.85 else rng.choice([0, 15, 17, 32])
        key, blk = rng.randbytes(klen), rng.randbytes(blen)
        out.append(case(BLOCK, key, b'', b'', blk, show(ref_block(key, blk)), 'key %d, block %d' % (klen, blen)))
    return out


def gcm_cases(rng, n):
    out = []
    for i in range(n):
        wide = i % 2 == 1
        enc, dec = (ENC256, DEC256) if wide else (ENC128, DEC128)
        width = 32 if wide else 16
        key, nonce = rng.randbytes(width), rng.randbytes(12)
        aad, pt = rng.randbytes(lengths(rng)), rng.randbytes(lengths(rng))
        ct = AESGCM(key).encrypt(nonce, pt, aad)
        tag = 'AES-%d len(P)=%d len(A)=%d' % (8 * width, len(pt), len(aad))
        out.append(case(enc, key, nonce, aad, pt, ct.hex(), 'encrypt ' + tag))
        out.append(case(dec, key, nonce, aad, ct, show(pt), 'decrypt ' + tag))
        kind = rng.choice(['ct', 'tag', 'aad', 'short', 'key', 'nonce', 'nonce'])
        if kind in ('ct', 'tag') and (kind == 'tag' or pt):
            bad = bytearray(ct)
            j = rng.randrange(len(pt)) if kind == 'ct' else len(pt) + rng.randrange(16)
            bad[j] ^= 1 << rng.randrange(8)
            out.append(case(dec, key, nonce, aad, bytes(bad), 'none', 'flipped %s bit, ' % kind + tag))
        elif kind == 'aad':
            a2 = bytearray(aad + b'\x00') if not aad else bytearray(aad)
            a2[rng.randrange(len(a2))] ^= 1 << rng.randrange(8)
            out.append(case(dec, key, nonce, bytes(a2), ct, 'none', 'changed AAD, ' + tag))
        elif kind == 'short':
            out.append(case(dec, key, nonce, aad, ct[:rng.randrange(16)], 'none', 'input under 16 bytes'))
        elif kind == 'key':
            k2 = rng.randbytes(rng.choice([0, 15, 17, 24, 32 if not wide else 16]))
            out.append(case(enc, k2, nonce, aad, pt, show(ref_gcm(enc, k2, nonce, aad, pt)), 'key of %d bytes' % len(k2)))
            out.append(case(dec, k2, nonce, aad, ct, 'none', 'key of %d bytes (decrypt)' % len(k2)))
        else:
            n2 = rng.randbytes(rng.choice([0, 8, 11, 13, 16]))
            out.append(case(enc, key, n2, aad, pt, 'none', 'nonce of %d bytes' % len(n2)))
            out.append(case(dec, key, n2, aad, ct, 'none', 'nonce of %d bytes (decrypt)' % len(n2)))
    return out


def main():
    ap = argparse.ArgumentParser(description='Tests of AES and AES-GCM.')
    ap.add_argument('checks', nargs='*', default=['fips197', 'nist', 'block', 'gcm'])
    ap.add_argument('-n', type=int, default=300)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    binary = build()
    ok = True
    for c in a.checks:
        rng = random.Random('aes-%s-%d' % (c, a.seed))
        cases = {'fips197': fips197, 'nist': nist,
                 'block': lambda: block_cases(rng, a.n), 'gcm': lambda: gcm_cases(rng, a.n)}[c]()
        ok &= report(c, run(binary, c, cases), cases)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
