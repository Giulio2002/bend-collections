#!/usr/bin/env python3
"""Differential test of src/crypto/argon2 against argon2-cffi.

  python3 tools/check_argon2.py [seed]

Builds tests/crypto/argon2/main.bend (unless build/argon2/test exists and is
newer than every source), runs its fixed vectors (RFC 9106 section 5.3 with
secret and associated data, and the parameter rejections), then compares
Argon2id tags on random inputs and small parameters (m = 8..64 KiB, t = 1..3,
p = 1..2 and some p = 3..4, tag lengths 4..100 across the H' boundary at 64,
passwords/salts/secrets/associated data of assorted lengths) with
argon2.low_level.hash_secret_raw(type=Type.ID, version=19), and the
password-hashing facade (src/crypto/password.bend, PHC strings) with
argon2.PasswordHasher. Prints a JSON verdict; exit status 0 iff no failure.
"""
import json, os, random, subprocess, sys, time
from pathlib import Path

from argon2.low_level import Type, hash_secret_raw

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/argon2/test'
SRC = [ROOT / 'tests/crypto/argon2/main.bend'] + sorted((ROOT / 'src/crypto/argon2').glob('*.bend')) + \
      [ROOT / 'src/crypto/blake/blake2b/sized.bend']
BEND = os.environ.get('BEND', 'bend')
BATCH = 40


def build():
    if BIN.exists() and all(BIN.stat().st_mtime > f.stat().st_mtime for f in SRC):
        return True, ''
    BIN.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([BEND, 'tests/crypto/argon2/main.bend', '-o', str(BIN)], cwd=ROOT,
                       capture_output=True, text=True, timeout=1800)
    return BIN.exists(), p.stdout + p.stderr


def hx(b):
    return b.hex() if b else '-'


def reference(pw, salt, key, ad, t, m, p, tl):
    if not (1 <= p < 2 ** 24 and 4 <= tl and m >= 8 * p and t >= 1 and len(salt) >= 8):
        return 'invalid'
    # argon2-cffi's low-level binding has no secret/ad arguments; use the raw
    # C binding for those through argon2._ffi when they are present.
    if key or ad:
        return raw_with_secret(pw, salt, key, ad, t, m, p, tl).hex()
    return hash_secret_raw(pw, salt, t, m, p, tl, Type.ID, 19).hex()


def raw_with_secret(pw, salt, key, ad, t, m, p, tl):
    from argon2.low_level import ffi, lib
    out = ffi.new('uint8_t[]', tl)
    keep = [ffi.new('uint8_t[]', x if x else b'\0') for x in (pw, salt, key, ad)]
    ctx = ffi.new('argon2_context *', dict(
        version=19, out=out, outlen=tl,
        pwd=keep[0], pwdlen=len(pw), salt=keep[1], saltlen=len(salt),
        secret=keep[2], secretlen=len(key), ad=keep[3], adlen=len(ad),
        t_cost=t, m_cost=m, lanes=p, threads=p,
        allocate_cbk=ffi.NULL, free_cbk=ffi.NULL, flags=lib.ARGON2_DEFAULT_FLAGS))
    rc = lib.argon2_ctx(ctx, lib.Argon2_id)
    if rc != 0:
        raise RuntimeError(ffi.string(lib.argon2_error_message(rc)).decode())
    return bytes(ffi.buffer(out, tl))


def rbytes(rng, n):
    return bytes(rng.randrange(256) for _ in range(n))


def cases(rng):
    lens = [0, 1, 3, 4, 5, 8, 15, 16, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 200]
    out = []
    for i in range(140):
        p = rng.choice([1, 1, 1, 2, 2, 3, 4])
        m = rng.choice([8 * p, 8 * p + 1, 8 * p + 3, 16 * p, rng.randrange(8 * p, 65), 64])
        m = max(m, 8 * p)
        t = rng.choice([1, 1, 2, 3])
        tl = rng.choice([4, 5, 16, 31, 32, 33, 63, 64, 65, 66, 96, 100, 128])
        pw = rbytes(rng, rng.choice(lens))
        salt = rbytes(rng, rng.choice([8, 9, 16, 16, 32, 65]))
        key = rbytes(rng, rng.choice([0, 0, 0, 8, 32])) if i % 3 == 0 else b''
        ad = rbytes(rng, rng.choice([0, 0, 12, 40])) if i % 4 == 0 else b''
        out.append((pw, salt, key, ad, t, m, p, tl))
    # a few larger memories (several address blocks per segment: segment length > 128)
    for m, t, p in [(1024, 1, 1), (2048, 2, 2), (4096, 1, 4)]:
        out.append((rbytes(rng, 16), rbytes(rng, 16), b'', b'', t, m, p, 32))
    # rejections
    out += [(b'pw', b'saltsalt', b'', b'', 1, 15, 2, 32), (b'pw', b'short', b'', b'', 1, 8, 1, 32),
            (b'pw', b'saltsalt', b'', b'', 0, 8, 1, 32), (b'pw', b'saltsalt', b'', b'', 1, 8, 1, 3),
            (b'pw', b'saltsalt', b'', b'', 1, 8, 0, 32)]
    return out


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    ok, log = build()
    if not ok:
        print(json.dumps({'passed': False, 'error': 'build failed', 'log': log[-2000:]}))
        return 1
    fails = []
    t0 = time.time()
    vec = subprocess.run([str(BIN)], capture_output=True, text=True, timeout=600).stdout.splitlines()
    if not vec or vec[-1] != '0 failures':
        fails.append({'vectors': vec})
    todo = cases(rng)
    for i in range(0, len(todo), BATCH):
        chunk = todo[i:i + BATCH]
        toks = [':'.join([hx(c[0]), hx(c[1]), hx(c[2]), hx(c[3])] + [str(x) for x in c[4:]]) for c in chunk]
        p = subprocess.run([str(BIN)] + toks, capture_output=True, text=True, timeout=1800)
        got = p.stdout.split('\n')
        for c, g in zip(chunk, got + [''] * len(chunk)):
            e = reference(*c)
            if g.strip() != e:
                fails.append({'case': [hx(c[0]), hx(c[1]), hx(c[2]), hx(c[3])] + list(c[4:]),
                              'expected': e, 'got': g.strip()})
    print(json.dumps({'passed': not fails, 'seed': seed, 'vectors': len(vec),
                      'cases': len(todo), 'seconds': round(time.time() - t0, 1),
                      'failures': fails[:20]}, indent=1))
    return 0 if not fails else 1


if __name__ == '__main__':
    sys.exit(main())
