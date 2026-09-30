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
PWBIN = ROOT / 'build/argon2/password'
PWSRC = [ROOT / 'tests/crypto/password/main.bend', ROOT / 'src/crypto/password.bend', ROOT / 'src/crypto/subtle.bend'] + SRC[1:]
BEND = os.environ.get('BEND', 'bend')
BATCH = 40


def build(binary=BIN, driver='tests/crypto/argon2/main.bend', srcs=SRC):
    if binary.exists() and all(binary.stat().st_mtime > f.stat().st_mtime for f in srcs):
        return True, ''
    binary.parent.mkdir(parents=True, exist_ok=True)
    p = subprocess.run([BEND, driver, '-o', str(binary)], cwd=ROOT,
                       capture_output=True, text=True, timeout=1800)
    return binary.exists(), p.stdout + p.stderr


def run_pw(toks):
    out = []
    for i in range(0, len(toks), BATCH):
        p = subprocess.run([str(PWBIN)] + toks[i:i + BATCH], capture_output=True, text=True, timeout=1800)
        got = p.stdout.split('\n')
        out += (got + [''] * BATCH)[:len(toks[i:i + BATCH])]
    return [g.strip() for g in out]


def password_cases(rng, fails):
    """hash_password / verify_password / needs_rehash against argon2-cffi's PasswordHasher."""
    from argon2 import PasswordHasher, Parameters, Type as T
    from argon2.exceptions import VerifyMismatchError
    from argon2 import extract_parameters
    n = 0
    params = []
    for _ in range(40):
        p = rng.choice([1, 1, 2])
        m = rng.choice([8 * p, 16, 32, 64, rng.randrange(8 * p, 100)])
        m = max(m, 8 * p)
        t = rng.choice([1, 2, 3])
        tag = rng.choice([4, 16, 32, 33, 64, 65])
        pw = rbytes(rng, rng.choice([0, 1, 8, 20, 64]))
        salt = rbytes(rng, rng.choice([8, 16, 32]))
        params.append((pw, salt, m, t, p, tag))
    # ours -> argon2-cffi
    hashed = run_pw(['hash:%s:%s:%d:%d:%d:%d' % (hx(pw), hx(salt), m, t, p, tag) for pw, salt, m, t, p, tag in params])
    for (pw, salt, m, t, p, tag), h in zip(params, hashed):
        n += 1
        ref = '$argon2id$v=19$m=%d,t=%d,p=%d$%s$%s' % (m, t, p, b64(salt), b64(hash_secret_raw(pw, salt, t, m, p, tag, Type.ID, 19)))
        if h != ref:
            fails.append({'password_hash': [hx(pw), hx(salt), m, t, p, tag], 'expected': ref, 'got': h})
            continue
        try:
            PasswordHasher().verify(h, pw)
        except Exception as e:
            fails.append({'cffi_rejects_ours': h, 'error': repr(e)})
    # argon2-cffi -> ours, right and wrong passwords
    toks, want = [], []
    for pw, salt, m, t, p, tag in params:
        ph = PasswordHasher(time_cost=t, memory_cost=m, parallelism=p, hash_len=tag, salt_len=len(salt))
        h = ph.hash(pw)
        toks += ['verify:%s:%s' % (hx(pw), h), 'verify:%s:%s' % (hx(pw + b'x'), h)]
        want += ['true', 'false']
        # a flipped tag byte is rejected
        parts = h.split('$')
        raw = bytearray(b64d(parts[-1]))
        raw[0] ^= 1
        toks.append('verify:%s:%s' % (hx(pw), '$'.join(parts[:-1] + [b64(bytes(raw))])))
        want.append('false')
        # needs_rehash: the same parameters, then each one changed
        toks.append('rehash:%s:%d:%d:%d:%d:%d' % (h, m, t, p, tag, len(salt)))
        want.append('false')
        for dm, dt, dp, dtag, dsalt in [(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 0, 0), (0, 0, 0, 1, 0), (0, 0, 0, 0, 1)]:
            toks.append('rehash:%s:%d:%d:%d:%d:%d' % (h, m + dm, t + dt, p + dp, tag + dtag, len(salt) + dsalt))
            want.append('true')
    # malformed or foreign strings: never verified, always rehashed
    bad = ['', '$argon2i$v=19$m=64,t=2,p=1$c29tZXNhbHQ$FqGkmHNGCd0BRW2kBt6fPZ2pPmyGwwChL8FGUhTOSSI',
           '$argon2id$v=16$m=64,t=2,p=1$c29tZXNhbHQ$FqGkmHNGCd0BRW2kBt6fPZ2pPmyGwwChL8FGUhTOSSI',
           '$argon2id$v=19$m=64,t=2,p=1$c29tZXNhbHQ', '$argon2id$v=19$m=64,t=2$c29tZXNhbHQ$FqGk',
           '$argon2id$v=19$m=64,t=2,p=1$c29tZXNhbHQ$FqGkmHNGCd0BRW2kBt6fPZ2pPmyGwwChL8FGUhTOSSJ',
           '$argon2id$v=19$m=,t=2,p=1$c29tZXNhbHQ$FqGkmHNGCd0BRW2kBt6fPZ2pPmyGwwChL8FGUhTOSSI']
    for b in bad:
        toks += ['verify:70617373776f7264:%s' % b, 'rehash:%s:64:2:1:32:8' % b]
        want += ['false', 'true']
    got = run_pw(toks)
    for tk, w, g in zip(toks, want, got):
        n += 1
        if w != g:
            fails.append({'password': tk, 'expected': w, 'got': g})
    # the OS-salted variant: fresh 16-byte salts, verified by argon2-cffi
    got = run_pw(['os:70617373776f7264:32:1:1:32:16'] * 4)
    salts = set()
    for g in got:
        n += 1
        try:
            PasswordHasher().verify(g, b'password')
            salts.add(g.split('$')[4])
            if len(b64d(g.split('$')[4])) != 16:
                fails.append({'os_salt_length': g})
        except Exception as e:
            fails.append({'os': g, 'error': repr(e)})
    if len(salts) != 4:
        fails.append({'os_salts_repeat': sorted(salts)})
    return n


def b64(b):
    import base64
    return base64.b64encode(b).decode().rstrip('=')


def b64d(s):
    import base64
    return base64.b64decode(s + '=' * (-len(s) % 4))


def hx(b):
    return b.hex() if b else '-'


def reference(pw, salt, key, ad, t, m, p, tl):
    mm = 4 * p * (m // (4 * p)) if p else 0
    if not (1 <= p < 2 ** 24 and 4 <= tl and 8 * p <= m < 2 ** 32 and t >= 1 and len(salt) >= 8 and mm <= 2 ** 23):
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
            (b'pw', b'saltsalt', b'', b'', 1, 2 ** 23 + 4, 1, 32), (b'pw', b'saltsalt', b'', b'', 1, 2 ** 24 + 3, 2, 32),
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
    ok, log = build(PWBIN, 'tests/crypto/password/main.bend', PWSRC)
    if not ok:
        fails.append({'error': 'password driver build failed', 'log': log[-2000:]})
        pw_cases = 0
    else:
        pw_cases = password_cases(rng, fails)
    print(json.dumps({'passed': not fails, 'seed': seed, 'vectors': len(vec),
                      'cases': len(todo), 'password_cases': pw_cases, 'seconds': round(time.time() - t0, 1),
                      'failures': fails[:20]}, indent=1))
    return 0 if not fails else 1


if __name__ == '__main__':
    sys.exit(main())
