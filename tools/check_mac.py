#!/usr/bin/env python3
"""HMAC-SHA256 and HKDF-SHA256 (src/crypto/mac.bend, src/crypto/kdf.bend)
against the RFC vectors and against Python's hmac/hashlib and the
`cryptography` package.

  python3 tools/check_mac.py            [-n CASES] [--seed S]

1. Builds and runs tests/crypto/mac/main.bend (RFC 4231 cases 1-7, verify)
   and tests/crypto/kdf/main.bend (RFC 5869 A.1-A.3, the length limit):
   every line must be "ok ...", with the expected number of checks. The RFC
   constants those files embed are re-derived here from hmac/cryptography.
2. Differential: builds tests/crypto/mac/diff.bend and feeds it random
   records (sign, verify, hkdf, expand, extract) whose lengths are drawn
   around the SHA-256 block boundaries (keys of 63/64/65 bytes and longer,
   messages around 55/56/64 bytes, outputs around 32-byte blocks and the
   8160-byte limit); every answer is compared with the reference.

Prints a JSON verdict; exit 1 on any failure.
"""
import argparse, hashlib, hmac, json, os, random, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from toolchain import BEND, ENV  # noqa: E402

OUT = ROOT / 'build' / 'crypto-mac'

RFC4231 = [  # (key, data, tag or truncated tag)
    (b'\x0b' * 20, b'Hi There', 'b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7'),
    (b'Jefe', b'what do ya want for nothing?', '5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843'),
    (b'\xaa' * 20, b'\xdd' * 50, '773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe'),
    (bytes(range(1, 26)), b'\xcd' * 50, '82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b'),
    (b'\x0c' * 20, b'Test With Truncation', 'a3b6167473100ee06e0c796c2955552b'),
    (b'\xaa' * 131, b'Test Using Larger Than Block-Size Key - Hash Key First', '60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54'),
    (b'\xaa' * 131, b'This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.', '9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2'),
]

RFC5869 = [  # (ikm, salt, info, L, prk, okm)
    (b'\x0b' * 22, bytes(range(0, 13)), bytes(range(0xf0, 0xfa)), 42,
     '077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5',
     '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865'),
    (bytes(range(0, 0x50)), bytes(range(0x60, 0xb0)), bytes(range(0xb0, 0x100)), 82,
     '06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244',
     'b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87'),
    (b'\x0b' * 22, b'', b'', 42,
     '19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04',
     '8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8'),
]

FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print('FAIL', msg, file=sys.stderr)


def h(key, msg):
    return hmac.new(key, msg, hashlib.sha256).digest()


def expand_rfc(prk, info, n):
    """RFC 5869 2.3, written from the RFC on Python's hmac."""
    if n > 255 * 32:
        return None
    t, okm, i = b'', b'', 1
    while len(okm) < n:
        t = h(prk, t + info + bytes([i]))
        okm += t
        i += 1
    return okm[:n]


def expand_crypto(prk, info, n):
    """The cryptography package's HKDFExpand (it takes 1 <= n <= 8160)."""
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.hkdf import HKDFExpand
    return HKDFExpand(algorithm=hashes.SHA256(), length=n, info=info).derive(prk)


def hkdf_crypto(salt, ikm, info, n):
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    return HKDF(algorithm=hashes.SHA256(), length=n, salt=salt or None, info=info).derive(ikm)


def hmac_crypto(key, msg):
    from cryptography.hazmat.primitives import hashes, hmac as chmac
    m = chmac.HMAC(key, hashes.SHA256())
    m.update(msg)
    return m.finalize()


def build(src, out):
    OUT.mkdir(parents=True, exist_ok=True)
    if out.exists():
        out.unlink()
    p = subprocess.run([BEND, src, '-o', str(out)], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=1800)
    if not out.exists():
        raise SystemExit('%s did not build:\n%s%s' % (src, p.stdout[-2000:], p.stderr[-2000:]))


def rfc_constants():
    """The RFC tables above (and embedded in the Bend tests) against the libraries."""
    n = 0
    for key, data, tag in RFC4231:
        for got in (h(key, data).hex(), hmac_crypto(key, data).hex()):
            if got[:len(tag)] != tag:
                fail('RFC 4231 constant %r does not match the library' % tag)
            n += 1
    for ikm, salt, info, L, prk, okm in RFC5869:
        if h(salt, ikm).hex() != prk:
            fail('RFC 5869 PRK constant %s' % prk)
        if expand_rfc(bytes.fromhex(prk), info, L).hex() != okm or hkdf_crypto(salt, ikm, info, L).hex() != okm:
            fail('RFC 5869 OKM constant %s' % okm)
        n += 3
    return n


def run_vectors(name, want_checks):
    binary = OUT / name
    build('tests/crypto/%s/main.bend' % name, binary)
    p = subprocess.run([str(binary)], env=ENV, capture_output=True, text=True, timeout=600)
    lines = [l for l in p.stdout.splitlines() if l.strip()]
    bad = [l for l in lines if not l.startswith('ok ')]
    if p.returncode or bad or len(lines) != want_checks:
        fail('%s vectors: exit %d, %d lines (want %d), bad: %s' % (name, p.returncode, len(lines), want_checks, bad[:5]))
    return len(lines) - len(bad)


def field(b):
    return struct.pack('<I', len(b)) + b


def lengths(rng, edges, hi):
    r = rng.random()
    if r < 0.4:
        return rng.choice(edges)
    if r < 0.9:
        return rng.randrange(0, hi)
    return rng.randrange(0, 4 * hi)


KEY_EDGES = [0, 1, 20, 31, 32, 33, 63, 64, 65, 100, 128, 129, 131, 200]
MSG_EDGES = [0, 1, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 191, 192]
OUT_EDGES = [0, 1, 31, 32, 33, 63, 64, 65, 95, 96, 97, 255, 256, 8159, 8160, 8161, 8192, 70000]


def differential(n, seed):
    rng = random.Random('mac-kdf-%d' % seed)
    recs, want, kinds = [], [], {}
    for _ in range(n):
        op = rng.choice([0, 0, 1, 1, 2, 2, 3, 4])
        if op == 0:
            key = rng.randbytes(lengths(rng, KEY_EDGES, 150))
            msg = rng.randbytes(lengths(rng, MSG_EDGES, 200))
            recs.append(bytes([0]) + field(key) + field(msg))
            tag = h(key, msg)
            if tag != hmac_crypto(key, msg):
                fail('hmac and cryptography disagree')
            want.append(tag.hex())
        elif op == 1:
            key = rng.randbytes(lengths(rng, KEY_EDGES, 150))
            msg = rng.randbytes(lengths(rng, MSG_EDGES, 200))
            tag = h(key, msg)
            mode = rng.randrange(6)
            if mode == 1:      # one flipped bit
                i = rng.randrange(32)
                tag = tag[:i] + bytes([tag[i] ^ (1 << rng.randrange(8))]) + tag[i + 1:]
            elif mode == 2:    # truncated
                tag = tag[:rng.randrange(32)]
            elif mode == 3:    # extended
                tag = tag + rng.randbytes(rng.randrange(1, 4))
            elif mode == 4:    # random
                tag = rng.randbytes(32)
            recs.append(bytes([1]) + field(key) + field(msg) + field(tag))
            want.append('true' if hmac.compare_digest(tag, h(key, msg)) else 'false')
        elif op in (2, 3):
            L = lengths(rng, OUT_EDGES, 300)
            info = rng.randbytes(lengths(rng, [0, 1, 10, 64, 80], 100))
            if op == 2:
                salt = rng.randbytes(lengths(rng, [0, 13, 32, 64, 65, 80], 100))
                ikm = rng.randbytes(lengths(rng, [0, 1, 22, 64, 80], 120))
                prk = h(salt, ikm)
                recs.append(bytes([2]) + field(salt) + field(ikm) + field(info) + struct.pack('<I', L))
            else:
                prk = rng.randbytes(lengths(rng, [0, 16, 31, 32, 33, 64, 65], 100))
                recs.append(bytes([3]) + field(prk) + field(info) + struct.pack('<I', L))
            okm = expand_rfc(prk, info, L)
            if okm is not None and 1 <= L:
                ref = hkdf_crypto(salt, ikm, info, L) if op == 2 else expand_crypto(prk, info, L)
                if ref != okm:
                    fail('RFC reference and cryptography disagree (op %d, L %d)' % (op, L))
            want.append('LengthTooLarge' if okm is None else okm.hex())
        else:
            salt = rng.randbytes(lengths(rng, [0, 13, 32, 64, 65], 100))
            ikm = rng.randbytes(lengths(rng, [0, 22, 64, 80], 120))
            recs.append(bytes([4]) + field(salt) + field(ikm))
            want.append(h(salt, ikm).hex())
        kinds[op] = kinds.get(op, 0) + 1
    driver = OUT / 'diff'
    build('tests/crypto/mac/diff.bend', driver)
    inp = OUT / 'diff.in'
    inp.write_bytes(b''.join(recs))
    p = subprocess.run([str(driver)], env={**ENV, 'FUZZ_INPUT': str(inp), 'FUZZ_COUNT': str(len(recs))},
                       capture_output=True, text=True, timeout=3600)
    got = p.stdout.split('\n')[:len(recs)]
    if p.returncode or len(got) != len(recs):
        fail('diff driver: exit %d, %d of %d answers: %s' % (p.returncode, len(got), len(recs), p.stderr[-500:]))
        return 0, kinds
    bad = 0
    for i, (g, w) in enumerate(zip(got, want)):
        if g != w:
            bad += 1
            if bad <= 5:
                fail('diff case %d (op %d): got %s want %s' % (i, recs[i][0], g[:40], w[:40]))
    inp.unlink()
    return len(recs) - bad, kinds


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('-n', type=int, default=3000)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    consts = rfc_constants()
    mac_ok = run_vectors('mac', 27)
    kdf_ok = run_vectors('kdf', 14)
    diff_ok, kinds = differential(a.n, a.seed)
    names = {0: 'sign', 1: 'verify', 2: 'hkdf', 3: 'expand', 4: 'extract'}
    verdict = {'rfc_constants_checked': consts, 'rfc4231_checks_passed': mac_ok, 'rfc5869_checks_passed': kdf_ok,
               'differential_passed': diff_ok, 'differential_cases': a.n, 'seed': a.seed,
               'differential_ops': {names[k]: v for k, v in sorted(kinds.items())},
               'failures': FAILURES, 'ok': not FAILURES}
    print(json.dumps(verdict, indent=1))
    return 0 if not FAILURES else 1


if __name__ == '__main__':
    sys.exit(main())
