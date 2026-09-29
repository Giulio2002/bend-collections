#!/usr/bin/env python3
"""Vectors and a differential test for X25519, the key exchange and Ed25519.

build/crypto/c25519 (tests/crypto/curve25519/main.bend) is run on
  - RFC 7748 section 5.2 (two scalar/u pairs, 1 and 1000 iterations) and
    section 6.1 (the Diffie-Hellman example),
  - RFC 8032 section 7.1 (TEST 1, 2, 3, 1024, SHA(abc)),
  - random keys and messages against the server's `cryptography` (X25519,
    Ed25519): public keys, shared secrets, signatures, verification of
    valid, tampered and non-canonical (S + L) signatures,
  - malformed input (wrong lengths, bytes >= 256): None / false.
The driver is compiled first (bend, or $BEND). Prints a JSON verdict; exit
status 1 on any mismatch.
"""
import json, os, random, shutil, subprocess, sys
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey
from cryptography.hazmat.primitives import serialization

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / 'build/crypto/c25519'
L = 2 ** 252 + 27742317777372353535851937790883648493
RAW = serialization.Encoding.Raw, serialization.PublicFormat.Raw

RFC7748 = [
    ('a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4',
     'e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c',
     'c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552'),
    ('4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d',
     'e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493',
     '95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957'),
]
ITER = [(1, '422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079'),
        (1000, '684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51')]
ALICE = ('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a',
         '8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a')
BOB = ('5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb',
       'de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f')
DH = '4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742'

RFC8032 = [
    ('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
     'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a', '',
     'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b'),
    ('4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
     '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c', '72',
     '92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00'),
    ('c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7',
     'fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025', 'af82',
     '6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a'),
]


def cases(rng):
    for k, u, out in RFC7748:
        yield 'x:%s:%s' % (k, u), out
    for n, out in ITER:
        yield 'iter:%d' % n, out
    for sk, pk in (ALICE, BOB):
        yield 'kpk:%s' % sk, pk
    yield 'ss:%s:%s' % (ALICE[0], BOB[1]), DH
    yield 'ss:%s:%s' % (BOB[0], ALICE[1]), DH
    for sk, pk, m, sig in RFC8032:
        yield 'epk:%s' % sk, pk
        yield 'esig:%s:%s' % (sk, m), sig
        yield 'ever:%s:%s:%s' % (pk, m, sig), 'true'
    for i in range(24):
        a, b = rng.randbytes(32), rng.randbytes(32)
        pa = X25519PrivateKey.from_private_bytes(a)
        pb = X25519PrivateKey.from_private_bytes(b)
        pub_b = pb.public_key().public_bytes(*RAW)
        yield 'kpk:%s' % a.hex(), pa.public_key().public_bytes(*RAW).hex()
        yield 'ss:%s:%s' % (a.hex(), pub_b.hex()), pa.exchange(X25519PublicKey.from_public_bytes(pub_b)).hex()
        u = rng.randbytes(32)  # arbitrary u, including non-canonical ones (bit 255, >= p)
        want = X25519PrivateKey.from_private_bytes(a).exchange(X25519PublicKey.from_public_bytes(u)).hex() if i % 3 else None
        if want is not None:
            yield 'x:%s:%s' % (a.hex(), u.hex()), want
    # small-order point u = 0 gives the all-zero secret: rejected
    yield 'ss:%s:%s' % ('11' * 32, '00' * 32), 'None'
    yield 'x:%s:%s' % ('11' * 32, '00' * 32), '00' * 32
    for i in range(16):
        seed = rng.randbytes(32)
        msg = rng.randbytes(rng.choice([0, 1, 31, 64, 111, 112, 113, 128, 200]))
        k = Ed25519PrivateKey.from_private_bytes(seed)
        pk = k.public_key().public_bytes(*RAW)
        sig = k.sign(msg)
        yield 'epk:%s' % seed.hex(), pk.hex()
        yield 'esig:%s:%s' % (seed.hex(), msg.hex()), sig.hex()
        yield 'ever:%s:%s:%s' % (pk.hex(), msg.hex(), sig.hex()), 'true'
        bad = bytearray(sig); bad[rng.randrange(64)] ^= 1 << rng.randrange(8)
        ok = True
        try:
            Ed25519PublicKey.from_public_bytes(pk).verify(bytes(bad), msg)
        except Exception:
            ok = False
        yield 'ever:%s:%s:%s' % (pk.hex(), msg.hex(), bytes(bad).hex()), 'true' if ok else 'false'
        yield 'ever:%s:%s:%s' % (pk.hex(), (msg + b'x').hex(), sig.hex()), 'false'
        s = int.from_bytes(sig[32:], 'little') + L
        if s < 2 ** 256:
            yield 'ever:%s:%s:%s' % (pk.hex(), msg.hex(), (sig[:32] + s.to_bytes(32, 'little')).hex()), 'false'
    # malformed input
    yield 'x:%s:%s' % ('11' * 31, '09' + '00' * 31), 'None'
    yield 'kpk:%s' % ('11' * 33), 'None'
    yield 'epk:%s' % ('11' * 31), 'None'
    yield 'esig:%s:00' % ('11' * 33), 'None'
    yield 'ever:%s:00:%s' % (RFC8032[0][1], '00' * 63), 'false'
    yield 'ever:%s:00:%s' % ('00' * 31, RFC8032[0][3]), 'false'


def build():
    bend = os.environ.get('BEND', shutil.which('bend') or 'bend')
    BIN.parent.mkdir(parents=True, exist_ok=True)
    b = subprocess.run([bend, 'tests/crypto/curve25519/main.bend', '-o', str(BIN.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True, timeout=3600)
    if b.returncode != 0 or not BIN.exists():
        print(json.dumps({'passed': False, 'build': (b.stdout + b.stderr)[-2000:]}, indent=1))
        return False
    return True


def main():
    if not build():
        return 1
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 25519)
    todo = list(cases(rng))
    fails = []
    for i in range(0, len(todo), 40):
        chunk = todo[i:i + 40]
        p = subprocess.run([str(BIN)] + [t for t, _ in chunk], capture_output=True, text=True, timeout=3600)
        got = p.stdout.split('\n')
        for (tok, want), g in zip(chunk, got + [''] * len(chunk)):
            if g.strip() != want:
                fails.append({'case': tok[:80], 'expected': want, 'got': g.strip()})
    print(json.dumps({'passed': not fails, 'cases': len(todo), 'failures': fails[:20]}, indent=1))
    return 0 if not fails else 1


if __name__ == '__main__':
    sys.exit(main())
