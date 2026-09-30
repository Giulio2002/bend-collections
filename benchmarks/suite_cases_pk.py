"""The pk group of benchmarks/crypto_suite.py: X25519, Ed25519, Argon2id and,
when src/crypto/secp256k1.bend is present, secp256k1. Case format:
suite_cases.py. Counts are small: one X25519 or Ed25519 operation takes
0.1-0.6 s in Bend."""
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives.kdf.argon2 import Argon2id
from crypto_suite import ROOT, checksum, pattern
from suite_cases import per_message

N = 'benchmarks/native/'
MONO = N + 'monocypher/'
MONO_SRC = [MONO + 'monocypher.c', MONO + 'monocypher-ed25519.c']
A2 = N + 'argon2/'
A2_SRC = [A2 + f for f in ('argon2.c', 'core.c', 'ref.c', 'encoding.c', 'thread.c', 'blake2/blake2b.c')]
RAW = dict(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)


def x25519(m, r):
    peer = X25519PrivateKey.from_private_bytes(pattern(32, 9, 5)).public_key()
    return X25519PrivateKey.from_private_bytes(m).exchange(peer)


def ed_public(m, r):
    return Ed25519PrivateKey.from_private_bytes(m).public_key().public_bytes(**RAW)


def ed_sign(m, r):
    return Ed25519PrivateKey.from_private_bytes(pattern(32, 13, 7)).sign(m)


ARGON2 = {0: (3, 64), 1: (2, 19456)}


def argon2id(m, r):
    t, mem = ARGON2[r['param']]
    return Argon2id(salt=pattern(16, 11, 7), length=32, iterations=t, lanes=1, memory_cost=mem).derive(m)


PK = [
    dict(name='x25519', bend='x25519', c='x25519', c_build={'x25519': ([N + 'suite_x25519.c'] + MONO_SRC, [MONO])},
         rows=[dict(size=32, count=8, label='shared secret')], py=per_message(x25519)),
    dict(name='ed25519_keygen', bend='ed25519_keygen', c='ed25519_keygen',
         c_build={'ed25519_keygen': ([N + 'suite_ed25519_keygen.c'] + MONO_SRC, [MONO])},
         rows=[dict(size=32, count=4, label='keygen')], py=per_message(ed_public)),
    dict(name='ed25519_sign', bend='ed25519_sign', c='ed25519_sign',
         c_build={'ed25519_sign': ([N + 'suite_ed25519_sign.c'] + MONO_SRC, [MONO])},
         rows=[dict(size=64, count=2, label='sign 64 B'), dict(size=1024, count=2, label='sign 1 KiB')],
         py=per_message(ed_sign)),
    dict(name='ed25519_verify', bend='ed25519_verify', c='ed25519_verify',
         c_build={'ed25519_verify': ([N + 'suite_ed25519_verify.c'] + MONO_SRC, [MONO])},
         rows=[dict(size=64, count=2, label='verify 64 B'), dict(size=1024, count=2, label='verify 1 KiB')],
         py=per_message(lambda m, r: b'\x01')),
    dict(name='argon2id', bend='argon2id', c='argon2id',
         c_build={'argon2id': ([N + 'suite_argon2id.c'] + A2_SRC, [A2], ['-DARGON2_NO_THREADS'])},
         rows=[dict(size=16, param=0, count=64, label='m=64 KiB t=3 p=1'),
               dict(size=16, param=1, count=1, label='m=19 MiB t=2 p=1')],
         py=per_message(argon2id)),
]

SECP = N + 'secp256k1/'
SECP_OPS = ['ECDSA sign', 'ECDSA verify', 'ECDSA recover', 'BIP-340 sign', 'BIP-340 verify']
if (ROOT / 'src/crypto/secp256k1.bend').exists():
    # no Python check: Bend and libsecp256k1 must agree (RFC 6979 / BIP-340 are deterministic)
    PK.append(dict(name='secp256k1', bend='secp256k1', c='secp256k1',
                   c_build={'secp256k1': ([N + 'suite_secp256k1.c', SECP + 'src/secp256k1.c', SECP + 'src/precomputed_ecmult.c',
                                           SECP + 'src/precomputed_ecmult_gen.c'], [SECP + 'include', SECP + 'src'],
                                          ['-DENABLE_MODULE_RECOVERY=1', '-DENABLE_MODULE_EXTRAKEYS=1', '-DENABLE_MODULE_SCHNORRSIG=1'])},
                   rows=[dict(size=32, param=i, count=2, label=op) for i, op in enumerate(SECP_OPS)], py=None))

GROUPS = {'pk': PK}
