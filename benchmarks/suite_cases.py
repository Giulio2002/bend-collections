"""The cases of benchmarks/crypto_suite.py, by group.

A case: name, Bend driver (benchmarks/bend/suite_<bend>.bend), C binary
(built from c_build[<c>] = (sources, include dirs, defines)), optional c_alt (a
second C reference timed in the same rotation), rows (size = message bytes,
param = BENCH_PARAM, count = messages per sample, env = extra environment,
label), and py(messages, row) -> the expected checksum, where
Python has the algorithm.
"""
import hashlib, hmac
from crypto_suite import checksum, pattern

N = 'benchmarks/native/'
MONO = N + 'monocypher/'
XKCP = [N + 'xkcp/KeccakP-1600-opt64.c']
KiB, MiB = 1024, 1048576
SIZES = [64, KiB, 16 * KiB, 64 * KiB, MiB]


def rows(sizes, total, **kw):
    """one row per size, count = total bytes // size (at least 1)"""
    return [dict(size=s, count=max(1, total // s), **kw) for s in sizes]


def per_message(f):
    """f(message, row) -> the output bytes"""
    return lambda msgs, row: checksum([f(m, row) for m in msgs])


def hkdf(salt, ikm, info, n):
    prk = hmac.new(salt, ikm, hashlib.sha256).digest()
    out, t, i = b'', b'', 1
    while len(out) < n:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        out += t
        i += 1
    return out[:n]


HASHERS = [('SHA-256', hashlib.sha256), ('SHA-512', hashlib.sha512), ('SHA3-256', hashlib.sha3_256)]


def hasher_rows():
    out = []
    for algo, (title, _) in enumerate(HASHERS):
        for size in [KiB, 64 * KiB, MiB]:
            for chunk in [0, 64]:
                out.append(dict(size=size, param=chunk, count=max(1, 2 * MiB // size), env={'BENCH_ALGO': str(algo)},
                                label='%s %s %s' % (title, '%d KiB' % (size // KiB) if size < MiB else '1 MiB',
                                                    'one-shot' if not chunk else '%d B chunks' % chunk)))
    return out




HASH = [
    dict(name='sha512', bend='sha512', c='sha512', c_build={'sha512': ([N + 'suite_sha512.c', MONO + 'monocypher-ed25519.c', MONO + 'monocypher.c'], [MONO])},
         rows=rows(SIZES, 4 * MiB), py=per_message(lambda m, r: hashlib.sha512(m).digest())),
    dict(name='sha3_256', bend='sha3_256', c='sha3_256', c_build={'sha3_256': ([N + 'suite_sha3_256.c'] + XKCP, [N + 'xkcp'])},
         rows=rows(SIZES, 4 * MiB), py=per_message(lambda m, r: hashlib.sha3_256(m).digest())),
    dict(name='hasher', bend='hasher', c='hasher',
         c_build={'hasher': ([N + 'suite_hasher.c', MONO + 'monocypher-ed25519.c', MONO + 'monocypher.c'] + XKCP, [MONO, N + 'xkcp'])},
         rows=hasher_rows(), py=per_message(lambda m, r: HASHERS[int(r['env']['BENCH_ALGO'])][1](m).digest())),
    dict(name='subtle_eq', bend='subtle_eq', c='subtle_eq', c_build={'subtle_eq': ([N + 'suite_subtle_eq.c'], [])},
         rows=rows([32, KiB, 64 * KiB], 4 * MiB) + [dict(r, param=1, label=l + ' words') for r, l in zip(rows([32, KiB, 64 * KiB], 4 * MiB), ['32 B', '1 KiB', '64 KiB'])],
         py=per_message(lambda m, r: b'\x01')),
    dict(name='hmac_sha256', bend='hmac', c='hmac', c_build={'hmac': ([N + 'suite_hmac.c'], [])},
         rows=rows(SIZES, 4 * MiB), py=per_message(lambda m, r: hmac.new(pattern(32, 7, 1), m, hashlib.sha256).digest())),
    dict(name='hkdf_sha256', bend='hkdf', c='hkdf', c_build={'hkdf': ([N + 'suite_hkdf.c'], [])},
         rows=[dict(size=32, param=L, count=max(8, 256 * KiB // L), label='%d B out' % L) for L in [32, 128, KiB, 8160]],
         py=per_message(lambda m, r: hkdf(pattern(32, 5, 3), m, pattern(16, 3, 11), r['param']))),
]

GROUPS = {'hash': HASH}
# the other groups live in their own modules
import importlib
for _m in ('suite_cases_cipher', 'suite_cases_pk', 'suite_cases_random'):
    try:
        GROUPS.update(importlib.import_module(_m).GROUPS)
    except ModuleNotFoundError as e:
        if e.name != _m:
            raise
