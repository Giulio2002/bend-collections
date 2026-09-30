"""The random group of benchmarks/crypto_suite.py: math/random (Go's
math/rand/v2 ChaCha8 and PCG, uint_below, float64, shuffle) and crypto/random
bytes, against benchmarks/native/gorand.h (Go transcribed to C).

The Python checker below is a mirror of Go's math/rand/v2 and of the C2SP
chacha8rand pseudocode (copied from tools/check_random.py, written from the
specification). Check gorand.h itself against Go's vectors with

  cc -O2 -Ibenchmarks/native -o build/gorand_check benchmarks/native/gorand_check.c
  build/gorand_check > build/gorand.txt
  python3 benchmarks/suite_cases_random.py --check build/gorand.txt
"""
import struct, sys
from crypto_suite import pattern

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
N = 'benchmarks/native/'
C_BUILD = {'random': ([N + 'suite_random.c'], [])}


# ---- the mirror (tools/check_random.py)
def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & M32


def quarter(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & M32; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & M32; s[b] = rotl(s[b] ^ s[c], 7)


CONSTANTS = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574]
QS = [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
      (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]


def chacha8_block(key, counter):
    init = CONSTANTS + list(key) + [counter, 0, 0, 0]
    s = init[:]
    for _ in range(4):
        for q in QS:
            quarter(s, *q)
    return [(s[i] + init[i]) & M32 for i in range(16)]


def c2sp_iteration(key):
    stream = []
    for i in range(16):
        w = chacha8_block(key, i)
        for j in range(4):
            w[j] = (w[j] - CONSTANTS[j]) & M32
        w[12] = (w[12] - i) & M32
        stream += w
    out = []
    for g in range(4):
        blocks = stream[64 * g:64 * g + 64]
        for i in range(16):
            for b in range(4):
                out.append(blocks[16 * b + i])
    return out[:248], out[248:]


class ChaCha8:
    def __init__(self, seed_bytes):
        self.key = [int.from_bytes(seed_bytes[4 * i:4 * i + 4], 'little') for i in range(8)]
        self.buf, self.pos = [], 0

    def next(self):
        if self.pos == len(self.buf):
            out, self.key = c2sp_iteration(self.key)
            self.buf, self.pos = [out[2 * i] | out[2 * i + 1] << 32 for i in range(124)], 0
        self.pos += 1
        return self.buf[self.pos - 1]


class PCG:
    MUL = (2549297995355413924 << 64) | 4865540595714422341
    INC = (6364136223846793005 << 64) | 1442695040888963407

    def __init__(self, s1, s2):
        self.state = (s1 << 64) | s2

    def next(self):
        self.state = (self.state * self.MUL + self.INC) & ((1 << 128) - 1)
        hi, lo = self.state >> 64, self.state & M64
        hi ^= hi >> 32
        hi = (hi * 0xda942042e4dd58b5) & M64
        hi ^= hi >> 48
        return (hi * (lo | 1)) & M64


def uint64n(src, n):
    if n & (n - 1) & M64 == 0:
        return src.next() & ((n - 1) & M64)
    m = src.next() * n
    hi, lo = m >> 64, m & M64
    if lo < n:
        thresh = ((1 << 64) - n) % n
        while lo < thresh:
            m = src.next() * n
            hi, lo = m >> 64, m & M64
    return hi


def float64_bits(src):
    return struct.unpack('<Q', struct.pack('<d', (src.next() & ((1 << 53) - 1)) / 2.0 ** 53))[0]


# ---- the checksums (suite_randlib.bend)
def fold_u64s(xs):
    """every value's 8 LE bytes, last value first"""
    c = 0
    for x in reversed(xs):
        for j in range(8):
            c = (c * 31 + ((x >> (8 * j)) & 255)) & M32
    return c


def seed():
    return pattern(32, 7, 1)


def py_draws(kind):
    def f(msgs, row):
        n = row['count']
        if kind == 'pcg':
            src = PCG(1, 2)
            return fold_u64s([src.next() for _ in range(n)])
        src = ChaCha8(seed())
        if kind == 'u64':
            return fold_u64s([src.next() for _ in range(n)])
        if kind == 'below':
            b = (1 << 63) + 1 if row['param'] else 1000000007
            return fold_u64s([uint64n(src, b) for _ in range(n)])
        return fold_u64s([float64_bits(src) for _ in range(n)])
    return f


def py_shuffle(msgs, row):
    src, xs = ChaCha8(seed()), list(range(row['size']))
    for _ in range(row['count']):
        for i in range(len(xs) - 1, 0, -1):
            j = uint64n(src, i + 1)
            xs[i], xs[j] = xs[j], xs[i]
    c = 0
    for x in xs:
        for j in range(4):
            c = (c * 31 + ((x >> (8 * j)) & 255)) & M32
    return c


def py_bytes(msgs, row):
    src, pend, reads = ChaCha8(seed()), [], []
    for _ in range(row['count']):
        out = []
        while len(out) < row['size']:
            if not pend:
                pend = list(src.next().to_bytes(8, 'little'))
            out.append(pend.pop(0))
        reads.append(out)
    c = 0
    for r in reversed(reads):
        for b in r:
            c = (c * 31 + b) & M32
    return c


def case(name, bend, op, rows, py):
    return dict(name=name, bend=bend, c='random', c_build=C_BUILD, input=False,
                rows=[dict(r, env={'BENCH_OP': str(op)}) for r in rows], py=py)


D = 1 << 21
RANDOM = [
    case('chacha8_uint64', 'chacha8_u64', 0, [dict(size=D, count=D, label='%d draws' % D)], py_draws('u64')),
    case('pcg_uint64', 'pcg_u64', 1, [dict(size=2 * D, count=2 * D, label='%d draws' % (2 * D))], py_draws('pcg')),
    case('uint_below', 'uint_below', 2, [dict(size=D, count=D, param=0, label='n = 1000000007'),
                                         dict(size=D // 2, count=D // 2, param=1, label='n = 2^63 + 1')], py_draws('below')),
    case('float64', 'float64', 3, [dict(size=D, count=D, label='%d draws' % D)], py_draws('f64')),
    case('shuffle', 'shuffle', 4, [dict(size=1000, count=2000, label='1000 items'),
                                   dict(size=10000, count=200, label='10000 items'),
                                   dict(size=100000, count=20, label='100000 items')], py_shuffle),
    case('crypto_random_bytes', 'crandom', 5, [dict(size=s, count=c) for s, c in
                                               [(64, 65536), (1024, 4096), (65536, 64), (1048576, 4)]], py_bytes),
]

GROUPS = {'random': RANDOM}


def check(path):
    sys.path.insert(0, 'tools')
    import hashlib
    import check_random as G
    lines = open(path).read().split('\n')
    c8 = [int(l.split()[1], 16) for l in lines if l.startswith('c8 ')]
    pcg = [int(l.split()[1], 16) for l in lines if l.startswith('pcg ')]
    reads = [bytes.fromhex(l.split()[1]) for l in lines if l.startswith('read')]
    ok = c8 == G.CHACHA8_OUTPUT and pcg == G.PCG_12 and len(reads) == 4 and \
        all(hashlib.sha256(r).hexdigest() == G.CHACHA8_HASH for r in reads)
    print('gorand.h vs Go vectors:', 'OK' if ok else 'MISMATCH',
          '(chacha8output %s, TestPCG %s, chacha8hash %s)' % (c8 == G.CHACHA8_OUTPUT, pcg == G.PCG_12,
                                                             [hashlib.sha256(r).hexdigest() == G.CHACHA8_HASH for r in reads]))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(check(sys.argv[2]) if sys.argv[1:2] == ['--check'] else 2)
