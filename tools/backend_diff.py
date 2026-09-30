#!/usr/bin/env python3
"""Backend differential harness: Bend against itself.

Every clause of this library is proved about the Bend source, but the
compiler that turns the source into C and JavaScript is not verified (it has
miscompiled proved code before: bendlang/bend#1142). This harness runs the
library's public functions on seeded random and edge-case inputs through
every execution path the toolchain has and fails on any disagreement:

  run   bend <driver>.bend -- <args>          check, then run (the bundled runtime)
  c     bend <driver>.bend -o <bin>; <bin>    the native C backend
  js    bend <driver>.bend -o <out>.js; node  the JavaScript backend

No reference implementation is involved, so functions without one are
covered too; tools/check_*.py remain the tests against references.

    python3 tools/backend_diff.py                 full run (about 30-60 minutes)
    python3 tools/backend_diff.py --quick         a few minutes
    python3 tools/backend_diff.py --only crypto   a group (base, containers,
                                                  math, crypto) or module names
    python3 tools/backend_diff.py --only fixed --case 3   rerun one case

Each case is one invocation of a driver on the same argv in the three paths;
the outputs must be identical. On a disagreement the first differing line is
reported with the seed, the module, the case index and a minimised argv
(a single token for stateless drivers, a shortened history for stateful ones),
and the exit status is 1. The report is build/backend_diff/report.json.

Three outcomes are counted but are not failures:
  * all-fail: every path stops with a runtime error (a Nat past 2^48 - 1,
    the runtime's documented limit);
  * resource-limit: a path overflows the machine stack on a deep recursion
    or hits the memory cap, and the others agree (the JavaScript lanes have a
    machine stack, the C runtime does not); --strict makes these failures;
  * known: a divergence recorded in docs/BACKEND_BUGS.md (the bits of an F32
    NaN, F32.show at a rounding tie, a Char outside the Unicode scalar
    values). NaN bit patterns are normalised before comparing; the other
    known divergences are kept out of the random inputs and probed by
    dedicated cases, and a probe that starts to agree is reported.
"""
import argparse
import itertools
import json
import os
import random
import resource
import struct
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tests' / 'support'))

from toolchain import BEND, ENV, VERSION  # noqa: E402

OUT = ROOT / 'build' / 'backend_diff'
NODE = os.environ.get('NODE', 'node')
PATHS = ('run', 'c', 'js')
LIM = 1 << 48          # the runtime's Nat limit
M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
STACK_MARKS = ('stack overflow', 'Maximum call stack', 'memory fault')
OOM_MARKS = ('out of memory', 'allocat', 'Allocation failed', 'reservation failed')

# ------------------------------------------------------------------ values

E32 = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 255, 256, 65535, 65536, 65537, (1 << 24) - 1, 1 << 24,
       (1 << 31) - 1, 1 << 31, (1 << 31) + 1, M32 - 1, M32, 0x55555555, 0xAAAAAAAA, 0x80000001, 0xFFFF0000,
       0x0000FFFF, 0xFFFFFFFE, 0x7FFFFFFE]
ENAT = E32 + [1 << 32, (1 << 32) + 1, (1 << 33) - 1, 1 << 40, (1 << 47) - 1, 1 << 47, (1 << 47) + 1, LIM - 2, LIM - 1]
E64 = [0, 1, 2, 65535, 65536, 65537, (1 << 31) - 1, 1 << 31, (1 << 31) + 1, M32, 1 << 32, (1 << 32) + 1,
       LIM - 1, LIM, LIM + 1, (1 << 63) - 1, 1 << 63, (1 << 63) + 1, M64 - 1, M64, 0xFFFFFFFF00000000,
       0x5555555555555555, 0xAAAAAAAAAAAAAAAA, 0x00000001FFFFFFFF, 0xFFFFFFFE00000001]


def p32(rng):
    c = rng.random()
    if c < 0.45:
        return rng.choice(E32)
    if c < 0.6:
        return rng.randrange(256)
    return rng.randrange(1 << 32)


def pnat(rng, lim=LIM):
    c = rng.random()
    if c < 0.45:
        v = rng.choice(ENAT)
    elif c < 0.6:
        v = rng.randrange(1000)
    else:
        v = rng.randrange(1 << rng.randrange(1, 49))
    return min(v, lim - 1)


def p64(rng):
    c = rng.random()
    if c < 0.45:
        return rng.choice(E64)
    if c < 0.55:
        return rng.randrange(256)
    return rng.randrange(1 << rng.randrange(1, 65))


def u64s(v):
    return '%d_%d' % (v >> 32, v & M32)


def rbytes(rng, n):
    c = rng.random()
    if c < 0.08:
        return b'\xff' * n
    if c < 0.14:
        return b'\x00' * n
    if c < 0.18:
        return bytes([0x80]) * n
    return bytes(rng.randrange(256) for _ in range(n))


def around(*blocks, top=3):
    """Lengths around the multiples of the given block sizes."""
    out = {0, 1, 2, 3, 4, 5, 7, 8, 9}
    for b in blocks:
        for k in range(1, top + 1):
            out |= {k * b - 1, k * b, k * b + 1}
        out |= {b - 9, b - 8, b - 17, b - 16}
    return sorted(x for x in out if x >= 0)


def f32r(x):
    """x rounded to binary32, as decimal text the drivers read back exactly."""
    try:
        return repr(struct.unpack('<f', struct.pack('<f', x))[0])
    except OverflowError:
        return '3.4028234663852886e+38'


def f32bits(b):
    return repr(struct.unpack('<f', struct.pack('<I', b))[0])


EF32 = ['0', '-0.0', '1', '-1', '0.5', '1.5', '2.5', '-2.5', '0.1', '0.3333333432674408', '1e-45', '1.1754943508222875e-38',
        '3.4028234663852886e+38', '-3.4028234663852886e+38', '16777216', '16777217', '2147483648', '4294967040',
        '1e10', '1e-10', '255', '256', '65535.5', '0.999999940395', '7', '3', '100', '1e20', '123456.789']


def pf32(rng):
    c = rng.random()
    if c < 0.4:
        return rng.choice(EF32)
    if c < 0.55:
        return f32bits(rng.randrange(1 << 32) & 0x7F7FFFFF | (rng.randrange(2) << 31))  # finite
    if c < 0.8:
        return f32r(rng.uniform(-10, 10))
    return f32r(rng.uniform(-1, 1) * 10.0 ** rng.randrange(-30, 30))


def show_tie(text):
    """F32.show prints 8 significant digits; is this value exactly halfway between two?
    (docs/BACKEND_BUGS.md, f32-show-tie: the paths round such a value differently.)"""
    try:
        v = struct.unpack('<f', struct.pack('<f', float(text)))[0]
    except (OverflowError, ValueError):
        return False
    if v != v or v in (float('inf'), float('-inf')):
        return False
    digits = ''.join(map(str, Decimal(v).as_tuple().digits)).strip('0')
    return len(digits) == 9 and digits[8] == '5'


def pf32_show(rng):
    while True:
        t = pf32(rng)
        if not show_tie(t):
            return t


# ------------------------------------------------------------------- cases

class Case:
    """One invocation: argv[:header] is fixed, the rest are tokens.

    kind 'tokens': every token prints one line and is independent of the
    others; kind 'history': the tokens are operations on one state; kind
    'whole': the argv is not a token list (nothing to minimise)."""

    def __init__(self, argv, kind='tokens', header=0, note='', expect=None):
        self.argv = [str(a) for a in argv]
        self.kind = kind
        self.header = header
        self.note = note
        self.expect = expect   # 'all-fail' for probes of the runtime's limits, 'known:<id>' for docs/BACKEND_BUGS.md


def batches(tokens, size, note=''):
    return [Case(tokens[i:i + size], note=note) for i in range(0, len(tokens), size)]


def lengths(rng, i, big):
    """Operation counts: empty, one, a large history, then random."""
    if i == 0:
        return 0
    if i == 1:
        return 1
    if i == 2:
        return big
    return rng.randrange(20, 300)


def weighted(rng, table):
    r = rng.random() * sum(w for w, _ in table)
    for w, f in table:
        r -= w
        if r < 0:
            return f
    return table[-1][1]


def histories(rng, n, table, header=lambda rng: [], big=1500):
    out = []
    for i in range(n):
        hd = header(rng)
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, big))]
        out.append(Case(hd + ops, kind='history', header=len(hd)))
    return out


# -------------------------------------------------------------- base shapes

def g_codegen(rng, n, oracle):
    toks = []
    per = max(1, n) * 12
    for _ in range(per):
        toks.append('0:%d:%d' % (p32(rng), p32(rng)))
        toks.append('1:%d:%d' % (p32(rng), p32(rng)))
        a = pnat(rng)
        b = rng.choice([0, 1, LIM - 1 - a, rng.randrange(LIM - a), min(pnat(rng), LIM - 1 - a)])
        toks.append('2:%d:%d' % (a, b))
        a = pnat(rng, LIM - 1)
        top = (LIM - 1) // max(a, 1)
        b = min(rng.choice([0, 1, 2, top, max(top - 1, 0), rng.randrange(top + 1), pnat(rng)]), top, LIM - 2)
        toks.append('3:%d:%d' % (a, b))
        toks.append('4:%d:%d' % (pnat(rng), rng.choice([0, 1, 2, pnat(rng), pnat(rng)])))
        e = rng.choice([0, 1, 2, 3, 5, 16, 24, 31, 32, 47, rng.randrange(48)])
        top = int(round((LIM - 1) ** (1.0 / e))) if e else LIM - 1
        while e and top ** e >= LIM:
            top -= 1
        toks.append('5:%d:%d' % (min(rng.choice([0, 1, 2, 3, top, rng.randrange(top + 1)]), top), e))
        toks.append('7:%s:%s' % (pf32(rng), pf32(rng)))
        toks.append('8:%s' % pf32_show(rng))
        toks.append('13:%d' % p32(rng))
        toks.append('14:%s' % rng.choice(['0', '0.5', '1.5', '2.5', '16777216', '2147483648', '4294967040', '255.99',
                                           f32r(rng.uniform(0, 4e9)), f32r(rng.uniform(0, 100))]))
        toks.append('11:%d:%d:%d' % (rng.randrange(0, 9), p32(rng), p32(rng)))
        toks.append('16:%d:%d' % (p32(rng), p32(rng)))
    texts = ['', '0', '1', '007', '12a', 'a', '-1', '+1', ' 1', '1 ', '4294967295', '4294967296', '281474976710655',
             '281474976710656', '99999999999999999999', '1.0', '0x10', '1e3', '٣', '00000000000000000000001']
    texts += [str(v) for v in ENAT]
    toks += ['6:%s' % t for t in texts]
    words = ['', 'a', 'A', 'abc', 'aXa', 'banana', ' pad ', 'héllo', '中文', '😀', 'a😀b', 'Zz', 'x' * 300, 'é', 'ab',
             'ba', 'aaa', '\t tab', 'ß', 'İ']
    toks += ['10:%s:%s' % (rng.choice(words), rng.choice(words)) for _ in range(per * 2)]
    toks += ['12:%d:%d' % (k, rng.choice([0, 1, max(k - 1, 0), k, k + 1, 2 * k + 3]))
             for k in [0, 1, 2, 10, 255, 256, 257, 1000, 3000] for _ in range(2)]
    rng.shuffle(toks)
    cases = batches(toks, 80)
    lib = ['9:%s:%s' % (pf32(rng), pf32(rng)) for _ in range(per * 2)]
    cases += batches(lib, 80, note='F32 library functions')
    # F32.to_u32 outside [0, 2^32) and the grammar F32.read accepts
    cases.append(Case(['14:%s' % t for t in ['-1', '-0.5', '4294967296', '1e20', '-1e20', '3.4028234663852886e+38',
                                              '-0.0', '4294967295', '4294967167']], note='F32.to_u32 out of range'))
    cases.append(Case(['7:%s:%s' % (t, u) for t, u in itertools.product(
        ['inf', '-inf', 'nan', 'Infinity', '.5', '5.', '+1', '1e5', '1E5', '1e+5', '1e-5', '0x10', '1_0', ' 1', '1 ',
         '1e', '--1', '1.2.3', '', '1e400', '1e-400', '0.0000000000000000000000000000000000000000000001'],
        ['1', '0'])], note='F32.read grammar'))
    # the runtime's Nat limit: every path must refuse, none may wrap
    for t in ['2:281474976710655:1', '3:16777216:16777216', '5:2:48', '3:4294967295:65537', '2:140737488355328:140737488355328']:
        cases.append(Case([t], note='Nat limit', expect='all-fail'))
    # F32.show at a tie in the 8th significant digit: BACKEND_BUGS.md "f32-show-tie"
    cases.append(Case(['8:%s' % t for t in ['12345.6875', '-12345.6875', '8388609.5', '0.5', '2.5', '1e21', '1e-7', '-0.0',
                                            '16777216', '0.1', '123456789', '3.4028234663852886e+38', '1e-45']],
                      note='F32.show'))
    for t in ['45566.3125', '-45566.3125', '1048576.25', '262144.625', '1024.03125']:
        cases.append(Case(['8:' + t], note='F32.show tie', expect='known:f32-show-tie'))
    # Chars: the scalar values agree; the others are BACKEND_BUGS.md "char-range"
    cases.append(Case(['15:%s' % t for t in ['65.66', '233', '128512', '1114111', '0', '55295', '57344', '65.0.66', '']],
                      note='Unicode scalar values'))
    for t in ['55296', '57343', '1114112', '3000000000', '4294967295', '65.55296.66']:
        cases.append(Case(['15:' + t], note='Char outside the Unicode scalar values', expect='known:char-range'))
    # deep non-tail recursion (the JavaScript lanes have a machine stack)
    for depth in [5000, 20000, 100000]:
        cases.append(Case(['12:%d:5' % depth], note='recursion depth %d' % depth))
    return cases


# --------------------------------------------------------------- containers

def g_stack(rng, n, oracle):
    return histories(rng, n, [(5, lambda r: 'push:%d' % pnat(r)), (2.5, lambda r: 'pop'), (1, lambda r: 'peek'),
                              (0.8, lambda r: 'len'), (0.7, lambda r: 'list')])


def g_queue(rng, n, oracle):
    return histories(rng, n, [(5, lambda r: 'enq:%d' % pnat(r)), (2.5, lambda r: 'deq'), (1, lambda r: 'peek'),
                              (0.8, lambda r: 'len'), (0.7, lambda r: 'list')])


def g_deque(rng, n, oracle):
    return histories(rng, n, [(2.5, lambda r: 'pf:%d' % pnat(r)), (2.5, lambda r: 'pb:%d' % pnat(r)),
                              (1.4, lambda r: 'popf'), (1.4, lambda r: 'popb'), (0.7, lambda r: 'peekf'),
                              (0.7, lambda r: 'peekb'), (0.6, lambda r: 'len'), (0.6, lambda r: 'list')])


def g_heap(rng, n, oracle):
    words = ['apple', 'fig', 'pear', 'kiwi', 'date', 'plum', 'banana', '', 'é', 'Apple', 'a', 'b', 'aa']
    out = []
    for i in range(n):
        kind = 'u32' if i % 3 else 'str'
        val = (lambda r: str(p32(r))) if kind == 'u32' else (lambda r: r.choice(words))
        table = [(4, lambda r: 'push:' + val(r)), (2.2, lambda r: 'pop'), (1.2, lambda r: 'peek'),
                 (0.6, lambda r: 'from:' + ','.join(val(r) for _ in range(r.randrange(1, 9)))),
                 (1, lambda r: 'len'), (1, lambda r: 'sorted')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 1200))]
        out.append(Case([kind] + ops, kind='history', header=1))
    return out


def g_priority_queue(rng, n, oracle):
    return g_heap(rng, n, oracle)


def g_dynamic_array(rng, n, oracle):
    out = []
    for i in range(n):
        kind = rng.choice(['nat', 'u32'])
        lim = rng.choice([0, 1, 3, 4, 5, 6, 8])
        val = (lambda r: str(pnat(r))) if kind == 'nat' else (lambda r: str(p32(r)))
        idx = lambda r: r.choice([0, 1, r.randrange((1 << lim) + 2), (1 << lim) - 1, 1 << lim, M32, 65536])
        table = [(3.5, lambda r: 'push:' + val(r)), (1, lambda r: 'pop'), (1, lambda r: 'get:%d' % idx(r)),
                 (1, lambda r: 'set:%d:%s' % (idx(r), val(r))), (0.7, lambda r: 'reserve:%d' % r.randrange((1 << lim) + 3)),
                 (0.3, lambda r: 'clear'), (0.8, lambda r: 'cap'), (0.8, lambda r: 'len'), (0.7, lambda r: 'to_list')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 1000))]
        out.append(Case([kind, str(lim)] + ops, kind='history', header=2))
    return out


def g_bitset(rng, n, oracle):
    out = []
    for i in range(n):
        size = rng.choice([0, 1, 7, 31, 32, 33, 63, 64, 65, 70, 255, 256, 257])
        idx = lambda r: r.choice([0, size - 1 if size else 0, size, size + 1, r.randrange(size + 2), 31, 32, M32])
        bits = lambda r: ''.join(r.choice('01') for _ in range(r.choice([size, size, size + 1, max(size - 1, 0)])))
        table = [(2.5, lambda r: 'set:%d' % idx(r)), (1.5, lambda r: 'clear:%d' % idx(r)), (1.2, lambda r: 'get:%d' % idx(r)),
                 (0.8, lambda r: 'count'), (2, lambda r: r.choice(['or', 'and', 'diff', 'xor']) + ':' + bits(r)),
                 (1, lambda r: 'len'), (1, lambda r: 'list')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 600))]
        out.append(Case([str(size)] + ops, kind='history', header=1))
    return out


def g_bitlist(rng, n, oracle):
    out = []
    for i in range(n):
        lim = rng.choice(['none', 'none', '0', '1', '3', '31', '32', '33', '64', '70'])
        idx = lambda r: r.choice([0, 1, 31, 32, 33, 63, 64, r.randrange(80), M32])
        table = [(4, lambda r: 'push:%d' % r.randrange(2)), (1, lambda r: 'pop'),
                 (1.2, lambda r: 'set:%d:%d' % (idx(r), r.randrange(2))), (1.2, lambda r: 'get:%d' % idx(r)),
                 (0.6, lambda r: 'count'), (0.6, lambda r: 'len'), (0.9, lambda r: 'list'), (0.2, lambda r: 'limit'),
                 (0.2, lambda r: 'clear')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 900))]
        out.append(Case([lim] + ops, kind='history', header=1))
    return out


def g_dll(rng, n, oracle):
    out = []
    for i in range(n):
        tag = rng.choice([1, 2, 5, 65535, M32 - 1])
        live = [0]

        def ref(r):
            return '%d:%d:%d' % (r.choice([tag, tag, tag, tag + 1]), r.randrange(0, max(1, live[0] + 2)),
                                 r.choice([0, 0, 0, 1, 2]))

        def grow(f):
            def g(r):
                live[0] += 1
                return f(r)
            return g
        table = [(2, grow(lambda r: 'pf:%d' % pnat(r))), (2, grow(lambda r: 'pb:%d' % pnat(r))),
                 (1, grow(lambda r: 'ib:%s:%d' % (ref(r), pnat(r)))), (1, grow(lambda r: 'ia:%s:%d' % (ref(r), pnat(r)))),
                 (1, lambda r: 'rm:' + ref(r)), (0.7, lambda r: 'get:' + ref(r)),
                 (0.6, lambda r: 'set:%s:%d' % (ref(r), pnat(r))), (0.5, lambda r: 'nx:' + ref(r)),
                 (0.5, lambda r: 'pv:' + ref(r)), (0.4, lambda r: 'len'), (0.4, lambda r: 'to_list')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 800))]
        out.append(Case([str(tag)] + ops, kind='history', header=1))
    return out


def g_iterator(rng, n, oracle):
    verbs = ['next', 'next', 'prev', 'prev', 'add', 'add', 'remove', 'set', 'first', 'last', 'hn', 'hp', 'pos', 'list']

    def op(r):
        v = r.choice(verbs)
        return '%s:%d' % (v, p32(r)) if v in ('add', 'set') else v
    return histories(rng, n, [(1, op)], big=900)


def g_tree_map(rng, n, oracle):
    ops_ids = list(range(32)) + list(range(33, 51))
    weights = [30, 8, 25, 2, 0.2, 3, 1, 1, 3, 3, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 5, 2, 2, 2, 3, 0.5, 1, 3, 3, 3, 2,
               2, 2] + [1] * 15
    out = []
    for i in range(n):
        kind = ['ascending', 'reverse', 'groups'][i % 3]
        steps = lengths(rng, i, 500)
        keys = rng.choice([150, 150, 8, 2000])
        args = []
        for _ in range(steps):
            op = rng.choices(ops_ids, weights=weights)[0]
            k = rng.choice([rng.randrange(keys), rng.randrange(keys), p32(rng)])
            v = rng.choice([rng.randrange(10000), p32(rng)])
            args.append('%d:%d:%d' % (op, k, v))
            if rng.random() < 0.25:
                args.append('99')
        out.append(Case([kind] + args + ['99'], kind='history', header=1))
    return out


def g_hash_table(rng, n, oracle):
    one = [chr(c) for c in range(ord('a'), ord('z') + 1)] + ['é', '中', '😀', '0', 'Z']
    multi = ['ab', 'ba', 'abc', 'key7', 'k' * 12, 'éé', '中文', 'a😀', 'aa', 'aaa', '']
    out = []
    for i in range(n):
        pool = one + multi + [''.join(rng.choice('xyz01') for _ in range(rng.randint(2, 6))) for _ in range(40)]
        if i % 4 == 3:
            pool += ['k%d' % j for j in range(600)]   # several growths
        key = lambda r: r.choice(pool)
        table = [(4, lambda r: 'set:%s:%d' % (key(r), p32(r))), (1.5, lambda r: 'get:' + key(r)),
                 (1, lambda r: 'has:' + key(r)), (1.5, lambda r: 'pop:' + key(r)), (0.8, lambda r: 'del:' + key(r)),
                 (0.7, lambda r: 'size'), (0.5, lambda r: 'keys')]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 2500))]
        out.append(Case(ops, kind='history'))
    return out


def g_lru(rng, n, oracle):
    keys = ['a', 'b', '', 'ab', 'hello', 'é', '😀', 'c', 'zz', 'k1', 'k2', 'k3', 'key-long-' * 4, 'A']
    out = []
    for i in range(n):
        cap = rng.choice([0, 1, 2, 3, 3, 8, 16, 100, 65536, M32])
        clock = [rng.choice([0, 1, M32 - 5, 1 << 31])]
        hi = rng.choice([0, 0, 1, M32])

        def tok(code, r, key=None, v=0, x=0):
            if r.random() < 0.4:
                clock[0] = (clock[0] + r.choice([1, 1, 2, 1000000, 3000000])) & M32
            return '%d:%s:%d:%d:%d:%d' % (code, r.choice(keys) if key is None else key, v, clock[0], hi, x)
        table = [(5, lambda r: tok(0, r, v=p32(r))), (3, lambda r: tok(1, r)), (1.5, lambda r: tok(2, r)),
                 (1.5, lambda r: tok(3, r)), (1.5, lambda r: tok(4, r)), (1, lambda r: tok(5, r)),
                 (0.4, lambda r: tok(6, r, x=r.choice([0, 1, 2, 3, 5, 16, M32]))),
                 (0.4, lambda r: tok(7, r, x=r.choice([0, 1, 1500000, 3000000, M32]))),
                 (0.4, lambda r: tok(8, r)), (1, lambda r: tok(9, r)), (0.6, lambda r: tok(10, r))]
        ops = [weighted(rng, table)(rng) for _ in range(lengths(rng, i, 1500))]
        out.append(Case([str(cap)] + ops, kind='history', header=1))
    return out


def g_intrusive(rng, n, oracle):
    import check_intrusive_list
    every = list(check_intrusive_list.cases())
    rng.shuffle(every)
    picked = every if n >= len(every) // 40 else every[:n * 40]
    out, batch = [], []
    for case in picked:
        if len(batch) + len(case) + 1 > 400 and batch:
            out.append(Case(batch, kind='history'))
            batch = []
        batch += ['reset'] + case
    if batch:
        out.append(Case(batch, kind='history'))
    return out[:max(n, 1)] if n < len(out) else out


# --------------------------------------------------------------------- math

def g_natural(rng, n, oracle):
    import check_math
    toks = [':'.join([op] + [str(x) for x in a]) for op, a in itertools.islice(check_math.cases(rng), n * 200)]
    edge = [0, 1, 2, 3, 255, 256, 65535, 65536, M32, 1 << 32, (1 << 32) + 1, 1 << 47, LIM - 2, LIM - 1]
    for a, b in itertools.product(edge, edge):
        toks += ['gcd:%d:%d' % (a, b), 'divmod:%d:%d' % (a, b), 'clamp:%d:%d:%d' % (a, min(a, b), max(a, b))]
        if a + b < LIM:
            toks.append('sum:%d:%d' % (a, b))
        if a * b < LIM:
            toks += ['prod:%d:%d' % (a, b), 'lcm:%d:%d' % (a, b)]
    toks += ['isqrt:%d' % a for a in edge] + ['bit_length:%d' % a for a in edge]
    toks += ['pow_mod:%d:%d:%d' % (a, rng.randrange(1000), m) for a in edge for m in [1, 2, 65535, 65536, (1 << 24) - 1]]
    rng.shuffle(toks)
    return batches(toks[:max(n, 1) * 200], 200)


INT_OPS = ['gcd', 'lcm', 'isqrt', 'iroot', 'ilog', 'factorial', 'perm', 'comb', 'pow_mod', 'mod_inverse', 'divmod',
           'bit_length', 'clamp', 'gcd_all', 'lcm_all', 'prod', 'sum', 'min', 'max', 'abs', 'sign', 'pow']
F_OPS = ['clamp', 'prod', 'sum', 'min', 'max', 'abs', 'sign', 'pow']


def rnd_int(rng, w):
    c = rng.random()
    if c < 0.2:
        return rng.choice(E32 if w == 32 else E64)
    if c < 0.4:
        return rng.randrange(0, 64)
    if c < 0.55:
        return rng.randrange(0, 1 << 16)
    if c < 0.8:
        return rng.randrange(0, 1 << w)
    if c < 0.88:
        return (1 << w) - 1 - rng.randrange(0, 4)
    if c < 0.94:
        k = rng.randrange(0, 1 << (w // 2))
        return min(max(k * k + rng.choice([-1, 0, 1]), 0), (1 << w) - 1)
    return rng.randrange(0, 1 << (w // 2 + 1))


def int_args(rng, op, w):
    r = lambda: rnd_int(rng, w)
    small = lambda: rng.randrange(0, 70)
    if op in ('isqrt', 'bit_length', 'abs', 'sign'):
        return [r()]
    if op == 'iroot':
        return [r(), rng.randrange(0, 9)]
    if op == 'ilog':
        return [r(), rng.choice([0, 1, 2, 3, 10, 16, r()])]
    if op == 'factorial':
        return [rng.choice([small(), r()])]
    if op in ('perm', 'comb'):
        k = rng.choice([small(), r(), rng.randrange(0, 1 << 12)])
        return [k, rng.choice([small(), rng.randrange(0, k + 2), r()])]
    if op == 'pow_mod':
        return [r(), r(), rng.choice([0, 1, r(), (1 << w) - rng.randrange(1, 60)])]
    if op == 'mod_inverse':
        return [r(), rng.choice([0, 1, r(), (1 << w) - 59])]
    if op == 'divmod':
        return [r(), rng.choice([0, 1, r(), small()])]
    if op == 'clamp':
        return [r(), r(), r()]
    if op in ('gcd_all', 'lcm_all', 'prod', 'sum'):
        return [rng.choice([small(), r()]) for _ in range(rng.randrange(0, 6))]
    if op == 'pow':
        return [rng.choice([small(), r()]), rng.randrange(0, 70)]
    return [r(), r()]


def f64bits(rng):
    c = rng.random()
    s = rng.randrange(2) << 63
    if c < 0.1:
        return s | rng.choice([0, 0x7FF0000000000000, 0x7FF8000000000000, 0x7FF0000000000001, 1, 0x7FEFFFFFFFFFFFFF,
                               0x0010000000000000, 0x000FFFFFFFFFFFFF, 0x3FF0000000000000, 0x433FFFFFFFFFFFFF,
                               0x41EFFFFFFFE00000, 0x41F0000000000000, 0x43F0000000000000])
    if c < 0.2:
        return s | rng.randrange(1, 1 << 52)
    if c < 0.3:
        return s | (rng.choice([1, 2, 1022, 1023, 1074, 1075, 1076, 1086, 1087, 1088, 2045, 2046]) << 52) | rng.randrange(1 << 52)
    if c < 0.45:
        return struct.unpack('>Q', struct.pack('>d', float(rng.randrange(-(1 << 20), 1 << 20))))[0]
    if c < 0.55:
        return struct.unpack('>Q', struct.pack('>d', rng.randrange(-(1 << 20), 1 << 20) + 0.5))[0]
    if c < 0.7:
        return s | (rng.randrange(1000, 1100) << 52) | rng.randrange(1 << 52)
    return rng.randrange(1 << 64)


def f64pair(rng):
    a = f64bits(rng)
    c = rng.random()
    if c < 0.15:
        return a, ((a ^ (1 << 63)) + rng.randrange(-3, 4)) & M64
    if c < 0.3:
        e = (a >> 52) & 0x7FF
        e2 = min(2046, max(0, e + rng.randrange(-60, 61)))
        return a, (rng.randrange(2) << 63) | (e2 << 52) | rng.randrange(1 << 52)
    if c < 0.4:
        return a, a ^ (rng.randrange(2) << 63)
    return a, f64bits(rng)


def g_generic(rng, n, oracle):
    toks = []
    per = max(1, n) * 3
    for ty, w in (('u32', 32), ('u64', 64)):
        enc = (lambda v: str(v)) if w == 32 else u64s
        for op in INT_OPS:
            for _ in range(per):
                a = int_args(rng, op, w)
                if op in ('pow', 'iroot'):
                    toks.append('%s:%s:%s:%d' % (ty, op, enc(a[0]), a[1]))
                else:
                    toks.append(':'.join([ty, op] + [enc(x) for x in a]))
    for op in F_OPS:
        for _ in range(per):
            k = 1 if op in ('abs', 'sign') else 3 if op == 'clamp' else rng.randrange(0, 6) if op in ('sum', 'prod') else 2
            if op == 'pow':
                toks.append('f32:pow:%s:%d' % (pf32(rng), rng.randrange(0, 40)))
                toks.append('f64:pow:%s:%d' % (u64s(f64bits(rng)), rng.randrange(0, 40)))
            else:
                toks.append(':'.join(['f32', op] + [pf32(rng) for _ in range(k)]))
                toks.append(':'.join(['f64', op] + [u64s(f64bits(rng)) for _ in range(k)]))
    rng.shuffle(toks)
    return batches(toks, 150)


def g_fixed(rng, n, oracle):
    import check_fixed
    toks = [t for t, _ in check_fixed.cases(rng, max(1, n // 2))]
    # the #1142 shape: 64-bit division and remainder around 2^32 and 2^48
    for a, b in itertools.product(E64, E64):
        for op in ('checked_div', 'checked_rem', 'wrapping_mul', 'overflowing_add', 'overflowing_sub', 'saturating_mul'):
            toks.append('u64:%s:%s:%s' % (op, u64s(a), u64s(b)))
    for a, b in itertools.product(E32, E32):
        for op in ('checked_div', 'checked_rem', 'wrapping_mul', 'checked_add', 'overflowing_sub', 'checked_mul'):
            toks.append('u32:%s:%d:%d' % (op, a, b))
    for a in ENAT:
        toks += ['nat:bit_count:%d' % a, 'nat:is_prime:%d' % min(a, M32), 'nat:egcd:%d:%d' % (a, rng.choice(ENAT))]
    rng.shuffle(toks)
    return batches(toks[:max(n, 1) * 250], 250)


F64_OPS = ['add', 'sub', 'mul', 'div', 'sqrt', 'lt', 'le', 'eq', 'neg', 'abs', 'copysign', 'of_nat']
F64X_OPS = ['trunc', 'floor', 'ceil', 'round', 'to_u64', 'to_u32', 'of_u64', 'frexp', 'ldexp', 'ulp', 'nextafter', 'fmin',
            'fmax', 'isnormal', 'issubnormal', 'is_integer', 'modf', 'fmod', 'remainder', 'isclose', 'ratio',
            'floor_u64', 'ceil_u64', 'round_u64', 'bits']


def g_f64(rng, n, oracle):
    toks = []
    for _ in range(max(1, n) * 17):
        for op in F64_OPS:
            a, b = f64pair(rng)
            toks.append('of_nat:%d' % pnat(rng) if op == 'of_nat' else '%s:%s:%s' % (op, u64s(a), u64s(b)))
    rng.shuffle(toks)
    return batches(toks, 200)


def g_f64x(rng, n, oracle):
    toks = []
    bits = lambda x: struct.unpack('>Q', struct.pack('>d', x))[0]
    for _ in range(max(1, n) * 8):
        for op in F64X_OPS:
            a, b = f64pair(rng)
            if op == 'ldexp':
                k = rng.choice([0, 1, 52, 1074, 1100, 2100, rng.randrange(0, 60), rng.randrange(0, 2200)])
                toks.append('ldexp:%s:%d:%d' % (u64s(a), rng.randrange(2), k))
            elif op == 'isclose':
                rel = rng.choice([1e-9, 0.0, 1e-3, 0.5, -1e-9, float('nan'), 1e-15])
                at = rng.choice([0.0, 1e-12, 1e-300, 1.0, -0.0, -1e-3])
                toks.append('isclose:%s:%s:%s:%s' % (u64s(a), u64s(b), u64s(bits(rel)), u64s(bits(at))))
            elif op == 'of_u64':
                toks.append('of_u64:%s:0_0:0_0:0_0' % u64s(p64(rng)))
            else:
                toks.append('%s:%s:%s:0_0:0_0' % (op, u64s(a), u64s(b)))
    rng.shuffle(toks)
    return batches(toks, 200)


def g_random(rng, n, oracle):
    import check_random as CR
    out = []
    for i in range(max(n, 1)):
        kind = ['c8', 'pcg', 'c8b', 'cr', 'crb', 'pcg'][i % 6]
        if kind in ('c8', 'cr'):
            src = kind + ':' + ':'.join(str(p32(rng)) for _ in range(8))
        elif kind in ('c8b', 'crb'):
            seed = [rng.randrange(256) for _ in range(32)]
            if i % 12 == 2:
                seed = rng.choice([seed[:31], seed + [1], [256] + seed[1:], [255] * 32, [0] * 32])
            src = kind + ':' + ':'.join(map(str, seed))
        else:
            src = 'pcg:%s:%s' % (u64s(p64(rng)), u64s(p64(rng)))
        k = rng.choice([1, 30, 120, 400])
        if kind in ('cr', 'crb'):
            toks = [rng.choice(['b:%d' % rng.randrange(0, 40), 'w:%d:%d' % (rng.randrange(0, 40), rng.randrange(0, 9)),
                                'u64', 'n:' + u64s(rng.choice(CR.EDGE + E64)), 's:%d' % rng.randrange(0, 40)])
                    for _ in range(k)]
        else:
            toks = CR.random_toks(rng, k)
            toks += ['n:' + u64s(v) for v in rng.sample(E64, 6)] + ['m:%d' % v for v in rng.sample(E32, 6) if v]
        out.append(Case([src] + toks, kind='history', header=1))
    return out


# ------------------------------------------------------------------- crypto

def hx(b):
    return bytes(b).hex()


def flip(rng, b):
    """One bit of b flipped, b truncated, or b extended."""
    b = bytearray(b)
    c = rng.random()
    if not b or c < 0.15:
        return bytes(b) + b'\x00'
    if c < 0.3:
        return bytes(b[:-1])
    b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    return bytes(b)


def arr_token(rng, code, block, big):
    n = rng.choice(around(block) + around(block, top=2) + [rng.randrange(0, big)])
    depth = 0
    while 4 << depth < n:
        depth += 1
    # tokens stay under ~16k hex digits: the drivers' own hex decoding recurses once per byte
    depth = max(0, depth + rng.choice([0, 0, 0, 1, 2, -1] if 4 << depth <= 1024 else [0, 0, 0, 1, -1]))
    ln = rng.choice([n, n, n, n, 4 << depth, (4 << depth) + 1, (4 << depth) - 1])
    data = rbytes(rng, 4 << depth)
    return '%d:%d:%d:%s' % (code, depth, ln, hx(data))


def g_hashes(rng, n, oracle):
    toks = []
    big = 1200
    for _ in range(max(1, n) * 4):
        toks.append('0:' + hx(rbytes(rng, rng.choice(around(64)))))
        toks.append('1:' + hx(rbytes(rng, rng.choice(around(128)))))
        toks.append('2:' + hx(rbytes(rng, rng.choice(around(136)))))
        alg = rng.randrange(3)
        block = [64, 128, 136][alg]
        chunks = [hx(rbytes(rng, rng.choice([0, 0, 1, block - 1, block, block + 1, rng.randrange(0, 2 * block)])))
                  for _ in range(rng.randrange(1, 6))]
        toks.append('3:%d:%s' % (alg, '.'.join(chunks)))
        a = rbytes(rng, rng.choice([0, 1, 16, 32, 33]))
        toks.append('4:%s:%s' % (hx(a), hx(rng.choice([a, flip(rng, a), rbytes(rng, len(a))]))))
        toks.append(arr_token(rng, 5, 64, big))
        toks.append(arr_token(rng, 6, 136, big))
        toks.append(arr_token(rng, 7, 128, big))
        toks.append(arr_token(rng, 8, 64, big))
        toks.append(arr_token(rng, 9, rng.choice([64, 1024]), 2100))
        key = rbytes(rng, rng.choice([0, 1, 20, 32, 63, 64, 65, 100, 131]))
        msg = rbytes(rng, rng.choice(around(64)))
        toks.append('10:%s:%s' % (hx(key), hx(msg)))
        toks.append('14:%s:%s' % (hx(key), hx(msg)))
        ln = rng.choice([0, 1, 31, 32, 33, 42, 64, 82, 255, 8160, 8161, 100000])
        toks.append('12:%s:%s:%s:%d' % (hx(key), hx(msg[:80]), hx(rbytes(rng, rng.choice([0, 1, 10, 80]))), ln))
        toks.append('13:%s:%s:%d' % (hx(rbytes(rng, 32)), hx(rbytes(rng, rng.choice([0, 10]))), rng.choice([0, 32, 33, 64, 500])))
    # HMAC verification of tags the C build produced, intact and damaged
    signs = [t for t in toks if t.startswith('10:')]
    tags = oracle(signs)
    for t, tag in zip(signs, tags):
        _, k, m = t.split(':')
        if len(tag) != 64:
            continue
        toks.append('11:%s:%s:%s' % (k, m, tag))
        toks.append('11:%s:%s:%s' % (k, m, hx(flip(rng, bytes.fromhex(tag)))))
    rng.shuffle(toks)
    cases = batches(toks, 60)
    # a long message in every list-based hash (recursion depth of the byte-list code)
    for code in (0, 1, 2):
        cases.append(Case(['%d:%s' % (code, hx(rbytes(rng, 6000)))], note='6000-byte message'))
    return cases


def g_aead(rng, n, oracle):
    toks = []
    sizes = {0: (32, 12), 1: (32, 24), 2: (16, 12), 3: (32, 12)}
    for _ in range(max(1, n) * 3):
        for alg in range(4):
            kl, nl = sizes[alg]
            if rng.random() < 0.12:
                kl = rng.choice([0, 15, 16, 17, 24, 31, 32, 33])
            if rng.random() < 0.12:
                nl = rng.choice([0, 8, 11, 12, 13, 16, 23, 24, 25])
            key, nonce = rbytes(rng, kl), rbytes(rng, nl)
            aad = rbytes(rng, rng.choice([0, 0, 1, 12, 15, 16, 17, 32, 64, 65]))
            pt = rbytes(rng, rng.choice([0, 1, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257,
                                         rng.randrange(0, 300)]))
            fields = '%d:%s:%s:%s:%s' % (alg, hx(key), hx(nonce), hx(aad), hx(pt))
            toks.append('%d:%s' % (rng.choice([2, 2, 0, 3]), fields))
            toks.append('%d:%s' % (rng.choice([1, 4]), fields))       # random data: rejected
            toks.append('11:%d:%s:%s' % (alg, hx(key), hx(nonce)))
        key = rbytes(rng, rng.choice([32, 32, 32, 31, 33, 0]))
        ctr = rng.choice([0, 1, 2, M32 - 1, M32, 1 << 31, rng.randrange(1 << 32)])
        pt = rbytes(rng, rng.choice(around(64, top=2) + [129, 191, 192, 193, 256]))
        toks.append('5:%s:%d:%s:%s' % (hx(key), ctr, hx(rbytes(rng, rng.choice([12, 12, 12, 8, 24]))), hx(pt)))
        toks.append('6:%s:%d:%s:%s' % (hx(key), ctr, hx(rbytes(rng, rng.choice([24, 24, 24, 12]))), hx(pt)))
        toks.append('7:%s:%s' % (hx(key), hx(rbytes(rng, rng.choice([16, 16, 16, 12, 17])))))
        toks.append('8:%s:%d:%s' % (hx(key), ctr, hx(rbytes(rng, 12))))
        pk = rbytes(rng, rng.choice([32, 32, 32, 32, 31, 33]))
        msg = rbytes(rng, rng.choice(around(16, top=4)))
        toks.append('9:%s:%s' % (hx(pk), hx(msg)))
        toks.append('12:%s:%s' % (hx(rbytes(rng, rng.choice([16, 24, 32, 16, 24, 32, 0, 15, 17, 33]))),
                                  hx(rbytes(rng, rng.choice([16, 16, 16, 16, 15, 17, 0])))))
    # decrypt what the C build sealed, intact and damaged; verify its Poly1305 tags
    seals = ['0:' + t.split(':', 1)[1] for t in toks if t[:2] in ('0:', '2:', '3:')][:max(1, n) * 8]
    for t, ct in zip(seals, oracle(seals)):
        if ct == 'none':
            continue
        _, alg, key, nonce, aad, _pt = t.split(':')
        toks.append('1:%s:%s:%s:%s:%s' % (alg, key, nonce, aad, ct))
        toks.append('4:%s:%s:%s:%s:%s' % (alg, key, nonce, aad, hx(flip(rng, bytes.fromhex(ct)))))
        toks.append('1:%s:%s:%s:%s:%s' % (alg, key, nonce, hx(flip(rng, bytes.fromhex(aad))), ct))
    polys = [t for t in toks if t.startswith('9:')]
    for t, tag in zip(polys, oracle(polys)):
        if tag == 'none':
            continue
        _, k, m = t.split(':')
        toks.append('10:%s:%s:%s' % (k, m, tag))
        toks.append('10:%s:%s:%s' % (k, m, hx(flip(rng, bytes.fromhex(tag)))))
    rng.shuffle(toks)
    return batches(toks, 40)


def g_argon2(rng, n, oracle):
    toks = []
    lens = [0, 1, 3, 4, 5, 8, 15, 16, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 200]
    hexd = lambda b: hx(b) if b else '-'
    for i in range(max(1, n) * 6):
        p = rng.choice([1, 1, 1, 2, 2, 3, 4])
        m = max(rng.choice([8 * p, 8 * p + 1, 8 * p + 3, 16 * p, rng.randrange(8 * p, 65), 64]), 8 * p)
        t = rng.choice([1, 1, 2, 3])
        tl = rng.choice([4, 5, 16, 31, 32, 33, 63, 64, 65, 66, 96, 100, 128])
        pw = rbytes(rng, rng.choice(lens))
        salt = rbytes(rng, rng.choice([8, 9, 16, 16, 32, 65]))
        key = rbytes(rng, rng.choice([0, 0, 0, 8, 32])) if i % 3 == 0 else b''
        ad = rbytes(rng, rng.choice([0, 0, 12, 40])) if i % 4 == 0 else b''
        toks.append(':'.join([hexd(pw), hexd(salt), hexd(key), hexd(ad), str(t), str(m), str(p), str(tl)]))
    toks += ['7077:73616c7473616c74:-:-:1:15:2:32', '7077:73686f7274:-:-:1:8:1:32', '7077:73616c7473616c74:-:-:0:8:1:32',
             '7077:73616c7473616c74:-:-:1:8:1:3', '7077:73616c7473616c74:-:-:1:8:0:32',
             '7077:73616c7473616c74:-:-:1:8388612:1:32', '70617373776f7264:73616c7473616c7473616c7473616c74:-:-:1:256:2:32']
    return batches(toks, 12)


def g_password(rng, n, oracle):
    hexd = lambda b: hx(b) if b else '-'
    hashes = []
    for _ in range(max(1, n) * 4):
        p = rng.choice([1, 1, 2])
        m = max(rng.choice([8 * p, 16, 32, 64, rng.randrange(8 * p, 100)]), 8 * p)
        t = rng.choice([1, 2, 3])
        tag = rng.choice([16, 32, 32, 64, 4, 3])
        pw = rbytes(rng, rng.choice([0, 1, 8, 32, 65]))
        salt = rbytes(rng, rng.choice([8, 16, 16, 32, 7]))
        hashes.append((pw, salt, m, t, p, tag))
    toks = ['hash:%s:%s:%d:%d:%d:%d' % (hexd(pw), hexd(salt), m, t, p, tag) for pw, salt, m, t, p, tag in hashes]
    more = []
    for (pw, salt, m, t, p, tag), phc in zip(hashes, oracle(toks)):
        if not phc.startswith('$'):
            continue
        more.append('verify:%s:%s' % (hexd(pw), phc))
        more.append('verify:%s:%s' % (hexd(flip(rng, pw)), phc))
        more.append('verify:%s:%s' % (hexd(pw), phc[:-2] + ('AA' if not phc.endswith('AA') else 'BB')))
        more.append('rehash:%s:%d:%d:%d:%d:%d' % (phc, m, t, p, tag, len(salt)))
        more.append('rehash:%s:%d:%d:%d:%d:%d' % (phc, m + rng.choice([0, 1]), t + rng.choice([0, 1]), p, tag, 16))
    more += ['verify:70:%s' % s for s in ['', '$argon2id$', '$argon2i$v=19$m=8,t=1,p=1$c2FsdHNhbHQ$AAAA', 'garbage',
                                           '$argon2id$v=19$m=8,t=1,p=1$c2FsdHNhbHQ', '$argon2id$v=16$m=8,t=1,p=1$c2FsdHNhbHQ$AAAAAA']]
    return batches(toks + more, 12)


def g_curve25519(rng, n, oracle):
    toks = []
    r32b = lambda: bytes(rng.randrange(256) for _ in range(32))
    edge = [b'\x00' * 32, b'\xff' * 32, bytes([9]) + b'\x00' * 31, bytes([1]) + b'\x00' * 31,
            bytes([0xed]) + b'\xff' * 30 + bytes([0x7f]), bytes([0xec]) + b'\xff' * 30 + bytes([0x7f])]
    seeds = []
    for i in range(max(1, n) * 2):
        a, b = r32b(), r32b()
        toks.append('kpk:' + hx(a))
        toks.append('x:%s:%s' % (hx(a), hx(rng.choice(edge + [b, b, b]))))
        toks.append('ss:%s:%s' % (hx(a), hx(rng.choice(edge + [b, b]))))
        seed = rng.choice([r32b(), r32b(), r32b(), b'\x00' * 32, b'\xff' * 32])
        msg = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 31, 64, 111, 112, 113, 128, 200])))
        seeds.append((seed, msg))
        toks += ['epk:' + hx(seed), 'cpk:' + hx(seed), 'esig:%s:%s' % (hx(seed), hx(msg)),
                 'ksig:%s:%s' % (hx(seed), hx(msg)), 'cksig:%s:%s' % (hx(seed), hx(msg))]
    toks += ['iter:1', 'iter:3', 'x:%s:%s' % ('11' * 31, '09' + '00' * 31), 'kpk:' + '11' * 33, 'epk:' + '11' * 31,
             'esig:%s:00' % ('11' * 33), 'cpk:' + '11' * 31]
    pk = oracle(['epk:' + hx(s) for s, _ in seeds])
    sg = oracle(['esig:%s:%s' % (hx(s), hx(m)) for s, m in seeds])
    for (seed, msg), p, s in zip(seeds, pk, sg):
        if len(p) != 64 or len(s) != 128:
            continue
        toks.append('ever:%s:%s:%s' % (p, hx(msg), s))
        toks.append('cver:%s:%s:%s' % (p, hx(msg), s))
        toks.append('ever:%s:%s:%s' % (p, hx(msg), hx(flip(rng, bytes.fromhex(s)))))
        toks.append('cver:%s:%s:%s' % (p, hx(msg + b'x'), s))
        toks.append('ever:%s:%s:%s' % (hx(flip(rng, bytes.fromhex(p))), hx(msg), s))
    rng.shuffle(toks)
    return batches(toks, 12)


SECP_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
SECP_P = (1 << 256) - (1 << 32) - 977


def g_secp256k1(rng, n, oracle):
    b32 = lambda v: v.to_bytes(32, 'big')
    r32b = lambda: bytes(rng.randrange(256) for _ in range(32))
    edge_sk = [b32(0), b32(1), b32(2), b32(SECP_N - 1), b32(SECP_N), b32(SECP_N + 1), b'\xff' * 32, b32(1 << 255),
               b32((SECP_N - 1) // 2), b32((SECP_N + 1) // 2)]
    edge_h = [b32(0), b32(1), b'\xff' * 32, b32(SECP_N), b32(SECP_N - 1), b32(SECP_P)]
    keys = []
    toks = []
    for i in range(max(1, n) * 2):
        sk = rng.choice(edge_sk) if rng.random() < 0.3 else r32b()
        h = rng.choice(edge_h) if rng.random() < 0.3 else r32b()
        aux = rng.choice([b32(0), r32b(), b'\xff' * 32])
        keys.append((sk, h, aux))
        toks += ['0:%s:%s' % (hx(sk), hx(h)), '4:%s:0' % hx(sk), '4:%s:1' % hx(sk), '8:' + hx(sk),
                 '6:%s:%s:%s' % (hx(sk), hx(h), hx(aux)), '10:' + hx(sk), '11:%s:%s:%s' % (hx(sk), hx(h), hx(aux))]
    toks += ['0:%s:%s' % ('11' * 31, '22' * 32), '0:%s:%s' % ('11' * 32, '22' * 31), '4:%s:0' % ('11' * 33),
             '5:' + '04' + '11' * 64, '5:' + '02' + '11' * 32, '9:' + '00' * 128, '9:' + 'ff' * 128, '9:' + '00' * 127,
             '3:%s:%s' % ('00' * 32, '00' * 65), '7:%s:%s:%s' % ('00' * 32, '00' * 32, '00' * 64)]
    sigs = oracle(['0:%s:%s' % (hx(sk), hx(h)) for sk, h, _ in keys])
    pubs = oracle(['4:%s:0' % hx(sk) for sk, _, _ in keys])
    cpubs = oracle(['4:%s:1' % hx(sk) for sk, _, _ in keys])
    xpubs = oracle(['8:' + hx(sk) for sk, _, _ in keys])
    ssigs = oracle(['6:%s:%s:%s' % (hx(sk), hx(h), hx(aux)) for sk, h, aux in keys])
    for (sk, h, aux), sig, pub, cpub, xpub, ssig in zip(keys, sigs, pubs, cpubs, xpubs, ssigs):
        if sig != 'none' and pub != 'none':
            raw = bytes.fromhex(sig)
            rs = hx(raw[:64])
            bad = hx(flip(rng, raw[:64]))
            high = hx(raw[:32] + b32(SECP_N - int.from_bytes(raw[32:64], 'big')))
            for p in (pub, cpub):
                toks += ['1:%s:%s:%s' % (p, hx(h), rs), '2:%s:%s:%s' % (p, hx(h), rs), '1:%s:%s:%s' % (p, hx(h), bad),
                         '1:%s:%s:%s' % (p, hx(h), high), '2:%s:%s:%s' % (p, hx(h), high)]
            toks += ['3:%s:%s' % (hx(h), sig), '3:%s:%s' % (hx(h), hx(flip(rng, raw))), '5:' + pub, '5:' + cpub,
                     '9:%s%s%s' % (hx(h), hx(b32(27 + raw[64])), rs), '9:%s%s%s' % (hx(h), hx(b32(raw[64])), rs),
                     '9:%s%s%s' % (hx(h), hx(b32(28 - raw[64])), rs)]
        if ssig != 'none' and xpub != 'none':
            toks += ['7:%s:%s:%s' % (xpub, hx(h), ssig), '7:%s:%s:%s' % (xpub, hx(h), hx(flip(rng, bytes.fromhex(ssig)))),
                     '7:%s:%s:%s' % (hx(flip(rng, bytes.fromhex(xpub))), hx(h), ssig)]
    rng.shuffle(toks)
    return batches(toks, 8)


# ------------------------------------------------------------------ modules

class Module:
    def __init__(self, name, group, driver, gen, quick, full, covers, nan32=None):
        self.name, self.group, self.driver, self.gen = name, group, driver, gen
        self.quick, self.full, self.covers = quick, full, covers
        self.nan32 = nan32    # tokens whose line is made of F32 bit patterns (NaNs are normalised)


T = 'tests/'
MODULES = [
    Module('codegen', 'base', T + 'backend_diff/codegen.bend', g_codegen, 2, 180,
           'Base primitives: U32, Nat, F32, String, Char, Array, List (the #1142 shapes, the 2^48 Nat limit); src/math/hash.bend, pow2.bend',
           nan32=lambda t: t.split(':')[0] in ('7', '9', '13')),
    Module('stack', 'containers', T + 'stack/main.bend', g_stack, 4, 360, 'src/containers/stack.bend'),
    Module('queue', 'containers', T + 'queue/main.bend', g_queue, 4, 360, 'src/containers/queue.bend'),
    Module('simple_queue', 'containers', T + 'simple_queue/main.bend', g_queue, 4, 240, 'src/containers/simple_queue.bend'),
    Module('deque', 'containers', T + 'deque/main.bend', g_deque, 4, 360, 'src/containers/deque.bend'),
    Module('dynamic_array', 'containers', T + 'dynamic_array/main.bend', g_dynamic_array, 4, 360, 'src/containers/dynamic_array.bend'),
    Module('binary_heap', 'containers', T + 'binary_heap/main.bend', g_heap, 4, 360, 'src/containers/binary_heap.bend'),
    Module('priority_queue', 'containers', T + 'priority_queue/main.bend', g_priority_queue, 4, 240, 'src/containers/priority_queue.bend'),
    Module('bitset', 'containers', T + 'bitset/main.bend', g_bitset, 4, 360, 'src/containers/bitset.bend'),
    Module('bitlist', 'containers', T + 'bitlist/main.bend', g_bitlist, 4, 360, 'src/containers/bitlist.bend'),
    Module('doubly_linked_list', 'containers', T + 'doubly_linked_list/main.bend', g_dll, 4, 360, 'src/containers/doubly_linked_list.bend'),
    Module('dlist_iterator', 'containers', T + 'dlist_iterator/main.bend', g_iterator, 4, 360, 'src/containers/dlist_iterator.bend'),
    Module('intrusive_list', 'containers', T + 'intrusive_doubly_linked_list/main.bend', g_intrusive, 3, 120,
           'src/containers/intrusive_doubly_linked_list.bend, intrusive_links.bend'),
    Module('tree_map', 'containers', T + 'tree_map/main.bend', g_tree_map, 4, 360, 'src/containers/balanced_search_tree.bend'),
    Module('hash_table', 'containers', T + 'hash_table/main.bend', g_hash_table, 4, 360, 'src/containers/hash_table.bend, src/math/hash.bend'),
    Module('lru', 'containers', T + 'backend_diff/lru.bend', g_lru, 4, 450, 'src/containers/lru.bend'),
    Module('natural', 'math', T + 'math/natural.bend', g_natural, 2, 90, 'src/math/natural.bend'),
    Module('generic', 'math', T + 'math/generic.bend', g_generic, 2, 120, 'src/math/generic.bend, instances.bend, num.bend (U32, U64, F32, F64)',
           nan32=lambda t: t.startswith('f32:')),
    Module('fixed', 'math', T + 'math/fixed.bend', g_fixed, 2, 120, 'src/math/fixed.bend, number.bend, u64.bend, w64.bend, pow2.bend'),
    Module('f64', 'math', T + 'math/f64.bend', g_f64, 1, 75, 'src/math/f64.bend (arithmetic, comparisons)'),
    Module('f64x', 'math', T + 'math/f64x.bend', g_f64x, 1, 75, 'src/math/f64.bend (rounding, conversions, remainders)'),
    Module('random', 'math', T + 'math/random.bend', g_random, 4, 360, 'src/math/random.bend, random/, src/crypto/random.bend'),
    Module('hashes', 'crypto', T + 'backend_diff/hashes.bend', g_hashes, 1, 180,
           'subtle, SHA-256 (list, packed), SHA-512, SHA3-256, the incremental hash facade, Keccak-256, BLAKE2b/2s/3, HMAC, HKDF'),
    Module('aead', 'crypto', T + 'backend_diff/aead.bend', g_aead, 1, 90,
           'aead.bend (ChaCha20-Poly1305, XChaCha20-Poly1305, AES-128-GCM, AES-256-GCM), chacha20, poly1305, the AES block cipher'),
    Module('argon2', 'crypto', T + 'crypto/argon2/main.bend', g_argon2, 1, 180, 'src/crypto/argon2/'),
    Module('password', 'crypto', T + 'crypto/password/main.bend', g_password, 1, 60, 'src/crypto/password.bend'),
    Module('curve25519', 'crypto', T + 'crypto/curve25519/main.bend', g_curve25519, 1, 120, 'X25519, kex.bend, Ed25519, sign.bend'),
    Module('secp256k1', 'crypto', T + 'backend_diff/secp.bend', g_secp256k1, 1, 60,
           'secp256k1.bend (ECDSA, recover, ecrecover, Ethereum addresses, BIP-340)'),
]


# ------------------------------------------------------------------ running

def limits(memory):
    def apply():
        raise_stack()
        if memory:
            try:
                resource.setrlimit(resource.RLIMIT_DATA, (memory, memory))
            except (ValueError, OSError):
                pass
    return apply


def raise_stack():
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        want = 1 << 30
        if hard != resource.RLIM_INFINITY:
            want = min(want, hard)
        if soft == resource.RLIM_INFINITY or soft >= want:
            return
        resource.setrlimit(resource.RLIMIT_STACK, (want, hard))
    except (ValueError, OSError):
        pass


class Runner:
    def __init__(self, mod, threads, timeout, memory=8 << 30):
        self.memory = memory
        self.mod = mod
        self.src = mod.driver
        self.bin = OUT / 'bin' / mod.name
        self.js = OUT / 'js' / (mod.name + '.js')
        self.threads = threads
        self.timeout = timeout

    def build(self):
        log = []
        for out in (self.bin, self.js):
            out.parent.mkdir(parents=True, exist_ok=True)
            if out.exists():
                out.unlink()
            p = subprocess.run([BEND, self.src, '-o', str(out)], cwd=ROOT, env=ENV, text=True,
                               capture_output=True, timeout=3600)
            if not out.exists():
                log.append('%s: %s' % (out.name, (p.stdout + p.stderr)[-600:]))
        return log

    def cmd(self, path, argv):
        if path == 'run':
            return [BEND, self.src, '--'] + argv
        if path == 'c':
            return [str(self.bin), '--threads', str(self.threads), '--'] + argv
        return [NODE, '--stack-size=50000', str(self.js), '--'] + argv

    def one(self, path, argv):
        """(status, stdout, stderr tail, seconds); status ok | fail | limit | timeout.

        limit: the machine stack or the memory cap (the JavaScript lanes run under
        an 8 GB RLIMIT_DATA so that a runaway allocation cannot take the host down;
        the native runtime reserves its heap up front and cannot be capped that way)."""
        t0 = time.time()
        try:
            p = subprocess.run(self.cmd(path, argv), cwd=ROOT, env=ENV, capture_output=True, timeout=self.timeout,
                               preexec_fn=limits(0 if path == 'c' else self.memory))
        except subprocess.TimeoutExpired:
            return 'timeout', '', '', time.time() - t0
        out = p.stdout.decode('utf-8', 'replace')
        err = p.stderr.decode('utf-8', 'replace')
        if p.returncode == 0:
            status = 'ok'
        elif any(m in err for m in STACK_MARKS) or p.returncode in (-11, 139):
            status = 'limit'
        elif any(m in err for m in OOM_MARKS):
            status = 'limit'
        else:
            status = 'fail'
        return status, out, err[-300:], time.time() - t0

    def all(self, argv, paths):
        return {p: self.one(p, argv) for p in paths}

    def oracle(self, tokens, size=40):
        """The C build's lines for independent tokens (inputs derived from outputs)."""
        out = []
        for i in range(0, len(tokens), size):
            chunk = tokens[i:i + size]
            status, text, err, _ = self.one('c', chunk)
            lines = text.split('\n')
            out += (lines + [''] * len(chunk))[:len(chunk)]
        return out


def is_nan32(word):
    if not word.isdigit() or len(word) > 10:
        return False
    v = int(word)
    return v <= M32 and (v >> 23) & 0xFF == 0xFF and v & 0x7FFFFF != 0


def normalise(mod, case, res):
    """Replace F32 NaN bit patterns by 'NaN' (docs/BACKEND_BUGS.md, nan-bits).
    Returns the results to compare and the number of lines this changed."""
    if mod.nan32 is None or case.kind != 'tokens':
        return res, 0
    toks = case.argv[case.header:]
    out, changed = {}, set()
    for p, (status, text, err, secs) in res.items():
        lines = text.split('\n')
        for i, tok in enumerate(toks[:len(lines)]):
            if mod.nan32(tok):
                fixed = ' '.join('NaN' if is_nan32(w) else w for w in lines[i].split(' '))
                if fixed != lines[i]:
                    lines[i] = fixed
                    changed.add(i)
        out[p] = (status, '\n'.join(lines), err, secs)
    if len({r[1] for r in res.values()}) == 1:
        return out, 0
    raw = {p: r[1].split('\n') for p, r in res.items()}
    return out, sum(1 for i in changed if len({tuple(v[i:i + 1]) for v in raw.values()}) > 1)


def verdict(res):
    """agree | all-fail | stack-limit | timeout | differ"""
    st = {p: r[0] for p, r in res.items()}
    if any(s == 'timeout' for s in st.values()):
        return 'timeout'
    if all(s == 'ok' for s in st.values()):
        return 'agree' if len({r[1] for r in res.values()}) == 1 else 'differ'
    if any(s == 'limit' for s in st.values()):
        good = {r[1] for p, r in res.items() if st[p] == 'ok'}
        return 'resource-limit' if len(good) <= 1 and all(s in ('ok', 'limit') for s in st.values()) else 'differ'
    if all(s == 'fail' for s in st.values()):
        return 'all-fail'
    return 'differ'


def first_diff(res):
    outs = {p: r[1].split('\n') for p, r in res.items()}
    top = max(len(v) for v in outs.values())
    for i in range(top):
        if len({tuple(v[i:i + 1]) for v in outs.values()}) > 1:
            return i
    return 0


def minimise(runner, case, res, paths, budget=40):
    """A smaller argv that still disagrees, and its results."""
    hd, toks = case.argv[:case.header], case.argv[case.header:]
    if case.kind == 'whole' or not toks:
        return case.argv, res
    def differs(argv):
        r, _ = normalise(runner.mod, Case(argv, case.kind, case.header), runner.all(argv, paths))
        return verdict(r) == 'differ', r
    if case.kind == 'tokens':
        i = min(first_diff(res), len(toks) - 1)
        bad, r = differs(hd + [toks[i]])
        if bad:
            return hd + [toks[i]], r
        bad, r = differs(hd + toks[:i + 1])
        return (hd + toks[:i + 1], r) if bad else (case.argv, res)
    best, best_res = toks, res
    i = first_diff(res)
    if i + 1 < len(best):                      # the operations after the first differing line
        bad, r = differs(hd + best[:i + 1])
        budget -= 1
        if bad:
            best, best_res = best[:i + 1], r
    chunk = max(len(best) // 2, 1)
    while chunk >= 1 and budget > 0:
        at, shrunk = 0, False
        while at < len(best) - 1 and budget > 0:
            trial = best[:at] + best[at + chunk:]
            if not trial:
                break
            bad, r = differs(hd + trial)
            budget -= 1
            if bad:
                best, best_res, shrunk = trial, r, True
            else:
                at += chunk
        if chunk == 1 and not shrunk:
            break
        chunk = chunk // 2 if chunk > 1 else (1 if shrunk else 0)
    return hd + best, best_res


def run_module(mod, args, pool, runner, built):
    t0 = time.time()
    row = {'module': mod.name, 'group': mod.group, 'driver': mod.driver, 'covers': mod.covers, 'cases': 0, 'lines': 0,
           'agree': 0, 'all_fail': 0, 'resource_limit': 0, 'timeouts': 0, 'known': {}, 'disagreements': [], 'notes': [],
           'errors': []}
    errors = built
    if errors:
        row['errors'] = ['build failed: ' + e for e in errors]
        row['seconds'] = round(time.time() - t0, 1)
        return row
    rng = random.Random('%d:%s' % (args.seed, mod.name))
    try:
        cases = mod.gen(rng, args.scale(mod), runner.oracle)
    except Exception as e:  # a generator needing a missing Python module is an error, not a pass
        row['errors'] = ['generator failed: %r' % (e,)]
        row['seconds'] = round(time.time() - t0, 1)
        return row
    picked = [(i, c) for i, c in enumerate(cases) if args.case is None or i == args.case]
    paths = args.paths

    def job(item):
        i, case = item
        return i, case, runner.all(case.argv, paths)

    def culprit(case, res, status):
        """The token that stops the first path whose status is `status`, by bisection."""
        lane = next(p for p in paths if res[p][0] == status)
        toks = case.argv[case.header:]
        while len(toks) > 1:
            half = toks[:len(toks) // 2]
            toks = half if runner.one(lane, case.argv[:case.header] + half)[0] == status else toks[len(half):]
        return toks[0]

    spent = {p: 0.0 for p in paths}
    for i, case, res in pool.map(job, picked):
        row['cases'] += 1
        # a batch of independent tokens that every path refuses (a Nat past the
        # limit): set the refused token aside and compare the others
        for _ in range(3):
            if case.kind != 'tokens' or case.expect or len(case.argv) - case.header < 2:
                break
            if verdict(res) != 'all-fail':
                break
            tok = culprit(case, res, 'fail')
            row['notes'].append({'case': i, 'kind': 'token refused by every path', 'token': tok[:120],
                                 'stderr': res[paths[0]][2].strip()[-120:]})
            row['refused'] = row.get('refused', 0) + 1
            rest = list(case.argv)
            rest.remove(tok)
            case = Case(rest, case.kind, case.header, case.note)
            res = runner.all(case.argv, paths)
        if args.show:
            print('case %d (%s%s): %s' % (i, case.kind, ', ' + case.note if case.note else '', ' '.join(case.argv)))
            for p in paths:
                print('--- %s [%s] %s\n%s' % (p, res[p][0], res[p][2].strip()[-200:], res[p][1]), end='')
        for p in paths:
            spent[p] += res[p][3]
        res, nans = normalise(mod, case, res)
        if nans:
            row['known']['nan-bits'] = row['known'].get('nan-bits', 0) + nans
        v = verdict(res)
        lines = res[paths[-1]][1].count('\n')
        if case.expect == 'all-fail' and v == 'agree':
            v = 'differ-expect'
        if case.expect and case.expect.startswith('known:'):
            key = case.expect[6:]
            if v in ('differ', 'all-fail', 'resource-limit'):
                row['known'][key] = row['known'].get(key, 0) + 1
            else:
                row['notes'].append({'case': i, 'kind': 'known divergence %s did not reproduce' % key, 'argv': case.argv[:6]})
            continue
        if v == 'agree':
            row['agree'] += 1
            row['lines'] += lines
        elif v == 'all-fail':
            row['all_fail'] += 1
            if case.expect != 'all-fail':
                row['notes'].append({'case': i, 'kind': 'all-fail', 'argv': case.argv[:6],
                                     'stderr': {p: res[p][2].strip()[-120:] for p in paths}})
        elif v == 'resource-limit':
            row['resource_limit'] += 1
            note = {'case': i, 'kind': 'resource-limit', 'note': case.note, 'argv_len': len(case.argv),
                    'status': {p: res[p][0] for p in paths},
                    'stderr': {p: res[p][2].strip()[-100:] for p in paths if res[p][0] != 'ok'}}
            if case.kind == 'tokens':       # the token that stops the path
                tok = culprit(case, res, 'limit')
                note['token'] = tok[:80]
                note['token_len'] = len(tok)
            row['notes'].append(note)
        elif v == 'timeout':
            row['timeouts'] += 1
            row['errors'].append('case %d: timeout %s' % (i, {p: res[p][0] for p in paths}))
        else:
            if v == 'differ-expect':
                argv, small = case.argv, res
            else:
                argv, small = minimise(runner, case, res, paths)
            at = first_diff(small)
            d = {'module': mod.name, 'seed': args.seed, 'case': i, 'note': case.note,
                 'rerun': 'python3 tools/backend_diff.py --only %s --seed %d --case %d' % (mod.name, args.seed, i),
                 'driver': mod.driver, 'argv': argv, 'argv_full_len': len(case.argv), 'line': at,
                 'status': {p: small[p][0] for p in paths},
                 'output': {p: (small[p][1].split('\n')[at:at + 1] or [''])[0][:400] for p in paths},
                 'stderr': {p: small[p][2].strip()[-200:] for p in paths},
                 'expected': case.expect or 'identical output'}
            row['disagreements'].append(d)
            print('DISAGREE %s case %d line %d\n  argv: %s\n%s' % (
                mod.name, i, at, ' '.join(argv)[:600],
                '\n'.join('  %-3s [%s] %s' % (p, d['status'][p], d['output'][p][:300]) for p in paths)), flush=True)
    row['seconds'] = round(time.time() - t0, 1)
    row['path_seconds'] = {p: round(s, 1) for p, s in spent.items()}
    return row


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--quick', action='store_true', help='a few minutes instead of 30-60')
    ap.add_argument('--only', default=None, help='comma-separated module or group names')
    ap.add_argument('--seed', type=int, default=2026)
    ap.add_argument('--case', type=int, default=None, help='run one case index of the selected module(s)')
    ap.add_argument('--scale', type=float, default=1.0, help='multiply every module\'s case count')
    ap.add_argument('-j', type=int, default=4, help='parallel cases (default 4)')
    ap.add_argument('--paths', default=','.join(PATHS), help='execution paths to compare (run,c,js)')
    ap.add_argument('--c-threads', type=int, default=1, help='--threads for the native binaries (default 1)')
    ap.add_argument('--timeout', type=int, default=900, help='seconds per invocation')
    ap.add_argument('--strict', action='store_true', help='stack-limit outcomes fail the run as well')
    ap.add_argument('--show', action='store_true', help='print the argv and every path\'s output of each case run')
    ap.add_argument('--list', action='store_true', help='list the modules and exit')
    ap.add_argument('--report', default=str(OUT / 'report.json'))
    args = ap.parse_args()
    args.paths = [p for p in args.paths.split(',') if p]
    if any(p not in PATHS for p in args.paths) or len(args.paths) < 2:
        ap.error('--paths needs at least two of ' + ','.join(PATHS))
    factor = args.scale
    args.scale = lambda mod: max(1, int(round((mod.quick if args.quick else mod.full) * factor)))
    wanted = set(args.only.split(',')) if args.only else None
    mods = [m for m in MODULES if wanted is None or m.name in wanted or m.group in wanted]
    if wanted and wanted - {m.name for m in mods} - {m.group for m in mods}:
        ap.error('unknown module or group: %s' % sorted(wanted - {m.name for m in mods} - {m.group for m in mods}))
    if args.list:
        for m in MODULES:
            print('%-20s %-11s %s' % (m.name, m.group, m.covers))
        return 0
    OUT.mkdir(parents=True, exist_ok=True)
    started = time.time()
    print('backend_diff: bend %s, paths %s, seed %d, %s, -j %d' % (
        VERSION, '/'.join(args.paths), args.seed, 'quick' if args.quick else 'full', args.j), flush=True)
    rows = []
    with ThreadPoolExecutor(max_workers=args.j) as pool:
        runners = [Runner(mod, args.c_threads, args.timeout) for mod in mods]
        t0 = time.time()
        built = list(pool.map(lambda r: r.build(), runners))
        print('built %d drivers (C and JS) in %.0fs' % (len(mods), time.time() - t0), flush=True)
        for mod, runner, log in zip(mods, runners, built):
            row = run_module(mod, args, pool, runner, log)
            rows.append(row)
            print('%-20s cases=%-4d lines=%-6d agree=%-4d all-fail=%-2d limit=%-2d known=%-3d DISAGREE=%-2d errors=%d  %6.1fs %s' % (
                mod.name, row['cases'], row['lines'], row['agree'], row['all_fail'], row['resource_limit'],
                sum(row['known'].values()), len(row['disagreements']), len(row['errors']), row['seconds'],
                row.get('path_seconds', '')), flush=True)
            for e in row['errors']:
                print('  ERROR %s' % e[:500], flush=True)
    bad = sum(len(r['disagreements']) for r in rows)
    errors = sum(len(r['errors']) for r in rows)
    stack = sum(r['resource_limit'] for r in rows)
    passed = bad == 0 and errors == 0 and not (args.strict and stack)
    report = {'passed': passed, 'bend': VERSION, 'paths': args.paths, 'seed': args.seed, 'quick': args.quick,
              'cases': sum(r['cases'] for r in rows), 'lines': sum(r['lines'] for r in rows),
              'disagreements': bad, 'errors': errors, 'resource_limit': stack,
              'known': {k: sum(r['known'].get(k, 0) for r in rows) for k in sorted({k for r in rows for k in r['known']})},
              'all_fail': sum(r['all_fail'] for r in rows), 'seconds': round(time.time() - started, 1), 'modules': rows}
    Path(args.report).parent.mkdir(parents=True, exist_ok=True)
    Path(args.report).write_text(json.dumps(report, indent=1))
    print('backend_diff: %d cases, %d lines compared across %s, %d disagreements, %d errors, %d resource-limit, %d all-fail, known %s, %.0fs -> %s' % (
        report['cases'], report['lines'], '/'.join(args.paths), bad, errors, stack, report['all_fail'],
        report['known'] or 'none', report['seconds'], 'PASS' if passed else 'FAIL'), flush=True)
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
