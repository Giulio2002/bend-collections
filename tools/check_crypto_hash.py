#!/usr/bin/env python3
"""Differential tests of the hash modules against Python's hashlib.

  python3 tools/check_crypto_hash.py                 every check
  python3 tools/check_crypto_hash.py sha512 -n 500   one check, 500 random cases

Checks (each a small Bend driver written to build/crypto_hash/, compiled with
the pinned Bend, fed a file of random records, its output compared line by
line with the reference):

  subtle     src/crypto/subtle.bend eq(a, b) against Python's a == b, on equal
             pairs, pairs differing in one byte (first, last, any position),
             pairs of different lengths and unrelated pairs
  sha512     src/crypto/sha512/sha512.bend against hashlib.sha512
  sha3_256   src/crypto/sha3/sha3_256.bend against hashlib.sha3_256
  hash       src/crypto/hash.bend: the one-shot sha256/sha512/sha3_256 and the
             incremental Hasher fed the same message in random chunks
             (including empty chunks and chunks straddling block boundaries),
             each against hashlib

Message lengths are drawn around every multiple of the block size (64, 128,
136) and uniformly. The FIPS 180-4 / FIPS 202 example vectors are also run.
Exit status 0 exactly when every case agrees.
"""
import argparse, hashlib, os, random, shutil, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'crypto_hash'
sys.path.insert(0, str(ROOT / 'tools'))
try:
    from toolchain import BEND  # noqa: E402
except Exception:  # pragma: no cover
    BEND = os.environ.get('BEND', shutil.which('bend') or 'bend')

# Shared reader: the input file is a sequence of little-endian u32 fields and
# bytes; `word` reads one u32, `take` n bytes.
PRELUDE = '''import Base
{imports}

def pack(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def w3(+b0: U32, +b1: U32, +b2: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, b1, b2, 0), Nil{{}})
    case h <> t: (pack(b0, b1, b2, h), t)

def w2(+b0: U32, +b1: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, b1, 0, 0), Nil{{}})
    case h <> t: w3(b0, b1, h, t)

def w1(+b0: U32, bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (pack(b0, 0, 0, 0), Nil{{}})
    case h <> t: w2(b0, h, t)

def word(bs: List<&2, U32>) -> U32 & List<&2, U32>:
  match bs:
    case Nil{{}}: (0, Nil{{}})
    case h <> t: w1(h, t)

def take(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n bs:
    case 0n _: (List.reverse(&2, U32, acc), bs)
    case 1n+p Nil{{}}: (List.reverse(&2, U32, acc), Nil{{}})
    case 1n+p h <> t: take(p, t, h <> acc)

# a length-prefixed byte string
def field_go(pair: U32 & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (n, rest) = pair
  take(U32.to_nat(n), rest, Nil{{}})

def field(bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  field_go(word(bs))

def hexd_if(x: U32, small: Bool) -> Char:
  match small:
    case True{{}}: Chr{{(48 + x : U32)}}
    case False{{}}: Chr{{(87 + x : U32)}}

def hexd(+x: U32) -> Char:
  hexd_if(x, U32.is_lt(x, 10))

def hex(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{{}}: ""
    case +b <> t: SCon{{hexd(U32.and(U32.shrn(b, 4n), 15)), SCon{{hexd(U32.and(b, 15)), hex(t)}}}}

def loaded(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (file, result) = pair
  do IO<List<&2, U32>>:
    File.close(file)
    IO.pass(List<&2, U32>, result)

def count(r: Maybe<&2, Nat>) -> Nat:
  match r:
    case None{{}}: 0n
    case Some{{n}}: n

{body}

# n records, each printing one line; the next record is already read
def records(n: Nat, pair: String & List<&2, U32>) -> IO(Unit):
  match n:
    case 0n:
      (s, rest) = pair
      IO.pure(Unit, Unit{{}})
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

# one record = one length-prefixed message; prints the hex digest
HASH_BODY = '''def hashed(pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (msg, rest) = pair
  (hex({call}(msg)), rest)

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  hashed(field(bs))
'''

SUBTLE_BODY = '''def show(b: Bool) -> String:
  match b:
    case True{}: "1"
    case False{}: "0"

def compared(a: List<&2, U32>, pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (b, rest) = pair
  (show(Subtle.eq(a, b)), rest)

def second(pair: List<&2, U32> & List<&2, U32>) -> String & List<&2, U32>:
  (a, rest) = pair
  compared(a, field(rest))

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  second(field(bs))
'''

# one record = algorithm tag, chunk count, chunks; prints one-shot and incremental digests
FACADE_BODY = '''def start(+tag: U32) -> Hash.Hasher:
  match U32.to_nat(tag):
    case 0n: Hash.new_sha256()
    case 1n: Hash.new_sha512()
    case _: Hash.new_sha3_256()

def oneshot(+tag: U32, msg: List<&2, U32>) -> List<&2, U32>:
  match U32.to_nat(tag):
    case 0n: Hash.sha256(msg)
    case 1n: Hash.sha512(msg)
    case _: Hash.sha3_256(msg)

# n chunks into h; also collects the whole message
def feed(n: Nat, h: Hash.Hasher, msg: List<&2, U32>, bs: List<&2, U32>) -> (Hash.Hasher & List<&2, U32>) & List<&2, U32>:
  match n:
    case 0n: ((h, msg), bs)
    case 1n+p:
      (chunk, rest) = field(bs)
      +c = chunk
      feed(p, Hash.update(h, c), List.append(&2, U32, msg, c), rest)

def both(+tag: U32, r: (Hash.Hasher & List<&2, U32>) & List<&2, U32>) -> String & List<&2, U32>:
  ((h, msg), rest) = r
  (hex(oneshot(tag, msg)) ++ " " ++ hex(Hash.digest(h)), rest)

def chunks(+tag: U32, pair: U32 & List<&2, U32>) -> String & List<&2, U32>:
  (n, rest) = pair
  both(tag, feed(U32.to_nat(n), start(tag), Nil{}, rest))

def one(bs: List<&2, U32>) -> String & List<&2, U32>:
  (tag, rest) = word(bs)
  chunks(tag, word(rest))
'''

CHECKS = {
    'subtle': ('import ../../src/crypto/subtle.bend as Subtle', SUBTLE_BODY),
    'sha512': ('import ../../src/crypto/sha512/sha512.bend as SHA', HASH_BODY.format(call='SHA.sha512')),
    'sha3_256': ('import ../../src/crypto/sha3/sha3_256.bend as SHA3', HASH_BODY.format(call='SHA3.sha3_256')),
    'hash': ('import ../../src/crypto/hash.bend as Hash', FACADE_BODY),
}

BLOCK = {'sha256': 64, 'sha512': 128, 'sha3_256': 136}
REF = {'sha256': hashlib.sha256, 'sha512': hashlib.sha512, 'sha3_256': hashlib.sha3_256}

VECTORS = [b'', b'abc',
           b'abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq',
           b'abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu',
           b'a' * 1000, b'a' * 1000000]


def u32(n):
    return struct.pack('<I', n)


def lengths(rng, block, n):
    edges = [0, 1, 2, 3, 7, 8, 9]
    for k in range(1, 5):
        for d in (-17, -16, -15, -9, -8, -1, 0, 1, 8):
            if k * block + d >= 0:
                edges.append(k * block + d)
    out = []
    for _ in range(n):
        r = rng.random()
        out.append(rng.choice(edges) if r < 0.5 else rng.randrange(0, 5 * block))
    return out


def build(name):
    OUT.mkdir(parents=True, exist_ok=True)
    imports, body = CHECKS[name]
    drv = OUT / ('check_%s.bend' % name)
    drv.write_text(PRELUDE.format(imports=imports, body=body))
    binary = OUT / ('check_%s' % name)
    b = subprocess.run([BEND, str(drv.relative_to(ROOT)), '-o', str(binary.relative_to(ROOT))],
                       cwd=ROOT, capture_output=True, text=True)
    if b.returncode or not binary.exists():
        raise SystemExit('%s: driver did not build\n%s%s' % (name, b.stdout[-3000:], b.stderr[-3000:]))
    return binary


def run(name, binary, recs):
    inp = OUT / ('check_%s.in' % name)
    inp.write_bytes(b''.join(recs))
    r = subprocess.run([str(binary), '--threads', '1'],
                       env={**os.environ, 'CHECK_INPUT': str(inp), 'CHECK_COUNT': str(len(recs))},
                       capture_output=True, text=True)
    got = r.stdout.splitlines()
    if r.returncode or len(got) != len(recs):
        raise SystemExit('%s: driver failed (%d of %d outputs)\n%s' % (name, len(got), len(recs), r.stderr[-2000:]))
    return got


def report(name, got, want, what):
    bad = [(i, g, w) for i, (g, w) in enumerate(zip(got, want)) if g != w]
    for i, g, w in bad[:5]:
        print('  MISMATCH %s case %d (%s): got %s, want %s' % (name, i, what[i], g[:40], w[:40]))
    print('%-9s %s  %d cases, %d failures' % (name, 'ok  ' if not bad else 'FAIL', len(got), len(bad)), flush=True)
    return not bad


def check_subtle(n, seed):
    rng = random.Random('subtle-%d' % seed)
    recs, want, what = [], [], []
    for i in range(n):
        L = rng.choice([0, 1, 2, 3, 16, 32, 64]) if rng.random() < 0.5 else rng.randrange(0, 100)
        a = rng.randbytes(L)
        kind = rng.choice(['equal', 'first', 'last', 'any', 'length', 'random'])
        b = bytearray(a)
        if kind in ('first', 'last', 'any') and L:
            j = {'first': 0, 'last': L - 1, 'any': rng.randrange(L)}[kind]
            b[j] ^= rng.randrange(1, 256)
        elif kind == 'length':
            b = bytearray(a + rng.randbytes(rng.randrange(1, 4))) if rng.random() < 0.5 or not L else bytearray(a[:rng.randrange(L)])
        elif kind == 'random':
            b = bytearray(rng.randbytes(L))
        b = bytes(b)
        recs.append(u32(len(a)) + a + u32(len(b)) + b)
        want.append('1' if a == b else '0')
        what.append('%s, len %d/%d' % (kind, len(a), len(b)))
    return report('subtle', run('subtle', build('subtle'), recs), want, what)


def check_hash(name, n, seed):
    rng = random.Random('%s-%d' % (name, seed))
    msgs = VECTORS + [rng.randbytes(L) for L in lengths(rng, BLOCK[name], n)]
    recs = [u32(len(m)) + m for m in msgs]
    want = [REF[name](m).hexdigest() for m in msgs]
    return report(name, run(name, build(name), recs), want, ['length %d' % len(m) for m in msgs])


def check_facade(n, seed):
    rng = random.Random('hash-%d' % seed)
    recs, want, what = [], [], []
    algos = ['sha256', 'sha512', 'sha3_256']
    for i in range(n):
        tag = i % 3
        algo = algos[tag]
        total = rng.choice(lengths(rng, BLOCK[algo], 1))
        cuts = sorted(rng.randrange(total + 1) for _ in range(rng.randrange(0, 5)))
        if rng.random() < 0.2:
            cuts += [cuts[-1]] if cuts else [0]        # an empty chunk
        m = rng.randbytes(total)
        parts, prev = [], 0
        for c in cuts + [total]:
            parts.append(m[prev:c])
            prev = c
        recs.append(u32(tag) + u32(len(parts)) + b''.join(u32(len(p)) + p for p in parts))
        d = REF[algo](m).hexdigest()
        want.append(d + ' ' + d)
        what.append('%s, %d bytes in chunks %s' % (algo, total, [len(p) for p in parts]))
    return report('hash', run('hash', build('hash'), recs), want, what)


def main():
    ap = argparse.ArgumentParser(description='Differential tests of the hash modules.')
    ap.add_argument('checks', nargs='*', default=['subtle', 'sha512', 'sha3_256', 'hash'])
    ap.add_argument('-n', type=int, default=300)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    ok = True
    for c in a.checks:
        if c == 'subtle':
            ok &= check_subtle(a.n, a.seed)
        elif c == 'hash':
            ok &= check_facade(a.n, a.seed)
        else:
            ok &= check_hash(c, a.n, a.seed)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
