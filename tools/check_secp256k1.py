#!/usr/bin/env python3
"""secp256k1 (src/crypto/secp256k1.bend): ECDSA with RFC 6979 nonces, low-S,
recovery, Ethereum addresses and ecrecover, and BIP-340 Schnorr, against
published vectors, the `cryptography` package and pure-Python references.

  python3 tools/check_secp256k1.py      [-n CASES] [--seed S] [-j JOBS]

1. Vectors (tests/crypto/secp256k1/): every BIP-340 test vector
   (bip340_vectors.csv, from the BIP repository, all 19, valid and
   invalid; signing and public keys also through the key pair API); the secp256k1 RFC 6979 vectors of bitcoinjs-lib; Wycheproof's
   ecdsa_secp256k1_sha256 (verify) and ecdsa_secp256k1_sha256_bitcoin
   (verify_strict) tests whose signature is a strict DER encoding of two
   integers below 2^256 (the API takes r || s; the others test DER
   parsing); go-ethereum's ecRecover precompile vectors and its
   crypto/signature_test.go key recovery vector.
2. Differential: random keys, hashes and messages; ECDSA signatures of the
   Bend code must verify in `cryptography` and `cryptography`'s signatures
   must verify in Bend (both directions), public keys must equal
   `cryptography`'s encodings, signatures/recovery ids/recovered keys and
   addresses must equal the pure-Python reference below, and BIP-340
   signing/verification must equal tools/bip340_reference.py (the BIP's
   reference code), including tampered signatures.

All cases run through one driver (tests/crypto/secp256k1/diff.bend), split
over -j processes. Prints a JSON verdict; exit 1 on any failure.
"""
import argparse, csv, hashlib, hmac, json, os, random, struct, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from toolchain import BEND, ENV  # noqa: E402
import bip340_reference as BIP  # noqa: E402

OUT = ROOT / 'build' / 'crypto-secp256k1'
VEC = ROOT / 'tests' / 'crypto' / 'secp256k1'
FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print('FAIL', msg, file=sys.stderr)


# ---------------------------------------------------------------- reference
# SEC 2 secp256k1, affine textbook arithmetic (SEC 1 section 2.2.1).
P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)


def padd(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a[0] == b[0] and (a[1] + b[1]) % P == 0:
        return None
    if a == b:
        lam = 3 * a[0] * a[0] * pow(2 * a[1], P - 2, P) % P
    else:
        lam = (b[1] - a[1]) * pow(b[0] - a[0], P - 2, P) % P
    x = (lam * lam - a[0] - b[0]) % P
    return (x, (lam * (a[0] - x) - a[1]) % P)


def pmul(k, a):
    r = None
    for i in reversed(range(k.bit_length())):
        r = padd(r, r)
        if (k >> i) & 1:
            r = padd(r, a)
    return r


def encode(q, compressed):
    if compressed:
        return bytes([2 + (q[1] & 1)]) + q[0].to_bytes(32, 'big')
    return b'\x04' + q[0].to_bytes(32, 'big') + q[1].to_bytes(32, 'big')


def decode(bs):
    if len(bs) == 33 and bs[0] in (2, 3):
        x = int.from_bytes(bs[1:], 'big')
        if x >= P:
            return None
        y2 = (x * x * x + 7) % P
        y = pow(y2, (P + 1) // 4, P)
        if y * y % P != y2:
            return None
        if y & 1 != bs[0] & 1:
            y = P - y if y else 0
        return (x, y)
    if len(bs) == 65 and bs[0] == 4:
        x, y = int.from_bytes(bs[1:33], 'big'), int.from_bytes(bs[33:], 'big')
        if x >= P or y >= P or (y * y - x * x * x - 7) % P:
            return None
        return (x, y)
    return None


def H(k, m):
    return hmac.new(k, m, hashlib.sha256).digest()


def rfc6979_sign(d, h):
    """SEC 1 4.1.3 with RFC 6979 3.2 nonces, then low-S (libsecp256k1)."""
    z = int.from_bytes(h, 'big') % N
    seed = d.to_bytes(32, 'big') + z.to_bytes(32, 'big')
    v, k = b'\1' * 32, b'\0' * 32
    k = H(k, v + b'\0' + seed)
    v = H(k, v)
    k = H(k, v + b'\1' + seed)
    v = H(k, v)
    while True:
        v = H(k, v)
        c = int.from_bytes(v, 'big')
        if 1 <= c < N:
            R = pmul(c, G)
            r = R[0] % N
            s = pow(c, N - 2, N) * (z + r * d) % N
            if r and s:
                rid = (R[1] & 1) | (2 if R[0] >= N else 0)
                if s > N // 2:
                    s, rid = N - s, rid ^ 1
                return r, s, rid
        k = H(k, v + b'\0')
        v = H(k, v)


def ecdsa_verify(pk, h, sig, strict):
    q = decode(pk)
    if q is None or len(h) != 32 or len(sig) != 64:
        return False
    r, s = int.from_bytes(sig[:32], 'big'), int.from_bytes(sig[32:], 'big')
    if not (1 <= r < N and 1 <= s < N) or (strict and s > N // 2):
        return False
    z = int.from_bytes(h, 'big') % N
    w = pow(s, N - 2, N)
    R = padd(pmul(z * w % N, G), pmul(r * w % N, q))
    return R is not None and R[0] % N == r


def recover(h, sig):
    if len(h) != 32 or len(sig) != 65:
        return None
    r, s, rid = int.from_bytes(sig[:32], 'big'), int.from_bytes(sig[32:64], 'big'), sig[64]
    if not (1 <= r < N and 1 <= s < N) or rid > 3:
        return None
    x = r + (rid >> 1) * N
    if x >= P:
        return None
    R = decode(bytes([2 + (rid & 1)]) + x.to_bytes(32, 'big'))
    if R is None:
        return None
    z = int.from_bytes(h, 'big') % N
    ri = pow(r, N - 2, N)
    Q = padd(pmul((-z * ri) % N, G), pmul(s * ri % N, R))
    return None if Q is None else encode(Q, False)


# Keccak-256 (the original padding 0x01, as Ethereum uses), FIPS 202's
# Keccak-f[1600] written out.
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
      0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
      0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
      0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
M64 = (1 << 64) - 1


def keccak_f(a):
    for rc in RC:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ (((c[(x + 1) % 5] << 1) | (c[(x + 1) % 5] >> 63)) & M64) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                r = ROT[x][y]
                b[y][(2 * x + 3 * y) % 5] = ((a[x][y] << r) | (a[x][y] >> (64 - r))) & M64 if r else a[x][y]
        a = [[b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
        a[0][0] ^= rc
    return a


def keccak256(msg):
    rate = 136
    m = bytearray(msg) + b'\x01' + b'\0' * ((-len(msg) - 1) % rate)
    m[-1] |= 0x80
    a = [[0] * 5 for _ in range(5)]
    for i in range(0, len(m), rate):
        for j in range(rate // 8):
            a[j % 5][j // 5] ^= int.from_bytes(m[i + 8 * j:i + 8 * j + 8], 'little')
        a = keccak_f(a)
    return b''.join(a[j % 5][j // 5].to_bytes(8, 'little') for j in range(4))


def eth_address(pk):
    if len(pk) != 65 or pk[0] != 4:
        return None
    return keccak256(pk[1:])[12:]


def ecrecover(inp):
    x = (inp + b'\0' * 128)[:128]
    h, vw, rs = x[:32], x[32:64], x[64:]
    if any(vw[:31]) or vw[31] not in (27, 28):
        return None
    pk = recover(h, rs + bytes([vw[31] - 27]))
    return None if pk is None else b'\0' * 12 + eth_address(pk)


# ---------------------------------------------------------------- driver
def field(b):
    return struct.pack('<I', len(b)) + b


def rec(op, *fields):
    return bytes([op]) + b''.join(field(f) for f in fields)


def build(src, out):
    OUT.mkdir(parents=True, exist_ok=True)
    if out.exists():
        out.unlink()
    p = subprocess.run([BEND, src, '-o', str(out)], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=3600)
    if not out.exists():
        raise SystemExit('%s did not build:\n%s%s' % (src, p.stdout[-2000:], p.stderr[-2000:]))


def run_chunk(driver, idx, recs):
    inp = OUT / ('diff%d.in' % idx)
    inp.write_bytes(b''.join(recs))
    p = subprocess.run([str(driver)], env={**ENV, 'FUZZ_INPUT': str(inp), 'FUZZ_COUNT': str(len(recs))},
                       capture_output=True, text=True, timeout=14400)
    inp.unlink()
    got = p.stdout.split('\n')[:len(recs)]
    if p.returncode or len(got) != len(recs):
        fail('driver chunk %d: exit %d, %d of %d answers: %s' % (idx, p.returncode, len(got), len(recs), p.stderr[-500:]))
        return [None] * len(recs)
    return got


def run_all(cases, jobs):
    """cases: list of (name, record, want); want a string or a set of strings."""
    driver = OUT / 'diff'
    build('tests/crypto/secp256k1/diff.bend', driver)
    recs = [c[1] for c in cases]
    size = (len(recs) + jobs - 1) // jobs
    chunks = [recs[i:i + size] for i in range(0, len(recs), size)]
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        outs = list(ex.map(lambda a: run_chunk(driver, a[0], a[1]), enumerate(chunks)))
    got = [g for o in outs for g in o]
    passed, by = 0, {}
    for (name, _, want), g in zip(cases, got):
        ok = g in want if isinstance(want, set) else g == want
        kind = name.split(':')[0]
        t = by.setdefault(kind, [0, 0])
        t[1] += 1
        if ok:
            passed += 1
            t[0] += 1
        elif len(FAILURES) < 40:
            fail('%s: got %s want %s' % (name, (g or '')[:140], str(want)[:140]))
    return passed, by, got


def hx(m):
    return 'none' if m is None else m.hex()


def tf(b):
    return 'true' if b else 'false'


# ---------------------------------------------------------------- vectors
def bip340_cases():
    cases = []
    with open(VEC / 'bip340_vectors.csv') as f:
        for row in csv.DictReader(f):
            i = row['index']
            pk = bytes.fromhex(row['public key'])
            msg = bytes.fromhex(row['message'])
            sig = bytes.fromhex(row['signature'])
            want = row['verification result'] == 'TRUE'
            if row['secret key']:
                sk = bytes.fromhex(row['secret key'])
                aux = bytes.fromhex(row['aux_rand'])
                if BIP.schnorr_sign(msg, sk, aux) != sig or BIP.pubkey_gen(sk) != pk:
                    fail('BIP-340 reference disagrees with vector %s' % i)
                cases.append(('bip340-sign:%s' % i, rec(6, sk, msg, aux), sig.hex()))
                cases.append(('bip340-pubkey:%s' % i, rec(8, sk), pk.hex()))
                cases.append(('bip340-sign-keypair:%s' % i, rec(10, sk, msg, aux), sig.hex()))
                cases.append(('bip340-keypair-pubkey:%s' % i, rec(11, sk), pk.hex()))
            cases.append(('bip340-verify:%s' % i, rec(7, pk, msg, sig), tf(want)))
    return cases


def rfc6979_cases():
    cases = []
    for v in json.load(open(VEC / 'rfc6979_secp256k1.json'))['ecdsa']:
        d = int(v['d'], 16)
        h = hashlib.sha256(v['message'].encode()).digest()
        r, s, rid = rfc6979_sign(d, h)
        want_r, want_s = int(v['signature']['r'], 16), int(v['signature']['s'], 16)
        if (r, s) != (want_r, want_s):
            fail('reference RFC 6979 disagrees with bitcoinjs vector d=%s' % v['d'])
        sig = r.to_bytes(32, 'big') + s.to_bytes(32, 'big')
        cases.append(('rfc6979-sign:%s' % v['d'][:8], rec(0, d.to_bytes(32, 'big'), h), (sig + bytes([rid])).hex()))
        pk = encode(pmul(d, G), True)
        cases.append(('rfc6979-verify:%s' % v['d'][:8], rec(1, pk, h, sig), 'true'))
    return cases


def der_int(b, i):
    if b[i] != 2:
        return None, i
    n = b[i + 1]
    if n == 0 or n > 33 or i + 2 + n > len(b):
        return None, i
    v = b[i + 2:i + 2 + n]
    return int.from_bytes(v, 'big'), i + 2 + n


def der_encode(r, s):
    def enc(x):
        b = x.to_bytes((x.bit_length() + 8) // 8, 'big') if x else b'\0'
        return b'\x02' + bytes([len(b)]) + b
    body = enc(r) + enc(s)
    return b'\x30' + bytes([len(body)]) + body


def wycheproof_cases(fname, op, strict):
    cases, skipped = [], 0
    data = json.load(open(VEC / fname))
    for tc, pk, msg, sig, result, comment in data['tests']:
        sig = bytes.fromhex(sig)
        try:
            r, i = der_int(sig, 2)
            s, j = der_int(sig, i)
        except IndexError:
            r = s = None
        if r is None or s is None or r >= 2**256 or s >= 2**256 or der_encode(r, s) != sig:
            skipped += 1
            continue
        h = hashlib.sha256(bytes.fromhex(msg)).digest()
        pkb = bytes.fromhex(pk)
        rs = r.to_bytes(32, 'big') + s.to_bytes(32, 'big')
        ref = ecdsa_verify(pkb, h, rs, strict)
        if result != 'acceptable' and ref != (result == 'valid'):
            fail('reference disagrees with Wycheproof %s #%d (%s)' % (fname, tc, comment))
        cases.append(('wycheproof%s:%d' % ('-bitcoin' if strict else '', tc), rec(op, pkb, h, rs), tf(ref)))
    return cases, skipped


def ecrecover_cases():
    cases = []
    for v in json.load(open(VEC / 'ethereum_ecrecover.json')):
        inp = bytes.fromhex(v['Input'])
        want = v['Expected'] or None
        ref = hx(ecrecover(inp))
        if ref != (want or 'none'):
            fail('reference ecrecover disagrees with go-ethereum vector %s' % v['Name'])
        cases.append(('ecrecover:%s' % v['Name'], rec(9, inp), want or 'none'))
    # go-ethereum crypto/signature_test.go
    msg = bytes.fromhex('ce0677bb30baa8cf067c88db9811f4333d131bf8bcf12fe7065d211dce971008')
    sig = bytes.fromhex('90f27b8b488db00b00606796d2987f6a5f59ae62ea05effe84fef5b8b0e549984a691139ad57a3f0b906637673aa2f63d1f55cb1a69199d4009eea23ceaddc9301')
    pk = bytes.fromhex('04e32df42865e97135acfb65f3bae71bdc86f4d49150ad6a440b6f15878109880a0a2b2667f7e725ceea70c673093bf67663e0312623c8e091b13cf2c0f11ef652')
    if recover(msg, sig) != pk:
        fail('reference recover disagrees with go-ethereum signature_test')
    cases.append(('geth-recover:1', rec(3, msg, sig), pk.hex()))
    cases.append(('geth-verify:1', rec(1, pk, msg, sig[:64]), 'true'))
    cases.append(('geth-verify:c', rec(1, bytes.fromhex('02e32df42865e97135acfb65f3bae71bdc86f4d49150ad6a440b6f15878109880a'), msg, sig[:64]), 'true'))
    # the address of the key 1 (widely published)
    a1 = eth_address(encode(G, False))
    if a1.hex() != '7e5f4552091a69125d5dfcb7b8c2659029395bdf':
        fail('reference keccak/address of key 1')
    cases.append(('eth-address:1', rec(5, encode(G, False)), a1.hex()))
    return cases


# ---------------------------------------------------------------- differential
def crypto_key(d):
    from cryptography.hazmat.primitives.asymmetric import ec
    return ec.derive_private_key(d, ec.SECP256K1())


def crypto_sign(d, h):
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.asymmetric.utils import Prehashed, decode_dss_signature
    der = crypto_key(d).sign(h, ec.ECDSA(Prehashed(hashes.SHA256())))
    return decode_dss_signature(der)


def crypto_verify(pk, h, r, s):
    from cryptography.exceptions import InvalidSignature
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.asymmetric.utils import Prehashed, encode_dss_signature
    key = ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256K1(), pk)
    try:
        key.verify(encode_dss_signature(r, s), h, ec.ECDSA(Prehashed(hashes.SHA256())))
        return True
    except InvalidSignature:
        return False


def crypto_pub(d, compressed):
    from cryptography.hazmat.primitives import serialization
    fmt = serialization.PublicFormat.CompressedPoint if compressed else serialization.PublicFormat.UncompressedPoint
    return crypto_key(d).public_key().public_bytes(serialization.Encoding.X962, fmt)


def rand_scalar(rng):
    r = rng.random()
    if r < 0.05:
        return rng.choice([1, 2, 3, N - 1, N - 2, N // 2, N // 2 + 1, 2**128, 2**255])
    return rng.randrange(1, N)


def differential(n, rng):
    cases, post = [], []
    for i in range(n):
        d = rand_scalar(rng)
        h = rng.randbytes(32) if rng.random() < 0.9 else rng.choice([b'\0' * 32, b'\xff' * 32, N.to_bytes(32, 'big')])
        skb = d.to_bytes(32, 'big')
        r, s, rid = rfc6979_sign(d, h)
        sig = r.to_bytes(32, 'big') + s.to_bytes(32, 'big')
        comp = rng.random() < 0.5
        pk = encode(pmul(d, G), comp)
        if pk != crypto_pub(d, comp):
            fail('reference public key disagrees with cryptography')
        if not crypto_verify(pk, h, r, s):
            fail('cryptography rejects the reference signature')
        cases.append(('diff-sign:%d' % i, rec(0, skb, h), (sig + bytes([rid])).hex()))
        cases.append(('diff-pubkey:%d' % i, rec(4, skb, bytes([1 if comp else 0])), pk.hex()))
        # cryptography's own (random-nonce) signatures, and their high-S twins
        cr, cs = crypto_sign(d, h)
        csig = cr.to_bytes(32, 'big') + cs.to_bytes(32, 'big')
        cases.append(('diff-verify-cryptography:%d' % i, rec(1, pk, h, csig), 'true'))
        cases.append(('diff-verify-strict:%d' % i, rec(2, pk, h, csig), tf(cs <= N // 2)))
        hs = cr.to_bytes(32, 'big') + (N - cs).to_bytes(32, 'big')
        cases.append(('diff-verify-highs:%d' % i, rec(1, pk, h, hs), 'true'))
        # tampering
        bad = bytearray(sig)
        bad[rng.randrange(64)] ^= 1 << rng.randrange(8)
        cases.append(('diff-verify-tampered:%d' % i, rec(1, pk, h, bytes(bad)), tf(ecdsa_verify(pk, h, bytes(bad), False))))
        h2 = bytearray(h)
        h2[rng.randrange(32)] ^= 1
        cases.append(('diff-verify-otherhash:%d' % i, rec(1, pk, bytes(h2), sig), tf(ecdsa_verify(pk, bytes(h2), sig, False))))
        # recovery and addresses
        full = encode(pmul(d, G), False)
        cases.append(('diff-recover:%d' % i, rec(3, h, sig + bytes([rid])), full.hex()))
        other = rid ^ 1
        cases.append(('diff-recover-other:%d' % i, rec(3, h, sig + bytes([other])), hx(recover(h, sig + bytes([other])))))
        cases.append(('diff-address:%d' % i, rec(5, full), eth_address(full).hex()))
        pre = h + (27 + (rid & 1)).to_bytes(32, 'big') + sig
        cases.append(('diff-ecrecover:%d' % i, rec(9, pre), hx(ecrecover(pre))))
        # the Bend signature must verify in cryptography: checked after the run
        post.append((len(cases) - 11, pk, h))
        # BIP-340
        msg = rng.randbytes(rng.choice([0, 1, 31, 32, 33, 64, 100]))
        aux = rng.randbytes(32)
        ssig = BIP.schnorr_sign(msg, skb, aux)
        xpk = BIP.pubkey_gen(skb)
        cases.append(('diff-schnorr-sign:%d' % i, rec(6, skb, msg, aux), ssig.hex()))
        cases.append(('diff-schnorr-pubkey:%d' % i, rec(8, skb), xpk.hex()))
        cases.append(('diff-schnorr-sign-keypair:%d' % i, rec(10, skb, msg, aux), ssig.hex()))
        cases.append(('diff-schnorr-keypair-pubkey:%d' % i, rec(11, skb), xpk.hex()))
        cases.append(('diff-schnorr-verify:%d' % i, rec(7, xpk, msg, ssig), 'true'))
        bad = bytearray(ssig)
        bad[rng.randrange(64)] ^= 1 << rng.randrange(8)
        cases.append(('diff-schnorr-tampered:%d' % i, rec(7, xpk, msg, bytes(bad)), tf(BIP.schnorr_verify(msg, xpk, bytes(bad)))))
    # malformed inputs
    for j, (op, fs, want) in enumerate([
            (0, [b'\0' * 32, b'\1' * 32], 'none'), (0, [N.to_bytes(32, 'big'), b'\1' * 32], 'none'),
            (0, [b'\1' * 31, b'\1' * 32], 'none'), (0, [b'\1' * 32, b'\1' * 31], 'none'),
            (4, [b'\0' * 32, b'\1'], 'none'), (8, [N.to_bytes(32, 'big')], 'none'),
            (1, [encode(G, True), b'\1' * 32, b'\1' * 63], 'false'),
            (1, [b'\2' + P.to_bytes(32, 'big'), b'\1' * 32, b'\1' * 64], 'false'),
            (1, [b'\4' + b'\0' * 64, b'\1' * 32, b'\1' * 64], 'false'),
            (3, [b'\1' * 32, b'\0' * 64 + b'\0'], 'none'), (3, [b'\1' * 32, b'\1' * 64 + b'\4'], 'none'),
            (5, [encode(G, True)], 'none'), (9, [b''], 'none'),
            (6, [b'\1' * 32, b'', b'\1' * 31], 'none'), (7, [b'\1' * 31, b'', b'\1' * 64], 'false')]):
        cases.append(('malformed:%d' % j, rec(op, *fs), want))
    return cases, post


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('-n', type=int, default=60)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('-j', type=int, default=4)
    a = ap.parse_args()
    rng = random.Random('secp256k1-%d' % a.seed)
    cases = bip340_cases() + rfc6979_cases() + ecrecover_cases()
    w1, sk1 = wycheproof_cases('wycheproof_ecdsa_secp256k1_sha256.json', 1, False)
    w2, sk2 = wycheproof_cases('wycheproof_ecdsa_secp256k1_sha256_bitcoin.json', 2, True)
    dcases, post = differential(a.n, rng)
    cases += w1 + w2 + dcases
    passed, by, got = run_all(cases, a.j)
    base = len(cases) - len(dcases)
    crossed = 0
    for idx, pk, h in post:
        g = got[base + idx]
        if g and g != 'none' and len(g) == 130:
            r, s = int(g[:64], 16), int(g[64:128], 16)
            if crypto_verify(pk, h, r, s):
                crossed += 1
            else:
                fail('cryptography rejects the Bend signature of case %d' % idx)
        else:
            fail('no Bend signature for case %d' % idx)
    verdict = {'cases': len(cases), 'passed': passed, 'bend_signatures_verified_by_cryptography': crossed, 'by_kind': {k: '%d/%d' % tuple(v) for k, v in sorted(by.items())},
               'wycheproof_skipped_non_der': sk1 + sk2, 'differential_rounds': a.n, 'seed': a.seed,
               'failures': FAILURES, 'ok': not FAILURES and passed == len(cases)}
    print(json.dumps(verdict, indent=1))
    return 0 if verdict['ok'] else 1


if __name__ == '__main__':
    sys.exit(main())
