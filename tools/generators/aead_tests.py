#!/usr/bin/env python3
"""Emit tests/crypto/aead/main.bend: ChaCha20-Poly1305 / XChaCha20-Poly1305 vectors.

  python3 tools/generators/aead_tests.py

Vectors: RFC 8439 section 2.8.2 (tag printed in the RFC) and
draft-irtf-cfrg-xchacha-03 appendix A.3.1 (tag printed in the draft), both
asserted against the references below; empty and block-boundary lengths;
decryption of sealed messages; rejection of a flipped ciphertext bit, a
flipped tag bit, a changed aad, a wrong nonce, inputs shorter than the tag,
and wrong key or nonce lengths. References: `cryptography`'s
ChaCha20Poly1305; XChaCha20-Poly1305 composed from a Python HChaCha20 as the
draft specifies.
"""
import os
import struct

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
OUT = os.path.join(ROOT, 'tests/crypto/aead/main.bend')
MASK = 0xffffffff


def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & MASK


def qr(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 7)


def hchacha20(key, nonce16):
    s = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] + list(struct.unpack('<8I', key)) + list(struct.unpack('<4I', nonce16))
    for _ in range(10):
        qr(s, 0, 4, 8, 12); qr(s, 1, 5, 9, 13); qr(s, 2, 6, 10, 14); qr(s, 3, 7, 11, 15)
        qr(s, 0, 5, 10, 15); qr(s, 1, 6, 11, 12); qr(s, 2, 7, 8, 13); qr(s, 3, 4, 9, 14)
    return struct.pack('<8I', *(s[0:4] + s[12:16]))


def seal(x, key, nonce, aad, pt):
    if len(key) != 32 or len(nonce) != (24 if x else 12):
        return None
    if x:
        key, nonce = hchacha20(key, nonce[:16]), bytes(4) + nonce[16:]
    return ChaCha20Poly1305(key).encrypt(nonce, pt, aad)


def open_(x, key, nonce, aad, data):
    if len(key) != 32 or len(nonce) != (24 if x else 12):
        return None
    if x:
        key, nonce = hchacha20(key, nonce[:16]), bytes(4) + nonce[16:]
    try:
        return ChaCha20Poly1305(key).decrypt(nonce, data, aad)
    except InvalidTag:
        return None


SUNSCREEN = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for "
             b"the future, sunscreen would be it.")
KEY = bytes(range(0x80, 0xa0))
AAD = bytes.fromhex('50515253c0c1c2c3c4c5c6c7')
N282 = bytes.fromhex('070000004041424344454647')
NX = bytes(range(0x40, 0x58))
assert seal(False, KEY, N282, AAD, SUNSCREEN)[-16:].hex() == '1ae10b594f09e26a7e902ecbd0600691'
assert seal(True, KEY, NX, AAD, SUNSCREEN)[-16:].hex() == 'c0875924c1c7987947deafd8780acf49'


def aes_seal(key, nonce, aad, pt):
    return AESGCM(key).encrypt(nonce, pt, aad) if len(nonce) == 12 else None


def aes_open(key, nonce, aad, data):
    if len(nonce) != 12:
        return None
    try:
        return AESGCM(key).decrypt(nonce, data, aad)
    except InvalidTag:
        return None


# NIST GCM test case 4 (McGrew and Viega, "The Galois/Counter Mode of Operation"):
# AES-128, 60-byte plaintext, 20-byte aad.
GCM_K = bytes.fromhex('feffe9928665731c6d6a8f9467308308')
GCM_N = bytes.fromhex('cafebabefacedbaddecaf888')
GCM_P = bytes.fromhex('d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39')
GCM_A = bytes.fromhex('feedfacedeadbeeffeedfacedeadbeefabaddad2')
assert AESGCM(GCM_K).encrypt(GCM_N, GCM_P, GCM_A)[-16:].hex() == '5bc94fbc3221a5db94fae95ae7121a47'


def blit(bs):
    return '[' + ', '.join(str(b) for b in bs) + ']'


CASES = []


def alg(x):
    return 'A.XCHACHA20_POLY1305{}' if x else 'A.CHACHA20_POLY1305{}'


def t_seal(label, x, key, nonce, aad, pt):
    r = seal(x, key, nonce, aad, pt)
    CASES.append((label, 'show(A.encrypt(%s, %s, %s, %s, %s))' % (alg(x), blit(key), blit(nonce), blit(aad), blit(pt)),
                  r.hex() if r is not None else 'invalid'))


def t_open(label, x, key, nonce, aad, data):
    r = open_(x, key, nonce, aad, data)
    CASES.append((label, 'show(A.decrypt(%s, %s, %s, %s, %s))' % (alg(x), blit(key), blit(nonce), blit(aad), blit(data)),
                  r.hex() if r is not None else 'invalid'))


def t_aes(label, alg_name, key, nonce, aad, pt=None, data=None):
    if pt is not None:
        want = aes_seal(key, nonce, aad, pt) if len(key) == {'A.AES_128_GCM{}': 16, 'A.AES_256_GCM{}': 32}[alg_name] else None
        CASES.append((label, 'show(A.encrypt(%s, %s, %s, %s, %s))' % (alg_name, blit(key), blit(nonce), blit(aad), blit(pt)),
                      want.hex() if want is not None else 'invalid'))
    else:
        want = aes_open(key, nonce, aad, data) if len(key) == {'A.AES_128_GCM{}': 16, 'A.AES_256_GCM{}': 32}[alg_name] else None
        CASES.append((label, 'show(A.decrypt(%s, %s, %s, %s, %s))' % (alg_name, blit(key), blit(nonce), blit(aad), blit(data)),
                      want.hex() if want is not None else 'invalid'))


def flip(bs, bit):
    b = bytearray(bs)
    b[bit // 8] ^= 1 << (bit % 8)
    return bytes(b)


def build_aes():
    sealed = aes_seal(GCM_K, GCM_N, GCM_A, GCM_P)
    t_aes('aes128gcm gcm tc4 seal', 'A.AES_128_GCM{}', GCM_K, GCM_N, GCM_A, pt=GCM_P)
    t_aes('aes128gcm gcm tc4 open', 'A.AES_128_GCM{}', GCM_K, GCM_N, GCM_A, data=sealed)
    t_aes('aes128gcm flipped tag bit', 'A.AES_128_GCM{}', GCM_K, GCM_N, GCM_A, data=flip(sealed, 8 * len(sealed) - 1))
    t_aes('aes128gcm changed aad', 'A.AES_128_GCM{}', GCM_K, GCM_N, flip(GCM_A, 3), data=sealed)
    t_aes('aes128gcm key 32', 'A.AES_128_GCM{}', GCM_K * 2, GCM_N, GCM_A, pt=GCM_P)
    t_aes('aes128gcm nonce 16', 'A.AES_128_GCM{}', GCM_K, GCM_N + bytes(4), GCM_A, pt=GCM_P)
    k256 = bytes(range(32))
    for n in [0, 1, 16, 33]:
        pt = bytes((5 * i + 1) & 255 for i in range(n))
        t_aes('aes256gcm length %d' % n, 'A.AES_256_GCM{}', k256, GCM_N, GCM_A, pt=pt)
        t_aes('aes256gcm open length %d' % n, 'A.AES_256_GCM{}', k256, GCM_N, GCM_A, data=aes_seal(k256, GCM_N, GCM_A, pt))
    t_aes('aes256gcm flipped ciphertext bit', 'A.AES_256_GCM{}', k256, GCM_N, GCM_A, data=flip(aes_seal(k256, GCM_N, GCM_A, b'abcdefgh'), 2))
    t_aes('aes256gcm key 16', 'A.AES_256_GCM{}', GCM_K, GCM_N, GCM_A, pt=GCM_P)


def build():
    for x, name, nonce in [(False, 'chacha20poly1305', N282), (True, 'xchacha20poly1305', NX)]:
        src = 'rfc8439 2.8.2' if not x else 'xchacha A.3.1'
        t_seal('%s %s seal' % (name, src), x, KEY, nonce, AAD, SUNSCREEN)
        sealed = seal(x, KEY, nonce, AAD, SUNSCREEN)
        t_open('%s %s open' % (name, src), x, KEY, nonce, AAD, sealed)
        t_open('%s flipped ciphertext bit' % name, x, KEY, nonce, AAD, flip(sealed, 37))
        t_open('%s flipped tag bit' % name, x, KEY, nonce, AAD, flip(sealed, 8 * len(sealed) - 3))
        t_open('%s changed aad' % name, x, KEY, nonce, flip(AAD, 0), sealed)
        t_open('%s empty aad' % name, x, KEY, nonce, b'', sealed)
        t_open('%s wrong nonce' % name, x, KEY, flip(nonce, 5), AAD, sealed)
        t_open('%s wrong key' % name, x, flip(KEY, 200), nonce, AAD, sealed)
        t_open('%s tag only' % name, x, KEY, nonce, AAD, sealed[-16:])
        t_open('%s 15 bytes' % name, x, KEY, nonce, AAD, sealed[:15])
        t_open('%s empty input' % name, x, KEY, nonce, AAD, b'')
        t_seal('%s key 31' % name, x, KEY[:31], nonce, AAD, SUNSCREEN)
        t_seal('%s nonce short' % name, x, KEY, nonce[:-1], AAD, SUNSCREEN)
        t_open('%s key 33' % name, x, KEY + b'\x00', nonce, AAD, sealed)
        t_open('%s nonce long' % name, x, KEY, nonce + b'\x00', AAD, sealed)
        key = bytes((9 * i + 1) & 255 for i in range(32))
        for n in [0, 1, 15, 16, 17, 63, 64, 65, 200]:
            pt = bytes((7 * i + n) & 255 for i in range(n))
            aad = bytes((3 * i + 2) & 255 for i in range((5 * n) % 37))
            t_seal('%s length %d' % (name, n), x, key, nonce, aad, pt)
            t_open('%s open length %d' % (name, n), x, key, nonce, aad, seal(x, key, nonce, aad, pt))


HEAD = '''# Generated by tools/generators/aead_tests.py; do not edit.
# ChaCha20-Poly1305 and XChaCha20-Poly1305 through the facade
# src/crypto/aead.bend: RFC 8439 2.8.2, draft-irtf-cfrg-xchacha-03 A.3.1,
# lengths around the Poly1305 and ChaCha20 block sizes, decryption of sealed
# messages and rejection of damaged ones. Expected values: the published
# tags, cross-checked with Python's `cryptography` (ChaCha20Poly1305).
import Base
import ../../../src/crypto/aead.bend as A

def hex_digit_if(x: U32, small: Bool) -> Char:
  match small:
    case True{}: Chr{(48 + x : U32)}
    case False{}: Chr{(87 + x : U32)}

def hex_digit(+x: U32) -> Char:
  hex_digit_if(x, U32.is_lt(x, 10))

def hex(bs: List<&2, U32>) -> String:
  match bs:
    case Nil{}: ""
    case +b <> t: SCon{hex_digit(U32.and(U32.shrn(b, 4n), 15)), SCon{hex_digit(U32.and(b, 15)), hex(t)}}

def show(r: Maybe<&2, List<&2, U32>>) -> String:
  match r:
    case None{}: "invalid"
    case Some{bs}: hex(bs)

def verdict(ok: Bool, label: String, got: String, want: String) -> IO(Bool):
  match ok:
    case True{}:
      IO.pure(Bool, True{})
    case False{}:
      do IO<Bool>:
        IO.print("FAIL " ++ label ++ ": got " ++ got ++ " want " ++ want)
        return False{}

def check(label: String, +got: String, +want: String) -> IO(Bool):
  verdict(String.eq(got, want), label, got, want)

def count(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}: 1n+n
    case False{}: n
'''


def main():
    build()
    build_aes()
    out = [HEAD]
    parts = [CASES[i:i + 12] for i in range(0, len(CASES), 12)]
    for k, part in enumerate(parts):
        out.append('\ndef part%d(n: Nat) -> IO(Nat):\n  do IO<Nat>:\n' % k)
        for j, (label, expr, want) in enumerate(part):
            out.append('    ok%d : Bool <- check("%s", %s, "%s")\n' % (j, label, expr, want))
        acc = 'n'
        for j in range(len(part)):
            acc = 'count(ok%d, %s)' % (j, acc)
        out.append('    return %s\n' % acc)
    out.append('\ndef main() -> IO(Unit):\n  do IO<Unit>:\n')
    prev = '0n'
    for k in range(len(parts)):
        out.append('    n%d : Nat <- part%d(%s)\n' % (k, k, prev))
        prev = 'n%d' % k
    out.append('    IO.print("aead: " ++ Nat.show(%s) ++ "/%d vectors pass")\n' % (prev, len(CASES)))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w') as f:
        f.write(''.join(out))
    print('%d cases -> %s' % (len(CASES), OUT))


if __name__ == '__main__':
    main()
