#!/usr/bin/env python3
"""Emit tests/crypto/chacha/main.bend: ChaCha20 / HChaCha20 / XChaCha20 vectors.

  python3 tools/generators/chacha_tests.py

Vectors: RFC 8439 sections 2.3.2 and 2.4.2 and appendices A.1 and A.2,
draft-irtf-cfrg-xchacha-03 section 2.2.1 (HChaCha20) and A.3.2 (XChaCha20),
plus edge cases (lengths around the 64-byte block, counter wrap, rejected
key and nonce lengths). Expected outputs are the published hex where the
documents print it, asserted here against the `cryptography` package's
ChaCha20 (and a Python HChaCha20 checked against the draft's vector), and
computed with those references elsewhere.
"""
import os
import struct

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
OUT = os.path.join(ROOT, 'tests/crypto/chacha/main.bend')

MASK = 0xffffffff


def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & MASK


def qr(s, a, b, c, d):
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 16)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 12)
    s[a] = (s[a] + s[b]) & MASK; s[d] = rotl(s[d] ^ s[a], 8)
    s[c] = (s[c] + s[d]) & MASK; s[b] = rotl(s[b] ^ s[c], 7)


def rounds(s, n=10):
    s = list(s)
    for _ in range(n):
        qr(s, 0, 4, 8, 12); qr(s, 1, 5, 9, 13); qr(s, 2, 6, 10, 14); qr(s, 3, 7, 11, 15)
        qr(s, 0, 5, 10, 15); qr(s, 1, 6, 11, 12); qr(s, 2, 7, 8, 13); qr(s, 3, 4, 9, 14)
    return s


CONST = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]


def hchacha20(key, nonce16):
    s = CONST + list(struct.unpack('<8I', key)) + list(struct.unpack('<4I', nonce16))
    s = rounds(s)
    return struct.pack('<8I', *(s[0:4] + s[12:16]))


def chacha20(key, counter, nonce, data):
    c = Cipher(algorithms.ChaCha20(key, struct.pack('<I', counter) + nonce), mode=None).encryptor()
    return c.update(data) + c.finalize()


def block(key, counter, nonce):
    return chacha20(key, counter, nonce, bytes(64))


def chacha20_wrap(key, counter, nonce, data):
    """RFC 8439 2.4 with the 32-bit block counter wrapping to 0 (OpenSSL,
    behind `cryptography`, carries it into the nonce instead)."""
    out = b''
    for j in range(0, len(data), 64):
        ks = block(key, (counter + j // 64) & MASK, nonce)
        out += bytes(a ^ b for a, b in zip(data[j:j + 64], ks))
    return out


def xchacha20(key, counter, nonce24, data):
    return chacha20(hchacha20(key, nonce24[:16]), counter, bytes(4) + nonce24[16:], data)


def hx(s):
    return bytes.fromhex(s.replace(' ', '').replace(':', '').replace('\n', ''))


K01 = bytes(range(32))
SUNSCREEN = (b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for "
             b"the future, sunscreen would be it.")
IETF = (b'Any submission to the IETF intended by the Contributor for publication as all or part of an IETF '
        b'Internet-Draft or RFC and any statement made within the context of an IETF activity is considered '
        b'an "IETF Contribution". Such statements include oral statements in IETF sessions, as well as '
        b'written and electronic communications made at any time or place, which are addressed to')
JABBER = (b"'Twas brillig, and the slithy toves\nDid gyre and gimble in the wabe:\nAll mimsy were the "
          b"borogoves,\nAnd the mome raths outgrabe.")
DHOLE = (b'The dhole (pronounced "dole") is also known as the Asiatic wild dog, red dog, and whistling dog. '
         b'It is about the size of a German shepherd but looks more like a long-legged fox. This highly '
         b'elusive and skilled jumper is classified with wolves, coyotes, jackals, and foxes in the '
         b'taxonomic family Canidae.')

# Published outputs (RFC 8439 2.3.2, 2.4.2; draft-irtf-cfrg-xchacha-03 2.2.1).
RFC_232 = hx('10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e'
             'd2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e')
RFC_242 = hx('6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b'
             'f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8'
             '07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736'
             '5af90bbf74a35be6b40b8eedf2785e42874d')
HCHACHA_221 = hx('82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc')

assert block(K01, 1, hx('000000090000004a00000000')) == RFC_232
assert chacha20(K01, 1, hx('000000000000004a00000000'), SUNSCREEN) == RFC_242
assert hchacha20(K01, hx('000000090000004a0000000031415927')) == HCHACHA_221


def blit(bs):
    return '[' + ', '.join(str(b) for b in bs) + ']'


CASES = []  # (label, bend expression, expected string)


def add(label, expr, want):
    CASES.append((label, expr, want))


def t_block(label, key, counter, nonce, want=None):
    w = want if want is not None else (block(key, counter, nonce).hex()
                                       if len(key) == 32 and len(nonce) == 12 else 'invalid')
    add(label, 'show(I.chacha20_block(%s, %d, %s))' % (blit(key), counter, blit(nonce)), w)


def t_enc(label, key, counter, nonce, pt):
    w = chacha20(key, counter, nonce, pt).hex() if len(key) == 32 and len(nonce) == 12 else 'invalid'
    add(label, 'show(I.chacha20(%s, %d, %s, %s))' % (blit(key), counter, blit(nonce), blit(pt)), w)


def t_h(label, key, nonce):
    w = hchacha20(key, nonce).hex() if len(key) == 32 and len(nonce) == 16 else 'invalid'
    add(label, 'show(I.hchacha20(%s, %s))' % (blit(key), blit(nonce)), w)


def t_x(label, key, counter, nonce, pt):
    w = xchacha20(key, counter, nonce, pt).hex() if len(key) == 32 and len(nonce) == 24 else 'invalid'
    add(label, 'show(I.xchacha20(%s, %d, %s, %s))' % (blit(key), counter, blit(nonce), blit(pt)), w)


def t_round(label, key, counter, nonce, pt):
    # decrypt(encrypt(pt)) == pt, printed as the plaintext's hex
    add(label, 'twice(%s, %d, %s, %s)' % (blit(key), counter, blit(nonce), blit(pt)), pt.hex())


def build():
    z32, z12 = bytes(32), bytes(12)
    t_block('rfc8439 2.3.2 block', K01, 1, hx('000000090000004a00000000'), RFC_232.hex())
    t_enc('rfc8439 2.4.2 sunscreen', K01, 1, hx('000000000000004a00000000'), SUNSCREEN)
    t_block('rfc8439 A.1 #1', z32, 0, z12)
    t_block('rfc8439 A.1 #2', z32, 1, z12)
    t_block('rfc8439 A.1 #3', bytes(31) + b'\x01', 1, z12)
    t_block('rfc8439 A.1 #4', b'\x00\xff' + bytes(30), 2, z12)
    t_block('rfc8439 A.1 #5', z32, 0, bytes(11) + b'\x02')
    t_enc('rfc8439 A.2 #1', z32, 0, z12, bytes(64))
    t_enc('rfc8439 A.2 #2', bytes(31) + b'\x01', 1, bytes(11) + b'\x02', IETF)
    t_enc('rfc8439 A.2 #3', hx('1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0'), 42,
          bytes(11) + b'\x02', JABBER)
    t_h('xchacha 2.2.1 hchacha20', K01, hx('000000090000004a0000000031415927'))
    xkey = bytes(range(0x80, 0xa0))
    t_x('xchacha A.3.2 xchacha20', xkey, 0, hx('404142434445464748494a4b4c4d4e4f5051525354555658'), DHOLE)
    # lengths around the block size, counter wrap, other round inputs
    key = bytes((7 * i + 3) & 255 for i in range(32))
    nonce = bytes((11 * i + 5) & 255 for i in range(12))
    for n in [0, 1, 15, 63, 64, 65, 127, 128, 129, 200]:
        pt = bytes((13 * i + n) & 255 for i in range(n))
        t_enc('length %d' % n, key, 1, nonce, pt)
    add('counter wrap', 'show(I.chacha20(%s, %d, %s, %s))' % (blit(key), 0xffffffff, blit(nonce), blit(bytes(range(130)))),
        chacha20_wrap(key, 0xffffffff, nonce, bytes(range(130))).hex())
    xn = bytes((5 * i + 1) & 255 for i in range(24))
    for n in [0, 1, 64, 100]:
        t_x('xchacha length %d' % n, key, 1, xn, bytes((3 * i) & 255 for i in range(n)))
    t_h('hchacha20 other', key, bytes(range(16)))
    # rejected lengths
    t_block('block key 31', bytes(31), 0, z12)
    t_block('block nonce 13', z32, 0, bytes(13))
    t_enc('encrypt key 33', bytes(33), 0, z12, b'abc')
    t_enc('encrypt nonce 8', z32, 0, bytes(8), b'abc')
    t_h('hchacha nonce 12', z32, z12)
    t_h('hchacha key 0', b'', bytes(16))
    t_x('xchacha nonce 12', z32, 0, z12, b'abc')
    t_x('xchacha nonce 25', z32, 0, bytes(25), b'abc')
    for n in [0, 1, 64, 65, 300]:
        t_round('round trip %d' % n, key, 5, nonce, bytes((17 * i + 9) & 255 for i in range(n)))


HEAD = '''# Generated by tools/generators/chacha_tests.py; do not edit.
# ChaCha20 / HChaCha20 / XChaCha20 vectors: RFC 8439 2.3.2, 2.4.2, A.1, A.2;
# draft-irtf-cfrg-xchacha-03 2.2.1, A.3.2; lengths around the block size,
# counter wrap, rejected key and nonce lengths, decrypt(encrypt(x)) == x.
# Expected values: the published hex, cross-checked with Python's
# `cryptography` (ChaCha20) and a Python HChaCha20 checked against the draft.
import Base
import ../../../src/crypto/chacha/chacha20.bend as I

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

def twice(+key: List<&2, U32>, +counter: U32, +nonce: List<&2, U32>, pt: List<&2, U32>) -> String:
  hex(I.encrypt_rounds(10n, key, counter, nonce, I.encrypt_rounds(10n, key, counter, nonce, pt)))

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
    out.append('    IO.print("chacha: " ++ Nat.show(%s) ++ "/%d vectors pass")\n' % (prev, len(CASES)))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, 'w') as f:
        f.write(''.join(out))
    print('%d cases -> %s' % (len(CASES), OUT))


if __name__ == '__main__':
    main()
