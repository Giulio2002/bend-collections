"""The cipher group of benchmarks/crypto_suite.py: ChaCha20, Poly1305 and the
AEADs (ChaCha20-Poly1305, XChaCha20-Poly1305, AES-128/256-GCM)."""
import struct
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305
from cryptography.hazmat.primitives.poly1305 import Poly1305
from crypto_suite import pattern
from suite_cases import N, MONO, KiB, MiB, SIZES, rows, per_message

BEAR = N + 'bearssl/'
BEAR_SRC = [BEAR + 'src/' + f for f in ['aes_ct64.c', 'aes_ct64_enc.c', 'aes_ct64_ctr.c', 'aes_big_enc.c', 'aes_big_ctr.c',
                                        'aes_common.c', 'ghash_ctmul64.c', 'gcm.c', 'ccopy.c', 'dec32le.c', 'enc32le.c', 'dec32be.c', 'enc32be.c']]
AEAD_SRC = [N + 'suite_aead.c', MONO + 'monocypher.c'] + BEAR_SRC
AEAD_INC = [MONO, BEAR + 'inc', BEAR + 'src']
KEY32, NONCE12, NONCE24 = pattern(32, 7, 1), pattern(12, 3, 5), pattern(24, 3, 5)


def rotl(x, n):
    return ((x << n) | (x >> (32 - n))) & 0xffffffff


def hchacha20(key, n16):
    """draft-irtf-cfrg-xchacha-03 2.2, for the XChaCha20-Poly1305 check"""
    s = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] + list(struct.unpack('<8I', key)) + list(struct.unpack('<4I', n16))

    def qr(a, b, c, d):
        s[a] = (s[a] + s[b]) & 0xffffffff; s[d] = rotl(s[d] ^ s[a], 16)
        s[c] = (s[c] + s[d]) & 0xffffffff; s[b] = rotl(s[b] ^ s[c], 12)
        s[a] = (s[a] + s[b]) & 0xffffffff; s[d] = rotl(s[d] ^ s[a], 8)
        s[c] = (s[c] + s[d]) & 0xffffffff; s[b] = rotl(s[b] ^ s[c], 7)
    for _ in range(10):
        qr(0, 4, 8, 12); qr(1, 5, 9, 13); qr(2, 6, 10, 14); qr(3, 7, 11, 15)
        qr(0, 5, 10, 15); qr(1, 6, 11, 12); qr(2, 7, 8, 13); qr(3, 4, 9, 14)
    return struct.pack('<8I', *(s[0:4] + s[12:16]))


def aead_seal(alg, m):
    if alg == 0:
        return ChaCha20Poly1305(KEY32).encrypt(NONCE12, m, None)
    if alg == 1:
        return ChaCha20Poly1305(hchacha20(KEY32, NONCE24[:16])).encrypt(b'\0' * 4 + NONCE24[16:], m, None)
    return AESGCM(pattern(16 if alg == 2 else 32, 7, 1)).encrypt(NONCE12, m, None)


def aead_py(m, r):
    return m if r.get('param') else aead_seal(int(r['env']['BENCH_ALG']), m)


def aead_case(name, alg, total, open_total, alt=False):
    rs = [dict(r, env={'BENCH_ALG': str(alg)}) for r in rows(SIZES, total)]
    rs += [dict(size=s, param=1, count=max(1, open_total // s), env={'BENCH_ALG': str(alg)}, label='%s open' % l)
           for s, l in [(KiB, '1 KiB'), (64 * KiB, '64 KiB')]]
    c = dict(name=name, bend='aead', c='aead', c_build={'aead': (AEAD_SRC, AEAD_INC)}, rows=rs, py=per_message(aead_py))
    if alt:
        c['c_alt'] = 'aead_tables'
        c['c_build']['aead_tables'] = (AEAD_SRC, AEAD_INC, ['-DAES_TABLES'])
    return c


CIPHER = [
    dict(name='chacha20', bend='chacha20', c='chacha20', c_build={'chacha20': ([N + 'suite_chacha20.c', MONO + 'monocypher.c'], [MONO])},
         rows=rows(SIZES, 2 * MiB),
         py=per_message(lambda m, r: Cipher(algorithms.ChaCha20(KEY32, struct.pack('<I', 1) + NONCE12), None).encryptor().update(m))),
    dict(name='poly1305', bend='poly1305', c='poly1305', c_build={'poly1305': ([N + 'suite_poly1305.c', MONO + 'monocypher.c'], [MONO])},
         rows=rows(SIZES, MiB), py=per_message(lambda m, r: Poly1305.generate_tag(KEY32, m))),
    aead_case('chacha20poly1305', 0, MiB, 512 * KiB),
    aead_case('xchacha20poly1305', 1, MiB, 512 * KiB),
    aead_case('aes128gcm', 2, 256 * KiB, 128 * KiB, alt=True),
    aead_case('aes256gcm', 3, 256 * KiB, 128 * KiB, alt=True),
]

GROUPS = {'cipher': CIPHER}
