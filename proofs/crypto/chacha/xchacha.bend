import Base
import ../../../src/crypto/chacha/core.bend as C
import ../../../src/crypto/chacha/chacha20.bend as I
import ../../../spec/crypto/chacha.bend as R
import ./core.bend as K
import ./stream.bend as T

# HChaCha20 and XChaCha20 against spec/crypto/chacha.bend: HChaCha20 for
# every number of double rounds, then at twenty rounds; XChaCha20 composed
# from HChaCha20 and the ChaCha20 stream.


def hout(+l: List<&2, U32>) -> List<&2, U32>:
  R.serialize([R.get(l, 0n), R.get(l, 1n), R.get(l, 2n), R.get(l, 3n), R.get(l, 12n), R.get(l, 13n), R.get(l, 14n), R.get(l, 15n)])

law hbody_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +nb: List<&2, U32>
  {I.hchacha_body(r, kb, nb) == R.hchacha_body(r, kb, nb) : List<&2, U32>}

def hbody_correct(r, kb, nb):
  +H = I.hstate(I.key_words(I.words(kb)), I.words(nb))
  Equal.trans(List<&2, U32>, C.hbytes(C.rounds(r, H)), hout(K.vec(C.rounds(r, H))), R.hchacha_body(r, kb, nb),
    K.hbytes_correct(C.rounds(r, H)),
    Equal.trans(List<&2, U32>, hout(K.vec(C.rounds(r, H))), hout(R.inner_blocks(r, K.vec(H))), R.hchacha_body(r, kb, nb),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => hout(l), K.vec(C.rounds(r, H)), R.inner_blocks(r, K.vec(H)), K.rounds_correct(r, H)),
      Equal.trans(List<&2, U32>, hout(R.inner_blocks(r, K.vec(H))), hout(R.inner_blocks(r, R.hstate(I.words(kb), I.words(nb)))), R.hchacha_body(r, kb, nb),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => hout(R.inner_blocks(r, l)), K.vec(H), R.hstate(I.words(kb), I.words(nb)), T.hstate_eq(I.words(kb), I.words(nb))),
        Equal.trans(List<&2, U32>, hout(R.inner_blocks(r, R.hstate(I.words(kb), I.words(nb)))), hout(R.inner_blocks(r, R.hstate(R.words(kb), I.words(nb)))), R.hchacha_body(r, kb, nb),
          Equal.cong(List<&2, U32>, List<&2, U32>, l => hout(R.inner_blocks(r, R.hstate(l, I.words(nb)))), I.words(kb), R.words(kb), T.words_eq(kb)),
          Equal.cong(List<&2, U32>, List<&2, U32>, l => hout(R.inner_blocks(r, R.hstate(R.words(kb), l))), I.words(nb), R.words(nb), T.words_eq(nb))))))

law hchacha_rounds_correct:
  for +r: Nat
  for +kb: List<&2, U32>
  for +nb: List<&2, U32>
  {I.hchacha_rounds(r, kb, nb) == R.hchacha_rounds(r, kb, nb) : List<&2, U32>}

def hchacha_rounds_correct(r, kb, nb):
  match kb:
    case Nil{}: hbody_correct(r, Nil{}, nb)
    case b <> rest: hbody_correct(r, b <> rest, nb)

law hchacha20_correct:
  for +kb: List<&2, U32>
  for +nb: List<&2, U32>
  {I.hchacha20_unchecked(kb, nb) == R.hchacha20(kb, nb) : List<&2, U32>}

def hchacha20_correct(kb, nb):
  hchacha_rounds_correct(10n, kb, nb)

law xencrypt_correct:
  for +kb: List<&2, U32>
  for +c: U32
  for +nb: List<&2, U32>
  for +pt: List<&2, U32>
  {I.xencrypt_unchecked(kb, c, nb, pt) == R.xencrypt(kb, c, nb, pt) : List<&2, U32>}

def xenc(+kb: List<&2, U32>, +c: U32, +sub: List<&2, U32>, +nn: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  R.encrypt_rounds(10n, sub, c, 0 <> 0 <> 0 <> 0 <> nn, pt)

def xencrypt_correct(kb, c, nb, pt):
  +sub = I.hchacha20_unchecked(kb, I.take(16n, nb))
  Equal.trans(List<&2, U32>, I.encrypt_rounds(10n, sub, c, 0 <> 0 <> 0 <> 0 <> I.skip(16n, nb), pt), xenc(kb, c, sub, I.skip(16n, nb), pt), R.xencrypt(kb, c, nb, pt),
    T.encrypt_correct(10n, sub, c, 0 <> 0 <> 0 <> 0 <> I.skip(16n, nb), pt),
    Equal.trans(List<&2, U32>, xenc(kb, c, sub, I.skip(16n, nb), pt), xenc(kb, c, sub, R.suffix(16n, nb), pt), R.xencrypt(kb, c, nb, pt),
      Equal.cong(List<&2, U32>, List<&2, U32>, l => xenc(kb, c, sub, l, pt), I.skip(16n, nb), R.suffix(16n, nb), T.skip_eq(16n, nb)),
      Equal.trans(List<&2, U32>, xenc(kb, c, sub, R.suffix(16n, nb), pt), xenc(kb, c, R.hchacha20(kb, I.take(16n, nb)), R.suffix(16n, nb), pt), R.xencrypt(kb, c, nb, pt),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => xenc(kb, c, l, R.suffix(16n, nb), pt), sub, R.hchacha20(kb, I.take(16n, nb)), hchacha20_correct(kb, I.take(16n, nb))),
        Equal.cong(List<&2, U32>, List<&2, U32>, l => xenc(kb, c, R.hchacha20(kb, l), R.suffix(16n, nb), pt), I.take(16n, nb), R.prefix(16n, nb), T.take_eq(16n, nb)))))
