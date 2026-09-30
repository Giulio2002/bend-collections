import Base
import ../../../src/crypto/mac.bend as MAC
import ../../../src/crypto/subtle.bend as Subtle
import ../../../spec/crypto/hmac.bend as Spec
import ../../../spec/crypto/subtle.bend as SubtleSpec
import ../subtle/laws.bend as SubtleLaws
import ../subtle/proof.bend as SubtleProof
import ./hmac.bend as P
import ./laws.bend as Laws

# Gate for src/crypto/mac.bend: `bend proofs/crypto/mac/proof.bend`.
# Sign: hmac.bend (the key block, then the two hashes through the proved
# SHA-256). Verify: subtle.eq is list equality (proofs/crypto/subtle).

def Laws.Sign.correct(key, msg):
  P.sign_correct(key, msg)

def Laws.Sign.length(key, msg):
  P.sign_len(key, msg)

def Laws.Verify.value(key, msg, tag):
  %P.sign_correct(key, msg) : {Subtle.eq(MAC.sign(key, msg), tag) == SubtleSpec.equal(_, tag) : Bool}
  SubtleLaws.Eq.value(MAC.sign(key, msg), tag)

def Laws.Verify.accepts(key, msg):
  SubtleLaws.Eq.refl(MAC.sign(key, msg))

def Laws.Verify.sound(key, msg, tag, h):
  Equal.sym(List<&2, U32>, MAC.sign(key, msg), tag, SubtleLaws.Eq.sound(MAC.sign(key, msg), tag, h))

def rejects(+key: List<&2, U32>, +msg: List<&2, U32>, +tag: List<&2, U32>, ne: {tag != MAC.sign(key, msg) : List<&2, U32>}, +b: Bool, +eb: {MAC.verify(key, msg, tag) == b : Bool}) -> {MAC.verify(key, msg, tag) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({MAC.verify(key, msg, tag) == False{} : Bool}, ne(Laws.Verify.sound(key, msg, tag, eb)))
    case False{}:
      eb

def Laws.Verify.rejects(key, msg, tag, ne):
  rejects(key, msg, tag, ne, MAC.verify(key, msg, tag), {==})
