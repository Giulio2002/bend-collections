import Base
import ../../../src/crypto/kdf.bend as KDF
import ../../../src/crypto/mac.bend as MAC
import ../../../spec/crypto/hkdf.bend as Spec
import ../../../spec/crypto/hmac.bend as HMAC
import ../mac/hmac.bend as MacP
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ./okm.bend as O
import ./laws.bend as Laws

# Gate for src/crypto/kdf.bend: `bend proofs/crypto/kdf/proof.bend`.
# The block chain and OKM lemmas are in okm.bend.

def is_done(r: Result<&2, &2, KDF.KdfError, List<&2, U32>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

def value(r: Result<&2, &2, KDF.KdfError, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{x}:
      x

def fail_done(+e: KDF.KdfError, +x: List<&2, U32>, +h: {Fail{e} == Done{x} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}) -> Empty:
  L.false_true(Equal.cong(Result<&2, &2, KDF.KdfError, List<&2, U32>>, Bool, is_done, Fail{e}, Done{x}, h))

def done_inj(+x: List<&2, U32>, +y: List<&2, U32>, +h: {Done{x} == Done{y} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}) -> {x == y : List<&2, U32>}:
  Equal.cong(Result<&2, &2, KDF.KdfError, List<&2, U32>>, List<&2, U32>, value, Done{x}, Done{y}, h)

def done_cong(+x: List<&2, U32>, +y: List<&2, U32>, +h: {x == y : List<&2, U32>}) -> {Done{x} == Done{y} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}:
  %h : {Done{x} == Done{_} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  {==}

def Laws.Extract.correct(salt, ikm):
  MacP.sign_correct(salt, ikm)

def expand_if(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, +b: Bool) -> {KDF.expand_if(prk, info, len, b) == Laws.as_result(Spec.expand_if(prk, info, len, b)) : Result<&2, &2, KDF.KdfError, List<&2, U32>>}:
  match b:
    case True{}:
      done_cong(KDF.blocks(len, prk, info, Nil{}, 1), Spec.okm(prk, info, len), O.okm_correct(prk, info, len))
    case False{}:
      {==}

def Laws.Expand.correct(prk, info, len):
  expand_if(prk, info, len, Nat.is_le(len, 8160n))

def Laws.Expand.done(prk, info, len, h):
  %Equal.sym(Bool, Nat.is_le(len, 8160n), True{}, h) : {KDF.expand_if(prk, info, len, _) == Done{Spec.okm(prk, info, len)} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  done_cong(KDF.blocks(len, prk, info, Nil{}, 1), Spec.okm(prk, info, len), O.okm_correct(prk, info, len))

def Laws.Expand.too_long(prk, info, len, h):
  %Equal.sym(Bool, Nat.is_le(len, 8160n), False{}, h) : {KDF.expand_if(prk, info, len, _) == Fail{KDF.LengthTooLarge{}} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  {==}

# From expand's result: the length fits, and the value is the block stream.
def done_ok(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, +out: List<&2, U32>, +b: Bool, +eb: {Nat.is_le(len, 8160n) == b : Bool}, +h: {KDF.expand_if(prk, info, len, b) == Done{out} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}) -> {Nat.is_le(len, 8160n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Nat.is_le(len, 8160n) == True{} : Bool}, fail_done(KDF.LengthTooLarge{}, out, h))

def done_value(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, +out: List<&2, U32>, +b: Bool, +h: {KDF.expand_if(prk, info, len, b) == Done{out} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}) -> {KDF.blocks(len, prk, info, Nil{}, 1) == out : List<&2, U32>}:
  match b:
    case True{}:
      done_inj(KDF.blocks(len, prk, info, Nil{}, 1), out, h)
    case False{}:
      Empty.absurd({KDF.blocks(len, prk, info, Nil{}, 1) == out : List<&2, U32>}, fail_done(KDF.LengthTooLarge{}, out, h))

# out is the specification's OKM.
def done_okm(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat, +out: List<&2, U32>, +h: {KDF.expand(prk, info, len) == Done{out} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}) -> {Spec.okm(prk, info, len) == out : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Spec.okm(prk, info, len), KDF.blocks(len, prk, info, Nil{}, 1), out,
    Equal.sym(List<&2, U32>, KDF.blocks(len, prk, info, Nil{}, 1), Spec.okm(prk, info, len), O.okm_correct(prk, info, len)),
    done_value(prk, info, len, out, Nat.is_le(len, 8160n), h))

def Laws.Expand.length(prk, info, len, out, h):
  %done_okm(prk, info, len, out, h) : {List.length(&2, U32, _) == len : Nat}
  O.okm_length(prk, info, len)

def Laws.Expand.prefix(prk, info, a, b, out, hab, h):
  +hb = done_ok(prk, info, b, out, Nat.is_le(b, 8160n), {==}, h)
  %done_okm(prk, info, b, out, h) : {KDF.expand(prk, info, a) == Done{List.take(&2, U32, _, a)} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  %Equal.sym(Result<&2, &2, KDF.KdfError, List<&2, U32>>, KDF.expand(prk, info, a), Done{Spec.okm(prk, info, a)}, Laws.Expand.done(prk, info, a, N.le_trans(a, b, 8160n, hab, hb))) : {_ == Done{List.take(&2, U32, Spec.okm(prk, info, b), a)} : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  done_cong(Spec.okm(prk, info, a), List.take(&2, U32, Spec.okm(prk, info, b), a), O.okm_prefix(prk, info, a, b, hab))

def Laws.Hkdf.correct(salt, ikm, info, len):
  %Equal.sym(List<&2, U32>, MAC.sign(salt, ikm), HMAC.hmac(salt, ikm), MacP.sign_correct(salt, ikm)) : {KDF.expand(_, info, len) == Laws.as_result(Spec.expand(HMAC.hmac(salt, ikm), info, len)) : Result<&2, &2, KDF.KdfError, List<&2, U32>>}
  Laws.Expand.correct(HMAC.hmac(salt, ikm), info, len)

def Laws.Okm.length(prk, info, len):
  O.okm_length(prk, info, len)

def Laws.Okm.prefix(prk, info, a, b, h):
  O.okm_prefix(prk, info, a, b, h)
