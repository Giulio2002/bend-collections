import Base
import ./suite.bend as S
import ../../src/crypto/kdf.bend as K

# HKDF-SHA256 (src/crypto/kdf.bend): every message is the input keying
# material; fixed 32-byte salt and 16-byte info; BENCH_PARAM output bytes.

def ok(r: Result<&2, &2, K.KdfError, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      [256]
    case Done{xs}:
      xs

def run(xs: List<&2, List<&2, U32>>, +salt: List<&2, U32>, +info: List<&2, U32>, +len: Nat, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      run(t, salt, info, len, ok(K.hkdf(salt, h, info, len)) <> acc)

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    +len : Nat <- S.env_nat("BENCH_PARAM")
    +salt : List<&2, U32> = S.pattern(32n, 5, 3)
    +info : List<&2, U32> = S.pattern(16n, 3, 11)
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(inputs, salt, info, len, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
