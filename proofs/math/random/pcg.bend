import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/math/w64.bend as SW
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/random/pcg.bend as P
import ../../../spec/math/random.bend as SR
import ../../../spec/math/random/pcg.bend as SP
import ../../lib/lemmas/spec/numeric.bend as S
import ../typed/w64m128.bend as M128
import ./pcg/step.bend as ST
import ./pcg/impl.bend as IM
import ./pcg/output.bend as OU

# The PCG clauses of spec/math/random.bend: one step of src/math/random/pcg.bend
# is the 128-bit LCG and its output DXSM (spec/math/random/pcg.bend), for
# every state and every multiplier and increment; next uses Go's constants.
# The algebra (pcg/step.bend) is width-generic; it is instantiated at 64
# here, where the one comparison at 128 bits happens in a small context.

def step(+mh: WU.U64, +ml: WU.U64, +ih: WU.U64, +il: WU.U64, +p: P.PCG) -> SR.PCG.step(mh, ml, ih, il, p):
  match p:
    case P.P{+hi, +lo}:
      IM.step_pair(mh, ml, ih, il, hi, lo, X.mul128(lo, ml), IM.m128(lo, ml))

def output(+cm: WU.U64, +hi: WU.U64, +lo: WU.U64, +t: Nat, +ht: {t == SP.dxsm1(SW.value(cm), SW.value(hi)) : Nat}) -> SR.PCG.output(cm, hi, lo, t, ht):
  OU.output(cm, hi, lo, t, ht)

def constants(+p: P.PCG) -> SR.PCG.constants(p):
  {==}
