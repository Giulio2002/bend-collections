import Base
import ../../../src/math/w64.bend as X
import ../../../src/math/u64.bend as WU
import ../../../src/math/random/pcg.bend as P
import ../../../spec/math/random.bend as SR
import ./pcg/step.bend as ST
import ./pcg/output.bend as OU

# The PCG clauses of spec/math/random.bend: one step of src/math/random/pcg.bend
# is the 128-bit LCG and its output DXSM (spec/math/random/pcg.bend), for
# every state and every multiplier and increment; next uses Go's constants.

def step(+mh: WU.U64, +ml: WU.U64, +ih: WU.U64, +il: WU.U64, +p: P.PCG) -> SR.PCG.step(mh, ml, ih, il, p):
  match p:
    case P.P{+hi, +lo}:
      ST.step_pair(mh, ml, ih, il, hi, lo, X.mul128(lo, ml), ST.m128(lo, ml))

def output(+cm: WU.U64, +hi: WU.U64, +lo: WU.U64) -> SR.PCG.output(cm, hi, lo):
  OU.output(cm, hi, lo)

def constants(+p: P.PCG) -> SR.PCG.constants(p):
  {==}
