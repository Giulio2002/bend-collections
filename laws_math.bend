import Base

# bend-collections-laws-math: the proved laws of bend-collections' math: integer math, per-type math, software binary64, 64-bit words, number theory.
# Importing this file checks every proof root below; see docs/*_CONTRACTS.md
# for what each clause states and what is not proved. Part of
# bend-collections-laws (laws.bend imports all three parts by name).

import ./proofs/math/number/proof.bend as MathNumberProof
import ./proofs/math/proof.bend as MathProof
import ./proofs/math/random/proof.bend as MathRandomProof
import ./proofs/math/random/proof_draws.bend as MathRandomProofDraws
import ./proofs/math/random/proof_float.bend as MathRandomProofFloat
import ./proofs/math/random/proof_pcg.bend as MathRandomProofPcg
import ./proofs/math/typed/examples.bend as MathTypedExamples
import ./proofs/math/typed/f64close.bend as MathTypedF64close
import ./proofs/math/typed/f64divc.bend as MathTypedF64divc
import ./proofs/math/typed/f64fmod.bend as MathTypedF64fmod
import ./proofs/math/typed/f64misc.bend as MathTypedF64misc
import ./proofs/math/typed/f64modf.bend as MathTypedF64modf
import ./proofs/math/typed/f64next.bend as MathTypedF64next
import ./proofs/math/typed/f64ofnat.bend as MathTypedF64ofnat
import ./proofs/math/typed/f64ratio.bend as MathTypedF64ratio
import ./proofs/math/typed/f64sqc.bend as MathTypedF64sqc
import ./proofs/math/typed/float.bend as MathTypedFloat
