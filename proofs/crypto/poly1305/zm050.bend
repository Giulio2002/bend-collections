import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/poly1305.bend as R
import ../../../src/crypto/poly1305/limbs.bend as Li
import ../../../src/crypto/poly1305/poly1305.bend as P
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../math/typed/width.bend as WW
import ../../math/typed/w64mul.bend as WM
import ../../math/typed/w64sh.bend as SH
import ../../math/typed/f64bits.bend as FB
import ../../math/natural/arith.bend as NR
import ./arith.bend as A
import ./value.bend as V
import ./step.bend as ST
import ./modp.bend as MP
import ./final.bend as F

# The implementation's Poly1305 tag is the RFC 8439 tag (spec/crypto/
# poly1305.bend) for every key and message: the limb accumulator stays
# congruent to the spec's accumulator mod p block by block, and the final
# freeze and byte serialization give the spec's num_to_16_le_bytes.
# mac_correct and mac_length are the clauses of laws.bend (proof.bend fills
# the laws with them; other proofs may import this file).

# ---- bytes to limbs ----

law mask_ev:
  for +xs: List<&2, U32>
  {V.ev(P.mask(xs)) == R.le_num(xs) : Nat}

def mask_ev(xs):
  match xs:
    case Nil{}: {==}
    case x <> t: WM.cong_r(U32.to_nat(U32.and(x, 255)), C.shift(8n, V.ev(P.mask(t))), C.shift(8n, R.le_num(t)), A.csh(8n, V.ev(P.mask(t)), R.le_num(t), mask_ev(t)))

law mask_fit:
  for +xs: List<&2, U32>
  {V.fit_all(P.mask(xs), 8n) == True{} : Bool}

def mask_fit(xs):
  match xs:
    case Nil{}: {==}
    case x <> t:
      L.and_intro(C.fits(8n, V.v(U32.and(x, 255))), V.fit_all(P.mask(t), 8n),
        A.fits_subst(8n, C.low(8n, V.v(x)), V.v(U32.and(x, 255)), A.sy(V.v(U32.and(x, 255)), C.low(8n, V.v(x)), FB.andm(x, 8n, 255, {==})), WW.low_fits(8n, V.v(x))),
        mask_fit(t))

