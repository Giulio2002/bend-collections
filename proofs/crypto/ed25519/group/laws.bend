import Base
import ../../../../spec/crypto/curve25519/edwards.bend as G
import ./gpt.bend as GP

# The clauses of spec/crypto/curve25519/edwards.bend: the abelian group of
# the twisted Edwards curve (gpt.bend on glaw.bend).

def closure(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: G.APt, +b: G.APt, +ha: G.OnCurve(1n+mp, d, a), +hb: G.OnCurve(1n+mp, d, b)) -> G.Group.closure(mp, d, hc, a, b, ha, hb):
  GP.add_on(mp, d, hc, a, b, ha, hb)

def zero_on(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d)) -> G.Group.zero_on(mp, d, hc):
  GP.zero_on(mp, d, hc)

def neg_on(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.neg_on(mp, d, hc, a, ha):
  GP.neg_on(mp, d, a, ha)

def comm(+mp: Nat, +d: Nat, +a: G.APt, +b: G.APt) -> G.Group.comm(mp, d, a, b):
  GP.add_comm(mp, d, a, b)

def zero(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.zero(mp, d, hc, a, ha):
  GP.add_zero_r(mp, d, hc, a, ha)

def neg(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.neg(mp, d, hc, a, ha):
  GP.add_neg(mp, d, hc, a, ha)

def assoc(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: G.APt, +b: G.APt, +c: G.APt, +ha: G.OnCurve(1n+mp, d, a), +hb: G.OnCurve(1n+mp, d, b), +hcc: G.OnCurve(1n+mp, d, c)) -> G.Group.assoc(mp, d, hc, a, b, c, ha, hb, hcc):
  GP.add_assoc(mp, d, hc, a, b, c, ha, hb, hcc)

def nmul_on(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +k: Nat, +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.nmul_on(mp, d, hc, k, a, ha):
  GP.nmul_on(mp, d, hc, k, a, ha)

def nmul_add(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +j: Nat, +k: Nat, +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.nmul_add(mp, d, hc, j, k, a, ha):
  GP.nmul_add(mp, d, hc, j, k, a, ha)

def nmul_mul(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +j: Nat, +k: Nat, +a: G.APt, +ha: G.OnCurve(1n+mp, d, a)) -> G.Group.nmul_mul(mp, d, hc, j, k, a, ha):
  GP.nmul_mul(mp, d, hc, j, k, a, ha)

def nmul_dist(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +k: Nat, +a: G.APt, +b: G.APt, +ha: G.OnCurve(1n+mp, d, a), +hb: G.OnCurve(1n+mp, d, b)) -> G.Group.nmul_dist(mp, d, hc, k, a, b, ha, hb):
  GP.nmul_dist(mp, d, hc, k, a, b, ha, hb)

