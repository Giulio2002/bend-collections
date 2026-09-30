import Base
import ../../../spec/crypto/curve25519/edwards.bend as G
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/ed25519_group.bend as EG

# Extended coordinates against the affine group (interface): the RFC's
# addition and doubling of valid points are valid and are the affine
# addition of their affine points.
#
# PLACEHOLDERS: these five statements are what fblaw.bend needs from the
# group-law work (origin/ed-grouplaw, "extended <-> affine"); each ?TODO is
# to be replaced by its proof there.

def id_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d)) -> EG.Valid(1n+mp, d, SE.identity()):
  ?TODO

def id_aff(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d)) -> {EG.affine(1n+mp, SE.identity()) == G.azero() : G.APt}:
  ?TODO

def valid_on(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +ha: EG.Valid(1n+mp, d, a)) -> G.OnCurve(1n+mp, d, EG.affine(1n+mp, a)):
  ?TODO

def add_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +b: SE.EPt, +ha: EG.Valid(1n+mp, d, a), +hb: EG.Valid(1n+mp, d, b)) -> EG.Valid(1n+mp, d, SE.add(1n+mp, d, a, b)):
  ?TODO

def add_aff(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +b: SE.EPt, +ha: EG.Valid(1n+mp, d, a), +hb: EG.Valid(1n+mp, d, b)) -> {EG.affine(1n+mp, SE.add(1n+mp, d, a, b)) == G.aadd(1n+mp, d, EG.affine(1n+mp, a), EG.affine(1n+mp, b)) : G.APt}:
  ?TODO

def dbl_valid(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +ha: EG.Valid(1n+mp, d, a)) -> EG.Valid(1n+mp, d, SE.double(1n+mp, a)):
  ?TODO

def dbl_aff(+mp: Nat, +d: Nat, +hc: G.Curve(mp, d), +a: SE.EPt, +ha: EG.Valid(1n+mp, d, a)) -> {EG.affine(1n+mp, SE.double(1n+mp, a)) == G.aadd(1n+mp, d, EG.affine(1n+mp, a), EG.affine(1n+mp, a)) : G.APt}:
  ?TODO
