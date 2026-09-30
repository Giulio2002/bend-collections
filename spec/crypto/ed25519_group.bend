import Base
import ./curve25519/field.bend as FS
import ./curve25519/edwards.bend as G
import ./ed25519.bend as ED

# Ed25519's points in extended coordinates (spec/crypto/ed25519.bend,
# RFC 8032 section 5.1.4) and the affine group of the curve
# (spec/crypto/curve25519/edwards.bend).

# ---- extended coordinates ----

# (X : Y : Z : T) stands for (X / Z, Y / Z)
def affine(+p: Nat, a: ED.EPt) -> G.APt:
  match a:
    case ED.EPt{x, y, +z, t}:
      G.APt{FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z))}

# Z != 0, (X / Z, Y / Z) on the curve and T Z == X Y
def valid(+p: Nat, +d: Nat, a: ED.EPt) -> Bool:
  match a:
    case ED.EPt{+x, +y, +z, +t}:
      Bool.and(Bool.not(Nat.is_eq(Nat.mod(z, p), 0n)),
        Bool.and(Nat.is_eq(G.lhs(p, FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z))), G.rhs(p, d, FS.fmul(p, x, FS.finv(p, z)), FS.fmul(p, y, FS.finv(p, z)))),
          Nat.is_eq(FS.fmul(p, t, z), FS.fmul(p, x, y))))

def Valid(+p: Nat, +d: Nat, +a: ED.EPt) -> Data:
  {valid(p, d, a) == True{} : Bool}
