import Base
import ../../../spec/lib/common.bend as C
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ../../../spec/crypto/ed25519_group.bend as EG
import ../../../src/crypto/ed25519/point.bend as PT

# The table form of [k] B over the specification's points
# (spec/crypto/ed25519.bend EPt, add, double), mirroring
# src/crypto/ed25519/point.bend: rows [0 a, 1 a, ..., 15 a] by repeated
# addition for a = B, 16 B, 16^2 B, ... (16 a by four doublings), and the
# sum over the hexadecimal digits of k of the row entries. The
# implementation's table multiplication is related to smulb point by point
# (pfb.bend); that smulb is the specification's double-and-add [k] B is
# the group law, stated here as LawE and LawQ in the two forms the
# clauses use (the encoding, and the comparison with another point).

def sx(a: SE.EPt) -> Nat:
  match a:
    case SE.EPt{x, y, z, t}:
      x

def sy(a: SE.EPt) -> Nat:
  match a:
    case SE.EPt{x, y, z, t}:
      y

def sz(a: SE.EPt) -> Nat:
  match a:
    case SE.EPt{x, y, z, t}:
      z

def st(a: SE.EPt) -> Nat:
  match a:
    case SE.EPt{x, y, z, t}:
      t

# entry d of a row (the identity when there is none)
def snth(d: Nat, r: List<&2, SE.EPt>) -> SE.EPt:
  match d r:
    case _ Nil{}:
      SE.identity()
    case 0n Con{a, t}:
      a
    case 1n+k Con{a, t}:
      snth(k, t)

# [m, m + a, ...]: n entries
def srow_go(n: Nat, +p: Nat, +d: Nat, +a: SE.EPt, +m: SE.EPt) -> List<&2, SE.EPt>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{m, srow_go(k, p, d, a, SE.add(p, d, m, a))}

# [0 a, 1 a, ..., 15 a]
def srow(+p: Nat, +d: Nat, +a: SE.EPt) -> List<&2, SE.EPt>:
  Con{SE.identity(), srow_go(15n, p, d, a, a)}

# 16 a
def sdbl4(+p: Nat, a: SE.EPt) -> SE.EPt:
  SE.double(p, SE.double(p, SE.double(p, SE.double(p, a))))

# the rows of a, 16 a, 16^2 a, ...: n of them
def stab(n: Nat, +p: Nat, +d: Nat, +a: SE.EPt) -> List<&2, List<&2, SE.EPt>>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{srow(p, d, a), stab(k, p, d, sdbl4(p, a))}

# acc plus, for every row and its digit, the row's entry at the digit
def sfb(+p: Nat, +d: Nat, tab: List<&2, List<&2, SE.EPt>>, ds: List<&2, Nat>, acc: SE.EPt) -> SE.EPt:
  match tab:
    case Nil{}:
      acc
    case Con{r, tt}:
      match ds:
        case Nil{}:
          acc
        case Con{dg, dt}:
          sfb(p, d, tt, dt, SE.add(p, d, acc, snth(dg, r)))

# the table form of [value(bs)] B for the 64 rows of the base point (the
# count 2^6 one, as the spec writes its loop counts)
def smulb(+one: Nat, +p: Nat, +d: Nat, +bs: List<&2, U32>) -> SE.EPt:
  sfb(p, d, stab(C.shift(6n, one), p, d, SE.base(p, d)), PT.nibs(bs), SE.identity())

# the specification's [value(bs)] B
def smul(+one: Nat, +p: Nat, +d: Nat, +bs: List<&2, U32>) -> SE.EPt:
  SE.mul(one, p, d, FS.value(bs), SE.base(p, d))

# the table form encodes as the specification's point
def LawE(+one: Nat, +pp: Nat) -> Type:
  @+bs: List<&2, U32> -> @+hb: {FS.bytes_ok(32n, bs) == True{} : Bool} -> {SE.encode(one, 1n+pp, smulb(one, 1n+pp, SE.dconst(one, 1n+pp), bs)) == SE.encode(one, 1n+pp, smul(one, 1n+pp, SE.dconst(one, 1n+pp), bs)) : List<&2, U32>}

# the table form compares with any point as the specification's point
def LawQ(+one: Nat, +pp: Nat) -> Type:
  @+bs: List<&2, U32> -> @+hb: {FS.bytes_ok(32n, bs) == True{} : Bool} -> @+q: SE.EPt -> {SE.equal(1n+pp, smulb(one, 1n+pp, SE.dconst(one, 1n+pp), bs), q) == SE.equal(1n+pp, smul(one, 1n+pp, SE.dconst(one, 1n+pp), bs), q) : Bool}

# ---- 4-bit windows (point.bend win, mul_win) ----

# 16 ([rest] a) + [d] a over the row srw, most significant digit first
def swin(+p: Nat, +d: Nat, +srw: List<&2, SE.EPt>, ds: List<&2, Nat>) -> SE.EPt:
  match ds:
    case Nil{}:
      SE.identity()
    case Con{dg, dt}:
      SE.add(p, d, sdbl4(p, swin(p, d, srw, dt)), snth(dg, srw))

def smulw(+p: Nat, +d: Nat, +bs: List<&2, U32>, +a: SE.EPt) -> SE.EPt:
  swin(p, d, srow(p, d, a), PT.nibs(bs))

# R + (the window form of [k] a) compares with any point as R + [k] a,
# for valid R and a
def LawW(+one: Nat, +pp: Nat) -> Type:
  @+bs: List<&2, U32> -> @+hb: {FS.bytes_ok(32n, bs) == True{} : Bool} -> @+x: SE.EPt -> @+r: SE.EPt -> @+a: SE.EPt -> @+hr: EG.Valid(1n+pp, SE.dconst(one, 1n+pp), r) -> @+ha: EG.Valid(1n+pp, SE.dconst(one, 1n+pp), a) -> {SE.equal(1n+pp, x, SE.add(1n+pp, SE.dconst(one, 1n+pp), r, smulw(1n+pp, SE.dconst(one, 1n+pp), bs, a))) == SE.equal(1n+pp, x, SE.add(1n+pp, SE.dconst(one, 1n+pp), r, SE.mul(one, 1n+pp, SE.dconst(one, 1n+pp), FS.value(bs), a))) : Bool}

# whatever the bytes, the decoding (or the identity, when there is none)
# is a valid point
def LawV(+one: Nat, +pp: Nat) -> Type:
  @+bs: List<&2, U32> -> EG.Valid(1n+pp, SE.dconst(one, 1n+pp), SE.base_of(SE.decode(1n+pp, SE.dconst(one, 1n+pp), bs)))
