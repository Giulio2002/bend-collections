import Base
import ../../../src/crypto/ed25519/point.bend as PT

# The windows of point.bend with the T coordinate skipped where the next
# operation is a doubling (which does not read T) compute the same point
# as win: winf == win.

def dd(+R: Nat, +p: PT.Pt) -> {PT.double(R, PT.double_nt(R, p)) == PT.double(R, PT.double(R, p)) : PT.Pt}:
  match p:
    case PT.Pt{x, y, z, t}:
      {==}

def cg(+R: Nat, +a: PT.Pt, +b: PT.Pt, +e: {a == b : PT.Pt}) -> {PT.double(R, a) == PT.double(R, b) : PT.Pt}:
  Equal.cong(PT.Pt, PT.Pt, z => PT.double(R, z), a, b, e)

def cgn(+R: Nat, +a: PT.Pt, +b: PT.Pt, +e: {a == b : PT.Pt}) -> {PT.double_nt(R, a) == PT.double_nt(R, b) : PT.Pt}:
  Equal.cong(PT.Pt, PT.Pt, z => PT.double_nt(R, z), a, b, e)

def tr(+a: PT.Pt, +b: PT.Pt, +c: PT.Pt, +e1: {a == b : PT.Pt}, +e2: {b == c : PT.Pt}) -> {a == c : PT.Pt}:
  Equal.trans(PT.Pt, a, b, c, e1, e2)

# dbl4n == dbl4
def d4(+R: Nat, +p: PT.Pt) -> {PT.dbl4n(R, p) == PT.dbl4(R, p) : PT.Pt}:
  +n1 = PT.double_nt(R, p)
  +n2 = PT.double_nt(R, n1)
  +d1 = PT.double(R, p)
  +e1 = dd(R, n2)
  +e2b = tr(PT.double(R, PT.double_nt(R, n2)), PT.double(R, PT.double(R, n2)), PT.double(R, PT.double(R, PT.double(R, n1))), e1, cg(R, PT.double(R, n2), PT.double(R, PT.double(R, n1)), dd(R, n1)))
  tr(PT.double(R, PT.double_nt(R, n2)), PT.double(R, PT.double(R, PT.double(R, n1))), PT.double(R, PT.double(R, PT.double(R, d1))), e2b, cg(R, PT.double(R, PT.double(R, n1)), PT.double(R, PT.double(R, d1)), cg(R, PT.double(R, n1), PT.double(R, d1), dd(R, p))))

# a doubling does not read T
def dnt(+R: Nat, +p: PT.Pt, +q: PT.Cp) -> {PT.double_nt(R, PT.add_c_nt(R, p, q)) == PT.double_nt(R, PT.add_c(R, p, q)) : PT.Pt}:
  match p q:
    case PT.Pt{x, y, z, t} PT.Cp{a, b, c, d}:
      {==}

# dbl4 of a point depends on its first doubling only
def d4n(+R: Nat, +a: PT.Pt, +b: PT.Pt, +e: {PT.double_nt(R, a) == PT.double_nt(R, b) : PT.Pt}) -> {PT.dbl4n(R, a) == PT.dbl4n(R, b) : PT.Pt}:
  Equal.cong(PT.Pt, PT.Pt, z => PT.double(R, PT.double_nt(R, PT.double_nt(R, z))), PT.double_nt(R, a), PT.double_nt(R, b), e)

# the first doubling of winn is the first doubling of win
def wn(+R: Nat, +rw: List<&2, PT.Cp>, +ds: List<&2, Nat>) -> {PT.double_nt(R, PT.winn(R, rw, ds)) == PT.double_nt(R, PT.win(R, rw, ds)) : PT.Pt}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +dt}:
      +q = PT.nthc(d, rw)
      +A = PT.dbl4n(R, PT.winn(R, rw, dt))
      +B = PT.dbl4(R, PT.win(R, rw, dt))
      +eA = tr(A, PT.dbl4n(R, PT.win(R, rw, dt)), B, d4n(R, PT.winn(R, rw, dt), PT.win(R, rw, dt), wn(R, rw, dt)), d4(R, PT.win(R, rw, dt)))
      tr(PT.double_nt(R, PT.add_c_nt(R, A, q)), PT.double_nt(R, PT.add_c(R, A, q)), PT.double_nt(R, PT.add_c(R, B, q)), dnt(R, A, q), cgn(R, PT.add_c(R, A, q), PT.add_c(R, B, q), Equal.cong(PT.Pt, PT.Pt, z => PT.add_c(R, z, q), A, B, eA)))

def winf_eq(+R: Nat, +rw: List<&2, PT.Cp>, +ds: List<&2, Nat>) -> {PT.winf(R, rw, ds) == PT.win(R, rw, ds) : PT.Pt}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +dt}:
      +q = PT.nthc(d, rw)
      +eA = tr(PT.dbl4n(R, PT.winn(R, rw, dt)), PT.dbl4n(R, PT.win(R, rw, dt)), PT.dbl4(R, PT.win(R, rw, dt)), d4n(R, PT.winn(R, rw, dt), PT.win(R, rw, dt), wn(R, rw, dt)), d4(R, PT.win(R, rw, dt)))
      Equal.cong(PT.Pt, PT.Pt, z => PT.add_c(R, z, q), PT.dbl4n(R, PT.winn(R, rw, dt)), PT.dbl4(R, PT.win(R, rw, dt)), eA)
