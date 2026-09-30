import Base
import ../../../src/crypto/secp256k1/fe.bend as F
import ../../../src/crypto/secp256k1/pt.bend as PX

# The register programs of the RCB formulas on field records (proof only):
# registers 0.. are the inputs, each instruction appends one register;
# RMulB{i, j} is the product by the register i holding b3 = 21 (F.mul21). The
# straight-line formulas of src/crypto/secp256k1/pt.bend are these programs
# run (ptbr.bend); ptp.bend follows the values register by register.

type ROp is Data:
  RAdd{i: Nat, j: Nat}
  RSub{i: Nat, j: Nat}
  RMul{i: Nat, j: Nat}
  RSq{i: Nat}
  RMulB{i: Nat, j: Nat}

def rnth(i: Nat, regs: List<&2, F.FE>) -> F.FE:
  match i regs:
    case _ Nil{}: F.zero()
    case 0n r <> t: r
    case 1n+k r <> t: rnth(k, t)

def rexec(op: ROp, +regs: List<&2, F.FE>) -> F.FE:
  match op:
    case RAdd{i, j}: F.add(rnth(i, regs), rnth(j, regs))
    case RSub{i, j}: F.sub(rnth(i, regs), rnth(j, regs))
    case RMul{i, j}: F.mul(rnth(i, regs), rnth(j, regs))
    case RSq{i}: F.sq(rnth(i, regs))
    case RMulB{i, j}: F.mul21(rnth(j, regs))

def rrun_go(prog: List<&2, ROp>, +regs: List<&2, F.FE>) -> List<&2, F.FE>:
  match prog:
    case Nil{}: regs
    case op <> t: rrun_go(t, List.append(&2, F.FE, regs, [rexec(op, regs)]))

# (the first register is looked at first, so that on unknown registers the
# proof checker keeps the run folded; the result is rrun_go's)
def rrun(prog: List<&2, ROp>, regs: List<&2, F.FE>) -> List<&2, F.FE>:
  match regs:
    case Nil{}: rrun_go(prog, Nil{})
    case F.FE{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15} <> t: rrun_go(prog, F.FE{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15} <> t)

# RCB Algorithm 7 (a = 0): registers X1 Y1 Z1 X2 Y2 Z2 b3 = 0..6; the result
# is X3 Y3 Z3 = registers 33, 36, 39
def radd_prog() -> List<&2, ROp>:
  [RMul{0n, 3n}, RMul{1n, 4n}, RMul{2n, 5n}, RAdd{0n, 1n}, RAdd{3n, 4n},
   RMul{10n, 11n}, RAdd{7n, 8n}, RSub{12n, 13n}, RAdd{1n, 2n}, RAdd{4n, 5n},
   RMul{15n, 16n}, RAdd{8n, 9n}, RSub{17n, 18n}, RAdd{0n, 2n}, RAdd{3n, 5n},
   RMul{20n, 21n}, RAdd{7n, 9n}, RSub{22n, 23n}, RAdd{7n, 7n}, RAdd{25n, 7n},
   RMulB{6n, 9n}, RAdd{8n, 27n}, RSub{8n, 27n}, RMulB{6n, 24n}, RMul{19n, 30n},
   RMul{14n, 29n}, RSub{32n, 31n}, RMul{30n, 26n}, RMul{29n, 28n}, RAdd{35n, 34n},
   RMul{26n, 14n}, RMul{28n, 19n}, RAdd{38n, 37n}]

# RCB Algorithm 9 (a = 0): registers X Y Z b3 = 0..3; the result is
# X3 Y3 Z3 = registers 21, 18, 13 (Y Y and Z Z are squares)
def rdbl_prog() -> List<&2, ROp>:
  [RSq{1n}, RAdd{4n, 4n}, RAdd{5n, 5n}, RAdd{6n, 6n}, RMul{1n, 2n},
   RSq{2n}, RMulB{3n, 9n}, RMul{10n, 7n}, RAdd{4n, 10n}, RMul{8n, 7n},
   RAdd{10n, 10n}, RAdd{14n, 10n}, RSub{4n, 15n}, RMul{16n, 12n}, RAdd{11n, 17n},
   RMul{0n, 1n}, RMul{16n, 19n}, RAdd{20n, 20n}]

def regs7(p: PX.PT, q: PX.PT) -> List<&2, F.FE>:
  match p q:
    case PX.PT{x1, y1, z1} PX.PT{x2, y2, z2}: [x1, y1, z1, x2, y2, z2, PX.b3()]

def regs4(p: PX.PT) -> List<&2, F.FE>:
  match p:
    case PX.PT{x, y, z}: [x, y, z, PX.b3()]

def add_out(+r: List<&2, F.FE>) -> PX.PT:
  PX.PT{rnth(33n, r), rnth(36n, r), rnth(39n, r)}

def dbl_out(+r: List<&2, F.FE>) -> PX.PT:
  PX.PT{rnth(21n, r), rnth(18n, r), rnth(13n, r)}
