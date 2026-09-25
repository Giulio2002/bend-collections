import Base
import ../../../src/crypto/keccak/types.bend as T

# 64-bit lanes are specified by two 32-bit halves, low half first.
def xor(a: T.Lane, b: T.Lane) -> T.Lane:
  match a b:
    case T.W{al,ah} T.W{bl,bh}: T.W{U32.xor(al,bl),U32.xor(ah,bh)}

def chi(a: T.Lane, b: T.Lane, c: T.Lane) -> T.Lane:
  match a b c:
    case T.W{al,ah} T.W{bl,bh} T.W{cl,ch}:
      T.W{U32.xor(al,U32.and(U32.xor(bl,4294967295),cl)),U32.xor(ah,U32.and(U32.xor(bh,4294967295),ch))}

def rotate_small(+lo: U32, +hi: U32, +n: Nat) -> T.Lane:
  T.W{U32.or(U32.shln(lo,n),U32.shrn(hi,Nat.sub(32n,n))),U32.or(U32.shln(hi,n),U32.shrn(lo,Nat.sub(32n,n)))}

def rotate_nonzero(lo: U32, hi: U32, +n: Nat, b: Bool) -> T.Lane:
  match b:
    case True{}: rotate_small(lo,hi,n)
    case False{}: rotate_small(hi,lo,Nat.sub(n,32n))

def rotate(a: T.Lane, +n: Nat) -> T.Lane:
  match a n:
    case T.W{lo,hi} 0n: T.W{lo,hi}
    case T.W{lo,hi} 32n: T.W{hi,lo}
    case T.W{lo,hi} n: rotate_nonzero(lo,hi,n,Nat.is_lt(n,32n))

def at(s: T.State, i: Nat) -> T.Lane:
  match s i:
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 0n: a0
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 1n: a1
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 2n: a2
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 3n: a3
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 4n: a4
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 5n: a5
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 6n: a6
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 7n: a7
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 8n: a8
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 9n: a9
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 10n: a10
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 11n: a11
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 12n: a12
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 13n: a13
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 14n: a14
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 15n: a15
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 16n: a16
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 17n: a17
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 18n: a18
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 19n: a19
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 20n: a20
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 21n: a21
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 22n: a22
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 23n: a23
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24} 24n: a24
    case _ _: T.W{0,0}

def column(+s: T.State, +x: Nat) -> T.Lane:
  xor(at(s,x),xor(at(s,Nat.add(x,5n)),xor(at(s,Nat.add(x,10n)),xor(at(s,Nat.add(x,15n)),at(s,Nat.add(x,20n))))))

def theta_lane(+s: T.State, +x: Nat, y: Nat) -> T.Lane:
  xor(at(s,Nat.add(x,Nat.mul(5n,y))),xor(column(s,Nat.mod(Nat.add(x,4n),5n)),rotate(column(s,Nat.mod(Nat.add(x,1n),5n)),1n)))

def theta(+s: T.State) -> T.State:
  T.S{theta_lane(s,0n,0n),theta_lane(s,1n,0n),theta_lane(s,2n,0n),theta_lane(s,3n,0n),theta_lane(s,4n,0n),theta_lane(s,0n,1n),theta_lane(s,1n,1n),theta_lane(s,2n,1n),theta_lane(s,3n,1n),theta_lane(s,4n,1n),theta_lane(s,0n,2n),theta_lane(s,1n,2n),theta_lane(s,2n,2n),theta_lane(s,3n,2n),theta_lane(s,4n,2n),theta_lane(s,0n,3n),theta_lane(s,1n,3n),theta_lane(s,2n,3n),theta_lane(s,3n,3n),theta_lane(s,4n,3n),theta_lane(s,0n,4n),theta_lane(s,1n,4n),theta_lane(s,2n,4n),theta_lane(s,3n,4n),theta_lane(s,4n,4n)}

def rho_pi(+s: T.State) -> T.State:
  T.S{rotate(at(s,0n),0n),rotate(at(s,6n),44n),rotate(at(s,12n),43n),rotate(at(s,18n),21n),rotate(at(s,24n),14n),rotate(at(s,3n),28n),rotate(at(s,9n),20n),rotate(at(s,10n),3n),rotate(at(s,16n),45n),rotate(at(s,22n),61n),rotate(at(s,1n),1n),rotate(at(s,7n),6n),rotate(at(s,13n),25n),rotate(at(s,19n),8n),rotate(at(s,20n),18n),rotate(at(s,4n),27n),rotate(at(s,5n),36n),rotate(at(s,11n),10n),rotate(at(s,17n),15n),rotate(at(s,23n),56n),rotate(at(s,2n),62n),rotate(at(s,8n),55n),rotate(at(s,14n),39n),rotate(at(s,15n),41n),rotate(at(s,21n),2n)}

def chi_state(+s: T.State) -> T.State:
  T.S{chi(at(s,0n),at(s,1n),at(s,2n)),chi(at(s,1n),at(s,2n),at(s,3n)),chi(at(s,2n),at(s,3n),at(s,4n)),chi(at(s,3n),at(s,4n),at(s,0n)),chi(at(s,4n),at(s,0n),at(s,1n)),chi(at(s,5n),at(s,6n),at(s,7n)),chi(at(s,6n),at(s,7n),at(s,8n)),chi(at(s,7n),at(s,8n),at(s,9n)),chi(at(s,8n),at(s,9n),at(s,5n)),chi(at(s,9n),at(s,5n),at(s,6n)),chi(at(s,10n),at(s,11n),at(s,12n)),chi(at(s,11n),at(s,12n),at(s,13n)),chi(at(s,12n),at(s,13n),at(s,14n)),chi(at(s,13n),at(s,14n),at(s,10n)),chi(at(s,14n),at(s,10n),at(s,11n)),chi(at(s,15n),at(s,16n),at(s,17n)),chi(at(s,16n),at(s,17n),at(s,18n)),chi(at(s,17n),at(s,18n),at(s,19n)),chi(at(s,18n),at(s,19n),at(s,15n)),chi(at(s,19n),at(s,15n),at(s,16n)),chi(at(s,20n),at(s,21n),at(s,22n)),chi(at(s,21n),at(s,22n),at(s,23n)),chi(at(s,22n),at(s,23n),at(s,24n)),chi(at(s,23n),at(s,24n),at(s,20n)),chi(at(s,24n),at(s,20n),at(s,21n))}

def iota(s: T.State, rc: T.Lane) -> T.State:
  match s:
    case T.S{a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}:
      T.S{xor(a0,rc),a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24}

def round(s: T.State, rc: T.Lane) -> T.State:
  iota(chi_state(rho_pi(theta(s))),rc)

def constant(i: Nat) -> T.Lane:
  match i:
    case 0n: T.W{1,0}
    case 1n: T.W{32898,0}
    case 2n: T.W{32906,2147483648}
    case 3n: T.W{2147516416,2147483648}
    case 4n: T.W{32907,0}
    case 5n: T.W{2147483649,0}
    case 6n: T.W{2147516545,2147483648}
    case 7n: T.W{32777,2147483648}
    case 8n: T.W{138,0}
    case 9n: T.W{136,0}
    case 10n: T.W{2147516425,0}
    case 11n: T.W{2147483658,0}
    case 12n: T.W{2147516555,0}
    case 13n: T.W{139,2147483648}
    case 14n: T.W{32905,2147483648}
    case 15n: T.W{32771,2147483648}
    case 16n: T.W{32770,2147483648}
    case 17n: T.W{128,2147483648}
    case 18n: T.W{32778,0}
    case 19n: T.W{2147483658,2147483648}
    case 20n: T.W{2147516545,2147483648}
    case 21n: T.W{32896,2147483648}
    case 22n: T.W{2147483649,0}
    case 23n: T.W{2147516424,2147483648}
    case _: T.W{0,0}

def rounds(n: Nat, +i: Nat, s: T.State) -> T.State:
  match n:
    case 0n: s
    case 1n+p: rounds(p,1n+i,round(s,constant(i)))

def permute(s: T.State) -> T.State:
  rounds(24n,0n,s)
