import Base
import ./types.bend as T
import ./lane.bend as L

def initial() -> T.State:
  T.S{T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0},T.W{0,0}}

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

def round(s: T.State, rc: T.Lane) -> T.State:
  match s:
    case T.S{+a0,+a1,+a2,+a3,+a4,+a5,+a6,+a7,+a8,+a9,+a10,+a11,+a12,+a13,+a14,+a15,+a16,+a17,+a18,+a19,+a20,+a21,+a22,+a23,+a24}:
      +c0 = L.xor(a0,L.xor(a5,L.xor(a10,L.xor(a15,a20))))
      +c1 = L.xor(a1,L.xor(a6,L.xor(a11,L.xor(a16,a21))))
      +c2 = L.xor(a2,L.xor(a7,L.xor(a12,L.xor(a17,a22))))
      +c3 = L.xor(a3,L.xor(a8,L.xor(a13,L.xor(a18,a23))))
      +c4 = L.xor(a4,L.xor(a9,L.xor(a14,L.xor(a19,a24))))
      +d0 = L.xor(c4,L.rol1(c1))
      +d1 = L.xor(c0,L.rol1(c2))
      +d2 = L.xor(c1,L.rol1(c3))
      +d3 = L.xor(c2,L.rol1(c4))
      +d4 = L.xor(c3,L.rol1(c0))
      +b0 = L.rol0(L.xor(a0,d0))
      +b10 = L.rol1(L.xor(a1,d1))
      +b20 = L.rol62(L.xor(a2,d2))
      +b5 = L.rol28(L.xor(a3,d3))
      +b15 = L.rol27(L.xor(a4,d4))
      +b16 = L.rol36(L.xor(a5,d0))
      +b1 = L.rol44(L.xor(a6,d1))
      +b11 = L.rol6(L.xor(a7,d2))
      +b21 = L.rol55(L.xor(a8,d3))
      +b6 = L.rol20(L.xor(a9,d4))
      +b7 = L.rol3(L.xor(a10,d0))
      +b17 = L.rol10(L.xor(a11,d1))
      +b2 = L.rol43(L.xor(a12,d2))
      +b12 = L.rol25(L.xor(a13,d3))
      +b22 = L.rol39(L.xor(a14,d4))
      +b23 = L.rol41(L.xor(a15,d0))
      +b8 = L.rol45(L.xor(a16,d1))
      +b18 = L.rol15(L.xor(a17,d2))
      +b3 = L.rol21(L.xor(a18,d3))
      +b13 = L.rol8(L.xor(a19,d4))
      +b14 = L.rol18(L.xor(a20,d0))
      +b24 = L.rol2(L.xor(a21,d1))
      +b9 = L.rol61(L.xor(a22,d2))
      +b19 = L.rol56(L.xor(a23,d3))
      +b4 = L.rol14(L.xor(a24,d4))
      T.S{L.xor(L.chi(b0,b1,b2),rc),L.chi(b1,b2,b3),L.chi(b2,b3,b4),L.chi(b3,b4,b0),L.chi(b4,b0,b1),L.chi(b5,b6,b7),L.chi(b6,b7,b8),L.chi(b7,b8,b9),L.chi(b8,b9,b5),L.chi(b9,b5,b6),L.chi(b10,b11,b12),L.chi(b11,b12,b13),L.chi(b12,b13,b14),L.chi(b13,b14,b10),L.chi(b14,b10,b11),L.chi(b15,b16,b17),L.chi(b16,b17,b18),L.chi(b17,b18,b19),L.chi(b18,b19,b15),L.chi(b19,b15,b16),L.chi(b20,b21,b22),L.chi(b21,b22,b23),L.chi(b22,b23,b24),L.chi(b23,b24,b20),L.chi(b24,b20,b21)}

def rounds_short(n: Nat, +i: Nat, s: T.State) -> T.State:
  match n:
    case 0n: s
    case 1n+p: rounds_short(p,1n+i,round(s,constant(i)))

def rounds(n: Nat, +i: Nat, s: T.State) -> T.State:
  match n s:
    case 0n s: s
    case 1n s: rounds_short(1n,i,s)
    case 2n+p T.S{+a0,+a1,+a2,+a3,+a4,+a5,+a6,+a7,+a8,+a9,+a10,+a11,+a12,+a13,+a14,+a15,+a16,+a17,+a18,+a19,+a20,+a21,+a22,+a23,+a24}:
      rc0 = constant(i)
      +c0r0 = L.xor(a0,L.xor(a5,L.xor(a10,L.xor(a15,a20))))
      +c1r0 = L.xor(a1,L.xor(a6,L.xor(a11,L.xor(a16,a21))))
      +c2r0 = L.xor(a2,L.xor(a7,L.xor(a12,L.xor(a17,a22))))
      +c3r0 = L.xor(a3,L.xor(a8,L.xor(a13,L.xor(a18,a23))))
      +c4r0 = L.xor(a4,L.xor(a9,L.xor(a14,L.xor(a19,a24))))
      +d0r0 = L.xor(c4r0,L.rol1(c1r0))
      +d1r0 = L.xor(c0r0,L.rol1(c2r0))
      +d2r0 = L.xor(c1r0,L.rol1(c3r0))
      +d3r0 = L.xor(c2r0,L.rol1(c4r0))
      +d4r0 = L.xor(c3r0,L.rol1(c0r0))
      +b0r0 = L.rol0(L.xor(a0,d0r0))
      +b1r0 = L.rol44(L.xor(a6,d1r0))
      +b2r0 = L.rol43(L.xor(a12,d2r0))
      +b3r0 = L.rol21(L.xor(a18,d3r0))
      +b4r0 = L.rol14(L.xor(a24,d4r0))
      +a0r1 = L.xor(L.chi(b0r0,b1r0,b2r0),rc0)
      +a1r1 = L.chi(b1r0,b2r0,b3r0)
      +a2r1 = L.chi(b2r0,b3r0,b4r0)
      +a3r1 = L.chi(b3r0,b4r0,b0r0)
      +a4r1 = L.chi(b4r0,b0r0,b1r0)
      +b5r0 = L.rol28(L.xor(a3,d3r0))
      +b6r0 = L.rol20(L.xor(a9,d4r0))
      +b7r0 = L.rol3(L.xor(a10,d0r0))
      +b8r0 = L.rol45(L.xor(a16,d1r0))
      +b9r0 = L.rol61(L.xor(a22,d2r0))
      +a5r1 = L.chi(b5r0,b6r0,b7r0)
      +a6r1 = L.chi(b6r0,b7r0,b8r0)
      +a7r1 = L.chi(b7r0,b8r0,b9r0)
      +a8r1 = L.chi(b8r0,b9r0,b5r0)
      +a9r1 = L.chi(b9r0,b5r0,b6r0)
      +b10r0 = L.rol1(L.xor(a1,d1r0))
      +b11r0 = L.rol6(L.xor(a7,d2r0))
      +b12r0 = L.rol25(L.xor(a13,d3r0))
      +b13r0 = L.rol8(L.xor(a19,d4r0))
      +b14r0 = L.rol18(L.xor(a20,d0r0))
      +a10r1 = L.chi(b10r0,b11r0,b12r0)
      +a11r1 = L.chi(b11r0,b12r0,b13r0)
      +a12r1 = L.chi(b12r0,b13r0,b14r0)
      +a13r1 = L.chi(b13r0,b14r0,b10r0)
      +a14r1 = L.chi(b14r0,b10r0,b11r0)
      +b15r0 = L.rol27(L.xor(a4,d4r0))
      +b16r0 = L.rol36(L.xor(a5,d0r0))
      +b17r0 = L.rol10(L.xor(a11,d1r0))
      +b18r0 = L.rol15(L.xor(a17,d2r0))
      +b19r0 = L.rol56(L.xor(a23,d3r0))
      +a15r1 = L.chi(b15r0,b16r0,b17r0)
      +a16r1 = L.chi(b16r0,b17r0,b18r0)
      +a17r1 = L.chi(b17r0,b18r0,b19r0)
      +a18r1 = L.chi(b18r0,b19r0,b15r0)
      +a19r1 = L.chi(b19r0,b15r0,b16r0)
      +b20r0 = L.rol62(L.xor(a2,d2r0))
      +b21r0 = L.rol55(L.xor(a8,d3r0))
      +b22r0 = L.rol39(L.xor(a14,d4r0))
      +b23r0 = L.rol41(L.xor(a15,d0r0))
      +b24r0 = L.rol2(L.xor(a21,d1r0))
      +a20r1 = L.chi(b20r0,b21r0,b22r0)
      +a21r1 = L.chi(b21r0,b22r0,b23r0)
      +a22r1 = L.chi(b22r0,b23r0,b24r0)
      +a23r1 = L.chi(b23r0,b24r0,b20r0)
      +a24r1 = L.chi(b24r0,b20r0,b21r0)
      rc1 = constant(1n+i)
      +c0r1 = L.xor(a0r1,L.xor(a5r1,L.xor(a10r1,L.xor(a15r1,a20r1))))
      +c1r1 = L.xor(a1r1,L.xor(a6r1,L.xor(a11r1,L.xor(a16r1,a21r1))))
      +c2r1 = L.xor(a2r1,L.xor(a7r1,L.xor(a12r1,L.xor(a17r1,a22r1))))
      +c3r1 = L.xor(a3r1,L.xor(a8r1,L.xor(a13r1,L.xor(a18r1,a23r1))))
      +c4r1 = L.xor(a4r1,L.xor(a9r1,L.xor(a14r1,L.xor(a19r1,a24r1))))
      +d0r1 = L.xor(c4r1,L.rol1(c1r1))
      +d1r1 = L.xor(c0r1,L.rol1(c2r1))
      +d2r1 = L.xor(c1r1,L.rol1(c3r1))
      +d3r1 = L.xor(c2r1,L.rol1(c4r1))
      +d4r1 = L.xor(c3r1,L.rol1(c0r1))
      +b0r1 = L.rol0(L.xor(a0r1,d0r1))
      +b1r1 = L.rol44(L.xor(a6r1,d1r1))
      +b2r1 = L.rol43(L.xor(a12r1,d2r1))
      +b3r1 = L.rol21(L.xor(a18r1,d3r1))
      +b4r1 = L.rol14(L.xor(a24r1,d4r1))
      +out0 = L.xor(L.chi(b0r1,b1r1,b2r1),rc1)
      +out1 = L.chi(b1r1,b2r1,b3r1)
      +out2 = L.chi(b2r1,b3r1,b4r1)
      +out3 = L.chi(b3r1,b4r1,b0r1)
      +out4 = L.chi(b4r1,b0r1,b1r1)
      +b5r1 = L.rol28(L.xor(a3r1,d3r1))
      +b6r1 = L.rol20(L.xor(a9r1,d4r1))
      +b7r1 = L.rol3(L.xor(a10r1,d0r1))
      +b8r1 = L.rol45(L.xor(a16r1,d1r1))
      +b9r1 = L.rol61(L.xor(a22r1,d2r1))
      +out5 = L.chi(b5r1,b6r1,b7r1)
      +out6 = L.chi(b6r1,b7r1,b8r1)
      +out7 = L.chi(b7r1,b8r1,b9r1)
      +out8 = L.chi(b8r1,b9r1,b5r1)
      +out9 = L.chi(b9r1,b5r1,b6r1)
      +b10r1 = L.rol1(L.xor(a1r1,d1r1))
      +b11r1 = L.rol6(L.xor(a7r1,d2r1))
      +b12r1 = L.rol25(L.xor(a13r1,d3r1))
      +b13r1 = L.rol8(L.xor(a19r1,d4r1))
      +b14r1 = L.rol18(L.xor(a20r1,d0r1))
      +out10 = L.chi(b10r1,b11r1,b12r1)
      +out11 = L.chi(b11r1,b12r1,b13r1)
      +out12 = L.chi(b12r1,b13r1,b14r1)
      +out13 = L.chi(b13r1,b14r1,b10r1)
      +out14 = L.chi(b14r1,b10r1,b11r1)
      +b15r1 = L.rol27(L.xor(a4r1,d4r1))
      +b16r1 = L.rol36(L.xor(a5r1,d0r1))
      +b17r1 = L.rol10(L.xor(a11r1,d1r1))
      +b18r1 = L.rol15(L.xor(a17r1,d2r1))
      +b19r1 = L.rol56(L.xor(a23r1,d3r1))
      +out15 = L.chi(b15r1,b16r1,b17r1)
      +out16 = L.chi(b16r1,b17r1,b18r1)
      +out17 = L.chi(b17r1,b18r1,b19r1)
      +out18 = L.chi(b18r1,b19r1,b15r1)
      +out19 = L.chi(b19r1,b15r1,b16r1)
      +b20r1 = L.rol62(L.xor(a2r1,d2r1))
      +b21r1 = L.rol55(L.xor(a8r1,d3r1))
      +b22r1 = L.rol39(L.xor(a14r1,d4r1))
      +b23r1 = L.rol41(L.xor(a15r1,d0r1))
      +b24r1 = L.rol2(L.xor(a21r1,d1r1))
      +out20 = L.chi(b20r1,b21r1,b22r1)
      +out21 = L.chi(b21r1,b22r1,b23r1)
      +out22 = L.chi(b22r1,b23r1,b24r1)
      +out23 = L.chi(b23r1,b24r1,b20r1)
      +out24 = L.chi(b24r1,b20r1,b21r1)
      rounds(p,2n+i,T.S{out0,out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24})

def permute(s: T.State) -> T.State:
  rounds(24n,0n,s)
