import Base
import ../../../src/crypto/curve25519/fe.bend as FE
import ../../../src/crypto/curve25519/limbs.bend as LS
import ../../lib/nat.bend as N
import ../../lib/logic.bend as L
import ./pass.bend as PS

# Each straight-line operation of src/crypto/curve25519/fe.bend is its
# reference list algorithm (src/crypto/curve25519/limbs.bend) on the limbs:
# one evaluation per operation, on symbolic limbs (written by
# tools/gen_fe.py together with fe.bend).

def add_b(+R: Nat, +a: FE.Fe, +b: FE.Fe) -> {FE.to_list(FE.add(R, a, b)) == LS.add_l(R, FE.to_list(a), FE.to_list(b)) : List<&2, Nat>}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

def sub_b(+R: Nat, +a: FE.Fe, +b: FE.Fe) -> {FE.to_list(FE.sub(R, a, b)) == LS.sub_l(R, FE.to_list(a), FE.to_list(b)) : List<&2, Nat>}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

def mul_b(+R: Nat, +a: FE.Fe, +b: FE.Fe) -> {FE.to_list(FE.mul(R, a, b)) == LS.mul_l(R, FE.to_list(a), FE.to_list(b)) : List<&2, Nat>}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

def mul_small_b(+R: Nat, +a: FE.Fe, +k: Nat) -> {FE.to_list(FE.mul_small(R, a, k)) == LS.mul_small_l(R, FE.to_list(a), k) : List<&2, Nat>}:
  match a:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14}:
      {==}

def select_b(+s: U32, +a: FE.Fe, +b: FE.Fe) -> {FE.to_list(FE.select(s, a, b)) == LS.sel(U32.to_nat(s), FE.to_list(a), FE.to_list(b)) : List<&2, Nat>}:
  match a b:
    case FE.Fe{a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14} FE.Fe{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14}:
      {==}

# of_list inverts to_list on 15 limbs
def to_of(+zs: List<&2, Nat>, +hl: {PS.ln(zs) == 15n : Nat}) -> {FE.to_list(FE.of_list(zs)) == zs : List<&2, Nat>}:
  match zs:
    case Nil{}:
      Empty.absurd({FE.to_list(FE.of_list(Nil{})) == Nil{} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Nil{}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Nil{}), z) == True{} : Bool}, PS.ln(Nil{}), 15n, hl, N.is_eq_refl(PS.ln(Nil{}))))))
    case Con{+x0, +z1}:
      match z1:
        case Nil{}:
          Empty.absurd({FE.to_list(FE.of_list(Con{x0, Nil{}})) == Con{x0, Nil{}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Nil{}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Nil{}}), z) == True{} : Bool}, PS.ln(Con{x0, Nil{}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Nil{}}))))))
        case Con{+x1, +z2}:
          match z2:
            case Nil{}:
              Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Nil{}}})) == Con{x0, Con{x1, Nil{}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Nil{}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Nil{}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Nil{}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Nil{}}}))))))
            case Con{+x2, +z3}:
              match z3:
                case Nil{}:
                  Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Nil{}}}})) == Con{x0, Con{x1, Con{x2, Nil{}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Nil{}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Nil{}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Nil{}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Nil{}}}}))))))
                case Con{+x3, +z4}:
                  match z4:
                    case Nil{}:
                      Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Nil{}}}}}))))))
                    case Con{+x4, +z5}:
                      match z5:
                        case Nil{}:
                          Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Nil{}}}}}}))))))
                        case Con{+x5, +z6}:
                          match z6:
                            case Nil{}:
                              Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Nil{}}}}}}}))))))
                            case Con{+x6, +z7}:
                              match z7:
                                case Nil{}:
                                  Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Nil{}}}}}}}}))))))
                                case Con{+x7, +z8}:
                                  match z8:
                                    case Nil{}:
                                      Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Nil{}}}}}}}}}))))))
                                    case Con{+x8, +z9}:
                                      match z9:
                                        case Nil{}:
                                          Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Nil{}}}}}}}}}}))))))
                                        case Con{+x9, +z10}:
                                          match z10:
                                            case Nil{}:
                                              Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Nil{}}}}}}}}}}}))))))
                                            case Con{+x10, +z11}:
                                              match z11:
                                                case Nil{}:
                                                  Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Nil{}}}}}}}}}}}}))))))
                                                case Con{+x11, +z12}:
                                                  match z12:
                                                    case Nil{}:
                                                      Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Nil{}}}}}}}}}}}}}))))))
                                                    case Con{+x12, +z13}:
                                                      match z13:
                                                        case Nil{}:
                                                          Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Nil{}}}}}}}}}}}}}}))))))
                                                        case Con{+x13, +z14}:
                                                          match z14:
                                                            case Nil{}:
                                                              Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Nil{}}}}}}}}}}}}}}}))))))
                                                            case Con{+x14, +z15}:
                                                              match z15:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{+x15, +z16}:
                                                                  Empty.absurd({FE.to_list(FE.of_list(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}})) == Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}} : List<&2, Nat>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}}), 15n), True{}, {==}, L.subst(Nat, z => {Nat.is_eq(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}}), z) == True{} : Bool}, PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}}), 15n, hl, N.is_eq_refl(PS.ln(Con{x0, Con{x1, Con{x2, Con{x3, Con{x4, Con{x5, Con{x6, Con{x7, Con{x8, Con{x9, Con{x10, Con{x11, Con{x12, Con{x13, Con{x14, Con{x15, z16}}}}}}}}}}}}}}}}))))))
