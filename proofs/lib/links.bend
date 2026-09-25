import Base
import ../../src/containers/hash_table.bend as H
import ./u32.bend as UW
import ../../spec/lib/common.bend as SC
import ./nat_list.bend as NL
import ./logic.bend as L
import ./nat.bend as N
import ./u32div.bend as UD
import ./words32.bend as W32
import ./word.bend as WD

# Ids linked through U32 words: lnk(s) is the link word of slot s, fst_or and
# last_or the link of a list's first and last id (or a default), and how they
# behave over appends and reversed appends.

def lnk(+s: Nat) -> U32:
  H.link(U32.from_nat(s))

def fst_or(t: List<&2, Nat>, +q: U32) -> U32:
  match t:
    case Nil{}:
      q
    case Con{+s, t2}:
      lnk(s)

def last_or(t: List<&2, Nat>, +p: U32) -> U32:
  match t:
    case Nil{}:
      p
    case Con{+s, +t2}:
      last_or(t2, lnk(s))

def u_refl(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  UW.u32_eq_refl(x)

def fst_app(+a: List<&2, Nat>, +b: List<&2, Nat>, +q: U32) -> {fst_or(SC.append(Nat, a, b), q) == fst_or(a, fst_or(b, q)) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

def last_app(+a: List<&2, Nat>, +b: List<&2, Nat>, +p: U32) -> {last_or(SC.append(Nat, a, b), p) == last_or(b, last_or(a, p)) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      last_app(t, b, lnk(h))

def last_lnk(+t: List<&2, Nat>, +a: Nat) -> {last_or(t, lnk(a)) == lnk(NL.lastn(t, a)) : U32}:
  match t:
    case Nil{}:
      {==}
    case Con{+b, +t2}:
      last_lnk(t2, b)

def fo_rapp(+l: List<&2, Nat>, +b: List<&2, Nat>, +d: U32) -> {fst_or(NL.rapp(l, b), d) == last_or(l, fst_or(b, d)) : U32}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      fo_rapp(r, Con{x, b}, d)

def slot_link(+one: Nat, +h1: {one == 1n : Nat}, +s: U32, +hs: {Nat.is_lt(1n+UD.v(s), WD.sc(32n, one)) == True{} : Bool}) -> {UD.v(H.slot(H.link(s))) == UD.v(s) : Nat}:
  +lv = W32.link_val(one, h1, s, hs)
  +hle = L.subst(Nat, z => {Nat.is_le(1n, z) == True{} : Bool}, 1n+UD.v(s), UD.v(H.link(s)), Equal.sym(Nat, UD.v(H.link(s)), 1n+UD.v(s), lv), N.zero_le(UD.v(s)))
  Equal.trans(Nat, UD.v(H.slot(H.link(s))), Nat.sub(UD.v(H.link(s)), 1n), UD.v(s), UW.sub_nat(H.link(s), 1, hle), Equal.trans(Nat, Nat.sub(UD.v(H.link(s)), 1n), Nat.sub(1n+UD.v(s), 1n), UD.v(s), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), UD.v(H.link(s)), 1n+UD.v(s), lv), N.sub_zero(UD.v(s))))

def slot_lnk(+one: Nat, +h1: {one == 1n : Nat}, +s: Nat, +sd: Nat, +hsd: {Nat.is_lt(1n+sd, 32n) == True{} : Bool}, +hs: {Nat.is_lt(s, SC.pow2(sd)) == True{} : Bool}) -> {UD.v(H.slot(lnk(s))) == s : Nat}:
  +hk = N.lt_le(sd, 32n, N.lt_trans(sd, 1n+sd, 32n, N.lt_succ(sd), hsd))
  +e1 = UW.to_nat_from_nat(s, sd, hk, hs)
  +hs2 = L.subst(Nat, z => {Nat.is_lt(z, SC.pow2(sd)) == True{} : Bool}, s, UD.v(U32.from_nat(s)), Equal.sym(Nat, UD.v(U32.from_nat(s)), s, e1), hs)
  Equal.trans(Nat, UD.v(H.slot(lnk(s))), UD.v(U32.from_nat(s)), s, slot_link(one, h1, U32.from_nat(s), W32.bound32(one, h1, UD.v(U32.from_nat(s)), sd, hsd, hs2)), e1)
