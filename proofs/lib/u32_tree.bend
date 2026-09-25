import Base
import ./logic.bend as L
import ./array.bend as AR
import ../../spec/lib/common.bend as SC
import ./u32div.bend as UD
import ./words32.bend as W32

# Perfect trees of U32 (AR.Tree) read and written at a U32 index below their
# size: the value read, and perfection and slots kept by an update.

def len_of(-T: Data, +d: Nat, +t: AR.Tree<T>, +pf: {AR.perfect(T, d, t) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(i, SC.length(T, AR.slots(T, t))) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, SC.pow2(d), SC.length(T, AR.slots(T, t)), Equal.sym(Nat, SC.length(T, AR.slots(T, t)), SC.pow2(d), AR.slots_length(T, d, t, pf)), hi)

def uget(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}) -> {Array.get(U32, AR.thaw(U32, t), i) == (AR.thaw(U32, t), W32.nth0(AR.slots(U32, t), UD.v(i))) : Array<U32> & U32}:
  AR.get(U32, d, t, i, W32.nth0(AR.slots(U32, t), UD.v(i)), hd, hi, W32.nth_some(AR.slots(U32, t), UD.v(i), len_of(U32, d, t, pf, UD.v(i), hi)), pf)

def uset_a(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: U32, +hi: {Nat.is_lt(UD.v(i), SC.pow2(d)) == True{} : Bool}, +x: U32) -> {Array.set(U32, AR.thaw(U32, t), i, x) == AR.thaw(U32, AR.upd(U32, d, t, UD.v(i), x)) : Array<U32>}:
  AR.set(U32, d, t, i, x, W32.nth0(AR.slots(U32, t), UD.v(i)), hd, hi, W32.nth_some(AR.slots(U32, t), UD.v(i), len_of(U32, d, t, pf, UD.v(i), hi)), pf)

def uset_p(+d: Nat, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: Nat, +x: U32) -> {AR.perfect(U32, d, AR.upd(U32, d, t, i, x)) == True{} : Bool}:
  AR.upd_perfect(U32, d, t, i, x, pf)

def uset_s(+d: Nat, +t: AR.Tree<U32>, +pf: {AR.perfect(U32, d, t) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +x: U32) -> {AR.slots(U32, AR.upd(U32, d, t, i, x)) == SC.update(U32, AR.slots(U32, t), i, x) : List<&2, U32>}:
  AR.upd_slots(U32, d, t, i, x, hi, pf)
