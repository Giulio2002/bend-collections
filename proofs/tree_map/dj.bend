import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ./frame.bend as FR
import ./path.bend as P

# Membership bookkeeping for id lists without repeats: an id of one part is
# absent from the others, absence splits over appends, and an absent id
# differs from a present one. (source: tools/generators/tm_hand/dj.src)


def nm_l(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {HT.memn(z, SC.append(Nat, a, b)) == False{} : Bool}) -> {HT.memn(z, a) == False{} : Bool}:
  FR.or_f_l(HT.memn(z, a), HT.memn(z, b), L.subst(Bool, w => {w == False{} : Bool}, HT.memn(z, SC.append(Nat, a, b)), Bool.or(HT.memn(z, a), HT.memn(z, b)), LS.memn_app(z, a, b), h))

def nm_r(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {HT.memn(z, SC.append(Nat, a, b)) == False{} : Bool}) -> {HT.memn(z, b) == False{} : Bool}:
  FR.or_f_r(HT.memn(z, a), HT.memn(z, b), L.subst(Bool, w => {w == False{} : Bool}, HT.memn(z, SC.append(Nat, a, b)), Bool.or(HT.memn(z, a), HT.memn(z, b)), LS.memn_app(z, a, b), h))

def nm_ch(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {HT.memn(z, Con{i, t}) == False{} : Bool}) -> {Nat.is_eq(i, z) == False{} : Bool}:
  FR.or_f_l(Nat.is_eq(i, z), HT.memn(z, t), h)

def nm_ct(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {HT.memn(z, Con{i, t}) == False{} : Bool}) -> {HT.memn(z, t) == False{} : Bool}:
  FR.or_f_r(Nat.is_eq(i, z), HT.memn(z, t), h)

def nm_app(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {HT.memn(z, a) == False{} : Bool}, +hb: {HT.memn(z, b) == False{} : Bool}) -> {HT.memn(z, SC.append(Nat, a, b)) == False{} : Bool}:
  %Equal.sym(Bool, HT.memn(z, SC.append(Nat, a, b)), Bool.or(HT.memn(z, a), HT.memn(z, b)), LS.memn_app(z, a, b)) : {_ == False{} : Bool}
  %Equal.sym(Bool, HT.memn(z, a), False{}, ha) : {Bool.or(_, HT.memn(z, b)) == False{} : Bool}
  hb

def nm_cons(+z: Nat, +i: Nat, +t: List<&2, Nat>, +hi: {Nat.is_eq(i, z) == False{} : Bool}, +ht: {HT.memn(z, t) == False{} : Bool}) -> {HT.memn(z, Con{i, t}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(i, z), False{}, hi) : {Bool.or(_, HT.memn(z, t)) == False{} : Bool}
  ht

# the head of a list without repeats is not in its tail
def nd_head(+i: Nat, +t: List<&2, Nat>, +h: {LST.nodupn(Con{i, t}) == True{} : Bool}) -> {HT.memn(i, t) == False{} : Bool}:
  LS.not_t_f(HT.memn(i, t), L.and_left(Bool.not(HT.memn(i, t)), LST.nodupn(t), h))

def nd_tail(+i: Nat, +t: List<&2, Nat>, +h: {LST.nodupn(Con{i, t}) == True{} : Bool}) -> {LST.nodupn(t) == True{} : Bool}:
  L.and_right(Bool.not(HT.memn(i, t)), LST.nodupn(t), h)

# an id of the right part is not in the left one, and conversely
def dj_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +z: Nat, +hz: {HT.memn(z, b) == True{} : Bool}) -> {HT.memn(z, a) == False{} : Bool}:
  LS.nd_dj(a, b, h, z, hz)

def dj_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +z: Nat, +hz: {HT.memn(z, a) == True{} : Bool}) -> {HT.memn(z, b) == False{} : Bool}:
  LS.nd_dj2(a, b, h, z, hz)

def ndl(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {LST.nodupn(a) == True{} : Bool}:
  LS.nd_l(a, b, h)

def ndr(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {LST.nodupn(b) == True{} : Bool}:
  LS.nd_r(a, b, h)

def mem_l(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {HT.memn(z, a) == True{} : Bool}) -> {HT.memn(z, SC.append(Nat, a, b)) == True{} : Bool}:
  LS.mem_app_l(z, a, b, h)

def mem_r(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {HT.memn(z, b) == True{} : Bool}) -> {HT.memn(z, SC.append(Nat, a, b)) == True{} : Bool}:
  LS.mem_app_r(z, a, b, h)

def mem_hd(+i: Nat, +t: List<&2, Nat>) -> {HT.memn(i, Con{i, t}) == True{} : Bool}:
  P.mem_self(i, t)

def mem_tl(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {HT.memn(z, t) == True{} : Bool}) -> {HT.memn(z, Con{i, t}) == True{} : Bool}:
  P.mem_cons(z, i, t, h)

# an absent id differs from a present one
def ne_nm(+a: Nat, +b: Nat, +xs: List<&2, Nat>, +ha: {HT.memn(a, xs) == False{} : Bool}, +hb: {HT.memn(b, xs) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  LS.not_t_f(Nat.is_eq(a, b), P.ne_mem(a, b, xs, ha, hb))
