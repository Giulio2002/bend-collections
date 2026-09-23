import Base
import ../lib/logic.bend as L
import ../spec/common.bend as SC
import ./frame.bend as FR
import ./path.bend as P
import ../lib/nat_list.bend as NL

# Membership bookkeeping for id lists without repeats: an id of one part is
# absent from the others, absence splits over appends, and an absent id
# differs from a present one. (source: tools/generators/tm_hand/dj.src)


def nm_l(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.memn(z, SC.append(Nat, a, b)) == False{} : Bool}) -> {NL.memn(z, a) == False{} : Bool}:
  FR.or_f_l(NL.memn(z, a), NL.memn(z, b), L.subst(Bool, w => {w == False{} : Bool}, NL.memn(z, SC.append(Nat, a, b)), Bool.or(NL.memn(z, a), NL.memn(z, b)), NL.memn_app(z, a, b), h))

def nm_r(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.memn(z, SC.append(Nat, a, b)) == False{} : Bool}) -> {NL.memn(z, b) == False{} : Bool}:
  FR.or_f_r(NL.memn(z, a), NL.memn(z, b), L.subst(Bool, w => {w == False{} : Bool}, NL.memn(z, SC.append(Nat, a, b)), Bool.or(NL.memn(z, a), NL.memn(z, b)), NL.memn_app(z, a, b), h))

def nm_ch(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {NL.memn(z, Con{i, t}) == False{} : Bool}) -> {Nat.is_eq(i, z) == False{} : Bool}:
  FR.or_f_l(Nat.is_eq(i, z), NL.memn(z, t), h)

def nm_ct(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {NL.memn(z, Con{i, t}) == False{} : Bool}) -> {NL.memn(z, t) == False{} : Bool}:
  FR.or_f_r(Nat.is_eq(i, z), NL.memn(z, t), h)

def nm_app(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {NL.memn(z, a) == False{} : Bool}, +hb: {NL.memn(z, b) == False{} : Bool}) -> {NL.memn(z, SC.append(Nat, a, b)) == False{} : Bool}:
  %Equal.sym(Bool, NL.memn(z, SC.append(Nat, a, b)), Bool.or(NL.memn(z, a), NL.memn(z, b)), NL.memn_app(z, a, b)) : {_ == False{} : Bool}
  %Equal.sym(Bool, NL.memn(z, a), False{}, ha) : {Bool.or(_, NL.memn(z, b)) == False{} : Bool}
  hb

def nm_cons(+z: Nat, +i: Nat, +t: List<&2, Nat>, +hi: {Nat.is_eq(i, z) == False{} : Bool}, +ht: {NL.memn(z, t) == False{} : Bool}) -> {NL.memn(z, Con{i, t}) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(i, z), False{}, hi) : {Bool.or(_, NL.memn(z, t)) == False{} : Bool}
  ht

# the head of a list without repeats is not in its tail
def nd_head(+i: Nat, +t: List<&2, Nat>, +h: {NL.nodupn(Con{i, t}) == True{} : Bool}) -> {NL.memn(i, t) == False{} : Bool}:
  NL.not_t_f(NL.memn(i, t), L.and_left(Bool.not(NL.memn(i, t)), NL.nodupn(t), h))

def nd_tail(+i: Nat, +t: List<&2, Nat>, +h: {NL.nodupn(Con{i, t}) == True{} : Bool}) -> {NL.nodupn(t) == True{} : Bool}:
  L.and_right(Bool.not(NL.memn(i, t)), NL.nodupn(t), h)

# an id of the right part is not in the left one, and conversely
def dj_l(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +z: Nat, +hz: {NL.memn(z, b) == True{} : Bool}) -> {NL.memn(z, a) == False{} : Bool}:
  NL.nd_dj(a, b, h, z, hz)

def dj_r(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}, +z: Nat, +hz: {NL.memn(z, a) == True{} : Bool}) -> {NL.memn(z, b) == False{} : Bool}:
  NL.nd_dj2(a, b, h, z, hz)

def ndl(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {NL.nodupn(a) == True{} : Bool}:
  NL.nd_l(a, b, h)

def ndr(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, a, b)) == True{} : Bool}) -> {NL.nodupn(b) == True{} : Bool}:
  NL.nd_r(a, b, h)

def mem_l(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.memn(z, a) == True{} : Bool}) -> {NL.memn(z, SC.append(Nat, a, b)) == True{} : Bool}:
  NL.mem_app_l(z, a, b, h)

def mem_r(+z: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +h: {NL.memn(z, b) == True{} : Bool}) -> {NL.memn(z, SC.append(Nat, a, b)) == True{} : Bool}:
  NL.mem_app_r(z, a, b, h)

def mem_hd(+i: Nat, +t: List<&2, Nat>) -> {NL.memn(i, Con{i, t}) == True{} : Bool}:
  P.mem_self(i, t)

def mem_tl(+z: Nat, +i: Nat, +t: List<&2, Nat>, +h: {NL.memn(z, t) == True{} : Bool}) -> {NL.memn(z, Con{i, t}) == True{} : Bool}:
  P.mem_cons(z, i, t, h)

# an absent id differs from a present one
def ne_nm(+a: Nat, +b: Nat, +xs: List<&2, Nat>, +ha: {NL.memn(a, xs) == False{} : Bool}, +hb: {NL.memn(b, xs) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  NL.not_t_f(Nat.is_eq(a, b), P.ne_mem(a, b, xs, ha, hb))
