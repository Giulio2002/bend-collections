import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../../spec/lib/common.bend as SC
import ../../lib/arith.bend as AT
import ../../../src/containers/bitset.bend as B
import ../../../src/containers/bitlist.bend as BLI
import ../../../src/containers/types/bitlist.bend as E
import ../../../spec/containers/bitset.bend as BS
import ../bitset/lists.bend as BL
import ../bitset/listx.bend as LX
import ../bitset/word.bend as W
import ../bitset/model.bend as MD
import ../bitset/state.bend as ST
import ../../../spec/containers/bitlist.bend as S

# List-level facts about the stored bits: F = ST.flat(ws) is every stored
# bit, the bitlist is its first n bits, and ST.invf(n, F) says n <= |F| and
# every stored bit from position n on is zero. These are the effects of
# push (in place or with a new word), pop, to_list and count on F, stated
# like the Lean 4 List lemmas they correspond to (List.take_succ,
# List.getElem_set, List.take_append_of_le_length, List.drop_append).
# (source: proofs/containers/bitlist/bits.src)


# ---- the zero tail ----

def nth_false(+xs: List<&2, Bool>, +n: Nat, +h: {Nat.is_lt(n, SC.length(Bool, xs)) == True{} : Bool}, +ht: {BL.allf(SC.drop(Bool, xs, n)) == True{} : Bool}) -> {SC.nth(Bool, xs, n) == Some{False{}} : Maybe<&2, Bool>}:
  match xs n:
    case Nil{} 0n:
      Empty.absurd({SC.nth(Bool, Nil{}, 0n) == Some{False{}} : Maybe<&2, Bool>}, L.false_true(h))
    case Nil{} 1n+p:
      Empty.absurd({SC.nth(Bool, Nil{}, 1n+p) == Some{False{}} : Maybe<&2, Bool>}, L.false_true(h))
    case Con{False{}, t} 0n:
      {==}
    case Con{True{}, t} 0n:
      Empty.absurd({SC.nth(Bool, Con{True{}, t}, 0n) == Some{False{}} : Maybe<&2, Bool>}, L.false_true(ht))
    case Con{False{}, +t} 1n+ +p:
      nth_false(t, p, h, ht)
    case Con{True{}, +t} 1n+ +p:
      nth_false(t, p, h, ht)

def allf_succ(+xs: List<&2, Bool>, +n: Nat, +ht: {BL.allf(SC.drop(Bool, xs, n)) == True{} : Bool}) -> {BL.allf(SC.drop(Bool, xs, 1n+n)) == True{} : Bool}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{False{}, +t} 0n:
      %Equal.sym(List<&2, Bool>, SC.drop(Bool, t, 0n), t, LX.drop_zero(Bool, t)) : {BL.allf(_) == True{} : Bool}
      ht
    case Con{True{}, t} 0n:
      Empty.absurd({BL.allf(SC.drop(Bool, Con{True{}, t}, 1n)) == True{} : Bool}, L.false_true(ht))
    case Con{False{}, +t} 1n+ +p:
      allf_succ(t, p, ht)
    case Con{True{}, +t} 1n+ +p:
      allf_succ(t, p, ht)

def invf_succ(+n: Nat, +xs: List<&2, Bool>, +h: {Nat.is_lt(n, SC.length(Bool, xs)) == True{} : Bool}, +g: {ST.invf(n, xs) == True{} : Bool}) -> {ST.invf(1n+n, xs) == True{} : Bool}:
  L.and_intro(Nat.is_le(1n+n, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, 1n+n)), N.lt_succ_le_succ(n, SC.length(Bool, xs), h), allf_succ(xs, n, ST.inv_tail(n, xs, g)))

# push of a zero bit into stored space: nothing is written
def push_zero(+n: Nat, +xs: List<&2, Bool>, +h: {Nat.is_lt(n, SC.length(Bool, xs)) == True{} : Bool}, +g: {ST.invf(n, xs) == True{} : Bool}) -> {SC.take(Bool, xs, 1n+n) == SC.snoc(Bool, SC.take(Bool, xs, n), False{}) : List<&2, Bool>}:
  LX.take_succ(Bool, xs, n, False{}, nth_false(xs, n, h, ST.inv_tail(n, xs, g)))

# push of any bit into stored space: bit n is written
def push_put(+n: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {Nat.is_lt(n, SC.length(Bool, xs)) == True{} : Bool}) -> {SC.take(Bool, SC.update(Bool, xs, n, v), 1n+n) == SC.snoc(Bool, SC.take(Bool, xs, n), v) : List<&2, Bool>}:
  LX.take_update_succ(Bool, xs, n, v, h)

def push_put_inv(+n: Nat, +xs: List<&2, Bool>, +v: Bool, +h: {Nat.is_lt(n, SC.length(Bool, xs)) == True{} : Bool}, +g: {ST.invf(n, xs) == True{} : Bool}) -> {ST.invf(1n+n, SC.update(Bool, xs, n, v)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Bool, SC.update(Bool, xs, n, v)), SC.length(Bool, xs), LL.length_update(Bool, xs, n, v)) : {Bool.and(Nat.is_le(1n+n, _), BL.allf(SC.drop(Bool, SC.update(Bool, xs, n, v), 1n+n))) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, SC.drop(Bool, SC.update(Bool, xs, n, v), 1n+n), SC.drop(Bool, xs, 1n+n), LX.drop_update(Bool, xs, n, v)) : {Bool.and(Nat.is_le(1n+n, SC.length(Bool, xs)), BL.allf(_)) == True{} : Bool}
  invf_succ(n, xs, h, g)

# ---- push into a new word ----


def flat_snoc(+ws: List<&2, U32>, +x: U32) -> {ST.flat(SC.snoc(U32, ws, x)) == SC.append(Bool, ST.flat(ws), W.ubits(x)) : List<&2, Bool>}:
  match ws:
    case Nil{}:
      LL.append_nil(Bool, W.ubits(x))
    case Con{+w, +t}:
      %Equal.sym(List<&2, Bool>, ST.flat(SC.snoc(U32, t, x)), SC.append(Bool, ST.flat(t), W.ubits(x)), flat_snoc(t, x)) : {SC.append(Bool, W.ubits(w), _) == SC.append(Bool, SC.append(Bool, W.ubits(w), ST.flat(t)), W.ubits(x)) : List<&2, Bool>}
      Equal.sym(List<&2, Bool>, SC.append(Bool, SC.append(Bool, W.ubits(w), ST.flat(t)), W.ubits(x)), SC.append(Bool, W.ubits(w), SC.append(Bool, ST.flat(t), W.ubits(x))), LL.append_assoc(Bool, W.ubits(w), ST.flat(t), W.ubits(x)))

def sub_succ_self(+n: Nat) -> {Nat.sub(1n+n, n) == 1n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      sub_succ_self(p)

def first_bit(+v: Bool) -> {SC.take(Bool, W.ubits(B.word_put(v, 0, 0n)), 1n) == Con{v, Nil{}} : List<&2, Bool>}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def rest_zero(+v: Bool) -> {BL.allf(SC.drop(Bool, W.ubits(B.word_put(v, 0, 0n)), 1n)) == True{} : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def drop_append_succ(+xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {SC.drop(Bool, SC.append(Bool, xs, ys), 1n+SC.length(Bool, xs)) == SC.drop(Bool, ys, 1n) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      drop_append_succ(t, ys)

# the new word holds bit |F| = v in its low position, zeros above
def push_new_abs(+ws: List<&2, U32>, +v: Bool) -> {SC.take(Bool, ST.flat(SC.snoc(U32, ws, B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))) == SC.snoc(Bool, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), v) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, ST.flat(SC.snoc(U32, ws, B.word_put(v, 0, 0n))), SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), flat_snoc(ws, B.word_put(v, 0, 0n))) : {SC.take(Bool, _, 1n+SC.length(Bool, ST.flat(ws))) == SC.snoc(Bool, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), v) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))), SC.append(Bool, ST.flat(ws), SC.take(Bool, W.ubits(B.word_put(v, 0, 0n)), Nat.sub(1n+SC.length(Bool, ST.flat(ws)), SC.length(Bool, ST.flat(ws))))), LL.sc_take_append_right(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n)), 1n+SC.length(Bool, ST.flat(ws)), N.le_succ(SC.length(Bool, ST.flat(ws))))) : {_ == SC.snoc(Bool, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), v) : List<&2, Bool>}
  %Equal.sym(Nat, Nat.sub(1n+SC.length(Bool, ST.flat(ws)), SC.length(Bool, ST.flat(ws))), 1n, sub_succ_self(SC.length(Bool, ST.flat(ws)))) : {SC.append(Bool, ST.flat(ws), SC.take(Bool, W.ubits(B.word_put(v, 0, 0n)), _)) == SC.snoc(Bool, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), v) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, W.ubits(B.word_put(v, 0, 0n)), 1n), Con{v, Nil{}}, first_bit(v)) : {SC.append(Bool, ST.flat(ws), _) == SC.snoc(Bool, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), v) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(ws), SC.length(Bool, ST.flat(ws))), ST.flat(ws), LX.take_all(Bool, ST.flat(ws))) : {SC.append(Bool, ST.flat(ws), Con{v, Nil{}}) == SC.snoc(Bool, _, v) : List<&2, Bool>}
  Equal.sym(List<&2, Bool>, SC.snoc(Bool, ST.flat(ws), v), SC.append(Bool, ST.flat(ws), Con{v, Nil{}}), LL.snoc_append(Bool, ST.flat(ws), v))

def push_new_inv(+ws: List<&2, U32>, +v: Bool) -> {ST.invf(1n+SC.length(Bool, ST.flat(ws)), ST.flat(SC.snoc(U32, ws, B.word_put(v, 0, 0n)))) == True{} : Bool}:
  %Equal.sym(List<&2, Bool>, ST.flat(SC.snoc(U32, ws, B.word_put(v, 0, 0n))), SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), flat_snoc(ws, B.word_put(v, 0, 0n))) : {ST.invf(1n+SC.length(Bool, ST.flat(ws)), _) == True{} : Bool}
  %Equal.sym(Nat, SC.length(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n)))), Nat.add(SC.length(Bool, ST.flat(ws)), SC.length(Bool, W.ubits(B.word_put(v, 0, 0n)))), LL.length_append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n)))) : {Bool.and(Nat.is_le(1n+SC.length(Bool, ST.flat(ws)), _), BL.allf(SC.drop(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))))) == True{} : Bool}
  %Equal.sym(Nat, SC.length(Bool, W.ubits(B.word_put(v, 0, 0n))), 32n, W.ulen(B.word_put(v, 0, 0n))) : {Bool.and(Nat.is_le(1n+SC.length(Bool, ST.flat(ws)), Nat.add(SC.length(Bool, ST.flat(ws)), _)), BL.allf(SC.drop(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(SC.length(Bool, ST.flat(ws)), 32n), 1n+Nat.add(SC.length(Bool, ST.flat(ws)), 31n), N.add_succ(SC.length(Bool, ST.flat(ws)), 31n)) : {Bool.and(Nat.is_le(1n+SC.length(Bool, ST.flat(ws)), _), BL.allf(SC.drop(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))))) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, SC.drop(Bool, SC.append(Bool, ST.flat(ws), W.ubits(B.word_put(v, 0, 0n))), 1n+SC.length(Bool, ST.flat(ws))), SC.drop(Bool, W.ubits(B.word_put(v, 0, 0n)), 1n), drop_append_succ(ST.flat(ws), W.ubits(B.word_put(v, 0, 0n)))) : {Bool.and(Nat.is_le(1n+SC.length(Bool, ST.flat(ws)), 1n+Nat.add(SC.length(Bool, ST.flat(ws)), 31n)), BL.allf(_)) == True{} : Bool}
  L.and_intro(Nat.is_le(1n+SC.length(Bool, ST.flat(ws)), 1n+Nat.add(SC.length(Bool, ST.flat(ws)), 31n)), BL.allf(SC.drop(Bool, W.ubits(B.word_put(v, 0, 0n)), 1n)), N.le_add_right(SC.length(Bool, ST.flat(ws)), 31n), rest_zero(v))

# ---- pop ----

def pop_spec(+l: Maybe<&2, Nat>, +c: Nat, +ys: List<&2, Bool>, +b: Bool) -> {S.pop(l, c, SC.snoc(Bool, ys, b)) == (S.M{l, c, ys}, E.OBit{Done{b}}) : S.Model & E.Obs}:
  match ys:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Bool>, SC.init(Bool, SC.snoc(Bool, Con{h, t}, b)), Con{h, t}, LL.init_snoc(Bool, Con{h, t}, b)) : {(S.M{l, c, _}, E.OBit{S.last_bit(SC.last(Bool, SC.snoc(Bool, Con{h, t}, b)))}) == (S.M{l, c, Con{h, t}}, E.OBit{Done{b}}) : S.Model & E.Obs}
      %Equal.sym(Maybe<&2, Bool>, SC.last(Bool, SC.snoc(Bool, Con{h, t}, b)), Some{b}, LL.last_snoc(Bool, Con{h, t}, b)) : {(S.M{l, c, Con{h, t}}, E.OBit{S.last_bit(_)}) == (S.M{l, c, Con{h, t}}, E.OBit{Done{b}}) : S.Model & E.Obs}
      {==}

def lt_of_inv(+m: Nat, +xs: List<&2, Bool>, +g: {ST.invf(1n+m, xs) == True{} : Bool}) -> {Nat.is_lt(m, SC.length(Bool, xs)) == True{} : Bool}:
  N.succ_le_lt(m, SC.length(Bool, xs), ST.inv_le(1n+m, xs, g))

# a zero last bit: the stored bits stay as they are
def pop_keep_inv(+m: Nat, +xs: List<&2, Bool>, +g: {ST.invf(1n+m, xs) == True{} : Bool}, +hb: {SC.nth(Bool, xs, m) == Some{False{}} : Maybe<&2, Bool>}) -> {ST.invf(m, xs) == True{} : Bool}:
  %Equal.sym(List<&2, Bool>, SC.drop(Bool, xs, m), Con{False{}, SC.drop(Bool, xs, 1n+m)}, LX.drop_cons(Bool, xs, m, False{}, hb)) : {Bool.and(Nat.is_le(m, SC.length(Bool, xs)), BL.allf(_)) == True{} : Bool}
  L.and_intro(Nat.is_le(m, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, 1n+m)), N.lt_le(m, SC.length(Bool, xs), lt_of_inv(m, xs, g)), ST.inv_tail(1n+m, xs, g))

# a one last bit is cleared
def pop_clear_inv(+m: Nat, +xs: List<&2, Bool>, +g: {ST.invf(1n+m, xs) == True{} : Bool}) -> {ST.invf(m, SC.update(Bool, xs, m, False{})) == True{} : Bool}:
  +hz = LL.nth_update_same(Bool, xs, m, False{}, lt_of_inv(m, xs, g))
  %Equal.sym(List<&2, Bool>, SC.drop(Bool, SC.update(Bool, xs, m, False{}), m), Con{False{}, SC.drop(Bool, SC.update(Bool, xs, m, False{}), 1n+m)}, LX.drop_cons(Bool, SC.update(Bool, xs, m, False{}), m, False{}, hz)) : {Bool.and(Nat.is_le(m, SC.length(Bool, SC.update(Bool, xs, m, False{}))), BL.allf(_)) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, SC.drop(Bool, SC.update(Bool, xs, m, False{}), 1n+m), SC.drop(Bool, xs, 1n+m), LX.drop_update(Bool, xs, m, False{})) : {Bool.and(Nat.is_le(m, SC.length(Bool, SC.update(Bool, xs, m, False{}))), BL.allf(_)) == True{} : Bool}
  %Equal.sym(Nat, SC.length(Bool, SC.update(Bool, xs, m, False{})), SC.length(Bool, xs), LL.length_update(Bool, xs, m, False{})) : {Bool.and(Nat.is_le(m, _), BL.allf(SC.drop(Bool, xs, 1n+m))) == True{} : Bool}
  L.and_intro(Nat.is_le(m, SC.length(Bool, xs)), BL.allf(SC.drop(Bool, xs, 1n+m)), N.lt_le(m, SC.length(Bool, xs), lt_of_inv(m, xs, g)), ST.inv_tail(1n+m, xs, g))

# ---- to_list: one word of the first n bits ----

def word_bits(+m: Nat, +x: U32, +rest: List<&2, Bool>, +h: {Nat.is_le(m, 32n) == True{} : Bool}) -> {BLI.word_bits(m, x, rest) == SC.append(Bool, SC.take(Bool, W.ubits(x), m), rest) : List<&2, Bool>}:
  match m x:
    case 0n U32{w}:
      match w:
        case WCon{b, t}:
          {==}
    case 1n+ +p U32{w}:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Bool, B.low(U32{WCon{b, t}}), b, W.low_word(b, t)) : {Con{_, BLI.word_bits(p, U32.shr(U32{WCon{b, t}}), rest)} == Con{b, SC.append(Bool, SC.take(Bool, W.wbits(31n, t), p), rest)} : List<&2, Bool>}
          %Equal.sym(List<&2, Bool>, BLI.word_bits(p, U32.shr(U32{WCon{b, t}}), rest), SC.append(Bool, SC.take(Bool, W.ubits(U32.shr(U32{WCon{b, t}})), p), rest), word_bits(p, U32.shr(U32{WCon{b, t}}), rest, N.le_trans(p, 1n+p, 32n, N.le_succ(p), h))) : {Con{b, _} == Con{b, SC.append(Bool, SC.take(Bool, W.wbits(31n, t), p), rest)} : List<&2, Bool>}
          %Equal.sym(List<&2, Bool>, W.ubits(U32.shr(U32{WCon{b, t}})), SC.snoc(Bool, W.wbits(31n, t), False{}), W.u_shr(b, t)) : {Con{b, SC.append(Bool, SC.take(Bool, _, p), rest)} == Con{b, SC.append(Bool, SC.take(Bool, W.wbits(31n, t), p), rest)} : List<&2, Bool>}
          %Equal.sym(List<&2, Bool>, SC.snoc(Bool, W.wbits(31n, t), False{}), SC.append(Bool, W.wbits(31n, t), Con{False{}, Nil{}}), LL.snoc_append(Bool, W.wbits(31n, t), False{})) : {Con{b, SC.append(Bool, SC.take(Bool, _, p), rest)} == Con{b, SC.append(Bool, SC.take(Bool, W.wbits(31n, t), p), rest)} : List<&2, Bool>}
          +h31 = L.subst(Nat, z => {Nat.is_le(p, z) == True{} : Bool}, 31n, SC.length(Bool, W.wbits(31n, t)), Equal.sym(Nat, SC.length(Bool, W.wbits(31n, t)), 31n, W.len_wbits(31n, t)), h)
          %Equal.sym(List<&2, Bool>, SC.take(Bool, SC.append(Bool, W.wbits(31n, t), Con{False{}, Nil{}}), p), SC.take(Bool, W.wbits(31n, t), p), LL.sc_take_append_left(Bool, W.wbits(31n, t), Con{False{}, Nil{}}, p, h31)) : {Con{b, SC.append(Bool, _, rest)} == Con{b, SC.append(Bool, SC.take(Bool, W.wbits(31n, t), p), rest)} : List<&2, Bool>}
          {==}

def sub_le_zero(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, L.false_true(h))
    case 1n+ +p 1n+ +r:
      sub_le_zero(p, r, h)

def sub_sub(+b: Nat, +a: Nat, +c: Nat) -> {Nat.sub(Nat.sub(a, b), c) == Nat.sub(a, Nat.add(c, b)) : Nat}:
  match b a:
    case 0n 0n:
      %Equal.sym(Nat, Nat.add(c, 0n), c, N.add_zero(c)) : {Nat.sub(0n, c) == Nat.sub(0n, _) : Nat}
      {==}
    case 0n 1n+ +q:
      %Equal.sym(Nat, Nat.add(c, 0n), c, N.add_zero(c)) : {Nat.sub(1n+q, c) == Nat.sub(1n+q, _) : Nat}
      {==}
    case 1n+ +p 0n:
      %Equal.sym(Nat, Nat.add(c, 1n+p), 1n+Nat.add(c, p), N.add_succ(c, p)) : {Nat.sub(0n, c) == Nat.sub(0n, _) : Nat}
      sub_le_zero(0n, c, N.zero_le(c))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Nat, Nat.add(c, 1n+p), 1n+Nat.add(c, p), N.add_succ(c, p)) : {Nat.sub(Nat.sub(q, p), c) == Nat.sub(1n+q, _) : Nat}
      sub_sub(p, q, c)

# the first s bits of 32 bits then more: a prefix of the word, then of the rest
def take_word(+a: List<&2, Bool>, +bs: List<&2, Bool>, +s: Nat, +ha: {SC.length(Bool, a) == 32n : Nat}, c: Bool, +ec: {Nat.is_lt(32n, s) == c : Bool}) -> {SC.take(Bool, SC.append(Bool, a, bs), s) == SC.append(Bool, SC.take(Bool, a, Nat.min(32n, s)), SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.min(32n, s), 32n, N.min_left(32n, s, ec)) : {SC.take(Bool, SC.append(Bool, a, bs), s) == SC.append(Bool, SC.take(Bool, a, _), SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}
      +hle = L.subst(Nat, z => {Nat.is_le(z, s) == True{} : Bool}, 32n, SC.length(Bool, a), Equal.sym(Nat, SC.length(Bool, a), 32n, ha), N.lt_le(32n, s, ec))
      %Equal.sym(List<&2, Bool>, SC.take(Bool, SC.append(Bool, a, bs), s), SC.append(Bool, a, SC.take(Bool, bs, Nat.sub(s, SC.length(Bool, a)))), LL.sc_take_append_right(Bool, a, bs, s, hle)) : {_ == SC.append(Bool, SC.take(Bool, a, 32n), SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}
      %Equal.sym(Nat, SC.length(Bool, a), 32n, ha) : {SC.append(Bool, a, SC.take(Bool, bs, Nat.sub(s, _))) == SC.append(Bool, SC.take(Bool, a, 32n), SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}
      +ht = L.subst(Nat, z => {SC.take(Bool, a, z) == a : List<&2, Bool>}, SC.length(Bool, a), 32n, ha, LX.take_all(Bool, a))
      %Equal.sym(List<&2, Bool>, SC.take(Bool, a, 32n), a, ht) : {SC.append(Bool, a, SC.take(Bool, bs, Nat.sub(s, 32n))) == SC.append(Bool, _, SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.min(32n, s), s, N.min_right(32n, s, ec)) : {SC.take(Bool, SC.append(Bool, a, bs), s) == SC.append(Bool, SC.take(Bool, a, _), SC.take(Bool, bs, Nat.sub(s, 32n))) : List<&2, Bool>}
      +hs = N.not_lt_le(32n, s, ec)
      %Equal.sym(Nat, Nat.sub(s, 32n), 0n, sub_le_zero(s, 32n, hs)) : {SC.take(Bool, SC.append(Bool, a, bs), s) == SC.append(Bool, SC.take(Bool, a, s), SC.take(Bool, bs, _)) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, SC.take(Bool, bs, 0n), Nil{}, LL.sc_take_zero(Bool, bs)) : {SC.take(Bool, SC.append(Bool, a, bs), s) == SC.append(Bool, SC.take(Bool, a, s), _) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, SC.append(Bool, SC.take(Bool, a, s), Nil{}), SC.take(Bool, a, s), LL.append_nil(Bool, SC.take(Bool, a, s))) : {SC.take(Bool, SC.append(Bool, a, bs), s) == _ : List<&2, Bool>}
      LL.sc_take_append_left(Bool, a, bs, s, L.subst(Nat, z => {Nat.is_le(s, z) == True{} : Bool}, 32n, SC.length(Bool, a), Equal.sym(Nat, SC.length(Bool, a), 32n, ha), hs))

def min_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+ +p 1n+ +r:
      min_le(p, r)


# word q of the first n bits: words q.. restricted to bits below n
def bits_step(+ws: List<&2, U32>, +n: Nat, +q: Nat, +x: U32, +hx: {SC.nth(U32, ws, q) == Some{x} : Maybe<&2, U32>}) -> {SC.take(Bool, ST.flat(SC.drop(U32, ws, q)), Nat.sub(n, Nat.mul(q, 32n))) == BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))) : List<&2, Bool>}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, ws, q), Con{x, SC.drop(U32, ws, 1n+q)}, LX.drop_cons(U32, ws, q, x, hx)) : {SC.take(Bool, ST.flat(_), Nat.sub(n, Nat.mul(q, 32n))) == BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))) : List<&2, Bool>}
  %sub_sub(Nat.mul(q, 32n), n, 32n) : {SC.take(Bool, SC.append(Bool, W.ubits(x), ST.flat(SC.drop(U32, ws, 1n+q))), Nat.sub(n, Nat.mul(q, 32n))) == BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), _)) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, SC.take(Bool, SC.append(Bool, W.ubits(x), ST.flat(SC.drop(U32, ws, 1n+q))), Nat.sub(n, Nat.mul(q, 32n))), SC.append(Bool, SC.take(Bool, W.ubits(x), Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n)))), SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(Nat.sub(n, Nat.mul(q, 32n)), 32n))), take_word(W.ubits(x), ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(n, Nat.mul(q, 32n)), W.ulen(x), Nat.is_lt(32n, Nat.sub(n, Nat.mul(q, 32n))), {==})) : {_ == BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(Nat.sub(n, Nat.mul(q, 32n)), 32n))) : List<&2, Bool>}
  Equal.sym(List<&2, Bool>, BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(Nat.sub(n, Nat.mul(q, 32n)), 32n))), SC.append(Bool, SC.take(Bool, W.ubits(x), Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n)))), SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(Nat.sub(n, Nat.mul(q, 32n)), 32n))), word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), x, SC.take(Bool, ST.flat(SC.drop(U32, ws, 1n+q)), Nat.sub(Nat.sub(n, Nat.mul(q, 32n)), 32n)), min_le(32n, Nat.sub(n, Nat.mul(q, 32n)))))

# ---- push helpers ----

def below_eq(+l: Maybe<&2, Nat>, +n: Nat) -> {BLI.below(l, n) == S.below(l, n) : Bool}:
  match l:
    case None{}:
      {==}
    case Some{k}:
      {==}

def upd_snoc_end(+p: List<&2, Bool>, +x: Bool, +v: Bool) -> {SC.update(Bool, SC.snoc(Bool, p, x), SC.length(Bool, p), v) == SC.snoc(Bool, p, v) : List<&2, Bool>}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      LL.cons_cong(Bool, h, SC.update(Bool, SC.snoc(Bool, t, x), SC.length(Bool, t), v), SC.snoc(Bool, t, v), upd_snoc_end(t, x, v))

def lt_plus(+k: Nat, +x: Nat) -> {Nat.is_lt(x, Nat.add(1n+k, x)) == True{} : Bool}:
  match k:
    case 0n:
      N.lt_succ(x)
    case 1n+ +p:
      N.lt_le_trans(x, Nat.add(1n+p, x), 1n+Nat.add(1n+p, x), lt_plus(p, x), N.le_succ(Nat.add(1n+p, x)))

def lt_mul32(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)) == True{} : Bool}:
  +h1 = AT.mul_le(1n+a, b, 32n, N.lt_succ_le_succ(a, b, h))
  N.lt_le_trans(Nat.mul(a, 32n), Nat.mul(1n+a, 32n), Nat.mul(b, 32n), lt_plus(31n, Nat.mul(a, 32n)), h1)

def mul32_lt(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}, +h: {Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, L.true_not_false(Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)), h, N.le_not_lt(Nat.mul(a, 32n), Nat.mul(b, 32n), AT.mul_le(b, a, 32n, N.not_lt_le(a, b, ec)))))

def mul32_nlt(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}, +h: {Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)) == False{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match c:
    case False{}:
      ec
    case True{}:
      Empty.absurd({Nat.is_lt(a, b) == False{} : Bool}, L.true_not_false(Nat.is_lt(Nat.mul(a, 32n), Nat.mul(b, 32n)), lt_mul32(a, b, ec), h))
