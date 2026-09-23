import Base
import ../lib/logic.bend as L
import ../../src/containers/hash_table.bend as H

# Check words, bit by bit (generic in the width; U32 is width 32 = 1 + 31).
#   top(p)   the word with only its top bit set  (U32: 2^31, H.tag())
#   low(p)   every bit but the top one            (U32: 2^31 - 1)
#   one(p)   the word 1

def top(+p: Nat) -> Word(1n+p):
  match p:
    case 0n:
      WCon{True{}, WNil{}}
    case 1n+q:
      WCon{False{}, top(q)}

def low(+p: Nat) -> Word(1n+p):
  match p:
    case 0n:
      WCon{False{}, WNil{}}
    case 1n+q:
      WCon{True{}, low(q)}

def one(+p: Nat) -> Word(2n+p):
  WCon{True{}, Word.zero(1n+p)}

# the top bit
def topb(+p: Nat, w: Word(1n+p)) -> Bool:
  match p w:
    case 0n WCon{b, WNil{}}:
      b
    case 1n+q WCon{b, t}:
      topb(q, t)

def tag_top() -> {H.tag() == U32{top(31n)} : U32}:
  {==}

def low_lit() -> {2147483647 == U32{low(31n)} : U32}:
  {==}

def one_lit() -> {1 == U32{one(30n)} : U32}:
  {==}

def zero_lit() -> {0 == U32{Word.zero(32n)} : U32}:
  {==}

# ---- comparison with the top bit ----

def ge_fin_false(+c: Cmp, +b: Bool) -> {Cmp.is_ge(Word.cmp.fin(b, False{}, c)) == Cmp.is_ge(c) : Bool}:
  match c b:
    case LT{} _:
      {==}
    case EQ{} True{}:
      {==}
    case EQ{} False{}:
      {==}
    case GT{} _:
      {==}

def ge_top_leaf(+b: Bool) -> {Cmp.is_ge(Word.cmp(1n, WCon{b, WNil{}}, top(0n))) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# w >= 2^p is its top bit
def ge_top(+p: Nat, +w: Word(1n+p)) -> {Cmp.is_ge(Word.cmp(1n+p, w, top(p))) == topb(p, w) : Bool}:
  match p w:
    case 0n WCon{b, WNil{}}:
      ge_top_leaf(b)
    case 1n+q WCon{b, t}:
      Equal.trans(Bool, Cmp.is_ge(Word.cmp.fin(b, False{}, Word.cmp(1n+q, t, top(q)))), Cmp.is_ge(Word.cmp(1n+q, t, top(q))), topb(q, t), ge_fin_false(Word.cmp(1n+q, t, top(q)), b), ge_top(q, t))

# ---- or / and with top and low ----

def or_true(+b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def or_false(+b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false(+b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def topb_or_top(+p: Nat, +x: Word(1n+p)) -> {topb(p, Word.or(1n+p, x, top(p))) == True{} : Bool}:
  match p x:
    case 0n WCon{b, WNil{}}:
      or_true(b)
    case 1n+q WCon{b, t}:
      topb_or_top(q, t)

def topb_and_low(+p: Nat, +x: Word(1n+p)) -> {topb(p, Word.and(1n+p, x, low(p))) == False{} : Bool}:
  match p x:
    case 0n WCon{b, WNil{}}:
      and_false(b)
    case 1n+q WCon{b, t}:
      topb_and_low(q, t)

def topb_or(+p: Nat, +x: Word(1n+p), +y: Word(1n+p)) -> {topb(p, Word.or(1n+p, x, y)) == Bool.or(topb(p, x), topb(p, y)) : Bool}:
  match p x y:
    case 0n WCon{a, WNil{}} WCon{b, WNil{}}:
      {==}
    case 1n+q WCon{a, s} WCon{b, t}:
      topb_or(q, s, t)

def topb_zero(+p: Nat) -> {topb(p, Word.zero(1n+p)) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      topb_zero(q)

def topb_one(+p: Nat) -> {topb(1n+p, one(p)) == False{} : Bool}:
  topb_zero(p)

# clearing the top bit of x with the top bit set gives back x without it
def and_low_or_top(+p: Nat, +x: Word(1n+p), +h: {topb(p, x) == False{} : Bool}) -> {Word.and(1n+p, Word.or(1n+p, x, top(p)), low(p)) == x : Word(1n+p)}:
  match p x:
    case 0n WCon{b, WNil{}}:
      Equal.cong(Bool, Word(1n), c => WCon{c, WNil{}}, Bool.and(Bool.or(b, True{}), False{}), b, Equal.trans(Bool, Bool.and(Bool.or(b, True{}), False{}), False{}, b, and_false(Bool.or(b, True{})), Equal.sym(Bool, b, False{}, h)))
    case 1n+q WCon{b, t}:
      +e1 = Equal.trans(Bool, Bool.and(Bool.or(b, False{}), True{}), Bool.or(b, False{}), b, and_true(Bool.or(b, False{})), or_false(b))
      +e2 = and_low_or_top(q, t, h)
      Equal.trans(Word(2n+q), WCon{Bool.and(Bool.or(b, False{}), True{}), Word.and(1n+q, Word.or(1n+q, t, top(q)), low(q))}, WCon{b, Word.and(1n+q, Word.or(1n+q, t, top(q)), low(q))}, WCon{b, t},
        Equal.cong(Bool, Word(2n+q), c => WCon{c, Word.and(1n+q, Word.or(1n+q, t, top(q)), low(q))}, Bool.and(Bool.or(b, False{}), True{}), b, e1),
        Equal.cong(Word(1n+q), Word(2n+q), w => WCon{b, w}, Word.and(1n+q, Word.or(1n+q, t, top(q)), low(q)), t, e2))

# ---- nonzero words ----

def eq_fin_false(+b: Bool, +c: Cmp, +h: {Cmp.is_eq(c) == False{} : Bool}) -> {Cmp.is_eq(Word.cmp.fin(b, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_eq(Word.cmp.fin(b, False{}, EQ{})) == False{} : Bool}, L.true_false(h))
    case GT{}:
      {==}

def top_nonzero_g(+p: Nat, +w: Word(1n+p), +h: {topb(p, w) == True{} : Bool}) -> {Cmp.is_eq(Word.cmp(1n+p, w, Word.zero(1n+p))) == False{} : Bool}:
  match p w:
    case 0n WCon{True{}, WNil{}}:
      {==}
    case 0n WCon{False{}, WNil{}}:
      Empty.absurd({Cmp.is_eq(Word.cmp(1n, WCon{False{}, WNil{}}, Word.zero(1n))) == False{} : Bool}, L.false_true(h))
    case 1n+q WCon{b, t}:
      eq_fin_false(b, Word.cmp(1n+q, t, Word.zero(1n+q)), top_nonzero_g(q, t, h))

def fin_tf(+c: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def bit0_nonzero(+p: Nat, +t: Word(p)) -> {Cmp.is_eq(Word.cmp(1n+p, WCon{True{}, t}, Word.zero(1n+p))) == False{} : Bool}:
  fin_tf(Word.cmp(p, t, Word.zero(p)))

# ---- the U32 check words ----

def lt_ge(+c: Cmp) -> {Cmp.is_lt(c) == Bool.not(Cmp.is_ge(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

# a code below 2^31 has its top bit clear
def small_top(+cw: Word(32n), +h: {U32.is_lt(U32{cw}, H.tag()) == True{} : Bool}) -> {topb(31n, cw) == False{} : Bool}:
  +c = Word.cmp(32n, cw, top(31n))
  not_true(topb(31n, cw), Equal.trans(Bool, Bool.not(topb(31n, cw)), Bool.not(Cmp.is_ge(c)), True{}, Equal.cong(Bool, Bool, z => Bool.not(z), topb(31n, cw), Cmp.is_ge(c), Equal.sym(Bool, Cmp.is_ge(c), topb(31n, cw), ge_top(31n, cw))), Equal.trans(Bool, Bool.not(Cmp.is_ge(c)), Cmp.is_lt(c), True{}, Equal.sym(Bool, Cmp.is_lt(c), Bool.not(Cmp.is_ge(c)), lt_ge(c)), h)))

def is_short_top(+w: Word(32n)) -> {H.is_short(U32{w}) == topb(31n, w) : Bool}:
  ge_top(31n, w)

def short_is_short(+c: U32) -> {H.is_short(H.short_word(c)) == True{} : Bool}:
  match c:
    case U32{+cw}:
      Equal.trans(Bool, H.is_short(U32{Word.or(32n, cw, top(31n))}), topb(31n, Word.or(32n, cw, top(31n))), True{}, is_short_top(Word.or(32n, cw, top(31n))), topb_or_top(31n, cw))

def short_nonzero(+c: U32) -> {U32.is_eq(H.short_word(c), 0) == False{} : Bool}:
  match c:
    case U32{+cw}:
      top_nonzero_g(31n, Word.or(32n, cw, top(31n)), topb_or_top(31n, cw))

# masking a short word gives back its character code
def short_back(+c: U32, +h: {U32.is_lt(c, H.tag()) == True{} : Bool}) -> {U32.and(H.short_word(c), 2147483647) == c : U32}:
  match c:
    case U32{+cw}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, Word.or(32n, cw, top(31n)), low(31n)), cw, and_low_or_top(31n, cw, small_top(cw, h)))

def short_inj(+a: U32, +b: U32, +ha: {U32.is_lt(a, H.tag()) == True{} : Bool}, +hb: {U32.is_lt(b, H.tag()) == True{} : Bool}, +e: {H.short_word(a) == H.short_word(b) : U32}) -> {a == b : U32}:
  Equal.trans(U32, a, U32.and(H.short_word(a), 2147483647), b, Equal.sym(U32, U32.and(H.short_word(a), 2147483647), a, short_back(a, ha)),
    Equal.trans(U32, U32.and(H.short_word(a), 2147483647), U32.and(H.short_word(b), 2147483647), b, Equal.cong(U32, U32, z => U32.and(z, 2147483647), H.short_word(a), H.short_word(b), e), short_back(b, hb)))

def lw_word(+hw: Word(32n)) -> Word(32n):
  Word.or(32n, Word.and(32n, hw, low(31n)), one(30n))

def long_top(+hw: Word(32n)) -> {topb(31n, lw_word(hw)) == False{} : Bool}:
  +x = Word.and(32n, hw, low(31n))
  %Equal.sym(Bool, topb(31n, Word.or(32n, x, one(30n))), Bool.or(topb(31n, x), topb(31n, one(30n))), topb_or(31n, x, one(30n))) : {_ == False{} : Bool}
  %Equal.sym(Bool, topb(31n, x), False{}, topb_and_low(31n, hw)) : {Bool.or(_, topb(31n, one(30n))) == False{} : Bool}
  topb_one(30n)

def long_is_long(+h: U32) -> {H.is_short(H.long_word(h)) == False{} : Bool}:
  match h:
    case U32{+hw}:
      Equal.trans(Bool, H.is_short(U32{lw_word(hw)}), topb(31n, lw_word(hw)), False{}, is_short_top(lw_word(hw)), long_top(hw))

def or_bit0(+p: Nat, +b: Bool, +t: Word(p)) -> {Word.or(1n+p, WCon{b, t}, WCon{True{}, Word.zero(p)}) == WCon{True{}, Word.or(p, t, Word.zero(p))} : Word(1n+p)}:
  Equal.cong(Bool, Word(1n+p), z => WCon{z, Word.or(p, t, Word.zero(p))}, Bool.or(b, True{}), True{}, or_true(b))

def long_nonzero(+h: U32) -> {U32.is_eq(H.long_word(h), 0) == False{} : Bool}:
  match h:
    case U32{WCon{+b0, +rest}}:
      +b = Bool.and(b0, True{})
      +t = Word.and(31n, rest, low(30n))
      +u = Word.or(31n, t, Word.zero(31n))
      L.subst(Word(32n), w => {Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))) == False{} : Bool}, WCon{True{}, u}, lw_word(WCon{b0, rest}), Equal.sym(Word(32n), lw_word(WCon{b0, rest}), WCon{True{}, u}, or_bit0(31n, b, t)), bit0_nonzero(31n, u))

# a long word is never a short word
def long_not_short(+h: U32, +c: U32, +e: {H.long_word(h) == H.short_word(c) : U32}) -> Empty:
  L.true_false(Equal.trans(Bool, True{}, H.is_short(H.short_word(c)), False{}, Equal.sym(Bool, H.is_short(H.short_word(c)), True{}, short_is_short(c)), Equal.trans(Bool, H.is_short(H.short_word(c)), H.is_short(H.long_word(h)), False{}, Equal.cong(U32, Bool, z => H.is_short(z), H.short_word(c), H.long_word(h), Equal.sym(U32, H.long_word(h), H.short_word(c), e)), long_is_long(h))))




# a word with its top bit set is its low bits with the top bit set
def or_and_low_top(+p: Nat, +x: Word(1n+p), +h: {topb(p, x) == True{} : Bool}) -> {Word.or(1n+p, Word.and(1n+p, x, low(p)), top(p)) == x : Word(1n+p)}:
  match p x:
    case 0n WCon{b, WNil{}}:
      Equal.cong(Bool, Word(1n), c => WCon{c, WNil{}}, Bool.or(Bool.and(b, False{}), True{}), b, Equal.trans(Bool, Bool.or(Bool.and(b, False{}), True{}), True{}, b, or_true(Bool.and(b, False{})), Equal.sym(Bool, b, True{}, h)))
    case 1n+q WCon{b, t}:
      +e1 = Equal.trans(Bool, Bool.or(Bool.and(b, True{}), False{}), Bool.and(b, True{}), b, or_false(Bool.and(b, True{})), and_true(b))
      Equal.trans(Word(2n+q), WCon{Bool.or(Bool.and(b, True{}), False{}), Word.or(1n+q, Word.and(1n+q, t, low(q)), top(q))}, WCon{b, Word.or(1n+q, Word.and(1n+q, t, low(q)), top(q))}, WCon{b, t},
        Equal.cong(Bool, Word(2n+q), c => WCon{c, Word.or(1n+q, Word.and(1n+q, t, low(q)), top(q))}, Bool.or(Bool.and(b, True{}), False{}), b, e1),
        Equal.cong(Word(1n+q), Word(2n+q), w => WCon{b, w}, Word.or(1n+q, Word.and(1n+q, t, low(q)), top(q)), t, or_and_low_top(q, t, h)))

def short_eta(+x: U32, +h: {H.is_short(x) == True{} : Bool}) -> {H.short_word(U32.and(x, 2147483647)) == x : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.or(32n, Word.and(32n, w, low(31n)), top(31n)), w, or_and_low_top(31n, w, Equal.trans(Bool, topb(31n, w), H.is_short(U32{w}), True{}, Equal.sym(Bool, H.is_short(U32{w}), topb(31n, w), is_short_top(w)), h)))
