import Base
import ../lib/logic.bend as L
import ../lib/u32alg.bend as A
import ../spec/hash_table.bend as S
import ../../src/containers/hash_table.bend as H
import ./strings.bend as STR
import ../lib/u32.bend as UW

# Key identity: structural String equality is an equivalence, and every key
# has one check word (a one-character key below 2^31 its short word, any
# other key its long hash word).


def chr_refl(+c: Char) -> {S.chr_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      UW.u32_eq_refl(x)

def str_refl(+s: String) -> {S.str_eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      L.and_intro(S.chr_eq(c, c), S.str_eq(t, t), chr_refl(c), str_refl(t))

def chr_eq_of(+a: Char, +b: Char, +h: {S.chr_eq(a, b) == True{} : Bool}) -> {a == b : Char}:
  match a b:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, z => Chr{z}, x, y, A.eq_of(x, y, h))

# equal by str_eq means equal
def str_eq_of(+a: String, +b: String, +h: {S.str_eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{c, t}:
      Empty.absurd({SNil{} == SCon{c, t} : String}, L.false_true(h))
    case SCon{c, t} SNil{}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, L.false_true(h))
    case SCon{+x, +s} SCon{+y, +t}:
      +ex = chr_eq_of(x, y, L.and_left(S.chr_eq(x, y), S.str_eq(s, t), h))
      +es = str_eq_of(s, t, L.and_right(S.chr_eq(x, y), S.str_eq(s, t), h))
      Equal.trans(String, SCon{x, s}, SCon{y, s}, SCon{y, t}, Equal.cong(Char, String, z => SCon{z, s}, x, y, ex), Equal.cong(String, String, z => SCon{y, z}, s, t, es))

def str_eq_true(+a: String, +b: String, +e: {a == b : String}) -> {S.str_eq(a, b) == True{} : Bool}:
  L.subst(String, z => {S.str_eq(a, z) == True{} : Bool}, a, b, e, str_refl(a))

def sym_c(+a: String, +b: String, +c: Bool, +hc: {S.str_eq(a, b) == c : Bool}, +d: Bool, +hd: {S.str_eq(b, a) == d : Bool}) -> {c == d : Bool}:
  match c d:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, S.str_eq(b, a), False{}, Equal.sym(Bool, S.str_eq(b, a), True{}, str_eq_true(b, a, Equal.sym(String, a, b, str_eq_of(a, b, hc)))), hd)))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, S.str_eq(a, b), False{}, Equal.sym(Bool, S.str_eq(a, b), True{}, str_eq_true(a, b, Equal.sym(String, b, a, str_eq_of(b, a, hd)))), hc)))

def str_sym(+a: String, +b: String) -> {S.str_eq(a, b) == S.str_eq(b, a) : Bool}:
  sym_c(a, b, S.str_eq(a, b), {==}, S.str_eq(b, a), {==})

# ---- the check word of a key ----

# a one-character key whose code is below 2^31 (stored by its word alone)
def short_c(+c: U32, t: String) -> Bool:
  match t:
    case SNil{}:
      U32.is_lt(c, H.tag())
    case SCon{d, r}:
      False{}

def shortk(key: String) -> Bool:
  match key:
    case SNil{}:
      False{}
    case SCon{Chr{+c}, +t}:
      short_c(c, t)

def kw_c(+c: U32, +t: String, sh: Bool) -> U32:
  match sh:
    case True{}:
      H.short_word(c)
    case False{}:
      STR.lword(SCon{Chr{c}, t})

def kword(key: String) -> U32:
  match key:
    case SNil{}:
      STR.lword(SNil{})
    case SCon{Chr{+c}, +t}:
      kw_c(c, t, short_c(c, t))

def kword_long(+key: String, +hk: {shortk(key) == False{} : Bool}) -> {kword(key) == STR.lword(key) : U32}:
  match key:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, +t}:
      L.subst(Bool, b => {kw_c(c, t, b) == STR.lword(SCon{Chr{c}, t}) : U32}, False{}, short_c(c, t), Equal.sym(Bool, short_c(c, t), False{}, hk), {==})

def kword_short(+c: U32, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}) -> {kword(SCon{Chr{c}, SNil{}}) == H.short_word(c) : U32}:
  L.subst(Bool, b => {kw_c(c, SNil{}, b) == H.short_word(c) : U32}, True{}, U32.is_lt(c, H.tag()), Equal.sym(Bool, U32.is_lt(c, H.tag()), True{}, hc), {==})

def not_true_eq(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

def not_true_eq2(+b: Bool, +h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, L.true_false(h))
