import Base
import ../lib/logic.bend as L
import ../lib/u32alg.bend as A
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./strings.bend as STR
import ./words.bend as WR
import ./keys.bend as K
import ./table.bend as TB
import ./buckets.bend as B
import ./step.bend as SP
import ../lib/u32.bend as UW

# The implementation's step decision (word match, then String compare)
# equals the model's "does the bucket hold the key", for a long key, when a
# long bucket's word is its stored key's word.

def not_false() -> {Bool.not(False{}) == True{} : Bool}:
  {==}

# a short word masked is a code below 2^31
def masked_small(+x: U32) -> {U32.is_lt(U32.and(x, 2147483647), H.tag()) == True{} : Bool}:
  match x:
    case U32{+w}:
      +a = Word.and(32n, w, WR.low(31n))
      +c = Word.cmp(32n, a, WR.top(31n))
      Equal.trans(Bool, Cmp.is_lt(c), Bool.not(Cmp.is_ge(c)), True{}, WR.lt_ge(c), L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, Cmp.is_ge(c), Equal.sym(Bool, Cmp.is_ge(c), False{}, Equal.trans(Bool, Cmp.is_ge(c), WR.topb(31n, a), False{}, WR.ge_top(31n, a), WR.topb_and_low(31n, w))), {==}))

def lword_long(+key: String) -> {H.is_short(STR.lword(key)) == False{} : Bool}:
  WR.long_is_long(STR.fold(key, 0))

# a one-character key below 2^31 is not a long-probed key
def short_ne_long(+c: U32, +key: String, +hc: {U32.is_lt(c, H.tag()) == True{} : Bool}, +hk: {K.shortk(key) == False{} : Bool}, +e: Bool, +he: {S.str_eq(SCon{Chr{c}, SNil{}}, key) == e : Bool}) -> {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +eq = K.str_eq_of(SCon{Chr{c}, SNil{}}, key, he)
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, K.shortk(key), False{}, Equal.trans(Bool, True{}, K.shortk(SCon{Chr{c}, SNil{}}), K.shortk(key), Equal.sym(Bool, K.shortk(SCon{Chr{c}, SNil{}}), True{}, hc), Equal.cong(String, Bool, z => K.shortk(z), SCon{Chr{c}, SNil{}}, key, eq)), hk)))

# words of different kinds differ
def kinds_ne(+x: U32, +w: U32, +hx: {H.is_short(x) == True{} : Bool}, +hw: {H.is_short(w) == False{} : Bool}, +s: Bool, +hs: {U32.is_eq(x, w) == s : Bool}) -> {s == False{} : Bool}:
  match s:
    case False{}:
      {==}
    case True{}:
      +eq = A.eq_of(x, w, hs)
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, H.is_short(w), False{}, Equal.trans(Bool, True{}, H.is_short(x), H.is_short(w), Equal.sym(Bool, H.is_short(x), True{}, hx), Equal.cong(U32, Bool, z => H.is_short(z), x, w, eq)), hw)))

def dl_short(+key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +l: U32, +k: String, +hxs: {H.is_short(x) == True{} : Bool}) -> {SP.ld_w(key, l, k, U32.is_eq(x, STR.lword(key))) == B.mstep(key, B.BF{x, l, TB.keyof_c(x, k, True{})}) : B.MS}:
  +sk = {SCon{Chr{U32.and(x, 2147483647)}, SNil{}} : String}
  Equal.trans(B.MS, SP.ld_w(key, l, k, U32.is_eq(x, STR.lword(key))), B.MNext{}, Bool.pick(B.MS, S.str_eq(sk, key), B.MHit{l}, B.MNext{}),
    Equal.cong(Bool, B.MS, b => SP.ld_w(key, l, k, b), U32.is_eq(x, STR.lword(key)), False{}, kinds_ne(x, STR.lword(key), hxs, lword_long(key), U32.is_eq(x, STR.lword(key)), {==})),
    Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), False{}, S.str_eq(sk, key), Equal.sym(Bool, S.str_eq(sk, key), False{}, short_ne_long(U32.and(x, 2147483647), key, masked_small(x), hk, S.str_eq(sk, key), {==}))))

# a long bucket whose word is not the probed word does not hold the key
def le_false(+k: String, +key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +hinv: {x == K.kword(k) : U32}, +hs: {U32.is_eq(x, STR.lword(key)) == False{} : Bool}, +e: Bool, +he: {S.str_eq(k, key) == e : Bool}) -> {e == False{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      +xw = Equal.trans(U32, x, K.kword(k), STR.lword(key), hinv, Equal.trans(U32, K.kword(k), K.kword(key), STR.lword(key), Equal.cong(String, U32, z => K.kword(z), k, key, K.str_eq_of(k, key, he)), K.kword_long(key, hk)))
      Empty.absurd({True{} == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_eq(x, STR.lword(key)), False{}, L.subst(U32, z => {True{} == U32.is_eq(x, z) : Bool}, x, STR.lword(key), xw, Equal.sym(Bool, U32.is_eq(x, x), True{}, UW.u32_eq_refl(x))), hs)))

def dl_long(+key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +l: U32, +k: String, +hinv: {x == K.kword(k) : U32}, +s: Bool, +hs: {U32.is_eq(x, STR.lword(key)) == s : Bool}) -> {SP.ld_w(key, l, k, s) == Bool.pick(B.MS, S.str_eq(k, key), B.MHit{l}, B.MNext{}) : B.MS}:
  match s:
    case True{}:
      Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), S.str_eq(key, k), S.str_eq(k, key), K.str_sym(key, k))
    case False{}:
      Equal.cong(Bool, B.MS, b => Bool.pick(B.MS, b, B.MHit{l}, B.MNext{}), False{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), False{}, le_false(k, key, hk, x, hinv, hs, S.str_eq(k, key), {==})))

def dsh(+key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +l: U32, +k: String, +hinv: {B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(k))) == True{} : Bool}, +sh: Bool, +hsh: {H.is_short(x) == sh : Bool}) -> {SP.ld_w(key, l, k, U32.is_eq(x, STR.lword(key))) == B.mstep(key, B.BF{x, l, TB.keyof_c(x, k, sh)}) : B.MS}:
  match sh:
    case True{}:
      dl_short(key, hk, x, l, k, hsh)
    case False{}:
      +e = B.imp_elim(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(k)), hinv, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, H.is_short(x), Equal.sym(Bool, H.is_short(x), False{}, hsh), {==}))
      dl_long(key, hk, x, l, k, A.eq_of(x, K.kword(k), e), U32.is_eq(x, STR.lword(key)), {==})

def dec_e(+key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +l: U32, +ks: List<&2, String>, +hinv: {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(ks, UD.v(H.slot(l))))))) == True{} : Bool}, +e: Bool, +he: {U32.is_eq(x, 0) == e : Bool}) -> {SP.ld_e(key, STR.lword(key), x, l, TB.nths(ks, UD.v(H.slot(l))), e) == B.mstep(key, TB.dec_c(x, l, ks, e)) : B.MS}:
  match e:
    case True{}:
      {==}
    case False{}:
      +h2 = B.imp_elim(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(ks, UD.v(H.slot(l)))))), hinv, L.subst(Bool, b => {Bool.not(b) == True{} : Bool}, False{}, U32.is_eq(x, 0), Equal.sym(Bool, U32.is_eq(x, 0), False{}, he), {==}))
      dsh(key, hk, x, l, TB.nths(ks, UD.v(H.slot(l))), h2, H.is_short(x), {==})

# THEOREM: a long-key step decides as the model's step on the decoded bucket.
def decide(+key: String, +hk: {K.shortk(key) == False{} : Bool}, +x: U32, +l: U32, +ks: List<&2, String>, +hinv: {B.implies(Bool.not(U32.is_eq(x, 0)), B.implies(Bool.not(H.is_short(x)), U32.is_eq(x, K.kword(TB.nths(ks, UD.v(H.slot(l))))))) == True{} : Bool}) -> {SP.ldec(key, STR.lword(key), x, l, TB.nths(ks, UD.v(H.slot(l)))) == B.mstep(key, TB.dec_c(x, l, ks, U32.is_eq(x, 0))) : B.MS}:
  dec_e(key, hk, x, l, ks, hinv, U32.is_eq(x, 0), {==})
