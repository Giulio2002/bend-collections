import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/prefix_trie.bend as PS
import ../../src/prefix_trie.bend as P
import ../../types/balanced_search_tree.bend as BE
import ../balanced_search_tree/sorted.bend as SO
import ../balanced_search_tree/specops.bend as SP

# Key facts for the trie proofs: keys of a sibling list's enumeration start
# with a character above the list's lower bound; String.order on keys with a
# known first character; prefixing every key with a character commutes with
# the finite-map operations, prefix filtering and longest-prefix selection.

def gtM(lo: Maybe<&2, U32>, +y: U32) -> Bool:
  match lo:
    case None{}:
      True{}
    case Some{l}:
      Cmp.is_lt(U32.cmp(l, y))

def keyok(lo: Maybe<&2, U32>, k: String) -> Bool:
  match k:
    case SNil{}:
      False{}
    case SCon{Chr{y}, t}:
      gtM(lo, y)

# Every key is nonempty and starts with a character above lo.
def hg(-V: Data, xs: List<&2, BE.Entry<String, V>>, +lo: Maybe<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(keyok(lo, BE.key(String, V, e)), hg(V, t, lo))

# Trie invariant: sibling characters strictly increase (above lo).
def ok(-V: Data, t: P.Trie<V>, +lo: Maybe<&2, U32>) -> Bool:
  match t:
    case P.TNil{}:
      True{}
    case P.TNode{+c, val, down, next}:
      Bool.and(gtM(lo, c), Bool.and(ok(V, down, None{}), ok(V, next, Some{c})))

# ---- String.order ----

def u_refl(+x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  O.refl(~U32, ~U32.cmp, ~O.u32_order, x)

def so_lt(+x: U32, +y: U32, +t1: String, +t2: String, +h: {U32.cmp(x, y) == LT{} : Cmp}) -> {String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}) == LT{} : Cmp}:
  Equal.trans(Cmp, String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}), O.lex(U32.cmp(x, y), String.order(t1, t2)), LT{}, O.so_cons(x, t1, y, t2), Equal.cong(Cmp, Cmp, z => O.lex(z, String.order(t1, t2)), U32.cmp(x, y), LT{}, h))

def so_same(+x: U32, +t1: String, +t2: String) -> {String.order(SCon{Chr{x}, t1}, SCon{Chr{x}, t2}) == String.order(t1, t2) : Cmp}:
  Equal.trans(Cmp, String.order(SCon{Chr{x}, t1}, SCon{Chr{x}, t2}), O.lex(U32.cmp(x, x), String.order(t1, t2)), String.order(t1, t2), O.so_cons(x, t1, x, t2), Equal.cong(Cmp, Cmp, z => O.lex(z, String.order(t1, t2)), U32.cmp(x, x), EQ{}, u_refl(x)))

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{}:
      {==}

# ---- head bounds ----

def gt_trans(+lo: Maybe<&2, U32>, +c: U32, +y: U32, +h1: {gtM(lo, c) == True{} : Bool}, +h2: {Cmp.is_lt(U32.cmp(c, y)) == True{} : Bool}) -> {gtM(lo, y) == True{} : Bool}:
  match lo:
    case None{}:
      {==}
    case Some{+l}:
      SO.is_lt_of(U32.cmp(l, y), SO.lt_trans(~U32, ~U32.cmp, ~O.u32_order, l, c, y, O.lt_is(U32.cmp(l, c), h1), O.lt_is(U32.cmp(c, y), h2)))

def keyok_weaken(+k: String, +c: U32, +lo: Maybe<&2, U32>, +h: {gtM(lo, c) == True{} : Bool}, +g: {keyok(Some{c}, k) == True{} : Bool}) -> {keyok(lo, k) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({keyok(lo, SNil{}) == True{} : Bool}, L.false_true(g))
    case SCon{Chr{+y}, t}:
      gt_trans(lo, c, y, h, g)

def hg_weaken(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +c: U32, +lo: Maybe<&2, U32>, +h: {gtM(lo, c) == True{} : Bool}, +g: {hg(V, xs, Some{c}) == True{} : Bool}) -> {hg(V, xs, lo) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(keyok(lo, BE.key(String, V, e)), hg(V, t, lo), keyok_weaken(BE.key(String, V, e), c, lo, h, L.and_left(keyok(Some{c}, BE.key(String, V, e)), hg(V, t, Some{c}), g)), hg_weaken(V, t, c, lo, h, L.and_right(keyok(Some{c}, BE.key(String, V, e)), hg(V, t, Some{c}), g)))

def hg_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +lo: Maybe<&2, U32>, +hx: {hg(V, xs, lo) == True{} : Bool}, +hy: {hg(V, ys, lo) == True{} : Bool}) -> {hg(V, SC.append(BE.Entry<String, V>, xs, ys), lo) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+e, +t}:
      L.and_intro(keyok(lo, BE.key(String, V, e)), hg(V, SC.append(BE.Entry<String, V>, t, ys), lo), L.and_left(keyok(lo, BE.key(String, V, e)), hg(V, t, lo), hx), hg_app(V, t, ys, lo, L.and_right(keyok(lo, BE.key(String, V, e)), hg(V, t, lo), hx), hy))

def hg_mapc(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +lo: Maybe<&2, U32>, +h: {gtM(lo, c) == True{} : Bool}) -> {hg(V, P.mapc(V, c, xs), lo) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{k, v}, +t}:
      L.and_intro(gtM(lo, c), hg(V, P.mapc(V, c, t), lo), h, hg_mapc(V, c, t, lo, h))

def hg_opt(-V: Data, +c: U32, val: Maybe<&2, V>, +lo: Maybe<&2, U32>, +h: {gtM(lo, c) == True{} : Bool}) -> {hg(V, P.opt(V, SCon{Chr{c}, SNil{}}, val), lo) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      L.and_intro(gtM(lo, c), True{}, h, {==})

def heads(-V: Data, +t: P.Trie<V>, +lo: Maybe<&2, U32>, +o: {ok(V, t, lo) == True{} : Bool}) -> {hg(V, P.ent(V, t), lo) == True{} : Bool}:
  match t:
    case P.TNil{}:
      {==}
    case P.TNode{+c, +val, +down, +next}:
      +g1 = L.and_left(gtM(lo, c), Bool.and(ok(V, down, None{}), ok(V, next, Some{c})), o)
      +g23 = L.and_right(gtM(lo, c), Bool.and(ok(V, down, None{}), ok(V, next, Some{c})), o)
      hg_app(V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, down)), P.ent(V, next)), lo, hg_opt(V, c, val, lo, g1),
        hg_app(V, P.mapc(V, c, P.ent(V, down)), P.ent(V, next), lo, hg_mapc(V, c, P.ent(V, down), lo, g1),
          hg_weaken(V, P.ent(V, next), c, lo, g1, heads(V, next, Some{c}, L.and_right(ok(V, down, None{}), ok(V, next, Some{c}), g23)))))

def ok_relax(-V: Data, +c: U32, +val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +lo2: Maybe<&2, U32>, +o: {ok(V, P.TNode{c, val, down, next}, lo) == True{} : Bool}, +h: {gtM(lo2, c) == True{} : Bool}) -> {ok(V, P.TNode{c, val, down, next}, lo2) == True{} : Bool}:
  L.and_intro(gtM(lo2, c), Bool.and(ok(V, down, None{}), ok(V, next, Some{c})), h, L.and_right(gtM(lo, c), Bool.and(ok(V, down, None{}), ok(V, next, Some{c})), o))

# ---- above / below from head bounds ----

def above_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +k: String, +ax: {SO.above(~String, ~String.order, V, xs, k) == True{} : Bool}, +ay: {SO.above(~String, ~String.order, V, ys, k) == True{} : Bool}) -> {SO.above(~String, ~String.order, V, SC.append(BE.Entry<String, V>, xs, ys), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      ay
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(String.order(k, BE.key(String, V, e))), SO.above(~String, ~String.order, V, SC.append(BE.Entry<String, V>, t, ys), k), L.and_left(Cmp.is_lt(String.order(k, BE.key(String, V, e))), SO.above(~String, ~String.order, V, t, k), ax), above_app(V, t, ys, k, L.and_right(Cmp.is_lt(String.order(k, BE.key(String, V, e))), SO.above(~String, ~String.order, V, t, k), ax), ay))

def below_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +k: String, +bx: {SO.below(~String, ~String.order, V, xs, k) == True{} : Bool}, +by: {SO.below(~String, ~String.order, V, ys, k) == True{} : Bool}) -> {SO.below(~String, ~String.order, V, SC.append(BE.Entry<String, V>, xs, ys), k) == True{} : Bool}:
  match xs:
    case Nil{}:
      by
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(String.order(BE.key(String, V, e), k)), SO.below(~String, ~String.order, V, SC.append(BE.Entry<String, V>, t, ys), k), L.and_left(Cmp.is_lt(String.order(BE.key(String, V, e), k)), SO.below(~String, ~String.order, V, t, k), bx), below_app(V, t, ys, k, L.and_right(Cmp.is_lt(String.order(BE.key(String, V, e), k)), SO.below(~String, ~String.order, V, t, k), bx), by))

def above1(+k: String, +x: U32, +rest: String, +g: {keyok(Some{x}, k) == True{} : Bool}) -> {Cmp.is_lt(String.order(SCon{Chr{x}, rest}, k)) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Cmp.is_lt(String.order(SCon{Chr{x}, rest}, SNil{})) == True{} : Bool}, L.false_true(g))
    case SCon{Chr{+y}, +t}:
      SO.is_lt_of(String.order(SCon{Chr{x}, rest}, SCon{Chr{y}, t}), so_lt(x, y, rest, t, O.lt_is(U32.cmp(x, y), g)))

def above_hg(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +rest: String, +h: {hg(V, xs, Some{x}) == True{} : Bool}) -> {SO.above(~String, ~String.order, V, xs, SCon{Chr{x}, rest}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(String.order(SCon{Chr{x}, rest}, BE.key(String, V, e))), SO.above(~String, ~String.order, V, t, SCon{Chr{x}, rest}), above1(BE.key(String, V, e), x, rest, L.and_left(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)), above_hg(V, t, x, rest, L.and_right(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)))

def above_nil1(+k: String, +x: U32, +g: {keyok(None{}, k) == True{} : Bool}) -> {Cmp.is_lt(String.order(SCon{Chr{x}, SNil{}}, SCon{Chr{x}, k})) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Cmp.is_lt(String.order(SCon{Chr{x}, SNil{}}, SCon{Chr{x}, SNil{}})) == True{} : Bool}, L.false_true(g))
    case SCon{+y, +t}:
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, SNil{}}, SCon{Chr{x}, SCon{y, t}}), String.order(SNil{}, SCon{y, t}), so_same(x, SNil{}, SCon{y, t})) : {Cmp.is_lt(_) == True{} : Bool}
      {==}

def above_mapc_nil(-V: Data, +x: U32, +xs: List<&2, BE.Entry<String, V>>, +h: {hg(V, xs, None{}) == True{} : Bool}) -> {SO.above(~String, ~String.order, V, P.mapc(V, x, xs), SCon{Chr{x}, SNil{}}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      L.and_intro(Cmp.is_lt(String.order(SCon{Chr{x}, SNil{}}, SCon{Chr{x}, k})), SO.above(~String, ~String.order, V, P.mapc(V, x, t), SCon{Chr{x}, SNil{}}), above_nil1(k, x, L.and_left(keyok(None{}, k), hg(V, t, None{}), h)), above_mapc_nil(V, x, t, L.and_right(keyok(None{}, k), hg(V, t, None{}), h)))

def above_root1(+k: String, +g: {keyok(None{}, k) == True{} : Bool}) -> {Cmp.is_lt(String.order(SNil{}, k)) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Cmp.is_lt(String.order(SNil{}, SNil{})) == True{} : Bool}, L.false_true(g))
    case SCon{y, t}:
      {==}

# Nonempty keys are all above the empty key.
def above_root(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +h: {hg(V, xs, None{}) == True{} : Bool}) -> {SO.above(~String, ~String.order, V, xs, SNil{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Cmp.is_lt(String.order(SNil{}, BE.key(String, V, e))), SO.above(~String, ~String.order, V, t, SNil{}), above_root1(BE.key(String, V, e), L.and_left(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)), above_root(V, t, L.and_right(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)))

def below_mapc(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +rest: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {SO.below(~String, ~String.order, V, P.mapc(V, c, xs), SCon{Chr{x}, rest}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      L.and_intro(Cmp.is_lt(String.order(SCon{Chr{c}, k}, SCon{Chr{x}, rest})), SO.below(~String, ~String.order, V, P.mapc(V, c, t), SCon{Chr{x}, rest}), SO.is_lt_of(String.order(SCon{Chr{c}, k}, SCon{Chr{x}, rest}), so_lt(c, x, k, rest, h)), below_mapc(V, c, t, x, rest, h))

def below_opt(-V: Data, +c: U32, val: Maybe<&2, V>, +x: U32, +rest: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {SO.below(~String, ~String.order, V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SCon{Chr{x}, rest}) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      L.and_intro(Cmp.is_lt(String.order(SCon{Chr{c}, SNil{}}, SCon{Chr{x}, rest})), True{}, SO.is_lt_of(String.order(SCon{Chr{c}, SNil{}}, SCon{Chr{x}, rest}), so_lt(c, x, SNil{}, rest, h)), {==})

def below_opt_eq(-V: Data, +c: U32, val: Maybe<&2, V>, +y: Char, +r: String) -> {SO.below(~String, ~String.order, V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SCon{Chr{c}, SCon{y, r}}) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, SNil{}}, SCon{Chr{c}, SCon{y, r}}), String.order(SNil{}, SCon{y, r}), so_same(c, SNil{}, SCon{y, r})) : {Bool.and(Cmp.is_lt(_), True{}) == True{} : Bool}
      {==}

def below_root(-V: Data, val: Maybe<&2, V>, +x: U32, +rest: String) -> {SO.below(~String, ~String.order, V, P.opt(V, SNil{}, val), SCon{Chr{x}, rest}) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      {==}

# ---- inserting in front / before a block ----

def ins_front(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +k: String, +v: V, +a: {SO.above(~String, ~String.order, V, xs, k) == True{} : Bool}) -> {S.ins(~String, ~String.order, V, k, v, xs) == Con{BE.Entry{k, v}, xs} : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Cmp, String.order(k, BE.key(String, V, e)), LT{}, O.lt_is(String.order(k, BE.key(String, V, e)), L.and_left(Cmp.is_lt(String.order(k, BE.key(String, V, e))), SO.above(~String, ~String.order, V, t, k), a))) : {S.ins_at(~String, ~String.order, V, _, k, v, e, t, S.ins(~String, ~String.order, V, k, v, t)) == Con{BE.Entry{k, v}, Con{e, t}} : List<&2, BE.Entry<String, V>>}
      {==}

def ins_split(-V: Data, +bs: List<&2, BE.Entry<String, V>>, +cs: List<&2, BE.Entry<String, V>>, +k: String, +v: V, +a: {SO.above(~String, ~String.order, V, cs, k) == True{} : Bool}) -> {S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, bs, cs)) == SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, bs), cs) : List<&2, BE.Entry<String, V>>}:
  match cs:
    case Nil{}:
      Equal.trans(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, bs, Nil{})), S.ins(~String, ~String.order, V, k, v, bs), SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, bs), Nil{}),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => S.ins(~String, ~String.order, V, k, v, z), SC.append(BE.Entry<String, V>, bs, Nil{}), bs, LL.append_nil(BE.Entry<String, V>, bs)),
        Equal.sym(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, bs), Nil{}), S.ins(~String, ~String.order, V, k, v, bs), LL.append_nil(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, bs))))
    case Con{+e, +r}:
      SP.ins_left(~String, ~String.order, V, bs, e, r, k, v, O.lt_is(String.order(k, BE.key(String, V, e)), L.and_left(Cmp.is_lt(String.order(k, BE.key(String, V, e))), SO.above(~String, ~String.order, V, r, k), a)))

# ---- prefixing keys with a character ----

def mapc_app(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>) -> {P.mapc(V, c, SC.append(BE.Entry<String, V>, xs, ys)) == SC.append(BE.Entry<String, V>, P.mapc(V, c, xs), P.mapc(V, c, ys)) : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +v}, +t}:
      LL.cons_cong(BE.Entry<String, V>, BE.Entry{SCon{Chr{c}, k}, v}, P.mapc(V, c, SC.append(BE.Entry<String, V>, t, ys)), SC.append(BE.Entry<String, V>, P.mapc(V, c, t), P.mapc(V, c, ys)), mapc_app(V, c, t, ys))

def mapc_opt(-V: Data, +c: U32, val: Maybe<&2, V>) -> {P.mapc(V, c, P.opt(V, SNil{}, val)) == P.opt(V, SCon{Chr{c}, SNil{}}, val) : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      {==}

def map_ins_c(-V: Data, +c: U32, +k: String, +v: V, +k2: String, +v2: V, +t: List<&2, BE.Entry<String, V>>, d: Cmp, +ed: {String.order(k, k2) == d : Cmp}, +ih: {P.mapc(V, c, S.ins(~String, ~String.order, V, k, v, t)) == S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t)) : List<&2, BE.Entry<String, V>>}) -> {P.mapc(V, c, S.ins(~String, ~String.order, V, k, v, Con{BE.Entry{k2, v2}, t})) == S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, Con{BE.Entry{k2, v2}, t})) : List<&2, BE.Entry<String, V>>}:
  match d:
    case LT{}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, k}, SCon{Chr{c}, k2}), String.order(k, k2), so_same(c, k, k2)) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, String.order(k, k2), k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(Cmp, String.order(k, k2), LT{}, ed) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, _, k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, k}, SCon{Chr{c}, k2}), String.order(k, k2), so_same(c, k, k2)) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, String.order(k, k2), k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(Cmp, String.order(k, k2), EQ{}, ed) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, _, k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      {==}
    case GT{}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, k}, SCon{Chr{c}, k2}), String.order(k, k2), so_same(c, k, k2)) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, String.order(k, k2), k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(Cmp, String.order(k, k2), GT{}, ed) : {P.mapc(V, c, S.ins_at(~String, ~String.order, V, _, k, v, BE.Entry{k2, v2}, t, S.ins(~String, ~String.order, V, k, v, t))) == S.ins_at(~String, ~String.order, V, _, SCon{Chr{c}, k}, v, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, t), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      LL.cons_cong(BE.Entry<String, V>, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, S.ins(~String, ~String.order, V, k, v, t)), S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, t)), ih)

def map_ins(-V: Data, +c: U32, +k: String, +v: V, +xs: List<&2, BE.Entry<String, V>>) -> {P.mapc(V, c, S.ins(~String, ~String.order, V, k, v, xs)) == S.ins(~String, ~String.order, V, SCon{Chr{c}, k}, v, P.mapc(V, c, xs)) : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +v2}, +t}:
      map_ins_c(V, c, k, v, k2, v2, t, String.order(k, k2), {==}, map_ins(V, c, k, v, t))

def map_keep(-V: Data, +c: U32, b: Bool, +k2: String, +v2: V, +r1: List<&2, BE.Entry<String, V>>, +r2: List<&2, BE.Entry<String, V>>, +e: {P.mapc(V, c, r1) == r2 : List<&2, BE.Entry<String, V>>}) -> {P.mapc(V, c, S.keep_at(String, V, b, BE.Entry{k2, v2}, r1)) == S.keep_at(String, V, b, BE.Entry{SCon{Chr{c}, k2}, v2}, r2) : List<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      LL.cons_cong(BE.Entry<String, V>, BE.Entry{SCon{Chr{c}, k2}, v2}, P.mapc(V, c, r1), r2, e)
    case False{}:
      e

def map_del(-V: Data, +c: U32, +k: String, +xs: List<&2, BE.Entry<String, V>>) -> {P.mapc(V, c, S.del(~String, ~String.order, V, k, xs)) == S.del(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, xs)) : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +v2}, +t}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, k}, SCon{Chr{c}, k2}), String.order(k, k2), so_same(c, k, k2)) : {P.mapc(V, c, S.keep_at(String, V, S.keep(String.order(k, k2)), BE.Entry{k2, v2}, S.del(~String, ~String.order, V, k, t))) == S.keep_at(String, V, S.keep(_), BE.Entry{SCon{Chr{c}, k2}, v2}, S.del(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, t))) : List<&2, BE.Entry<String, V>>}
      map_keep(V, c, S.keep(String.order(k, k2)), k2, v2, S.del(~String, ~String.order, V, k, t), S.del(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, t)), map_del(V, c, k, t))

def map_find_at(-V: Data, d: Cmp, +c: U32, +k2: String, +v2: V, +x: Maybe<&2, V>, +y: Maybe<&2, V>, +h: {x == y : Maybe<&2, V>}) -> {S.find_at(String, V, d, BE.Entry{SCon{Chr{c}, k2}, v2}, x) == S.find_at(String, V, d, BE.Entry{k2, v2}, y) : Maybe<&2, V>}:
  match d:
    case EQ{}:
      {==}
    case LT{}:
      h
    case GT{}:
      h

def map_find(-V: Data, +c: U32, +k: String, +xs: List<&2, BE.Entry<String, V>>) -> {S.find(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, xs)) == S.find(~String, ~String.order, V, k, xs) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k2, +v2}, +t}:
      %Equal.sym(Cmp, String.order(SCon{Chr{c}, k}, SCon{Chr{c}, k2}), String.order(k, k2), so_same(c, k, k2)) : {S.find_at(String, V, _, BE.Entry{SCon{Chr{c}, k2}, v2}, S.find(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, t))) == S.find_at(String, V, String.order(k, k2), BE.Entry{k2, v2}, S.find(~String, ~String.order, V, k, t)) : Maybe<&2, V>}
      map_find_at(V, String.order(k, k2), c, k2, v2, S.find(~String, ~String.order, V, SCon{Chr{c}, k}, P.mapc(V, c, t)), S.find(~String, ~String.order, V, k, t), map_find(V, c, k, t))

# ---- prefix filtering ----

def kif(-V: Data, b: Bool, +c: U32, +k: String, +v: V, +r1: List<&2, BE.Entry<String, V>>, +r2: List<&2, BE.Entry<String, V>>, +e: {r1 == P.mapc(V, c, r2) : List<&2, BE.Entry<String, V>>}) -> {PS.keep_if(V, b, BE.Entry{SCon{Chr{c}, k}, v}, r1) == P.mapc(V, c, PS.keep_if(V, b, BE.Entry{k, v}, r2)) : List<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      LL.cons_cong(BE.Entry<String, V>, BE.Entry{SCon{Chr{c}, k}, v}, r1, P.mapc(V, c, r2), e)
    case False{}:
      e

def map_pfx(-V: Data, +c: U32, +p: String, +xs: List<&2, BE.Entry<String, V>>) -> {PS.with_prefix(V, SCon{Chr{c}, p}, P.mapc(V, c, xs)) == P.mapc(V, c, PS.with_prefix(V, p, xs)) : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +v}, +t}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, u_refl(c)) : {PS.keep_if(V, Bool.and(Cmp.is_eq(_), PS.is_prefix(p, k)), BE.Entry{SCon{Chr{c}, k}, v}, PS.with_prefix(V, SCon{Chr{c}, p}, P.mapc(V, c, t))) == P.mapc(V, c, PS.keep_if(V, PS.is_prefix(p, k), BE.Entry{k, v}, PS.with_prefix(V, p, t))) : List<&2, BE.Entry<String, V>>}
      kif(V, PS.is_prefix(p, k), c, k, v, PS.with_prefix(V, SCon{Chr{c}, p}, P.mapc(V, c, t)), PS.with_prefix(V, p, t), map_pfx(V, c, p, t))

def pfx_nil(-V: Data, +xs: List<&2, BE.Entry<String, V>>) -> {PS.with_prefix(V, SNil{}, xs) == xs : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      LL.cons_cong(BE.Entry<String, V>, e, PS.with_prefix(V, SNil{}, t), t, pfx_nil(V, t))

def kif_app(-V: Data, b: Bool, +e: BE.Entry<String, V>, +r1: List<&2, BE.Entry<String, V>>, +r2: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +h: {r1 == SC.append(BE.Entry<String, V>, r2, ys) : List<&2, BE.Entry<String, V>>}) -> {PS.keep_if(V, b, e, r1) == SC.append(BE.Entry<String, V>, PS.keep_if(V, b, e, r2), ys) : List<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      LL.cons_cong(BE.Entry<String, V>, e, r1, SC.append(BE.Entry<String, V>, r2, ys), h)
    case False{}:
      h

def wp_app(-V: Data, +p: String, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>) -> {PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, xs, ys)) == SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, xs), PS.with_prefix(V, p, ys)) : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      kif_app(V, PS.is_prefix(p, BE.key(String, V, e)), e, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, t, ys)), PS.with_prefix(V, p, t), PS.with_prefix(V, p, ys), wp_app(V, p, t, ys))

# No key has p as a prefix.
def np(-V: Data, xs: List<&2, BE.Entry<String, V>>, +p: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, t, p))

# No key is a prefix of s.
def nm(-V: Data, xs: List<&2, BE.Entry<String, V>>, +s: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, t, s))

def kif_none(-V: Data, b: Bool, +e: BE.Entry<String, V>, +r: List<&2, BE.Entry<String, V>>, +hb: {Bool.not(b) == True{} : Bool}, +hr: {r == Nil{} : List<&2, BE.Entry<String, V>>}) -> {PS.keep_if(V, b, e, r) == Nil{} : List<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      Empty.absurd({PS.keep_if(V, True{}, e, r) == Nil{} : List<&2, BE.Entry<String, V>>}, L.false_true(hb))
    case False{}:
      hr

def wp_none(-V: Data, +p: String, +xs: List<&2, BE.Entry<String, V>>, +h: {np(V, xs, p) == True{} : Bool}) -> {PS.with_prefix(V, p, xs) == Nil{} : List<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      kif_none(V, PS.is_prefix(p, BE.key(String, V, e)), e, PS.with_prefix(V, p, t), L.and_left(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, t, p), h), wp_none(V, p, t, L.and_right(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, t, p), h)))

def np_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +p: String, +hx: {np(V, xs, p) == True{} : Bool}, +hy: {np(V, ys, p) == True{} : Bool}) -> {np(V, SC.append(BE.Entry<String, V>, xs, ys), p) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+e, +t}:
      L.and_intro(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, SC.append(BE.Entry<String, V>, t, ys), p), L.and_left(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, t, p), hx), np_app(V, t, ys, p, L.and_right(Bool.not(PS.is_prefix(p, BE.key(String, V, e))), np(V, t, p), hx), hy))

def nm_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +s: String, +hx: {nm(V, xs, s) == True{} : Bool}, +hy: {nm(V, ys, s) == True{} : Bool}) -> {nm(V, SC.append(BE.Entry<String, V>, xs, ys), s) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+e, +t}:
      L.and_intro(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, SC.append(BE.Entry<String, V>, t, ys), s), L.and_left(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, t, s), hx), nm_app(V, t, ys, s, L.and_right(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, t, s), hx), hy))

def np1(+k: String, +x: U32, +r: String, +g: {keyok(Some{x}, k) == True{} : Bool}) -> {Bool.not(PS.is_prefix(SCon{Chr{x}, r}, k)) == True{} : Bool}:
  match k:
    case SNil{}:
      {==}
    case SCon{Chr{+y}, +t}:
      %Equal.sym(Cmp, U32.cmp(x, y), LT{}, O.lt_is(U32.cmp(x, y), g)) : {Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(r, t))) == True{} : Bool}
      {==}

def nm1(+k: String, +x: U32, +r: String, +g: {keyok(Some{x}, k) == True{} : Bool}) -> {Bool.not(PS.is_prefix(k, SCon{Chr{x}, r})) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Bool.not(PS.is_prefix(SNil{}, SCon{Chr{x}, r})) == True{} : Bool}, L.false_true(g))
    case SCon{Chr{+y}, +t}:
      %Equal.sym(Cmp, U32.cmp(y, x), GT{}, SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, x, y, O.lt_is(U32.cmp(x, y), g))) : {Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(t, r))) == True{} : Bool}
      {==}

def np_hg(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +r: String, +h: {hg(V, xs, Some{x}) == True{} : Bool}) -> {np(V, xs, SCon{Chr{x}, r}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Bool.not(PS.is_prefix(SCon{Chr{x}, r}, BE.key(String, V, e))), np(V, t, SCon{Chr{x}, r}), np1(BE.key(String, V, e), x, r, L.and_left(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)), np_hg(V, t, x, r, L.and_right(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)))

def nm_hg(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +r: String, +h: {hg(V, xs, Some{x}) == True{} : Bool}) -> {nm(V, xs, SCon{Chr{x}, r}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Bool.not(PS.is_prefix(BE.key(String, V, e), SCon{Chr{x}, r})), nm(V, t, SCon{Chr{x}, r}), nm1(BE.key(String, V, e), x, r, L.and_left(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)), nm_hg(V, t, x, r, L.and_right(keyok(Some{x}, BE.key(String, V, e)), hg(V, t, Some{x}), h)))

def np_mapc(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +r: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {np(V, P.mapc(V, c, xs), SCon{Chr{x}, r}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      %Equal.sym(Cmp, U32.cmp(x, c), GT{}, SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, c, x, h)) : {Bool.and(Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(r, k))), np(V, P.mapc(V, c, t), SCon{Chr{x}, r})) == True{} : Bool}
      np_mapc(V, c, t, x, r, h)

def nm_mapc(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +x: U32, +r: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {nm(V, P.mapc(V, c, xs), SCon{Chr{x}, r}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      %Equal.sym(Cmp, U32.cmp(c, x), LT{}, h) : {Bool.and(Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(k, r))), nm(V, P.mapc(V, c, t), SCon{Chr{x}, r})) == True{} : Bool}
      nm_mapc(V, c, t, x, r, h)

def np_opt(-V: Data, +c: U32, val: Maybe<&2, V>, +x: U32, +r: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {np(V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SCon{Chr{x}, r}) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, U32.cmp(x, c), GT{}, SO.gt_of_lt(~U32, ~U32.cmp, ~O.u32_order, c, x, h)) : {Bool.and(Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(r, SNil{}))), True{}) == True{} : Bool}
      {==}

def nm_opt(-V: Data, +c: U32, val: Maybe<&2, V>, +x: U32, +r: String, +h: {U32.cmp(c, x) == LT{} : Cmp}) -> {nm(V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SCon{Chr{x}, r}) == True{} : Bool}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, U32.cmp(c, x), LT{}, h) : {Bool.and(Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(SNil{}, r))), True{}) == True{} : Bool}
      {==}

def nm_nil1(+k: String, +g: {keyok(None{}, k) == True{} : Bool}) -> {Bool.not(PS.is_prefix(k, SNil{})) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Bool.not(PS.is_prefix(SNil{}, SNil{})) == True{} : Bool}, L.false_true(g))
    case SCon{Chr{y}, t}:
      {==}

# Nonempty keys are not prefixes of the empty string.
def nm_nil(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +h: {hg(V, xs, None{}) == True{} : Bool}) -> {nm(V, xs, SNil{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Bool.not(PS.is_prefix(BE.key(String, V, e), SNil{})), nm(V, t, SNil{}), nm_nil1(BE.key(String, V, e), L.and_left(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)), nm_nil(V, t, L.and_right(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)))

def nm_mapc_nil1(+c: U32, +k: String, +g: {keyok(None{}, k) == True{} : Bool}) -> {Bool.not(PS.is_prefix(SCon{Chr{c}, k}, SCon{Chr{c}, SNil{}})) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Bool.not(PS.is_prefix(SCon{Chr{c}, SNil{}}, SCon{Chr{c}, SNil{}})) == True{} : Bool}, L.false_true(g))
    case SCon{Chr{y}, t}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, u_refl(c)) : {Bool.not(Bool.and(Cmp.is_eq(_), PS.is_prefix(SCon{Chr{y}, t}, SNil{}))) == True{} : Bool}
      {==}

def nm_mapc_nil(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +h: {hg(V, xs, None{}) == True{} : Bool}) -> {nm(V, P.mapc(V, c, xs), SCon{Chr{c}, SNil{}}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      L.and_intro(Bool.not(PS.is_prefix(SCon{Chr{c}, k}, SCon{Chr{c}, SNil{}})), nm(V, P.mapc(V, c, t), SCon{Chr{c}, SNil{}}), nm_mapc_nil1(c, k, L.and_left(keyok(None{}, k), hg(V, t, None{}), h)), nm_mapc_nil(V, c, t, L.and_right(keyok(None{}, k), hg(V, t, None{}), h)))

# ---- longest-prefix selection ----

def best_none(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +s: String, +acc: Maybe<&2, BE.Entry<String, V>>, +h: {nm(V, xs, s) == True{} : Bool}) -> {PS.best(V, xs, s, acc) == acc : Maybe<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(Bool, PS.is_prefix(BE.key(String, V, e), s), False{}, not_true(PS.is_prefix(BE.key(String, V, e), s), L.and_left(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, t, s), h))) : {PS.best(V, t, s, PS.pick(V, _, e, acc)) == acc : Maybe<&2, BE.Entry<String, V>>}
      best_none(V, t, s, acc, L.and_right(Bool.not(PS.is_prefix(BE.key(String, V, e), s)), nm(V, t, s), h))

def best_app(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +ys: List<&2, BE.Entry<String, V>>, +s: String, +acc: Maybe<&2, BE.Entry<String, V>>) -> {PS.best(V, SC.append(BE.Entry<String, V>, xs, ys), s, acc) == PS.best(V, ys, s, PS.best(V, xs, s, acc)) : Maybe<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      best_app(V, t, ys, s, PS.pick(V, PS.is_prefix(BE.key(String, V, e), s), e, acc))

def bk_c2(-V: Data, +e2: BE.Entry<String, V>, +t2: List<&2, BE.Entry<String, V>>, +s: String, +e: BE.Entry<String, V>, +d: Maybe<&2, BE.Entry<String, V>>, b: Bool, +eb: {Nat.is_lt(String.length(BE.key(String, V, e)), String.length(BE.key(String, V, e2))) == b : Bool}, ih: @+e3: BE.Entry<String, V> -> {P.orM(V, PS.best(V, t2, s, Some{e3}), d) == PS.best(V, t2, s, Some{e3}) : Maybe<&2, BE.Entry<String, V>>}) -> {P.orM(V, PS.best(V, t2, s, PS.longer(V, e2, Some{e})), d) == PS.best(V, t2, s, PS.longer(V, e2, Some{e})) : Maybe<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(String.length(BE.key(String, V, e)), String.length(BE.key(String, V, e2))), True{}, eb) : {P.orM(V, PS.best(V, t2, s, PS.longer_if(V, _, e2, e)), d) == PS.best(V, t2, s, PS.longer_if(V, _, e2, e)) : Maybe<&2, BE.Entry<String, V>>}
      ih(e2)
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(String.length(BE.key(String, V, e)), String.length(BE.key(String, V, e2))), False{}, eb) : {P.orM(V, PS.best(V, t2, s, PS.longer_if(V, _, e2, e)), d) == PS.best(V, t2, s, PS.longer_if(V, _, e2, e)) : Maybe<&2, BE.Entry<String, V>>}
      ih(e)

def bk_c(-V: Data, +e2: BE.Entry<String, V>, +t2: List<&2, BE.Entry<String, V>>, +s: String, +e: BE.Entry<String, V>, +d: Maybe<&2, BE.Entry<String, V>>, b: Bool, +eb: {PS.is_prefix(BE.key(String, V, e2), s) == b : Bool}, ih: @+e3: BE.Entry<String, V> -> {P.orM(V, PS.best(V, t2, s, Some{e3}), d) == PS.best(V, t2, s, Some{e3}) : Maybe<&2, BE.Entry<String, V>>}) -> {P.orM(V, PS.best(V, Con{e2, t2}, s, Some{e}), d) == PS.best(V, Con{e2, t2}, s, Some{e}) : Maybe<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      %Equal.sym(Bool, PS.is_prefix(BE.key(String, V, e2), s), True{}, eb) : {P.orM(V, PS.best(V, t2, s, PS.pick(V, _, e2, Some{e})), d) == PS.best(V, t2, s, PS.pick(V, _, e2, Some{e})) : Maybe<&2, BE.Entry<String, V>>}
      bk_c2(V, e2, t2, s, e, d, Nat.is_lt(String.length(BE.key(String, V, e)), String.length(BE.key(String, V, e2))), {==}, ih)
    case False{}:
      %Equal.sym(Bool, PS.is_prefix(BE.key(String, V, e2), s), False{}, eb) : {P.orM(V, PS.best(V, t2, s, PS.pick(V, _, e2, Some{e})), d) == PS.best(V, t2, s, PS.pick(V, _, e2, Some{e})) : Maybe<&2, BE.Entry<String, V>>}
      ih(e)

# Once a candidate exists the result stays present.
def best_keep(-V: Data, +t: List<&2, BE.Entry<String, V>>, +s: String, +e: BE.Entry<String, V>, +d: Maybe<&2, BE.Entry<String, V>>) -> {P.orM(V, PS.best(V, t, s, Some{e}), d) == PS.best(V, t, s, Some{e}) : Maybe<&2, BE.Entry<String, V>>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e2, +t2}:
      bk_c(V, e2, t2, s, e, d, PS.is_prefix(BE.key(String, V, e2), s), {==}, e3 => best_keep(V, t2, s, e3, d))

def allgt(-V: Data, xs: List<&2, BE.Entry<String, V>>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Nat.is_lt(n, String.length(BE.key(String, V, e))), allgt(V, t, n))

def ba_c(-V: Data, +e: BE.Entry<String, V>, +t: List<&2, BE.Entry<String, V>>, +s: String, +a: BE.Entry<String, V>, b: Bool, +eb: {PS.is_prefix(BE.key(String, V, e), s) == b : Bool}, +hl: {Nat.is_lt(String.length(BE.key(String, V, a)), String.length(BE.key(String, V, e))) == True{} : Bool}, +ih: {PS.best(V, t, s, Some{a}) == P.orM(V, PS.best(V, t, s, None{}), Some{a}) : Maybe<&2, BE.Entry<String, V>>}) -> {PS.best(V, Con{e, t}, s, Some{a}) == P.orM(V, PS.best(V, Con{e, t}, s, None{}), Some{a}) : Maybe<&2, BE.Entry<String, V>>}:
  match b:
    case False{}:
      %Equal.sym(Bool, PS.is_prefix(BE.key(String, V, e), s), False{}, eb) : {PS.best(V, t, s, PS.pick(V, _, e, Some{a})) == P.orM(V, PS.best(V, t, s, PS.pick(V, _, e, None{})), Some{a}) : Maybe<&2, BE.Entry<String, V>>}
      ih
    case True{}:
      %Equal.sym(Bool, PS.is_prefix(BE.key(String, V, e), s), True{}, eb) : {PS.best(V, t, s, PS.pick(V, _, e, Some{a})) == P.orM(V, PS.best(V, t, s, PS.pick(V, _, e, None{})), Some{a}) : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Bool, Nat.is_lt(String.length(BE.key(String, V, a)), String.length(BE.key(String, V, e))), True{}, hl) : {PS.best(V, t, s, PS.longer_if(V, _, e, a)) == P.orM(V, PS.best(V, t, s, Some{e}), Some{a}) : Maybe<&2, BE.Entry<String, V>>}
      Equal.sym(Maybe<&2, BE.Entry<String, V>>, P.orM(V, PS.best(V, t, s, Some{e}), Some{a}), PS.best(V, t, s, Some{e}), best_keep(V, t, s, e, Some{a}))

# An accumulator shorter than every key only survives when nothing matches.
def best_acc(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +s: String, +a: BE.Entry<String, V>, +h: {allgt(V, xs, String.length(BE.key(String, V, a))) == True{} : Bool}) -> {PS.best(V, xs, s, Some{a}) == P.orM(V, PS.best(V, xs, s, None{}), Some{a}) : Maybe<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      ba_c(V, e, t, s, a, PS.is_prefix(BE.key(String, V, e), s), {==}, L.and_left(Nat.is_lt(String.length(BE.key(String, V, a)), String.length(BE.key(String, V, e))), allgt(V, t, String.length(BE.key(String, V, a))), h), best_acc(V, t, s, a, L.and_right(Nat.is_lt(String.length(BE.key(String, V, a)), String.length(BE.key(String, V, e))), allgt(V, t, String.length(BE.key(String, V, a))), h)))

def allgt_mapc(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +n: Nat, +h: {allgt(V, xs, n) == True{} : Bool}) -> {allgt(V, P.mapc(V, c, xs), 1n+n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, v}, +t}:
      L.and_intro(Nat.is_lt(1n+n, String.length(SCon{Chr{c}, k})), allgt(V, P.mapc(V, c, t), 1n+n), L.and_left(Nat.is_lt(n, String.length(k)), allgt(V, t, n), h), allgt_mapc(V, c, t, n, L.and_right(Nat.is_lt(n, String.length(k)), allgt(V, t, n), h)))

def allgt1(+k: String, +g: {keyok(None{}, k) == True{} : Bool}) -> {Nat.is_lt(0n, String.length(k)) == True{} : Bool}:
  match k:
    case SNil{}:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.false_true(g))
    case SCon{y, t}:
      {==}

def allgt_hg(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +h: {hg(V, xs, None{}) == True{} : Bool}) -> {allgt(V, xs, 0n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.and_intro(Nat.is_lt(0n, String.length(BE.key(String, V, e))), allgt(V, t, 0n), allgt1(BE.key(String, V, e), L.and_left(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)), allgt_hg(V, t, L.and_right(keyok(None{}, BE.key(String, V, e)), hg(V, t, None{}), h)))

def lif_shift(-V: Data, b: Bool, +c: U32, +k: String, +v: V, +ka: String, +va: V) -> {PS.longer_if(V, b, BE.Entry{SCon{Chr{c}, k}, v}, BE.Entry{SCon{Chr{c}, ka}, va}) == P.shift(V, c, PS.longer_if(V, b, BE.Entry{k, v}, BE.Entry{ka, va})) : Maybe<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def longer_shift(-V: Data, +c: U32, +k: String, +v: V, a: Maybe<&2, BE.Entry<String, V>>) -> {PS.longer(V, BE.Entry{SCon{Chr{c}, k}, v}, P.shift(V, c, a)) == P.shift(V, c, PS.longer(V, BE.Entry{k, v}, a)) : Maybe<&2, BE.Entry<String, V>>}:
  match a:
    case None{}:
      {==}
    case Some{BE.Entry{+ka, +va}}:
      lif_shift(V, Nat.is_lt(String.length(ka), String.length(k)), c, k, v, ka, va)

def pick_shift(-V: Data, b: Bool, +c: U32, +k: String, +v: V, +a: Maybe<&2, BE.Entry<String, V>>) -> {PS.pick(V, b, BE.Entry{SCon{Chr{c}, k}, v}, P.shift(V, c, a)) == P.shift(V, c, PS.pick(V, b, BE.Entry{k, v}, a)) : Maybe<&2, BE.Entry<String, V>>}:
  match b:
    case True{}:
      longer_shift(V, c, k, v, a)
    case False{}:
      {==}

def best_shift(-V: Data, +c: U32, +xs: List<&2, BE.Entry<String, V>>, +r: String, +a: Maybe<&2, BE.Entry<String, V>>) -> {PS.best(V, P.mapc(V, c, xs), SCon{Chr{c}, r}, P.shift(V, c, a)) == P.shift(V, c, PS.best(V, xs, r, a)) : Maybe<&2, BE.Entry<String, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{BE.Entry{+k, +v}, +t}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, u_refl(c)) : {PS.best(V, P.mapc(V, c, t), SCon{Chr{c}, r}, PS.pick(V, Bool.and(Cmp.is_eq(_), PS.is_prefix(k, r)), BE.Entry{SCon{Chr{c}, k}, v}, P.shift(V, c, a))) == P.shift(V, c, PS.best(V, t, r, PS.pick(V, PS.is_prefix(k, r), BE.Entry{k, v}, a))) : Maybe<&2, BE.Entry<String, V>>}
      Equal.trans(Maybe<&2, BE.Entry<String, V>>, PS.best(V, P.mapc(V, c, t), SCon{Chr{c}, r}, PS.pick(V, PS.is_prefix(k, r), BE.Entry{SCon{Chr{c}, k}, v}, P.shift(V, c, a))), PS.best(V, P.mapc(V, c, t), SCon{Chr{c}, r}, P.shift(V, c, PS.pick(V, PS.is_prefix(k, r), BE.Entry{k, v}, a))), P.shift(V, c, PS.best(V, t, r, PS.pick(V, PS.is_prefix(k, r), BE.Entry{k, v}, a))),
        Equal.cong(Maybe<&2, BE.Entry<String, V>>, Maybe<&2, BE.Entry<String, V>>, z => PS.best(V, P.mapc(V, c, t), SCon{Chr{c}, r}, z), PS.pick(V, PS.is_prefix(k, r), BE.Entry{SCon{Chr{c}, k}, v}, P.shift(V, c, a)), P.shift(V, c, PS.pick(V, PS.is_prefix(k, r), BE.Entry{k, v}, a)), pick_shift(V, PS.is_prefix(k, r), c, k, v, a)),
        best_shift(V, c, t, r, PS.pick(V, PS.is_prefix(k, r), BE.Entry{k, v}, a)))

def best_opt(-V: Data, +c: U32, val: Maybe<&2, V>, +r: String) -> {PS.best(V, P.opt(V, SCon{Chr{c}, SNil{}}, val), SCon{Chr{c}, r}, None{}) == P.shift(V, c, P.here(V, val)) : Maybe<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, u_refl(c)) : {PS.pick(V, Bool.and(Cmp.is_eq(_), PS.is_prefix(SNil{}, r)), BE.Entry{SCon{Chr{c}, SNil{}}, w}, None{}) == P.shift(V, c, P.here(V, Some{w})) : Maybe<&2, BE.Entry<String, V>>}
      {==}

def best_root(-V: Data, val: Maybe<&2, V>, +s: String) -> {PS.best(V, P.opt(V, SNil{}, val), s, None{}) == P.here(V, val) : Maybe<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      {==}
