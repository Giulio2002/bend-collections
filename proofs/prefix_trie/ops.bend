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
import ../balanced_search_tree/query.bend as Q
import ./keys.bend as K

# Sibling-list level: every trie walk refines the corresponding operation of
# the ordered-map model on the list's enumeration P.ent (keys relative to the
# list's parent). A node's enumeration is A ++ (B ++ C): its own entry, its
# children's entries prefixed with its character, and its later siblings'.

def okc(-V: Data, +c: U32, +val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +o: {K.ok(V, P.TNode{c, val, down, next}, lo) == True{} : Bool}) -> {K.gtM(lo, c) == True{} : Bool}:
  L.and_left(K.gtM(lo, c), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c})), o)

def okd(-V: Data, +c: U32, +val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +o: {K.ok(V, P.TNode{c, val, down, next}, lo) == True{} : Bool}) -> {K.ok(V, down, None{}) == True{} : Bool}:
  L.and_left(K.ok(V, down, None{}), K.ok(V, next, Some{c}), L.and_right(K.gtM(lo, c), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c})), o))

def okn(-V: Data, +c: U32, +val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +o: {K.ok(V, P.TNode{c, val, down, next}, lo) == True{} : Bool}) -> {K.ok(V, next, Some{c}) == True{} : Bool}:
  L.and_right(K.ok(V, down, None{}), K.ok(V, next, Some{c}), L.and_right(K.gtM(lo, c), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c})), o))

# Keys of the whole list t (first character c) are above x·rest when x < c.
def above_lt(-V: Data, +c: U32, +val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +o: {K.ok(V, P.TNode{c, val, down, next}, lo) == True{} : Bool}, +x: U32, +rest: String, +h: {U32.cmp(x, c) == LT{} : Cmp}) -> {K.hg(V, P.ent(V, P.TNode{c, val, down, next}), Some{x}) == True{} : Bool}:
  K.heads(V, P.TNode{c, val, down, next}, Some{x}, K.ok_relax(V, c, val, down, next, lo, Some{x}, o, SO.is_lt_of(U32.cmp(x, c), h)))

# ---- insertion ----

def chain_ent(-V: Data, +rest: String, +x: U32, +v: V, +next: P.Trie<V>) -> {P.ent(V, P.chain(V, rest, x, v, next)) == Con{BE.Entry{SCon{Chr{x}, rest}, v}, P.ent(V, next)} : List<&2, BE.Entry<String, V>>}:
  match rest:
    case SNil{}:
      {==}
    case SCon{Chr{+y}, +r}:
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, P.mapc(V, x, z), P.ent(V, next)), P.ent(V, P.chain(V, r, y, v, P.TNil{})), Con{BE.Entry{SCon{Chr{y}, r}, v}, Nil{}}, chain_ent(V, r, y, v, P.TNil{}))

def chain_ok(-V: Data, +rest: String, +x: U32, +v: V, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +gx: {K.gtM(lo, x) == True{} : Bool}, +on: {K.ok(V, next, Some{x}) == True{} : Bool}) -> {K.ok(V, P.chain(V, rest, x, v, next), lo) == True{} : Bool}:
  match rest:
    case SNil{}:
      L.and_intro(K.gtM(lo, x), Bool.and(True{}, K.ok(V, next, Some{x})), gx, L.and_intro(True{}, K.ok(V, next, Some{x}), {==}, on))
    case SCon{Chr{+y}, +r}:
      L.and_intro(K.gtM(lo, x), Bool.and(K.ok(V, P.chain(V, r, y, v, P.TNil{}), None{}), K.ok(V, next, Some{x})), gx, L.and_intro(K.ok(V, P.chain(V, r, y, v, P.TNil{}), None{}), K.ok(V, next, Some{x}), chain_ok(V, r, y, v, P.TNil{}, None{}, {==}, {==}), on))

def eqnil_ins(-V: Data, +c: U32, val: Maybe<&2, V>, +down: P.Trie<V>, +next: P.Trie<V>, +v: V, +hd: {K.hg(V, P.ent(V, down), None{}) == True{} : Bool}, +hn: {K.hg(V, P.ent(V, next), Some{c}) == True{} : Bool}) -> {P.ent(V, P.TNode{c, Some{v}, down, next}) == S.ins(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, v, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      +R = SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, down)), P.ent(V, next))
      Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, v, R), Con{BE.Entry{SCon{Chr{c}, SNil{}}, v}, R}, K.ins_front(V, R, SCon{Chr{c}, SNil{}}, v, K.above_app(V, P.mapc(V, c, P.ent(V, down)), P.ent(V, next), SCon{Chr{c}, SNil{}}, K.above_mapc_nil(V, c, P.ent(V, down), hd), K.above_hg(V, P.ent(V, next), c, SNil{}, hn))))
    case Some{+w}:
      +R = SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, down)), P.ent(V, next))
      Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, v, Con{BE.Entry{SCon{Chr{c}, SNil{}}, w}, R}), Con{BE.Entry{SCon{Chr{c}, SNil{}}, v}, R}, SP.ins_eq(~String, ~String.order, V, BE.Entry{SCon{Chr{c}, SNil{}}, w}, R, SCon{Chr{c}, SNil{}}, v, O.refl(~String, ~String.order, ~O.string_order, SCon{Chr{c}, SNil{}})))

def ins_ent(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +v: V, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {P.ent(V, P.ins(V, t, x, a, rest, v)) == S.ins(~String, ~String.order, V, SCon{Chr{x}, rest}, v, P.ent(V, t)) : List<&2, BE.Entry<String, V>>}:
  match t a rest:
    case P.TNil{} _ _:
      chain_ent(V, rest, x, v, P.TNil{})
    case P.TNode{+c, +val, +down, +next} LT{} _:
      +nd = {P.TNode{c, val, down, next} : P.Trie<V>}
      Equal.trans(List<&2, BE.Entry<String, V>>, P.ent(V, P.chain(V, rest, x, v, nd)), Con{BE.Entry{SCon{Chr{x}, rest}, v}, P.ent(V, nd)}, S.ins(~String, ~String.order, V, SCon{Chr{x}, rest}, v, P.ent(V, nd)),
        chain_ent(V, rest, x, v, nd),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, SCon{Chr{x}, rest}, v, P.ent(V, nd)), Con{BE.Entry{SCon{Chr{x}, rest}, v}, P.ent(V, nd)}, K.ins_front(V, P.ent(V, nd), SCon{Chr{x}, rest}, v, K.above_hg(V, P.ent(V, nd), x, rest, above_lt(V, c, val, down, next, lo, o, x, rest, ea)))))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +k = {SCon{Chr{x}, rest} : String}
      +cx = SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)
      Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, P.ent(V, P.ins(V, next, x, P.hc(V, x, next), rest, v)))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.ins(~String, ~String.order, V, k, v, C))), S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, z)), P.ent(V, P.ins(V, next, x, P.hc(V, x, next), rest, v)), S.ins(~String, ~String.order, V, k, v, C), ins_ent(V, next, x, P.hc(V, x, next), rest, v, {==}, Some{c}, okn(V, c, val, down, next, lo, o))),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.ins(~String, ~String.order, V, k, v, C))),
          Equal.trans(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.ins(~String, ~String.order, V, k, v, C))),
            SP.ins_pass(~String, ~String.order, ~O.string_order, V, A, SC.append(BE.Entry<String, V>, B, C), k, v, K.below_opt(V, c, val, x, rest, cx)),
            Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, B, S.ins(~String, ~String.order, V, k, v, C)), SP.ins_pass(~String, ~String.order, ~O.string_order, V, B, C, k, v, K.below_mapc(V, c, P.ent(V, down), x, rest, cx))))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.ent(V, P.ins(V, P.TNode{c, val, down, next}, x, EQ{}, SNil{}, v)) == S.ins(~String, ~String.order, V, SCon{Chr{_}, SNil{}}, v, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      eqnil_ins(V, c, val, down, next, v, K.heads(V, down, None{}, okd(V, c, val, down, next, lo, o)), K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o)))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +k = {SCon{Chr{c}, SCon{Chr{y}, r}} : String}
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.ent(V, P.ins(V, P.TNode{c, val, down, next}, x, EQ{}, SCon{Chr{y}, r}, v)) == S.ins(~String, ~String.order, V, SCon{Chr{_}, SCon{Chr{y}, r}}, v, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, P.ins(V, down, y, P.hc(V, y, down), r, v))), C)), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, B), C)), S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, z, C)), P.mapc(V, c, P.ent(V, P.ins(V, down, y, P.hc(V, y, down), r, v))), S.ins(~String, ~String.order, V, k, v, B),
          Equal.trans(List<&2, BE.Entry<String, V>>, P.mapc(V, c, P.ent(V, P.ins(V, down, y, P.hc(V, y, down), r, v))), P.mapc(V, c, S.ins(~String, ~String.order, V, SCon{Chr{y}, r}, v, P.ent(V, down))), S.ins(~String, ~String.order, V, k, v, B),
            Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => P.mapc(V, c, z), P.ent(V, P.ins(V, down, y, P.hc(V, y, down), r, v)), S.ins(~String, ~String.order, V, SCon{Chr{y}, r}, v, P.ent(V, down)), ins_ent(V, down, y, P.hc(V, y, down), r, v, {==}, None{}, okd(V, c, val, down, next, lo, o))),
            K.map_ins(V, c, SCon{Chr{y}, r}, v, P.ent(V, down)))),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, B), C)),
          Equal.trans(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, B), C)),
            SP.ins_pass(~String, ~String.order, ~O.string_order, V, A, SC.append(BE.Entry<String, V>, B, C), k, v, K.below_opt_eq(V, c, val, Chr{y}, r)),
            Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, S.ins(~String, ~String.order, V, k, v, B), C), K.ins_split(V, B, C, k, v, K.above_hg(V, C, c, SCon{Chr{y}, r}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o))))))))

def ins_okp(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +v: V, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}, +gx: {K.gtM(lo, x) == True{} : Bool}) -> {K.ok(V, P.ins(V, t, x, a, rest, v), lo) == True{} : Bool}:
  match t a rest:
    case P.TNil{} _ _:
      chain_ok(V, rest, x, v, P.TNil{}, lo, gx, {==})
    case P.TNode{+c, +val, +down, +next} LT{} _:
      chain_ok(V, rest, x, v, P.TNode{c, val, down, next}, lo, gx, K.ok_relax(V, c, val, down, next, lo, Some{x}, o, SO.is_lt_of(U32.cmp(x, c), ea)))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      L.and_intro(K.gtM(lo, c), Bool.and(K.ok(V, down, None{}), K.ok(V, P.ins(V, next, x, P.hc(V, x, next), rest, v), Some{c})), okc(V, c, val, down, next, lo, o),
        L.and_intro(K.ok(V, down, None{}), K.ok(V, P.ins(V, next, x, P.hc(V, x, next), rest, v), Some{c}), okd(V, c, val, down, next, lo, o),
          ins_okp(V, next, x, P.hc(V, x, next), rest, v, {==}, Some{c}, okn(V, c, val, down, next, lo, o), SO.is_lt_of(U32.cmp(c, x), SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      o
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      L.and_intro(K.gtM(lo, c), Bool.and(K.ok(V, P.ins(V, down, y, P.hc(V, y, down), r, v), None{}), K.ok(V, next, Some{c})), okc(V, c, val, down, next, lo, o),
        L.and_intro(K.ok(V, P.ins(V, down, y, P.hc(V, y, down), r, v), None{}), K.ok(V, next, Some{c}), ins_okp(V, down, y, P.hc(V, y, down), r, v, {==}, None{}, okd(V, c, val, down, next, lo, o), {==}), okn(V, c, val, down, next, lo, o)))

# ---- lookup ----

def find_skip(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +k: String, +bA: {SO.below(~String, ~String.order, V, A, k) == True{} : Bool}, +bB: {SO.below(~String, ~String.order, V, B, k) == True{} : Bool}) -> {S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) == S.find(~String, ~String.order, V, k, C) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SP.orM(V, S.find(~String, ~String.order, V, k, A), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, C),
    SP.find_app(~String, ~String.order, V, A, SC.append(BE.Entry<String, V>, B, C), k),
    Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~String, ~String.order, V, k, A), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SP.orM(V, None{}, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, C),
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, A), None{}, SP.find_below(~String, ~String.order, ~O.string_order, V, A, k, bA)),
      Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SP.orM(V, S.find(~String, ~String.order, V, k, B), S.find(~String, ~String.order, V, k, C)), S.find(~String, ~String.order, V, k, C),
        SP.find_app(~String, ~String.order, V, B, C, k),
        Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~String, ~String.order, V, k, C)), S.find(~String, ~String.order, V, k, B), None{}, SP.find_below(~String, ~String.order, ~O.string_order, V, B, k, bB)))))

def find_mid(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +k: String, +bA: {SO.below(~String, ~String.order, V, A, k) == True{} : Bool}, +aC: {SO.above(~String, ~String.order, V, C, k) == True{} : Bool}) -> {S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) == S.find(~String, ~String.order, V, k, B) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SP.orM(V, S.find(~String, ~String.order, V, k, A), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, B),
    SP.find_app(~String, ~String.order, V, A, SC.append(BE.Entry<String, V>, B, C), k),
    Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~String, ~String.order, V, k, A), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SP.orM(V, None{}, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, B),
      Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, A), None{}, SP.find_below(~String, ~String.order, ~O.string_order, V, A, k, bA)),
      Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SP.orM(V, S.find(~String, ~String.order, V, k, B), S.find(~String, ~String.order, V, k, C)), S.find(~String, ~String.order, V, k, B),
        SP.find_app(~String, ~String.order, V, B, C, k),
        Equal.trans(Maybe<&2, V>, SP.orM(V, S.find(~String, ~String.order, V, k, B), S.find(~String, ~String.order, V, k, C)), SP.orM(V, S.find(~String, ~String.order, V, k, B), None{}), S.find(~String, ~String.order, V, k, B),
          Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, S.find(~String, ~String.order, V, k, B), z), S.find(~String, ~String.order, V, k, C), None{}, SP.find_above(~String, ~String.order, V, C, k, aC)),
          Q.orM_none(V, S.find(~String, ~String.order, V, k, B))))))

def eqnil_find(-V: Data, +c: U32, val: Maybe<&2, V>, +R: List<&2, BE.Entry<String, V>>, +aR: {SO.above(~String, ~String.order, V, R, SCon{Chr{c}, SNil{}}) == True{} : Bool}) -> {val == S.find(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, SC.append(BE.Entry<String, V>, P.opt(V, SCon{Chr{c}, SNil{}}, val), R)) : Maybe<&2, V>}:
  match val:
    case None{}:
      Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, R), None{}, SP.find_above(~String, ~String.order, V, R, SCon{Chr{c}, SNil{}}, aR))
    case Some{+w}:
      Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, Con{BE.Entry{SCon{Chr{c}, SNil{}}, w}, R}), Some{w}, SP.find_eq(~String, ~String.order, V, BE.Entry{SCon{Chr{c}, SNil{}}, w}, R, SCon{Chr{c}, SNil{}}, O.refl(~String, ~String.order, ~O.string_order, SCon{Chr{c}, SNil{}})))

def find_ok(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {P.find(V, t, x, a, rest) == S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, P.ent(V, t)) : Maybe<&2, V>}:
  match t a rest:
    case P.TNil{} _ _:
      {==}
    case P.TNode{+c, +val, +down, +next} LT{} _:
      +nd = {P.TNode{c, val, down, next} : P.Trie<V>}
      Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, P.ent(V, nd)), None{}, SP.find_above(~String, ~String.order, V, P.ent(V, nd), SCon{Chr{x}, rest}, K.above_hg(V, P.ent(V, nd), x, rest, above_lt(V, c, val, down, next, lo, o, x, rest, ea))))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +cx = SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)
      Equal.trans(Maybe<&2, V>, P.find(V, next, x, P.hc(V, x, next), rest), S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, C), S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        find_ok(V, next, x, P.hc(V, x, next), rest, {==}, Some{c}, okn(V, c, val, down, next, lo, o)),
        Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, SCon{Chr{x}, rest}, C), find_skip(V, A, B, C, SCon{Chr{x}, rest}, K.below_opt(V, c, val, x, rest, cx), K.below_mapc(V, c, P.ent(V, down), x, rest, cx))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.find(V, P.TNode{c, val, down, next}, x, EQ{}, SNil{}) == S.find(~String, ~String.order, V, SCon{Chr{_}, SNil{}}, P.ent(V, P.TNode{c, val, down, next})) : Maybe<&2, V>}
      eqnil_find(V, c, val, SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, down)), P.ent(V, next)), K.above_app(V, P.mapc(V, c, P.ent(V, down)), P.ent(V, next), SCon{Chr{c}, SNil{}}, K.above_mapc_nil(V, c, P.ent(V, down), K.heads(V, down, None{}, okd(V, c, val, down, next, lo, o))), K.above_hg(V, P.ent(V, next), c, SNil{}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o)))))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +k = {SCon{Chr{c}, SCon{Chr{y}, r}} : String}
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.find(V, P.TNode{c, val, down, next}, x, EQ{}, SCon{Chr{y}, r}) == S.find(~String, ~String.order, V, SCon{Chr{_}, SCon{Chr{y}, r}}, P.ent(V, P.TNode{c, val, down, next})) : Maybe<&2, V>}
      Equal.trans(Maybe<&2, V>, P.find(V, down, y, P.hc(V, y, down), r), S.find(~String, ~String.order, V, SCon{Chr{y}, r}, P.ent(V, down)), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        find_ok(V, down, y, P.hc(V, y, down), r, {==}, None{}, okd(V, c, val, down, next, lo, o)),
        Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, SCon{Chr{y}, r}, P.ent(V, down)),
          Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), S.find(~String, ~String.order, V, k, B), S.find(~String, ~String.order, V, SCon{Chr{y}, r}, P.ent(V, down)),
            find_mid(V, A, B, C, k, K.below_opt_eq(V, c, val, Chr{y}, r), K.above_hg(V, C, c, SCon{Chr{y}, r}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o)))),
            K.map_find(V, c, SCon{Chr{y}, r}, P.ent(V, down)))))

# ---- removal ----

def prune_ent(-V: Data, +c: U32, val: Maybe<&2, V>, down: P.Trie<V>, +next: P.Trie<V>) -> {P.ent(V, P.prune(V, c, val, down, next)) == P.ent(V, P.TNode{c, val, down, next}) : List<&2, BE.Entry<String, V>>}:
  match val down:
    case None{} P.TNil{}:
      {==}
    case None{} P.TNode{c2, v2, d2, n2}:
      {==}
    case Some{w} P.TNil{}:
      {==}
    case Some{w} P.TNode{c2, v2, d2, n2}:
      {==}

def ok_weaken(-V: Data, +t: P.Trie<V>, +c: U32, +lo: Maybe<&2, U32>, +h: {K.gtM(lo, c) == True{} : Bool}, +o: {K.ok(V, t, Some{c}) == True{} : Bool}) -> {K.ok(V, t, lo) == True{} : Bool}:
  match t:
    case P.TNil{}:
      {==}
    case P.TNode{+c2, +val, +down, +next}:
      L.and_intro(K.gtM(lo, c2), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c2})), K.gt_trans(lo, c, c2, h, L.and_left(Cmp.is_lt(U32.cmp(c, c2)), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c2})), o)), L.and_right(Cmp.is_lt(U32.cmp(c, c2)), Bool.and(K.ok(V, down, None{}), K.ok(V, next, Some{c2})), o))

def prune_ok(-V: Data, +c: U32, val: Maybe<&2, V>, down: P.Trie<V>, +next: P.Trie<V>, +lo: Maybe<&2, U32>, +g: {K.gtM(lo, c) == True{} : Bool}, +od: {K.ok(V, down, None{}) == True{} : Bool}, +on: {K.ok(V, next, Some{c}) == True{} : Bool}) -> {K.ok(V, P.prune(V, c, val, down, next), lo) == True{} : Bool}:
  match val down:
    case None{} P.TNil{}:
      ok_weaken(V, next, c, lo, g, on)
    case None{} P.TNode{+c2, +v2, +d2, +n2}:
      L.and_intro(K.gtM(lo, c), Bool.and(K.ok(V, P.TNode{c2, v2, d2, n2}, None{}), K.ok(V, next, Some{c})), g, L.and_intro(K.ok(V, P.TNode{c2, v2, d2, n2}, None{}), K.ok(V, next, Some{c}), od, on))
    case Some{w} P.TNil{}:
      L.and_intro(K.gtM(lo, c), Bool.and(True{}, K.ok(V, next, Some{c})), g, L.and_intro(True{}, K.ok(V, next, Some{c}), od, on))
    case Some{w} P.TNode{+c2, +v2, +d2, +n2}:
      L.and_intro(K.gtM(lo, c), Bool.and(K.ok(V, P.TNode{c2, v2, d2, n2}, None{}), K.ok(V, next, Some{c})), g, L.and_intro(K.ok(V, P.TNode{c2, v2, d2, n2}, None{}), K.ok(V, next, Some{c}), od, on))

def del_skip(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +k: String, +bA: {SO.below(~String, ~String.order, V, A, k) == True{} : Bool}, +bB: {SO.below(~String, ~String.order, V, B, k) == True{} : Bool}) -> {S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) == SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C))) : List<&2, BE.Entry<String, V>>}:
  Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, A), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C))),
    SP.del_app(~String, ~String.order, V, A, SC.append(BE.Entry<String, V>, B, C), k),
    Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, A), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C))),
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, z, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.del(~String, ~String.order, V, k, A), A, SP.del_below(~String, ~String.order, ~O.string_order, V, A, k, bA)),
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C)),
        Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), S.del(~String, ~String.order, V, k, C)), SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C)),
          SP.del_app(~String, ~String.order, V, B, C, k),
          Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, z, S.del(~String, ~String.order, V, k, C)), S.del(~String, ~String.order, V, k, B), B, SP.del_below(~String, ~String.order, ~O.string_order, V, B, k, bB))))))

def del_mid(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +k: String, +bA: {SO.below(~String, ~String.order, V, A, k) == True{} : Bool}, +aC: {SO.above(~String, ~String.order, V, C, k) == True{} : Bool}) -> {S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) == SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C)) : List<&2, BE.Entry<String, V>>}:
  Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, A), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C)),
    SP.del_app(~String, ~String.order, V, A, SC.append(BE.Entry<String, V>, B, C), k),
    Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, A), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C)),
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, z, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C))), S.del(~String, ~String.order, V, k, A), A, SP.del_below(~String, ~String.order, ~O.string_order, V, A, k, bA)),
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C),
        Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), S.del(~String, ~String.order, V, k, C)), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C),
          SP.del_app(~String, ~String.order, V, B, C, k),
          Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), z), S.del(~String, ~String.order, V, k, C), C, SP.del_above(~String, ~String.order, V, C, k, aC))))))

def del_self(-V: Data, +c: U32, val: Maybe<&2, V>, +R: List<&2, BE.Entry<String, V>>, +aR: {SO.above(~String, ~String.order, V, R, SCon{Chr{c}, SNil{}}) == True{} : Bool}) -> {S.del(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, SC.append(BE.Entry<String, V>, P.opt(V, SCon{Chr{c}, SNil{}}, val), R)) == R : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      SP.del_above(~String, ~String.order, V, R, SCon{Chr{c}, SNil{}}, aR)
    case Some{+w}:
      Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, Con{BE.Entry{SCon{Chr{c}, SNil{}}, w}, R}), S.del(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, R), R,
        SP.del_eq(~String, ~String.order, V, BE.Entry{SCon{Chr{c}, SNil{}}, w}, R, SCon{Chr{c}, SNil{}}, O.refl(~String, ~String.order, ~O.string_order, SCon{Chr{c}, SNil{}})),
        SP.del_above(~String, ~String.order, V, R, SCon{Chr{c}, SNil{}}, aR))

def rem_ent(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {P.ent(V, P.rem(V, t, x, a, rest)) == S.del(~String, ~String.order, V, SCon{Chr{x}, rest}, P.ent(V, t)) : List<&2, BE.Entry<String, V>>}:
  match t a rest:
    case P.TNil{} _ _:
      {==}
    case P.TNode{+c, +val, +down, +next} LT{} _:
      +nd = {P.TNode{c, val, down, next} : P.Trie<V>}
      Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SCon{Chr{x}, rest}, P.ent(V, nd)), P.ent(V, nd), SP.del_above(~String, ~String.order, V, P.ent(V, nd), SCon{Chr{x}, rest}, K.above_hg(V, P.ent(V, nd), x, rest, above_lt(V, c, val, down, next, lo, o, x, rest, ea))))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +k = {SCon{Chr{x}, rest} : String}
      +cx = SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)
      Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, P.ent(V, P.rem(V, next, x, P.hc(V, x, next), rest)))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C))), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, z)), P.ent(V, P.rem(V, next, x, P.hc(V, x, next), rest)), S.del(~String, ~String.order, V, k, C), rem_ent(V, next, x, P.hc(V, x, next), rest, {==}, Some{c}, okn(V, c, val, down, next, lo, o))),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, S.del(~String, ~String.order, V, k, C))), del_skip(V, A, B, C, k, K.below_opt(V, c, val, x, rest, cx), K.below_mapc(V, c, P.ent(V, down), x, rest, cx))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      +R = SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, down)), P.ent(V, next))
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.ent(V, P.rem(V, P.TNode{c, val, down, next}, x, EQ{}, SNil{})) == S.del(~String, ~String.order, V, SCon{Chr{_}, SNil{}}, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      Equal.trans(List<&2, BE.Entry<String, V>>, P.ent(V, P.prune(V, c, None{}, down, next)), R, S.del(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, SC.append(BE.Entry<String, V>, P.opt(V, SCon{Chr{c}, SNil{}}, val), R)),
        prune_ent(V, c, None{}, down, next),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SCon{Chr{c}, SNil{}}, SC.append(BE.Entry<String, V>, P.opt(V, SCon{Chr{c}, SNil{}}, val), R)), R, del_self(V, c, val, R, K.above_app(V, P.mapc(V, c, P.ent(V, down)), P.ent(V, next), SCon{Chr{c}, SNil{}}, K.above_mapc_nil(V, c, P.ent(V, down), K.heads(V, down, None{}, okd(V, c, val, down, next, lo, o))), K.above_hg(V, P.ent(V, next), c, SNil{}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o)))))))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +k = {SCon{Chr{c}, SCon{Chr{y}, r}} : String}
      +d1 = P.rem(V, down, y, P.hc(V, y, down), r)
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.ent(V, P.rem(V, P.TNode{c, val, down, next}, x, EQ{}, SCon{Chr{y}, r})) == S.del(~String, ~String.order, V, SCon{Chr{_}, SCon{Chr{y}, r}}, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      Equal.trans(List<&2, BE.Entry<String, V>>, P.ent(V, P.prune(V, c, val, d1, next)), P.ent(V, P.TNode{c, val, d1, next}), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        prune_ent(V, c, val, d1, next),
        Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, P.mapc(V, c, P.ent(V, d1)), C)), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C)), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
          Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, z, C)), P.mapc(V, c, P.ent(V, d1)), S.del(~String, ~String.order, V, k, B),
            Equal.trans(List<&2, BE.Entry<String, V>>, P.mapc(V, c, P.ent(V, d1)), P.mapc(V, c, S.del(~String, ~String.order, V, SCon{Chr{y}, r}, P.ent(V, down))), S.del(~String, ~String.order, V, k, B),
              Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => P.mapc(V, c, z), P.ent(V, d1), S.del(~String, ~String.order, V, SCon{Chr{y}, r}, P.ent(V, down)), rem_ent(V, down, y, P.hc(V, y, down), r, {==}, None{}, okd(V, c, val, down, next, lo, o))),
              K.map_del(V, c, SCon{Chr{y}, r}, P.ent(V, down)))),
          Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, B), C)), del_mid(V, A, B, C, k, K.below_opt_eq(V, c, val, Chr{y}, r), K.above_hg(V, C, c, SCon{Chr{y}, r}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o)))))))

def rem_okp(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {K.ok(V, P.rem(V, t, x, a, rest), lo) == True{} : Bool}:
  match t a rest:
    case P.TNil{} _ _:
      {==}
    case P.TNode{+c, +val, +down, +next} LT{} _:
      o
    case P.TNode{+c, +val, +down, +next} GT{} _:
      L.and_intro(K.gtM(lo, c), Bool.and(K.ok(V, down, None{}), K.ok(V, P.rem(V, next, x, P.hc(V, x, next), rest), Some{c})), okc(V, c, val, down, next, lo, o),
        L.and_intro(K.ok(V, down, None{}), K.ok(V, P.rem(V, next, x, P.hc(V, x, next), rest), Some{c}), okd(V, c, val, down, next, lo, o), rem_okp(V, next, x, P.hc(V, x, next), rest, {==}, Some{c}, okn(V, c, val, down, next, lo, o))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      prune_ok(V, c, None{}, down, next, lo, okc(V, c, val, down, next, lo, o), okd(V, c, val, down, next, lo, o), okn(V, c, val, down, next, lo, o))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      prune_ok(V, c, val, P.rem(V, down, y, P.hc(V, y, down), r), next, lo, okc(V, c, val, down, next, lo, o), rem_okp(V, down, y, P.hc(V, y, down), r, {==}, None{}, okd(V, c, val, down, next, lo, o)), okn(V, c, val, down, next, lo, o))

# ---- prefix listing ----

def wp_skip(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +p: String, +nA: {PS.with_prefix(V, p, A) == Nil{} : List<&2, BE.Entry<String, V>>}, +nB: {PS.with_prefix(V, p, B) == Nil{} : List<&2, BE.Entry<String, V>>}) -> {PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) == PS.with_prefix(V, p, C) : List<&2, BE.Entry<String, V>>}:
  %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, A), PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C))), K.wp_app(V, p, A, SC.append(BE.Entry<String, V>, B, C))) : {_ == PS.with_prefix(V, p, C) : List<&2, BE.Entry<String, V>>}
  %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, A), Nil{}, nA) : {SC.append(BE.Entry<String, V>, _, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C))) == PS.with_prefix(V, p, C) : List<&2, BE.Entry<String, V>>}
  %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), PS.with_prefix(V, p, C)), K.wp_app(V, p, B, C)) : {_ == PS.with_prefix(V, p, C) : List<&2, BE.Entry<String, V>>}
  %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, B), Nil{}, nB) : {SC.append(BE.Entry<String, V>, _, PS.with_prefix(V, p, C)) == PS.with_prefix(V, p, C) : List<&2, BE.Entry<String, V>>}
  {==}

def wp_opt_self(-V: Data, +c: U32, val: Maybe<&2, V>) -> {PS.with_prefix(V, SCon{Chr{c}, SNil{}}, P.opt(V, SCon{Chr{c}, SNil{}}, val)) == P.opt(V, SCon{Chr{c}, SNil{}}, val) : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, K.u_refl(c)) : {PS.keep_if(V, Bool.and(Cmp.is_eq(_), True{}), BE.Entry{SCon{Chr{c}, SNil{}}, w}, Nil{}) == Con{BE.Entry{SCon{Chr{c}, SNil{}}, w}, Nil{}} : List<&2, BE.Entry<String, V>>}
      {==}

def wp_opt_long(-V: Data, +c: U32, val: Maybe<&2, V>, +y: U32, +r: String) -> {PS.with_prefix(V, SCon{Chr{c}, SCon{Chr{y}, r}}, P.opt(V, SCon{Chr{c}, SNil{}}, val)) == Nil{} : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      %Equal.sym(Cmp, U32.cmp(c, c), EQ{}, K.u_refl(c)) : {PS.keep_if(V, Bool.and(Cmp.is_eq(_), False{}), BE.Entry{SCon{Chr{c}, SNil{}}, w}, Nil{}) == Nil{} : List<&2, BE.Entry<String, V>>}
      {==}

def pe_ok(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {P.pe(V, t, x, a, rest) == PS.with_prefix(V, SCon{Chr{x}, rest}, P.ent(V, t)) : List<&2, BE.Entry<String, V>>}:
  match t a rest:
    case P.TNil{} _ _:
      {==}
    case P.TNode{+c, +val, +down, +next} LT{} _:
      +nd = {P.TNode{c, val, down, next} : P.Trie<V>}
      Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, SCon{Chr{x}, rest}, P.ent(V, nd)), Nil{}, K.wp_none(V, SCon{Chr{x}, rest}, P.ent(V, nd), K.np_hg(V, P.ent(V, nd), x, rest, above_lt(V, c, val, down, next, lo, o, x, rest, ea))))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +cx = SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)
      Equal.trans(List<&2, BE.Entry<String, V>>, P.pe(V, next, x, P.hc(V, x, next), rest), PS.with_prefix(V, SCon{Chr{x}, rest}, C), PS.with_prefix(V, SCon{Chr{x}, rest}, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))),
        pe_ok(V, next, x, P.hc(V, x, next), rest, {==}, Some{c}, okn(V, c, val, down, next, lo, o)),
        Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, SCon{Chr{x}, rest}, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), PS.with_prefix(V, SCon{Chr{x}, rest}, C), wp_skip(V, A, B, C, SCon{Chr{x}, rest}, K.wp_none(V, SCon{Chr{x}, rest}, A, K.np_opt(V, c, val, x, rest, cx)), K.wp_none(V, SCon{Chr{x}, rest}, B, K.np_mapc(V, c, P.ent(V, down), x, rest, cx)))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +p = {SCon{Chr{c}, SNil{}} : String}
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.pe(V, P.TNode{c, val, down, next}, x, EQ{}, SNil{}) == PS.with_prefix(V, SCon{Chr{_}, SNil{}}, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, P.mapc(V, c, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), P.ent(V, down))), SC.append(BE.Entry<String, V>, P.mapc(V, c, P.opt(V, SNil{}, val)), B), K.mapc_app(V, c, P.opt(V, SNil{}, val), P.ent(V, down))) : {_ == PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, P.mapc(V, c, P.opt(V, SNil{}, val)), A, K.mapc_opt(V, c, val)) : {SC.append(BE.Entry<String, V>, _, B) == PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, A), PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C))), K.wp_app(V, p, A, SC.append(BE.Entry<String, V>, B, C))) : {SC.append(BE.Entry<String, V>, A, B) == _ : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), PS.with_prefix(V, p, C)), K.wp_app(V, p, B, C)) : {SC.append(BE.Entry<String, V>, A, B) == SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, A), _) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, A), A, wp_opt_self(V, c, val)) : {SC.append(BE.Entry<String, V>, A, B) == SC.append(BE.Entry<String, V>, _, SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), PS.with_prefix(V, p, C))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, C), Nil{}, K.wp_none(V, p, C, K.np_hg(V, C, c, SNil{}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o))))) : {SC.append(BE.Entry<String, V>, A, B) == SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), _)) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, B), P.mapc(V, c, PS.with_prefix(V, SNil{}, P.ent(V, down))), K.map_pfx(V, c, SNil{}, P.ent(V, down))) : {SC.append(BE.Entry<String, V>, A, B) == SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, _, Nil{})) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, SNil{}, P.ent(V, down)), P.ent(V, down), K.pfx_nil(V, P.ent(V, down))) : {SC.append(BE.Entry<String, V>, A, B) == SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, P.mapc(V, c, _), Nil{})) : List<&2, BE.Entry<String, V>>}
      Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), B, SC.append(BE.Entry<String, V>, B, Nil{}), Equal.sym(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, B, Nil{}), B, LL.append_nil(BE.Entry<String, V>, B)))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +p = {SCon{Chr{c}, SCon{Chr{y}, r}} : String}
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.pe(V, P.TNode{c, val, down, next}, x, EQ{}, SCon{Chr{y}, r}) == PS.with_prefix(V, SCon{Chr{_}, SCon{Chr{y}, r}}, P.ent(V, P.TNode{c, val, down, next})) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, P.pe(V, down, y, P.hc(V, y, down), r), PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down)), pe_ok(V, down, y, P.hc(V, y, down), r, {==}, None{}, okd(V, c, val, down, next, lo, o))) : {P.mapc(V, c, _) == PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C))), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, A), PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C))), K.wp_app(V, p, A, SC.append(BE.Entry<String, V>, B, C))) : {P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))) == _ : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, SC.append(BE.Entry<String, V>, B, C)), SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), PS.with_prefix(V, p, C)), K.wp_app(V, p, B, C)) : {P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))) == SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, A), _) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, A), Nil{}, wp_opt_long(V, c, val, y, r)) : {P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))) == SC.append(BE.Entry<String, V>, _, SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), PS.with_prefix(V, p, C))) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, C), Nil{}, K.wp_none(V, p, C, K.np_hg(V, C, c, SCon{Chr{y}, r}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o))))) : {P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))) == SC.append(BE.Entry<String, V>, PS.with_prefix(V, p, B), _) : List<&2, BE.Entry<String, V>>}
      %Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, p, B), P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))), K.map_pfx(V, c, SCon{Chr{y}, r}, P.ent(V, down))) : {P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))) == SC.append(BE.Entry<String, V>, _, Nil{}) : List<&2, BE.Entry<String, V>>}
      Equal.sym(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))), Nil{}), P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down))), LL.append_nil(BE.Entry<String, V>, P.mapc(V, c, PS.with_prefix(V, SCon{Chr{y}, r}, P.ent(V, down)))))

# ---- longest prefix ----

def orM_nil(-V: Data, +m: Maybe<&2, BE.Entry<String, V>>) -> {P.orM(V, m, None{}) == m : Maybe<&2, BE.Entry<String, V>>}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

# The node's own value (length 0 relative key) is shorter than every child key.
def best_here(-V: Data, +xs: List<&2, BE.Entry<String, V>>, +s: String, val: Maybe<&2, V>, +h: {K.allgt(V, xs, 0n) == True{} : Bool}) -> {PS.best(V, xs, s, P.here(V, val)) == P.orM(V, PS.best(V, xs, s, None{}), P.here(V, val)) : Maybe<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      Equal.sym(Maybe<&2, BE.Entry<String, V>>, P.orM(V, PS.best(V, xs, s, None{}), None{}), PS.best(V, xs, s, None{}), orM_nil(V, PS.best(V, xs, s, None{})))
    case Some{w}:
      K.best_acc(V, xs, s, BE.Entry{SNil{}, w}, h)

def best_skip(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +s: String, +acc: Maybe<&2, BE.Entry<String, V>>, +nA: {K.nm(V, A, s) == True{} : Bool}, +nB: {K.nm(V, B, s) == True{} : Bool}) -> {PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, acc) == PS.best(V, C, s, acc) : Maybe<&2, BE.Entry<String, V>>}:
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, acc), PS.best(V, SC.append(BE.Entry<String, V>, B, C), s, PS.best(V, A, s, acc)), K.best_app(V, A, SC.append(BE.Entry<String, V>, B, C), s, acc)) : {_ == PS.best(V, C, s, acc) : Maybe<&2, BE.Entry<String, V>>}
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, A, s, acc), acc, K.best_none(V, A, s, acc, nA)) : {PS.best(V, SC.append(BE.Entry<String, V>, B, C), s, _) == PS.best(V, C, s, acc) : Maybe<&2, BE.Entry<String, V>>}
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, B, C), s, acc), PS.best(V, C, s, PS.best(V, B, s, acc)), K.best_app(V, B, C, s, acc)) : {_ == PS.best(V, C, s, acc) : Maybe<&2, BE.Entry<String, V>>}
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, B, s, acc), acc, K.best_none(V, B, s, acc, nB)) : {PS.best(V, C, s, _) == PS.best(V, C, s, acc) : Maybe<&2, BE.Entry<String, V>>}
  {==}

# Own entry first, then the children; later siblings never match.
def best_node(-V: Data, +A: List<&2, BE.Entry<String, V>>, +B: List<&2, BE.Entry<String, V>>, +C: List<&2, BE.Entry<String, V>>, +s: String, +nC: {K.nm(V, C, s) == True{} : Bool}) -> {PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, None{}) == PS.best(V, B, s, PS.best(V, A, s, None{})) : Maybe<&2, BE.Entry<String, V>>}:
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, None{}), PS.best(V, SC.append(BE.Entry<String, V>, B, C), s, PS.best(V, A, s, None{})), K.best_app(V, A, SC.append(BE.Entry<String, V>, B, C), s, None{})) : {_ == PS.best(V, B, s, PS.best(V, A, s, None{})) : Maybe<&2, BE.Entry<String, V>>}
  %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, B, C), s, PS.best(V, A, s, None{})), PS.best(V, C, s, PS.best(V, B, s, PS.best(V, A, s, None{}))), K.best_app(V, B, C, s, PS.best(V, A, s, None{}))) : {_ == PS.best(V, B, s, PS.best(V, A, s, None{})) : Maybe<&2, BE.Entry<String, V>>}
  K.best_none(V, C, s, PS.best(V, B, s, PS.best(V, A, s, None{})), nC)

def lp_ok(-V: Data, t: P.Trie<V>, +x: U32, a: Cmp, +rest: String, +ea: {P.hc(V, x, t) == a : Cmp}, +lo: Maybe<&2, U32>, +o: {K.ok(V, t, lo) == True{} : Bool}) -> {P.lp(V, t, x, a, rest) == PS.best(V, P.ent(V, t), SCon{Chr{x}, rest}, None{}) : Maybe<&2, BE.Entry<String, V>>}:
  match t a rest:
    case P.TNil{} _ _:
      {==}
    case P.TNode{+c, +val, +down, +next} LT{} _:
      +nd = {P.TNode{c, val, down, next} : P.Trie<V>}
      Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, P.ent(V, nd), SCon{Chr{x}, rest}, None{}), None{}, K.best_none(V, P.ent(V, nd), SCon{Chr{x}, rest}, None{}, K.nm_hg(V, P.ent(V, nd), x, rest, above_lt(V, c, val, down, next, lo, o, x, rest, ea))))
    case P.TNode{+c, +val, +down, +next} GT{} _:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +cx = SO.lt_of_gt(~U32, ~U32.cmp, ~O.u32_order, x, c, ea)
      Equal.trans(Maybe<&2, BE.Entry<String, V>>, P.lp(V, next, x, P.hc(V, x, next), rest), PS.best(V, C, SCon{Chr{x}, rest}, None{}), PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), SCon{Chr{x}, rest}, None{}),
        lp_ok(V, next, x, P.hc(V, x, next), rest, {==}, Some{c}, okn(V, c, val, down, next, lo, o)),
        Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), SCon{Chr{x}, rest}, None{}), PS.best(V, C, SCon{Chr{x}, rest}, None{}), best_skip(V, A, B, C, SCon{Chr{x}, rest}, None{}, K.nm_opt(V, c, val, x, rest, cx), K.nm_mapc(V, c, P.ent(V, down), x, rest, cx))))
    case P.TNode{+c, +val, +down, +next} EQ{} SNil{}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +s = {SCon{Chr{c}, SNil{}} : String}
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.lp(V, P.TNode{c, val, down, next}, x, EQ{}, SNil{}) == PS.best(V, P.ent(V, P.TNode{c, val, down, next}), SCon{Chr{_}, SNil{}}, None{}) : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, None{}), PS.best(V, B, s, PS.best(V, A, s, None{})), best_node(V, A, B, C, s, K.nm_hg(V, C, c, SNil{}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o))))) : {P.shift(V, c, P.here(V, val)) == _ : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, A, s, None{}), P.shift(V, c, P.here(V, val)), K.best_opt(V, c, val, SNil{})) : {P.shift(V, c, P.here(V, val)) == PS.best(V, B, s, _) : Maybe<&2, BE.Entry<String, V>>}
      Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, B, s, P.shift(V, c, P.here(V, val))), P.shift(V, c, P.here(V, val)), K.best_none(V, B, s, P.shift(V, c, P.here(V, val)), K.nm_mapc_nil(V, c, P.ent(V, down), K.heads(V, down, None{}, okd(V, c, val, down, next, lo, o)))))
    case P.TNode{+c, +val, +down, +next} EQ{} SCon{Chr{+y}, +r}:
      +A = P.opt(V, SCon{Chr{c}, SNil{}}, val)
      +B = P.mapc(V, c, P.ent(V, down))
      +C = P.ent(V, next)
      +s = {SCon{Chr{c}, SCon{Chr{y}, r}} : String}
      +hd = K.heads(V, down, None{}, okd(V, c, val, down, next, lo, o))
      %Equal.sym(U32, x, c, O.u32_antisym(x, c, ea)) : {P.lp(V, P.TNode{c, val, down, next}, x, EQ{}, SCon{Chr{y}, r}) == PS.best(V, P.ent(V, P.TNode{c, val, down, next}), SCon{Chr{_}, SCon{Chr{y}, r}}, None{}) : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, A, SC.append(BE.Entry<String, V>, B, C)), s, None{}), PS.best(V, B, s, PS.best(V, A, s, None{})), best_node(V, A, B, C, s, K.nm_hg(V, C, c, SCon{Chr{y}, r}, K.heads(V, next, Some{c}, okn(V, c, val, down, next, lo, o))))) : {P.shift(V, c, P.orM(V, P.lp(V, down, y, P.hc(V, y, down), r), P.here(V, val))) == _ : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, A, s, None{}), P.shift(V, c, P.here(V, val)), K.best_opt(V, c, val, SCon{Chr{y}, r})) : {P.shift(V, c, P.orM(V, P.lp(V, down, y, P.hc(V, y, down), r), P.here(V, val))) == PS.best(V, B, s, _) : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, B, s, P.shift(V, c, P.here(V, val))), P.shift(V, c, PS.best(V, P.ent(V, down), SCon{Chr{y}, r}, P.here(V, val))), K.best_shift(V, c, P.ent(V, down), SCon{Chr{y}, r}, P.here(V, val))) : {P.shift(V, c, P.orM(V, P.lp(V, down, y, P.hc(V, y, down), r), P.here(V, val))) == _ : Maybe<&2, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, P.ent(V, down), SCon{Chr{y}, r}, P.here(V, val)), P.orM(V, PS.best(V, P.ent(V, down), SCon{Chr{y}, r}, None{}), P.here(V, val)), best_here(V, P.ent(V, down), SCon{Chr{y}, r}, val, K.allgt_hg(V, P.ent(V, down), hd))) : {P.shift(V, c, P.orM(V, P.lp(V, down, y, P.hc(V, y, down), r), P.here(V, val))) == P.shift(V, c, _) : Maybe<&2, BE.Entry<String, V>>}
      Equal.cong(Maybe<&2, BE.Entry<String, V>>, Maybe<&2, BE.Entry<String, V>>, z => P.shift(V, c, P.orM(V, z, P.here(V, val))), P.lp(V, down, y, P.hc(V, y, down), r), PS.best(V, P.ent(V, down), SCon{Chr{y}, r}, None{}), lp_ok(V, down, y, P.hc(V, y, down), r, {==}, None{}, okd(V, c, val, down, next, lo, o)))
