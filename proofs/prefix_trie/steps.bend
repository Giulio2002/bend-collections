import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../spec/prefix_trie.bend as PS
import ../../src/prefix_trie.bend as P
import ../../types/balanced_search_tree.bend as BE
import ../../types/prefix_trie.bend as E
import ../balanced_search_tree/sorted.bend as SO
import ../balanced_search_tree/specops.bend as SP
import ./keys.bend as K
import ./ops.bend as OP

# Trie state: abstraction, invariant and every public operation.

# The empty key's entry, then the root list's entries.
def abs(-V: Data, s: P.PrefixTrie<V>) -> List<&2, BE.Entry<String, V>>:
  match s:
    case P.PT{val, kids}:
      SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), P.ent(V, kids))

# Invariant: every sibling list is strictly increasing by character code.
def inv(-V: Data, s: P.PrefixTrie<V>) -> Bool:
  match s:
    case P.PT{val, kids}:
      K.ok(V, kids, None{})

def view1(-V: Data, r: P.PrefixTrie<V> & E.Obs<V>) -> List<&2, BE.Entry<String, V>> & E.Obs<V>:
  match r:
    case Tuple{s, o}:
      (abs(V, s), o)

def StepOK(-V: Data, s: P.PrefixTrie<V>, op: E.Op<V>) -> Type:
  {view1(V, P.step(V, s, op)) == PS.step(V, abs(V, s), op) : List<&2, BE.Entry<String, V>> & E.Obs<V>} & {inv(V, Pair.fst(P.PrefixTrie<V>, E.Obs<V>, P.step(V, s, op))) == True{} : Bool}

# ---- root-level refinement ----

def root_ins_nil(-V: Data, val: Maybe<&2, V>, +R: List<&2, BE.Entry<String, V>>, +v: V, +a: {SO.above(~String, ~String.order, V, R, SNil{}) == True{} : Bool}) -> {Con{BE.Entry{SNil{}, v}, R} == S.ins(~String, ~String.order, V, SNil{}, v, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), R)) : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, SNil{}, v, R), Con{BE.Entry{SNil{}, v}, R}, K.ins_front(V, R, SNil{}, v, a))
    case Some{+w}:
      Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, SNil{}, v, Con{BE.Entry{SNil{}, w}, R}), Con{BE.Entry{SNil{}, v}, R}, SP.ins_eq(~String, ~String.order, V, BE.Entry{SNil{}, w}, R, SNil{}, v, O.refl(~String, ~String.order, ~O.string_order, SNil{})))

def root_ins(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, key: String, +v: V, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {abs(V, P.insert(V, P.PT{val, kids}, key, v)) == S.ins(~String, ~String.order, V, key, v, abs(V, P.PT{val, kids})) : List<&2, BE.Entry<String, V>>}:
  match key:
    case SNil{}:
      root_ins_nil(V, val, P.ent(V, kids), v, K.above_root(V, P.ent(V, kids), K.heads(V, kids, None{}, o)))
    case SCon{Chr{+x}, +r}:
      +A = P.opt(V, SNil{}, val)
      +k = {SCon{Chr{x}, r} : String}
      Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, P.ent(V, P.ins(V, kids, x, P.hc(V, x, kids), r, v))), SC.append(BE.Entry<String, V>, A, S.ins(~String, ~String.order, V, k, v, P.ent(V, kids))), S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), P.ent(V, P.ins(V, kids, x, P.hc(V, x, kids), r, v)), S.ins(~String, ~String.order, V, k, v, P.ent(V, kids)), OP.ins_ent(V, kids, x, P.hc(V, x, kids), r, v, {==}, None{}, o)),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.ins(~String, ~String.order, V, k, v, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), SC.append(BE.Entry<String, V>, A, S.ins(~String, ~String.order, V, k, v, P.ent(V, kids))), SP.ins_pass(~String, ~String.order, ~O.string_order, V, A, P.ent(V, kids), k, v, K.below_root(V, val, x, r))))

def root_ins_ok(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, key: String, +v: V, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {inv(V, P.insert(V, P.PT{val, kids}, key, v)) == True{} : Bool}:
  match key:
    case SNil{}:
      o
    case SCon{Chr{+x}, +r}:
      OP.ins_okp(V, kids, x, P.hc(V, x, kids), r, v, {==}, None{}, o, {==})

def root_find_nil(-V: Data, val: Maybe<&2, V>, +R: List<&2, BE.Entry<String, V>>, +a: {SO.above(~String, ~String.order, V, R, SNil{}) == True{} : Bool}) -> {val == S.find(~String, ~String.order, V, SNil{}, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), R)) : Maybe<&2, V>}:
  match val:
    case None{}:
      Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SNil{}, R), None{}, SP.find_above(~String, ~String.order, V, R, SNil{}, a))
    case Some{+w}:
      Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, SNil{}, Con{BE.Entry{SNil{}, w}, R}), Some{w}, SP.find_eq(~String, ~String.order, V, BE.Entry{SNil{}, w}, R, SNil{}, O.refl(~String, ~String.order, ~O.string_order, SNil{})))

def root_get(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, key: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {P.get(V, P.PT{val, kids}, key) == S.find(~String, ~String.order, V, key, abs(V, P.PT{val, kids})) : Maybe<&2, V>}:
  match key:
    case SNil{}:
      root_find_nil(V, val, P.ent(V, kids), K.above_root(V, P.ent(V, kids), K.heads(V, kids, None{}, o)))
    case SCon{Chr{+x}, +r}:
      +A = P.opt(V, SNil{}, val)
      +k = {SCon{Chr{x}, r} : String}
      Equal.trans(Maybe<&2, V>, P.find(V, kids, x, P.hc(V, x, kids), r), S.find(~String, ~String.order, V, k, P.ent(V, kids)), S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))),
        OP.find_ok(V, kids, x, P.hc(V, x, kids), r, {==}, None{}, o),
        Equal.sym(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), S.find(~String, ~String.order, V, k, P.ent(V, kids)),
          Equal.trans(Maybe<&2, V>, S.find(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), SP.orM(V, S.find(~String, ~String.order, V, k, A), S.find(~String, ~String.order, V, k, P.ent(V, kids))), S.find(~String, ~String.order, V, k, P.ent(V, kids)),
            SP.find_app(~String, ~String.order, V, A, P.ent(V, kids), k),
            Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => SP.orM(V, z, S.find(~String, ~String.order, V, k, P.ent(V, kids))), S.find(~String, ~String.order, V, k, A), None{}, SP.find_below(~String, ~String.order, ~O.string_order, V, A, k, K.below_root(V, val, x, r))))))

def root_del_nil(-V: Data, val: Maybe<&2, V>, +R: List<&2, BE.Entry<String, V>>, +a: {SO.above(~String, ~String.order, V, R, SNil{}) == True{} : Bool}) -> {R == S.del(~String, ~String.order, V, SNil{}, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), R)) : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SNil{}, R), R, SP.del_above(~String, ~String.order, V, R, SNil{}, a))
    case Some{+w}:
      Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SNil{}, Con{BE.Entry{SNil{}, w}, R}), R,
        Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, SNil{}, Con{BE.Entry{SNil{}, w}, R}), S.del(~String, ~String.order, V, SNil{}, R), R,
          SP.del_eq(~String, ~String.order, V, BE.Entry{SNil{}, w}, R, SNil{}, O.refl(~String, ~String.order, ~O.string_order, SNil{})),
          SP.del_above(~String, ~String.order, V, R, SNil{}, a)))

def root_del(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, key: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {abs(V, P.delete(V, P.PT{val, kids}, key)) == S.del(~String, ~String.order, V, key, abs(V, P.PT{val, kids})) : List<&2, BE.Entry<String, V>>}:
  match key:
    case SNil{}:
      root_del_nil(V, val, P.ent(V, kids), K.above_root(V, P.ent(V, kids), K.heads(V, kids, None{}, o)))
    case SCon{Chr{+x}, +r}:
      +A = P.opt(V, SNil{}, val)
      +k = {SCon{Chr{x}, r} : String}
      Equal.trans(List<&2, BE.Entry<String, V>>, SC.append(BE.Entry<String, V>, A, P.ent(V, P.rem(V, kids, x, P.hc(V, x, kids), r))), SC.append(BE.Entry<String, V>, A, S.del(~String, ~String.order, V, k, P.ent(V, kids))), S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))),
        Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, A, z), P.ent(V, P.rem(V, kids, x, P.hc(V, x, kids), r)), S.del(~String, ~String.order, V, k, P.ent(V, kids)), OP.rem_ent(V, kids, x, P.hc(V, x, kids), r, {==}, None{}, o)),
        Equal.sym(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), SC.append(BE.Entry<String, V>, A, S.del(~String, ~String.order, V, k, P.ent(V, kids))),
          Equal.trans(List<&2, BE.Entry<String, V>>, S.del(~String, ~String.order, V, k, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), SC.append(BE.Entry<String, V>, S.del(~String, ~String.order, V, k, A), S.del(~String, ~String.order, V, k, P.ent(V, kids))), SC.append(BE.Entry<String, V>, A, S.del(~String, ~String.order, V, k, P.ent(V, kids))),
            SP.del_app(~String, ~String.order, V, A, P.ent(V, kids), k),
            Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, z, S.del(~String, ~String.order, V, k, P.ent(V, kids))), S.del(~String, ~String.order, V, k, A), A, SP.del_below(~String, ~String.order, ~O.string_order, V, A, k, K.below_root(V, val, x, r))))))

def root_del_ok(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, key: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {inv(V, P.delete(V, P.PT{val, kids}, key)) == True{} : Bool}:
  match key:
    case SNil{}:
      o
    case SCon{Chr{+x}, +r}:
      OP.rem_okp(V, kids, x, P.hc(V, x, kids), r, {==}, None{}, o)

def wp_root(-V: Data, val: Maybe<&2, V>, +x: U32, +r: String) -> {PS.with_prefix(V, SCon{Chr{x}, r}, P.opt(V, SNil{}, val)) == Nil{} : List<&2, BE.Entry<String, V>>}:
  match val:
    case None{}:
      {==}
    case Some{w}:
      {==}

def root_pfx(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, p: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {P.prefix_entries(V, P.PT{val, kids}, p) == PS.with_prefix(V, p, abs(V, P.PT{val, kids})) : List<&2, BE.Entry<String, V>>}:
  match p:
    case SNil{}:
      Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, SNil{}, abs(V, P.PT{val, kids})), abs(V, P.PT{val, kids}), K.pfx_nil(V, abs(V, P.PT{val, kids})))
    case SCon{Chr{+x}, +r}:
      +A = P.opt(V, SNil{}, val)
      +q = {SCon{Chr{x}, r} : String}
      Equal.trans(List<&2, BE.Entry<String, V>>, P.pe(V, kids, x, P.hc(V, x, kids), r), PS.with_prefix(V, q, P.ent(V, kids)), PS.with_prefix(V, q, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))),
        OP.pe_ok(V, kids, x, P.hc(V, x, kids), r, {==}, None{}, o),
        Equal.sym(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, q, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), PS.with_prefix(V, q, P.ent(V, kids)),
          Equal.trans(List<&2, BE.Entry<String, V>>, PS.with_prefix(V, q, SC.append(BE.Entry<String, V>, A, P.ent(V, kids))), SC.append(BE.Entry<String, V>, PS.with_prefix(V, q, A), PS.with_prefix(V, q, P.ent(V, kids))), PS.with_prefix(V, q, P.ent(V, kids)),
            K.wp_app(V, q, A, P.ent(V, kids)),
            Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>>, z => SC.append(BE.Entry<String, V>, z, PS.with_prefix(V, q, P.ent(V, kids))), PS.with_prefix(V, q, A), Nil{}, wp_root(V, val, x, r)))))

def entry_eq(-V: Data, +m: Maybe<&2, BE.Entry<String, V>>) -> {P.entry(V, m) == PS.entry(V, m) : Result<&2, &2, E.Error, BE.Entry<String, V>>}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

def root_lp(-V: Data, +val: Maybe<&2, V>, +kids: P.Trie<V>, text: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {P.longest_prefix(V, P.PT{val, kids}, text) == PS.entry(V, PS.best(V, abs(V, P.PT{val, kids}), text, None{})) : Result<&2, &2, E.Error, BE.Entry<String, V>>}:
  match text:
    case SNil{}:
      +R = P.ent(V, kids)
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), R), SNil{}, None{}), PS.best(V, R, SNil{}, PS.best(V, P.opt(V, SNil{}, val), SNil{}, None{})), K.best_app(V, P.opt(V, SNil{}, val), R, SNil{}, None{})) : {P.entry(V, P.here(V, val)) == PS.entry(V, _) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, P.opt(V, SNil{}, val), SNil{}, None{}), P.here(V, val), K.best_root(V, val, SNil{})) : {P.entry(V, P.here(V, val)) == PS.entry(V, PS.best(V, R, SNil{}, _)) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, R, SNil{}, P.here(V, val)), P.here(V, val), K.best_none(V, R, SNil{}, P.here(V, val), K.nm_nil(V, R, K.heads(V, kids, None{}, o)))) : {P.entry(V, P.here(V, val)) == PS.entry(V, _) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      entry_eq(V, P.here(V, val))
    case SCon{Chr{+x}, +r}:
      +R = P.ent(V, kids)
      +s = {SCon{Chr{x}, r} : String}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, SC.append(BE.Entry<String, V>, P.opt(V, SNil{}, val), R), s, None{}), PS.best(V, R, s, PS.best(V, P.opt(V, SNil{}, val), s, None{})), K.best_app(V, P.opt(V, SNil{}, val), R, s, None{})) : {P.entry(V, P.orM(V, P.lp(V, kids, x, P.hc(V, x, kids), r), P.here(V, val))) == PS.entry(V, _) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, P.opt(V, SNil{}, val), s, None{}), P.here(V, val), K.best_root(V, val, s)) : {P.entry(V, P.orM(V, P.lp(V, kids, x, P.hc(V, x, kids), r), P.here(V, val))) == PS.entry(V, PS.best(V, R, s, _)) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, PS.best(V, R, s, P.here(V, val)), P.orM(V, PS.best(V, R, s, None{}), P.here(V, val)), OP.best_here(V, R, s, val, K.allgt_hg(V, R, K.heads(V, kids, None{}, o)))) : {P.entry(V, P.orM(V, P.lp(V, kids, x, P.hc(V, x, kids), r), P.here(V, val))) == PS.entry(V, _) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      %Equal.sym(Maybe<&2, BE.Entry<String, V>>, P.lp(V, kids, x, P.hc(V, x, kids), r), PS.best(V, R, s, None{}), OP.lp_ok(V, kids, x, P.hc(V, x, kids), r, {==}, None{}, o)) : {P.entry(V, P.orM(V, _, P.here(V, val))) == PS.entry(V, P.orM(V, PS.best(V, R, s, None{}), P.here(V, val))) : Result<&2, &2, E.Error, BE.Entry<String, V>>}
      entry_eq(V, P.orM(V, PS.best(V, R, s, None{}), P.here(V, val)))

def result_value(-V: Data, +m: Maybe<&2, V>) -> {P.result(V, m) == PS.value(V, m) : Result<&2, &2, E.Error, V>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def present_some(-V: Data, +m: Maybe<&2, V>) -> {P.present(V, m) == PS.is_some(V, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def rm_core(-V: Data, m: Maybe<&2, V>, +val: Maybe<&2, V>, +kids: P.Trie<V>, +k: String, +o: {K.ok(V, kids, None{}) == True{} : Bool}) -> {view1(V, P.obs_val(V, P.remove_at(V, m, P.PT{val, kids}, k))) == PS.remove_at(V, m, k, abs(V, P.PT{val, kids})) : List<&2, BE.Entry<String, V>> & E.Obs<V>} & {inv(V, Pair.fst(P.PrefixTrie<V>, E.Obs<V>, P.obs_val(V, P.remove_at(V, m, P.PT{val, kids}, k)))) == True{} : Bool}:
  match m:
    case None{}:
      ({==}, o)
    case Some{+w}:
      (Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>> & E.Obs<V>, xs => (xs, E.OVal{Done{w}}), abs(V, P.delete(V, P.PT{val, kids}, k)), S.del(~String, ~String.order, V, k, abs(V, P.PT{val, kids})), root_del(V, val, kids, k, o)),
       root_del_ok(V, val, kids, k, o))

# ---- every operation ----

def step_ok(-V: Data, +s: P.PrefixTrie<V>, +op: E.Op<V>, +g: {inv(V, s) == True{} : Bool}) -> StepOK(V, s, op):
  match s op:
    case P.PT{+val, +kids} E.Insert{+k, +v}:
      (Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>> & E.Obs<V>, xs => (xs, E.OUnit{}), abs(V, P.insert(V, P.PT{val, kids}, k, v)), S.ins(~String, ~String.order, V, k, v, abs(V, P.PT{val, kids})), root_ins(V, val, kids, k, v, g)),
       root_ins_ok(V, val, kids, k, v, g))
    case P.PT{+val, +kids} E.Lookup{+k}:
      (Equal.cong(Result<&2, &2, E.Error, V>, List<&2, BE.Entry<String, V>> & E.Obs<V>, z => (abs(V, P.PT{val, kids}), E.OVal{z}), P.result(V, P.get(V, P.PT{val, kids}, k)), PS.value(V, PS.find(V, k, abs(V, P.PT{val, kids}))),
         Equal.trans(Result<&2, &2, E.Error, V>, P.result(V, P.get(V, P.PT{val, kids}, k)), PS.value(V, P.get(V, P.PT{val, kids}, k)), PS.value(V, PS.find(V, k, abs(V, P.PT{val, kids}))),
           result_value(V, P.get(V, P.PT{val, kids}, k)),
           Equal.cong(Maybe<&2, V>, Result<&2, &2, E.Error, V>, z => PS.value(V, z), P.get(V, P.PT{val, kids}, k), PS.find(V, k, abs(V, P.PT{val, kids})), root_get(V, val, kids, k, g)))),
       g)
    case P.PT{+val, +kids} E.Remove{+k}:
      %Equal.sym(Maybe<&2, V>, P.get(V, P.PT{val, kids}, k), PS.find(V, k, abs(V, P.PT{val, kids})), root_get(V, val, kids, k, g)) : {view1(V, P.obs_val(V, P.remove_at(V, _, P.PT{val, kids}, k))) == PS.remove_at(V, PS.find(V, k, abs(V, P.PT{val, kids})), k, abs(V, P.PT{val, kids})) : List<&2, BE.Entry<String, V>> & E.Obs<V>} & {inv(V, Pair.fst(P.PrefixTrie<V>, E.Obs<V>, P.obs_val(V, P.remove_at(V, _, P.PT{val, kids}, k)))) == True{} : Bool}
      rm_core(V, PS.find(V, k, abs(V, P.PT{val, kids})), val, kids, k, g)
    case P.PT{+val, +kids} E.Contains{+k}:
      (Equal.cong(Bool, List<&2, BE.Entry<String, V>> & E.Obs<V>, z => (abs(V, P.PT{val, kids}), E.OBool{z}), P.present(V, P.get(V, P.PT{val, kids}, k)), PS.is_some(V, PS.find(V, k, abs(V, P.PT{val, kids}))),
         Equal.trans(Bool, P.present(V, P.get(V, P.PT{val, kids}, k)), PS.is_some(V, P.get(V, P.PT{val, kids}, k)), PS.is_some(V, PS.find(V, k, abs(V, P.PT{val, kids}))),
           present_some(V, P.get(V, P.PT{val, kids}, k)),
           Equal.cong(Maybe<&2, V>, Bool, z => PS.is_some(V, z), P.get(V, P.PT{val, kids}, k), PS.find(V, k, abs(V, P.PT{val, kids})), root_get(V, val, kids, k, g)))),
       g)
    case P.PT{+val, +kids} E.PrefixEntries{+p}:
      (Equal.cong(List<&2, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>> & E.Obs<V>, z => (abs(V, P.PT{val, kids}), E.OList{z}), P.prefix_entries(V, P.PT{val, kids}, p), PS.with_prefix(V, p, abs(V, P.PT{val, kids})), root_pfx(V, val, kids, p, g)),
       g)
    case P.PT{+val, +kids} E.LongestPrefix{+t}:
      (Equal.cong(Result<&2, &2, E.Error, BE.Entry<String, V>>, List<&2, BE.Entry<String, V>> & E.Obs<V>, z => (abs(V, P.PT{val, kids}), E.OEntry{z}), P.longest_prefix(V, P.PT{val, kids}, t), PS.entry(V, PS.best(V, abs(V, P.PT{val, kids}), t, None{})), root_lp(V, val, kids, t, g)),
       g)
