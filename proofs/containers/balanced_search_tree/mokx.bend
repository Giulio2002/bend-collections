import Base
import ../../lib/logic.bend as L
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./ok.bend as OK

# A mirror result's answer mapped: a refinement with the value v found
# gives one with the value's presence (changed_value) or its entry
# (entry_value). (source: tools/generators/tm_hand/mokx.src)


def cv_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m0: S.Model<K, V>, +m: ST.Sh<K, V>, +v: V, +sh2: ST.Sh<K, V>, +o: Maybe<&2, V>, +h1: {(ST.real(~K, ~V, ~cmp, m), Some{v}) == (ST.real(~K, ~V, ~cmp, sh2), o) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}, r: {(m0, Some{v}) == (ST.model(~K, ~V, ~cmp, sh2), o) : S.Model<K, V> & Maybe<&2, V>} & {ST.good(~K, ~V, ~cmp, sh2) == True{} : Bool}) -> OK.MOK(~K, ~V, ~cmp, Bool, (m0, True{}), MI.changed_value(~K, ~V, ~cmp, (m, Some{v}))):
  match r:
    case Tuple{h2, hg}:
      +e1 = L.pair_fst(M.TreeMap<K, V, cmp>, Maybe<&2, V>, ST.real(~K, ~V, ~cmp, m), Some{v}, ST.real(~K, ~V, ~cmp, sh2), o, h1)
      +e2 = L.pair_fst(S.Model<K, V>, Maybe<&2, V>, m0, Some{v}, ST.model(~K, ~V, ~cmp, sh2), o, h2)
      (sh2, (True{}, (L.pair_eq(M.TreeMap<K, V, cmp>, Bool, ST.real(~K, ~V, ~cmp, m), True{}, ST.real(~K, ~V, ~cmp, sh2), True{}, e1, {==}), (L.pair_eq(S.Model<K, V>, Bool, m0, True{}, ST.model(~K, ~V, ~cmp, sh2), True{}, e2, {==}), hg))))

# the value found: the answer is that something changed
def cv_mok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m0: S.Model<K, V>, +m: ST.Sh<K, V>, +v: V, p: OK.MOK(~K, ~V, ~cmp, Maybe<&2, V>, (m0, Some{v}), (m, Some{v}))) -> OK.MOK(~K, ~V, ~cmp, Bool, (m0, True{}), MI.changed_value(~K, ~V, ~cmp, (m, Some{v}))):
  match p:
    case Tuple{+sh2, Tuple{+o, Tuple{+h1, r}}}:
      cv_r(~K, ~V, ~cmp, m0, m, v, sh2, o, h1, r)

def ev_r(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m0: S.Model<K, V>, +m: ST.Sh<K, V>, +k: K, +v: V, +sh2: ST.Sh<K, V>, +o: Maybe<&2, V>, +h1: {(ST.real(~K, ~V, ~cmp, m), Some{v}) == (ST.real(~K, ~V, ~cmp, sh2), o) : M.TreeMap<K, V, cmp> & Maybe<&2, V>}, r: {(m0, Some{v}) == (ST.model(~K, ~V, ~cmp, sh2), o) : S.Model<K, V> & Maybe<&2, V>} & {ST.good(~K, ~V, ~cmp, sh2) == True{} : Bool}) -> OK.MOK(~K, ~V, ~cmp, Maybe<&2, M.Entry<K, V>>, (m0, Some{M.Entry{k, v}}), MI.entry_value(~K, ~V, ~cmp, Some{k}, (m, Some{v}))):
  match r:
    case Tuple{h2, hg}:
      +e1 = L.pair_fst(M.TreeMap<K, V, cmp>, Maybe<&2, V>, ST.real(~K, ~V, ~cmp, m), Some{v}, ST.real(~K, ~V, ~cmp, sh2), o, h1)
      +e2 = L.pair_fst(S.Model<K, V>, Maybe<&2, V>, m0, Some{v}, ST.model(~K, ~V, ~cmp, sh2), o, h2)
      (sh2, (Some{M.Entry{k, v}}, (L.pair_eq(M.TreeMap<K, V, cmp>, Maybe<&2, M.Entry<K, V>>, ST.real(~K, ~V, ~cmp, m), Some{M.Entry{k, v}}, ST.real(~K, ~V, ~cmp, sh2), Some{M.Entry{k, v}}, e1, {==}), (L.pair_eq(S.Model<K, V>, Maybe<&2, M.Entry<K, V>>, m0, Some{M.Entry{k, v}}, ST.model(~K, ~V, ~cmp, sh2), Some{M.Entry{k, v}}, e2, {==}), hg))))

# the value found: the answer is its entry
def ev_mok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +m0: S.Model<K, V>, +m: ST.Sh<K, V>, +k: K, +v: V, p: OK.MOK(~K, ~V, ~cmp, Maybe<&2, V>, (m0, Some{v}), (m, Some{v}))) -> OK.MOK(~K, ~V, ~cmp, Maybe<&2, M.Entry<K, V>>, (m0, Some{M.Entry{k, v}}), MI.entry_value(~K, ~V, ~cmp, Some{k}, (m, Some{v}))):
  match p:
    case Tuple{+sh2, Tuple{+o, Tuple{+h1, r}}}:
      ev_r(~K, ~V, ~cmp, m0, m, k, v, sh2, o, h1, r)
