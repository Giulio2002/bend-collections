import Base
import ../../lib/nat.bend as N
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ../../../src/containers/dynamic_array.bend as D
import ./state.bend as ST
import ./mirror.bend as MI

# The empty map: the shadow with no nodes is good at any limit and depth
# within bounds; new and with_limit build it, and its model is the
# specification's empty map. (source: tools/generators/tm_hand/life.src)


def good_empty(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +l: Nat, +d: Nat, +hcl: {Nat.is_le(l, 31n) == True{} : Bool}, +hcd: {Nat.is_le(d, l) == True{} : Bool}) -> {ST.good(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, l, d, Nil{}, Nil{}, ST.TE{}, Nil{}}) == True{} : Bool}:
  ST.good_intro(~K, ~V, ~cmp, 0n, 0n, 0n, 0n, 0n, l, d, Nil{}, Nil{}, ST.TE{}, Nil{}, hcl, hcd, N.zero_le(SC.pow2(d)), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def new_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp) -> {ST.real(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, 31n, 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == M.new(~K, ~V, ~cmp) : M.TreeMap<K, V, cmp>} & ({ST.model(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, 31n, 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == S.new(K, V) : S.Model<K, V>} & {ST.good(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, 31n, 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == True{} : Bool}):
  ({==}, ({==}, good_empty(~K, ~V, ~cmp, 31n, 0n, {==}, {==})))


def wl_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: Nat, +b: Bool, +hb: {Nat.is_lt(k, 31n) == b : Bool}) -> {ST.real(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, b), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == M.TM{0n, 0n, 0n, 0n, 0n, M.NS{D.clamp_limit(k, b), 0n, 1n, 0n, M.ns_nats(0n), M.ns_nats(0n), M.ns_nats(0n), M.ns_nats(0n), M.ns_nokeys(~K, 0n)}, D.DA{D.clamp_limit(k, b), 0n, 1n, 0n, D.empty_slots_at(~Maybe<&2, V>, 0n)}} : M.TreeMap<K, V, cmp>} & ({ST.model(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, b), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == S.TM{S.pick(Nat, b, k, 31n), Nil{}} : S.Model<K, V>} & {ST.good(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, b), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == True{} : Bool}):
  match b:
    case True{}:
      ({==}, ({==}, good_empty(~K, ~V, ~cmp, k, 0n, N.lt_le(k, 31n, hb), N.zero_le(k))))
    case False{}:
      ({==}, ({==}, good_empty(~K, ~V, ~cmp, 31n, 0n, {==}, {==})))

# with_limit: the limit clamped to 31
def with_limit_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: Nat) -> {ST.real(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, Nat.is_lt(k, 31n)), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == M.with_limit(~K, ~V, ~cmp, k) : M.TreeMap<K, V, cmp>} & ({ST.model(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, Nat.is_lt(k, 31n)), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == S.with_limit(K, V, k) : S.Model<K, V>} & {ST.good(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, D.clamp_limit(k, Nat.is_lt(k, 31n)), 0n, Nil{}, Nil{}, ST.TE{}, Nil{}}) == True{} : Bool}):
  wl_c(~K, ~V, ~cmp, k, Nat.is_lt(k, 31n), {==})

# clearing: the same limit and depth, no nodes
def clear_ok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> {ST.real(~K, ~V, ~cmp, MI.clear(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == ST.real(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, l, d, Nil{}, Nil{}, ST.TE{}, Nil{}}) : M.TreeMap<K, V, cmp>} & ({S.clear(K, V, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == ST.model(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, l, d, Nil{}, Nil{}, ST.TE{}, Nil{}}) : S.Model<K, V>} & {ST.good(~K, ~V, ~cmp, ST.SH{0n, 0n, 0n, 0n, 0n, l, d, Nil{}, Nil{}, ST.TE{}, Nil{}}) == True{} : Bool}):
  ({==}, ({==}, good_empty(~K, ~V, ~cmp, l, d, ST.g_cl(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cd(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))))
