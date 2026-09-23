import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../spec/tree_map.bend as S
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ./state.bend as ST
import ./mirror.bend as MI
import ./ok.bend as OK
import ./tree.bend as TR
import ./ends.bend as EN
import ./path.bend as P
import ./plug.bend as PG
import ./dj.bend as DJ

# Cursors: the mirror's cursor holds node ids, the specification's the keys
# at them. A good cursor is over a good shadow, its next and current ids 0 or
# in the tree, and the next one not the current one. (source: tools/generators/tm_hand/cur.src)


# the key at an id
def ck(~K: Data, +nl: List<&2, M.Node<K>>, +j: Nat) -> Maybe<&2, K>:
  M.node_key(~K, ST.nd(K, nl, j))

# an id is 0 or in the ids
def idok(+xs: List<&2, Nat>, +j: Nat) -> Bool:
  Bool.or(Nat.is_eq(j, 0n), HT.memn(j, xs))

def cmod(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: MI.MCursor<K, V>) -> S.Cursor<K, V>:
  match c:
    case MI.MC{ST.SH{n, root, lo, hi, free, +l, d, +nl, +pl, +t, fl}, +nx, +cu, lo2, hi2, fw}:
      S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(t), nl, pl)}, ck(~K, nl, nx), ck(~K, nl, cu), lo2, hi2, fw}

def cgood(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, c: MI.MCursor<K, V>) -> Bool:
  match c:
    case MI.MC{ST.SH{+n, +root, +lo, +hi, +free, +l, +d, +nl, +pl, +t, +fl}, +nx, +cu, lo2, hi2, fw}:
      Bool.and(ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, t, fl), Bool.and(idok(ST.ids(t), nx), Bool.and(idok(ST.ids(t), cu), Bool.or(Nat.is_eq(nx, 0n), Bool.not(Nat.is_eq(nx, cu))))))

# a mirror cursor result refining a specification's: a good cursor whose real
# cursor the mirror's gives, and whose model the specification's is
def COK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, spec: S.Cursor<K, V> & X, mir: MI.MCursor<K, V> & X) -> Type:
  Sigma<&1, &1, MI.MCursor<K, V>, c2 => Sigma<&1, &1, X, o => {MI.rcp(~K, ~V, ~cmp, X, mir) == (MI.rc(~K, ~V, ~cmp, c2), o) : M.Cursor<K, V, cmp> & X} & ({spec == (cmod(~K, ~V, ~cmp, c2), o) : S.Cursor<K, V> & X} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>>

def CPOK(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, spec: S.Cursor<K, V> & X, r: M.Cursor<K, V, cmp> & X) -> Type:
  Sigma<&1, &1, MI.MCursor<K, V>, c2 => Sigma<&1, &1, X, o => {r == (MI.rc(~K, ~V, ~cmp, c2), o) : M.Cursor<K, V, cmp> & X} & ({spec == (cmod(~K, ~V, ~cmp, c2), o) : S.Cursor<K, V> & X} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>>

def cok_cpok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -spec: S.Cursor<K, V> & X, -mir: MI.MCursor<K, V> & X, -r: M.Cursor<K, V, cmp> & X, +hs: {r == MI.rcp(~K, ~V, ~cmp, X, mir) : M.Cursor<K, V, cmp> & X}, p: COK(~K, ~V, ~cmp, X, spec, mir)) -> CPOK(~K, ~V, ~cmp, X, spec, r):
  match p:
    case Tuple{+c2, Tuple{+o, Tuple{+h1, rest}}}:
      (c2, (o, (Equal.trans(M.Cursor<K, V, cmp> & X, r, MI.rcp(~K, ~V, ~cmp, X, mir), (MI.rc(~K, ~V, ~cmp, c2), o), hs, h1), rest)))

# ---- ids ----

def or_r(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def fst0_ok(+xs: List<&2, Nat>) -> {idok(xs, ST.fst0(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      or_r(Nat.is_eq(x, 0n), HT.memn(x, Con{x, t}), DJ.mem_hd(x, t))

def idok_c(+x: Nat, +xs: List<&2, Nat>, +j: Nat, +h: {idok(xs, j) == True{} : Bool}, +b: Bool, +hb: {Nat.is_eq(j, 0n) == b : Bool}) -> {idok(Con{x, xs}, j) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, 0n), True{}, hb) : {Bool.or(_, HT.memn(j, Con{x, xs})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, 0n), False{}, hb) : {Bool.or(_, HT.memn(j, Con{x, xs})) == True{} : Bool}
      P.mem_cons(j, x, xs, L.subst(Bool, z => {Bool.or(z, HT.memn(j, xs)) == True{} : Bool}, Nat.is_eq(j, 0n), False{}, hb, h))

def idok_cons(+x: Nat, +xs: List<&2, Nat>, +j: Nat, +h: {idok(xs, j) == True{} : Bool}) -> {idok(Con{x, xs}, j) == True{} : Bool}:
  idok_c(x, xs, j, h, Nat.is_eq(j, 0n), {==})

# an id ok in a tail is ok in the list
def lo_up(+x: Nat, +y: Nat, +u: List<&2, Nat>, +h: {idok(Con{y, u}, ST.last0(Con{y, u})) == True{} : Bool}) -> {idok(Con{x, Con{y, u}}, ST.last0(Con{y, u})) == True{} : Bool}:
  idok_cons(x, Con{y, u}, ST.last0(Con{y, u}), h)

def last0_c(+x: Nat, +t: List<&2, Nat>, +ih: {idok(t, ST.last0(t)) == True{} : Bool}) -> {idok(Con{x, t}, ST.last0(Con{x, t})) == True{} : Bool}:
  match t:
    case Nil{}:
      or_r(Nat.is_eq(x, 0n), HT.memn(x, Con{x, Nil{}}), DJ.mem_hd(x, Nil{}))
    case Con{+y, +u}:
      lo_up(x, y, u, ih)

def last0_ok(+xs: List<&2, Nat>) -> {idok(xs, ST.last0(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      last0_c(x, t, last0_ok(t))

