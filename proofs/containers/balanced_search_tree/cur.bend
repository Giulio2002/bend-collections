import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/containers/balanced_search_tree/main.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./ends.bend as EN
import ./path.bend as P
import ./dj.bend as DJ
import ../../lib/nat_list.bend as NL

# Cursors: the mirror's cursor holds node ids, the specification's the keys
# at them. A good cursor is over a good shadow, its next and current ids 0 or
# in the tree, and the next one not the current one. (source: tools/generators/tm_hand/cur.src)


# the key at an id
def ck(~K: Data, +nl: List<&2, M.Node<K>>, +j: Nat) -> Maybe<&2, K>:
  M.node_key(~K, ST.nd(K, nl, j))

# an id is 0 or in the ids
def idok(+xs: List<&2, Nat>, +j: Nat) -> Bool:
  Bool.or(Nat.is_eq(j, 0n), NL.memn(j, xs))

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

# a step over the same shadow: the cursor the mirror gives, exactly
def CSTEP(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, spec: S.Cursor<K, V> & X, mir: MI.MCursor<K, V> & X, +sh: ST.Sh<K, V>, lo2: M.Bound<K>, hi2: M.Bound<K>, +fw: Bool) -> Type:
  Sigma<&1, &1, Nat, nx_ => Sigma<&1, &1, Nat, cu_ => Sigma<&1, &1, X, o => {mir == (MI.MC{sh, nx_, cu_, lo2, hi2, fw}, o) : MI.MCursor<K, V> & X} & ({spec == (cmod(~K, ~V, ~cmp, MI.MC{sh, nx_, cu_, lo2, hi2, fw}), o) : S.Cursor<K, V> & X} & {cgood(~K, ~V, ~cmp, MI.MC{sh, nx_, cu_, lo2, hi2, fw}) == True{} : Bool})>>>

def cstep_cok(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, -X: Data, -spec: S.Cursor<K, V> & X, -mir: MI.MCursor<K, V> & X, +sh: ST.Sh<K, V>, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +fw: Bool, p: CSTEP(~K, ~V, ~cmp, X, spec, mir, sh, lo2, hi2, fw)) -> COK(~K, ~V, ~cmp, X, spec, mir):
  match p:
    case Tuple{+nx, Tuple{+cu, Tuple{+o, Tuple{+h1, rest}}}}:
      (MI.MC{sh, nx, cu, lo2, hi2, fw}, (o, (L.subst(MI.MCursor<K, V> & X, z => {MI.rcp(~K, ~V, ~cmp, X, z) == (MI.rc(~K, ~V, ~cmp, MI.MC{sh, nx, cu, lo2, hi2, fw}), o) : M.Cursor<K, V, cmp> & X}, (MI.MC{sh, nx, cu, lo2, hi2, fw}, o), mir, Equal.sym(MI.MCursor<K, V> & X, mir, (MI.MC{sh, nx, cu, lo2, hi2, fw}, o), h1), {==}), rest)))

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
      or_r(Nat.is_eq(x, 0n), NL.memn(x, Con{x, t}), DJ.mem_hd(x, t))

def idok_c(+x: Nat, +xs: List<&2, Nat>, +j: Nat, +h: {idok(xs, j) == True{} : Bool}, +b: Bool, +hb: {Nat.is_eq(j, 0n) == b : Bool}) -> {idok(Con{x, xs}, j) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, 0n), True{}, hb) : {Bool.or(_, NL.memn(j, Con{x, xs})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, 0n), False{}, hb) : {Bool.or(_, NL.memn(j, Con{x, xs})) == True{} : Bool}
      P.mem_cons(j, x, xs, L.subst(Bool, z => {Bool.or(z, NL.memn(j, xs)) == True{} : Bool}, Nat.is_eq(j, 0n), False{}, hb, h))

def idok_cons(+x: Nat, +xs: List<&2, Nat>, +j: Nat, +h: {idok(xs, j) == True{} : Bool}) -> {idok(Con{x, xs}, j) == True{} : Bool}:
  idok_c(x, xs, j, h, Nat.is_eq(j, 0n), {==})

# an id ok in a tail is ok in the list
def lo_up(+x: Nat, +y: Nat, +u: List<&2, Nat>, +h: {idok(Con{y, u}, ST.last0(Con{y, u})) == True{} : Bool}) -> {idok(Con{x, Con{y, u}}, ST.last0(Con{y, u})) == True{} : Bool}:
  idok_cons(x, Con{y, u}, ST.last0(Con{y, u}), h)

def last0_c(+x: Nat, +t: List<&2, Nat>, +ih: {idok(t, ST.last0(t)) == True{} : Bool}) -> {idok(Con{x, t}, ST.last0(Con{x, t})) == True{} : Bool}:
  match t:
    case Nil{}:
      or_r(Nat.is_eq(x, 0n), NL.memn(x, Con{x, Nil{}}), DJ.mem_hd(x, Nil{}))
    case Con{+y, +u}:
      lo_up(x, y, u, ih)

def last0_ok(+xs: List<&2, Nat>) -> {idok(xs, ST.last0(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      last0_c(x, t, last0_ok(t))


# ---- ranges read the same ----

def oo_eq(+c: Cmp, +b: Bool) -> {M.ordering_ok(c, b) == S.ordering_ok(c, b) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def al_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +lo: M.Bound<K>) -> {M.above_lower(~K, ~V, ~cmp, k, lo) == S.above_lower(~K, ~cmp, k, lo) : Bool}:
  match lo:
    case M.Unbounded{}:
      {==}
    case M.Inclusive{+a}:
      oo_eq(cmp(a, k), True{})
    case M.Exclusive{+a}:
      oo_eq(cmp(a, k), False{})

def bu_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +hi: M.Bound<K>) -> {M.below_upper(~K, ~V, ~cmp, k, hi) == S.below_upper(~K, ~cmp, k, hi) : Bool}:
  match hi:
    case M.Unbounded{}:
      {==}
    case M.Inclusive{+a}:
      oo_eq(cmp(k, a), True{})
    case M.Exclusive{+a}:
      oo_eq(cmp(k, a), False{})

def inr_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +k: K, +lo: M.Bound<K>, +hi: M.Bound<K>) -> {M.in_range(~K, ~V, ~cmp, k, lo, hi) == S.in_range(~K, ~cmp, k, lo, hi) : Bool}:
  %Equal.sym(Bool, M.above_lower(~K, ~V, ~cmp, k, lo), S.above_lower(~K, ~cmp, k, lo), al_eq(~K, ~V, ~cmp, k, lo)) : {Bool.and(_, M.below_upper(~K, ~V, ~cmp, k, hi)) == S.in_range(~K, ~cmp, k, lo, hi) : Bool}
  %Equal.sym(Bool, M.below_upper(~K, ~V, ~cmp, k, hi), S.below_upper(~K, ~cmp, k, hi), bu_eq(~K, ~V, ~cmp, k, hi)) : {Bool.and(S.above_lower(~K, ~cmp, k, lo), _) == S.in_range(~K, ~cmp, k, lo, hi) : Bool}
  {==}

# ---- starting a cursor ----


def or_not(+b: Bool) -> {Bool.or(b, Bool.not(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cg_start(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}, +j: Nat, +hj: {idok(ST.ids(tg), j) == True{} : Bool}, +fw: Bool) -> {cgood(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, j, 0n, M.Unbounded{}, M.Unbounded{}, fw}) == True{} : Bool}:
  L.and_intro(ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl), Bool.and(idok(ST.ids(tg), j), Bool.and(idok(ST.ids(tg), 0n), Bool.or(Nat.is_eq(j, 0n), Bool.not(Nat.is_eq(j, 0n))))), hg, L.and_intro(idok(ST.ids(tg), j), Bool.and(idok(ST.ids(tg), 0n), Bool.or(Nat.is_eq(j, 0n), Bool.not(Nat.is_eq(j, 0n)))), hj, L.and_intro(idok(ST.ids(tg), 0n), Bool.or(Nat.is_eq(j, 0n), Bool.not(Nat.is_eq(j, 0n))), {==}, or_not(Nat.is_eq(j, 0n)))))

def iterator_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.rc(~K, ~V, ~cmp, MI.iterator(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == MI.rc(~K, ~V, ~cmp, c2) : M.Cursor<K, V, cmp>} & ({S.iterator(K, V, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>:
  %Equal.sym(Nat, lo, ST.fst0(ST.ids(tg)), N.eq_from_is_eq(lo, ST.fst0(ST.ids(tg)), ST.g_clo(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))) : Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.rc(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, 0n, M.Unbounded{}, M.Unbounded{}, True{}}) == MI.rc(~K, ~V, ~cmp, c2) : M.Cursor<K, V, cmp>} & ({S.iterator(K, V, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>
  (MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.fst0(ST.ids(tg)), 0n, M.Unbounded{}, M.Unbounded{}, True{}}, ({==}, (L.subst(Maybe<&2, K>, z => {S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, z, None{}, M.Unbounded{}, M.Unbounded{}, True{}} == S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, ck(~K, nl, ST.fst0(ST.ids(tg))), None{}, M.Unbounded{}, M.Unbounded{}, True{}} : S.Cursor<K, V>}, ck(~K, nl, ST.fst0(ST.ids(tg))), S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.head(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), ck(~K, nl, ST.fst0(ST.ids(tg))), EN.first_key_eq(~K, ~V, nl, pl, ST.ids(tg), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))), {==}), cg_start(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, ST.fst0(ST.ids(tg)), fst0_ok(ST.ids(tg)), True{}))))

def descending_iterator_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +hg: {ST.goodF(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl) == True{} : Bool}) -> Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.rc(~K, ~V, ~cmp, MI.descending_iterator(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == MI.rc(~K, ~V, ~cmp, c2) : M.Cursor<K, V, cmp>} & ({S.descending_iterator(K, V, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>:
  %Equal.sym(Nat, hi, ST.last0(ST.ids(tg)), N.eq_from_is_eq(hi, ST.last0(ST.ids(tg)), ST.g_chi(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg))) : Sigma<&1, &1, MI.MCursor<K, V>, c2 => {MI.rc(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, _, 0n, M.Unbounded{}, M.Unbounded{}, False{}}) == MI.rc(~K, ~V, ~cmp, c2) : M.Cursor<K, V, cmp>} & ({S.descending_iterator(K, V, ST.model(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl})) == cmod(~K, ~V, ~cmp, c2) : S.Cursor<K, V>} & {cgood(~K, ~V, ~cmp, c2) == True{} : Bool})>
  (MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, ST.last0(ST.ids(tg)), 0n, M.Unbounded{}, M.Unbounded{}, False{}}, ({==}, (L.subst(Maybe<&2, K>, z => {S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, z, None{}, M.Unbounded{}, M.Unbounded{}, False{}} == S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, ck(~K, nl, ST.last0(ST.ids(tg))), None{}, M.Unbounded{}, M.Unbounded{}, False{}} : S.Cursor<K, V>}, ck(~K, nl, ST.last0(ST.ids(tg))), S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), Equal.sym(Maybe<&2, K>, S.key_m(K, V, S.last(M.Entry<K, V>, ST.ents(~K, ~V, ST.ids(tg), nl, pl))), ck(~K, nl, ST.last0(ST.ids(tg))), EN.last_key_eq(~K, ~V, nl, pl, ST.ids(tg), EN.oks_tree(~K, ~V, nl, pl, tg, 0n, ST.g_crep(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg), ST.g_cpay(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg)))), {==}), cg_start(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, hg, ST.last0(ST.ids(tg)), last0_ok(ST.ids(tg)), False{}))))

# ---- has_next: the next id's key in range ----


def has_next_x(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +nx: Nat, +cu: Nat, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +fw: Bool, +hc: {cgood(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw}) == True{} : Bool}, +x: M.Node<K>, +hx: {ST.nd(K, nl, nx) == x : M.Node<K>}) -> COK(~K, ~V, ~cmp, Bool, S.iterator_has_next(~K, ~V, ~cmp, S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, M.node_key(~K, x), ck(~K, nl, cu), lo2, hi2, fw}), MI.iterator_has_checked(~K, ~V, ~cmp, nx, cu, lo2, hi2, fw, (ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x))):
  match x:
    case M.Free{f}:
      (MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw}, (False{}, ({==}, (L.subst(Maybe<&2, K>, z => {(S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, None{}, ck(~K, nl, cu), lo2, hi2, fw}, False{}) == (S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, z, ck(~K, nl, cu), lo2, hi2, fw}, False{}) : S.Cursor<K, V> & Bool}, None{}, ck(~K, nl, nx), Equal.sym(Maybe<&2, K>, ck(~K, nl, nx), None{}, L.subst(M.Node<K>, z => {ck(~K, nl, nx) == M.node_key(~K, z) : Maybe<&2, K>}, ST.nd(K, nl, nx), M.Free{f}, hx, {==})), {==}), hc))))
    case M.N{+c0, +x1, +x2, +x3, +k0}:
      +ek = Equal.sym(Maybe<&2, K>, ck(~K, nl, nx), Some{k0}, L.subst(M.Node<K>, z => {ck(~K, nl, nx) == M.node_key(~K, z) : Maybe<&2, K>}, ST.nd(K, nl, nx), M.N{c0, x1, x2, x3, k0}, hx, {==}))
      +er = inr_eq(~K, ~V, ~cmp, k0, lo2, hi2)
      (MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw}, (M.in_range(~K, ~V, ~cmp, k0, lo2, hi2), ({==}, (L.subst(Maybe<&2, K>, z => {(S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, Some{k0}, ck(~K, nl, cu), lo2, hi2, fw}, S.in_range(~K, ~cmp, k0, lo2, hi2)) == (S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, z, ck(~K, nl, cu), lo2, hi2, fw}, M.in_range(~K, ~V, ~cmp, k0, lo2, hi2)) : S.Cursor<K, V> & Bool}, Some{k0}, ck(~K, nl, nx), ek, L.subst(Bool, z => {(S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, Some{k0}, ck(~K, nl, cu), lo2, hi2, fw}, S.in_range(~K, ~cmp, k0, lo2, hi2)) == (S.CR{S.TM{l, ST.ents(~K, ~V, ST.ids(tg), nl, pl)}, Some{k0}, ck(~K, nl, cu), lo2, hi2, fw}, z) : S.Cursor<K, V> & Bool}, S.in_range(~K, ~cmp, k0, lo2, hi2), M.in_range(~K, ~V, ~cmp, k0, lo2, hi2), Equal.sym(Bool, M.in_range(~K, ~V, ~cmp, k0, lo2, hi2), S.in_range(~K, ~cmp, k0, lo2, hi2), er), {==})), hc))))

def has_next_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +nx: Nat, +cu: Nat, +lo2: M.Bound<K>, +hi2: M.Bound<K>, +fw: Bool, +hc: {cgood(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw}) == True{} : Bool}) -> COK(~K, ~V, ~cmp, Bool, S.iterator_has_next(~K, ~V, ~cmp, cmod(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw})), MI.iterator_has_next(~K, ~V, ~cmp, MI.MC{ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, nx, cu, lo2, hi2, fw})):
  has_next_x(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, nx, cu, lo2, hi2, fw, hc, ST.nd(K, nl, nx), {==})
