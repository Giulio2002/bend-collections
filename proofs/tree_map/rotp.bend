import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./path.bend as P
import ./plug.bend as PG
import ./setters.bend as SE
import ./rotm.bend as RM
import ./rot.bend as RT
import ./nbr.bend as NB
import ./dj.bend as DJ
import ./spath.bend as SP
import ./ends.bend as EN
import ../spec/tree_map.bend as S

# A rotation of the mirror at the subtree a path leads to: its result over
# the node list, the rotated subtree linked, the path leading to it, the
# same ids, the root pointer at the plugged tree's root.
# (source: tools/generators/tm_hand/rotp.src)


# ---- a node's fields from its links ----

def f_left(-K: Data, +x: M.Node<K>, +a: Nat, +b: Nat, +q: Nat, +h: {ST.is_node(K, x, a, b, q) == True{} : Bool}) -> {M.node_left(~K, x) == a : Nat}:
  match x:
    case M.Free{f}:
      Empty.absurd({M.node_left(~K, M.Free{f}) == a : Nat}, L.false_true(h))
    case M.N{c, +x1, x2, x3, k}:
      N.eq_from_is_eq(x1, a, L.and_left(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q)), h))

def f_right(-K: Data, +x: M.Node<K>, +a: Nat, +b: Nat, +q: Nat, +h: {ST.is_node(K, x, a, b, q) == True{} : Bool}) -> {M.node_right(~K, x) == b : Nat}:
  match x:
    case M.Free{f}:
      Empty.absurd({M.node_right(~K, M.Free{f}) == b : Nat}, L.false_true(h))
    case M.N{c, x1, +x2, x3, k}:
      N.eq_from_is_eq(x2, b, L.and_left(Nat.is_eq(x2, b), Nat.is_eq(x3, q), L.and_right(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q)), h)))

def dir_c(+x: Nat, +lft: Bool, +s: Nat, +h: {Bool.not(Nat.is_eq(x, s)) == True{} : Bool}) -> {Nat.is_eq(ST.pk(Nat, lft, x, s), x) == lft : Bool}:
  match lft:
    case True{}:
      N.is_eq_refl(x)
    case False{}:
      N.is_eq_sym_false(x, s, LS.not_t_f(Nat.is_eq(x, s), h))

# the side the parent's node has x on is the path's
def dir_eq(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hd: {P.dist(c, x) == True{} : Bool}, +hx: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x) == SP.dir(c) : Bool}:
  match c:
    case Nil{}:
      N.is_eq_sym_false(x, 0n, LS.not_t_f(Nat.is_eq(x, 0n), P.ne_zero(x, hx)))
    case Con{P.FR{+q, +lft, +s}, +u}:
      +hk = L.and_left(P.cok1(~K, P.FR{q, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, q, nl), hok)
      +hn = L.and_left(ST.is_node(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, q, nl), L.and_right(Nat.is_lt(0n, q), Bool.and(ST.is_node(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, q, nl)), hk))
      %Equal.sym(Nat, M.node_left(~K, ST.nd(K, nl, q)), ST.pk(Nat, lft, x, ST.rid(s)), f_left(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u), hn)) : {Nat.is_eq(_, x) == lft : Bool}
      dir_c(x, lft, ST.rid(s), L.and_left(Bool.not(Nat.is_eq(x, ST.rid(s))), P.dist(u, q), hd))


# ---- the mirror's rotations at a path ----


def rl_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +x: Nat, +y: Nat, +b: Nat, +hxp: {M.node_parent(~K, ST.nd(K, nl, x)) == P.top(c) : Nat}, +hxr: {M.node_right(~K, ST.nd(K, nl, x)) == y : Nat}, +hyl: {M.node_left(~K, ST.nd(K, nl, y)) == b : Nat}, +hd: {Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x) == SP.dir(c) : Bool}) -> {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, y, b, P.top(c), SP.dir(c)), pl, tg, fl} : ST.Sh<K, V>}:
  +e0 = RM.rotate_left_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x)
  +e1 = L.subst(Nat, z => {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(z, root, M.node_right(~K, ST.nd(K, nl, x))), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, M.node_right(~K, ST.nd(K, nl, x)), M.node_left(~K, ST.nd(K, nl, M.node_right(~K, ST.nd(K, nl, x)))), z, Nat.is_eq(M.node_left(~K, ST.nd(K, nl, z)), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_parent(~K, ST.nd(K, nl, x)), P.top(c), hxp, e0)
  +e2 = L.subst(Nat, z => {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, z), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, z, M.node_left(~K, ST.nd(K, nl, z)), P.top(c), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_right(~K, ST.nd(K, nl, x)), y, hxr, e1)
  +e3 = L.subst(Nat, z => {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, y, z, P.top(c), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_left(~K, ST.nd(K, nl, y)), b, hyl, e2)
  L.subst(Bool, z => {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, y, b, P.top(c), z), pl, tg, fl} : ST.Sh<K, V>}, Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x), SP.dir(c), hd, e3)

def rr_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +x: Nat, +y: Nat, +b: Nat, +hxp: {M.node_parent(~K, ST.nd(K, nl, x)) == P.top(c) : Nat}, +hxl: {M.node_left(~K, ST.nd(K, nl, x)) == y : Nat}, +hyr: {M.node_right(~K, ST.nd(K, nl, y)) == b : Nat}, +hd: {Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x) == SP.dir(c) : Bool}) -> {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, y, b, P.top(c), SP.dir(c)), pl, tg, fl} : ST.Sh<K, V>}:
  +e0 = RM.rotate_right_m(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, x)
  +e1 = L.subst(Nat, z => {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(z, root, M.node_left(~K, ST.nd(K, nl, x))), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, M.node_left(~K, ST.nd(K, nl, x)), M.node_right(~K, ST.nd(K, nl, M.node_left(~K, ST.nd(K, nl, x)))), z, Nat.is_eq(M.node_left(~K, ST.nd(K, nl, z)), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_parent(~K, ST.nd(K, nl, x)), P.top(c), hxp, e0)
  +e2 = L.subst(Nat, z => {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, z), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, z, M.node_right(~K, ST.nd(K, nl, z)), P.top(c), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_left(~K, ST.nd(K, nl, x)), y, hxl, e1)
  +e3 = L.subst(Nat, z => {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, y, z, P.top(c), Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x)), pl, tg, fl} : ST.Sh<K, V>}, M.node_right(~K, ST.nd(K, nl, y)), b, hyr, e2)
  L.subst(Bool, z => {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, y, b, P.top(c), z), pl, tg, fl} : ST.Sh<K, V>}, Nat.is_eq(M.node_left(~K, ST.nd(K, nl, P.top(c))), x), SP.dir(c), hd, e3)

# ---- ids and the root ----

def ids_rl(+x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr) -> {ST.ids(ST.TN{y, ST.TN{x, ta, tb}, tc}) == ST.ids(ST.TN{x, ta, ST.TN{y, tb, tc}}) : List<&2, Nat>}:
  LL.append_assoc(Nat, ST.ids(ta), Con{x, ST.ids(tb)}, Con{y, ST.ids(tc)})

def ids_rr(+x: Nat, +y: Nat, +ta: ST.Tr, +tb: ST.Tr, +tc: ST.Tr) -> {ST.ids(ST.TN{y, ta, ST.TN{x, tb, tc}}) == ST.ids(ST.TN{x, ST.TN{y, ta, tb}, tc}) : List<&2, Nat>}:
  Equal.sym(List<&2, Nat>, ST.ids(ST.TN{x, ST.TN{y, ta, tb}, tc}), ST.ids(ST.TN{y, ta, ST.TN{x, tb, tc}}), LL.append_assoc(Nat, ST.ids(ta), Con{y, ST.ids(tb)}, Con{x, ST.ids(tc)}))

def wh_eq(+c: List<&2, P.Fr>, +t1: ST.Tr, +t2: ST.Tr, +e: {ST.ids(t1) == ST.ids(t2) : List<&2, Nat>}) -> {SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t1), P.after(c))) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t2), P.after(c))) : List<&2, Nat>}:
  L.subst(List<&2, Nat>, z => {SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t1), P.after(c))) == SC.append(Nat, P.before(c), SC.append(Nat, z, P.after(c))) : List<&2, Nat>}, ST.ids(t1), ST.ids(t2), e, {==})

def rid_plug_tn(+u: List<&2, P.Fr>, +p: Nat, +a: ST.Tr, +b: ST.Tr, +a2: ST.Tr, +b2: ST.Tr) -> {ST.rid(PG.plug(u, ST.TN{p, a, b})) == ST.rid(PG.plug(u, ST.TN{p, a2, b2})) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{P.FR{+q, +lft, +s}, +w}:
      match lft:
        case True{}:
          rid_plug_tn(w, q, ST.TN{p, a, b}, s, ST.TN{p, a2, b2}, s)
        case False{}:
          rid_plug_tn(w, q, s, ST.TN{p, a, b}, s, ST.TN{p, a2, b2})

# the root after rotating: the rotated subtree's root at the top, else the same
def root_rot(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +y: Nat, +t1: ST.Tr, +t2: ST.Tr, +root: Nat, +hx: {ST.rid(t1) == x : Nat}, +hy: {ST.rid(t2) == y : Nat}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hroot: {root == ST.rid(PG.plug(c, t1)) : Nat}) -> {RM.rootq(P.top(c), root, y) == ST.rid(PG.plug(c, t2)) : Nat}:
  match c:
    case Nil{}:
      Equal.sym(Nat, ST.rid(t2), y, hy)
    case Con{P.FR{0n, +lft, +s}, +u}:
      Empty.absurd({RM.rootq(0n, root, y) == ST.rid(PG.plug(Con{P.FR{0n, lft, s}, u}, t2)) : Nat}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 0n, nl)), L.and_left(P.cok1(~K, P.FR{0n, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 0n, nl), hok))))
    case Con{P.FR{1n+j, True{}, +s}, +u}:
      Equal.trans(Nat, root, ST.rid(PG.plug(u, ST.TN{1n+j, t1, s})), ST.rid(PG.plug(u, ST.TN{1n+j, t2, s})), hroot, rid_plug_tn(u, 1n+j, t1, s, t2, s))
    case Con{P.FR{1n+j, False{}, +s}, +u}:
      Equal.trans(Nat, root, ST.rid(PG.plug(u, ST.TN{1n+j, s, t1})), ST.rid(PG.plug(u, ST.TN{1n+j, s, t2})), hroot, rid_plug_tn(u, 1n+j, s, t1, s, t2))

# ---- facts from no repeated ids ----

def q_notin(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +t: ST.Tr, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c)))) == True{} : Bool}) -> {HT.memn(P.top(c), ST.ids(t)) == False{} : Bool}:
  match c:
    case Nil{}:
      RT.zero_ids(~K, nl, t, 0n, hr)
    case Con{P.FR{+q, True{}, +s}, +u}:
      DJ.dj_l(ST.ids(t), Con{q, SC.append(Nat, ST.ids(s), P.after(u))}, DJ.ndr(P.before(u), SC.append(Nat, ST.ids(t), Con{q, SC.append(Nat, ST.ids(s), P.after(u))}), hnd), q, DJ.mem_hd(q, SC.append(Nat, ST.ids(s), P.after(u))))
    case Con{P.FR{+q, False{}, +s}, +u}:
      DJ.nm_l(q, ST.ids(t), P.after(u), DJ.dj_r(SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}})), SC.append(Nat, ST.ids(t), P.after(u)), hnd, q, DJ.mem_r(q, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}}), DJ.mem_r(q, ST.ids(s), Con{q, Nil{}}, DJ.mem_hd(q, Nil{})))))

def w_notin(+c: List<&2, P.Fr>, +t: ST.Tr, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c)))) == True{} : Bool}, +w: Nat, +hw: {HT.memn(w, ST.ids(t)) == True{} : Bool}) -> {HT.memn(w, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}:
  DJ.nm_app(w, P.before(c), P.after(c), DJ.dj_l(P.before(c), SC.append(Nat, ST.ids(t), P.after(c)), hnd, w, DJ.mem_l(w, ST.ids(t), P.after(c), hw)), DJ.dj_r(ST.ids(t), P.after(c), DJ.ndr(P.before(c), SC.append(Nat, ST.ids(t), P.after(c)), hnd), w, hw))

def nd_sub(+c: List<&2, P.Fr>, +t: ST.Tr, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c)))) == True{} : Bool}) -> {LST.nodupn(ST.ids(t)) == True{} : Bool}:
  DJ.ndl(ST.ids(t), P.after(c), DJ.ndr(P.before(c), SC.append(Nat, ST.ids(t), P.after(c)), hnd))

# ---- rotating along a path ----


def rotl_path_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ta, ST.TN{y, tb, tc}}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ta, ST.TN{y, tb, tc}}), P.after(c)))) == True{} : Bool}) -> {MI.rotate_left(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotl_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c)), pl, tg, fl} : ST.Sh<K, V>}:
  rl_eq(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, c, x, y, ST.rid(tb), NB.parent_eq(~K, ST.nd(K, nl, x), ST.rid(ta), y, P.top(c), TR.rep_node(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), f_right(K, ST.nd(K, nl, x), ST.rid(ta), y, P.top(c), TR.rep_node(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), f_left(K, ST.nd(K, nl, y), ST.rid(tb), ST.rid(tc), x, TR.rep_node(~K, y, tb, tc, x, nl, TR.rep_r(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr))), dir_eq(~K, nl, c, x, hok, P.nd_dist(~K, nl, c, x, ta, ST.TN{y, tb, tc}, L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), ST.rid(ta), y, P.top(c)), Bool.and(ST.rep(~K, ta, x, nl), ST.rep(~K, ST.TN{y, tb, tc}, x, nl))), hr), hok, hnd), L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), ST.rid(ta), y, P.top(c)), Bool.and(ST.rep(~K, ta, x, nl), ST.rep(~K, ST.TN{y, tb, tc}, x, nl))), hr)))

def rotr_path_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ST.TN{y, ta, tb}, tc}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ST.TN{y, ta, tb}, tc}), P.after(c)))) == True{} : Bool}) -> {MI.rotate_right(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, x) == ST.SH{n, RM.rootq(P.top(c), root, y), lo, hi, free, l, d, RM.rotr_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c)), pl, tg, fl} : ST.Sh<K, V>}:
  rr_eq(~K, ~V, ~cmp, n, root, lo, hi, free, l, d, nl, pl, tg, fl, c, x, y, ST.rid(tb), NB.parent_eq(~K, ST.nd(K, nl, x), y, ST.rid(tc), P.top(c), TR.rep_node(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), f_left(K, ST.nd(K, nl, x), y, ST.rid(tc), P.top(c), TR.rep_node(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), f_right(K, ST.nd(K, nl, y), ST.rid(ta), ST.rid(tb), x, TR.rep_node(~K, y, ta, tb, x, nl, TR.rep_l(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr))), dir_eq(~K, nl, c, x, hok, P.nd_dist(~K, nl, c, x, ST.TN{y, ta, tb}, tc, L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), y, ST.rid(tc), P.top(c)), Bool.and(ST.rep(~K, ST.TN{y, ta, tb}, x, nl), ST.rep(~K, tc, x, nl))), hr), hok, hnd), L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), y, ST.rid(tc), P.top(c)), Bool.and(ST.rep(~K, ST.TN{y, ta, tb}, x, nl), ST.rep(~K, tc, x, nl))), hr)))

def rotl_path_rep(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ta, ST.TN{y, tb, tc}}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ta, ST.TN{y, tb, tc}}), P.after(c)))) == True{} : Bool}) -> {ST.rep(~K, ST.TN{y, ST.TN{x, ta, tb}, tc}, P.top(c), RM.rotl_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c))) == True{} : Bool}:
  RT.rotl_rep(~K, ~cmp, ~o, nl, x, ta, y, tb, tc, P.top(c), SP.dir(c), L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), ST.rid(ta), y, P.top(c)), Bool.and(ST.rep(~K, ta, x, nl), ST.rep(~K, ST.TN{y, tb, tc}, x, nl))), hr), L.and_left(Nat.is_lt(0n, y), Bool.and(ST.is_node(K, ST.nd(K, nl, y), ST.rid(tb), ST.rid(tc), x), Bool.and(ST.rep(~K, tb, y, nl), ST.rep(~K, tc, y, nl))), TR.rep_r(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), TR.rep_node(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr), TR.rep_node(~K, y, tb, tc, x, nl, TR.rep_r(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), TR.rep_l(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr), TR.rep_l(~K, y, tb, tc, x, nl, TR.rep_r(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), TR.rep_r(~K, y, tb, tc, x, nl, TR.rep_r(~K, x, ta, ST.TN{y, tb, tc}, P.top(c), nl, hr)), nd_sub(c, ST.TN{x, ta, ST.TN{y, tb, tc}}, hnd), q_notin(~K, nl, c, ST.TN{x, ta, ST.TN{y, tb, tc}}, hr, hnd))

def rotr_path_rep(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ST.TN{y, ta, tb}, tc}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ST.TN{y, ta, tb}, tc}), P.after(c)))) == True{} : Bool}) -> {ST.rep(~K, ST.TN{y, ta, ST.TN{x, tb, tc}}, P.top(c), RM.rotr_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c))) == True{} : Bool}:
  RT.rotr_rep(~K, ~cmp, ~o, nl, x, y, ta, tb, tc, P.top(c), SP.dir(c), L.and_left(Nat.is_lt(0n, x), Bool.and(ST.is_node(K, ST.nd(K, nl, x), y, ST.rid(tc), P.top(c)), Bool.and(ST.rep(~K, ST.TN{y, ta, tb}, x, nl), ST.rep(~K, tc, x, nl))), hr), L.and_left(Nat.is_lt(0n, y), Bool.and(ST.is_node(K, ST.nd(K, nl, y), ST.rid(ta), ST.rid(tb), x), Bool.and(ST.rep(~K, ta, y, nl), ST.rep(~K, tb, y, nl))), TR.rep_l(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), TR.rep_node(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr), TR.rep_node(~K, y, ta, tb, x, nl, TR.rep_l(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), TR.rep_l(~K, y, ta, tb, x, nl, TR.rep_l(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), TR.rep_r(~K, y, ta, tb, x, nl, TR.rep_l(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr)), TR.rep_r(~K, x, ST.TN{y, ta, tb}, tc, P.top(c), nl, hr), nd_sub(c, ST.TN{x, ST.TN{y, ta, tb}, tc}, hnd), q_notin(~K, nl, c, ST.TN{x, ST.TN{y, ta, tb}, tc}, hr, hnd))


def rotl_path_ctx(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ta, ST.TN{y, tb, tc}}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ta, ST.TN{y, tb, tc}}), P.after(c)))) == True{} : Bool}) -> {P.ctxok(~K, c, y, RM.rotl_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c))) == True{} : Bool}:
  match tb:
    case ST.TE{}:
      RT.rotl_ctx(~K, ~cmp, ~o, nl, c, x, y, 0n, hok, w_notin(c, ST.TN{x, ta, ST.TN{y, ST.TE{}, tc}}, hnd, x, DJ.mem_r(x, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, DJ.mem_hd(x, Con{y, ST.ids(tc)}))), w_notin(c, ST.TN{x, ta, ST.TN{y, ST.TE{}, tc}}, hnd, y, DJ.mem_r(y, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, DJ.mem_tl(y, x, Con{y, ST.ids(tc)}, DJ.mem_hd(y, ST.ids(tc))))), RT.zero_ctx(~K, nl, c, x, hok), RT.nd_drop(P.before(c), ST.ids(ST.TN{x, ta, ST.TN{y, ST.TE{}, tc}}), P.after(c), hnd))
    case ST.TN{+b, +b1, +b2}:
      +mb = DJ.mem_r(b, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)})}, DJ.mem_tl(b, x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)}), DJ.mem_l(b, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)}, P.mem_root(b, b1, b2))))
      RT.rotl_ctx(~K, ~cmp, ~o, nl, c, x, y, b, hok, w_notin(c, ST.TN{x, ta, ST.TN{y, ST.TN{b, b1, b2}, tc}}, hnd, x, DJ.mem_r(x, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)})}, DJ.mem_hd(x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)})))), w_notin(c, ST.TN{x, ta, ST.TN{y, ST.TN{b, b1, b2}, tc}}, hnd, y, DJ.mem_r(y, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)})}, DJ.mem_tl(y, x, SC.append(Nat, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)}), DJ.mem_r(y, ST.ids(ST.TN{b, b1, b2}), Con{y, ST.ids(tc)}, DJ.mem_hd(y, ST.ids(tc)))))), w_notin(c, ST.TN{x, ta, ST.TN{y, ST.TN{b, b1, b2}, tc}}, hnd, b, mb), RT.nd_drop(P.before(c), ST.ids(ST.TN{x, ta, ST.TN{y, ST.TN{b, b1, b2}, tc}}), P.after(c), hnd))


def rotr_path_ctx(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +hr: {ST.rep(~K, ST.TN{x, ST.TN{y, ta, tb}, tc}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{x, ST.TN{y, ta, tb}, tc}), P.after(c)))) == True{} : Bool}) -> {P.ctxok(~K, c, y, RM.rotr_nl(K, nl, x, y, ST.rid(tb), P.top(c), SP.dir(c))) == True{} : Bool}:
  match tb:
    case ST.TE{}:
      RT.rotr_ctx(~K, ~cmp, ~o, nl, c, x, y, 0n, hok, w_notin(c, ST.TN{x, ST.TN{y, ta, ST.TE{}}, tc}, hnd, x, DJ.mem_r(x, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, DJ.mem_hd(x, ST.ids(tc)))), w_notin(c, ST.TN{x, ST.TN{y, ta, ST.TE{}}, tc}, hnd, y, DJ.mem_l(y, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, DJ.mem_r(y, ST.ids(ta), Con{y, Nil{}}, DJ.mem_hd(y, Nil{})))), RT.zero_ctx(~K, nl, c, x, hok), RT.nd_drop(P.before(c), ST.ids(ST.TN{x, ST.TN{y, ta, ST.TE{}}, tc}), P.after(c), hnd))
    case ST.TN{+b, +b1, +b2}:
      +mb = DJ.mem_l(b, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(ST.TN{b, b1, b2})}), Con{x, ST.ids(tc)}, DJ.mem_r(b, ST.ids(ta), Con{y, ST.ids(ST.TN{b, b1, b2})}, DJ.mem_tl(b, y, ST.ids(ST.TN{b, b1, b2}), P.mem_root(b, b1, b2))))
      RT.rotr_ctx(~K, ~cmp, ~o, nl, c, x, y, b, hok, w_notin(c, ST.TN{x, ST.TN{y, ta, ST.TN{b, b1, b2}}, tc}, hnd, x, DJ.mem_r(x, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(ST.TN{b, b1, b2})}), Con{x, ST.ids(tc)}, DJ.mem_hd(x, ST.ids(tc)))), w_notin(c, ST.TN{x, ST.TN{y, ta, ST.TN{b, b1, b2}}, tc}, hnd, y, DJ.mem_l(y, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(ST.TN{b, b1, b2})}), Con{x, ST.ids(tc)}, DJ.mem_r(y, ST.ids(ta), Con{y, ST.ids(ST.TN{b, b1, b2})}, DJ.mem_hd(y, ST.ids(ST.TN{b, b1, b2}))))), w_notin(c, ST.TN{x, ST.TN{y, ta, ST.TN{b, b1, b2}}, tc}, hnd, b, mb), RT.nd_drop(P.before(c), ST.ids(ST.TN{x, ST.TN{y, ta, ST.TN{b, b1, b2}}, tc}), P.after(c), hnd))

# ---- what the rotations keep everywhere ----


def attn_ents(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool) -> {ST.ents(~K, ~V, xs, RM.attn(K, nl, q, y, dir), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+j True{}:
      SE.ents_setl(~K, ~V, xs, nl, pl, 1n+j, y)
    case 1n+j False{}:
      SE.ents_setr(~K, ~V, xs, nl, pl, 1n+j, y)

def rotl_ents(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {ST.ents(~K, ~V, xs, RM.rotl_nl(K, nl, x, y, b, q, dir), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl), ST.ents(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, x, y), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), ST.ents(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setl(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl, y, x), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl), ST.ents(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl, y, q), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl), ST.ents(~K, ~V, xs, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl), ST.ents(~K, ~V, xs, nl, pl), attn_ents(~K, ~V, xs, pl, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl), ST.ents(~K, ~V, xs, SE.setr(K, nl, x, b), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, SE.setr(K, nl, x, b), pl, b, x), SE.ents_setr(~K, ~V, xs, nl, pl, x, b))))))

def rotr_ents(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {ST.ents(~K, ~V, xs, RM.rotr_nl(K, nl, x, y, b, q, dir), pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl), ST.ents(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, x, y), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), ST.ents(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setr(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl, y, x), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl), ST.ents(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl, y, q), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl), ST.ents(~K, ~V, xs, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl), ST.ents(~K, ~V, xs, nl, pl), attn_ents(~K, ~V, xs, pl, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), Equal.trans(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, xs, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl), ST.ents(~K, ~V, xs, SE.setl(K, nl, x, b), pl), ST.ents(~K, ~V, xs, nl, pl), SE.ents_setp(~K, ~V, xs, SE.setl(K, nl, x, b), pl, b, x), SE.ents_setl(~K, ~V, xs, nl, pl, x, b))))))

def attn_oks(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool) -> {EN.oks(~K, ~V, xs, RM.attn(K, nl, q, y, dir), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+j True{}:
      SE.oks_setl(~K, ~V, xs, nl, pl, 1n+j, y)
    case 1n+j False{}:
      SE.oks_setr(~K, ~V, xs, nl, pl, 1n+j, y)

def rotl_oks(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {EN.oks(~K, ~V, xs, RM.rotl_nl(K, nl, x, y, b, q, dir), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl), EN.oks(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, x, y), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), EN.oks(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setl(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl, y, x), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), pl), EN.oks(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl, y, q), Equal.trans(Bool, EN.oks(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), pl), EN.oks(~K, ~V, xs, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl), EN.oks(~K, ~V, xs, nl, pl), attn_oks(~K, ~V, xs, pl, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, SE.setr(K, nl, x, b), b, x), pl), EN.oks(~K, ~V, xs, SE.setr(K, nl, x, b), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, SE.setr(K, nl, x, b), pl, b, x), SE.oks_setr(~K, ~V, xs, nl, pl, x, b))))))

def rotr_oks(~K: Data, ~V: Data, +xs: List<&2, Nat>, +pl: List<&2, Maybe<&2, V>>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {EN.oks(~K, ~V, xs, RM.rotr_nl(K, nl, x, y, b, q, dir), pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), pl), EN.oks(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl, x, y), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), pl), EN.oks(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setr(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl, y, x), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), pl), EN.oks(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl, y, q), Equal.trans(Bool, EN.oks(~K, ~V, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), pl), EN.oks(~K, ~V, xs, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl), EN.oks(~K, ~V, xs, nl, pl), attn_oks(~K, ~V, xs, pl, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), Equal.trans(Bool, EN.oks(~K, ~V, xs, SE.setp(K, SE.setl(K, nl, x, b), b, x), pl), EN.oks(~K, ~V, xs, SE.setl(K, nl, x, b), pl), EN.oks(~K, ~V, xs, nl, pl), SE.oks_setp(~K, ~V, xs, SE.setl(K, nl, x, b), pl, b, x), SE.oks_setl(~K, ~V, xs, nl, pl, x, b))))))

def attn_fll(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool) -> {ST.fll(~K, RM.attn(K, nl, q, y, dir), fl) == ST.fll(~K, nl, fl) : Bool}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+j True{}:
      SE.fll_setl(~K, fl, nl, 1n+j, y)
    case 1n+j False{}:
      SE.fll_setr(~K, fl, nl, 1n+j, y)

def rotl_fll(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {ST.fll(~K, RM.rotl_nl(K, nl, x, y, b, q, dir), fl) == ST.fll(~K, nl, fl) : Bool}:
  Equal.trans(Bool, ST.fll(~K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), fl), ST.fll(~K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), Equal.trans(Bool, ST.fll(~K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), fl), ST.fll(~K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), fl), ST.fll(~K, nl, fl), SE.fll_setl(~K, fl, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), Equal.trans(Bool, ST.fll(~K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), fl), ST.fll(~K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), Equal.trans(Bool, ST.fll(~K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), fl), ST.fll(~K, SE.setp(K, SE.setr(K, nl, x, b), b, x), fl), ST.fll(~K, nl, fl), attn_fll(~K, fl, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), Equal.trans(Bool, ST.fll(~K, SE.setp(K, SE.setr(K, nl, x, b), b, x), fl), ST.fll(~K, SE.setr(K, nl, x, b), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, SE.setr(K, nl, x, b), b, x), SE.fll_setr(~K, fl, nl, x, b))))))

def rotr_fll(~K: Data, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {ST.fll(~K, RM.rotr_nl(K, nl, x, y, b, q, dir), fl) == ST.fll(~K, nl, fl) : Bool}:
  Equal.trans(Bool, ST.fll(~K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), fl), ST.fll(~K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), Equal.trans(Bool, ST.fll(~K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), fl), ST.fll(~K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), fl), ST.fll(~K, nl, fl), SE.fll_setr(~K, fl, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), Equal.trans(Bool, ST.fll(~K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), fl), ST.fll(~K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), Equal.trans(Bool, ST.fll(~K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), fl), ST.fll(~K, SE.setp(K, SE.setl(K, nl, x, b), b, x), fl), ST.fll(~K, nl, fl), attn_fll(~K, fl, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), Equal.trans(Bool, ST.fll(~K, SE.setp(K, SE.setl(K, nl, x, b), b, x), fl), ST.fll(~K, SE.setl(K, nl, x, b), fl), ST.fll(~K, nl, fl), SE.fll_setp(~K, fl, SE.setl(K, nl, x, b), b, x), SE.fll_setl(~K, fl, nl, x, b))))))

def attn_len(~K: Data, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool) -> {SC.length(M.Node<K>, RM.attn(K, nl, q, y, dir)) == SC.length(M.Node<K>, nl) : Nat}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+j True{}:
      SE.setl_len(K, nl, 1n+j, y)
    case 1n+j False{}:
      SE.setr_len(K, nl, 1n+j, y)

def rotl_len(~K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {SC.length(M.Node<K>, RM.rotl_nl(K, nl, x, y, b, q, dir)) == SC.length(M.Node<K>, nl) : Nat}:
  Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y)), SC.length(M.Node<K>, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x)), SC.length(M.Node<K>, nl), SE.setp_len(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), Equal.trans(Nat, SC.length(M.Node<K>, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x)), SC.length(M.Node<K>, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q)), SC.length(M.Node<K>, nl), SE.setl_len(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q)), SC.length(M.Node<K>, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir)), SC.length(M.Node<K>, nl), SE.setp_len(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), Equal.trans(Nat, SC.length(M.Node<K>, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir)), SC.length(M.Node<K>, SE.setp(K, SE.setr(K, nl, x, b), b, x)), SC.length(M.Node<K>, nl), attn_len(~K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, SE.setr(K, nl, x, b), b, x)), SC.length(M.Node<K>, SE.setr(K, nl, x, b)), SC.length(M.Node<K>, nl), SE.setp_len(K, SE.setr(K, nl, x, b), b, x), SE.setr_len(K, nl, x, b))))))

def rotr_len(~K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool) -> {SC.length(M.Node<K>, RM.rotr_nl(K, nl, x, y, b, q, dir)) == SC.length(M.Node<K>, nl) : Nat}:
  Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y)), SC.length(M.Node<K>, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x)), SC.length(M.Node<K>, nl), SE.setp_len(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), Equal.trans(Nat, SC.length(M.Node<K>, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x)), SC.length(M.Node<K>, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q)), SC.length(M.Node<K>, nl), SE.setr_len(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q)), SC.length(M.Node<K>, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir)), SC.length(M.Node<K>, nl), SE.setp_len(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), Equal.trans(Nat, SC.length(M.Node<K>, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir)), SC.length(M.Node<K>, SE.setp(K, SE.setl(K, nl, x, b), b, x)), SC.length(M.Node<K>, nl), attn_len(~K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), Equal.trans(Nat, SC.length(M.Node<K>, SE.setp(K, SE.setl(K, nl, x, b), b, x)), SC.length(M.Node<K>, SE.setl(K, nl, x, b)), SC.length(M.Node<K>, nl), SE.setp_len(K, SE.setl(K, nl, x, b), b, x), SE.setl_len(K, nl, x, b))))))
