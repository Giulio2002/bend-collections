import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./path.bend as P
import ./plug.bend as PG
import ./frame.bend as FRM
import ./frame.bend as FRM
import ./prim.bend as PR
import ./mirror.bend as MI
import ./prim.bend as PR
import ./mirror.bend as MI
import ./nbr.bend as NB

# The successor of a node with two children: the leftmost node of its right
# subtree, reached by a path of left turns below it (the ids before stay);
# copying its key into the node keeps every link.
# (source: tools/generators/tm_hand/succ.src)


# ---- the leftmost node below ----


def lm_up(-K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +j: Nat, +j2: Nat, +a2: ST.Tr, +b2: ST.Tr, +tb: ST.Tr, r: Sigma<&1, &1, List<&2, P.Fr>, lc_ => Sigma<&1, &1, Nat, ls_ => Sigma<&1, &1, ST.Tr, lb_ => {SC.append(Nat, P.before(lc_), SC.append(Nat, ST.ids(ST.TN{ls_, ST.TE{}, lb_}), P.after(lc_))) == SC.append(Nat, P.before(Con{P.FR{j, True{}, tb}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, True{}, tb}, c}))) : List<&2, Nat>} & ({ls_ == ST.fst0(ST.ids(ST.TN{j2, a2, b2})) : Nat} & ({PG.plug(lc_, ST.TN{ls_, ST.TE{}, lb_}) == PG.plug(Con{P.FR{j, True{}, tb}, c}, ST.TN{j2, a2, b2}) : ST.Tr} & ({P.before(lc_) == P.before(Con{P.FR{j, True{}, tb}, c}) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{ls_, ST.TE{}, lb_}, P.top(lc_), nl) == True{} : Bool} & {P.ctxok(~K, lc_, ls_, nl) == True{} : Bool}))))>>>) -> Sigma<&1, &1, List<&2, P.Fr>, lc_ => Sigma<&1, &1, Nat, ls_ => Sigma<&1, &1, ST.Tr, lb_ => {SC.append(Nat, P.before(lc_), SC.append(Nat, ST.ids(ST.TN{ls_, ST.TE{}, lb_}), P.after(lc_))) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb}), P.after(c))) : List<&2, Nat>} & ({ls_ == ST.fst0(ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb})) : Nat} & ({PG.plug(lc_, ST.TN{ls_, ST.TE{}, lb_}) == PG.plug(c, ST.TN{j, ST.TN{j2, a2, b2}, tb}) : ST.Tr} & ({P.before(lc_) == P.before(c) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{ls_, ST.TE{}, lb_}, P.top(lc_), nl) == True{} : Bool} & {P.ctxok(~K, lc_, ls_, nl) == True{} : Bool}))))>>>:
  match r:
    case Tuple{+lc, Tuple{+ls, Tuple{+lb, Tuple{h1, Tuple{h2, rest}}}}}:
      (lc, (ls, (lb, (Equal.trans(List<&2, Nat>, SC.append(Nat, P.before(lc), SC.append(Nat, ST.ids(ST.TN{ls, ST.TE{}, lb}), P.after(lc))), SC.append(Nat, P.before(Con{P.FR{j, True{}, tb}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, True{}, tb}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb}), P.after(c))), h1, Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{j, True{}, tb}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, True{}, tb}, c}))), P.ids_l(c, j, ST.TN{j2, a2, b2}, tb))), (Equal.trans(Nat, ls, ST.fst0(ST.ids(ST.TN{j2, a2, b2})), ST.fst0(ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb})), h2, Equal.sym(Nat, ST.fst0(ST.ids(ST.TN{j, ST.TN{j2, a2, b2}, tb})), ST.fst0(ST.ids(ST.TN{j2, a2, b2})), NB.fst0_app(ST.ids(a2), j2, ST.ids(b2), Con{j, ST.ids(tb)}))), rest)))))


# descending left from a node the path leads to
def lmost(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +ta: ST.Tr, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +j: Nat, +tb: ST.Tr, +hr: {ST.rep(~K, ST.TN{j, ta, tb}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, j, nl) == True{} : Bool}) -> Sigma<&1, &1, List<&2, P.Fr>, lc_ => Sigma<&1, &1, Nat, ls_ => Sigma<&1, &1, ST.Tr, lb_ => {SC.append(Nat, P.before(lc_), SC.append(Nat, ST.ids(ST.TN{ls_, ST.TE{}, lb_}), P.after(lc_))) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ta, tb}), P.after(c))) : List<&2, Nat>} & ({ls_ == ST.fst0(ST.ids(ST.TN{j, ta, tb})) : Nat} & ({PG.plug(lc_, ST.TN{ls_, ST.TE{}, lb_}) == PG.plug(c, ST.TN{j, ta, tb}) : ST.Tr} & ({P.before(lc_) == P.before(c) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{ls_, ST.TE{}, lb_}, P.top(lc_), nl) == True{} : Bool} & {P.ctxok(~K, lc_, ls_, nl) == True{} : Bool}))))>>>:
  match ta:
    case ST.TE{}:
      (c, (j, (tb, ({==}, ({==}, ({==}, ({==}, (hr, hok))))))))
    case ST.TN{+j2, +a2, +b2}:
      lm_up(K, nl, c, j, j2, a2, b2, tb, lmost(~K, ~cmp, ~o, a2, nl, Con{P.FR{j, True{}, tb}, c}, j2, b2, Pair.snd({P.ctxok(~K, Con{P.FR{j, True{}, tb}, c}, j2, nl) == True{} : Bool}, {ST.rep(~K, ST.TN{j2, a2, b2}, j, nl) == True{} : Bool}, P.ok_l(~K, nl, c, j, ST.TN{j2, a2, b2}, tb, hr, hok)), Pair.fst({P.ctxok(~K, Con{P.FR{j, True{}, tb}, c}, j2, nl) == True{} : Bool}, {ST.rep(~K, ST.TN{j2, a2, b2}, j, nl) == True{} : Bool}, P.ok_l(~K, nl, c, j, ST.TN{j2, a2, b2}, tb, hr, hok))))

# ---- a node's key changed, its links kept ----


def isn_at(-K: Data, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +a: Nat, +b: Nat, +q: Nat) -> {ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), 1n+ii), a, b, q) == ST.is_node(K, ST.nd(K, nl, 1n+ii), a, b, q) : Bool}:
  %Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), 1n+ii), M.N{c0, a0, b0, q0, ks}, FRM.nd_wr_same(K, nl, ii, M.N{c0, a0, b0, q0, ks}, hb)) : {ST.is_node(K, _, a, b, q) == ST.is_node(K, ST.nd(K, nl, 1n+ii), a, b, q) : Bool}
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+ii), M.N{c0, a0, b0, q0, k0}, hx) : {ST.is_node(K, M.N{c0, a0, b0, q0, ks}, a, b, q) == ST.is_node(K, _, a, b, q) : Bool}
  {==}

def isn_kc(-K: Data, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +j: Nat, +a: Nat, +b: Nat, +q: Nat, +e: Bool, +he: {Nat.is_eq(1n+ii, j) == e : Bool}) -> {ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), j), a, b, q) == ST.is_node(K, ST.nd(K, nl, j), a, b, q) : Bool}:
  match e:
    case False{}:
      %Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), j), ST.nd(K, nl, j), FRM.nd_wr_other(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}, j, he)) : {ST.is_node(K, _, a, b, q) == ST.is_node(K, ST.nd(K, nl, j), a, b, q) : Bool}
      {==}
    case True{}:
      L.subst(Nat, z => {ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), z), a, b, q) == ST.is_node(K, ST.nd(K, nl, z), a, b, q) : Bool}, 1n+ii, j, N.eq_from_is_eq(1n+ii, j, he), isn_at(K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, a, b, q))

def isn_k(-K: Data, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +j: Nat, +a: Nat, +b: Nat, +q: Nat) -> {ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), j), a, b, q) == ST.is_node(K, ST.nd(K, nl, j), a, b, q) : Bool}:
  isn_kc(K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, j, a, b, q, Nat.is_eq(1n+ii, j), {==})


def rep_k(~K: Data, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +t: ST.Tr, +p: Nat) -> {ST.rep(~K, t, p, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})) == ST.rep(~K, t, p, nl) : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+j, +tl, +tr}:
      %Equal.sym(Bool, ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), j), ST.rid(tl), ST.rid(tr), p), ST.is_node(K, ST.nd(K, nl, j), ST.rid(tl), ST.rid(tr), p), isn_k(K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, j, ST.rid(tl), ST.rid(tr), p)) : {Bool.and(Nat.is_lt(0n, j), Bool.and(_, Bool.and(ST.rep(~K, tl, j, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})), ST.rep(~K, tr, j, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}))))) == ST.rep(~K, ST.TN{j, tl, tr}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, tl, j, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})), ST.rep(~K, tl, j, nl), rep_k(~K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, tl, j)) : {Bool.and(Nat.is_lt(0n, j), Bool.and(ST.is_node(K, ST.nd(K, nl, j), ST.rid(tl), ST.rid(tr), p), Bool.and(_, ST.rep(~K, tr, j, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}))))) == ST.rep(~K, ST.TN{j, tl, tr}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, tr, j, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})), ST.rep(~K, tr, j, nl), rep_k(~K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, tr, j)) : {Bool.and(Nat.is_lt(0n, j), Bool.and(ST.is_node(K, ST.nd(K, nl, j), ST.rid(tl), ST.rid(tr), p), Bool.and(ST.rep(~K, tl, j, nl), _))) == ST.rep(~K, ST.TN{j, tl, tr}, p, nl) : Bool}
      {==}


def ctx_k(~K: Data, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +c: List<&2, P.Fr>, +x: Nat) -> {P.ctxok(~K, c, x, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})) == P.ctxok(~K, c, x, nl) : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{+q, +lft, +s}, +u}:
      %Equal.sym(Bool, ST.is_node(K, ST.nd(K, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.is_node(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), isn_k(K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, q, ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u))) : {Bool.and(Bool.and(Nat.is_lt(0n, q), Bool.and(_, ST.rep(~K, s, q, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})))), P.ctxok(~K, u, q, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}))) == P.ctxok(~K, Con{P.FR{q, lft, s}, u}, x, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, s, q, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})), ST.rep(~K, s, q, nl), rep_k(~K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, s, q)) : {Bool.and(Bool.and(Nat.is_lt(0n, q), Bool.and(ST.is_node(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), _)), P.ctxok(~K, u, q, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}))) == P.ctxok(~K, Con{P.FR{q, lft, s}, u}, x, nl) : Bool}
      %Equal.sym(Bool, P.ctxok(~K, u, q, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks})), P.ctxok(~K, u, q, nl), ctx_k(~K, nl, ii, c0, a0, b0, q0, k0, ks, hx, hb, u, q)) : {Bool.and(Bool.and(Nat.is_lt(0n, q), Bool.and(ST.is_node(K, ST.nd(K, nl, q), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, q, nl))), _) == P.ctxok(~K, Con{P.FR{q, lft, s}, u}, x, nl) : Bool}
      {==}

# ---- the move: the successor's key and payload into the node ----


def msucc_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l: Nat, +d: Nat, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +ii: Nat, +c0: Bool, +a0: Nat, +b0: Nat, +q0: Nat, +k0: K, +ks: K, +hx: {ST.nd(K, nl, 1n+ii) == M.N{c0, a0, b0, q0, k0} : M.Node<K>}, +hb: {Nat.is_lt(ii, SC.length(M.Node<K>, nl)) == True{} : Bool}, +s: Nat, +cs: Bool, +as: Nat, +bs: Nat, +qs: Nat, +hs: {ST.nd(K, nl, s) == M.N{cs, as, bs, qs, ks} : M.Node<K>}) -> {MI.move_successor(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, pl, tg, fl}, 1n+ii, s) == (ST.SH{n, root, lo, hi, free, l, d, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), PR.ex_pl(V, PR.ex_pl(V, pl, s, None{}), 1n+ii, ST.pv(V, pl, s)), tg, fl}, s) : ST.Sh<K, V> & Nat}:
  %Equal.sym(M.Node<K>, ST.nd(K, nl, s), M.N{cs, as, bs, qs, ks}, hs) : {MI.move_successor_3(~K, ~V, ~cmp, s, MI.exchange(~K, ~V, ~cmp, MI.copy_key(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, s, None{}), tg, fl}, 1n+ii, _), 1n+ii, ST.pv(V, pl, s))) == (ST.SH{n, root, lo, hi, free, l, d, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), PR.ex_pl(V, PR.ex_pl(V, pl, s, None{}), 1n+ii, ST.pv(V, pl, s)), tg, fl}, s) : ST.Sh<K, V> & Nat}
  %Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+ii), M.N{c0, a0, b0, q0, k0}, hx) : {MI.move_successor_3(~K, ~V, ~cmp, s, MI.exchange(~K, ~V, ~cmp, MI.set_key_node(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l, d, nl, PR.ex_pl(V, pl, s, None{}), tg, fl}, 1n+ii, ks, _), 1n+ii, ST.pv(V, pl, s))) == (ST.SH{n, root, lo, hi, free, l, d, PR.wr_nl(K, nl, 1n+ii, M.N{c0, a0, b0, q0, ks}), PR.ex_pl(V, PR.ex_pl(V, pl, s, None{}), 1n+ii, ST.pv(V, pl, s)), tg, fl}, s) : ST.Sh<K, V> & Nat}
  {==}

# ---- the rightmost node below ----


def rm_up(-K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +j: Nat, +ta: ST.Tr, +j2: Nat, +a2: ST.Tr, +b2: ST.Tr, r: Sigma<&1, &1, List<&2, P.Fr>, rc_ => Sigma<&1, &1, Nat, rs_ => Sigma<&1, &1, ST.Tr, ra_ => {SC.append(Nat, P.before(rc_), SC.append(Nat, ST.ids(ST.TN{rs_, ra_, ST.TE{}}), P.after(rc_))) == SC.append(Nat, P.before(Con{P.FR{j, False{}, ta}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, False{}, ta}, c}))) : List<&2, Nat>} & ({rs_ == ST.last0(ST.ids(ST.TN{j2, a2, b2})) : Nat} & ({PG.plug(rc_, ST.TN{rs_, ra_, ST.TE{}}) == PG.plug(Con{P.FR{j, False{}, ta}, c}, ST.TN{j2, a2, b2}) : ST.Tr} & ({P.after(rc_) == P.after(Con{P.FR{j, False{}, ta}, c}) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{rs_, ra_, ST.TE{}}, P.top(rc_), nl) == True{} : Bool} & {P.ctxok(~K, rc_, rs_, nl) == True{} : Bool}))))>>>) -> Sigma<&1, &1, List<&2, P.Fr>, rc_ => Sigma<&1, &1, Nat, rs_ => Sigma<&1, &1, ST.Tr, ra_ => {SC.append(Nat, P.before(rc_), SC.append(Nat, ST.ids(ST.TN{rs_, ra_, ST.TE{}}), P.after(rc_))) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}}), P.after(c))) : List<&2, Nat>} & ({rs_ == ST.last0(ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}})) : Nat} & ({PG.plug(rc_, ST.TN{rs_, ra_, ST.TE{}}) == PG.plug(c, ST.TN{j, ta, ST.TN{j2, a2, b2}}) : ST.Tr} & ({P.after(rc_) == P.after(c) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{rs_, ra_, ST.TE{}}, P.top(rc_), nl) == True{} : Bool} & {P.ctxok(~K, rc_, rs_, nl) == True{} : Bool}))))>>>:
  match r:
    case Tuple{+rc, Tuple{+rs, Tuple{+ra, Tuple{h1, Tuple{h2, rest}}}}}:
      (rc, (rs, (ra, (Equal.trans(List<&2, Nat>, SC.append(Nat, P.before(rc), SC.append(Nat, ST.ids(ST.TN{rs, ra, ST.TE{}}), P.after(rc))), SC.append(Nat, P.before(Con{P.FR{j, False{}, ta}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, False{}, ta}, c}))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}}), P.after(c))), h1, Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{j, False{}, ta}, c}), SC.append(Nat, ST.ids(ST.TN{j2, a2, b2}), P.after(Con{P.FR{j, False{}, ta}, c}))), P.ids_r(c, j, ta, ST.TN{j2, a2, b2}))), (Equal.trans(Nat, rs, ST.last0(ST.ids(ST.TN{j2, a2, b2})), ST.last0(ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}})), h2, Equal.sym(Nat, ST.last0(ST.ids(ST.TN{j, ta, ST.TN{j2, a2, b2}})), ST.last0(ST.ids(ST.TN{j2, a2, b2})), NB.last0_sub(ST.ids(ta), j, j2, a2, b2))), rest)))))


# descending right from a node the path leads to
def rmost(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +tb: ST.Tr, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +j: Nat, +ta: ST.Tr, +hr: {ST.rep(~K, ST.TN{j, ta, tb}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, j, nl) == True{} : Bool}) -> Sigma<&1, &1, List<&2, P.Fr>, rc_ => Sigma<&1, &1, Nat, rs_ => Sigma<&1, &1, ST.Tr, ra_ => {SC.append(Nat, P.before(rc_), SC.append(Nat, ST.ids(ST.TN{rs_, ra_, ST.TE{}}), P.after(rc_))) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{j, ta, tb}), P.after(c))) : List<&2, Nat>} & ({rs_ == ST.last0(ST.ids(ST.TN{j, ta, tb})) : Nat} & ({PG.plug(rc_, ST.TN{rs_, ra_, ST.TE{}}) == PG.plug(c, ST.TN{j, ta, tb}) : ST.Tr} & ({P.after(rc_) == P.after(c) : List<&2, Nat>} & ({ST.rep(~K, ST.TN{rs_, ra_, ST.TE{}}, P.top(rc_), nl) == True{} : Bool} & {P.ctxok(~K, rc_, rs_, nl) == True{} : Bool}))))>>>:
  match tb:
    case ST.TE{}:
      (c, (j, (ta, ({==}, (Equal.sym(Nat, ST.last0(SC.append(Nat, ST.ids(ta), Con{j, Nil{}})), j, NB.last0_snoc(ST.ids(ta), j)), ({==}, ({==}, (hr, hok))))))))
    case ST.TN{+j2, +a2, +b2}:
      rm_up(K, nl, c, j, ta, j2, a2, b2, rmost(~K, ~cmp, ~o, b2, nl, Con{P.FR{j, False{}, ta}, c}, j2, a2, Pair.snd({P.ctxok(~K, Con{P.FR{j, False{}, ta}, c}, j2, nl) == True{} : Bool}, {ST.rep(~K, ST.TN{j2, a2, b2}, j, nl) == True{} : Bool}, P.ok_r(~K, nl, c, j, ta, ST.TN{j2, a2, b2}, hr, hok)), Pair.fst({P.ctxok(~K, Con{P.FR{j, False{}, ta}, c}, j2, nl) == True{} : Bool}, {ST.rep(~K, ST.TN{j2, a2, b2}, j, nl) == True{} : Bool}, P.ok_r(~K, nl, c, j, ta, ST.TN{j2, a2, b2}, hr, hok))))
