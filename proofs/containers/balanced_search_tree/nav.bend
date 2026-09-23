import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./path.bend as P
import ./nbr.bend as NB
import ../../lib/nat_list.bend as NL

# Navigation (floor, ceiling, lower, higher): the loop descends by
# comparison keeping the best candidate, which along the path is the first
# id after (upward) or the last before (downward) the current subtree; at an
# equal key it answers the node (inclusive) or its neighbour. The loop is
# the ghost navigation gnav. (source: tools/generators/tm_hand/nav.src)


def gnav(~K: Data, ~cmp: K -> K -> Cmp, t: ST.Tr, +c: List<&2, P.Fr>, +nl: List<&2, M.Node<K>>, +k: K, +h: Bool, +incl: Bool) -> Nat:
  match t:
    case ST.TE{}:
      ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c)))
    case ST.TN{+i, +l, +r}:
      TR.pk3(Nat, TR.kc(~K, ~cmp, k, ST.nd(K, nl, i)), gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))


# the candidate after a step left / right
def best_l(+h: Bool, +i: Nat, +a: Nat, +b: Nat) -> {M.pick(Nat, h, i, ST.pk(Nat, h, a, b)) == ST.pk(Nat, h, i, b) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def best_r(+h: Bool, +i: Nat, +a: Nat, +b: Nat) -> {M.pick(Nat, h, ST.pk(Nat, h, a, b), i) == ST.pk(Nat, h, a, i) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def nav_eq(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +i: Nat, +h: Bool, +incl: Bool, +v: Nat, +e: {MI.neighbor(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, i, h) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, v) : ST.Sh<K, V> & Nat}) -> {MI.nav_equal(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, i, h, incl) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, incl, i, v)) : ST.Sh<K, V> & Nat}:
  match incl:
    case True{}:
      {==}
    case False{}:
      e


def nav_c(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +k: K, +h: Bool, +incl: Bool, +g: Nat, +cc: Bool, +a: Nat, +b: Nat, +q: Nat, +key: K, +ea: {a == ST.rid(l) : Nat}, +eb: {b == ST.rid(r) : Nat}, +ihl: {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(l), ST.pk(Nat, h, i, ST.last0(P.before(c))), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(l), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, +ihr: {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(r), ST.pk(Nat, h, ST.fst0(P.after(c)), i), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(r), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, +ne: {MI.neighbor(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, i, h) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}, +o: Cmp) -> {MI.nav_loop(~K, ~V, ~cmp, 1n+g, k, h, incl, i, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, (M.N{cc, a, b, q, key}, o))) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, TR.pk3(Nat, o, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))) : ST.Sh<K, V> & Nat}:
  match o:
    case LT{}:
      %Equal.sym(Nat, a, ST.rid(l), ea) : {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, _, M.pick(Nat, h, i, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c)))), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
      %Equal.sym(Nat, M.pick(Nat, h, i, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c)))), ST.pk(Nat, h, i, ST.last0(P.before(c))), best_l(h, i, ST.fst0(P.after(c)), ST.last0(P.before(c)))) : {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(l), _, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(l), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
      ihl
    case GT{}:
      %Equal.sym(Nat, b, ST.rid(r), eb) : {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, _, M.pick(Nat, h, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), i), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, _, k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
      %Equal.sym(Nat, M.pick(Nat, h, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), i), ST.pk(Nat, h, ST.fst0(P.after(c)), i), best_r(h, i, ST.fst0(P.after(c)), ST.last0(P.before(c)))) : {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(r), _, MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(r), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}
      ihr
    case EQ{}:
      nav_eq(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, i, h, incl, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))), ne)

def nav_node(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +k: K, +h: Bool, +incl: Bool, +g: Nat, +x: M.Node<K>, +hx: {ST.is_node(K, x, ST.rid(l), ST.rid(r), P.top(c)) == True{} : Bool}, +ihl: {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(l), ST.pk(Nat, h, i, ST.last0(P.before(c))), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(l), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, +ihr: {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(r), ST.pk(Nat, h, ST.fst0(P.after(c)), i), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(r), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, +ne: {MI.neighbor(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, i, h) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}) -> {MI.nav_loop(~K, ~V, ~cmp, 1n+g, k, h, incl, i, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), MI.probe_node(~K, ~V, ~cmp, i, k, (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, x))) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, TR.pk3(Nat, TR.kc(~K, ~cmp, k, x), gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))) : ST.Sh<K, V> & Nat}:
  match x:
    case M.Free{fx}:
      Empty.absurd({MI.nav_loop(~K, ~V, ~cmp, 1n+g, k, h, incl, i, ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), MI.probe_node(~K, ~V, ~cmp, i, k, (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, M.Free{fx}))) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, TR.pk3(Nat, EQ{}, gnav(~K, ~cmp, l, Con{P.FR{i, True{}, r}, c}, nl, k, h, incl), gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl), ST.pk(Nat, incl, i, ST.pk(Nat, h, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))))) : ST.Sh<K, V> & Nat}, L.false_true(hx))
    case M.N{+cc, +a, +b, +q, +key}:
      +ha = L.and_left(Nat.is_eq(a, ST.rid(l)), Bool.and(Nat.is_eq(b, ST.rid(r)), Nat.is_eq(q, P.top(c))), hx)
      +hb = L.and_left(Nat.is_eq(b, ST.rid(r)), Nat.is_eq(q, P.top(c)), L.and_right(Nat.is_eq(a, ST.rid(l)), Bool.and(Nat.is_eq(b, ST.rid(r)), Nat.is_eq(q, P.top(c))), hx))
      nav_c(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, k, h, incl, g, cc, a, b, q, key, N.eq_from_is_eq(a, ST.rid(l), ha), N.eq_from_is_eq(b, ST.rid(r), hb), ihl, ihr, ne, cmp(k, key))


# the loop from a subtree the path leads to is the ghost navigation
def nav_ptr(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +f: Nat, +c: List<&2, P.Fr>, +t: ST.Tr, +k: K, +h: Bool, +incl: Bool, +hr: {ST.rep(~K, t, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, ST.rid(t), nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(t), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}, +hf: {Nat.is_lt(TR.ht(t), f) == True{} : Bool}) -> {MI.nav_loop(~K, ~V, ~cmp, f, k, h, incl, ST.rid(t), ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(t), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, t, c, nl, k, h, incl)) : ST.Sh<K, V> & Nat}:
  match f t:
    case 0n +t:
      Empty.absurd({MI.nav_loop(~K, ~V, ~cmp, 0n, k, h, incl, ST.rid(t), ST.pk(Nat, h, ST.fst0(P.after(c)), ST.last0(P.before(c))), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(t), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, t, c, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, L.true_not_false(Nat.is_lt(TR.ht(t), 0n), hf, N.not_lt_zero(TR.ht(t))))
    case 1n+g ST.TE{}:
      {==}
    case 1n+g ST.TN{+i, +l, +r}:
      +el = P.ids_l(c, i, l, r)
      +er = P.ids_r(c, i, l, r)
      +ihl = nav_ptr(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, g, Con{P.FR{i, True{}, r}, c}, l, k, h, incl, Pair.snd({P.ctxok(~K, Con{P.FR{i, True{}, r}, c}, ST.rid(l), nl) == True{} : Bool}, {ST.rep(~K, l, i, nl) == True{} : Bool}, P.ok_l(~K, nl, c, i, l, r, hr, hok)), Pair.fst({P.ctxok(~K, Con{P.FR{i, True{}, r}, c}, ST.rid(l), nl) == True{} : Bool}, {ST.rep(~K, l, i, nl) == True{} : Bool}, P.ok_l(~K, nl, c, i, l, r, hr, hok)), L.subst(List<&2, Nat>, z => {NL.nodupn(z) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, True{}, r}, c}), SC.append(Nat, ST.ids(l), P.after(Con{P.FR{i, True{}, r}, c}))), el, hnd), Equal.trans(List<&2, Nat>, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, True{}, r}, c}), SC.append(Nat, ST.ids(l), P.after(Con{P.FR{i, True{}, r}, c}))), hid, el), hn, TR.ht_l(i, l, r, g, hf))
      +ihr0 = nav_ptr(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, g, Con{P.FR{i, False{}, l}, c}, r, k, h, incl, Pair.snd({P.ctxok(~K, Con{P.FR{i, False{}, l}, c}, ST.rid(r), nl) == True{} : Bool}, {ST.rep(~K, r, i, nl) == True{} : Bool}, P.ok_r(~K, nl, c, i, l, r, hr, hok)), Pair.fst({P.ctxok(~K, Con{P.FR{i, False{}, l}, c}, ST.rid(r), nl) == True{} : Bool}, {ST.rep(~K, r, i, nl) == True{} : Bool}, P.ok_r(~K, nl, c, i, l, r, hr, hok)), L.subst(List<&2, Nat>, z => {NL.nodupn(z) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, False{}, l}, c}), SC.append(Nat, ST.ids(r), P.after(Con{P.FR{i, False{}, l}, c}))), er, hnd), Equal.trans(List<&2, Nat>, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), SC.append(Nat, P.before(Con{P.FR{i, False{}, l}, c}), SC.append(Nat, ST.ids(r), P.after(Con{P.FR{i, False{}, l}, c}))), hid, er), hn, TR.ht_r(i, l, r, g, hf))
      +ihr = L.subst(Nat, z => {MI.nav_loop(~K, ~V, ~cmp, g, k, h, incl, ST.rid(r), ST.pk(Nat, h, ST.fst0(P.after(c)), z), MI.probe(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.rid(r), k)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, gnav(~K, ~cmp, r, Con{P.FR{i, False{}, l}, c}, nl, k, h, incl)) : ST.Sh<K, V> & Nat}, ST.last0(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(l), Con{i, Nil{}}))), i, NB.last0_end(P.before(c), ST.ids(l), i), ihr0)
      +ne = NB.neighbor_m(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn, h)
      nav_node(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, k, h, incl, g, ST.nd(K, nl, i), TR.rep_node(~K, i, l, r, P.top(c), nl, hr), ihl, ihr, ne)
