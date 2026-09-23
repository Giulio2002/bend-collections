import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/order.bend as O
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./prim.bend as PR
import ./path.bend as P
import ./ends.bend as EN
import ./frame.bend as FR
import ../../lib/nat_list.bend as NL

# Two node lists agreeing on a list of ids (a Bool, so the fact can be used
# many times): nodes compared field by field, keys by the comparator, which
# for a lawful one is equality. Agreement on a subtree's ids keeps its links,
# on a list its entries, on a path its frames; a write agrees off its id;
# agreement composes. (source: tools/generators/tm_hand/agree.src)


def beq(+a: Bool, +b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def ndeq(~K: Data, ~cmp: K -> K -> Cmp, x: M.Node<K>, y: M.Node<K>) -> Bool:
  match x y:
    case M.Free{+a} M.Free{+b}:
      Nat.is_eq(a, b)
    case M.Free{a} M.N{c2, a2, b2, q2, k2}:
      False{}
    case M.N{c, a, b, q, k} M.Free{f}:
      False{}
    case M.N{+c, +a, +b, +q, +k} M.N{+c2, +a2, +b2, +q2, +k2}:
      Bool.and(beq(c, c2), Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2))))))

def beq_refl(+a: Bool) -> {beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def beq_eq(+a: Bool, +b: Bool, +h: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, L.false_true(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, L.false_true(h))
    case False{} False{}:
      {==}

def iseq_eq(+c: Cmp, +h: {S.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(h))

def ndeq_refl(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +x: M.Node<K>) -> {ndeq(~K, ~cmp, x, x) == True{} : Bool}:
  match x:
    case M.Free{+a}:
      N.is_eq_refl(a)
    case M.N{+c, +a, +b, +q, +k}:
      %Equal.sym(Bool, beq(c, c), True{}, beq_refl(c)) : {Bool.and(_, Bool.and(Nat.is_eq(a, a), Bool.and(Nat.is_eq(b, b), Bool.and(Nat.is_eq(q, q), S.is_eq(cmp(k, k)))))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(a, a), True{}, N.is_eq_refl(a)) : {Bool.and(True{}, Bool.and(_, Bool.and(Nat.is_eq(b, b), Bool.and(Nat.is_eq(q, q), S.is_eq(cmp(k, k)))))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(b, b), True{}, N.is_eq_refl(b)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Bool.and(Nat.is_eq(q, q), S.is_eq(cmp(k, k)))))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(q, q), True{}, N.is_eq_refl(q)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(_, S.is_eq(cmp(k, k)))))) == True{} : Bool}
      %Equal.sym(Cmp, cmp(k, k), EQ{}, O.refl(~K, ~cmp, ~o, k)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, S.is_eq(_))))) == True{} : Bool}
      {==}


def ndeq_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +x: M.Node<K>, +y: M.Node<K>, +h: {ndeq(~K, ~cmp, x, y) == True{} : Bool}) -> {x == y : M.Node<K>}:
  match x y:
    case M.Free{+a} M.Free{+b}:
      %Equal.sym(Nat, a, b, N.eq_from_is_eq(a, b, h)) : {M.Free{_} == M.Free{b} : M.Node<K>}
      {==}
    case M.Free{a} M.N{c2, a2, b2, q2, k2}:
      Empty.absurd({M.Free{a} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}, L.false_true(h))
    case M.N{c, a, b, q, k} M.Free{f}:
      Empty.absurd({M.N{c, a, b, q, k} == M.Free{f} : M.Node<K>}, L.false_true(h))
    case M.N{+c, +a, +b, +q, +k} M.N{+c2, +a2, +b2, +q2, +k2}:
      +h2 = L.and_right(beq(c, c2), Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2))))), h)
      +h3 = L.and_right(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2)))), h2)
      +h4 = L.and_right(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2))), h3)
      +h5 = L.and_right(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2)), h4)
      %Equal.sym(Bool, c, c2, beq_eq(c, c2, L.and_left(beq(c, c2), Bool.and(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2))))), h))) : {M.N{_, a, b, q, k} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}
      %Equal.sym(Nat, a, a2, N.eq_from_is_eq(a, a2, L.and_left(Nat.is_eq(a, a2), Bool.and(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2)))), h2))) : {M.N{c2, _, b, q, k} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}
      %Equal.sym(Nat, b, b2, N.eq_from_is_eq(b, b2, L.and_left(Nat.is_eq(b, b2), Bool.and(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2))), h3))) : {M.N{c2, a2, _, q, k} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}
      %Equal.sym(Nat, q, q2, N.eq_from_is_eq(q, q2, L.and_left(Nat.is_eq(q, q2), S.is_eq(cmp(k, k2)), h4))) : {M.N{c2, a2, b2, _, k} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}
      %Equal.sym(K, k, k2, O.antisym(~K, ~cmp, o, k, k2, iseq_eq(cmp(k, k2), h5))) : {M.N{c2, a2, b2, q2, _} == M.N{c2, a2, b2, q2, k2} : M.Node<K>}
      {==}

def ndeq_of_eq(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +x: M.Node<K>, +y: M.Node<K>, +e: {x == y : M.Node<K>}) -> {ndeq(~K, ~cmp, x, y) == True{} : Bool}:
  L.subst(M.Node<K>, z => {ndeq(~K, ~cmp, x, z) == True{} : Bool}, x, y, e, ndeq_refl(~K, ~cmp, ~o, x))

# ---- agreement on a list of ids ----

def agr(~K: Data, ~cmp: K -> K -> Cmp, xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+j, t}:
      Bool.and(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, nl2, j)), agr(~K, ~cmp, t, nl, nl2))


def agr_head(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +j: Nat, +t: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, Con{j, t}, nl, nl2) == True{} : Bool}) -> {ST.nd(K, nl, j) == ST.nd(K, nl2, j) : M.Node<K>}:
  ndeq_eq(~K, ~cmp, ~o, ST.nd(K, nl, j), ST.nd(K, nl2, j), L.and_left(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, nl2, j)), agr(~K, ~cmp, t, nl, nl2), h))

def agr_refl(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>) -> {agr(~K, ~cmp, xs, nl, nl) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, nl, j)), agr(~K, ~cmp, t, nl, nl), ndeq_refl(~K, ~cmp, ~o, ST.nd(K, nl, j)), agr_refl(~K, ~cmp, ~o, t, nl))

def agr_trans(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +c: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, xs, a, b) == True{} : Bool}, +h2: {agr(~K, ~cmp, xs, b, c) == True{} : Bool}) -> {agr(~K, ~cmp, xs, a, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      +e1 = ndeq_eq(~K, ~cmp, ~o, ST.nd(K, a, j), ST.nd(K, b, j), L.and_left(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), h))
      +e2 = ndeq_eq(~K, ~cmp, ~o, ST.nd(K, b, j), ST.nd(K, c, j), L.and_left(ndeq(~K, ~cmp, ST.nd(K, b, j), ST.nd(K, c, j)), agr(~K, ~cmp, t, b, c), h2))
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, c, j)), agr(~K, ~cmp, t, a, c), ndeq_of_eq(~K, ~cmp, ~o, ST.nd(K, a, j), ST.nd(K, c, j), Equal.trans(M.Node<K>, ST.nd(K, a, j), ST.nd(K, b, j), ST.nd(K, c, j), e1, e2)), agr_trans(~K, ~cmp, ~o, t, a, b, c, L.and_right(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), h), L.and_right(ndeq(~K, ~cmp, ST.nd(K, b, j), ST.nd(K, c, j)), agr(~K, ~cmp, t, b, c), h2)))

def agr_sym(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, xs, a, b) == True{} : Bool}) -> {agr(~K, ~cmp, xs, b, a) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, b, j), ST.nd(K, a, j)), agr(~K, ~cmp, t, b, a), ndeq_of_eq(~K, ~cmp, ~o, ST.nd(K, b, j), ST.nd(K, a, j), Equal.sym(M.Node<K>, ST.nd(K, a, j), ST.nd(K, b, j), ndeq_eq(~K, ~cmp, ~o, ST.nd(K, a, j), ST.nd(K, b, j), L.and_left(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), h)))), agr_sym(~K, ~cmp, ~o, t, a, b, L.and_right(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), h)))

def agr_l(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, SC.append(Nat, xs, ys), a, b) == True{} : Bool}) -> {agr(~K, ~cmp, xs, a, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), L.and_left(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, SC.append(Nat, t, ys), a, b), h), agr_l(~K, ~cmp, ~o, t, ys, a, b, L.and_right(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, SC.append(Nat, t, ys), a, b), h)))

def agr_r(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, SC.append(Nat, xs, ys), a, b) == True{} : Bool}) -> {agr(~K, ~cmp, ys, a, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+j, +t}:
      agr_r(~K, ~cmp, ~o, t, ys, a, b, L.and_right(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, SC.append(Nat, t, ys), a, b), h))

def agr_app(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +hx: {agr(~K, ~cmp, xs, a, b) == True{} : Bool}, +hy: {agr(~K, ~cmp, ys, a, b) == True{} : Bool}) -> {agr(~K, ~cmp, SC.append(Nat, xs, ys), a, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+j, +t}:
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, SC.append(Nat, t, ys), a, b), L.and_left(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), hx), agr_app(~K, ~cmp, ~o, t, ys, a, b, L.and_right(ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), agr(~K, ~cmp, t, a, b), hx), hy))

# a write agrees off its id
def agr_wr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +id: Nat, +x: M.Node<K>, +hn: {NL.memn(id, xs) == False{} : Bool}) -> {agr(~K, ~cmp, xs, nl, PR.wr_nl(K, nl, id, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      L.and_intro(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, PR.wr_nl(K, nl, id, x), j)), agr(~K, ~cmp, t, nl, PR.wr_nl(K, nl, id, x)), ndeq_of_eq(~K, ~cmp, ~o, ST.nd(K, nl, j), ST.nd(K, PR.wr_nl(K, nl, id, x), j), Equal.sym(M.Node<K>, ST.nd(K, PR.wr_nl(K, nl, id, x), j), ST.nd(K, nl, j), FR.nd_wr_other(K, nl, id, x, j, FR.ne_sym(j, id, FR.or_f_l(Nat.is_eq(j, id), NL.memn(id, t), hn))))), agr_wr(~K, ~cmp, ~o, t, nl, id, x, FR.or_f_r(Nat.is_eq(j, id), NL.memn(id, t), hn)))

# ---- what agreement keeps ----


def rep_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +t: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, ST.ids(t), nl, nl2) == True{} : Bool}) -> {ST.rep(~K, t, p, nl2) == ST.rep(~K, t, p, nl) : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +l, +r}:
      +hr = agr_r(~K, ~cmp, ~o, ST.ids(l), Con{i, ST.ids(r)}, nl, nl2, h)
      %Equal.sym(M.Node<K>, ST.nd(K, nl2, i), ST.nd(K, nl, i), Equal.sym(M.Node<K>, ST.nd(K, nl, i), ST.nd(K, nl2, i), agr_head(~K, ~cmp, ~o, i, ST.ids(r), nl, nl2, hr))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, _, ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl2), ST.rep(~K, r, i, nl2)))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, l, i, nl2), ST.rep(~K, l, i, nl), rep_agr(~K, ~cmp, ~o, l, i, nl, nl2, agr_l(~K, ~cmp, ~o, ST.ids(l), Con{i, ST.ids(r)}, nl, nl2, h))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(_, ST.rep(~K, r, i, nl2)))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      %Equal.sym(Bool, ST.rep(~K, r, i, nl2), ST.rep(~K, r, i, nl), rep_agr(~K, ~cmp, ~o, r, i, nl, nl2, L.and_right(ndeq(~K, ~cmp, ST.nd(K, nl, i), ST.nd(K, nl2, i)), agr(~K, ~cmp, ST.ids(r), nl, nl2), hr))) : {Bool.and(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl), _))) == ST.rep(~K, ST.TN{i, l, r}, p, nl) : Bool}
      {==}


def ctx_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +c: List<&2, P.Fr>, +x: Nat, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, SC.append(Nat, P.before(c), P.after(c)), nl, nl2) == True{} : Bool}) -> {P.ctxok(~K, c, x, nl2) == P.ctxok(~K, c, x, nl) : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{+p, +lft, +s}, +t}:
      match lft:
        case True{}:
          +h1 = agr_r(~K, ~cmp, ~o, P.before(t), Con{p, SC.append(Nat, ST.ids(s), P.after(t))}, nl, nl2, h)
          +hbt = agr_l(~K, ~cmp, ~o, P.before(t), Con{p, SC.append(Nat, ST.ids(s), P.after(t))}, nl, nl2, h)
          +h2 = L.and_right(ndeq(~K, ~cmp, ST.nd(K, nl, p), ST.nd(K, nl2, p)), agr(~K, ~cmp, SC.append(Nat, ST.ids(s), P.after(t)), nl, nl2), h1)
          +hs = agr_l(~K, ~cmp, ~o, ST.ids(s), P.after(t), nl, nl2, h2)
          +hat = agr_r(~K, ~cmp, ~o, ST.ids(s), P.after(t), nl, nl2, h2)
          %Equal.sym(M.Node<K>, ST.nd(K, nl2, p), ST.nd(K, nl, p), Equal.sym(M.Node<K>, ST.nd(K, nl, p), ST.nd(K, nl2, p), agr_head(~K, ~cmp, ~o, p, SC.append(Nat, ST.ids(s), P.after(t)), nl, nl2, h1))) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, _, x, ST.rid(s), P.top(t)), ST.rep(~K, s, p, nl2))), P.ctxok(~K, t, p, nl2)) == P.ctxok(~K, Con{P.FR{p, True{}, s}, t}, x, nl) : Bool}
          %Equal.sym(Bool, ST.rep(~K, s, p, nl2), ST.rep(~K, s, p, nl), rep_agr(~K, ~cmp, ~o, s, p, nl, nl2, hs)) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), x, ST.rid(s), P.top(t)), _)), P.ctxok(~K, t, p, nl2)) == P.ctxok(~K, Con{P.FR{p, True{}, s}, t}, x, nl) : Bool}
          %Equal.sym(Bool, P.ctxok(~K, t, p, nl2), P.ctxok(~K, t, p, nl), ctx_agr(~K, ~cmp, ~o, t, p, nl, nl2, agr_app(~K, ~cmp, ~o, P.before(t), P.after(t), nl, nl2, hbt, hat))) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), x, ST.rid(s), P.top(t)), ST.rep(~K, s, p, nl))), _) == P.ctxok(~K, Con{P.FR{p, True{}, s}, t}, x, nl) : Bool}
          {==}
        case False{}:
          +h1 = agr_l(~K, ~cmp, ~o, SC.append(Nat, P.before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}})), P.after(t), nl, nl2, h)
          +hat = agr_r(~K, ~cmp, ~o, SC.append(Nat, P.before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}})), P.after(t), nl, nl2, h)
          +hbt = agr_l(~K, ~cmp, ~o, P.before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}}), nl, nl2, h1)
          +h2 = agr_r(~K, ~cmp, ~o, P.before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}}), nl, nl2, h1)
          +hs = agr_l(~K, ~cmp, ~o, ST.ids(s), Con{p, Nil{}}, nl, nl2, h2)
          +hp = agr_r(~K, ~cmp, ~o, ST.ids(s), Con{p, Nil{}}, nl, nl2, h2)
          %Equal.sym(M.Node<K>, ST.nd(K, nl2, p), ST.nd(K, nl, p), Equal.sym(M.Node<K>, ST.nd(K, nl, p), ST.nd(K, nl2, p), agr_head(~K, ~cmp, ~o, p, Nil{}, nl, nl2, hp))) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, _, ST.rid(s), x, P.top(t)), ST.rep(~K, s, p, nl2))), P.ctxok(~K, t, p, nl2)) == P.ctxok(~K, Con{P.FR{p, False{}, s}, t}, x, nl) : Bool}
          %Equal.sym(Bool, ST.rep(~K, s, p, nl2), ST.rep(~K, s, p, nl), rep_agr(~K, ~cmp, ~o, s, p, nl, nl2, hs)) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), x, P.top(t)), _)), P.ctxok(~K, t, p, nl2)) == P.ctxok(~K, Con{P.FR{p, False{}, s}, t}, x, nl) : Bool}
          %Equal.sym(Bool, P.ctxok(~K, t, p, nl2), P.ctxok(~K, t, p, nl), ctx_agr(~K, ~cmp, ~o, t, p, nl, nl2, agr_app(~K, ~cmp, ~o, P.before(t), P.after(t), nl, nl2, hbt, hat))) : {Bool.and(Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(s), x, P.top(t)), ST.rep(~K, s, p, nl))), _) == P.ctxok(~K, Con{P.FR{p, False{}, s}, t}, x, nl) : Bool}
          {==}


def ents_agr(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +h: {agr(~K, ~cmp, xs, nl, nl2) == True{} : Bool}) -> {ST.ents(~K, ~V, xs, nl2, pl) == ST.ents(~K, ~V, xs, nl, pl) : List<&2, M.Entry<K, V>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, nl2, j), ST.nd(K, nl, j), Equal.sym(M.Node<K>, ST.nd(K, nl, j), ST.nd(K, nl2, j), agr_head(~K, ~cmp, ~o, j, t, nl, nl2, h))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, _, ST.pv(V, pl, j)), ST.ents(~K, ~V, t, nl2, pl)) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      %Equal.sym(List<&2, M.Entry<K, V>>, ST.ents(~K, ~V, t, nl2, pl), ST.ents(~K, ~V, t, nl, pl), ents_agr(~K, ~V, ~cmp, ~o, t, nl, nl2, pl, L.and_right(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, nl2, j)), agr(~K, ~cmp, t, nl, nl2), h))) : {ST.cons_m(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j)), _) == ST.ents(~K, ~V, Con{j, t}, nl, pl) : List<&2, M.Entry<K, V>>}
      {==}

def oks_agr(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +h: {agr(~K, ~cmp, xs, nl, nl2) == True{} : Bool}) -> {EN.oks(~K, ~V, xs, nl2, pl) == EN.oks(~K, ~V, xs, nl, pl) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, nl2, j), ST.nd(K, nl, j), Equal.sym(M.Node<K>, ST.nd(K, nl, j), ST.nd(K, nl2, j), agr_head(~K, ~cmp, ~o, j, t, nl, nl2, h))) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, _, ST.pv(V, pl, j))), EN.oks(~K, ~V, t, nl2, pl)) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      %Equal.sym(Bool, EN.oks(~K, ~V, t, nl2, pl), EN.oks(~K, ~V, t, nl, pl), oks_agr(~K, ~V, ~cmp, ~o, t, nl, nl2, pl, L.and_right(ndeq(~K, ~cmp, ST.nd(K, nl, j), ST.nd(K, nl2, j)), agr(~K, ~cmp, t, nl, nl2), h))) : {Bool.and(S.is_some(M.Entry<K, V>, ST.ent(K, V, ST.nd(K, nl, j), ST.pv(V, pl, j))), _) == EN.oks(~K, ~V, Con{j, t}, nl, pl) : Bool}
      {==}

def fll_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +fl: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +h: {agr(~K, ~cmp, fl, nl, nl2) == True{} : Bool}) -> {ST.fll(~K, nl2, fl) == ST.fll(~K, nl, fl) : Bool}:
  match fl:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      %Equal.sym(M.Node<K>, ST.nd(K, nl2, f), ST.nd(K, nl, f), Equal.sym(M.Node<K>, ST.nd(K, nl, f), ST.nd(K, nl2, f), agr_head(~K, ~cmp, ~o, f, t, nl, nl2, h))) : {Bool.and(ST.is_free(K, _, ST.fst0(t)), ST.fll(~K, nl2, t)) == ST.fll(~K, nl, Con{f, t}) : Bool}
      %Equal.sym(Bool, ST.fll(~K, nl2, t), ST.fll(~K, nl, t), fll_agr(~K, ~cmp, ~o, t, nl, nl2, L.and_right(ndeq(~K, ~cmp, ST.nd(K, nl, f), ST.nd(K, nl2, f)), agr(~K, ~cmp, t, nl, nl2), h))) : {Bool.and(ST.is_free(K, ST.nd(K, nl, f), ST.fst0(t)), _) == ST.fll(~K, nl, Con{f, t}) : Bool}
      {==}
