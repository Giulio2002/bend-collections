import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ./state.bend as ST
import ./tree.bend as TR

# Paths into the ghost tree: the frames from a subtree up to the root (the
# parent's id, whether the subtree is its left child, the sibling), the ids
# before and after the subtree in key order, and the links each frame's
# parent has. A descent extends the path; the ids split around the subtree;
# with no repeated ids a subtree's root differs from every sibling's; the
# path is shorter than the ids. (source: tools/generators/tm_hand/path.src)


type Fr is Data:
  FR{p: Nat, lft: Bool, sib: ST.Tr}


def fp(f: Fr) -> Nat:
  match f:
    case FR{+p, lft, s}:
      p

def top(c: List<&2, Fr>) -> Nat:
  match c:
    case Nil{}:
      0n
    case Con{+f, t}:
      fp(f)

def bef1(f: Fr, +b: List<&2, Nat>) -> List<&2, Nat>:
  match f:
    case FR{+p, lft, s}:
      match lft:
        case True{}:
          b
        case False{}:
          SC.append(Nat, b, SC.append(Nat, ST.ids(s), Con{p, Nil{}}))

def aft1(f: Fr, +a: List<&2, Nat>) -> List<&2, Nat>:
  match f:
    case FR{+p, lft, s}:
      match lft:
        case True{}:
          Con{p, SC.append(Nat, ST.ids(s), a)}
        case False{}:
          a

# the ids before and after the subtree the path leads to
def before(c: List<&2, Fr>) -> List<&2, Nat>:
  match c:
    case Nil{}:
      Nil{}
    case Con{+f, t}:
      bef1(f, before(t))

def after(c: List<&2, Fr>) -> List<&2, Nat>:
  match c:
    case Nil{}:
      Nil{}
    case Con{+f, t}:
      aft1(f, after(t))

# a frame's parent links to x on its side, to the sibling on the other, and
# to q above; the sibling hangs below it
def cok1(~K: Data, f: Fr, +x: Nat, +q: Nat, +nl: List<&2, M.Node<K>>) -> Bool:
  match f:
    case FR{+p, +lft, +s}:
      Bool.and(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), q), ST.rep(~K, s, p, nl)))

def ctxok(~K: Data, c: List<&2, Fr>, +x: Nat, +nl: List<&2, M.Node<K>>) -> Bool:
  match c:
    case Nil{}:
      True{}
    case Con{+f, +t}:
      Bool.and(cok1(~K, f, x, top(t), nl), ctxok(~K, t, fp(f), nl))


# ---- the ids around a descent ----

def eq_l(+b: List<&2, Nat>, +a: List<&2, Nat>, +i: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>) -> {SC.append(Nat, b, SC.append(Nat, SC.append(Nat, x, Con{i, y}), a)) == SC.append(Nat, b, SC.append(Nat, x, Con{i, SC.append(Nat, y, a)})) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, x, Con{i, y}), a), SC.append(Nat, x, SC.append(Nat, Con{i, y}, a)), LL.append_assoc(Nat, x, Con{i, y}, a)) : {SC.append(Nat, b, _) == SC.append(Nat, b, SC.append(Nat, x, Con{i, SC.append(Nat, y, a)})) : List<&2, Nat>}
  {==}

def eq_r(+b: List<&2, Nat>, +a: List<&2, Nat>, +i: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>) -> {SC.append(Nat, b, SC.append(Nat, SC.append(Nat, x, Con{i, y}), a)) == SC.append(Nat, SC.append(Nat, b, SC.append(Nat, x, Con{i, Nil{}})), SC.append(Nat, y, a)) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, b, SC.append(Nat, x, Con{i, Nil{}})), SC.append(Nat, y, a)), SC.append(Nat, b, SC.append(Nat, SC.append(Nat, x, Con{i, Nil{}}), SC.append(Nat, y, a))), LL.append_assoc(Nat, b, SC.append(Nat, x, Con{i, Nil{}}), SC.append(Nat, y, a))) : {SC.append(Nat, b, SC.append(Nat, SC.append(Nat, x, Con{i, y}), a)) == _ : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, x, Con{i, Nil{}}), SC.append(Nat, y, a)), SC.append(Nat, x, SC.append(Nat, Con{i, Nil{}}, SC.append(Nat, y, a))), LL.append_assoc(Nat, x, Con{i, Nil{}}, SC.append(Nat, y, a))) : {SC.append(Nat, b, SC.append(Nat, SC.append(Nat, x, Con{i, y}), a)) == SC.append(Nat, b, _) : List<&2, Nat>}
  eq_l(b, a, i, x, y)


# the ids, split around a subtree, split around its left child
def ids_l(+c: List<&2, Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr) -> {SC.append(Nat, before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(c))) == SC.append(Nat, before(Con{FR{i, True{}, r}, c}), SC.append(Nat, ST.ids(l), after(Con{FR{i, True{}, r}, c}))) : List<&2, Nat>}:
  eq_l(before(c), after(c), i, ST.ids(l), ST.ids(r))

def ids_r(+c: List<&2, Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr) -> {SC.append(Nat, before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(c))) == SC.append(Nat, before(Con{FR{i, False{}, l}, c}), SC.append(Nat, ST.ids(r), after(Con{FR{i, False{}, l}, c}))) : List<&2, Nat>}:
  eq_r(before(c), after(c), i, ST.ids(l), ST.ids(r))

# the links along a descent
def ok_l(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, top(c), nl) == True{} : Bool}, +hc: {ctxok(~K, c, i, nl) == True{} : Bool}) -> {ctxok(~K, Con{FR{i, True{}, r}, c}, ST.rid(l), nl) == True{} : Bool} & {ST.rep(~K, l, i, nl) == True{} : Bool}:
  +h2 = L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr)
  +h3 = L.and_right(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl)), h2)
  +k1 = L.and_intro(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), ST.rep(~K, r, i, nl)), L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr), L.and_intro(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), ST.rep(~K, r, i, nl), L.and_left(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl)), h2), L.and_right(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl), h3)))
  (L.and_intro(cok1(~K, FR{i, True{}, r}, ST.rid(l), top(c), nl), ctxok(~K, c, i, nl), k1, hc), L.and_left(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl), h3))

def ok_r(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, top(c), nl) == True{} : Bool}, +hc: {ctxok(~K, c, i, nl) == True{} : Bool}) -> {ctxok(~K, Con{FR{i, False{}, l}, c}, ST.rid(r), nl) == True{} : Bool} & {ST.rep(~K, r, i, nl) == True{} : Bool}:
  +h2 = L.and_right(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr)
  +h3 = L.and_right(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl)), h2)
  +k1 = L.and_intro(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), ST.rep(~K, l, i, nl)), L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr), L.and_intro(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), ST.rep(~K, l, i, nl), L.and_left(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl)), h2), L.and_left(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl), h3)))
  (L.and_intro(cok1(~K, FR{i, False{}, l}, ST.rid(r), top(c), nl), ctxok(~K, c, i, nl), k1, hc), L.and_right(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl), h3))

# ---- siblings differ ----

# the subtree's root is none of the frames' siblings (walking up)
def dist(c: List<&2, Fr>, +x: Nat) -> Bool:
  match c:
    case Nil{}:
      True{}
    case Con{+f, +t}:
      match f:
        case FR{+p, lft, +s}:
          Bool.and(Bool.not(Nat.is_eq(x, ST.rid(s))), dist(t, p))


def mem_self(+i: Nat, +y: List<&2, Nat>) -> {HT.memn(i, Con{i, y}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(i, i), True{}, N.is_eq_refl(i)) : {Bool.or(_, HT.memn(i, y)) == True{} : Bool}
  {==}

def mem_root(+i: Nat, +l: ST.Tr, +r: ST.Tr) -> {HT.memn(i, ST.ids(ST.TN{i, l, r})) == True{} : Bool}:
  LS.mem_app_r(i, ST.ids(l), Con{i, ST.ids(r)}, mem_self(i, ST.ids(r)))

def mem_cons(+y: Nat, +p: Nat, +xs: List<&2, Nat>, +h: {HT.memn(y, xs) == True{} : Bool}) -> {HT.memn(y, Con{p, xs}) == True{} : Bool}:
  %Equal.sym(Bool, HT.memn(y, xs), True{}, h) : {Bool.or(Nat.is_eq(p, y), _) == True{} : Bool}
  LS.or_true_b(Nat.is_eq(p, y))

def ne_c(+i: Nat, +j: Nat, +xs: List<&2, Nat>, +hi: {HT.memn(i, xs) == False{} : Bool}, +hj: {HT.memn(j, xs) == True{} : Bool}, +b: Bool, +hb: {Nat.is_eq(i, j) == b : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      +e = N.eq_from_is_eq(i, j, hb)
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, HT.memn(i, xs), False{}, Equal.sym(Bool, HT.memn(i, xs), True{}, L.subst(Nat, z => {HT.memn(z, xs) == True{} : Bool}, j, i, Equal.sym(Nat, i, j, e), hj)), hi)))
    case False{}:
      {==}

# an absent id differs from a present one
def ne_mem(+i: Nat, +j: Nat, +xs: List<&2, Nat>, +hi: {HT.memn(i, xs) == False{} : Bool}, +hj: {HT.memn(j, xs) == True{} : Bool}) -> {Bool.not(Nat.is_eq(i, j)) == True{} : Bool}:
  ne_c(i, j, xs, hi, hj, Nat.is_eq(i, j), {==})

def ne_zero(+i: Nat, +hi: {Nat.is_lt(0n, i) == True{} : Bool}) -> {Bool.not(Nat.is_eq(i, 0n)) == True{} : Bool}:
  match i:
    case 0n:
      Empty.absurd({Bool.not(Nat.is_eq(0n, 0n)) == True{} : Bool}, L.false_true(hi))
    case 1n+j:
      {==}


# the root differs from every sibling, when no id repeats
def nd_dist(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hi: {Nat.is_lt(0n, i) == True{} : Bool}, +hok: {ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {LST.nodupn(SC.append(Nat, before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(c)))) == True{} : Bool}) -> {dist(c, i) == True{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      match f:
        case FR{+p, +lft, +s}:
          match lft:
            case True{}:
              match s:
                case ST.TE{}:
                  +hk = L.and_left(cok1(~K, FR{p, True{}, ST.TE{}}, i, top(t), nl), ctxok(~K, t, p, nl), hok)
                  +hp = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), i, ST.rid(ST.TE{}), top(t)), ST.rep(~K, ST.TE{}, p, nl)), hk)
                  +hn = LS.nd_dj2(ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TE{}}, t}), LS.nd_r(before(t), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TE{}}, t})), hnd), i, mem_root(i, l, r))
                  +hnd2 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, before(Con{FR{p, True{}, ST.TE{}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TE{}}, t}))), SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{i, l, r}, ST.TE{}}), after(t))), Equal.sym(List<&2, Nat>, SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{i, l, r}, ST.TE{}}), after(t))), SC.append(Nat, before(Con{FR{p, True{}, ST.TE{}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TE{}}, t}))), ids_l(t, p, ST.TN{i, l, r}, ST.TE{})), hnd)
                  +rec = nd_dist(~K, nl, t, p, ST.TN{i, l, r}, ST.TE{}, hp, L.and_right(cok1(~K, FR{p, True{}, ST.TE{}}, i, top(t), nl), ctxok(~K, t, p, nl), hok), hnd2)
                  L.and_intro(Bool.not(Nat.is_eq(i, 0n)), dist(t, p), ne_zero(i, hi), rec)
                case ST.TN{+j, +sl, +sr}:
                  +hk = L.and_left(cok1(~K, FR{p, True{}, ST.TN{j, sl, sr}}, i, top(t), nl), ctxok(~K, t, p, nl), hok)
                  +hp = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), i, ST.rid(ST.TN{j, sl, sr}), top(t)), ST.rep(~K, ST.TN{j, sl, sr}, p, nl)), hk)
                  +hn = LS.nd_dj2(ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}), LS.nd_r(before(t), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t})), hnd), i, mem_root(i, l, r))
                  +hnd2 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, before(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}))), SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{i, l, r}, ST.TN{j, sl, sr}}), after(t))), Equal.sym(List<&2, Nat>, SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{i, l, r}, ST.TN{j, sl, sr}}), after(t))), SC.append(Nat, before(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}))), ids_l(t, p, ST.TN{i, l, r}, ST.TN{j, sl, sr})), hnd)
                  +rec = nd_dist(~K, nl, t, p, ST.TN{i, l, r}, ST.TN{j, sl, sr}, hp, L.and_right(cok1(~K, FR{p, True{}, ST.TN{j, sl, sr}}, i, top(t), nl), ctxok(~K, t, p, nl), hok), hnd2)
                  L.and_intro(Bool.not(Nat.is_eq(i, j)), dist(t, p), ne_mem(i, j, after(Con{FR{p, True{}, ST.TN{j, sl, sr}}, t}), hn, mem_cons(j, p, SC.append(Nat, ST.ids(ST.TN{j, sl, sr}), after(t)), LS.mem_app_l(j, ST.ids(ST.TN{j, sl, sr}), after(t), mem_root(j, sl, sr)))), rec)
            case False{}:
              match s:
                case ST.TE{}:
                  +hk = L.and_left(cok1(~K, FR{p, False{}, ST.TE{}}, i, top(t), nl), ctxok(~K, t, p, nl), hok)
                  +hp = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(ST.TE{}), i, top(t)), ST.rep(~K, ST.TE{}, p, nl)), hk)
                  +hn = LS.nd_dj(before(Con{FR{p, False{}, ST.TE{}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(t)), hnd, i, LS.mem_app_l(i, ST.ids(ST.TN{i, l, r}), after(t), mem_root(i, l, r)))
                  +hnd2 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, before(Con{FR{p, False{}, ST.TE{}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, False{}, ST.TE{}}, t}))), SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TE{}, ST.TN{i, l, r}}), after(t))), Equal.sym(List<&2, Nat>, SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TE{}, ST.TN{i, l, r}}), after(t))), SC.append(Nat, before(Con{FR{p, False{}, ST.TE{}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, False{}, ST.TE{}}, t}))), ids_r(t, p, ST.TE{}, ST.TN{i, l, r})), hnd)
                  +rec = nd_dist(~K, nl, t, p, ST.TE{}, ST.TN{i, l, r}, hp, L.and_right(cok1(~K, FR{p, False{}, ST.TE{}}, i, top(t), nl), ctxok(~K, t, p, nl), hok), hnd2)
                  L.and_intro(Bool.not(Nat.is_eq(i, 0n)), dist(t, p), ne_zero(i, hi), rec)
                case ST.TN{+j, +sl, +sr}:
                  +hk = L.and_left(cok1(~K, FR{p, False{}, ST.TN{j, sl, sr}}, i, top(t), nl), ctxok(~K, t, p, nl), hok)
                  +hp = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.rid(ST.TN{j, sl, sr}), i, top(t)), ST.rep(~K, ST.TN{j, sl, sr}, p, nl)), hk)
                  +hn = LS.nd_dj(before(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(t)), hnd, i, LS.mem_app_l(i, ST.ids(ST.TN{i, l, r}), after(t), mem_root(i, l, r)))
                  +hnd2 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, before(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}))), SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{j, sl, sr}, ST.TN{i, l, r}}), after(t))), Equal.sym(List<&2, Nat>, SC.append(Nat, before(t), SC.append(Nat, ST.ids(ST.TN{p, ST.TN{j, sl, sr}, ST.TN{i, l, r}}), after(t))), SC.append(Nat, before(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}), SC.append(Nat, ST.ids(ST.TN{i, l, r}), after(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}))), ids_r(t, p, ST.TN{j, sl, sr}, ST.TN{i, l, r})), hnd)
                  +rec = nd_dist(~K, nl, t, p, ST.TN{j, sl, sr}, ST.TN{i, l, r}, hp, L.and_right(cok1(~K, FR{p, False{}, ST.TN{j, sl, sr}}, i, top(t), nl), ctxok(~K, t, p, nl), hok), hnd2)
                  L.and_intro(Bool.not(Nat.is_eq(i, j)), dist(t, p), ne_mem(i, j, before(Con{FR{p, False{}, ST.TN{j, sl, sr}}, t}), hn, LS.mem_app_r(j, before(t), SC.append(Nat, ST.ids(ST.TN{j, sl, sr}), Con{p, Nil{}}), LS.mem_app_l(j, ST.ids(ST.TN{j, sl, sr}), Con{p, Nil{}}, mem_root(j, sl, sr)))), rec)

# ---- the path is shorter than the ids ----


def cons_len(+x: List<&2, Nat>, +p: Nat, +y: List<&2, Nat>) -> {SC.length(Nat, SC.append(Nat, x, Con{p, y})) == 1n+SC.length(Nat, SC.append(Nat, x, y)) : Nat}:
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, SC.length(Nat, SC.append(Nat, t, Con{p, y})), 1n+SC.length(Nat, SC.append(Nat, t, y)), cons_len(t, p, y)) : {1n+_ == 1n+1n+SC.length(Nat, SC.append(Nat, t, y)) : Nat}
      {==}

def ins_le(+x: List<&2, Nat>, +z: List<&2, Nat>, +y: List<&2, Nat>) -> {Nat.is_le(SC.length(Nat, SC.append(Nat, x, y)), SC.length(Nat, SC.append(Nat, x, SC.append(Nat, z, y)))) == True{} : Bool}:
  match x:
    case Nil{}:
      %Equal.sym(Nat, SC.length(Nat, SC.append(Nat, z, y)), Nat.add(SC.length(Nat, z), SC.length(Nat, y)), LL.length_append(Nat, z, y)) : {Nat.is_le(SC.length(Nat, y), _) == True{} : Bool}
      TR.le_add_l(SC.length(Nat, z), SC.length(Nat, y))
    case Con{+h, +t}:
      ins_le(t, z, y)

def depth(+c: List<&2, Fr>) -> {Nat.is_le(SC.length(Fr, c), SC.length(Nat, SC.append(Nat, before(c), after(c)))) == True{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      match f:
        case FR{+p, +lft, +s}:
          match lft:
            case True{}:
              %Equal.sym(Nat, SC.length(Nat, SC.append(Nat, before(t), Con{p, SC.append(Nat, ST.ids(s), after(t))})), 1n+SC.length(Nat, SC.append(Nat, before(t), SC.append(Nat, ST.ids(s), after(t)))), cons_len(before(t), p, SC.append(Nat, ST.ids(s), after(t)))) : {Nat.is_le(1n+SC.length(Fr, t), _) == True{} : Bool}
              N.le_trans(SC.length(Fr, t), SC.length(Nat, SC.append(Nat, before(t), after(t))), SC.length(Nat, SC.append(Nat, before(t), SC.append(Nat, ST.ids(s), after(t)))), depth(t), ins_le(before(t), ST.ids(s), after(t)))
            case False{}:
              %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}})), after(t)), SC.append(Nat, before(t), SC.append(Nat, SC.append(Nat, ST.ids(s), Con{p, Nil{}}), after(t))), LL.append_assoc(Nat, before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}}), after(t))) : {Nat.is_le(1n+SC.length(Fr, t), SC.length(Nat, _)) == True{} : Bool}
              %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, ST.ids(s), Con{p, Nil{}}), after(t)), SC.append(Nat, ST.ids(s), Con{p, after(t)}), LL.append_assoc(Nat, ST.ids(s), Con{p, Nil{}}, after(t))) : {Nat.is_le(1n+SC.length(Fr, t), SC.length(Nat, SC.append(Nat, before(t), _))) == True{} : Bool}
              +x = L.subst(Nat, z => {Nat.is_le(1n+SC.length(Fr, t), z) == True{} : Bool}, 1n+SC.length(Nat, SC.append(Nat, before(t), after(t))), SC.length(Nat, SC.append(Nat, before(t), Con{p, after(t)})), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, before(t), Con{p, after(t)})), 1n+SC.length(Nat, SC.append(Nat, before(t), after(t))), cons_len(before(t), p, after(t))), depth(t))
              N.le_trans(1n+SC.length(Fr, t), SC.length(Nat, SC.append(Nat, before(t), Con{p, after(t)})), SC.length(Nat, SC.append(Nat, before(t), SC.append(Nat, ST.ids(s), Con{p, after(t)}))), x, ins_le(before(t), ST.ids(s), Con{p, after(t)}))
