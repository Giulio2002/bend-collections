import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./mirror.bend as MI
import ./tree.bend as TR
import ./path.bend as P
import ../../lib/nat_list.bend as NL

# The neighbour walk: from a node the path leads to, the next id in key
# order (forward) is the first of its right subtree's and the ids after it,
# the previous the last of the ids before it and its left subtree's. The
# walk descends to the extreme of a child, or ascends while it came from the
# other side. (source: tools/generators/tm_hand/nbr.src)


# ---- ends of lists ----

def last0_snoc(+z: List<&2, Nat>, +p: Nat) -> {ST.last0(SC.append(Nat, z, Con{p, Nil{}})) == p : Nat}:
  match z:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{+y, +u}:
          last0_snoc(Con{y, u}, p)

def last0_end(+x: List<&2, Nat>, +y: List<&2, Nat>, +p: Nat) -> {ST.last0(SC.append(Nat, x, SC.append(Nat, y, Con{p, Nil{}}))) == p : Nat}:
  %Equal.sym(List<&2, Nat>, SC.append(Nat, x, SC.append(Nat, y, Con{p, Nil{}})), SC.append(Nat, SC.append(Nat, x, y), Con{p, Nil{}}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, x, y), Con{p, Nil{}}), SC.append(Nat, x, SC.append(Nat, y, Con{p, Nil{}})), LL.append_assoc(Nat, x, y, Con{p, Nil{}}))) : {ST.last0(_) == p : Nat}
  last0_snoc(SC.append(Nat, x, y), p)

def last0_tail(+x: List<&2, Nat>, +y: Nat, +w: List<&2, Nat>) -> {ST.last0(SC.append(Nat, x, Con{y, w})) == ST.last0(Con{y, w}) : Nat}:
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{+h2, +u}:
          last0_tail(Con{h2, u}, y, w)

def last0_drop(+y: Nat, +a: List<&2, Nat>, +z: Nat, +b: List<&2, Nat>) -> {ST.last0(Con{y, SC.append(Nat, a, Con{z, b})}) == ST.last0(SC.append(Nat, a, Con{z, b})) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

# the last of x, y, and a node's ids is the node's last
def last0_sub(+x: List<&2, Nat>, +y: Nat, +j: Nat, +a: ST.Tr, +b: ST.Tr) -> {ST.last0(SC.append(Nat, x, Con{y, ST.ids(ST.TN{j, a, b})})) == ST.last0(ST.ids(ST.TN{j, a, b})) : Nat}:
  %Equal.sym(Nat, ST.last0(SC.append(Nat, x, Con{y, ST.ids(ST.TN{j, a, b})})), ST.last0(Con{y, ST.ids(ST.TN{j, a, b})}), last0_tail(x, y, ST.ids(ST.TN{j, a, b}))) : {_ == ST.last0(ST.ids(ST.TN{j, a, b})) : Nat}
  last0_drop(y, ST.ids(a), j, ST.ids(b))

def fst0_app(+a: List<&2, Nat>, +z: Nat, +b: List<&2, Nat>, +x: List<&2, Nat>) -> {ST.fst0(SC.append(Nat, SC.append(Nat, a, Con{z, b}), x)) == ST.fst0(SC.append(Nat, a, Con{z, b})) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      {==}

# ---- a node's links ----

def match_pk(+fw: Bool, +b: Nat, +a: Nat) -> {M.pick(Nat, fw, b, a) == ST.pk(Nat, fw, b, a) : Nat}:
  match fw:
    case True{}:
      {==}
    case False{}:
      {==}


def child_eq(~K: Data, +x: M.Node<K>, +a: Nat, +b: Nat, +p: Nat, +fw: Bool, +hx: {ST.is_node(K, x, a, b, p) == True{} : Bool}) -> {M.child(~K, x, fw) == ST.pk(Nat, fw, b, a) : Nat}:
  match x:
    case M.Free{f}:
      Empty.absurd({M.child(~K, M.Free{f}, fw) == ST.pk(Nat, fw, b, a) : Nat}, L.false_true(hx))
    case M.N{c, +x1, +x2, +x3, key}:
      +ea = N.eq_from_is_eq(x1, a, L.and_left(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, p)), hx))
      +eb = N.eq_from_is_eq(x2, b, L.and_left(Nat.is_eq(x2, b), Nat.is_eq(x3, p), L.and_right(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, p)), hx)))
      %Equal.sym(Nat, x1, a, ea) : {M.pick(Nat, fw, x2, _) == ST.pk(Nat, fw, b, a) : Nat}
      %Equal.sym(Nat, x2, b, eb) : {M.pick(Nat, fw, _, a) == ST.pk(Nat, fw, b, a) : Nat}
      match_pk(fw, b, a)


def parent_eq(~K: Data, +x: M.Node<K>, +a: Nat, +b: Nat, +p: Nat, +hx: {ST.is_node(K, x, a, b, p) == True{} : Bool}) -> {M.node_parent(~K, x) == p : Nat}:
  match x:
    case M.Free{f}:
      Empty.absurd({M.node_parent(~K, M.Free{f}) == p : Nat}, L.false_true(hx))
    case M.N{c, +x1, +x2, +x3, key}:
      N.eq_from_is_eq(x3, p, L.and_right(Nat.is_eq(x2, b), Nat.is_eq(x3, p), L.and_right(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, p)), hx)))

# ---- the extreme of a subtree ----


# forward: the last id of the subtree, backward: the first
def ext_r(~K: Data, +nl: List<&2, M.Node<K>>, +g: Nat, +j: Nat, +ua: ST.Tr, +ub: ST.Tr, +p: Nat, +hr: {ST.rep(~K, ST.TN{j, ua, ub}, p, nl) == True{} : Bool}, +hf: {Nat.is_lt(TR.ht(ST.TN{j, ua, ub}), g) == True{} : Bool}) -> {MI.ext_loop(~K, g, nl, True{}, j, M.child(~K, ST.nd(K, nl, j), True{})) == ST.last0(ST.ids(ST.TN{j, ua, ub})) : Nat}:
  match g ub:
    case 0n +ub:
      Empty.absurd({MI.ext_loop(~K, 0n, nl, True{}, j, M.child(~K, ST.nd(K, nl, j), True{})) == ST.pk(Nat, True{}, ST.last0(ST.ids(ST.TN{j, ua, ub})), ST.fst0(ST.ids(ST.TN{j, ua, ub}))) : Nat}, L.true_not_false(Nat.is_lt(TR.ht(ST.TN{j, ua, ub}), 0n), hf, N.not_lt_zero(TR.ht(ST.TN{j, ua, ub}))))
    case 1n+g2 ST.TE{}:
      %Equal.sym(Nat, M.child(~K, ST.nd(K, nl, j), True{}), ST.pk(Nat, True{}, 0n, ST.rid(ua)), child_eq(~K, ST.nd(K, nl, j), ST.rid(ua), 0n, p, True{}, TR.rep_node(~K, j, ua, ST.TE{}, p, nl, hr))) : {MI.ext_loop(~K, 1n+g2, nl, True{}, j, _) == ST.pk(Nat, True{}, ST.last0(ST.ids(ST.TN{j, ua, ST.TE{}})), ST.fst0(ST.ids(ST.TN{j, ua, ST.TE{}}))) : Nat}
      %Equal.sym(Nat, ST.last0(SC.append(Nat, ST.ids(ua), Con{j, Nil{}})), j, last0_snoc(ST.ids(ua), j)) : {j == _ : Nat}
      {==}
    case 1n+g2 ST.TN{+j2, +a, +b}:
      match j2:
        case 0n:
          Empty.absurd({MI.ext_loop(~K, 1n+g2, nl, True{}, j, M.child(~K, ST.nd(K, nl, j), True{})) == ST.pk(Nat, True{}, ST.last0(ST.ids(ST.TN{j, ua, ST.TN{0n, a, b}})), ST.fst0(ST.ids(ST.TN{j, ua, ST.TN{0n, a, b}}))) : Nat}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.rid(a), ST.rid(b), j), Bool.and(ST.rep(~K, a, 0n, nl), ST.rep(~K, b, 0n, nl))), TR.rep_r(~K, j, ua, ST.TN{0n, a, b}, p, nl, hr))))
        case 1n+j3:
          +ih = ext_r(~K, nl, g2, 1n+j3, a, b, j, TR.rep_r(~K, j, ua, ST.TN{1n+j3, a, b}, p, nl, hr), TR.ht_r(j, ua, ST.TN{1n+j3, a, b}, g2, hf))
          %Equal.sym(Nat, M.child(~K, ST.nd(K, nl, j), True{}), ST.pk(Nat, True{}, 1n+j3, ST.rid(ua)), child_eq(~K, ST.nd(K, nl, j), ST.rid(ua), 1n+j3, p, True{}, TR.rep_node(~K, j, ua, ST.TN{1n+j3, a, b}, p, nl, hr))) : {MI.ext_loop(~K, 1n+g2, nl, True{}, j, _) == ST.pk(Nat, True{}, ST.last0(ST.ids(ST.TN{j, ua, ST.TN{1n+j3, a, b}})), ST.fst0(ST.ids(ST.TN{j, ua, ST.TN{1n+j3, a, b}}))) : Nat}
          %Equal.sym(Nat, ST.last0(SC.append(Nat, ST.ids(ua), Con{j, ST.ids(ST.TN{1n+j3, a, b})})), ST.last0(ST.ids(ST.TN{1n+j3, a, b})), last0_sub(ST.ids(ua), j, 1n+j3, a, b)) : {MI.ext_loop(~K, g2, nl, True{}, 1n+j3, M.child(~K, ST.nd(K, nl, 1n+j3), True{})) == _ : Nat}
          ih

def ext_l(~K: Data, +nl: List<&2, M.Node<K>>, +g: Nat, +j: Nat, +ua: ST.Tr, +ub: ST.Tr, +p: Nat, +hr: {ST.rep(~K, ST.TN{j, ua, ub}, p, nl) == True{} : Bool}, +hf: {Nat.is_lt(TR.ht(ST.TN{j, ua, ub}), g) == True{} : Bool}) -> {MI.ext_loop(~K, g, nl, False{}, j, M.child(~K, ST.nd(K, nl, j), False{})) == ST.fst0(ST.ids(ST.TN{j, ua, ub})) : Nat}:
  match g ua:
    case 0n +ua:
      Empty.absurd({MI.ext_loop(~K, 0n, nl, False{}, j, M.child(~K, ST.nd(K, nl, j), False{})) == ST.pk(Nat, False{}, ST.last0(ST.ids(ST.TN{j, ua, ub})), ST.fst0(ST.ids(ST.TN{j, ua, ub}))) : Nat}, L.true_not_false(Nat.is_lt(TR.ht(ST.TN{j, ua, ub}), 0n), hf, N.not_lt_zero(TR.ht(ST.TN{j, ua, ub}))))
    case 1n+g2 ST.TE{}:
      %Equal.sym(Nat, M.child(~K, ST.nd(K, nl, j), False{}), ST.pk(Nat, False{}, ST.rid(ub), 0n), child_eq(~K, ST.nd(K, nl, j), 0n, ST.rid(ub), p, False{}, TR.rep_node(~K, j, ST.TE{}, ub, p, nl, hr))) : {MI.ext_loop(~K, 1n+g2, nl, False{}, j, _) == ST.pk(Nat, False{}, ST.last0(ST.ids(ST.TN{j, ST.TE{}, ub})), ST.fst0(ST.ids(ST.TN{j, ST.TE{}, ub}))) : Nat}
      {==}
    case 1n+g2 ST.TN{+j2, +a, +b}:
      match j2:
        case 0n:
          Empty.absurd({MI.ext_loop(~K, 1n+g2, nl, False{}, j, M.child(~K, ST.nd(K, nl, j), False{})) == ST.pk(Nat, False{}, ST.last0(ST.ids(ST.TN{j, ST.TN{0n, a, b}, ub})), ST.fst0(ST.ids(ST.TN{j, ST.TN{0n, a, b}, ub}))) : Nat}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.rid(a), ST.rid(b), j), Bool.and(ST.rep(~K, a, 0n, nl), ST.rep(~K, b, 0n, nl))), TR.rep_l(~K, j, ST.TN{0n, a, b}, ub, p, nl, hr))))
        case 1n+j3:
          +ih = ext_l(~K, nl, g2, 1n+j3, a, b, j, TR.rep_l(~K, j, ST.TN{1n+j3, a, b}, ub, p, nl, hr), TR.ht_l(j, ST.TN{1n+j3, a, b}, ub, g2, hf))
          %Equal.sym(Nat, M.child(~K, ST.nd(K, nl, j), False{}), ST.pk(Nat, False{}, ST.rid(ub), 1n+j3), child_eq(~K, ST.nd(K, nl, j), 1n+j3, ST.rid(ub), p, False{}, TR.rep_node(~K, j, ST.TN{1n+j3, a, b}, ub, p, nl, hr))) : {MI.ext_loop(~K, 1n+g2, nl, False{}, j, _) == ST.pk(Nat, False{}, ST.last0(ST.ids(ST.TN{j, ST.TN{1n+j3, a, b}, ub})), ST.fst0(ST.ids(ST.TN{j, ST.TN{1n+j3, a, b}, ub}))) : Nat}
          %Equal.sym(Nat, ST.fst0(SC.append(Nat, ST.ids(ST.TN{1n+j3, a, b}), Con{j, ST.ids(ub)})), ST.fst0(ST.ids(ST.TN{1n+j3, a, b})), fst0_app(ST.ids(a), 1n+j3, ST.ids(b), Con{j, ST.ids(ub)})) : {MI.ext_loop(~K, g2, nl, False{}, 1n+j3, M.child(~K, ST.nd(K, nl, 1n+j3), False{})) == _ : Nat}
          ih


# ---- the ascent ----


def pk_same(+fw: Bool, +a: Nat) -> {ST.pk(Nat, fw, a, a) == a : Nat}:
  match fw:
    case True{}:
      {==}
    case False{}:
      {==}

def done_loop(-K: Data, +nl: List<&2, M.Node<K>>, +g: Nat, +fw: Bool, +p: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {MI.asc_loop(K, g, nl, fw, M.Ascend{0n, p, True{}}) == p : Nat}:
  match g:
    case 0n:
      Empty.absurd({MI.asc_loop(K, 0n, nl, fw, M.Ascend{0n, p, True{}}) == p : Nat}, L.false_true(hg))
    case 1n+h:
      {==}

def not_eq_f(+x: Nat, +y: Nat, +h: {Bool.not(Nat.is_eq(x, y)) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  NL.not_t_f(Nat.is_eq(x, y), h)


def asc_node(-K: Data, +nl: List<&2, M.Node<K>>, +t: List<&2, P.Fr>, +p: Nat, +lft: Bool, +s: ST.Tr, +x: Nat, +g: Nat, +fw: Bool, +a: Nat, +b: Nat, +q: Nat, +ea: {a == ST.pk(Nat, lft, x, ST.rid(s)) : Nat}, +eb: {b == ST.pk(Nat, lft, ST.rid(s), x) : Nat}, +eq: {q == P.top(t) : Nat}, +hne: {Bool.not(Nat.is_eq(x, ST.rid(s))) == True{} : Bool}, +hg: {Nat.is_lt(SC.length(P.Fr, t), g) == True{} : Bool}, +ih: {MI.asc_loop(K, g, nl, fw, M.Ascend{p, P.top(t), False{}}) == ST.pk(Nat, fw, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}) -> {MI.asc_loop(K, g, nl, fw, M.ascend_choice(p, p, q, Nat.is_eq(x, M.pick(Nat, fw, a, b)))) == ST.pk(Nat, fw, ST.fst0(P.after(Con{P.FR{p, lft, s}, t})), ST.last0(P.before(Con{P.FR{p, lft, s}, t}))) : Nat}:
  match lft fw:
    case True{} True{}:
      %Equal.sym(Nat, a, x, ea) : {MI.asc_loop(K, g, nl, True{}, M.ascend_choice(p, p, q, Nat.is_eq(x, _))) == p : Nat}
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, N.is_eq_refl(x)) : {MI.asc_loop(K, g, nl, True{}, M.ascend_choice(p, p, q, _)) == p : Nat}
      done_loop(K, nl, g, True{}, p, N.le_lt_trans(0n, SC.length(P.Fr, t), g, N.zero_le(SC.length(P.Fr, t)), hg))
    case False{} False{}:
      %Equal.sym(Nat, b, x, eb) : {MI.asc_loop(K, g, nl, False{}, M.ascend_choice(p, p, q, Nat.is_eq(x, _))) == ST.pk(Nat, False{}, ST.fst0(P.after(Con{P.FR{p, False{}, s}, t})), ST.last0(P.before(Con{P.FR{p, False{}, s}, t}))) : Nat}
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, N.is_eq_refl(x)) : {MI.asc_loop(K, g, nl, False{}, M.ascend_choice(p, p, q, _)) == ST.pk(Nat, False{}, ST.fst0(P.after(Con{P.FR{p, False{}, s}, t})), ST.last0(P.before(Con{P.FR{p, False{}, s}, t}))) : Nat}
      %Equal.sym(Nat, ST.last0(SC.append(Nat, P.before(t), SC.append(Nat, ST.ids(s), Con{p, Nil{}}))), p, last0_end(P.before(t), ST.ids(s), p)) : {MI.asc_loop(K, g, nl, False{}, M.Ascend{0n, p, True{}}) == _ : Nat}
      done_loop(K, nl, g, False{}, p, N.le_lt_trans(0n, SC.length(P.Fr, t), g, N.zero_le(SC.length(P.Fr, t)), hg))
    case True{} False{}:
      %Equal.sym(Nat, b, ST.rid(s), eb) : {MI.asc_loop(K, g, nl, False{}, M.ascend_choice(p, p, q, Nat.is_eq(x, _))) == ST.pk(Nat, False{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      %Equal.sym(Bool, Nat.is_eq(x, ST.rid(s)), False{}, not_eq_f(x, ST.rid(s), hne)) : {MI.asc_loop(K, g, nl, False{}, M.ascend_choice(p, p, q, _)) == ST.pk(Nat, False{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      %Equal.sym(Nat, q, P.top(t), eq) : {MI.asc_loop(K, g, nl, False{}, M.Ascend{p, _, False{}}) == ST.pk(Nat, False{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      ih
    case False{} True{}:
      %Equal.sym(Nat, a, ST.rid(s), ea) : {MI.asc_loop(K, g, nl, True{}, M.ascend_choice(p, p, q, Nat.is_eq(x, _))) == ST.pk(Nat, True{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      %Equal.sym(Bool, Nat.is_eq(x, ST.rid(s)), False{}, not_eq_f(x, ST.rid(s), hne)) : {MI.asc_loop(K, g, nl, True{}, M.ascend_choice(p, p, q, _)) == ST.pk(Nat, True{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      %Equal.sym(Nat, q, P.top(t), eq) : {MI.asc_loop(K, g, nl, True{}, M.Ascend{p, _, False{}}) == ST.pk(Nat, True{}, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}
      ih

def asc_frame(-K: Data, +nl: List<&2, M.Node<K>>, +t: List<&2, P.Fr>, +p: Nat, +lft: Bool, +s: ST.Tr, +x: Nat, +g: Nat, +fw: Bool, +y: M.Node<K>, +hy: {ST.is_node(K, y, ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(t)) == True{} : Bool}, +hne: {Bool.not(Nat.is_eq(x, ST.rid(s))) == True{} : Bool}, +hg: {Nat.is_lt(SC.length(P.Fr, t), g) == True{} : Bool}, +ih: {MI.asc_loop(K, g, nl, fw, M.Ascend{p, P.top(t), False{}}) == ST.pk(Nat, fw, ST.fst0(P.after(t)), ST.last0(P.before(t))) : Nat}) -> {MI.asc_loop(K, g, nl, fw, MI.asc_step(K, x, p, fw, y)) == ST.pk(Nat, fw, ST.fst0(P.after(Con{P.FR{p, lft, s}, t})), ST.last0(P.before(Con{P.FR{p, lft, s}, t}))) : Nat}:
  match y:
    case M.Free{f}:
      Empty.absurd({MI.asc_loop(K, g, nl, fw, MI.asc_step(K, x, p, fw, M.Free{f})) == ST.pk(Nat, fw, ST.fst0(P.after(Con{P.FR{p, lft, s}, t})), ST.last0(P.before(Con{P.FR{p, lft, s}, t}))) : Nat}, L.false_true(hy))
    case M.N{c, +a, +b, +q, key}:
      +h1 = L.and_left(Nat.is_eq(a, ST.pk(Nat, lft, x, ST.rid(s))), Bool.and(Nat.is_eq(b, ST.pk(Nat, lft, ST.rid(s), x)), Nat.is_eq(q, P.top(t))), hy)
      +h23 = L.and_right(Nat.is_eq(a, ST.pk(Nat, lft, x, ST.rid(s))), Bool.and(Nat.is_eq(b, ST.pk(Nat, lft, ST.rid(s), x)), Nat.is_eq(q, P.top(t))), hy)
      +h2 = L.and_left(Nat.is_eq(b, ST.pk(Nat, lft, ST.rid(s), x)), Nat.is_eq(q, P.top(t)), h23)
      +h3 = L.and_right(Nat.is_eq(b, ST.pk(Nat, lft, ST.rid(s), x)), Nat.is_eq(q, P.top(t)), h23)
      asc_node(K, nl, t, p, lft, s, x, g, fw, a, b, q, N.eq_from_is_eq(a, ST.pk(Nat, lft, x, ST.rid(s)), h1), N.eq_from_is_eq(b, ST.pk(Nat, lft, ST.rid(s), x), h2), N.eq_from_is_eq(q, P.top(t), h3), hne, hg, ih)

# ascending from x, the path's parent: forward the first id after, backward
# the last id before
def asc(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +g: Nat, +fw: Bool, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hd: {P.dist(c, x) == True{} : Bool}, +hf: {Nat.is_lt(SC.length(P.Fr, c), g) == True{} : Bool}) -> {MI.asc_loop(K, g, nl, fw, M.Ascend{x, P.top(c), False{}}) == ST.pk(Nat, fw, ST.fst0(P.after(c)), ST.last0(P.before(c))) : Nat}:
  match c g:
    case Nil{} 0n:
      Empty.absurd({MI.asc_loop(K, 0n, nl, fw, M.Ascend{x, 0n, False{}}) == ST.pk(Nat, fw, ST.fst0(P.after(Nil{})), ST.last0(P.before(Nil{}))) : Nat}, L.false_true(hf))
    case Nil{} 1n+g2:
      match g2:
        case 0n:
          %Equal.sym(Nat, ST.pk(Nat, fw, 0n, 0n), 0n, pk_same(fw, 0n)) : {0n == _ : Nat}
          {==}
        case 1n+g3:
          %Equal.sym(Nat, ST.pk(Nat, fw, 0n, 0n), 0n, pk_same(fw, 0n)) : {0n == _ : Nat}
          {==}
    case Con{P.FR{+p, +lft, +s}, +t} 0n:
      Empty.absurd({MI.asc_loop(K, 0n, nl, fw, M.Ascend{x, p, False{}}) == ST.pk(Nat, fw, ST.fst0(P.after(Con{P.FR{p, lft, s}, t})), ST.last0(P.before(Con{P.FR{p, lft, s}, t}))) : Nat}, L.false_true(hf))
    case Con{P.FR{+p, +lft, +s}, +t} 1n+g2:
      +hk = L.and_left(P.cok1(~K, P.FR{p, lft, s}, x, P.top(t), nl), P.ctxok(~K, t, p, nl), hok)
      +hk2 = L.and_right(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(t)), ST.rep(~K, s, p, nl)), hk)
      +hy = L.and_left(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(t)), ST.rep(~K, s, p, nl), hk2)
      +hne = L.and_left(Bool.not(Nat.is_eq(x, ST.rid(s))), P.dist(t, p), hd)
      +ih = asc(~K, nl, t, p, g2, fw, L.and_right(P.cok1(~K, P.FR{p, lft, s}, x, P.top(t), nl), P.ctxok(~K, t, p, nl), hok), L.and_right(Bool.not(Nat.is_eq(x, ST.rid(s))), P.dist(t, p), hd), hf)
      asc_frame(K, nl, t, p, lft, s, x, g2, fw, ST.nd(K, nl, p), hy, hne, hf, ih)

# ---- the neighbour ----


def sub_len(+b: List<&2, Nat>, +x: List<&2, Nat>, +a: List<&2, Nat>) -> {Nat.is_le(SC.length(Nat, x), SC.length(Nat, SC.append(Nat, b, SC.append(Nat, x, a)))) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(Nat, SC.append(Nat, b, SC.append(Nat, x, a))), Nat.add(SC.length(Nat, b), SC.length(Nat, SC.append(Nat, x, a))), LL.length_append(Nat, b, SC.append(Nat, x, a))) : {Nat.is_le(SC.length(Nat, x), _) == True{} : Bool}
  %Equal.sym(Nat, SC.length(Nat, SC.append(Nat, x, a)), Nat.add(SC.length(Nat, x), SC.length(Nat, a)), LL.length_append(Nat, x, a)) : {Nat.is_le(SC.length(Nat, x), Nat.add(SC.length(Nat, b), _)) == True{} : Bool}
  N.le_trans(SC.length(Nat, x), Nat.add(SC.length(Nat, x), SC.length(Nat, a)), Nat.add(SC.length(Nat, b), Nat.add(SC.length(Nat, x), SC.length(Nat, a))), N.le_add_right(SC.length(Nat, x), SC.length(Nat, a)), TR.le_add_l(SC.length(Nat, b), Nat.add(SC.length(Nat, x), SC.length(Nat, a))))

# n is the length of the split ids
def n_wh(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}) -> {n == SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) : Nat}:
  %Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), ST.ids(tg), Equal.sym(List<&2, Nat>, ST.ids(tg), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))), hid)) : {n == SC.length(Nat, _) : Nat}
  hn

def asc_fuel(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}) -> {Nat.is_lt(SC.length(P.Fr, c), 1n+n) == True{} : Bool}:
  +le = N.le_trans(SC.length(P.Fr, c), SC.length(Nat, SC.append(Nat, P.before(c), P.after(c))), SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), P.depth(c), P.ins_le(P.before(c), ST.ids(ST.TN{i, l, r}), P.after(c)))
  N.le_lt_succ(SC.length(P.Fr, c), n, L.subst(Nat, z => {Nat.is_le(SC.length(P.Fr, c), z) == True{} : Bool}, SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), n, Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), n_wh(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn)), le))

def ht_fuel(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}) -> {Nat.is_lt(TR.ht(ST.TN{i, l, r}), 1n+n) == True{} : Bool}:
  +le = N.le_trans(TR.ht(ST.TN{i, l, r}), SC.length(Nat, ST.ids(ST.TN{i, l, r})), SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), TR.ht_le(ST.TN{i, l, r}), sub_len(P.before(c), ST.ids(ST.TN{i, l, r}), P.after(c)))
  N.le_lt_succ(TR.ht(ST.TN{i, l, r}), n, L.subst(Nat, z => {Nat.is_le(TR.ht(ST.TN{i, l, r}), z) == True{} : Bool}, SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), n, Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))), n_wh(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn)), le))

def lt_step(+a: Nat, +n: Nat, +h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.is_lt(a, 1n+n) == True{} : Bool}:
  N.lt_trans(a, n, 1n+n, h, N.lt_succ(n))


def last0_app2(+x: List<&2, Nat>, +a: List<&2, Nat>, +z: Nat, +b: List<&2, Nat>) -> {ST.last0(SC.append(Nat, x, SC.append(Nat, a, Con{z, b}))) == ST.last0(SC.append(Nat, a, Con{z, b})) : Nat}:
  %Equal.sym(List<&2, Nat>, SC.append(Nat, x, SC.append(Nat, a, Con{z, b})), SC.append(Nat, SC.append(Nat, x, a), Con{z, b}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, x, a), Con{z, b}), SC.append(Nat, x, SC.append(Nat, a, Con{z, b})), LL.append_assoc(Nat, x, a, Con{z, b}))) : {ST.last0(_) == ST.last0(SC.append(Nat, a, Con{z, b})) : Nat}
  %Equal.sym(Nat, ST.last0(SC.append(Nat, SC.append(Nat, x, a), Con{z, b})), ST.last0(Con{z, b}), last0_tail(SC.append(Nat, x, a), z, b)) : {_ == ST.last0(SC.append(Nat, a, Con{z, b})) : Nat}
  Equal.sym(Nat, ST.last0(SC.append(Nat, a, Con{z, b})), ST.last0(Con{z, b}), last0_tail(a, z, b))

# forward: the first id of the right subtree, or the first after the node
def nbs_f(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}) -> {MI.nbs(~K, nl, n, i, P.top(c), True{}, ST.pk(Nat, True{}, ST.rid(r), ST.rid(l))) == ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))) : Nat}:
  match r:
    case ST.TE{}:
      asc(~K, nl, c, i, 1n+n, True{}, hok, P.nd_dist(~K, nl, c, i, l, ST.TE{}, L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), P.top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr), hok, hnd), asc_fuel(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn))
    case ST.TN{+j, +a, +b}:
      match j:
        case 0n:
          Empty.absurd({MI.nbs(~K, nl, n, i, P.top(c), True{}, 0n) == ST.fst0(SC.append(Nat, ST.ids(ST.TN{0n, a, b}), P.after(c))) : Nat}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.rid(a), ST.rid(b), i), Bool.and(ST.rep(~K, a, 0n, nl), ST.rep(~K, b, 0n, nl))), TR.rep_r(~K, i, l, ST.TN{0n, a, b}, P.top(c), nl, hr))))
        case 1n+j3:
          %Equal.sym(Nat, ST.fst0(SC.append(Nat, SC.append(Nat, ST.ids(a), Con{1n+j3, ST.ids(b)}), P.after(c))), ST.fst0(SC.append(Nat, ST.ids(a), Con{1n+j3, ST.ids(b)})), fst0_app(ST.ids(a), 1n+j3, ST.ids(b), P.after(c))) : {MI.nbs(~K, nl, n, i, P.top(c), True{}, 1n+j3) == _ : Nat}
          ext_l(~K, nl, 1n+n, 1n+j3, a, b, i, TR.rep_r(~K, i, l, ST.TN{1n+j3, a, b}, P.top(c), nl, hr), lt_step(TR.ht(ST.TN{1n+j3, a, b}), n, TR.ht_r(i, l, ST.TN{1n+j3, a, b}, n, ht_fuel(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, ST.TN{1n+j3, a, b}, hr, hok, hnd, hid, hn))))

# backward: the last id of the left subtree, or the last before the node
def nbs_b(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}) -> {MI.nbs(~K, nl, n, i, P.top(c), False{}, ST.pk(Nat, False{}, ST.rid(r), ST.rid(l))) == ST.last0(SC.append(Nat, P.before(c), ST.ids(l))) : Nat}:
  match l:
    case ST.TE{}:
      %Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), Nil{}), P.before(c), LL.append_nil(Nat, P.before(c))) : {MI.nbs(~K, nl, n, i, P.top(c), False{}, 0n) == ST.last0(_) : Nat}
      asc(~K, nl, c, i, 1n+n, False{}, hok, P.nd_dist(~K, nl, c, i, ST.TE{}, r, L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), P.top(c)), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr), hok, hnd), asc_fuel(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn))
    case ST.TN{+j, +a, +b}:
      match j:
        case 0n:
          Empty.absurd({MI.nbs(~K, nl, n, i, P.top(c), False{}, 0n) == ST.last0(SC.append(Nat, P.before(c), ST.ids(ST.TN{0n, a, b}))) : Nat}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.rid(a), ST.rid(b), i), Bool.and(ST.rep(~K, a, 0n, nl), ST.rep(~K, b, 0n, nl))), TR.rep_l(~K, i, ST.TN{0n, a, b}, r, P.top(c), nl, hr))))
        case 1n+j3:
          %Equal.sym(Nat, ST.last0(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(a), Con{1n+j3, ST.ids(b)}))), ST.last0(SC.append(Nat, ST.ids(a), Con{1n+j3, ST.ids(b)})), last0_app2(P.before(c), ST.ids(a), 1n+j3, ST.ids(b))) : {MI.nbs(~K, nl, n, i, P.top(c), False{}, 1n+j3) == _ : Nat}
          ext_r(~K, nl, 1n+n, 1n+j3, a, b, i, TR.rep_l(~K, i, ST.TN{1n+j3, a, b}, r, P.top(c), nl, hr), lt_step(TR.ht(ST.TN{1n+j3, a, b}), n, TR.ht_l(i, ST.TN{1n+j3, a, b}, r, n, ht_fuel(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, ST.TN{1n+j3, a, b}, r, hr, hok, hnd, hid, hn))))


def nbs_fw(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}, +fw: Bool) -> {MI.nbs(~K, nl, n, i, P.top(c), fw, ST.pk(Nat, fw, ST.rid(r), ST.rid(l))) == ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))) : Nat}:
  match fw:
    case True{}:
      nbs_f(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn)
    case False{}:
      nbs_b(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn)

# the neighbour of a node the path leads to
def neighbor_m(~K: Data, ~V: Data, ~cmp: K -> K -> Cmp, +n: Nat, +root: Nat, +lo: Nat, +hi: Nat, +free: Nat, +l0: Nat, +d0: Nat, +nl: List<&2, M.Node<K>>, +pl: List<&2, Maybe<&2, V>>, +tg: ST.Tr, +fl: List<&2, Nat>, +c: List<&2, P.Fr>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +hr: {ST.rep(~K, ST.TN{i, l, r}, P.top(c), nl) == True{} : Bool}, +hok: {P.ctxok(~K, c, i, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c)))) == True{} : Bool}, +hid: {ST.ids(tg) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{i, l, r}), P.after(c))) : List<&2, Nat>}, +hn: {n == SC.length(Nat, ST.ids(tg)) : Nat}, +fw: Bool) -> {MI.neighbor(~K, ~V, ~cmp, ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, i, fw) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}:
  %Equal.sym(Nat, M.node_parent(~K, ST.nd(K, nl, i)), P.top(c), parent_eq(~K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), P.top(c), TR.rep_node(~K, i, l, r, P.top(c), nl, hr))) : {(ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, MI.nbs(~K, nl, n, i, _, fw, M.child(~K, ST.nd(K, nl, i), fw))) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}
  %Equal.sym(Nat, M.child(~K, ST.nd(K, nl, i), fw), ST.pk(Nat, fw, ST.rid(r), ST.rid(l)), child_eq(~K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), P.top(c), fw, TR.rep_node(~K, i, l, r, P.top(c), nl, hr))) : {(ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, MI.nbs(~K, nl, n, i, P.top(c), fw, _)) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}
  %Equal.sym(Nat, MI.nbs(~K, nl, n, i, P.top(c), fw, ST.pk(Nat, fw, ST.rid(r), ST.rid(l))), ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l)))), nbs_fw(~K, ~V, ~cmp, n, root, lo, hi, free, l0, d0, nl, pl, tg, fl, c, i, l, r, hr, hok, hnd, hid, hn, fw)) : {(ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, _) == (ST.SH{n, root, lo, hi, free, l0, d0, nl, pl, tg, fl}, ST.pk(Nat, fw, ST.fst0(SC.append(Nat, ST.ids(r), P.after(c))), ST.last0(SC.append(Nat, P.before(c), ST.ids(l))))) : ST.Sh<K, V> & Nat}
  {==}
