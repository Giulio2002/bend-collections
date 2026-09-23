import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./setters.bend as SE
import ./rotm.bend as RM
import ../lib/order.bend as O
import ./agree.bend as AG
import ../lib/nat_list.bend as NL

# Nodes through a sequence of setters: a setter skips other ids and applies
# its field change to its own; a node's links after field changes.
# (source: tools/generators/tm_hand/rotn.src)


def skipl(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.nd(K, SE.setl(K, nl, id, v), j) == ST.nd(K, nl, j) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setl(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), SE.modl(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), SE.ndl(K, nl, id, v, j)) : {_ == ST.nd(K, nl, j) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, j), False{}, h) : {ST.pk(M.Node<K>, _, SE.modl(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) == ST.nd(K, nl, j) : M.Node<K>}
  {==}

def hitl(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.nd(K, SE.setl(K, nl, id, v), id) == SE.modl(K, ST.nd(K, nl, id), v) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setl(K, nl, id, v), id), ST.pk(M.Node<K>, Nat.is_eq(id, id), SE.modl(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)), SE.ndl(K, nl, id, v, id)) : {_ == SE.modl(K, ST.nd(K, nl, id), v) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, N.is_eq_refl(id)) : {ST.pk(M.Node<K>, _, SE.modl(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)) == SE.modl(K, ST.nd(K, nl, id), v) : M.Node<K>}
  {==}

def skipr(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.nd(K, SE.setr(K, nl, id, v), j) == ST.nd(K, nl, j) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setr(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), SE.modr(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), SE.ndr(K, nl, id, v, j)) : {_ == ST.nd(K, nl, j) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, j), False{}, h) : {ST.pk(M.Node<K>, _, SE.modr(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) == ST.nd(K, nl, j) : M.Node<K>}
  {==}

def hitr(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.nd(K, SE.setr(K, nl, id, v), id) == SE.modr(K, ST.nd(K, nl, id), v) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setr(K, nl, id, v), id), ST.pk(M.Node<K>, Nat.is_eq(id, id), SE.modr(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)), SE.ndr(K, nl, id, v, id)) : {_ == SE.modr(K, ST.nd(K, nl, id), v) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, N.is_eq_refl(id)) : {ST.pk(M.Node<K>, _, SE.modr(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)) == SE.modr(K, ST.nd(K, nl, id), v) : M.Node<K>}
  {==}

def skipp(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.nd(K, SE.setp(K, nl, id, v), j) == ST.nd(K, nl, j) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), SE.modp(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), SE.ndp(K, nl, id, v, j)) : {_ == ST.nd(K, nl, j) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, j), False{}, h) : {ST.pk(M.Node<K>, _, SE.modp(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) == ST.nd(K, nl, j) : M.Node<K>}
  {==}

def hitp(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Nat) -> {ST.nd(K, SE.setp(K, nl, id, v), id) == SE.modp(K, ST.nd(K, nl, id), v) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, nl, id, v), id), ST.pk(M.Node<K>, Nat.is_eq(id, id), SE.modp(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)), SE.ndp(K, nl, id, v, id)) : {_ == SE.modp(K, ST.nd(K, nl, id), v) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, N.is_eq_refl(id)) : {ST.pk(M.Node<K>, _, SE.modp(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)) == SE.modp(K, ST.nd(K, nl, id), v) : M.Node<K>}
  {==}

def skipc(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool, +j: Nat, +h: {Nat.is_eq(id, j) == False{} : Bool}) -> {ST.nd(K, SE.setc(K, nl, id, v), j) == ST.nd(K, nl, j) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setc(K, nl, id, v), j), ST.pk(M.Node<K>, Nat.is_eq(id, j), SE.modc(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)), SE.ndc(K, nl, id, v, j)) : {_ == ST.nd(K, nl, j) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, j), False{}, h) : {ST.pk(M.Node<K>, _, SE.modc(K, ST.nd(K, nl, j), v), ST.nd(K, nl, j)) == ST.nd(K, nl, j) : M.Node<K>}
  {==}

def hitc(-K: Data, +nl: List<&2, M.Node<K>>, +id: Nat, +v: Bool) -> {ST.nd(K, SE.setc(K, nl, id, v), id) == SE.modc(K, ST.nd(K, nl, id), v) : M.Node<K>}:
  %Equal.sym(M.Node<K>, ST.nd(K, SE.setc(K, nl, id, v), id), ST.pk(M.Node<K>, Nat.is_eq(id, id), SE.modc(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)), SE.ndc(K, nl, id, v, id)) : {_ == SE.modc(K, ST.nd(K, nl, id), v) : M.Node<K>}
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, N.is_eq_refl(id)) : {ST.pk(M.Node<K>, _, SE.modc(K, ST.nd(K, nl, id), v), ST.nd(K, nl, id)) == SE.modc(K, ST.nd(K, nl, id), v) : M.Node<K>}
  {==}

def skipa(-K: Data, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool, +j: Nat, +h: {Nat.is_eq(q, j) == False{} : Bool}) -> {ST.nd(K, RM.attn(K, nl, q, y, dir), j) == ST.nd(K, nl, j) : M.Node<K>}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+i True{}:
      skipl(K, nl, 1n+i, y, j, h)
    case 1n+i False{}:
      skipr(K, nl, 1n+i, y, j, h)

# the parent's node after attach: the child on its side
def moda(-K: Data, x: M.Node<K>, +y: Nat, +dir: Bool) -> M.Node<K>:
  match dir:
    case True{}:
      SE.modl(K, x, y)
    case False{}:
      SE.modr(K, x, y)

def hita(-K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +y: Nat, +dir: Bool) -> {ST.nd(K, RM.attn(K, nl, 1n+i, y, dir), 1n+i) == moda(K, ST.nd(K, nl, 1n+i), y, dir) : M.Node<K>}:
  match dir:
    case True{}:
      hitl(K, nl, 1n+i, y)
    case False{}:
      hitr(K, nl, 1n+i, y)

# ---- links after field changes ----


def isn_pr(-K: Data, +x: M.Node<K>, +a: Nat, +b0: Nat, +q0: Nat, +b: Nat, +p: Nat, +h: {ST.is_node(K, x, a, b0, q0) == True{} : Bool}) -> {ST.is_node(K, SE.modp(K, SE.modr(K, x, b), p), a, b, p) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({ST.is_node(K, SE.modp(K, SE.modr(K, M.Free{f}, b), p), a, b, p) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k}:
      L.and_intro(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(b, b), Nat.is_eq(p, p)), L.and_left(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b0), Nat.is_eq(x3, q0)), h), L.and_intro(Nat.is_eq(b, b), Nat.is_eq(p, p), N.is_eq_refl(b), N.is_eq_refl(p)))

def isn_pl(-K: Data, +x: M.Node<K>, +a0: Nat, +b: Nat, +q0: Nat, +a: Nat, +p: Nat, +h: {ST.is_node(K, x, a0, b, q0) == True{} : Bool}) -> {ST.is_node(K, SE.modp(K, SE.modl(K, x, a), p), a, b, p) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({ST.is_node(K, SE.modp(K, SE.modl(K, M.Free{f}, a), p), a, b, p) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k}:
      L.and_intro(Nat.is_eq(a, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(p, p)), N.is_eq_refl(a), L.and_intro(Nat.is_eq(x2, b), Nat.is_eq(p, p), L.and_left(Nat.is_eq(x2, b), Nat.is_eq(x3, q0), L.and_right(Nat.is_eq(x1, a0), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q0)), h)), N.is_eq_refl(p)))

def isn_lp(-K: Data, +x: M.Node<K>, +a0: Nat, +b: Nat, +q0: Nat, +a: Nat, +p: Nat, +h: {ST.is_node(K, x, a0, b, q0) == True{} : Bool}) -> {ST.is_node(K, SE.modl(K, SE.modp(K, x, p), a), a, b, p) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({ST.is_node(K, SE.modl(K, SE.modp(K, M.Free{f}, p), a), a, b, p) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k}:
      L.and_intro(Nat.is_eq(a, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(p, p)), N.is_eq_refl(a), L.and_intro(Nat.is_eq(x2, b), Nat.is_eq(p, p), L.and_left(Nat.is_eq(x2, b), Nat.is_eq(x3, q0), L.and_right(Nat.is_eq(x1, a0), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q0)), h)), N.is_eq_refl(p)))

def isn_rp(-K: Data, +x: M.Node<K>, +a: Nat, +b0: Nat, +q0: Nat, +b: Nat, +p: Nat, +h: {ST.is_node(K, x, a, b0, q0) == True{} : Bool}) -> {ST.is_node(K, SE.modr(K, SE.modp(K, x, p), b), a, b, p) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({ST.is_node(K, SE.modr(K, SE.modp(K, M.Free{f}, p), b), a, b, p) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k}:
      L.and_intro(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(b, b), Nat.is_eq(p, p)), L.and_left(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b0), Nat.is_eq(x3, q0)), h), L.and_intro(Nat.is_eq(b, b), Nat.is_eq(p, p), N.is_eq_refl(b), N.is_eq_refl(p)))

def isn_p(-K: Data, +x: M.Node<K>, +a: Nat, +b: Nat, +q0: Nat, +p: Nat, +h: {ST.is_node(K, x, a, b, q0) == True{} : Bool}) -> {ST.is_node(K, SE.modp(K, x, p), a, b, p) == True{} : Bool}:
  match x:
    case M.Free{f}:
      Empty.absurd({ST.is_node(K, SE.modp(K, M.Free{f}, p), a, b, p) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k}:
      L.and_intro(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(p, p)), L.and_left(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q0)), h), L.and_intro(Nat.is_eq(x2, b), Nat.is_eq(p, p), L.and_left(Nat.is_eq(x2, b), Nat.is_eq(x3, q0), L.and_right(Nat.is_eq(x1, a), Bool.and(Nat.is_eq(x2, b), Nat.is_eq(x3, q0)), h)), N.is_eq_refl(p)))

# the parent's links with the child on the path's side replaced
def isn_a(-K: Data, +x: M.Node<K>, +lft: Bool, +c0: Nat, +s: Nat, +q: Nat, +y: Nat, +h: {ST.is_node(K, x, ST.pk(Nat, lft, c0, s), ST.pk(Nat, lft, s, c0), q) == True{} : Bool}) -> {ST.is_node(K, moda(K, x, y, lft), ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q) == True{} : Bool}:
  match x lft:
    case M.Free{f} +lft:
      Empty.absurd({ST.is_node(K, moda(K, M.Free{f}, y, lft), ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q) == True{} : Bool}, L.false_true(h))
    case M.N{c, +x1, +x2, +x3, k} True{}:
      L.and_intro(Nat.is_eq(y, y), Bool.and(Nat.is_eq(x2, s), Nat.is_eq(x3, q)), N.is_eq_refl(y), L.and_right(Nat.is_eq(x1, c0), Bool.and(Nat.is_eq(x2, s), Nat.is_eq(x3, q)), h))
    case M.N{c, +x1, +x2, +x3, k} False{}:
      L.and_intro(Nat.is_eq(x1, s), Bool.and(Nat.is_eq(y, y), Nat.is_eq(x3, q)), L.and_left(Nat.is_eq(x1, s), Bool.and(Nat.is_eq(x2, c0), Nat.is_eq(x3, q)), h), L.and_intro(Nat.is_eq(y, y), Nat.is_eq(x3, q), N.is_eq_refl(y), L.and_right(Nat.is_eq(x2, c0), Nat.is_eq(x3, q), L.and_right(Nat.is_eq(x1, s), Bool.and(Nat.is_eq(x2, c0), Nat.is_eq(x3, q)), h))))

# ---- agreement through the rotations' writes ----


def attn_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool, +hq: {NL.memn(q, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, RM.attn(K, nl, q, y, dir)) == True{} : Bool}:
  match q dir:
    case 0n +dir:
      AG.agr_refl(~K, ~cmp, ~o, xs, nl)
    case 1n+i True{}:
      SE.setl_agr(~K, ~cmp, ~o, xs, nl, 1n+i, y, hq)
    case 1n+i False{}:
      SE.setr_agr(~K, ~cmp, ~o, xs, nl, 1n+i, y, hq)


# ids the left rotation does not write keep their nodes
def rotl_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +hx: {NL.memn(x, xs) == False{} : Bool}, +hy: {NL.memn(y, xs) == False{} : Bool}, +hb: {NL.memn(b, xs) == False{} : Bool}, +hq: {NL.memn(q, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, RM.rotl_nl(K, nl, x, y, b, q, dir)) == True{} : Bool}:
  +a1 = SE.setr_agr(~K, ~cmp, ~o, xs, nl, x, b, hx)
  +a2 = SE.setp_agr(~K, ~cmp, ~o, xs, SE.setr(K, nl, x, b), b, x, hb)
  +a3 = attn_agr(~K, ~cmp, ~o, xs, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir, hq)
  +a4 = SE.setp_agr(~K, ~cmp, ~o, xs, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q, hy)
  +a5 = SE.setl_agr(~K, ~cmp, ~o, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x, hy)
  +a6 = SE.setp_agr(~K, ~cmp, ~o, xs, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, hx)
  AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), AG.agr_trans(~K, ~cmp, ~o, xs, nl, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setp(K, SE.setr(K, nl, x, b), b, x), RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setr(K, nl, x, b), SE.setp(K, SE.setr(K, nl, x, b), b, x), a1, a2), a3), a4), a5), a6)


def rotr_agr(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +hx: {NL.memn(x, xs) == False{} : Bool}, +hy: {NL.memn(y, xs) == False{} : Bool}, +hb: {NL.memn(b, xs) == False{} : Bool}, +hq: {NL.memn(q, xs) == False{} : Bool}) -> {AG.agr(~K, ~cmp, xs, nl, RM.rotr_nl(K, nl, x, y, b, q, dir)) == True{} : Bool}:
  +a1 = SE.setl_agr(~K, ~cmp, ~o, xs, nl, x, b, hx)
  +a2 = SE.setp_agr(~K, ~cmp, ~o, xs, SE.setl(K, nl, x, b), b, x, hb)
  +a3 = attn_agr(~K, ~cmp, ~o, xs, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir, hq)
  +a4 = SE.setp_agr(~K, ~cmp, ~o, xs, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q, hy)
  +a5 = SE.setr_agr(~K, ~cmp, ~o, xs, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x, hy)
  +a6 = SE.setp_agr(~K, ~cmp, ~o, xs, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, hx)
  AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), AG.agr_trans(~K, ~cmp, ~o, xs, nl, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setp(K, SE.setl(K, nl, x, b), b, x), RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), AG.agr_trans(~K, ~cmp, ~o, xs, nl, SE.setl(K, nl, x, b), SE.setp(K, SE.setl(K, nl, x, b), b, x), a1, a2), a3), a4), a5), a6)

# ---- the rotated nodes ----


# x: its right child b, its parent y
def rotl_x(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +a: Nat, +hxn: {ST.is_node(K, ST.nd(K, nl, x), a, y, q) == True{} : Bool}, +nyx: {Nat.is_eq(y, x) == False{} : Bool}, +nqx: {Nat.is_eq(q, x) == False{} : Bool}, +nbx: {Nat.is_eq(b, x) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, q, dir), x), a, b, y) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), SE.modp(K, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), y), SE.modp(K, SE.modr(K, ST.nd(K, nl, x), b), y), hitp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), y) == SE.modp(K, z, y) : M.Node<K>}, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), SE.modr(K, ST.nd(K, nl, x), b), Equal.trans(M.Node<K>, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), x), SE.modr(K, ST.nd(K, nl, x), b), skipl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x, x, nyx), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), x), ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), x), SE.modr(K, ST.nd(K, nl, x), b), skipp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q, x, nyx), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), x), ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), x), SE.modr(K, ST.nd(K, nl, x), b), skipa(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir, x, nqx), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), x), ST.nd(K, SE.setr(K, nl, x, b), x), SE.modr(K, ST.nd(K, nl, x), b), skipp(K, SE.setr(K, nl, x, b), b, x, x, nbx), hitr(K, nl, x, b))))), {==}))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, a, b, y) == True{} : Bool}, SE.modp(K, SE.modr(K, ST.nd(K, nl, x), b), y), ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), SE.modp(K, SE.modr(K, ST.nd(K, nl, x), b), y), e), isn_pr(K, ST.nd(K, nl, x), a, y, q, b, y, hxn))

# y: its left child x, its parent q
def rotl_y(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +cc: Nat, +hyn: {ST.is_node(K, ST.nd(K, nl, y), b, cc, x) == True{} : Bool}, +nxy: {Nat.is_eq(x, y) == False{} : Bool}, +nqy: {Nat.is_eq(q, y) == False{} : Bool}, +nby: {Nat.is_eq(b, y) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, q, dir), y), x, cc, q) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), y), SE.modl(K, SE.modp(K, ST.nd(K, nl, y), q), x), skipp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, y, nxy), Equal.trans(M.Node<K>, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), y), SE.modl(K, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y), x), SE.modl(K, SE.modp(K, ST.nd(K, nl, y), q), x), hitl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), L.subst(M.Node<K>, z => {SE.modl(K, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y), x) == SE.modl(K, z, x) : M.Node<K>}, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y), SE.modp(K, ST.nd(K, nl, y), q), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y), SE.modp(K, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y), q), SE.modp(K, ST.nd(K, nl, y), q), hitp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y), q) == SE.modp(K, z, q) : M.Node<K>}, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y), ST.nd(K, nl, y), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y), ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), y), ST.nd(K, nl, y), skipa(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir, y, nqy), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), y), ST.nd(K, SE.setr(K, nl, x, b), y), ST.nd(K, nl, y), skipp(K, SE.setr(K, nl, x, b), b, x, y, nby), skipr(K, nl, x, b, y, nxy))), {==})), {==})))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, x, cc, q) == True{} : Bool}, SE.modl(K, SE.modp(K, ST.nd(K, nl, y), q), x), ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), SE.modl(K, SE.modp(K, ST.nd(K, nl, y), q), x), e), isn_lp(K, ST.nd(K, nl, y), b, cc, x, x, q, hyn))

# b, the moved subtree's root: its parent x
def rotl_b(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +b1: Nat, +b2: Nat, +hbn: {ST.is_node(K, ST.nd(K, nl, b), b1, b2, y) == True{} : Bool}, +nxb: {Nat.is_eq(x, b) == False{} : Bool}, +nyb: {Nat.is_eq(y, b) == False{} : Bool}, +nqb: {Nat.is_eq(q, b) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, q, dir), b), b1, b2, x) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), b), SE.modp(K, ST.nd(K, nl, b), x), skipp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, b, nxb), Equal.trans(M.Node<K>, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), b), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), b), SE.modp(K, ST.nd(K, nl, b), x), skipl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x, b, nyb), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), b), ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), b), SE.modp(K, ST.nd(K, nl, b), x), skipp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q, b, nyb), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), b), ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), b), SE.modp(K, ST.nd(K, nl, b), x), skipa(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir, b, nqb), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), b), SE.modp(K, ST.nd(K, SE.setr(K, nl, x, b), b), x), SE.modp(K, ST.nd(K, nl, b), x), hitp(K, SE.setr(K, nl, x, b), b, x), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, SE.setr(K, nl, x, b), b), x) == SE.modp(K, z, x) : M.Node<K>}, ST.nd(K, SE.setr(K, nl, x, b), b), ST.nd(K, nl, b), skipr(K, nl, x, b, b, nxb), {==}))))))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, b1, b2, x) == True{} : Bool}, SE.modp(K, ST.nd(K, nl, b), x), ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), SE.modp(K, ST.nd(K, nl, b), x), e), isn_p(K, ST.nd(K, nl, b), b1, b2, y, x, hbn))

# q, the parent: y on the path's side
def rotl_q(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +i: Nat, +lft: Bool, +s: Nat, +q2: Nat, +hqn: {ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, s), ST.pk(Nat, lft, s, x), q2) == True{} : Bool}, +nxq: {Nat.is_eq(x, 1n+i) == False{} : Bool}, +nyq: {Nat.is_eq(y, 1n+i) == False{} : Bool}, +nbq: {Nat.is_eq(b, 1n+i) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q2) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), x, y), 1n+i), ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipp(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), x, y, 1n+i, nxq), Equal.trans(M.Node<K>, ST.nd(K, SE.setl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), 1n+i), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipl(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x, 1n+i, nyq), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), 1n+i), ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipp(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i, 1n+i, nyq), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i, y, lft), 1n+i), moda(K, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i), y, lft), moda(K, ST.nd(K, nl, 1n+i), y, lft), hita(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), i, y, lft), L.subst(M.Node<K>, z => {moda(K, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i), y, lft) == moda(K, z, y, lft) : M.Node<K>}, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i), ST.nd(K, nl, 1n+i), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, nl, x, b), b, x), 1n+i), ST.nd(K, SE.setr(K, nl, x, b), 1n+i), ST.nd(K, nl, 1n+i), skipp(K, SE.setr(K, nl, x, b), b, x, 1n+i, nbq), skipr(K, nl, x, b, 1n+i, nxq)), {==})))))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q2) == True{} : Bool}, moda(K, ST.nd(K, nl, 1n+i), y, lft), ST.nd(K, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), Equal.sym(M.Node<K>, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), e), isn_a(K, ST.nd(K, nl, 1n+i), lft, x, s, q2, y, hqn))

# ---- the right rotation's nodes ----

def rotr_x(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +cc: Nat, +hxn: {ST.is_node(K, ST.nd(K, nl, x), y, cc, q) == True{} : Bool}, +nyx: {Nat.is_eq(y, x) == False{} : Bool}, +nqx: {Nat.is_eq(q, x) == False{} : Bool}, +nbx: {Nat.is_eq(b, x) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, q, dir), x), b, cc, y) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), SE.modp(K, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), y), SE.modp(K, SE.modl(K, ST.nd(K, nl, x), b), y), hitp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), y) == SE.modp(K, z, y) : M.Node<K>}, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), SE.modl(K, ST.nd(K, nl, x), b), Equal.trans(M.Node<K>, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), x), SE.modl(K, ST.nd(K, nl, x), b), skipr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x, x, nyx), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), x), ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), x), SE.modl(K, ST.nd(K, nl, x), b), skipp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q, x, nyx), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), x), ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), x), SE.modl(K, ST.nd(K, nl, x), b), skipa(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir, x, nqx), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), x), ST.nd(K, SE.setl(K, nl, x, b), x), SE.modl(K, ST.nd(K, nl, x), b), skipp(K, SE.setl(K, nl, x, b), b, x, x, nbx), hitl(K, nl, x, b))))), {==}))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, b, cc, y) == True{} : Bool}, SE.modp(K, SE.modl(K, ST.nd(K, nl, x), b), y), ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), x), SE.modp(K, SE.modl(K, ST.nd(K, nl, x), b), y), e), isn_pl(K, ST.nd(K, nl, x), y, cc, q, b, y, hxn))

def rotr_y(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +aa: Nat, +hyn: {ST.is_node(K, ST.nd(K, nl, y), aa, b, x) == True{} : Bool}, +nxy: {Nat.is_eq(x, y) == False{} : Bool}, +nqy: {Nat.is_eq(q, y) == False{} : Bool}, +nby: {Nat.is_eq(b, y) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, q, dir), y), aa, x, q) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), y), SE.modr(K, SE.modp(K, ST.nd(K, nl, y), q), x), skipp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, y, nxy), Equal.trans(M.Node<K>, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), y), SE.modr(K, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y), x), SE.modr(K, SE.modp(K, ST.nd(K, nl, y), q), x), hitr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), L.subst(M.Node<K>, z => {SE.modr(K, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y), x) == SE.modr(K, z, x) : M.Node<K>}, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y), SE.modp(K, ST.nd(K, nl, y), q), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y), SE.modp(K, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y), q), SE.modp(K, ST.nd(K, nl, y), q), hitp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y), q) == SE.modp(K, z, q) : M.Node<K>}, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y), ST.nd(K, nl, y), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y), ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), y), ST.nd(K, nl, y), skipa(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir, y, nqy), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), y), ST.nd(K, SE.setl(K, nl, x, b), y), ST.nd(K, nl, y), skipp(K, SE.setl(K, nl, x, b), b, x, y, nby), skipl(K, nl, x, b, y, nxy))), {==})), {==})))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, aa, x, q) == True{} : Bool}, SE.modr(K, SE.modp(K, ST.nd(K, nl, y), q), x), ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), y), SE.modr(K, SE.modp(K, ST.nd(K, nl, y), q), x), e), isn_rp(K, ST.nd(K, nl, y), aa, b, x, x, q, hyn))

def rotr_b(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +q: Nat, +dir: Bool, +b1: Nat, +b2: Nat, +hbn: {ST.is_node(K, ST.nd(K, nl, b), b1, b2, y) == True{} : Bool}, +nxb: {Nat.is_eq(x, b) == False{} : Bool}, +nyb: {Nat.is_eq(y, b) == False{} : Bool}, +nqb: {Nat.is_eq(q, b) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, q, dir), b), b1, b2, x) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), b), SE.modp(K, ST.nd(K, nl, b), x), skipp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y, b, nxb), Equal.trans(M.Node<K>, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), b), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), b), SE.modp(K, ST.nd(K, nl, b), x), skipr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x, b, nyb), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), b), ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), b), SE.modp(K, ST.nd(K, nl, b), x), skipp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q, b, nyb), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), b), ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), b), SE.modp(K, ST.nd(K, nl, b), x), skipa(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir, b, nqb), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), b), SE.modp(K, ST.nd(K, SE.setl(K, nl, x, b), b), x), SE.modp(K, ST.nd(K, nl, b), x), hitp(K, SE.setl(K, nl, x, b), b, x), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, SE.setl(K, nl, x, b), b), x) == SE.modp(K, z, x) : M.Node<K>}, ST.nd(K, SE.setl(K, nl, x, b), b), ST.nd(K, nl, b), skipl(K, nl, x, b, b, nxb), {==}))))))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, b1, b2, x) == True{} : Bool}, SE.modp(K, ST.nd(K, nl, b), x), ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), q, y, dir), y, q), y, x), x, y), b), SE.modp(K, ST.nd(K, nl, b), x), e), isn_p(K, ST.nd(K, nl, b), b1, b2, y, x, hbn))

def rotr_q(-K: Data, +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +i: Nat, +lft: Bool, +s: Nat, +q2: Nat, +hqn: {ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, s), ST.pk(Nat, lft, s, x), q2) == True{} : Bool}, +nxq: {Nat.is_eq(x, 1n+i) == False{} : Bool}, +nyq: {Nat.is_eq(y, 1n+i) == False{} : Bool}, +nbq: {Nat.is_eq(b, 1n+i) == False{} : Bool}) -> {ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q2) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), x, y), 1n+i), ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipp(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), x, y, 1n+i, nxq), Equal.trans(M.Node<K>, ST.nd(K, SE.setr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x), 1n+i), ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipr(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), y, x, 1n+i, nyq), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i), 1n+i), ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), skipp(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), y, 1n+i, 1n+i, nyq), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i, y, lft), 1n+i), moda(K, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i), y, lft), moda(K, ST.nd(K, nl, 1n+i), y, lft), hita(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), i, y, lft), L.subst(M.Node<K>, z => {moda(K, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i), y, lft) == moda(K, z, y, lft) : M.Node<K>}, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i), ST.nd(K, nl, 1n+i), Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, SE.setl(K, nl, x, b), b, x), 1n+i), ST.nd(K, SE.setl(K, nl, x, b), 1n+i), ST.nd(K, nl, 1n+i), skipp(K, SE.setl(K, nl, x, b), b, x, 1n+i, nbq), skipl(K, nl, x, b, 1n+i, nxq)), {==})))))
  L.subst(M.Node<K>, z => {ST.is_node(K, z, ST.pk(Nat, lft, y, s), ST.pk(Nat, lft, s, y), q2) == True{} : Bool}, moda(K, ST.nd(K, nl, 1n+i), y, lft), ST.nd(K, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), Equal.sym(M.Node<K>, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), moda(K, ST.nd(K, nl, 1n+i), y, lft), e), isn_a(K, ST.nd(K, nl, 1n+i), lft, x, s, q2, y, hqn))

