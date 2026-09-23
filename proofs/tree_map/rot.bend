import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../spec/common.bend as SC
import ../../src/containers/balanced_search_tree.bend as M
import ../hash_table/state.bend as HT
import ../lru/state.bend as LST
import ../lru/lists.bend as LS
import ../lib/list.bend as LL
import ./state.bend as ST
import ./tree.bend as TR
import ./path.bend as P
import ./agree.bend as AG
import ./setters.bend as SE
import ./rotm.bend as RM
import ./rotn.bend as RN
import ./dj.bend as DJ
import ./spath.bend as SP

# Rotations along a path: rotating the subtree the path leads to (a node x
# with a child y) gives the rotated subtree, linked as the ghost says below
# the path's parent, and the path still leads to it (now rooted at y).
# (source: tools/generators/tm_hand/rot.src)


# ---- ids are positive ----

def ne0(+x: Nat, +h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_eq(0n, x) == False{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, L.false_true(h))
    case 1n+j:
      {==}

def zero_ids(~K: Data, +nl: List<&2, M.Node<K>>, +t: ST.Tr, +p: Nat, +hr: {ST.rep(~K, t, p, nl) == True{} : Bool}) -> {HT.memn(0n, ST.ids(t)) == False{} : Bool}:
  match t:
    case ST.TE{}:
      {==}
    case ST.TN{+i, +l, +r}:
      DJ.nm_app(0n, ST.ids(l), Con{i, ST.ids(r)}, zero_ids(~K, nl, l, i, TR.rep_l(~K, i, l, r, p, nl, hr)), DJ.nm_cons(0n, i, ST.ids(r), N.is_eq_sym_false(0n, i, ne0(i, L.and_left(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), hr))), zero_ids(~K, nl, r, i, TR.rep_r(~K, i, l, r, p, nl, hr))))


def zero_ctx(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +hc: {P.ctxok(~K, c, x, nl) == True{} : Bool}) -> {HT.memn(0n, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{+p, True{}, +s}, +u}:
      +hk = L.and_left(P.cok1(~K, P.FR{p, True{}, s}, x, P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
      +h0 = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, True{}, x, ST.rid(s)), ST.pk(Nat, True{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl)), hk)
      +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, True{}, x, ST.rid(s)), ST.pk(Nat, True{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl), L.and_right(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, True{}, x, ST.rid(s)), ST.pk(Nat, True{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl)), hk))
      +hu = zero_ctx(~K, nl, u, p, L.and_right(P.cok1(~K, P.FR{p, True{}, s}, x, P.top(u), nl), P.ctxok(~K, u, p, nl), hc))
      +zs = zero_ids(~K, nl, s, p, hs)
      +zp = N.is_eq_sym_false(0n, p, ne0(p, h0))
      DJ.nm_app(0n, P.before(u), Con{p, SC.append(Nat, ST.ids(s), P.after(u))}, DJ.nm_l(0n, P.before(u), P.after(u), hu), DJ.nm_cons(0n, p, SC.append(Nat, ST.ids(s), P.after(u)), zp, DJ.nm_app(0n, ST.ids(s), P.after(u), zs, DJ.nm_r(0n, P.before(u), P.after(u), hu))))
    case Con{P.FR{+p, False{}, +s}, +u}:
      +hk = L.and_left(P.cok1(~K, P.FR{p, False{}, s}, x, P.top(u), nl), P.ctxok(~K, u, p, nl), hc)
      +h0 = L.and_left(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, False{}, x, ST.rid(s)), ST.pk(Nat, False{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl)), hk)
      +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, False{}, x, ST.rid(s)), ST.pk(Nat, False{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl), L.and_right(Nat.is_lt(0n, p), Bool.and(ST.is_node(K, ST.nd(K, nl, p), ST.pk(Nat, False{}, x, ST.rid(s)), ST.pk(Nat, False{}, ST.rid(s), x), P.top(u)), ST.rep(~K, s, p, nl)), hk))
      +hu = zero_ctx(~K, nl, u, p, L.and_right(P.cok1(~K, P.FR{p, False{}, s}, x, P.top(u), nl), P.ctxok(~K, u, p, nl), hc))
      +zs = zero_ids(~K, nl, s, p, hs)
      +zp = N.is_eq_sym_false(0n, p, ne0(p, h0))
      DJ.nm_app(0n, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{p, Nil{}})), P.after(u), DJ.nm_app(0n, P.before(u), SC.append(Nat, ST.ids(s), Con{p, Nil{}}), DJ.nm_l(0n, P.before(u), P.after(u), hu), DJ.nm_app(0n, ST.ids(s), Con{p, Nil{}}, zs, DJ.nm_cons(0n, p, Nil{}, zp, {==}))), DJ.nm_r(0n, P.before(u), P.after(u), hu))

# ---- lists around a frame ----


def nd_drop(+b: List<&2, Nat>, +s: List<&2, Nat>, +a: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, b, SC.append(Nat, s, a))) == True{} : Bool}) -> {LST.nodupn(SC.append(Nat, b, a)) == True{} : Bool}:
  match s:
    case Nil{}:
      h
    case Con{+z, +t}:
      +e = LS.nd_mid(b, z, SC.append(Nat, t, a))
      nd_drop(b, t, a, L.and_left(LST.nodupn(SC.append(Nat, b, SC.append(Nat, t, a))), Bool.not(HT.memn(z, SC.append(Nat, b, SC.append(Nat, t, a)))), L.subst(Bool, w => {w == True{} : Bool}, LST.nodupn(SC.append(Nat, b, Con{z, SC.append(Nat, t, a)})), Bool.and(LST.nodupn(SC.append(Nat, b, SC.append(Nat, t, a))), Bool.not(HT.memn(z, SC.append(Nat, b, SC.append(Nat, t, a))))), e, h)))

def nd_mid_nm(+b: List<&2, Nat>, +z: Nat, +a: List<&2, Nat>, +h: {LST.nodupn(SC.append(Nat, b, Con{z, a})) == True{} : Bool}) -> {HT.memn(z, SC.append(Nat, b, a)) == False{} : Bool}:
  LS.not_t_f(HT.memn(z, SC.append(Nat, b, a)), L.and_right(LST.nodupn(SC.append(Nat, b, a)), Bool.not(HT.memn(z, SC.append(Nat, b, a))), L.subst(Bool, w => {w == True{} : Bool}, LST.nodupn(SC.append(Nat, b, Con{z, a})), Bool.and(LST.nodupn(SC.append(Nat, b, a)), Bool.not(HT.memn(z, SC.append(Nat, b, a)))), LS.nd_mid(b, z, a), h)))



# the parent of a frame is neither in the sibling nor in the frames above
def fq_s(+q: Nat, +lft: Bool, +s: ST.Tr, +u: List<&2, P.Fr>, +h: {LST.nodupn(SC.append(Nat, P.before(Con{P.FR{q, lft, s}, u}), P.after(Con{P.FR{q, lft, s}, u}))) == True{} : Bool}) -> {HT.memn(q, ST.ids(s)) == False{} : Bool} & {HT.memn(q, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}:
  match lft:
    case True{}:
      +hm = nd_mid_nm(P.before(u), q, SC.append(Nat, ST.ids(s), P.after(u)), h)
      +hr = DJ.nm_r(q, P.before(u), SC.append(Nat, ST.ids(s), P.after(u)), hm)
      (DJ.nm_l(q, ST.ids(s), P.after(u), hr), DJ.nm_app(q, P.before(u), P.after(u), DJ.nm_l(q, P.before(u), SC.append(Nat, ST.ids(s), P.after(u)), hm), DJ.nm_r(q, ST.ids(s), P.after(u), hr)))
    case False{}:
      +e1 = LL.append_assoc(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}}), P.after(u))
      +e2 = LL.append_assoc(Nat, ST.ids(s), Con{q, Nil{}}, P.after(u))
      +e3 = LL.append_assoc(Nat, P.before(u), ST.ids(s), Con{q, P.after(u)})
      +h1 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}})), P.after(u)), SC.append(Nat, P.before(u), SC.append(Nat, SC.append(Nat, ST.ids(s), Con{q, Nil{}}), P.after(u))), e1, h)
      +h2 = L.subst(List<&2, Nat>, z => {LST.nodupn(SC.append(Nat, P.before(u), z)) == True{} : Bool}, SC.append(Nat, SC.append(Nat, ST.ids(s), Con{q, Nil{}}), P.after(u)), SC.append(Nat, ST.ids(s), Con{q, P.after(u)}), e2, h1)
      +h3 = L.subst(List<&2, Nat>, z => {LST.nodupn(z) == True{} : Bool}, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, P.after(u)})), SC.append(Nat, SC.append(Nat, P.before(u), ST.ids(s)), Con{q, P.after(u)}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, P.before(u), ST.ids(s)), Con{q, P.after(u)}), SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, P.after(u)})), e3), h2)
      +hm = nd_mid_nm(SC.append(Nat, P.before(u), ST.ids(s)), q, P.after(u), h3)
      +hl = DJ.nm_l(q, SC.append(Nat, P.before(u), ST.ids(s)), P.after(u), hm)
      (DJ.nm_r(q, P.before(u), ST.ids(s), hl), DJ.nm_app(q, P.before(u), P.after(u), DJ.nm_l(q, P.before(u), ST.ids(s), hl), DJ.nm_r(q, SC.append(Nat, P.before(u), ST.ids(s)), P.after(u), hm)))

# an id absent from a frame's lists is absent from its sibling and above
def fw_s(+w: Nat, +q: Nat, +lft: Bool, +s: ST.Tr, +u: List<&2, P.Fr>, +h: {HT.memn(w, SC.append(Nat, P.before(Con{P.FR{q, lft, s}, u}), P.after(Con{P.FR{q, lft, s}, u}))) == False{} : Bool}) -> {HT.memn(w, ST.ids(s)) == False{} : Bool} & {HT.memn(w, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}:
  match lft:
    case True{}:
      +h2 = DJ.nm_ct(w, q, SC.append(Nat, ST.ids(s), P.after(u)), DJ.nm_r(w, P.before(u), Con{q, SC.append(Nat, ST.ids(s), P.after(u))}, h))
      (DJ.nm_l(w, ST.ids(s), P.after(u), h2), DJ.nm_app(w, P.before(u), P.after(u), DJ.nm_l(w, P.before(u), Con{q, SC.append(Nat, ST.ids(s), P.after(u))}, h), DJ.nm_r(w, ST.ids(s), P.after(u), h2)))
    case False{}:
      +h1 = DJ.nm_l(w, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}})), P.after(u), h)
      (DJ.nm_l(w, ST.ids(s), Con{q, Nil{}}, DJ.nm_r(w, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}}), h1)), DJ.nm_app(w, P.before(u), P.after(u), DJ.nm_l(w, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}}), h1), DJ.nm_r(w, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{q, Nil{}})), P.after(u), h)))

# ---- the left rotation: the rotated subtree ----

def rep_intro(~K: Data, +nl: List<&2, M.Node<K>>, +i: Nat, +l: ST.Tr, +r: ST.Tr, +p: Nat, +h0: {Nat.is_lt(0n, i) == True{} : Bool}, +hn: {ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p) == True{} : Bool}, +hl: {ST.rep(~K, l, i, nl) == True{} : Bool}, +hr: {ST.rep(~K, r, i, nl) == True{} : Bool}) -> {ST.rep(~K, ST.TN{i, l, r}, p, nl) == True{} : Bool}:
  L.and_intro(Nat.is_lt(0n, i), Bool.and(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl))), h0, L.and_intro(ST.is_node(K, ST.nd(K, nl, i), ST.rid(l), ST.rid(r), p), Bool.and(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl)), hn, L.and_intro(ST.rep(~K, l, i, nl), ST.rep(~K, r, i, nl), hl, hr)))

def rep_moved(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +t: ST.Tr, +p: Nat, +nl: List<&2, M.Node<K>>, +nl2: List<&2, M.Node<K>>, +ha: {AG.agr(~K, ~cmp, ST.ids(t), nl, nl2) == True{} : Bool}, +h: {ST.rep(~K, t, p, nl) == True{} : Bool}) -> {ST.rep(~K, t, p, nl2) == True{} : Bool}:
  Equal.trans(Bool, ST.rep(~K, t, p, nl2), ST.rep(~K, t, p, nl), True{}, AG.rep_agr(~K, ~cmp, ~o, t, p, nl, nl2, ha), h)


def rotl_rep(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +x: Nat, +ta: ST.Tr, +y: Nat, +tb: ST.Tr, +tc: ST.Tr, +q: Nat, +dir: Bool, +h0x: {Nat.is_lt(0n, x) == True{} : Bool}, +h0y: {Nat.is_lt(0n, y) == True{} : Bool}, +hxn: {ST.is_node(K, ST.nd(K, nl, x), ST.rid(ta), y, q) == True{} : Bool}, +hyn: {ST.is_node(K, ST.nd(K, nl, y), ST.rid(tb), ST.rid(tc), x) == True{} : Bool}, +hA: {ST.rep(~K, ta, x, nl) == True{} : Bool}, +hB: {ST.rep(~K, tb, y, nl) == True{} : Bool}, +hC: {ST.rep(~K, tc, y, nl) == True{} : Bool}, +hS: {LST.nodupn(SC.append(Nat, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})})) == True{} : Bool}, +hqS: {HT.memn(q, SC.append(Nat, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})})) == False{} : Bool}) -> {ST.rep(~K, ST.TN{y, ST.TN{x, ta, tb}, tc}, q, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir)) == True{} : Bool}:
  match tb:
    case ST.TE{}:
      +hR = DJ.ndr(ST.ids(ta), Con{x, SC.append(Nat, Nil{}, Con{y, ST.ids(tc)})}, hS)
      +xR1 = DJ.nd_head(x, Con{y, ST.ids(tc)}, hR)
      +nyx = DJ.nm_ch(x, y, ST.ids(tc), xR1)
      +xIA = DJ.dj_l(ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, hS, x, DJ.mem_hd(x, Con{y, ST.ids(tc)}))
      +yIA = DJ.dj_l(ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, hS, y, DJ.mem_tl(y, x, Con{y, ST.ids(tc)}, DJ.mem_hd(y, ST.ids(tc))))
      +xIC = DJ.nm_ct(x, y, ST.ids(tc), xR1)
      +yIC = DJ.nd_head(y, ST.ids(tc), DJ.nd_tail(x, Con{y, ST.ids(tc)}, hR))
      +mx = DJ.mem_r(x, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, DJ.mem_hd(x, Con{y, ST.ids(tc)}))
      +my = DJ.mem_r(y, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, DJ.mem_tl(y, x, Con{y, ST.ids(tc)}, DJ.mem_hd(y, ST.ids(tc))))
      +nqx = DJ.ne_nm(q, x, SC.append(Nat, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}), hqS, mx)
      +nqy = DJ.ne_nm(q, y, SC.append(Nat, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}), hqS, my)
      +qIA = DJ.nm_l(q, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, hqS)
      +qIC = DJ.nm_ct(q, y, ST.ids(tc), DJ.nm_ct(q, x, Con{y, ST.ids(tc)}, DJ.nm_r(q, ST.ids(ta), Con{x, Con{y, ST.ids(tc)}}, hqS)))
      +agA = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(ta), nl, x, y, 0n, q, dir, xIA, yIA, zero_ids(~K, nl, ta, x, hA), qIA)
      +agC = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(tc), nl, x, y, 0n, q, dir, xIC, yIC, zero_ids(~K, nl, tc, y, hC), qIC)
      +rx = RN.rotl_x(K, nl, x, y, 0n, q, dir, ST.rid(ta), hxn, nyx, nqx, ne0(x, h0x))
      +ry = RN.rotl_y(K, nl, x, y, 0n, q, dir, ST.rid(tc), hyn, N.is_eq_sym_false(y, x, nyx), nqy, ne0(y, h0y))
      rep_intro(~K, RM.rotl_nl(K, nl, x, y, 0n, q, dir), y, ST.TN{x, ta, ST.TE{}}, tc, q, h0y, ry, rep_intro(~K, RM.rotl_nl(K, nl, x, y, 0n, q, dir), x, ta, ST.TE{}, y, h0x, rx, rep_moved(~K, ~cmp, ~o, ta, x, nl, RM.rotl_nl(K, nl, x, y, 0n, q, dir), agA, hA), {==}), rep_moved(~K, ~cmp, ~o, tc, y, nl, RM.rotl_nl(K, nl, x, y, 0n, q, dir), agC, hC))
    case ST.TN{+b, +b1, +b2}:
      +hR = DJ.ndr(ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hS)
      +hR1 = DJ.nd_tail(x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), hR)
      +xR1 = DJ.nd_head(x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), hR)
      +myR1 = DJ.mem_r(y, ST.ids(tb), Con{y, ST.ids(tc)}, DJ.mem_hd(y, ST.ids(tc)))
      +mbIB = DJ.mem_r(b, ST.ids(b1), Con{b, ST.ids(b2)}, DJ.mem_hd(b, ST.ids(b2)))
      +mbR1 = DJ.mem_l(b, ST.ids(tb), Con{y, ST.ids(tc)}, mbIB)
      +mx = DJ.mem_r(x, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, DJ.mem_hd(x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})))
      +my = DJ.mem_r(y, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, DJ.mem_tl(y, x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), myR1))
      +mb = DJ.mem_r(b, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, DJ.mem_tl(b, x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), mbR1))
      +xIA = DJ.dj_l(ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hS, x, DJ.mem_hd(x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})))
      +yIA = DJ.dj_l(ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hS, y, DJ.mem_tl(y, x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), myR1))
      +bIA = DJ.dj_l(ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hS, b, DJ.mem_tl(b, x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), mbR1))
      +xIB = DJ.nm_l(x, ST.ids(tb), Con{y, ST.ids(tc)}, xR1)
      +xyc = DJ.nm_r(x, ST.ids(tb), Con{y, ST.ids(tc)}, xR1)
      +nyx = DJ.nm_ch(x, y, ST.ids(tc), xyc)
      +xIC = DJ.nm_ct(x, y, ST.ids(tc), xyc)
      +yIB = DJ.dj_l(ST.ids(tb), Con{y, ST.ids(tc)}, hR1, y, DJ.mem_hd(y, ST.ids(tc)))
      +yIC = DJ.nd_head(y, ST.ids(tc), DJ.ndr(ST.ids(tb), Con{y, ST.ids(tc)}, hR1))
      +nxb = DJ.ne_nm(x, b, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), xR1, mbR1)
      +byc = DJ.dj_r(ST.ids(tb), Con{y, ST.ids(tc)}, hR1, b, mbIB)
      +nyb = DJ.nm_ch(b, y, ST.ids(tc), byc)
      +bIC = DJ.nm_ct(b, y, ST.ids(tc), byc)
      +nqx = DJ.ne_nm(q, x, SC.append(Nat, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}), hqS, mx)
      +nqy = DJ.ne_nm(q, y, SC.append(Nat, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}), hqS, my)
      +nqb = DJ.ne_nm(q, b, SC.append(Nat, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}), hqS, mb)
      +qIA = DJ.nm_l(q, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hqS)
      +qR1 = DJ.nm_ct(q, x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)}), DJ.nm_r(q, ST.ids(ta), Con{x, SC.append(Nat, ST.ids(tb), Con{y, ST.ids(tc)})}, hqS))
      +qIB = DJ.nm_l(q, ST.ids(tb), Con{y, ST.ids(tc)}, qR1)
      +qIC = DJ.nm_ct(q, y, ST.ids(tc), DJ.nm_r(q, ST.ids(tb), Con{y, ST.ids(tc)}, qR1))
      +hIB = DJ.ndl(ST.ids(tb), Con{y, ST.ids(tc)}, hR1)
      +bB1 = DJ.dj_l(ST.ids(b1), Con{b, ST.ids(b2)}, hIB, b, DJ.mem_hd(b, ST.ids(b2)))
      +bB2 = DJ.nd_head(b, ST.ids(b2), DJ.ndr(ST.ids(b1), Con{b, ST.ids(b2)}, hIB))
      +xB1 = DJ.nm_l(x, ST.ids(b1), Con{b, ST.ids(b2)}, xIB)
      +xB2 = DJ.nm_ct(x, b, ST.ids(b2), DJ.nm_r(x, ST.ids(b1), Con{b, ST.ids(b2)}, xIB))
      +yB1 = DJ.nm_l(y, ST.ids(b1), Con{b, ST.ids(b2)}, yIB)
      +yB2 = DJ.nm_ct(y, b, ST.ids(b2), DJ.nm_r(y, ST.ids(b1), Con{b, ST.ids(b2)}, yIB))
      +qB1 = DJ.nm_l(q, ST.ids(b1), Con{b, ST.ids(b2)}, qIB)
      +qB2 = DJ.nm_ct(q, b, ST.ids(b2), DJ.nm_r(q, ST.ids(b1), Con{b, ST.ids(b2)}, qIB))
      +agA = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(ta), nl, x, y, b, q, dir, xIA, yIA, bIA, qIA)
      +agC = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(tc), nl, x, y, b, q, dir, xIC, yIC, bIC, qIC)
      +agB1 = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(b1), nl, x, y, b, q, dir, xB1, yB1, bB1, qB1)
      +agB2 = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(b2), nl, x, y, b, q, dir, xB2, yB2, bB2, qB2)
      +h0b = L.and_left(Nat.is_lt(0n, b), Bool.and(ST.is_node(K, ST.nd(K, nl, b), ST.rid(b1), ST.rid(b2), y), Bool.and(ST.rep(~K, b1, b, nl), ST.rep(~K, b2, b, nl))), hB)
      +rx = RN.rotl_x(K, nl, x, y, b, q, dir, ST.rid(ta), hxn, nyx, nqx, N.is_eq_sym_false(x, b, nxb))
      +ry = RN.rotl_y(K, nl, x, y, b, q, dir, ST.rid(tc), hyn, N.is_eq_sym_false(y, x, nyx), nqy, N.is_eq_sym_false(y, b, nyb))
      +rb = RN.rotl_b(K, nl, x, y, b, q, dir, ST.rid(b1), ST.rid(b2), TR.rep_node(~K, b, b1, b2, y, nl, hB), nxb, nyb, nqb)
      +repB = rep_intro(~K, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), b, b1, b2, x, h0b, rb, rep_moved(~K, ~cmp, ~o, b1, b, nl, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), agB1, TR.rep_l(~K, b, b1, b2, y, nl, hB)), rep_moved(~K, ~cmp, ~o, b2, b, nl, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), agB2, TR.rep_r(~K, b, b1, b2, y, nl, hB)))
      rep_intro(~K, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), y, ST.TN{x, ta, ST.TN{b, b1, b2}}, tc, q, h0y, ry, rep_intro(~K, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), x, ta, ST.TN{b, b1, b2}, y, h0x, rx, rep_moved(~K, ~cmp, ~o, ta, x, nl, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), agA, hA), repB), rep_moved(~K, ~cmp, ~o, tc, y, nl, RM.rotl_nl(K, nl, x, y, ST.rid(tb), q, dir), agC, hC))

# ---- the left rotation: the path ----


def ctx_frame(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +i: Nat, +lft: Bool, +s: ST.Tr, +u: List<&2, P.Fr>, +hok: {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, x, nl) == True{} : Bool}, +hx: {HT.memn(x, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hy: {HT.memn(y, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hb: {HT.memn(b, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hBA: {LST.nodupn(SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == True{} : Bool}, +mq: {HT.memn(1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == True{} : Bool}) -> {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, y, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft)) == True{} : Bool}:
  +hk = L.and_left(P.cok1(~K, P.FR{1n+i, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hok)
  +hu = L.and_right(P.cok1(~K, P.FR{1n+i, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hok)
  +h0 = L.and_left(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk)
  +hqn = L.and_left(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +nxq = DJ.ne_nm(x, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hx, mq)
  +nyq = DJ.ne_nm(y, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hy, mq)
  +nbq = DJ.ne_nm(b, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hb, mq)
  +rq = RN.rotl_q(K, nl, x, y, b, i, lft, ST.rid(s), P.top(u), hqn, nxq, nyq, nbq)
  +agS = RN.rotl_agr(~K, ~cmp, ~o, ST.ids(s), nl, x, y, b, 1n+i, lft, Pair.fst({HT.memn(x, ST.ids(s)) == False{} : Bool}, {HT.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(x, 1n+i, lft, s, u, hx)), Pair.fst({HT.memn(y, ST.ids(s)) == False{} : Bool}, {HT.memn(y, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(y, 1n+i, lft, s, u, hy)), Pair.fst({HT.memn(b, ST.ids(s)) == False{} : Bool}, {HT.memn(b, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(b, 1n+i, lft, s, u, hb)), Pair.fst({HT.memn(1n+i, ST.ids(s)) == False{} : Bool}, {HT.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fq_s(1n+i, lft, s, u, hBA)))
  +agU = RN.rotl_agr(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), nl, x, y, b, 1n+i, lft, Pair.snd({HT.memn(x, ST.ids(s)) == False{} : Bool}, {HT.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(x, 1n+i, lft, s, u, hx)), Pair.snd({HT.memn(y, ST.ids(s)) == False{} : Bool}, {HT.memn(y, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(y, 1n+i, lft, s, u, hy)), Pair.snd({HT.memn(b, ST.ids(s)) == False{} : Bool}, {HT.memn(b, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(b, 1n+i, lft, s, u, hb)), Pair.snd({HT.memn(1n+i, ST.ids(s)) == False{} : Bool}, {HT.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fq_s(1n+i, lft, s, u, hBA)))
  +hu2 = Equal.trans(Bool, P.ctxok(~K, u, 1n+i, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft)), P.ctxok(~K, u, 1n+i, nl), True{}, AG.ctx_agr(~K, ~cmp, ~o, u, 1n+i, nl, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), agU), hu)
  +hs2 = rep_moved(~K, ~cmp, ~o, s, 1n+i, nl, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), agS, hs)
  L.and_intro(P.cok1(~K, P.FR{1n+i, lft, s}, y, P.top(u), RM.rotl_nl(K, nl, x, y, b, 1n+i, lft)), P.ctxok(~K, u, 1n+i, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft)), L.and_intro(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), y), P.top(u)), ST.rep(~K, s, 1n+i, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft))), h0, L.and_intro(ST.is_node(K, ST.nd(K, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), y), P.top(u)), ST.rep(~K, s, 1n+i, RM.rotl_nl(K, nl, x, y, b, 1n+i, lft)), rq, hs2)), hu2)

def rotl_ctx(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +y: Nat, +b: Nat, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hx: {HT.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hy: {HT.memn(y, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hb: {HT.memn(b, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hBA: {LST.nodupn(SC.append(Nat, P.before(c), P.after(c))) == True{} : Bool}) -> {P.ctxok(~K, c, y, RM.rotl_nl(K, nl, x, y, b, P.top(c), SP.dir(c))) == True{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{0n, +lft, +s}, +u}:
      Empty.absurd({P.ctxok(~K, Con{P.FR{0n, lft, s}, u}, y, RM.rotl_nl(K, nl, x, y, b, 0n, lft)) == True{} : Bool}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 0n, nl)), L.and_left(P.cok1(~K, P.FR{0n, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 0n, nl), hok))))
    case Con{P.FR{1n+i, True{}, +s}, +u}:
      ctx_frame(~K, ~cmp, ~o, nl, x, y, b, i, True{}, s, u, hok, hx, hy, hb, hBA, DJ.mem_r(1n+i, P.before(u), Con{1n+i, SC.append(Nat, ST.ids(s), P.after(u))}, DJ.mem_hd(1n+i, SC.append(Nat, ST.ids(s), P.after(u)))))
    case Con{P.FR{1n+i, False{}, +s}, +u}:
      ctx_frame(~K, ~cmp, ~o, nl, x, y, b, i, False{}, s, u, hok, hx, hy, hb, hBA, DJ.mem_l(1n+i, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}})), P.after(u), DJ.mem_r(1n+i, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}}), DJ.mem_r(1n+i, ST.ids(s), Con{1n+i, Nil{}}, DJ.mem_hd(1n+i, Nil{})))))

# ---- the right rotation: the rotated subtree ----


def rotr_rep(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +ta: ST.Tr, +tb: ST.Tr, +tc: ST.Tr, +q: Nat, +dir: Bool, +h0x: {Nat.is_lt(0n, x) == True{} : Bool}, +h0y: {Nat.is_lt(0n, y) == True{} : Bool}, +hxn: {ST.is_node(K, ST.nd(K, nl, x), y, ST.rid(tc), q) == True{} : Bool}, +hyn: {ST.is_node(K, ST.nd(K, nl, y), ST.rid(ta), ST.rid(tb), x) == True{} : Bool}, +hA: {ST.rep(~K, ta, y, nl) == True{} : Bool}, +hB: {ST.rep(~K, tb, y, nl) == True{} : Bool}, +hC: {ST.rep(~K, tc, x, nl) == True{} : Bool}, +hS: {LST.nodupn(SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)})) == True{} : Bool}, +hqS: {HT.memn(q, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)})) == False{} : Bool}) -> {ST.rep(~K, ST.TN{y, ta, ST.TN{x, tb, tc}}, q, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir)) == True{} : Bool}:
  match tb:
    case ST.TE{}:
      +hP1 = DJ.ndl(SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hS)
      +xIC = DJ.nd_head(x, ST.ids(tc), DJ.ndr(SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hS))
      +xP1 = DJ.dj_l(SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hS, x, DJ.mem_hd(x, ST.ids(tc)))
      +xIA = DJ.nm_l(x, ST.ids(ta), Con{y, Nil{}}, xP1)
      +nyx = DJ.nm_ch(x, y, Nil{}, DJ.nm_r(x, ST.ids(ta), Con{y, Nil{}}, xP1))
      +myP1 = DJ.mem_r(y, ST.ids(ta), Con{y, Nil{}}, DJ.mem_hd(y, Nil{}))
      +yxc = DJ.dj_r(SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hS, y, myP1)
      +nxy = DJ.nm_ch(y, x, ST.ids(tc), yxc)
      +yIC = DJ.nm_ct(y, x, ST.ids(tc), yxc)
      +yIA = DJ.dj_l(ST.ids(ta), Con{y, Nil{}}, hP1, y, DJ.mem_hd(y, Nil{}))
      +mx = DJ.mem_r(x, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, DJ.mem_hd(x, ST.ids(tc)))
      +my = DJ.mem_l(y, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, myP1)
      +nqx = DJ.ne_nm(q, x, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}), hqS, mx)
      +nqy = DJ.ne_nm(q, y, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}), hqS, my)
      +qP1 = DJ.nm_l(q, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hqS)
      +qIA = DJ.nm_l(q, ST.ids(ta), Con{y, Nil{}}, qP1)
      +qIC = DJ.nm_ct(q, x, ST.ids(tc), DJ.nm_r(q, SC.append(Nat, ST.ids(ta), Con{y, Nil{}}), Con{x, ST.ids(tc)}, hqS))
      +agA = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(ta), nl, x, y, 0n, q, dir, xIA, yIA, zero_ids(~K, nl, ta, y, hA), qIA)
      +agC = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(tc), nl, x, y, 0n, q, dir, xIC, yIC, zero_ids(~K, nl, tc, x, hC), qIC)
      +rx = RN.rotr_x(K, nl, x, y, 0n, q, dir, ST.rid(tc), hxn, nyx, nqx, ne0(x, h0x))
      +ry = RN.rotr_y(K, nl, x, y, 0n, q, dir, ST.rid(ta), hyn, nxy, nqy, ne0(y, h0y))
      rep_intro(~K, RM.rotr_nl(K, nl, x, y, 0n, q, dir), y, ta, ST.TN{x, ST.TE{}, tc}, q, h0y, ry, rep_moved(~K, ~cmp, ~o, ta, y, nl, RM.rotr_nl(K, nl, x, y, 0n, q, dir), agA, hA), rep_intro(~K, RM.rotr_nl(K, nl, x, y, 0n, q, dir), x, ST.TE{}, tc, y, h0x, rx, {==}, rep_moved(~K, ~cmp, ~o, tc, x, nl, RM.rotr_nl(K, nl, x, y, 0n, q, dir), agC, hC)))
    case ST.TN{+b, +b1, +b2}:
      +hP1 = DJ.ndl(SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hS)
      +xIC = DJ.nd_head(x, ST.ids(tc), DJ.ndr(SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hS))
      +xP1 = DJ.dj_l(SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hS, x, DJ.mem_hd(x, ST.ids(tc)))
      +xIA = DJ.nm_l(x, ST.ids(ta), Con{y, ST.ids(tb)}, xP1)
      +xyb = DJ.nm_r(x, ST.ids(ta), Con{y, ST.ids(tb)}, xP1)
      +nyx = DJ.nm_ch(x, y, ST.ids(tb), xyb)
      +xIB = DJ.nm_ct(x, y, ST.ids(tb), xyb)
      +myP1 = DJ.mem_r(y, ST.ids(ta), Con{y, ST.ids(tb)}, DJ.mem_hd(y, ST.ids(tb)))
      +yxc = DJ.dj_r(SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hS, y, myP1)
      +nxy = DJ.nm_ch(y, x, ST.ids(tc), yxc)
      +yIC = DJ.nm_ct(y, x, ST.ids(tc), yxc)
      +yIA = DJ.dj_l(ST.ids(ta), Con{y, ST.ids(tb)}, hP1, y, DJ.mem_hd(y, ST.ids(tb)))
      +hYB = DJ.ndr(ST.ids(ta), Con{y, ST.ids(tb)}, hP1)
      +yIB = DJ.nd_head(y, ST.ids(tb), hYB)
      +mbIB = DJ.mem_r(b, ST.ids(b1), Con{b, ST.ids(b2)}, DJ.mem_hd(b, ST.ids(b2)))
      +mbP1 = DJ.mem_r(b, ST.ids(ta), Con{y, ST.ids(tb)}, DJ.mem_tl(b, y, ST.ids(tb), mbIB))
      +mx = DJ.mem_r(x, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, DJ.mem_hd(x, ST.ids(tc)))
      +my = DJ.mem_l(y, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, myP1)
      +mb = DJ.mem_l(b, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, mbP1)
      +nyb = DJ.ne_nm(y, b, ST.ids(tb), yIB, mbIB)
      +bIA = DJ.dj_l(ST.ids(ta), Con{y, ST.ids(tb)}, hP1, b, DJ.mem_tl(b, y, ST.ids(tb), mbIB))
      +bxc = DJ.dj_r(SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hS, b, mbP1)
      +nxb = DJ.nm_ch(b, x, ST.ids(tc), bxc)
      +bIC = DJ.nm_ct(b, x, ST.ids(tc), bxc)
      +nqx = DJ.ne_nm(q, x, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}), hqS, mx)
      +nqy = DJ.ne_nm(q, y, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}), hqS, my)
      +nqb = DJ.ne_nm(q, b, SC.append(Nat, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}), hqS, mb)
      +qP1 = DJ.nm_l(q, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hqS)
      +qIA = DJ.nm_l(q, ST.ids(ta), Con{y, ST.ids(tb)}, qP1)
      +qIB = DJ.nm_ct(q, y, ST.ids(tb), DJ.nm_r(q, ST.ids(ta), Con{y, ST.ids(tb)}, qP1))
      +qIC = DJ.nm_ct(q, x, ST.ids(tc), DJ.nm_r(q, SC.append(Nat, ST.ids(ta), Con{y, ST.ids(tb)}), Con{x, ST.ids(tc)}, hqS))
      +hIB = DJ.nd_tail(y, ST.ids(tb), hYB)
      +bB1 = DJ.dj_l(ST.ids(b1), Con{b, ST.ids(b2)}, hIB, b, DJ.mem_hd(b, ST.ids(b2)))
      +bB2 = DJ.nd_head(b, ST.ids(b2), DJ.ndr(ST.ids(b1), Con{b, ST.ids(b2)}, hIB))
      +xB1 = DJ.nm_l(x, ST.ids(b1), Con{b, ST.ids(b2)}, xIB)
      +xB2 = DJ.nm_ct(x, b, ST.ids(b2), DJ.nm_r(x, ST.ids(b1), Con{b, ST.ids(b2)}, xIB))
      +yB1 = DJ.nm_l(y, ST.ids(b1), Con{b, ST.ids(b2)}, yIB)
      +yB2 = DJ.nm_ct(y, b, ST.ids(b2), DJ.nm_r(y, ST.ids(b1), Con{b, ST.ids(b2)}, yIB))
      +qB1 = DJ.nm_l(q, ST.ids(b1), Con{b, ST.ids(b2)}, qIB)
      +qB2 = DJ.nm_ct(q, b, ST.ids(b2), DJ.nm_r(q, ST.ids(b1), Con{b, ST.ids(b2)}, qIB))
      +agA = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(ta), nl, x, y, b, q, dir, xIA, yIA, bIA, qIA)
      +agC = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(tc), nl, x, y, b, q, dir, xIC, yIC, bIC, qIC)
      +agB1 = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(b1), nl, x, y, b, q, dir, xB1, yB1, bB1, qB1)
      +agB2 = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(b2), nl, x, y, b, q, dir, xB2, yB2, bB2, qB2)
      +h0b = L.and_left(Nat.is_lt(0n, b), Bool.and(ST.is_node(K, ST.nd(K, nl, b), ST.rid(b1), ST.rid(b2), y), Bool.and(ST.rep(~K, b1, b, nl), ST.rep(~K, b2, b, nl))), hB)
      +rx = RN.rotr_x(K, nl, x, y, b, q, dir, ST.rid(tc), hxn, nyx, nqx, N.is_eq_sym_false(x, b, nxb))
      +ry = RN.rotr_y(K, nl, x, y, b, q, dir, ST.rid(ta), hyn, nxy, nqy, N.is_eq_sym_false(y, b, nyb))
      +rb = RN.rotr_b(K, nl, x, y, b, q, dir, ST.rid(b1), ST.rid(b2), TR.rep_node(~K, b, b1, b2, y, nl, hB), nxb, nyb, nqb)
      +repB = rep_intro(~K, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), b, b1, b2, x, h0b, rb, rep_moved(~K, ~cmp, ~o, b1, b, nl, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), agB1, TR.rep_l(~K, b, b1, b2, y, nl, hB)), rep_moved(~K, ~cmp, ~o, b2, b, nl, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), agB2, TR.rep_r(~K, b, b1, b2, y, nl, hB)))
      rep_intro(~K, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), y, ta, ST.TN{x, ST.TN{b, b1, b2}, tc}, q, h0y, ry, rep_moved(~K, ~cmp, ~o, ta, y, nl, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), agA, hA), rep_intro(~K, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), x, ST.TN{b, b1, b2}, tc, y, h0x, rx, repB, rep_moved(~K, ~cmp, ~o, tc, x, nl, RM.rotr_nl(K, nl, x, y, ST.rid(tb), q, dir), agC, hC)))

# ---- the right rotation: the path ----


def ctx_frame_r(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +x: Nat, +y: Nat, +b: Nat, +i: Nat, +lft: Bool, +s: ST.Tr, +u: List<&2, P.Fr>, +hok: {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, x, nl) == True{} : Bool}, +hx: {HT.memn(x, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hy: {HT.memn(y, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hb: {HT.memn(b, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}, +hBA: {LST.nodupn(SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == True{} : Bool}, +mq: {HT.memn(1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == True{} : Bool}) -> {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, y, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft)) == True{} : Bool}:
  +hk = L.and_left(P.cok1(~K, P.FR{1n+i, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hok)
  +hu = L.and_right(P.cok1(~K, P.FR{1n+i, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hok)
  +h0 = L.and_left(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk)
  +hqn = L.and_left(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +nxq = DJ.ne_nm(x, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hx, mq)
  +nyq = DJ.ne_nm(y, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hy, mq)
  +nbq = DJ.ne_nm(b, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u})), hb, mq)
  +rq = RN.rotr_q(K, nl, x, y, b, i, lft, ST.rid(s), P.top(u), hqn, nxq, nyq, nbq)
  +agS = RN.rotr_agr(~K, ~cmp, ~o, ST.ids(s), nl, x, y, b, 1n+i, lft, Pair.fst({HT.memn(x, ST.ids(s)) == False{} : Bool}, {HT.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(x, 1n+i, lft, s, u, hx)), Pair.fst({HT.memn(y, ST.ids(s)) == False{} : Bool}, {HT.memn(y, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(y, 1n+i, lft, s, u, hy)), Pair.fst({HT.memn(b, ST.ids(s)) == False{} : Bool}, {HT.memn(b, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(b, 1n+i, lft, s, u, hb)), Pair.fst({HT.memn(1n+i, ST.ids(s)) == False{} : Bool}, {HT.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fq_s(1n+i, lft, s, u, hBA)))
  +agU = RN.rotr_agr(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), nl, x, y, b, 1n+i, lft, Pair.snd({HT.memn(x, ST.ids(s)) == False{} : Bool}, {HT.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(x, 1n+i, lft, s, u, hx)), Pair.snd({HT.memn(y, ST.ids(s)) == False{} : Bool}, {HT.memn(y, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(y, 1n+i, lft, s, u, hy)), Pair.snd({HT.memn(b, ST.ids(s)) == False{} : Bool}, {HT.memn(b, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fw_s(b, 1n+i, lft, s, u, hb)), Pair.snd({HT.memn(1n+i, ST.ids(s)) == False{} : Bool}, {HT.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, fq_s(1n+i, lft, s, u, hBA)))
  +hu2 = Equal.trans(Bool, P.ctxok(~K, u, 1n+i, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft)), P.ctxok(~K, u, 1n+i, nl), True{}, AG.ctx_agr(~K, ~cmp, ~o, u, 1n+i, nl, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), agU), hu)
  +hs2 = rep_moved(~K, ~cmp, ~o, s, 1n+i, nl, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), agS, hs)
  L.and_intro(P.cok1(~K, P.FR{1n+i, lft, s}, y, P.top(u), RM.rotr_nl(K, nl, x, y, b, 1n+i, lft)), P.ctxok(~K, u, 1n+i, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft)), L.and_intro(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), y), P.top(u)), ST.rep(~K, s, 1n+i, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft))), h0, L.and_intro(ST.is_node(K, ST.nd(K, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft), 1n+i), ST.pk(Nat, lft, y, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), y), P.top(u)), ST.rep(~K, s, 1n+i, RM.rotr_nl(K, nl, x, y, b, 1n+i, lft)), rq, hs2)), hu2)

def rotr_ctx(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +y: Nat, +b: Nat, +hok: {P.ctxok(~K, c, x, nl) == True{} : Bool}, +hx: {HT.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hy: {HT.memn(y, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hb: {HT.memn(b, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hBA: {LST.nodupn(SC.append(Nat, P.before(c), P.after(c))) == True{} : Bool}) -> {P.ctxok(~K, c, y, RM.rotr_nl(K, nl, x, y, b, P.top(c), SP.dir(c))) == True{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{0n, +lft, +s}, +u}:
      Empty.absurd({P.ctxok(~K, Con{P.FR{0n, lft, s}, u}, y, RM.rotr_nl(K, nl, x, y, b, 0n, lft)) == True{} : Bool}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 0n), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 0n, nl)), L.and_left(P.cok1(~K, P.FR{0n, lft, s}, x, P.top(u), nl), P.ctxok(~K, u, 0n, nl), hok))))
    case Con{P.FR{1n+i, True{}, +s}, +u}:
      ctx_frame_r(~K, ~cmp, ~o, nl, x, y, b, i, True{}, s, u, hok, hx, hy, hb, hBA, DJ.mem_r(1n+i, P.before(u), Con{1n+i, SC.append(Nat, ST.ids(s), P.after(u))}, DJ.mem_hd(1n+i, SC.append(Nat, ST.ids(s), P.after(u)))))
    case Con{P.FR{1n+i, False{}, +s}, +u}:
      ctx_frame_r(~K, ~cmp, ~o, nl, x, y, b, i, False{}, s, u, hok, hx, hy, hb, hBA, DJ.mem_l(1n+i, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}})), P.after(u), DJ.mem_r(1n+i, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}}), DJ.mem_r(1n+i, ST.ids(s), Con{1n+i, Nil{}}, DJ.mem_hd(1n+i, Nil{})))))
