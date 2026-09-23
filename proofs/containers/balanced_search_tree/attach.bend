import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/order.bend as O
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./path.bend as P
import ./plug.bend as PG
import ./agree.bend as AG
import ./setters.bend as SE
import ./rotm.bend as RM
import ./rotn.bend as RN
import ./rot.bend as RT
import ./rotp.bend as RP
import ./fix.bend as FX
import ./dj.bend as DJ
import ./spath.bend as SP
import ../../lib/nat_list.bend as NL

# Attaching a new leaf where the search stopped: the node list agreeing with
# the old one on the tree's ids and holding the new red leaf x, attach links
# x under the path's parent on the path's side (or makes it the root); the
# path then leads to the leaf, the ids stay without repeats, the root stays
# black. (source: tools/generators/tm_hand/attach.src)


# the parent (or 0) is not the new id
def top_ne(~K: Data, +nl: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +hc0: {P.ctxok(~K, c, 0n, nl) == True{} : Bool}, +hx0: {Nat.is_lt(0n, x) == True{} : Bool}, +hxf: {NL.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}) -> {Nat.is_eq(P.top(c), x) == False{} : Bool}:
  match c:
    case Nil{}:
      RT.ne0(x, hx0)
    case Con{P.FR{+q, +lft, +s}, +u}:
      N.is_eq_sym_false(x, q, DJ.ne_nm(x, q, SC.append(Nat, P.before(Con{P.FR{q, lft, s}, u}), P.after(Con{P.FR{q, lft, s}, u})), hxf, FX.q_in(q, lft, s, u)))

# the leaf's links
def att_leaf(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +nla: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +k: K, +hc0: {P.ctxok(~K, c, 0n, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), P.after(c))) == True{} : Bool}, +hag: {AG.agr(~K, ~cmp, SC.append(Nat, P.before(c), P.after(c)), nl, nla) == True{} : Bool}, +hxn: {ST.nd(K, nla, x) == M.N{True{}, 0n, 0n, P.top(c), k} : M.Node<K>}, +hx0: {Nat.is_lt(0n, x) == True{} : Bool}, +hxf: {NL.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}) -> {ST.rep(~K, ST.TN{x, ST.TE{}, ST.TE{}}, P.top(c), SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c))) == True{} : Bool}:
  +e = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c)), x), SE.modp(K, ST.nd(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x), P.top(c)), SE.modp(K, M.N{True{}, 0n, 0n, P.top(c), k}, P.top(c)), RN.hitp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c)), L.subst(M.Node<K>, z => {SE.modp(K, ST.nd(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x), P.top(c)) == SE.modp(K, z, P.top(c)) : M.Node<K>}, ST.nd(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x), M.N{True{}, 0n, 0n, P.top(c), k}, Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x), ST.nd(K, nla, x), M.N{True{}, 0n, 0n, P.top(c), k}, RN.skipa(K, nla, P.top(c), x, SP.dir(c), x, top_ne(~K, nl, c, x, hc0, hx0, hxf)), hxn), {==}))
  RT.rep_intro(~K, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c)), x, ST.TE{}, ST.TE{}, P.top(c), hx0, L.subst(M.Node<K>, z => {ST.is_node(K, z, 0n, 0n, P.top(c)) == True{} : Bool}, M.N{True{}, 0n, 0n, P.top(c), k}, ST.nd(K, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c)), x), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c)), x), M.N{True{}, 0n, 0n, P.top(c), k}, e), L.and_intro(Nat.is_eq(0n, 0n), Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(P.top(c), P.top(c))), {==}, L.and_intro(Nat.is_eq(0n, 0n), Nat.is_eq(P.top(c), P.top(c)), {==}, N.is_eq_refl(P.top(c))))), {==}, {==})


# the parent's frame after attaching: the leaf on the path's side
def att_frame(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +nla: List<&2, M.Node<K>>, +x: Nat, +k: K, +i: Nat, +lft: Bool, +s: ST.Tr, +u: List<&2, P.Fr>, +hc0: {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, 0n, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == True{} : Bool}, +hags: {AG.agr(~K, ~cmp, ST.ids(s), nl, nla) == True{} : Bool}, +hagu: {AG.agr(~K, ~cmp, SC.append(Nat, P.before(u), P.after(u)), nl, nla) == True{} : Bool}, +hagq: {ST.nd(K, nl, 1n+i) == ST.nd(K, nla, 1n+i) : M.Node<K>}, +hq: {Nat.is_eq(x, 1n+i) == False{} : Bool}, +hxf: {NL.memn(x, SC.append(Nat, P.before(Con{P.FR{1n+i, lft, s}, u}), P.after(Con{P.FR{1n+i, lft, s}, u}))) == False{} : Bool}) -> {P.ctxok(~K, Con{P.FR{1n+i, lft, s}, u}, x, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i)) == True{} : Bool}:
  +hk = L.and_left(P.cok1(~K, P.FR{1n+i, lft, s}, 0n, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hc0)
  +hu = L.and_right(P.cok1(~K, P.FR{1n+i, lft, s}, 0n, P.top(u), nl), P.ctxok(~K, u, 1n+i, nl), hc0)
  +h0 = L.and_left(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk)
  +hqn = L.and_left(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +hs = L.and_right(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 1n+i, nl), L.and_right(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+i), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 1n+i, nl)), hk))
  +qs = Pair.fst({NL.memn(1n+i, ST.ids(s)) == False{} : Bool}, {NL.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, RT.fq_s(1n+i, lft, s, u, hnd))
  +qu = Pair.snd({NL.memn(1n+i, ST.ids(s)) == False{} : Bool}, {NL.memn(1n+i, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, RT.fq_s(1n+i, lft, s, u, hnd))
  +xs = Pair.fst({NL.memn(x, ST.ids(s)) == False{} : Bool}, {NL.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, RT.fw_s(x, 1n+i, lft, s, u, hxf))
  +xu = Pair.snd({NL.memn(x, ST.ids(s)) == False{} : Bool}, {NL.memn(x, SC.append(Nat, P.before(u), P.after(u))) == False{} : Bool}, RT.fw_s(x, 1n+i, lft, s, u, hxf))
  +e1 = Equal.trans(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), 1n+i), ST.nd(K, RM.attn(K, nla, 1n+i, x, lft), 1n+i), RN.moda(K, ST.nd(K, nl, 1n+i), x, lft), RN.skipp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i, 1n+i, hq), Equal.trans(M.Node<K>, ST.nd(K, RM.attn(K, nla, 1n+i, x, lft), 1n+i), RN.moda(K, ST.nd(K, nla, 1n+i), x, lft), RN.moda(K, ST.nd(K, nl, 1n+i), x, lft), RN.hita(K, nla, i, x, lft), L.subst(M.Node<K>, z => {RN.moda(K, ST.nd(K, nla, 1n+i), x, lft) == RN.moda(K, z, x, lft) : M.Node<K>}, ST.nd(K, nla, 1n+i), ST.nd(K, nl, 1n+i), Equal.sym(M.Node<K>, ST.nd(K, nl, 1n+i), ST.nd(K, nla, 1n+i), hagq), {==})))
  +rq = L.subst(M.Node<K>, z => {ST.is_node(K, z, ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)) == True{} : Bool}, RN.moda(K, ST.nd(K, nl, 1n+i), x, lft), ST.nd(K, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), 1n+i), Equal.sym(M.Node<K>, ST.nd(K, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), 1n+i), RN.moda(K, ST.nd(K, nl, 1n+i), x, lft), e1), RN.isn_a(K, ST.nd(K, nl, 1n+i), lft, 0n, ST.rid(s), P.top(u), x, hqn))
  +hs2 = RT.rep_moved(~K, ~cmp, ~o, s, 1n+i, nl, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), AG.agr_trans(~K, ~cmp, ~o, ST.ids(s), nl, RM.attn(K, nla, 1n+i, x, lft), SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), AG.agr_trans(~K, ~cmp, ~o, ST.ids(s), nl, nla, RM.attn(K, nla, 1n+i, x, lft), hags, RN.attn_agr(~K, ~cmp, ~o, ST.ids(s), nla, 1n+i, x, lft, qs)), SE.setp_agr(~K, ~cmp, ~o, ST.ids(s), RM.attn(K, nla, 1n+i, x, lft), x, 1n+i, xs)), hs)
  +hu2 = Equal.trans(Bool, P.ctxok(~K, u, 1n+i, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i)), P.ctxok(~K, u, 1n+i, nl), True{}, AG.ctx_agr(~K, ~cmp, ~o, u, 1n+i, nl, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), AG.agr_trans(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), nl, RM.attn(K, nla, 1n+i, x, lft), SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), AG.agr_trans(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), nl, nla, RM.attn(K, nla, 1n+i, x, lft), hagu, RN.attn_agr(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), nla, 1n+i, x, lft, qu)), SE.setp_agr(~K, ~cmp, ~o, SC.append(Nat, P.before(u), P.after(u)), RM.attn(K, nla, 1n+i, x, lft), x, 1n+i, xu))), hu)
  L.and_intro(P.cok1(~K, P.FR{1n+i, lft, s}, x, P.top(u), SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i)), P.ctxok(~K, u, 1n+i, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i)), L.and_intro(Nat.is_lt(0n, 1n+i), Bool.and(ST.is_node(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i))), h0, L.and_intro(ST.is_node(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i), 1n+i), ST.pk(Nat, lft, x, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), x), P.top(u)), ST.rep(~K, s, 1n+i, SE.setp(K, RM.attn(K, nla, 1n+i, x, lft), x, 1n+i)), rq, hs2)), hu2)


# the path leads to the leaf
def att_ctx(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +nla: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +k: K, +hc0: {P.ctxok(~K, c, 0n, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), P.after(c))) == True{} : Bool}, +hag: {AG.agr(~K, ~cmp, SC.append(Nat, P.before(c), P.after(c)), nl, nla) == True{} : Bool}, +hxn: {ST.nd(K, nla, x) == M.N{True{}, 0n, 0n, P.top(c), k} : M.Node<K>}, +hx0: {Nat.is_lt(0n, x) == True{} : Bool}, +hxf: {NL.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}) -> {P.ctxok(~K, c, x, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c))) == True{} : Bool}:
  match c:
    case Nil{}:
      {==}
    case Con{P.FR{0n, +lft, +s}, +u}:
      Empty.absurd({P.ctxok(~K, Con{P.FR{0n, lft, s}, u}, x, SE.setp(K, RM.attn(K, nla, 0n, x, lft), x, 0n)) == True{} : Bool}, L.false_true(L.and_left(Nat.is_lt(0n, 0n), Bool.and(ST.is_node(K, ST.nd(K, nl, 1n+0n), ST.pk(Nat, lft, 0n, ST.rid(s)), ST.pk(Nat, lft, ST.rid(s), 0n), P.top(u)), ST.rep(~K, s, 0n, nl)), L.and_left(P.cok1(~K, P.FR{0n, lft, s}, 0n, P.top(u), nl), P.ctxok(~K, u, 0n, nl), hc0))))
    case Con{P.FR{1n+i, True{}, +s}, +u}:
      +h1 = AG.agr_r(~K, ~cmp, ~o, P.before(u), Con{1n+i, SC.append(Nat, ST.ids(s), P.after(u))}, nl, nla, hag)
      +h2 = L.and_right(AG.ndeq(~K, ~cmp, ST.nd(K, nl, 1n+i), ST.nd(K, nla, 1n+i)), AG.agr(~K, ~cmp, SC.append(Nat, ST.ids(s), P.after(u)), nl, nla), h1)
      +hq = N.is_eq_sym_false(x, 1n+i, DJ.ne_nm(x, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, True{}, s}, u}), P.after(Con{P.FR{1n+i, True{}, s}, u})), hxf, FX.q_in(1n+i, True{}, s, u)))
      att_frame(~K, ~cmp, ~o, nl, nla, x, k, i, True{}, s, u, hc0, hnd, AG.agr_l(~K, ~cmp, ~o, ST.ids(s), P.after(u), nl, nla, h2), AG.agr_app(~K, ~cmp, ~o, P.before(u), P.after(u), nl, nla, AG.agr_l(~K, ~cmp, ~o, P.before(u), Con{1n+i, SC.append(Nat, ST.ids(s), P.after(u))}, nl, nla, hag), AG.agr_r(~K, ~cmp, ~o, ST.ids(s), P.after(u), nl, nla, h2)), AG.agr_head(~K, ~cmp, ~o, 1n+i, SC.append(Nat, ST.ids(s), P.after(u)), nl, nla, h1), N.is_eq_sym_false(1n+i, x, hq), hxf)
    case Con{P.FR{1n+i, False{}, +s}, +u}:
      +h1 = AG.agr_l(~K, ~cmp, ~o, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}})), P.after(u), nl, nla, hag)
      +h2 = AG.agr_r(~K, ~cmp, ~o, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}}), nl, nla, h1)
      +hq = N.is_eq_sym_false(x, 1n+i, DJ.ne_nm(x, 1n+i, SC.append(Nat, P.before(Con{P.FR{1n+i, False{}, s}, u}), P.after(Con{P.FR{1n+i, False{}, s}, u})), hxf, FX.q_in(1n+i, False{}, s, u)))
      att_frame(~K, ~cmp, ~o, nl, nla, x, k, i, False{}, s, u, hc0, hnd, AG.agr_l(~K, ~cmp, ~o, ST.ids(s), Con{1n+i, Nil{}}, nl, nla, h2), AG.agr_app(~K, ~cmp, ~o, P.before(u), P.after(u), nl, nla, AG.agr_l(~K, ~cmp, ~o, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}}), nl, nla, h1), AG.agr_r(~K, ~cmp, ~o, SC.append(Nat, P.before(u), SC.append(Nat, ST.ids(s), Con{1n+i, Nil{}})), P.after(u), nl, nla, hag)), AG.agr_head(~K, ~cmp, ~o, 1n+i, Nil{}, nl, nla, AG.agr_r(~K, ~cmp, ~o, ST.ids(s), Con{1n+i, Nil{}}, nl, nla, h2)), N.is_eq_sym_false(1n+i, x, hq), hxf)

# ---- the root stays black ----

def agr_mem_c(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +j: Nat, +t: List<&2, Nat>, +y: Nat, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +h: {AG.agr(~K, ~cmp, Con{j, t}, a, b) == True{} : Bool}, +e: Bool, +he: {Nat.is_eq(j, y) == e : Bool}, +hm: {Bool.or(e, NL.memn(y, t)) == True{} : Bool}, ih: @+hmt: {NL.memn(y, t) == True{} : Bool} -> {ST.nd(K, a, y) == ST.nd(K, b, y) : M.Node<K>}) -> {ST.nd(K, a, y) == ST.nd(K, b, y) : M.Node<K>}:
  match e:
    case True{}:
      +ej = N.eq_from_is_eq(j, y, he)
      L.subst(Nat, z => {ST.nd(K, a, z) == ST.nd(K, b, z) : M.Node<K>}, j, y, ej, AG.agr_head(~K, ~cmp, ~o, j, t, a, b, h))
    case False{}:
      ih(hm)

# agreeing lists agree at a member
def agr_mem(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +xs: List<&2, Nat>, +y: Nat, +a: List<&2, M.Node<K>>, +b: List<&2, M.Node<K>>, +h: {AG.agr(~K, ~cmp, xs, a, b) == True{} : Bool}, +hm: {NL.memn(y, xs) == True{} : Bool}) -> {ST.nd(K, a, y) == ST.nd(K, b, y) : M.Node<K>}:
  match xs:
    case Nil{}:
      Empty.absurd({ST.nd(K, a, y) == ST.nd(K, b, y) : M.Node<K>}, L.false_true(hm))
    case Con{+j, +t}:
      agr_mem_c(~K, ~cmp, ~o, j, t, y, a, b, h, Nat.is_eq(j, y), {==}, hm, hmt => agr_mem(~K, ~cmp, ~o, t, y, a, b, L.and_right(AG.ndeq(~K, ~cmp, ST.nd(K, a, j), ST.nd(K, b, j)), AG.agr(~K, ~cmp, t, a, b), h), hmt))

def red_attn(-K: Data, +nl: List<&2, M.Node<K>>, +q: Nat, +y: Nat, +dir: Bool, +j: Nat) -> {ST.is_red(K, ST.nd(K, RM.attn(K, nl, q, y, dir), j)) == ST.is_red(K, ST.nd(K, nl, j)) : Bool}:
  match q dir:
    case 0n +dir:
      {==}
    case 1n+i True{}:
      SE.red_setl(K, nl, 1n+i, y, j)
    case 1n+i False{}:
      SE.red_setr(K, nl, 1n+i, y, j)


def att_rb(~K: Data, ~cmp: K -> K -> Cmp, ~o: O.Order(~K, ~cmp), +nl: List<&2, M.Node<K>>, +nla: List<&2, M.Node<K>>, +c: List<&2, P.Fr>, +x: Nat, +k: K, +hc0: {P.ctxok(~K, c, 0n, nl) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), P.after(c))) == True{} : Bool}, +hag: {AG.agr(~K, ~cmp, SC.append(Nat, P.before(c), P.after(c)), nl, nla) == True{} : Bool}, +hxn: {ST.nd(K, nla, x) == M.N{True{}, 0n, 0n, P.top(c), k} : M.Node<K>}, +hx0: {Nat.is_lt(0n, x) == True{} : Bool}, +hxf: {NL.memn(x, SC.append(Nat, P.before(c), P.after(c))) == False{} : Bool}, +hrb: {ST.root_black(~K, PG.plug(c, ST.TE{}), nl) == True{} : Bool}) -> {Bool.or(ST.root_black(~K, PG.plug(c, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c))), FX.isnil(c)) == True{} : Bool}:
  match c:
    case Nil{}:
      NL.or_true_b(ST.root_black(~K, ST.TN{x, ST.TE{}, ST.TE{}}, SE.setp(K, RM.attn(K, nla, P.top(c), x, SP.dir(c)), x, P.top(c))))
    case Con{P.FR{+q, True{}, +s}, +u}:
      +mR = FX.rid_in(u, q, True{}, s, ST.TE{})
      +e1 = Equal.trans(Bool, ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, RM.attn(K, nla, q, x, True{}), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), SE.red_setp(K, RM.attn(K, nla, q, x, True{}), x, q, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))), Equal.trans(Bool, ST.is_red(K, ST.nd(K, RM.attn(K, nla, q, x, True{}), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nla, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), red_attn(K, nla, q, x, True{}, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))), L.subst(M.Node<K>, z => {ST.is_red(K, z) == ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))) : Bool}, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))), ST.nd(K, nla, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))), agr_mem(~K, ~cmp, ~o, SC.append(Nat, P.before(Con{P.FR{q, True{}, s}, u}), P.after(Con{P.FR{q, True{}, s}, u})), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})), nl, nla, hag, mR), {==})))
      +v1 = L.subst(Nat, z => {ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q)) == Bool.not(ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q), z))) : Bool}, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}})), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})), RP.rid_plug_tn(u, q, ST.TN{x, ST.TE{}, ST.TE{}}, s, ST.TE{}, s), FX.rb_rid(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q)))
      +v2 = L.subst(Bool, z => {ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q)) == Bool.not(z) : Bool}, ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q), ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{})))), e1, v1)
      +v3 = Equal.trans(Bool, ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q)), Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))))), True{}, v2, Equal.trans(Bool, Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))))), ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}), nl), True{}, Equal.sym(Bool, ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}), nl), Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}))))), FX.rb_rid(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TE{}), nl)), hrb))
      FX.or_lt(ST.root_black(~K, PG.plug(Con{P.FR{q, True{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, True{}), x, q)), False{}, v3)
    case Con{P.FR{+q, False{}, +s}, +u}:
      +mR = FX.rid_in(u, q, False{}, s, ST.TE{})
      +e1 = Equal.trans(Bool, ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, RM.attn(K, nla, q, x, False{}), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), SE.red_setp(K, RM.attn(K, nla, q, x, False{}), x, q, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))), Equal.trans(Bool, ST.is_red(K, ST.nd(K, RM.attn(K, nla, q, x, False{}), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nla, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), red_attn(K, nla, q, x, False{}, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))), L.subst(M.Node<K>, z => {ST.is_red(K, z) == ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))) : Bool}, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))), ST.nd(K, nla, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))), agr_mem(~K, ~cmp, ~o, SC.append(Nat, P.before(Con{P.FR{q, False{}, s}, u}), P.after(Con{P.FR{q, False{}, s}, u})), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})), nl, nla, hag, mR), {==})))
      +v1 = L.subst(Nat, z => {ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q)) == Bool.not(ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q), z))) : Bool}, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}})), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})), RP.rid_plug_tn(u, q, s, ST.TN{x, ST.TE{}, ST.TE{}}, s, ST.TE{}), FX.rb_rid(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q)))
      +v2 = L.subst(Bool, z => {ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q)) == Bool.not(z) : Bool}, ST.is_red(K, ST.nd(K, SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q), ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{})))), e1, v1)
      +v3 = Equal.trans(Bool, ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q)), Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))))), True{}, v2, Equal.trans(Bool, Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))))), ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}), nl), True{}, Equal.sym(Bool, ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}), nl), Bool.not(ST.is_red(K, ST.nd(K, nl, ST.rid(PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}))))), FX.rb_rid(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TE{}), nl)), hrb))
      FX.or_lt(ST.root_black(~K, PG.plug(Con{P.FR{q, False{}, s}, u}, ST.TN{x, ST.TE{}, ST.TE{}}), SE.setp(K, RM.attn(K, nla, q, x, False{}), x, q)), False{}, v3)
