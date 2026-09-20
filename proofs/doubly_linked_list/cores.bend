import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../src/balanced_search_tree.bend as B
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ../../types/balanced_search_tree.bend as BE
import ./nodes.bend as NS
import ./links.bend as LK
import ./facts.bend as F

# The three structural updates: link a fresh node between two runs, unlink
# a node, overwrite a value. Each re-establishes the whole invariant F.Good
# for the new item sequence.

def ok_fst_mid(+xs: List<&2, Nat>, +n: Nat, +ys: List<&2, Nat>) -> {F.okM(LK.fst(ys, None{}), SC.append(Nat, xs, Con{n, ys})) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      F.mem_appR(j, xs, Con{n, Con{j, t}}, L.subst(Bool, z => {Bool.or(Nat.is_eq(j, n), z) == True{} : Bool}, True{}, NS.mem(j, Con{j, t}), Equal.sym(Bool, NS.mem(j, Con{j, t}), True{}, F.mem_self(j, t)), LK.or_true(Nat.is_eq(j, n))))

def link_core(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +Q: List<&2, E.Item<T>>, +x: T, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, LK.fst(NS.ids(T, Q), None{})), lkQ: LK.lk(T, nodes, Q, LK.lst(NS.ids(T, P), None{}), None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Q)), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Q)), fresh) == True{} : Bool}) -> F.Good(T, D.link(T, nodes, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{}), fresh, x), D.end_link(LK.lst(NS.ids(T, P), None{}), fresh, head), D.end_link(LK.fst(NS.ids(T, Q), None{}), fresh, tail), 1n+count, 1n+fresh, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})):
  -NL = List<&2, Nat>
  +lp = NS.ids(T, P)
  +lq = NS.ids(T, Q)
  +a0 = LK.lst(lp, None{})
  +b0 = LK.fst(lq, None{})
  +nd = {D.N{x, a0, b0} : D.Node<T>}
  +ms1 = D.put(T, nodes, fresh, nd)
  +ms2 = D.set_prev(T, ms1, b0, Some{fresh})
  +g1 = NS.put_inv(T, nodes, fresh, nd, g)
  +g2 = NS.sp_inv(T, ms1, b0, Some{fresh}, g1)
  +ipq = NS.ids_app(T, P, Q)
  +ipnq = NS.ids_app(T, P, Con{E.Item{fresh, x}, Q})
  +dpq = L.subst(NL, z => {LK.dist(z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq, d)
  +mn = L.subst(NL, z => {NS.mem(fresh, z) == False{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq, F.notmem_lt(NS.ids(T, SC.append(E.Item<T>, P, Q)), fresh, lt))
  +mP = LK.or_false_l(NS.mem(fresh, lp), NS.mem(fresh, lq), F.mem_split(fresh, lp, lq, mn))
  +mQ = LK.or_false_r(NS.mem(fresh, lp), NS.mem(fresh, lq), F.mem_split(fresh, lp, lq, mn))
  +en3 = Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, D.set_next(T, ms2, a0, Some{fresh}), fresh), D.node(T, ms2, fresh), Some{nd},
    F.node_sn_skip(T, ms2, a0, Some{fresh}, fresh, lp, g2, F.memM_lst(lp), mP),
    Equal.trans(Maybe<&2, D.Node<T>>, D.node(T, ms2, fresh), D.node(T, ms1, fresh), Some{nd},
      F.node_sp_skip(T, ms1, b0, Some{fresh}, fresh, lq, g1, F.ok_fst(Nil{}, lq), mQ),
      NS.get_put_same(T, nodes, fresh, nd, g)))
  +al1 = F.allin_ext(T, NS.nabs(T, nodes), lp, fresh, lq, L.subst(NL, z => {NS.allin(T, NS.nabs(T, nodes), z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq, a))
  +al2 = NS.allin_put(T, nodes, fresh, nd, SC.append(Nat, lp, Con{fresh, lq}), g, al1, F.mem_appR(fresh, lp, Con{fresh, lq}, F.mem_self(fresh, lq)))
  +al3 = F.allin_sp(T, ms1, b0, Some{fresh}, SC.append(Nat, lp, Con{fresh, lq}), g1, al2, ok_fst_mid(lp, fresh, lq))
  +al4 = F.allin_sn(T, ms2, a0, Some{fresh}, SC.append(Nat, lp, Con{fresh, lq}), g2, al3, F.ok_lst(lp, Con{fresh, lq}))
  (NS.sn_inv(T, ms2, a0, Some{fresh}, g2),
   (LK.join(T, D.set_next(T, ms2, a0, Some{fresh}), P, Con{E.Item{fresh, x}, Q}, None{}, None{},
      LK.retarget_last(T, ms2, P, None{}, b0, Some{fresh}, g2, F.dist_l(lp, lq, dpq),
        LK.frame_spM(T, ms1, P, None{}, b0, b0, Some{fresh}, g1, F.disj_fst(lp, lq, dpq),
          LK.frame_put(T, nodes, P, None{}, b0, fresh, nd, g, mP, lkP))),
      (en3,
       LK.frame_snM(T, ms2, Q, Some{fresh}, None{}, a0, Some{fresh}, g2, F.disj_lst(lp, lq, dpq),
         LK.retarget_first(T, ms1, Q, a0, None{}, Some{fresh}, g1, F.dist_r(lp, lq, dpq),
           LK.frame_put(T, nodes, Q, a0, None{}, fresh, nd, g, mQ, lkQ))))),
    (F.head_link(T, P, Q, fresh, x, head, eh),
     (F.tail_link(T, P, Q, fresh, x, tail, et),
      (Equal.trans(Nat, 1n+count, 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), Equal.cong(Nat, Nat, z => 1n+z, count, SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), ec), Equal.sym(Nat, SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), F.len_mid(T, P, E.Item{fresh, x}, Q))),
       (L.subst(NL, z => {LK.dist(z) == True{} : Bool}, SC.append(Nat, lp, Con{fresh, lq}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), SC.append(Nat, lp, Con{fresh, lq}), ipnq), F.dist_mid(lp, fresh, lq, dpq, mn)),
        (L.subst(NL, z => {NS.allin(T, NS.nabs(T, D.set_next(T, ms2, a0, Some{fresh})), z) == True{} : Bool}, SC.append(Nat, lp, Con{fresh, lq}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), SC.append(Nat, lp, Con{fresh, lq}), ipnq), al4),
         L.subst(NL, z => {F.allLt(z, 1n+fresh) == True{} : Bool}, SC.append(Nat, lp, Con{fresh, lq}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{fresh, x}, Q})), SC.append(Nat, lp, Con{fresh, lq}), ipnq), F.lt_mid(lp, lq, fresh, L.subst(NL, z => {F.allLt(z, fresh) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq, lt))))))))))

def unlink_core(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +h: Nat, +v: T, +Q: List<&2, E.Item<T>>, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{h}), lkQ: LK.lk(T, nodes, Q, Some{h}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), fresh) == True{} : Bool}) -> F.Good(T, D.unlink(T, nodes, h, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})), D.end_unlink(LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{}), head), D.end_unlink(LK.fst(NS.ids(T, Q), None{}), LK.lst(NS.ids(T, P), None{}), tail), Nat.sub(count, 1n), fresh, SC.append(E.Item<T>, P, Q)):
  -NL = List<&2, Nat>
  +lp = NS.ids(T, P)
  +lq = NS.ids(T, Q)
  +a0 = LK.lst(lp, None{})
  +b0 = LK.fst(lq, None{})
  +ms1 = D.drop(T, nodes, h)
  +ms2 = D.set_prev(T, ms1, b0, a0)
  +g1 = NS.drop_inv(T, nodes, h, g)
  +g2 = NS.sp_inv(T, ms1, b0, a0, g1)
  +iphq = NS.ids_app(T, P, Con{E.Item{h, v}, Q})
  +ipq = NS.ids_app(T, P, Q)
  +dL = L.subst(NL, z => {LK.dist(z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), SC.append(Nat, lp, Con{h, lq}), iphq, d)
  +mP = F.disj(lp, Con{h, lq}, h, dL, F.mem_self(h, lq))
  +mQ = LK.dist_head(h, lq, F.dist_r(lp, Con{h, lq}, dL))
  +dpq = F.dist_del(lp, h, lq, dL)
  +al1 = L.subst(List<&2, BE.Entry<Nat, D.Node<T>>>, z => {NS.allin(T, z, NS.ids(T, SC.append(E.Item<T>, P, Q))) == True{} : Bool}, S.del(~Nat, ~Nat.cmp, D.Node<T>, h, NS.nabs(T, nodes)), NS.nabs(T, ms1), Equal.sym(List<&2, BE.Entry<Nat, D.Node<T>>>, NS.nabs(T, ms1), S.del(~Nat, ~Nat.cmp, D.Node<T>, h, NS.nabs(T, nodes)), NS.drop_abs(T, nodes, h, g)), NS.allin_del(T, NS.nabs(T, nodes), h, P, v, Q, a))
  +al1b = L.subst(NL, z => {NS.allin(T, NS.nabs(T, ms1), z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq, al1)
  +al2 = F.allin_sp(T, ms1, b0, a0, SC.append(Nat, lp, lq), g1, al1b, F.ok_fst(lp, lq))
  +al3 = F.allin_sn(T, ms2, a0, b0, SC.append(Nat, lp, lq), g2, al2, F.ok_lst(lp, lq))
  +en = F.len_mid(T, P, E.Item{h, v}, Q)
  (NS.sn_inv(T, ms2, a0, b0, g2),
   (LK.join(T, D.set_next(T, ms2, a0, b0), P, Q, None{}, None{},
      LK.retarget_last(T, ms2, P, None{}, Some{h}, b0, g2, F.dist_l(lp, lq, dpq),
        LK.frame_spM(T, ms1, P, None{}, Some{h}, b0, a0, g1, F.disj_fst(lp, lq, dpq),
          LK.frame_drop(T, nodes, P, None{}, Some{h}, h, g, mP, lkP))),
      LK.frame_snM(T, ms2, Q, a0, None{}, a0, b0, g2, F.disj_lst(lp, lq, dpq),
        LK.retarget_first(T, ms1, Q, Some{h}, None{}, a0, g1, F.dist_r(lp, lq, dpq),
          LK.frame_drop(T, nodes, Q, Some{h}, None{}, h, g, mQ, lkQ)))),
    (F.head_unlink(T, P, h, v, Q, head, eh),
     (F.tail_unlink(T, P, h, v, Q, tail, et),
      (Equal.trans(Nat, Nat.sub(count, 1n), Nat.sub(1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), 1n), SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)),
         Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), count, 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), Equal.trans(Nat, count, SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), ec, en)),
         N.sub_zero(SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)))),
       (L.subst(NL, z => {LK.dist(z) == True{} : Bool}, SC.append(Nat, lp, lq), NS.ids(T, SC.append(E.Item<T>, P, Q)), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq), dpq),
        (L.subst(NL, z => {NS.allin(T, NS.nabs(T, D.set_next(T, ms2, a0, b0)), z) == True{} : Bool}, SC.append(Nat, lp, lq), NS.ids(T, SC.append(E.Item<T>, P, Q)), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq), al3),
         L.subst(NL, z => {F.allLt(z, fresh) == True{} : Bool}, SC.append(Nat, lp, lq), NS.ids(T, SC.append(E.Item<T>, P, Q)), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Q)), SC.append(Nat, lp, lq), ipq), F.lt_del(lp, h, lq, fresh, L.subst(NL, z => {F.allLt(z, fresh) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{h, v}, Q})), SC.append(Nat, lp, Con{h, lq}), iphq, lt))))))))))

def set_core(-T: Data, +nodes: B.OrdMap<Nat, D.Node<T>>, +head: Maybe<&2, Nat>, +tail: Maybe<&2, Nat>, +count: Nat, +fresh: Nat, +P: List<&2, E.Item<T>>, +i: Nat, +v: T, +Q: List<&2, E.Item<T>>, +x: T, +g: {NS.ninv(T, nodes) == True{} : Bool}, lkP: LK.lk(T, nodes, P, None{}, Some{i}), lkQ: LK.lk(T, nodes, Q, Some{i}, None{}), +eh: {head == LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), None{}) : Maybe<&2, Nat>}, +et: {tail == LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), None{}) : Maybe<&2, Nat>}, +ec: {count == SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})) : Nat}, +d: {LK.dist(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q}))) == True{} : Bool}, +a: {NS.allin(T, NS.nabs(T, nodes), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q}))) == True{} : Bool}, +lt: {F.allLt(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), fresh) == True{} : Bool}) -> F.Good(T, D.put(T, nodes, i, D.N{x, LK.lst(NS.ids(T, P), None{}), LK.fst(NS.ids(T, Q), None{})}), head, tail, count, fresh, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})):
  -NL = List<&2, Nat>
  +lp = NS.ids(T, P)
  +lq = NS.ids(T, Q)
  +nd = {D.N{x, LK.lst(lp, None{}), LK.fst(lq, None{})} : D.Node<T>}
  +iv = NS.ids_app(T, P, Con{E.Item{i, v}, Q})
  +ie = Equal.trans(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), SC.append(Nat, lp, Con{i, lq}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids_app(T, P, Con{E.Item{i, x}, Q}), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), SC.append(Nat, lp, Con{i, lq}), iv))
  +dL = L.subst(NL, z => {LK.dist(z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), SC.append(Nat, lp, Con{i, lq}), iv, d)
  +mP = F.disj(lp, Con{i, lq}, i, dL, F.mem_self(i, lq))
  +mQ = LK.dist_head(i, lq, F.dist_r(lp, Con{i, lq}, dL))
  +mi = L.subst(NL, z => {NS.mem(i, z) == True{} : Bool}, SC.append(Nat, lp, Con{i, lq}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), SC.append(Nat, lp, Con{i, lq}), iv), F.mem_appR(i, lp, Con{i, lq}, F.mem_self(i, lq)))
  (NS.put_inv(T, nodes, i, nd, g),
   (LK.join(T, D.put(T, nodes, i, nd), P, Con{E.Item{i, x}, Q}, None{}, None{},
      LK.frame_put(T, nodes, P, None{}, Some{i}, i, nd, g, mP, lkP),
      (NS.get_put_same(T, nodes, i, nd, g), LK.frame_put(T, nodes, Q, Some{i}, None{}, i, nd, g, mQ, lkQ))),
    (Equal.trans(Maybe<&2, Nat>, head, LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), None{}), LK.fst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), None{}), eh, Equal.cong(NL, Maybe<&2, Nat>, z => LK.fst(z, None{}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), ie))),
     (Equal.trans(Maybe<&2, Nat>, tail, LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), None{}), LK.lst(NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), None{}), et, Equal.cong(NL, Maybe<&2, Nat>, z => LK.lst(z, None{}), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), ie))),
      (Equal.trans(Nat, count, 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.trans(Nat, count, SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), ec, F.len_mid(T, P, E.Item{i, v}, Q)), Equal.sym(Nat, SC.length(E.Item<T>, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), 1n+SC.length(E.Item<T>, SC.append(E.Item<T>, P, Q)), F.len_mid(T, P, E.Item{i, x}, Q))),
       (L.subst(NL, z => {LK.dist(z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), ie), d),
        (L.subst(NL, z => {NS.allin(T, NS.nabs(T, D.put(T, nodes, i, nd)), z) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), ie), NS.allin_put(T, nodes, i, nd, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), g, a, mi)),
         L.subst(NL, z => {F.allLt(z, fresh) == True{} : Bool}, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), Equal.sym(NL, NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, x}, Q})), NS.ids(T, SC.append(E.Item<T>, P, Con{E.Item{i, v}, Q})), ie), lt))))))))
