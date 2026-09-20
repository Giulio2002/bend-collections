import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../lib/order.bend as O
import ../../spec/common.bend as SC
import ../../spec/binary_heap.bend as S
import ../../src/binary_heap.bend as H
import ./multiset.bend as M
import ./tree.bend as TR

# The heap tree operations preserve the multiset (TR.ab) and heap order (TR.ho).

# ---- Braun insertion ----

def hins_ab_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +y: A, +l: H.Tree<A>, +r: H.Tree<A>, +acc: List<&2, A>, +b: Bool, +eb: {S.le(~A, ~cmp, x, y) == b : Bool}, +ih: {TR.ab(~A, ~cmp, H.ins(~A, ~cmp, r, H.larger(A, x, y, b)), TR.ab(~A, ~cmp, l, acc)) == S.ins(~A, ~cmp, H.larger(A, x, y, b), TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, l, acc))) : List<&2, A>}) -> {TR.ab(~A, ~cmp, H.ins(~A, ~cmp, H.Node{y, l, r}, x), acc) == S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, H.Node{y, l, r}, acc)) : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(Bool, S.le(~A, ~cmp, x, y), True{}, eb) : {S.ins(~A, ~cmp, H.smaller(A, x, y, _), TR.ab(~A, ~cmp, H.ins(~A, ~cmp, r, H.larger(A, x, y, _)), TR.ab(~A, ~cmp, l, acc))) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, r, y), TR.ab(~A, ~cmp, l, acc)), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, l, acc))), ih) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      %TR.ab_comm(~A, ~cmp, ~o, l, r, acc) : {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, _)) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      {==}
    case False{}:
      %Equal.sym(Bool, S.le(~A, ~cmp, x, y), False{}, eb) : {S.ins(~A, ~cmp, H.smaller(A, x, y, _), TR.ab(~A, ~cmp, H.ins(~A, ~cmp, r, H.larger(A, x, y, _)), TR.ab(~A, ~cmp, l, acc))) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, r, x), TR.ab(~A, ~cmp, l, acc)), S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, l, acc))), ih) : {S.ins(~A, ~cmp, y, _) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      %TR.ab_comm(~A, ~cmp, ~o, l, r, acc) : {S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, x, _)) == S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, y, x, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)))

def hins_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: H.Tree<A>, +x: A, +acc: List<&2, A>) -> {TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), acc) == S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, acc)) : List<&2, A>}:
  match t:
    case H.Leaf{}:
      {==}
    case H.Node{+y, +l, +r}:
      hins_ab_c(~A, ~cmp, ~o, x, y, l, r, acc, S.le(~A, ~cmp, x, y), {==}, hins_ab(~A, ~cmp, ~o, r, H.larger(A, x, y, S.le(~A, ~cmp, x, y)), TR.ab(~A, ~cmp, l, acc)))

def allt_hins(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +t: H.Tree<A>, +x: A) -> {TR.allt(~A, ~cmp, z, H.ins(~A, ~cmp, t, x)) == Bool.and(S.le(~A, ~cmp, z, x), TR.allt(~A, ~cmp, z, t)) : Bool}:
  %Equal.sym(Bool, TR.allt(~A, ~cmp, z, H.ins(~A, ~cmp, t, x)), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{})), TR.allt_ab(~A, ~cmp, ~o, z, H.ins(~A, ~cmp, t, x))) : {_ == Bool.and(S.le(~A, ~cmp, z, x), TR.allt(~A, ~cmp, z, t)) : Bool}
  %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.ins(~A, ~cmp, t, x), Nil{}), S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, Nil{})), hins_ab(~A, ~cmp, ~o, t, x, Nil{})) : {M.all_ge(~A, ~cmp, z, _) == Bool.and(S.le(~A, ~cmp, z, x), TR.allt(~A, ~cmp, z, t)) : Bool}
  %Equal.sym(Bool, M.all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, t, Nil{}))), Bool.and(S.le(~A, ~cmp, z, x), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, t, Nil{}))), M.all_ge_ins(~A, ~cmp, ~o, z, x, TR.ab(~A, ~cmp, t, Nil{}))) : {_ == Bool.and(S.le(~A, ~cmp, z, x), TR.allt(~A, ~cmp, z, t)) : Bool}
  %Equal.sym(Bool, TR.allt(~A, ~cmp, z, t), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, t, Nil{})), TR.allt_ab(~A, ~cmp, ~o, z, t)) : {Bool.and(S.le(~A, ~cmp, z, x), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, t, Nil{}))) == Bool.and(S.le(~A, ~cmp, z, x), _) : Bool}
  {==}

def hins_ho_c(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +y: A, +l: H.Tree<A>, +r: H.Tree<A>, +h: {TR.ho(~A, ~cmp, H.Node{y, l, r}) == True{} : Bool}, +b: Bool, +eb: {S.le(~A, ~cmp, x, y) == b : Bool}, +ih: {TR.ho(~A, ~cmp, H.ins(~A, ~cmp, r, H.larger(A, x, y, b))) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.ins(~A, ~cmp, H.Node{y, l, r}, x)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, S.le(~A, ~cmp, x, y), True{}, eb) : {TR.ho(~A, ~cmp, H.Node{H.smaller(A, x, y, _), H.ins(~A, ~cmp, r, H.larger(A, x, y, _)), l}) == True{} : Bool}
      TR.ho_mk(~A, ~cmp, x, H.ins(~A, ~cmp, r, y), l,
        L.subst(Bool, c => {c == True{} : Bool}, Bool.and(S.le(~A, ~cmp, x, y), TR.allt(~A, ~cmp, x, r)), TR.allt(~A, ~cmp, x, H.ins(~A, ~cmp, r, y)), Equal.sym(Bool, TR.allt(~A, ~cmp, x, H.ins(~A, ~cmp, r, y)), Bool.and(S.le(~A, ~cmp, x, y), TR.allt(~A, ~cmp, x, r)), allt_hins(~A, ~cmp, ~o, x, r, y)),
          L.and_intro(S.le(~A, ~cmp, x, y), TR.allt(~A, ~cmp, x, r), eb, TR.allt_mono(~A, ~cmp, ~o, x, y, r, eb, TR.ho_r(~A, ~cmp, y, l, r, h)))),
        TR.allt_mono(~A, ~cmp, ~o, x, y, l, eb, TR.ho_l(~A, ~cmp, y, l, r, h)),
        ih, TR.ho_hl(~A, ~cmp, y, l, r, h))
    case False{}:
      %Equal.sym(Bool, S.le(~A, ~cmp, x, y), False{}, eb) : {TR.ho(~A, ~cmp, H.Node{H.smaller(A, x, y, _), H.ins(~A, ~cmp, r, H.larger(A, x, y, _)), l}) == True{} : Bool}
      TR.ho_mk(~A, ~cmp, y, H.ins(~A, ~cmp, r, x), l,
        L.subst(Bool, c => {c == True{} : Bool}, Bool.and(S.le(~A, ~cmp, y, x), TR.allt(~A, ~cmp, y, r)), TR.allt(~A, ~cmp, y, H.ins(~A, ~cmp, r, x)), Equal.sym(Bool, TR.allt(~A, ~cmp, y, H.ins(~A, ~cmp, r, x)), Bool.and(S.le(~A, ~cmp, y, x), TR.allt(~A, ~cmp, y, r)), allt_hins(~A, ~cmp, ~o, y, r, x)),
          L.and_intro(S.le(~A, ~cmp, y, x), TR.allt(~A, ~cmp, y, r), O.total(~A, ~cmp, ~o, x, y, eb), TR.ho_r(~A, ~cmp, y, l, r, h))),
        TR.ho_l(~A, ~cmp, y, l, r, h),
        ih, TR.ho_hl(~A, ~cmp, y, l, r, h))

def hins_ho(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: H.Tree<A>, +x: A, +h: {TR.ho(~A, ~cmp, t) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.ins(~A, ~cmp, t, x)) == True{} : Bool}:
  match t:
    case H.Leaf{}:
      {==}
    case H.Node{+y, +l, +r}:
      hins_ho_c(~A, ~cmp, ~o, x, y, l, r, h, S.le(~A, ~cmp, x, y), {==}, hins_ho(~A, ~cmp, ~o, r, H.larger(A, x, y, S.le(~A, ~cmp, x, y)), TR.ho_hr(~A, ~cmp, y, l, r, h)))

# ---- leftmost removal ----

def left_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +l: H.Tree<A>, +d: A, +x: A, +r: H.Tree<A>, +acc: List<&2, A>) -> {TR.ab(~A, ~cmp, H.Node{x, l, r}, acc) == S.ins(~A, ~cmp, H.leftmost(A, d, H.Node{x, l, r}), TR.ab(~A, ~cmp, H.drop_leftmost(A, H.Node{x, l, r}), acc)) : List<&2, A>}:
  match l:
    case H.Leaf{}:
      {==}
    case H.Node{+y, +ll, +lr}:
      +lm = H.leftmost(A, d, H.Node{y, ll, lr})
      +dl = H.drop_leftmost(A, H.Node{y, ll, lr})
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.Node{y, ll, lr}, TR.ab(~A, ~cmp, r, acc)), S.ins(~A, ~cmp, lm, TR.ab(~A, ~cmp, dl, TR.ab(~A, ~cmp, r, acc))), left_ab(~A, ~cmp, ~o, ll, d, y, lr, TR.ab(~A, ~cmp, r, acc))) : {S.ins(~A, ~cmp, x, _) == S.ins(~A, ~cmp, lm, S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, dl, acc)))) : List<&2, A>}
      %TR.ab_comm(~A, ~cmp, ~o, r, dl, acc) : {S.ins(~A, ~cmp, x, S.ins(~A, ~cmp, lm, _)) == S.ins(~A, ~cmp, lm, S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, dl, acc)))) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, x, lm, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, dl, acc)))

def left_allt(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +z: A, +d: A, +x: A, +l: H.Tree<A>, +r: H.Tree<A>) -> {TR.allt(~A, ~cmp, z, H.Node{x, l, r}) == Bool.and(S.le(~A, ~cmp, z, H.leftmost(A, d, H.Node{x, l, r})), TR.allt(~A, ~cmp, z, H.drop_leftmost(A, H.Node{x, l, r}))) : Bool}:
  +n = {H.Node{x, l, r} : H.Tree<A>}
  +lm = H.leftmost(A, d, n)
  +dl = H.drop_leftmost(A, n)
  %Equal.sym(Bool, TR.allt(~A, ~cmp, z, n), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, n, Nil{})), TR.allt_ab(~A, ~cmp, ~o, z, n)) : {_ == Bool.and(S.le(~A, ~cmp, z, lm), TR.allt(~A, ~cmp, z, dl)) : Bool}
  %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, n, Nil{}), S.ins(~A, ~cmp, lm, TR.ab(~A, ~cmp, dl, Nil{})), left_ab(~A, ~cmp, ~o, l, d, x, r, Nil{})) : {M.all_ge(~A, ~cmp, z, _) == Bool.and(S.le(~A, ~cmp, z, lm), TR.allt(~A, ~cmp, z, dl)) : Bool}
  %Equal.sym(Bool, M.all_ge(~A, ~cmp, z, S.ins(~A, ~cmp, lm, TR.ab(~A, ~cmp, dl, Nil{}))), Bool.and(S.le(~A, ~cmp, z, lm), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, dl, Nil{}))), M.all_ge_ins(~A, ~cmp, ~o, z, lm, TR.ab(~A, ~cmp, dl, Nil{}))) : {_ == Bool.and(S.le(~A, ~cmp, z, lm), TR.allt(~A, ~cmp, z, dl)) : Bool}
  %Equal.sym(Bool, TR.allt(~A, ~cmp, z, dl), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, dl, Nil{})), TR.allt_ab(~A, ~cmp, ~o, z, dl)) : {Bool.and(S.le(~A, ~cmp, z, lm), M.all_ge(~A, ~cmp, z, TR.ab(~A, ~cmp, dl, Nil{}))) == Bool.and(S.le(~A, ~cmp, z, lm), _) : Bool}
  {==}

def left_ho(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +l: H.Tree<A>, +d: A, +x: A, +r: H.Tree<A>, +h: {TR.ho(~A, ~cmp, H.Node{x, l, r}) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.drop_leftmost(A, H.Node{x, l, r})) == True{} : Bool}:
  match l:
    case H.Leaf{}:
      TR.ho_hr(~A, ~cmp, x, H.Leaf{}, r, h)
    case H.Node{+y, +ll, +lr}:
      +L0 = {H.Node{y, ll, lr} : H.Tree<A>}
      TR.ho_mk(~A, ~cmp, x, r, H.drop_leftmost(A, L0), TR.ho_r(~A, ~cmp, x, L0, r, h),
        L.and_right(S.le(~A, ~cmp, x, H.leftmost(A, d, L0)), TR.allt(~A, ~cmp, x, H.drop_leftmost(A, L0)), L.subst(Bool, c => {c == True{} : Bool}, TR.allt(~A, ~cmp, x, L0), Bool.and(S.le(~A, ~cmp, x, H.leftmost(A, d, L0)), TR.allt(~A, ~cmp, x, H.drop_leftmost(A, L0))), left_allt(~A, ~cmp, ~o, x, d, y, ll, lr), TR.ho_l(~A, ~cmp, x, L0, r, h))),
        TR.ho_hr(~A, ~cmp, x, L0, r, h),
        left_ho(~A, ~cmp, ~o, ll, d, y, lr, TR.ho_hl(~A, ~cmp, x, L0, r, h)))

# ---- sift (replace the root, restore order) ----

def sift_stmt(~A: Data, ~cmp: A -> A -> Cmp, t: H.Tree<A>, +y: A, +c: Nat, +acc: List<&2, A>) -> Type:
  match t:
    case H.Leaf{}:
      Unit
    case H.Node{+x, +l, +r}:
      {TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, l, r}, y, c), acc) == S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc))) : List<&2, A>}

def sift_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: H.Tree<A>, +y: A, +c: Nat, +acc: List<&2, A>) -> sift_stmt(~A, ~cmp, t, y, c, acc):
  match t c:
    case H.Leaf{} _:
      Unit{}
    case H.Node{x, H.Leaf{}, H.Leaf{}} 0n:
      {==}
    case H.Node{x, H.Leaf{}, H.Node{+b, +rl, +rr}} 0n:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Leaf{}} 0n:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Node{+b, +rl, +rr}} 0n:
      {==}
    case H.Node{x, H.Leaf{}, H.Leaf{}} 1n:
      {==}
    case H.Node{x, H.Leaf{}, H.Node{+b, +rl, +rr}} 1n:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Leaf{}} 1n:
      +ch = H.choice(~A, ~cmp, y, ll, lr)
      +rt = {H.Leaf{} : H.Tree<A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, ch), TR.ab(~A, ~cmp, rt, acc)), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc)))), sift_ab(~A, ~cmp, ~o, H.Node{a, ll, lr}, y, ch, TR.ab(~A, ~cmp, rt, acc))) : {S.ins(~A, ~cmp, a, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, a, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc))))) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, a, y, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc))))
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Node{+b, +rl, +rr}} 1n:
      +ch = H.choice(~A, ~cmp, y, ll, lr)
      +rt = {H.Node{b, rl, rr} : H.Tree<A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, ch), TR.ab(~A, ~cmp, rt, acc)), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc)))), sift_ab(~A, ~cmp, ~o, H.Node{a, ll, lr}, y, ch, TR.ab(~A, ~cmp, rt, acc))) : {S.ins(~A, ~cmp, a, _) == S.ins(~A, ~cmp, y, S.ins(~A, ~cmp, a, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc))))) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, a, y, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, rt, acc))))
    case H.Node{x, H.Leaf{}, H.Leaf{}} 2n:
      {==}
    case H.Node{x, H.Leaf{}, H.Node{+b, +rl, +rr}} 2n:
      +ch = H.choice(~A, ~cmp, y, rl, rr)
      +lt = {H.Leaf{} : H.Tree<A>}
      +s0 = TR.ab(~A, ~cmp, rl, TR.ab(~A, ~cmp, rr, acc))
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, ch), acc), S.ins(~A, ~cmp, y, s0), sift_ab(~A, ~cmp, ~o, H.Node{b, rl, rr}, y, ch, acc)) : {S.ins(~A, ~cmp, b, TR.ab(~A, ~cmp, lt, _)) == S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, y, s0)), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, s0)), TR.ab_ins(~A, ~cmp, ~o, lt, y, s0)) : {S.ins(~A, ~cmp, b, _) == S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0)), S.ins(~A, ~cmp, b, TR.ab(~A, ~cmp, lt, s0)), TR.ab_ins(~A, ~cmp, ~o, lt, b, s0)) : {S.ins(~A, ~cmp, b, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, s0))) == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, b, y, TR.ab(~A, ~cmp, lt, s0))
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Leaf{}} 2n:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Node{+b, +rl, +rr}} 2n:
      +ch = H.choice(~A, ~cmp, y, rl, rr)
      +lt = {H.Node{a, ll, lr} : H.Tree<A>}
      +s0 = TR.ab(~A, ~cmp, rl, TR.ab(~A, ~cmp, rr, acc))
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, ch), acc), S.ins(~A, ~cmp, y, s0), sift_ab(~A, ~cmp, ~o, H.Node{b, rl, rr}, y, ch, acc)) : {S.ins(~A, ~cmp, b, TR.ab(~A, ~cmp, lt, _)) == S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, y, s0)), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, s0)), TR.ab_ins(~A, ~cmp, ~o, lt, y, s0)) : {S.ins(~A, ~cmp, b, _) == S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0))) : List<&2, A>}
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, lt, S.ins(~A, ~cmp, b, s0)), S.ins(~A, ~cmp, b, TR.ab(~A, ~cmp, lt, s0)), TR.ab_ins(~A, ~cmp, ~o, lt, b, s0)) : {S.ins(~A, ~cmp, b, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, lt, s0))) == S.ins(~A, ~cmp, y, _) : List<&2, A>}
      M.ins_comm(~A, ~cmp, ~o, b, y, TR.ab(~A, ~cmp, lt, s0))
    case H.Node{x, H.Leaf{}, H.Leaf{}} 3n+k:
      {==}
    case H.Node{x, H.Leaf{}, H.Node{+b, +rl, +rr}} 3n+k:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Leaf{}} 3n+k:
      {==}
    case H.Node{x, H.Node{+a, +ll, +lr}, H.Node{+b, +rl, +rr}} 3n+k:
      {==}

def sift_allt(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +q: A, +x: A, +l: H.Tree<A>, +r: H.Tree<A>, +y: A, +c: Nat) -> {TR.allt(~A, ~cmp, q, H.sift(~A, ~cmp, H.Node{x, l, r}, y, c)) == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), TR.allt(~A, ~cmp, q, r))) : Bool}:
  +st = H.sift(~A, ~cmp, H.Node{x, l, r}, y, c)
  %Equal.sym(Bool, TR.allt(~A, ~cmp, q, st), M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, st, Nil{})), TR.allt_ab(~A, ~cmp, ~o, q, st)) : {_ == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), TR.allt(~A, ~cmp, q, r))) : Bool}
  %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, st, Nil{}), S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))), sift_ab(~A, ~cmp, ~o, H.Node{x, l, r}, y, c, Nil{})) : {M.all_ge(~A, ~cmp, q, _) == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), TR.allt(~A, ~cmp, q, r))) : Bool}
  %Equal.sym(Bool, M.all_ge(~A, ~cmp, q, S.ins(~A, ~cmp, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{})))), Bool.and(S.le(~A, ~cmp, q, y), M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{})))), M.all_ge_ins(~A, ~cmp, ~o, q, y, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{})))) : {_ == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), TR.allt(~A, ~cmp, q, r))) : Bool}
  %Equal.sym(Bool, M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, Nil{}))), Bool.and(TR.allt(~A, ~cmp, q, l), M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, r, Nil{}))), TR.all_ge_ab(~A, ~cmp, ~o, q, l, TR.ab(~A, ~cmp, r, Nil{}))) : {Bool.and(S.le(~A, ~cmp, q, y), _) == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), TR.allt(~A, ~cmp, q, r))) : Bool}
  %Equal.sym(Bool, TR.allt(~A, ~cmp, q, r), M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, r, Nil{})), TR.allt_ab(~A, ~cmp, ~o, q, r)) : {Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), M.all_ge(~A, ~cmp, q, TR.ab(~A, ~cmp, r, Nil{})))) == Bool.and(S.le(~A, ~cmp, q, y), Bool.and(TR.allt(~A, ~cmp, q, l), _)) : Bool}
  {==}

def ho_stmt(~A: Data, ~cmp: A -> A -> Cmp, t: H.Tree<A>, +y: A) -> Type:
  match t:
    case H.Leaf{}:
      Unit
    case H.Node{+x, +l, +r}:
      {Bool.and(TR.ho(~A, ~cmp, l), TR.ho(~A, ~cmp, r)) == True{} : Bool} -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, l, r}, y, H.choice(~A, ~cmp, y, l, r))) == True{} : Bool}

def bound_node(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +p: A, +a: A, +ll: H.Tree<A>, +lr: H.Tree<A>, +hp: {S.le(~A, ~cmp, p, a) == True{} : Bool}, +h: {TR.ho(~A, ~cmp, H.Node{a, ll, lr}) == True{} : Bool}) -> {TR.allt(~A, ~cmp, p, H.Node{a, ll, lr}) == True{} : Bool}:
  TR.allt_mono(~A, ~cmp, ~o, p, a, H.Node{a, ll, lr}, hp, TR.ho_self(~A, ~cmp, ~o, a, ll, lr, h))

# The root a of a heap-ordered node, moved up over y (a <= y), bounds the sifted subtree.
def up_bound(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +a: A, +ll: H.Tree<A>, +lr: H.Tree<A>, +y: A, +hay: {S.le(~A, ~cmp, a, y) == True{} : Bool}, +h: {TR.ho(~A, ~cmp, H.Node{a, ll, lr}) == True{} : Bool}) -> {TR.allt(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr))) == True{} : Bool}:
  L.subst(Bool, c => {c == True{} : Bool}, Bool.and(S.le(~A, ~cmp, a, y), Bool.and(TR.allt(~A, ~cmp, a, ll), TR.allt(~A, ~cmp, a, lr))), TR.allt(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr))), Equal.sym(Bool, TR.allt(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr))), Bool.and(S.le(~A, ~cmp, a, y), Bool.and(TR.allt(~A, ~cmp, a, ll), TR.allt(~A, ~cmp, a, lr))), sift_allt(~A, ~cmp, ~o, a, a, ll, lr, y, H.choice(~A, ~cmp, y, ll, lr))),
    L.and_intro(S.le(~A, ~cmp, a, y), Bool.and(TR.allt(~A, ~cmp, a, ll), TR.allt(~A, ~cmp, a, lr)), hay, L.and_intro(TR.allt(~A, ~cmp, a, ll), TR.allt(~A, ~cmp, a, lr), TR.ho_l(~A, ~cmp, a, ll, lr, h), TR.ho_r(~A, ~cmp, a, ll, lr, h))))

def kid_ho(~A: Data, ~cmp: A -> A -> Cmp, +a: A, +ll: H.Tree<A>, +lr: H.Tree<A>, +h: {TR.ho(~A, ~cmp, H.Node{a, ll, lr}) == True{} : Bool}) -> {Bool.and(TR.ho(~A, ~cmp, ll), TR.ho(~A, ~cmp, lr)) == True{} : Bool}:
  L.and_intro(TR.ho(~A, ~cmp, ll), TR.ho(~A, ~cmp, lr), TR.ho_hl(~A, ~cmp, a, ll, lr, h), TR.ho_hr(~A, ~cmp, a, ll, lr, h))

def sh_nl(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +a: A, +ll: H.Tree<A>, +lr: H.Tree<A>, +y: A, +b1: Bool, +e1: {S.le(~A, ~cmp, y, a) == b1 : Bool}, +hl: {TR.ho(~A, ~cmp, H.Node{a, ll, lr}) == True{} : Bool}, ih: @+hk: {Bool.and(TR.ho(~A, ~cmp, ll), TR.ho(~A, ~cmp, lr)) == True{} : Bool} -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr))) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, H.Node{a, ll, lr}, H.Leaf{}}, y, H.stay_or(b1, 1n))) == True{} : Bool}:
  match b1:
    case True{}:
      TR.ho_mk(~A, ~cmp, y, H.Node{a, ll, lr}, H.Leaf{}, bound_node(~A, ~cmp, ~o, y, a, ll, lr, e1, hl), {==}, hl, {==})
    case False{}:
      TR.ho_mk(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr)), H.Leaf{}, up_bound(~A, ~cmp, ~o, a, ll, lr, y, O.total(~A, ~cmp, ~o, y, a, e1), hl), {==}, ih(kid_ho(~A, ~cmp, a, ll, lr, hl)), {==})

def sh_ln(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +b: A, +rl: H.Tree<A>, +rr: H.Tree<A>, +y: A, +b2: Bool, +e2: {S.le(~A, ~cmp, y, b) == b2 : Bool}, +hr: {TR.ho(~A, ~cmp, H.Node{b, rl, rr}) == True{} : Bool}, ih: @+hk: {Bool.and(TR.ho(~A, ~cmp, rl), TR.ho(~A, ~cmp, rr)) == True{} : Bool} -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, H.choice(~A, ~cmp, y, rl, rr))) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, H.Leaf{}, H.Node{b, rl, rr}}, y, H.stay_or(b2, 2n))) == True{} : Bool}:
  match b2:
    case True{}:
      TR.ho_mk(~A, ~cmp, y, H.Leaf{}, H.Node{b, rl, rr}, {==}, bound_node(~A, ~cmp, ~o, y, b, rl, rr, e2, hr), {==}, hr)
    case False{}:
      TR.ho_mk(~A, ~cmp, b, H.Leaf{}, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, H.choice(~A, ~cmp, y, rl, rr)), {==}, up_bound(~A, ~cmp, ~o, b, rl, rr, y, O.total(~A, ~cmp, ~o, y, b, e2), hr), {==}, ih(kid_ho(~A, ~cmp, b, rl, rr, hr)))

def sh_nn(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +x: A, +a: A, +ll: H.Tree<A>, +lr: H.Tree<A>, +b: A, +rl: H.Tree<A>, +rr: H.Tree<A>, +y: A, +b1: Bool, +e1: {S.le(~A, ~cmp, y, a) == b1 : Bool}, +b2: Bool, +e2: {S.le(~A, ~cmp, y, b) == b2 : Bool}, +b3: Bool, +e3: {S.le(~A, ~cmp, a, b) == b3 : Bool}, +hl: {TR.ho(~A, ~cmp, H.Node{a, ll, lr}) == True{} : Bool}, +hr: {TR.ho(~A, ~cmp, H.Node{b, rl, rr}) == True{} : Bool}, ihl: @+hk: {Bool.and(TR.ho(~A, ~cmp, ll), TR.ho(~A, ~cmp, lr)) == True{} : Bool} -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr))) == True{} : Bool}, ihr: @+hk: {Bool.and(TR.ho(~A, ~cmp, rl), TR.ho(~A, ~cmp, rr)) == True{} : Bool} -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, H.choice(~A, ~cmp, y, rl, rr))) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, H.Node{a, ll, lr}, H.Node{b, rl, rr}}, y, H.choose2(b1, b2, b3))) == True{} : Bool}:
  match b1 b2 b3:
    case True{} True{} _:
      TR.ho_mk(~A, ~cmp, y, H.Node{a, ll, lr}, H.Node{b, rl, rr}, bound_node(~A, ~cmp, ~o, y, a, ll, lr, e1, hl), bound_node(~A, ~cmp, ~o, y, b, rl, rr, e2, hr), hl, hr)
    case True{} False{} True{}:
      Empty.absurd({TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, H.Node{a, ll, lr}, H.Node{b, rl, rr}}, y, H.choose2(b1, b2, b3))) == True{} : Bool}, L.true_not_false(S.le(~A, ~cmp, y, b), O.trans(~A, ~cmp, o, y, a, b, e1, e3), e2))
    case True{} False{} False{}:
      TR.ho_mk(~A, ~cmp, b, H.Node{a, ll, lr}, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, H.choice(~A, ~cmp, y, rl, rr)), bound_node(~A, ~cmp, ~o, b, a, ll, lr, O.total(~A, ~cmp, ~o, a, b, e3), hl), up_bound(~A, ~cmp, ~o, b, rl, rr, y, O.total(~A, ~cmp, ~o, y, b, e2), hr), hl, ihr(kid_ho(~A, ~cmp, b, rl, rr, hr)))
    case False{} True{} True{}:
      TR.ho_mk(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr)), H.Node{b, rl, rr}, up_bound(~A, ~cmp, ~o, a, ll, lr, y, O.total(~A, ~cmp, ~o, y, a, e1), hl), bound_node(~A, ~cmp, ~o, a, b, rl, rr, e3, hr), ihl(kid_ho(~A, ~cmp, a, ll, lr, hl)), hr)
    case False{} True{} False{}:
      Empty.absurd({TR.ho(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, H.Node{a, ll, lr}, H.Node{b, rl, rr}}, y, H.choose2(b1, b2, b3))) == True{} : Bool}, L.true_not_false(S.le(~A, ~cmp, a, b), O.trans(~A, ~cmp, o, a, y, b, O.total(~A, ~cmp, ~o, y, a, e1), e2), e3))
    case False{} False{} True{}:
      TR.ho_mk(~A, ~cmp, a, H.sift(~A, ~cmp, H.Node{a, ll, lr}, y, H.choice(~A, ~cmp, y, ll, lr)), H.Node{b, rl, rr}, up_bound(~A, ~cmp, ~o, a, ll, lr, y, O.total(~A, ~cmp, ~o, y, a, e1), hl), bound_node(~A, ~cmp, ~o, a, b, rl, rr, e3, hr), ihl(kid_ho(~A, ~cmp, a, ll, lr, hl)), hr)
    case False{} False{} False{}:
      TR.ho_mk(~A, ~cmp, b, H.Node{a, ll, lr}, H.sift(~A, ~cmp, H.Node{b, rl, rr}, y, H.choice(~A, ~cmp, y, rl, rr)), bound_node(~A, ~cmp, ~o, b, a, ll, lr, O.total(~A, ~cmp, ~o, a, b, e3), hl), up_bound(~A, ~cmp, ~o, b, rl, rr, y, O.total(~A, ~cmp, ~o, y, b, e2), hr), hl, ihr(kid_ho(~A, ~cmp, b, rl, rr, hr)))

def sift_ho(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +t: H.Tree<A>, +y: A) -> ho_stmt(~A, ~cmp, t, y):
  match t:
    case H.Leaf{}:
      Unit{}
    case H.Node{+x, H.Leaf{}, H.Leaf{}}:
      hk => {==}
    case H.Node{+x, H.Node{+a, +ll, +lr}, H.Leaf{}}:
      hk => sh_nl(~A, ~cmp, ~o, x, a, ll, lr, y, S.le(~A, ~cmp, y, a), {==}, L.and_left(TR.ho(~A, ~cmp, H.Node{a, ll, lr}), True{}, hk), hk2 => sift_ho(~A, ~cmp, ~o, H.Node{a, ll, lr}, y)(hk2))
    case H.Node{+x, H.Leaf{}, H.Node{+b, +rl, +rr}}:
      hk => sh_ln(~A, ~cmp, ~o, x, b, rl, rr, y, S.le(~A, ~cmp, y, b), {==}, hk, hk2 => sift_ho(~A, ~cmp, ~o, H.Node{b, rl, rr}, y)(hk2))
    case H.Node{+x, H.Node{+a, +ll, +lr}, H.Node{+b, +rl, +rr}}:
      +hk => sh_nn(~A, ~cmp, ~o, x, a, ll, lr, b, rl, rr, y, S.le(~A, ~cmp, y, a), {==}, S.le(~A, ~cmp, y, b), {==}, S.le(~A, ~cmp, a, b), {==}, L.and_left(TR.ho(~A, ~cmp, H.Node{a, ll, lr}), TR.ho(~A, ~cmp, H.Node{b, rl, rr}), hk), L.and_right(TR.ho(~A, ~cmp, H.Node{a, ll, lr}), TR.ho(~A, ~cmp, H.Node{b, rl, rr}), hk), hk2 => sift_ho(~A, ~cmp, ~o, H.Node{a, ll, lr}, y)(hk2), hk3 => sift_ho(~A, ~cmp, ~o, H.Node{b, rl, rr}, y)(hk3))

# ---- root deletion ----

def del_ab(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +l: H.Tree<A>, +r: H.Tree<A>, +acc: List<&2, A>) -> {TR.ab(~A, ~cmp, H.del_root(~A, ~cmp, l, r), acc) == TR.ab(~A, ~cmp, l, TR.ab(~A, ~cmp, r, acc)) : List<&2, A>}:
  match l:
    case H.Leaf{}:
      {==}
    case H.Node{+x, +ll, +lr}:
      +n = {H.Node{x, ll, lr} : H.Tree<A>}
      +lm = H.leftmost(A, x, n)
      +dl = H.drop_leftmost(A, n)
      %Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, H.sift(~A, ~cmp, H.Node{x, r, dl}, lm, H.choice(~A, ~cmp, lm, r, dl)), acc), S.ins(~A, ~cmp, lm, TR.ab(~A, ~cmp, r, TR.ab(~A, ~cmp, dl, acc))), sift_ab(~A, ~cmp, ~o, H.Node{x, r, dl}, lm, H.choice(~A, ~cmp, lm, r, dl), acc)) : {_ == S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      %TR.ab_comm(~A, ~cmp, ~o, dl, r, acc) : {S.ins(~A, ~cmp, lm, _) == S.ins(~A, ~cmp, x, TR.ab(~A, ~cmp, ll, TR.ab(~A, ~cmp, lr, TR.ab(~A, ~cmp, r, acc)))) : List<&2, A>}
      Equal.sym(List<&2, A>, TR.ab(~A, ~cmp, n, TR.ab(~A, ~cmp, r, acc)), S.ins(~A, ~cmp, lm, TR.ab(~A, ~cmp, dl, TR.ab(~A, ~cmp, r, acc))), left_ab(~A, ~cmp, ~o, ll, x, x, lr, TR.ab(~A, ~cmp, r, acc)))

def del_ho(~A: Data, ~cmp: A -> A -> Cmp, ~o: O.Order(~A, ~cmp), +l: H.Tree<A>, +r: H.Tree<A>, +hl: {TR.ho(~A, ~cmp, l) == True{} : Bool}, +hr: {TR.ho(~A, ~cmp, r) == True{} : Bool}) -> {TR.ho(~A, ~cmp, H.del_root(~A, ~cmp, l, r)) == True{} : Bool}:
  match l:
    case H.Leaf{}:
      hr
    case H.Node{+x, +ll, +lr}:
      +n = {H.Node{x, ll, lr} : H.Tree<A>}
      +lm = H.leftmost(A, x, n)
      +dl = H.drop_leftmost(A, n)
      sift_ho(~A, ~cmp, ~o, H.Node{x, r, dl}, lm)(L.and_intro(TR.ho(~A, ~cmp, r), TR.ho(~A, ~cmp, dl), hr, left_ho(~A, ~cmp, ~o, ll, x, x, lr, hl)))
