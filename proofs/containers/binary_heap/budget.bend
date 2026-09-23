import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/array.bend as AR
import ../../lib/spec_common.bend as SC
import ./spec.bend as S
import ./root.bend as RT
import ./state.bend as ST

# The capacity budget in terms of the heap's SIZE: the number of stored
# elements stays below 2^q with q <= 31. A push only doubles a full block
# (size = 2^depth), and then 2^depth = size < 2^q forces depth < 31, so the
# doubled block still has at most 2^31 slots.

def pow2_inv_c(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}, c: Bool, +ec: {Nat.is_lt(a, b) == c : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      Empty.absurd({Nat.is_lt(a, b) == True{} : Bool}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(SC.pow2(a), SC.pow2(a)), True{}, Equal.sym(Bool, Nat.is_lt(SC.pow2(a), SC.pow2(a)), False{}, N.lt_irrefl(SC.pow2(a))),
        N.lt_le_trans(SC.pow2(a), SC.pow2(b), SC.pow2(a), h, N.pow2_mono(b, a, N.not_lt_le(a, b, ec))))))

def pow2_inv(+a: Nat, +b: Nat, +h: {Nat.is_lt(SC.pow2(a), SC.pow2(b)) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  pow2_inv_c(a, b, h, Nat.is_lt(a, b), {==})

def room_or_c(+size: Nat, +depth: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hs: {Nat.is_lt(size, SC.pow2(q)) == True{} : Bool}, b: Bool, +eb: {Nat.is_lt(size, SC.pow2(depth)) == b : Bool}) -> {Bool.or(Nat.is_lt(size, SC.pow2(depth)), Nat.is_lt(depth, 31n)) == True{} : Bool}:
  match b:
    case True{}:
      L.subst(Bool, c => {Bool.or(c, Nat.is_lt(depth, 31n)) == True{} : Bool}, True{}, Nat.is_lt(size, SC.pow2(depth)), Equal.sym(Bool, Nat.is_lt(size, SC.pow2(depth)), True{}, eb), {==})
    case False{}:
      +hd = N.lt_le_trans(depth, q, 31n, pow2_inv(depth, q, N.le_lt_trans(SC.pow2(depth), size, SC.pow2(q), N.not_lt_le(size, SC.pow2(depth), eb), hs)), hq)
      L.subst(Bool, c => {Bool.or(Nat.is_lt(size, SC.pow2(depth)), c) == True{} : Bool}, True{}, Nat.is_lt(depth, 31n), Equal.sym(Bool, Nat.is_lt(depth, 31n), True{}, hd),
        L.subst(Bool, c => {Bool.or(c, True{}) == True{} : Bool}, False{}, Nat.is_lt(size, SC.pow2(depth)), Equal.sym(Bool, Nat.is_lt(size, SC.pow2(depth)), False{}, eb), {==}))

# the push premise the block needs, from the size budget
def room_or(+size: Nat, +depth: Nat, +q: Nat, +hq: {Nat.is_le(q, 31n) == True{} : Bool}, +hs: {Nat.is_lt(size, SC.pow2(q)) == True{} : Bool}) -> {Bool.or(Nat.is_lt(size, SC.pow2(depth)), Nat.is_lt(depth, 31n)) == True{} : Bool}:
  room_or_c(size, depth, q, hq, hs, Nat.is_lt(size, SC.pow2(depth)), {==})

# the size of a good shadow is the length of its model
def sz_len(~A: Data, ~cmp: A -> A -> Cmp, sh: ST.Shadow<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}) -> {ST.sh_size(~A, sh) == SC.length(A, ST.model(~A, ~cmp, sh)) : Nat}:
  match sh:
    case ST.Sh{+size, +depth, +t}:
      Equal.sym(Nat, SC.length(A, ST.model(~A, ~cmp, ST.Sh{size, depth, t})), size, RT.model_length(~A, ~cmp, AR.slots(Maybe<&2, A>, t), size, ST.g_lay(~A, ~cmp, size, depth, t, g)))

# a push onto a good shadow adds one element
def push_size(~A: Data, ~cmp: A -> A -> Cmp, +y: A, +sh: ST.Shadow<A>, +sh1: ST.Shadow<A>, +g: {ST.good(~A, ~cmp, sh) == True{} : Bool}, +g1: {ST.good(~A, ~cmp, sh1) == True{} : Bool}, +ems: {ST.model(~A, ~cmp, sh1) == S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)) : List<&2, A>}) -> {ST.sh_size(~A, sh1) == 1n+ST.sh_size(~A, sh) : Nat}:
  Equal.trans(Nat, ST.sh_size(~A, sh1), SC.length(A, ST.model(~A, ~cmp, sh1)), 1n+ST.sh_size(~A, sh),
    sz_len(~A, ~cmp, sh1, g1),
    Equal.trans(Nat, SC.length(A, ST.model(~A, ~cmp, sh1)), SC.length(A, S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh))), 1n+ST.sh_size(~A, sh),
      Equal.cong(List<&2, A>, Nat, zs => SC.length(A, zs), ST.model(~A, ~cmp, sh1), S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)), ems),
      Equal.trans(Nat, SC.length(A, S.ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh))), 1n+SC.length(A, ST.model(~A, ~cmp, sh)), 1n+ST.sh_size(~A, sh),
        RT.length_ins(~A, ~cmp, y, ST.model(~A, ~cmp, sh)),
        N.succ_cong(SC.length(A, ST.model(~A, ~cmp, sh)), ST.sh_size(~A, sh), Equal.sym(Nat, ST.sh_size(~A, sh), SC.length(A, ST.model(~A, ~cmp, sh)), sz_len(~A, ~cmp, sh, g))))))

def len_from_list(~A: Data, ~cmp: A -> A -> Cmp, ys: List<&2, A>, +acc: List<&2, A>) -> {SC.length(A, S.from_list(~A, ~cmp, ys, acc)) == Nat.add(SC.length(A, ys), SC.length(A, acc)) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Equal.trans(Nat, SC.length(A, S.from_list(~A, ~cmp, t, S.ins(~A, ~cmp, y, acc))), Nat.add(SC.length(A, t), SC.length(A, S.ins(~A, ~cmp, y, acc))), 1n+Nat.add(SC.length(A, t), SC.length(A, acc)),
        len_from_list(~A, ~cmp, t, S.ins(~A, ~cmp, y, acc)),
        Equal.trans(Nat, Nat.add(SC.length(A, t), SC.length(A, S.ins(~A, ~cmp, y, acc))), Nat.add(SC.length(A, t), 1n+SC.length(A, acc)), 1n+Nat.add(SC.length(A, t), SC.length(A, acc)),
          Equal.cong(Nat, Nat, z => Nat.add(SC.length(A, t), z), SC.length(A, S.ins(~A, ~cmp, y, acc)), 1n+SC.length(A, acc), RT.length_ins(~A, ~cmp, y, acc)),
          N.add_succ(SC.length(A, t), SC.length(A, acc))))
