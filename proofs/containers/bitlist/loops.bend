import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../../../src/containers/bitset.bend as B
import ../../../src/containers/bitlist.bend as BLI
import ../../../src/containers/dynamic_array.bend as D
import ../../../src/containers/types/dynamic_array.bend as DE
import ../dynamic_array/spec.bend as DS
import ../dynamic_array/state.bend as DAS
import ../dynamic_array/steps.bend as DSP
import ../dynamic_array/trace.bend as DTR
import ../bitset/listx.bend as LX
import ../bitset/model.bend as MD
import ../bitset/walk.bend as WK
import ../bitset/state.bend as ST
import ../bitset/fastcount.bend as FC
import ./da.bend as DI
import ./bits.bend as BT

# The two whole-array walks of src/containers/bitlist.bend: count sums the
# populations of the words upward, to_list emits the first n bits from the
# last word down. Each word read goes through the dynamic array's contract,
# which hands back a new good shadow with the same words, so the loop
# invariant carries "a good shadow whose words are xs".
# (source: proofs/containers/bitlist/loops.src)


# a read of word q: the new shadow keeps the words; the value is word q
def read_same(+s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +q: Nat) -> {DAS.good(U32, DI.gsh(s, gs, q)) == True{} : Bool} & ({DI.ws(DI.gsh(s, gs, q)) == xs : List<&2, U32>} & {DI.lim(DI.gsh(s, gs, q)) == c : Nat}):
  (DI.get_good(s, gs, q), (Equal.trans(List<&2, U32>, DI.ws(DI.gsh(s, gs, q)), DI.ws(s), xs, DI.get_ws(s, gs, q), es), Equal.trans(Nat, DI.lim(DI.gsh(s, gs, q)), DI.lim(s), c, DI.get_lim(s, gs, q), ec)))


def read_eq(+s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +q: Nat) -> {D.get(U32, DAS.real(U32, s), q) == (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, s), q), (DAS.real(U32, DI.gsh(s, gs, q)), DI.unitem(DTR.so_obs(U32, s, DE.Get{q}, DSP.step_ok(U32, s, DE.Get{q}, gs)))), DI.get_eq(s, gs, q)) : {_ == (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}
  %Equal.sym(Result<&2, &2, DE.Error, U32>, DI.unitem(DTR.so_obs(U32, s, DE.Get{q}, DSP.step_ok(U32, s, DE.Get{q}, gs))), DS.item_result(U32, SC.nth(U32, DI.ws(s), q)), DI.get_val(s, gs, q)) : {(DAS.real(U32, DI.gsh(s, gs, q)), _) == (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}
  %Equal.sym(List<&2, U32>, DI.ws(s), xs, es) : {(DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, _, q))) == (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))) : D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>}
  {==}

# ---- count ----


def CountOK(k: Nat, s: DAS.Shadow<U32>, acc: Nat, q: Nat, xs: List<&2, U32>, c: Nat) -> Type:
  Sigma<&1, &1, DAS.Shadow<U32>, s_2 => {BLI.count_go(k, (DAS.real(U32, s), acc), q) == (DAS.real(U32, s_2), Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), k)))) : D.DynArray<&2, U32> & Nat} & {DAS.good(U32, s_2) == True{} : Bool} & ({DI.ws(s_2) == xs : List<&2, U32>} & {DI.lim(s_2) == c : Nat})>

def drop_none(-A: Data, +xs: List<&2, A>, +q: Nat, +h: {SC.nth(A, xs, q) == None{} : Maybe<&2, A>}) -> {SC.drop(A, xs, q) == Nil{} : List<&2, A>}:
  match xs q:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({SC.drop(A, Con{x, t}, 0n) == Nil{} : List<&2, A>}, L.none_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, h)))
    case Con{+x, +t} 1n+ +p:
      drop_none(A, t, p, h)

def nth_none_succ(-A: Data, +xs: List<&2, A>, +q: Nat, +h: {SC.nth(A, xs, q) == None{} : Maybe<&2, A>}) -> {SC.nth(A, xs, 1n+q) == None{} : Maybe<&2, A>}:
  match xs q:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{x, t} 0n:
      Empty.absurd({SC.nth(A, Con{x, t}, 1n) == None{} : Maybe<&2, A>}, L.none_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, h)))
    case Con{+x, +t} 1n+ +p:
      nth_none_succ(A, t, p, h)

def cw_none(+xs: List<&2, U32>, +k: Nat, +q: Nat, +h: {SC.nth(U32, xs, q) == None{} : Maybe<&2, U32>}) -> {MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+k)) == MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), k)) : Nat}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, xs, q), Nil{}, drop_none(U32, xs, q, h)) : {MD.count_words(SC.take(U32, _, 1n+k)) == MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), k)) : Nat}
  %Equal.sym(List<&2, U32>, SC.drop(U32, xs, 1n+q), Nil{}, drop_none(U32, xs, 1n+q, nth_none_succ(U32, xs, q, h))) : {MD.count_words(SC.take(U32, Nil{}, 1n+k)) == MD.count_words(SC.take(U32, _, k)) : Nat}
  {==}

def cw_some(+xs: List<&2, U32>, +k: Nat, +q: Nat, +x: U32, +h: {SC.nth(U32, xs, q) == Some{x} : Maybe<&2, U32>}) -> {MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+k)) == Nat.add(B.word_count(32n, x), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), k))) : Nat}:
  %Equal.sym(List<&2, U32>, SC.drop(U32, xs, q), Con{x, SC.drop(U32, xs, 1n+q)}, LX.drop_cons(U32, xs, q, x, h)) : {MD.count_words(SC.take(U32, _, 1n+k)) == Nat.add(B.word_count(32n, x), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), k))) : Nat}
  {==}


def count_lift(+r: Nat, s: DAS.Shadow<U32>, +acc: Nat, +q: Nat, +xs: List<&2, U32>, +c: Nat, s1: DAS.Shadow<U32>, +acc1: Nat, +e_step: {BLI.count_go(1n+r, (DAS.real(U32, s), acc), q) == BLI.count_go(r, (DAS.real(U32, s1), acc1), 1n+q) : D.DynArray<&2, U32> & Nat}, +e_sum: {Nat.add(acc1, MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))) == Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r))) : Nat}, ih: CountOK(r, s1, acc1, 1n+q, xs, c)) -> CountOK(1n+r, s, acc, q, xs, c):
  match ih:
    case Tuple{s2, Tuple{e2, same}}:
      (s2, (Equal.trans(D.DynArray<&2, U32> & Nat, BLI.count_go(1n+r, (DAS.real(U32, s), acc), q), BLI.count_go(r, (DAS.real(U32, s1), acc1), 1n+q), (DAS.real(U32, s2), Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r)))), e_step,
              Equal.trans(D.DynArray<&2, U32> & Nat, BLI.count_go(r, (DAS.real(U32, s1), acc1), 1n+q), (DAS.real(U32, s2), Nat.add(acc1, MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r)))), (DAS.real(U32, s2), Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r)))), e2,
                Equal.cong(Nat, D.DynArray<&2, U32> & Nat, z => (DAS.real(U32, s2), z), Nat.add(acc1, MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))), Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r))), e_sum))), same))


def count_rd(+r: Nat, +s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +acc: Nat, +q: Nat, +y: Maybe<&2, U32>, +hy: {SC.nth(U32, xs, q) == y : Maybe<&2, U32>}) -> {BLI.count_go(1n+r, (DAS.real(U32, s), acc), q) == BLI.count_go(r, BLI.count_add((DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, y)), acc), 1n+q) : D.DynArray<&2, U32> & Nat}:
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, s), q), (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))), read_eq(s, gs, xs, c, es, ec, q)) : {BLI.count_go(r, BLI.count_add(_, acc), 1n+q) == BLI.count_go(r, BLI.count_add((DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, y)), acc), 1n+q) : D.DynArray<&2, U32> & Nat}
  %Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, q), y, hy) : {BLI.count_go(r, BLI.count_add((DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, _)), acc), 1n+q) == BLI.count_go(r, BLI.count_add((DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, y)), acc), 1n+q) : D.DynArray<&2, U32> & Nat}
  {==}



def count_sum(+acc: Nat, +r: Nat, +q: Nat, +xs: List<&2, U32>, +x: U32, +hy: {SC.nth(U32, xs, q) == Some{x} : Maybe<&2, U32>}) -> {Nat.add(B.count_word(x, acc, U32.is_eq(x, 0)), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))) == Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r))) : Nat}:
  %Equal.sym(Nat, B.count_word(x, acc, U32.is_eq(x, 0)), Nat.add(acc, B.word_count(32n, x)), FC.count_word_ok(x, acc, U32.is_eq(x, 0), {==})) : {Nat.add(_, MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))) == Nat.add(acc, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r))) : Nat}
  %Equal.sym(Nat, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r)), Nat.add(B.word_count(32n, x), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))), cw_some(xs, r, q, x, hy)) : {Nat.add(Nat.add(acc, B.word_count(32n, x)), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r))) == Nat.add(acc, _) : Nat}
  N.add_assoc(acc, B.word_count(32n, x), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r)))

def count_y(+r: Nat, +s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +acc: Nat, +q: Nat, +y: Maybe<&2, U32>, +hy: {SC.nth(U32, xs, q) == y : Maybe<&2, U32>}, +e_rd: {BLI.count_go(1n+r, (DAS.real(U32, s), acc), q) == BLI.count_go(r, BLI.count_add((DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, y)), acc), 1n+q) : D.DynArray<&2, U32> & Nat}, rec: @+a2: Nat -> @+q2: Nat -> @+s2: DAS.Shadow<U32> -> @+g2: {DAS.good(U32, s2) == True{} : Bool} -> @+e2: {DI.ws(s2) == xs : List<&2, U32>} -> @+f2: {DI.lim(s2) == c : Nat} -> CountOK(r, s2, a2, q2, xs, c)) -> CountOK(1n+r, s, acc, q, xs, c):
  match y:
    case None{}:
      +gs1 = DI.get_good(s, gs, q)
      +es1 = Equal.trans(List<&2, U32>, DI.ws(DI.gsh(s, gs, q)), DI.ws(s), xs, DI.get_ws(s, gs, q), es)
      +ec1 = Equal.trans(Nat, DI.lim(DI.gsh(s, gs, q)), DI.lim(s), c, DI.get_lim(s, gs, q), ec)
      +e_sum = Equal.cong(Nat, Nat, z => Nat.add(acc, z), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r)), MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r)), Equal.sym(Nat, MD.count_words(SC.take(U32, SC.drop(U32, xs, q), 1n+r)), MD.count_words(SC.take(U32, SC.drop(U32, xs, 1n+q), r)), cw_none(xs, r, q, hy)))
      count_lift(r, s, acc, q, xs, c, DI.gsh(s, gs, q), acc, e_rd, e_sum, rec(acc, 1n+q, DI.gsh(s, gs, q), gs1, es1, ec1))
    case Some{+x}:
      +gs1 = DI.get_good(s, gs, q)
      +es1 = Equal.trans(List<&2, U32>, DI.ws(DI.gsh(s, gs, q)), DI.ws(s), xs, DI.get_ws(s, gs, q), es)
      +ec1 = Equal.trans(Nat, DI.lim(DI.gsh(s, gs, q)), DI.lim(s), c, DI.get_lim(s, gs, q), ec)
      count_lift(r, s, acc, q, xs, c, DI.gsh(s, gs, q), B.count_word(x, acc, U32.is_eq(x, 0)), e_rd, count_sum(acc, r, q, xs, x, hy), rec(B.count_word(x, acc, U32.is_eq(x, 0)), 1n+q, DI.gsh(s, gs, q), gs1, es1, ec1))

def count_loop(k: Nat, +s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +acc: Nat, +q: Nat) -> CountOK(k, s, acc, q, xs, c):
  match k:
    case 0n:
      (s, (%Equal.sym(List<&2, U32>, SC.take(U32, SC.drop(U32, xs, q), 0n), Nil{}, LX.take_zero(U32, SC.drop(U32, xs, q))) : {(DAS.real(U32, s), acc) == (DAS.real(U32, s), Nat.add(acc, MD.count_words(_))) : D.DynArray<&2, U32> & Nat}
           %Equal.sym(Nat, Nat.add(acc, 0n), acc, N.add_zero(acc)) : {(DAS.real(U32, s), acc) == (DAS.real(U32, s), _) : D.DynArray<&2, U32> & Nat}
           {==}, (gs, (es, ec))))
    case 1n+ +r:
      count_y(r, s, gs, xs, c, es, ec, acc, q, SC.nth(U32, xs, q), {==}, count_rd(r, s, gs, xs, c, es, ec, acc, q, SC.nth(U32, xs, q), {==}), (a2 => q2 => s2 => g2 => e2 => f2 => count_loop(r, s2, g2, xs, c, e2, f2, a2, q2)))

# ---- to_list ----


def BitsOK(k: Nat, s: DAS.Shadow<U32>, n: Nat, xs: List<&2, U32>, c: Nat) -> Type:
  Sigma<&1, &1, DAS.Shadow<U32>, s_2 => {BLI.bits_go(k, (DAS.real(U32, s), SC.take(Bool, ST.flat(SC.drop(U32, xs, k)), Nat.sub(n, Nat.mul(k, 32n)))), n) == (DAS.real(U32, s_2), SC.take(Bool, ST.flat(SC.drop(U32, xs, 0n)), Nat.sub(n, Nat.mul(0n, 32n)))) : D.DynArray<&2, U32> & List<&2, Bool>} & {DAS.good(U32, s_2) == True{} : Bool} & ({DI.ws(s_2) == xs : List<&2, U32>} & {DI.lim(s_2) == c : Nat})>

def bits_lift(+q: Nat, s: DAS.Shadow<U32>, +n: Nat, +xs: List<&2, U32>, +c: Nat, s1: DAS.Shadow<U32>, +e_step: {BLI.bits_go(1n+q, (DAS.real(U32, s), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))), n) == BLI.bits_go(q, (DAS.real(U32, s1), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n) : D.DynArray<&2, U32> & List<&2, Bool>}, ih: BitsOK(q, s1, n, xs, c)) -> BitsOK(1n+q, s, n, xs, c):
  match ih:
    case Tuple{s2, Tuple{e2, same}}:
      (s2, (Equal.trans(D.DynArray<&2, U32> & List<&2, Bool>, BLI.bits_go(1n+q, (DAS.real(U32, s), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))), n), BLI.bits_go(q, (DAS.real(U32, s1), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n), (DAS.real(U32, s2), SC.take(Bool, ST.flat(SC.drop(U32, xs, 0n)), Nat.sub(n, Nat.mul(0n, 32n)))), e_step, e2), same))


def bits_rd(+s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +n: Nat, +q: Nat, +hq: {Nat.is_lt(q, SC.length(U32, xs)) == True{} : Bool}) -> {BLI.bits_go(1n+q, (DAS.real(U32, s), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))), n) == BLI.bits_go(q, (DAS.real(U32, DI.gsh(s, gs, q)), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n) : D.DynArray<&2, U32> & List<&2, Bool>}:
  +hx = WK.nthw_nth(xs, q, hq)
  %Equal.sym(D.DynArray<&2, U32> & Result<&2, &2, DE.Error, U32>, D.get(U32, DAS.real(U32, s), q), (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, SC.nth(U32, xs, q))), read_eq(s, gs, xs, c, es, ec, q)) : {BLI.bits_go(q, BLI.bits_add(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n))), _), n) == BLI.bits_go(q, (DAS.real(U32, DI.gsh(s, gs, q)), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n) : D.DynArray<&2, U32> & List<&2, Bool>}
  %Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, q), Some{WK.nthw(xs, q)}, hx) : {BLI.bits_go(q, BLI.bits_add(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n))), (DAS.real(U32, DI.gsh(s, gs, q)), DS.item_result(U32, _))), n) == BLI.bits_go(q, (DAS.real(U32, DI.gsh(s, gs, q)), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n) : D.DynArray<&2, U32> & List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), WK.nthw(xs, q), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n))), Equal.sym(List<&2, Bool>, SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n))), BLI.word_bits(Nat.min(32n, Nat.sub(n, Nat.mul(q, 32n))), WK.nthw(xs, q), SC.take(Bool, ST.flat(SC.drop(U32, xs, 1n+q)), Nat.sub(n, Nat.mul(1n+q, 32n)))), BT.bits_step(xs, n, q, WK.nthw(xs, q), hx))) : {BLI.bits_go(q, (DAS.real(U32, DI.gsh(s, gs, q)), _), n) == BLI.bits_go(q, (DAS.real(U32, DI.gsh(s, gs, q)), SC.take(Bool, ST.flat(SC.drop(U32, xs, q)), Nat.sub(n, Nat.mul(q, 32n)))), n) : D.DynArray<&2, U32> & List<&2, Bool>}
  {==}

def bits_loop(k: Nat, +s: DAS.Shadow<U32>, +gs: {DAS.good(U32, s) == True{} : Bool}, +xs: List<&2, U32>, +c: Nat, +es: {DI.ws(s) == xs : List<&2, U32>}, +ec: {DI.lim(s) == c : Nat}, +n: Nat, +hk: {Nat.is_le(k, SC.length(U32, xs)) == True{} : Bool}) -> BitsOK(k, s, n, xs, c):
  match k:
    case 0n:
      (s, ({==}, (gs, (es, ec))))
    case 1n+ +q:
      +hq = N.succ_le_lt(q, SC.length(U32, xs), hk)
      +gs1 = DI.get_good(s, gs, q)
      +es1 = Equal.trans(List<&2, U32>, DI.ws(DI.gsh(s, gs, q)), DI.ws(s), xs, DI.get_ws(s, gs, q), es)
      +ec1 = Equal.trans(Nat, DI.lim(DI.gsh(s, gs, q)), DI.lim(s), c, DI.get_lim(s, gs, q), ec)
      bits_lift(q, s, n, xs, c, DI.gsh(s, gs, q), bits_rd(s, gs, xs, c, es, ec, n, q, hq), bits_loop(q, DI.gsh(s, gs, q), gs1, xs, c, es1, ec1, n, N.lt_le(q, SC.length(U32, xs), hq)))
