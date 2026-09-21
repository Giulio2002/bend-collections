import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as A
import ../../spec/common.bend as SC
import ../../spec/union_find.bend as S
import ../../src/union_find.bend as U
import ./cells.bend as CL
import ./model.bend as M
import ./union.bend as UN
import ./depth.bend as DP
import ./arr.bend as AR
import ./state.bend as ST
import ./flat.bend as FL
import ../lib/pow2t.bend as PT
import ../../src/pow2.bend as P2

# The constructor: new(n) = new_at(n, depth_for(n)) allocates and fills the
# three arenas, and `initial(n)` is their shadow. This file proves that the
# shadow really is what the constructor builds, that it satisfies the
# representation invariant and that its model is the spec's [0 .. n-1].
#
# The eager arenas are filled by flat loops (roots0, mems0); their mirror
# trees are `tfill` of the uniform block (proofs/union_find/flat.bend), and
# the size arena is Base's `Array.new`, whose mirror is `A.trep`.

def i0(+d: Nat) -> A.Tree<U.Nt>:
  FL.tfill(~U.Nt, ~FL.iota_f, d, SC.pow2(d), A.trep(U.Nt, d, U.N{0n}))

def s0(+d: Nat) -> A.Tree<U.Ms>:
  FL.tfill(~U.Ms, ~FL.solo_f, d, SC.pow2(d), A.trep(U.Ms, d, U.M{Nil{}}))

def i0_perfect(+d: Nat) -> {A.perfect(U.Nt, d, i0(d)) == True{} : Bool}:
  FL.tfill_perfect(~U.Nt, ~FL.iota_f, d, SC.pow2(d), A.trep(U.Nt, d, U.N{0n}), A.trep_perfect(U.Nt, d, U.N{0n}))

def s0_perfect(+d: Nat) -> {A.perfect(U.Ms, d, s0(d)) == True{} : Bool}:
  FL.tfill_perfect(~U.Ms, ~FL.solo_f, d, SC.pow2(d), A.trep(U.Ms, d, U.M{Nil{}}), A.trep_perfect(U.Ms, d, U.M{Nil{}}))

def i0_nth(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(U.Nt, A.slots(U.Nt, i0(d)), j) == Some{U.N{j}} : Maybe<&2, U.Nt>}:
  FL.tfill_nth(~U.Nt, ~FL.iota_f, d, A.trep(U.Nt, d, U.N{0n}), j, hj, A.trep_perfect(U.Nt, d, U.N{0n}))

def s0_nth(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(U.Ms, A.slots(U.Ms, s0(d)), j) == Some{U.M{Con{j, Nil{}}}} : Maybe<&2, U.Ms>}:
  FL.tfill_nth(~U.Ms, ~FL.solo_f, d, A.trep(U.Ms, d, U.M{Nil{}}), j, hj, A.trep_perfect(U.Ms, d, U.M{Nil{}}))

# The executable arenas are the thawed mirrors.
def roots0_ok(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {U.roots0(d) == A.thaw(U.Nt, i0(d)) : Array<U.Nt>}:
  %Equal.sym(Nat, P2.pow2t(d), SC.pow2(d), PT.same(d)) : {U.iota_go(_, Array.new(U.Nt, d, U.N{0n})) == A.thaw(U.Nt, i0(d)) : Array<U.Nt>}
  %Equal.sym(Array<U.Nt>, Array.new(U.Nt, d, U.N{0n}), A.thaw(U.Nt, A.trep(U.Nt, d, U.N{0n})), A.new(U.Nt, d, U.N{0n})) : {U.iota_go(SC.pow2(d), _) == A.thaw(U.Nt, i0(d)) : Array<U.Nt>}
  FL.iota_go_ok(d, SC.pow2(d), A.trep(U.Nt, d, U.N{0n}), hd, N.le_refl(SC.pow2(d)), A.trep_perfect(U.Nt, d, U.N{0n}))

def mems0_ok(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {U.mems0(d) == A.thaw(U.Ms, s0(d)) : Array<U.Ms>}:
  %Equal.sym(Nat, P2.pow2t(d), SC.pow2(d), PT.same(d)) : {U.solo_go(_, Array.new(U.Ms, d, U.M{Nil{}})) == A.thaw(U.Ms, s0(d)) : Array<U.Ms>}
  %Equal.sym(Array<U.Ms>, Array.new(U.Ms, d, U.M{Nil{}}), A.thaw(U.Ms, A.trep(U.Ms, d, U.M{Nil{}})), A.new(U.Ms, d, U.M{Nil{}})) : {U.solo_go(SC.pow2(d), _) == A.thaw(U.Ms, s0(d)) : Array<U.Ms>}
  FL.solo_go_ok(d, SC.pow2(d), A.trep(U.Ms, d, U.M{Nil{}}), hd, N.le_refl(SC.pow2(d)), A.trep_perfect(U.Ms, d, U.M{Nil{}}))

# ---- slot j of each arena ----

def nth_rep(-T: Data, +m: Nat, +v: T, +j: Nat, +h: {Nat.is_lt(j, m) == True{} : Bool}) -> {SC.nth(T, SC.replicate(T, m, v), j) == Some{v} : Maybe<&2, T>}:
  match m j:
    case 0n _:
      Empty.absurd({SC.nth(T, Nil{}, j) == Some{v} : Maybe<&2, T>}, L.false_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, N.not_lt_zero(j)), h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nth_rep(T, p, v, q, h)

def zrep_nth(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(U.Nt, A.slots(U.Nt, A.trep(U.Nt, d, U.N{1n})), j) == Some{U.N{1n}} : Maybe<&2, U.Nt>}:
  %Equal.sym(List<&2, U.Nt>, A.slots(U.Nt, A.trep(U.Nt, d, U.N{1n})), SC.replicate(U.Nt, SC.pow2(d), U.N{1n}), A.trep_slots(U.Nt, d, U.N{1n})) : {SC.nth(U.Nt, _, j) == Some{U.N{1n}} : Maybe<&2, U.Nt>}
  nth_rep(U.Nt, SC.pow2(d), U.N{1n}, j, hj)

# ---- the cell list of the initial arenas ----

def cell0(+y: Nat) -> CL.Cell:
  CL.Cell{y, 1n, Con{y, Nil{}}}

def z0(+d: Nat) -> A.Tree<U.Nt>:
  A.trep(U.Nt, d, U.N{1n})

def cl0(+d: Nat) -> List<&2, CL.Cell>:
  ST.clist(d, i0(d), z0(d), s0(d))

def nt_of(m: Maybe<&2, U.Nt>) -> U.Nt:
  match m:
    case None{}:
      U.N{0n}
    case Some{x}:
      x

def ms_of(m: Maybe<&2, U.Ms>) -> U.Ms:
  match m:
    case None{}:
      U.M{Nil{}}
    case Some{x}:
      x

def nslot(+xs: List<&2, U.Nt>, +j: Nat, +v: Nat, +hj: {Nat.is_lt(j, SC.length(U.Nt, xs)) == True{} : Bool}, +e: {SC.nth(U.Nt, xs, j) == Some{U.N{v}} : Maybe<&2, U.Nt>}) -> {AR.nthn(CL.nmap(xs), j) == v : Nat}:
  Equal.trans(Nat, AR.nthn(CL.nmap(xs), j), U.nval(AR.nths(xs, j)), v,
    Equal.sym(Nat, U.nval(AR.nths(xs, j)), AR.nthn(CL.nmap(xs), j), AR.nval_nths(xs, j)),
    Equal.cong(U.Nt, Nat, U.nval, AR.nths(xs, j), U.N{v},
      Equal.cong(Maybe<&2, U.Nt>, U.Nt, m => nt_of(m), Some{AR.nths(xs, j)}, Some{U.N{v}},
        Equal.trans(Maybe<&2, U.Nt>, Some{AR.nths(xs, j)}, SC.nth(U.Nt, xs, j), Some{U.N{v}},
          Equal.sym(Maybe<&2, U.Nt>, SC.nth(U.Nt, xs, j), Some{AR.nths(xs, j)}, AR.nths_nth(xs, j, hj)),
          e))))

def mslot(+xs: List<&2, U.Ms>, +j: Nat, +v: List<&2, Nat>, +hj: {Nat.is_lt(j, SC.length(U.Ms, xs)) == True{} : Bool}, +e: {SC.nth(U.Ms, xs, j) == Some{U.M{v}} : Maybe<&2, U.Ms>}) -> {AR.nthm(CL.mmap(xs), j) == v : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, AR.nthm(CL.mmap(xs), j), U.mval(AR.msths(xs, j)), v,
    Equal.sym(List<&2, Nat>, U.mval(AR.msths(xs, j)), AR.nthm(CL.mmap(xs), j), AR.mval_msths(xs, j)),
    Equal.cong(U.Ms, List<&2, Nat>, U.mval, AR.msths(xs, j), U.M{v},
      Equal.cong(Maybe<&2, U.Ms>, U.Ms, m => ms_of(m), Some{AR.msths(xs, j)}, Some{U.M{v}},
        Equal.trans(Maybe<&2, U.Ms>, Some{AR.msths(xs, j)}, SC.nth(U.Ms, xs, j), Some{U.M{v}},
          Equal.sym(Maybe<&2, U.Ms>, SC.nth(U.Ms, xs, j), Some{AR.msths(xs, j)}, AR.msths_nth(xs, j, hj)),
          e))))

def len_i(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(U.Nt, A.slots(U.Nt, i0(d)))) == True{} : Bool}:
  A.len_lt(U.Nt, d, i0(d), j, i0_perfect(d), hj)

def len_z(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(U.Nt, A.slots(U.Nt, z0(d)))) == True{} : Bool}:
  A.len_lt(U.Nt, d, z0(d), j, A.trep_perfect(U.Nt, d, U.N{1n}), hj)

def len_s(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {Nat.is_lt(j, SC.length(U.Ms, A.slots(U.Ms, s0(d)))) == True{} : Bool}:
  A.len_lt(U.Ms, d, s0(d), j, s0_perfect(d), hj)

def r_at(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {AR.nthn(AR.rsl(i0(d)), j) == j : Nat}:
  nslot(A.slots(U.Nt, i0(d)), j, j, len_i(d, j, hj), i0_nth(d, j, hj))

def z_at(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {AR.nthn(AR.rsl(z0(d)), j) == 1n : Nat}:
  nslot(A.slots(U.Nt, z0(d)), j, 1n, len_z(d, j, hj), zrep_nth(d, j, hj))

def m_at(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {AR.nthm(AR.msl(s0(d)), j) == Con{j, Nil{}} : List<&2, Nat>}:
  mslot(A.slots(U.Ms, s0(d)), j, Con{j, Nil{}}, len_s(d, j, hj), s0_nth(d, j, hj))

def cl0_nth(+d: Nat, +j: Nat, +hj: {Nat.is_lt(j, SC.pow2(d)) == True{} : Bool}) -> {SC.nth(CL.Cell, cl0(d), j) == Some{cell0(j)} : Maybe<&2, CL.Cell>}:
  Equal.trans(Maybe<&2, CL.Cell>,
    SC.nth(CL.Cell, cl0(d), j),
    Some{CL.Cell{AR.nthn(AR.rsl(i0(d)), j), AR.nthn(AR.rsl(z0(d)), j), AR.nthm(AR.msl(s0(d)), j)}},
    Some{cell0(j)},
    ST.cl_nth(d, i0(d), z0(d), s0(d), j, i0_perfect(d), A.trep_perfect(U.Nt, d, U.N{1n}), s0_perfect(d), hj),
    Equal.trans(Maybe<&2, CL.Cell>,
      Some{CL.Cell{AR.nthn(AR.rsl(i0(d)), j), AR.nthn(AR.rsl(z0(d)), j), AR.nthm(AR.msl(s0(d)), j)}},
      Some{CL.Cell{j, AR.nthn(AR.rsl(z0(d)), j), AR.nthm(AR.msl(s0(d)), j)}},
      Some{cell0(j)},
      Equal.cong(Nat, Maybe<&2, CL.Cell>, q => Some{CL.Cell{q, AR.nthn(AR.rsl(z0(d)), j), AR.nthm(AR.msl(s0(d)), j)}}, AR.nthn(AR.rsl(i0(d)), j), j, r_at(d, j, hj)),
      Equal.trans(Maybe<&2, CL.Cell>,
        Some{CL.Cell{j, AR.nthn(AR.rsl(z0(d)), j), AR.nthm(AR.msl(s0(d)), j)}},
        Some{CL.Cell{j, 1n, AR.nthm(AR.msl(s0(d)), j)}},
        Some{cell0(j)},
        Equal.cong(Nat, Maybe<&2, CL.Cell>, q => Some{CL.Cell{j, q, AR.nthm(AR.msl(s0(d)), j)}}, AR.nthn(AR.rsl(z0(d)), j), 1n, z_at(d, j, hj)),
        Equal.cong(List<&2, Nat>, Maybe<&2, CL.Cell>, q => Some{CL.Cell{j, 1n, q}}, AR.nthm(AR.msl(s0(d)), j), Con{j, Nil{}}, m_at(d, j, hj)))))

# ---- the initial cell list satisfies the invariant ----

def lc0(+d: Nat, +y: Nat, +hy: {Nat.is_lt(y, SC.pow2(d)) == True{} : Bool}) -> {M.lc(cl0(d), y) == cell0(y) : CL.Cell}:
  Equal.cong(Maybe<&2, CL.Cell>, CL.Cell, m => CL.cell_of(m, y), SC.nth(CL.Cell, cl0(d), y), Some{cell0(y)}, cl0_nth(d, y, hy))

def rt0(+d: Nat, +y: Nat, +hy: {Nat.is_lt(y, SC.pow2(d)) == True{} : Bool}) -> {M.rt(cl0(d), y) == y : Nat}:
  Equal.cong(CL.Cell, Nat, c => CL.croot(c), M.lc(cl0(d), y), cell0(y), lc0(d, y, hy))

def or_false(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mem0(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +y: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.mem_ok(cl0(d), y, Con{y, Nil{}}, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.lt_le_trans(j, n, SC.pow2(d), N.succ_le_lt(j, n, hk), hc)
      L.and_intro(M.mem_ok(cl0(d), y, Con{y, Nil{}}, j), M.beq(M.elem(Con{y, Nil{}}, j), Nat.is_eq(M.rt(cl0(d), j), y)),
        mem0(n, d, hc, y, j, N.lt_le(j, n, N.succ_le_lt(j, n, hk))),
        M.beq_of(Bool.or(Nat.is_eq(y, j), False{}), Nat.is_eq(M.rt(cl0(d), j), y),
          Equal.trans(Bool, Bool.or(Nat.is_eq(y, j), False{}), Nat.is_eq(j, y), Nat.is_eq(M.rt(cl0(d), j), y),
            Equal.trans(Bool, Bool.or(Nat.is_eq(y, j), False{}), Nat.is_eq(y, j), Nat.is_eq(j, y), or_false(Nat.is_eq(y, j)), M.is_eq_sym(y, j)),
            Equal.cong(Nat, Bool, q => Nat.is_eq(q, y), j, M.rt(cl0(d), j), Equal.sym(Nat, M.rt(cl0(d), j), j, rt0(d, j, hj))))))

def cnt0_case(+y: Nat, +j: Nat, b: Bool, +eb: {Nat.is_eq(j, y) == b : Bool}) -> {Nat.add(S.eq_bit(Nat.is_lt(y, j)), S.eq_bit(Nat.is_eq(j, y))) == S.eq_bit(Nat.is_lt(y, 1n+j)) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Nat, j, y, N.eq_from_is_eq(j, y, eb)) : {Nat.add(S.eq_bit(Nat.is_lt(y, _)), S.eq_bit(Nat.is_eq(_, y))) == S.eq_bit(Nat.is_lt(y, 1n+_)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(y, y), False{}, N.lt_irrefl(y)) : {Nat.add(S.eq_bit(_), S.eq_bit(Nat.is_eq(y, y))) == S.eq_bit(Nat.is_lt(y, 1n+y)) : Nat}
      %Equal.sym(Bool, Nat.is_eq(y, y), True{}, N.is_eq_refl(y)) : {Nat.add(0n, S.eq_bit(_)) == S.eq_bit(Nat.is_lt(y, 1n+y)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(y, 1n+y), True{}, N.lt_succ(y)) : {1n == S.eq_bit(_) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(j, y), False{}, eb) : {Nat.add(S.eq_bit(Nat.is_lt(y, j)), S.eq_bit(_)) == S.eq_bit(Nat.is_lt(y, 1n+j)) : Nat}
      %UN.lt_succ_ne(y, j, Equal.trans(Bool, Nat.is_eq(y, j), Nat.is_eq(j, y), False{}, M.is_eq_sym(y, j), eb)) : {Nat.add(S.eq_bit(Nat.is_lt(y, j)), 0n) == S.eq_bit(_) : Nat}
      N.add_zero(S.eq_bit(Nat.is_lt(y, j)))

def cnt0(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +y: Nat, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.cnt_r(cl0(d), y, k) == S.eq_bit(Nat.is_lt(y, k)) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, N.not_lt_zero(y)) : {0n == S.eq_bit(_) : Nat}
      {==}
    case 1n+j:
      +hj = N.lt_le_trans(j, n, SC.pow2(d), N.succ_le_lt(j, n, hk), hc)
      %Equal.sym(Nat, M.cnt_r(cl0(d), y, j), S.eq_bit(Nat.is_lt(y, j)), cnt0(n, d, hc, y, j, N.lt_le(j, n, N.succ_le_lt(j, n, hk)))) : {Nat.add(_, S.eq_bit(Nat.is_eq(M.rt(cl0(d), j), y))) == S.eq_bit(Nat.is_lt(y, 1n+j)) : Nat}
      %Equal.sym(Nat, M.rt(cl0(d), j), j, rt0(d, j, hj)) : {Nat.add(S.eq_bit(Nat.is_lt(y, j)), S.eq_bit(Nat.is_eq(_, y))) == S.eq_bit(Nat.is_lt(y, 1n+j)) : Nat}
      cnt0_case(y, j, Nat.is_eq(j, y), {==})

def good0_at(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.good_at(cl0(d), n, y) == True{} : Bool}:
  +hy2 = N.lt_le_trans(y, n, SC.pow2(d), hy, hc)
  +er = rt0(d, y, hy2)
  %Equal.sym(Nat, M.rt(cl0(d), y), y, er) : {Bool.and(Nat.is_lt(_, n), Bool.and(Nat.is_eq(M.rt(cl0(d), _), _), M.root_ok(Nat.is_eq(_, y), cl0(d), n, y))) == True{} : Bool}
  %Equal.sym(Nat, M.rt(cl0(d), y), y, er) : {Bool.and(Nat.is_lt(y, n), Bool.and(Nat.is_eq(_, y), M.root_ok(Nat.is_eq(y, y), cl0(d), n, y))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(y, y), True{}, N.is_eq_refl(y)) : {Bool.and(Nat.is_lt(y, n), Bool.and(_, M.root_ok(_, cl0(d), n, y))) == True{} : Bool}
  L.and_intro(Nat.is_lt(y, n), Bool.and(True{}, M.root_ok(True{}, cl0(d), n, y)), hy,
    L.subst(CL.Cell, c => {UN.RK(cl0(d), n, y, c) == True{} : Bool}, cell0(y), M.lc(cl0(d), y), Equal.sym(CL.Cell, M.lc(cl0(d), y), cell0(y), lc0(d, y, hy2)),
      L.and_intro(Bool.and(Nat.is_lt(y, n), True{}), Bool.and(M.mem_ok(cl0(d), y, Con{y, Nil{}}, n), Nat.is_eq(1n, M.cnt_r(cl0(d), y, n))), L.and_intro(Nat.is_lt(y, n), True{}, hy, {==}),
        L.and_intro(M.mem_ok(cl0(d), y, Con{y, Nil{}}, n), Nat.is_eq(1n, M.cnt_r(cl0(d), y, n)), mem0(n, d, hc, y, n, N.le_refl(n)),
          %Equal.sym(Nat, M.cnt_r(cl0(d), y, n), S.eq_bit(Nat.is_lt(y, n)), cnt0(n, d, hc, y, n, N.le_refl(n))) : {Nat.is_eq(1n, _) == True{} : Bool}
          %Equal.sym(Bool, Nat.is_lt(y, n), True{}, hy) : {Nat.is_eq(1n, S.eq_bit(_)) == True{} : Bool}
          {==}))))

def good0(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.good(cl0(d), n, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(M.good(cl0(d), n, j), M.good_at(cl0(d), n, j), good0(n, d, hc, j, N.lt_le(j, n, N.succ_le_lt(j, n, hk))), good0_at(n, d, hc, j, N.succ_le_lt(j, n, hk)))

def fix0(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.cnt_fix(cl0(d), k) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.lt_le_trans(j, n, SC.pow2(d), N.succ_le_lt(j, n, hk), hc)
      %Equal.sym(Nat, M.cnt_fix(cl0(d), j), j, fix0(n, d, hc, j, N.lt_le(j, n, N.succ_le_lt(j, n, hk)))) : {Nat.add(_, S.eq_bit(Nat.is_eq(M.rt(cl0(d), j), j))) == 1n+j : Nat}
      %Equal.sym(Nat, M.rt(cl0(d), j), j, rt0(d, j, hj)) : {Nat.add(j, S.eq_bit(Nat.is_eq(_, j))) == 1n+j : Nat}
      %Equal.sym(Bool, Nat.is_eq(j, j), True{}, N.is_eq_refl(j)) : {Nat.add(j, S.eq_bit(_)) == 1n+j : Nat}
      Equal.trans(Nat, Nat.add(j, 1n), Nat.add(1n, j), 1n+j, N.add_comm(j, 1n), {==})

def iota_snoc(+k: Nat, +off: Nat) -> {S.iota(1n+k, off) == SC.snoc(Nat, S.iota(k, off), Nat.add(off, k)) : List<&2, Nat>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(off, 0n), off, N.add_zero(off)) : {Con{off, Nil{}} == Con{_, Nil{}} : List<&2, Nat>}
      {==}
    case 1n+q:
      %Equal.sym(List<&2, Nat>, S.iota(1n+q, 1n+off), SC.snoc(Nat, S.iota(q, 1n+off), Nat.add(1n+off, q)), iota_snoc(q, 1n+off)) : {Con{off, _} == SC.snoc(Nat, Con{off, S.iota(q, 1n+off)}, Nat.add(off, 1n+q)) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(off, 1n+q), 1n+Nat.add(off, q), N.add_succ(off, q)) : {Con{off, SC.snoc(Nat, S.iota(q, 1n+off), 1n+Nat.add(off, q))} == Con{off, SC.snoc(Nat, S.iota(q, 1n+off), _)} : List<&2, Nat>}
      {==}

def labs0(+n: Nat, +d: Nat, +hc: {Nat.is_le(n, SC.pow2(d)) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.labs(cl0(d), k) == S.iota(k, 0n) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +hj = N.lt_le_trans(j, n, SC.pow2(d), N.succ_le_lt(j, n, hk), hc)
      %Equal.sym(List<&2, Nat>, S.iota(1n+j, 0n), SC.snoc(Nat, S.iota(j, 0n), j), iota_snoc(j, 0n)) : {SC.snoc(Nat, M.labs(cl0(d), j), M.rt(cl0(d), j)) == _ : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, M.labs(cl0(d), j), S.iota(j, 0n), labs0(n, d, hc, j, N.lt_le(j, n, N.succ_le_lt(j, n, hk)))) : {SC.snoc(Nat, _, M.rt(cl0(d), j)) == SC.snoc(Nat, S.iota(j, 0n), j) : List<&2, Nat>}
      %Equal.sym(Nat, M.rt(cl0(d), j), j, rt0(d, j, hj)) : {SC.snoc(Nat, S.iota(j, 0n), _) == SC.snoc(Nat, S.iota(j, 0n), j) : List<&2, Nat>}
      {==}

# ---- the initial shadow ----

# The shadow of the constructor: the arenas new_at allocates and fills.
def initial(+n: Nat) -> ST.Sh:
  {ST.Sh{n, U.depth_for(n), i0(U.depth_for(n)), z0(U.depth_for(n)), s0(U.depth_for(n)), n} : ST.Sh}

def new_real(+n: Nat) -> {U.new(n) == ST.real(initial(n)) : U.UnionFind}:
  +d = U.depth_for(n)
  +hd = DP.depth_lt(n)
  %Equal.sym(Array<U.Nt>, U.roots0(d), A.thaw(U.Nt, i0(d)), roots0_ok(d, hd)) : {U.UF{n, d, _, U.sizes0(d), U.mems0(d), n} == ST.real(initial(n)) : U.UnionFind}
  %Equal.sym(Array<U.Nt>, U.sizes0(d), A.thaw(U.Nt, z0(d)), A.new(U.Nt, d, U.N{1n})) : {U.UF{n, d, A.thaw(U.Nt, i0(d)), _, U.mems0(d), n} == ST.real(initial(n)) : U.UnionFind}
  %Equal.sym(Array<U.Ms>, U.mems0(d), A.thaw(U.Ms, s0(d)), mems0_ok(d, hd)) : {U.UF{n, d, A.thaw(U.Nt, i0(d)), A.thaw(U.Nt, z0(d)), _, n} == ST.real(initial(n)) : U.UnionFind}
  {==}

def new_good(+n: Nat, +h: {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}) -> {ST.good(initial(n)) == True{} : Bool}:
  ST.g_mk(n, U.depth_for(n), i0(U.depth_for(n)), z0(U.depth_for(n)), s0(U.depth_for(n)), n,
    N.is_eq_refl(U.depth_for(n)),
    i0_perfect(U.depth_for(n)),
    A.trep_perfect(U.Nt, U.depth_for(n), U.N{1n}),
    s0_perfect(U.depth_for(n)),
    h,
    good0(n, U.depth_for(n), h, n, N.le_refl(n)),
    M.eq_true(n, M.cnt_fix(cl0(U.depth_for(n)), n), Equal.sym(Nat, M.cnt_fix(cl0(U.depth_for(n)), n), n, fix0(n, U.depth_for(n), h, n, N.le_refl(n)))))

def new_model(+n: Nat, +h: {Nat.is_le(n, SC.pow2(U.depth_for(n))) == True{} : Bool}) -> {ST.model(initial(n)) == S.new(n) : List<&2, Nat>}:
  labs0(n, U.depth_for(n), h, n, N.le_refl(n))
