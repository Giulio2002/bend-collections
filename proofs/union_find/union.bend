import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../../spec/common.bend as SC
import ../../spec/union_find.bend as S
import ../../src/union_find.bend as U
import ./cells.bend as CL
import ./model.bend as M

# Merging two distinct classes: the members of `small` are relinked to
# `big`, whose cell gets the combined size and member list. At the list
# level the result is cl2; every label becomes sw(y), the spec relabelling.

def relinked(b: Bool, c: CL.Cell, +r: Nat) -> CL.Cell:
  match b:
    case True{}:
      CL.with_root(c, r)
    case False{}:
      c

def rl(ms: List<&2, Nat>, +cl: List<&2, CL.Cell>, +big: Nat) -> List<&2, CL.Cell>:
  match ms:
    case Nil{}:
      cl
    case Con{+m, rest}:
      rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big)

def newcell(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat) -> CL.Cell:
  CL.Cell{big, Nat.add(M.sz(cl, big), M.sz(cl, small)), SC.append(Nat, M.ms(cl, small), M.ms(cl, big))}

def cl2(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat) -> List<&2, CL.Cell>:
  SC.update(CL.Cell, rl(M.ms(cl, small), cl, big), big, newcell(cl, big, small))

def sw(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +y: Nat) -> Nat:
  S.swap_label(Nat.is_eq(M.rt(cl, y), small), big, M.rt(cl, y))

# ---- cells ----

def wr_root(+c: CL.Cell, +r: Nat) -> {CL.croot(CL.with_root(c, r)) == r : Nat}:
  match c:
    case CL.Cell{q, z, m}:
      {==}

def wr_idem(+c: CL.Cell, +r: Nat) -> {CL.with_root(CL.with_root(c, r), r) == CL.with_root(c, r) : CL.Cell}:
  match c:
    case CL.Cell{q, z, m}:
      {==}

def relinked_wr(b: Bool, +c: CL.Cell, +r: Nat) -> {relinked(b, CL.with_root(c, r), r) == CL.with_root(c, r) : CL.Cell}:
  match b:
    case True{}:
      wr_idem(c, r)
    case False{}:
      {==}

def lc_same(+cl: List<&2, CL.Cell>, +i: Nat, +c: CL.Cell, +h: {Nat.is_lt(i, SC.length(CL.Cell, cl)) == True{} : Bool}) -> {M.lc(SC.update(CL.Cell, cl, i, c), i) == c : CL.Cell}:
  %Equal.sym(Maybe<&2, CL.Cell>, SC.nth(CL.Cell, SC.update(CL.Cell, cl, i, c), i), Some{c}, LL.nth_update_same(CL.Cell, cl, i, c, h)) : {CL.cell_of(_, i) == c : CL.Cell}
  {==}

def lc_other(+cl: List<&2, CL.Cell>, +i: Nat, +j: Nat, +c: CL.Cell, +ne: {Nat.is_eq(i, j) == False{} : Bool}) -> {M.lc(SC.update(CL.Cell, cl, i, c), j) == M.lc(cl, j) : CL.Cell}:
  %Equal.sym(Maybe<&2, CL.Cell>, SC.nth(CL.Cell, SC.update(CL.Cell, cl, i, c), j), SC.nth(CL.Cell, cl, j), LL.nth_update_other(CL.Cell, cl, i, j, c, ne)) : {CL.cell_of(_, j) == M.lc(cl, j) : CL.Cell}
  {==}

def length_rl(+ms: List<&2, Nat>, +cl: List<&2, CL.Cell>, +big: Nat) -> {SC.length(CL.Cell, rl(ms, cl, big)) == SC.length(CL.Cell, cl) : Nat}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, rest}:
      Equal.trans(Nat, SC.length(CL.Cell, rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big)), SC.length(CL.Cell, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big))), SC.length(CL.Cell, cl),
        length_rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big),
        LL.length_update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)))

def rl_case(+m: Nat, +rest: List<&2, Nat>, +cl: List<&2, CL.Cell>, +big: Nat, +y: Nat, b: Bool, +eb: {Nat.is_eq(m, y) == b : Bool}, +hy: {Nat.is_lt(y, SC.length(CL.Cell, cl)) == True{} : Bool}, +ih: {M.lc(rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big), y) == relinked(M.elem(rest, y), M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), y), big) : CL.Cell}) -> {M.lc(rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big), y) == relinked(Bool.or(b, M.elem(rest, y)), M.lc(cl, y), big) : CL.Cell}:
  match b:
    case True{}:
      +e = N.eq_from_is_eq(m, y, eb)
      +hm = L.subst(Nat, q => {Nat.is_lt(q, SC.length(CL.Cell, cl)) == True{} : Bool}, y, m, Equal.sym(Nat, m, y, e), hy)
      %Equal.sym(CL.Cell, M.lc(rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big), y), relinked(M.elem(rest, y), M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), y), big), ih) : {_ == CL.with_root(M.lc(cl, y), big) : CL.Cell}
      %e : {relinked(M.elem(rest, _), M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), _), big) == CL.with_root(M.lc(cl, _), big) : CL.Cell}
      %Equal.sym(CL.Cell, M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), m), CL.with_root(M.lc(cl, m), big), lc_same(cl, m, CL.with_root(M.lc(cl, m), big), hm)) : {relinked(M.elem(rest, m), _, big) == CL.with_root(M.lc(cl, m), big) : CL.Cell}
      relinked_wr(M.elem(rest, m), M.lc(cl, m), big)
    case False{}:
      %Equal.sym(CL.Cell, M.lc(rl(rest, SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), big), y), relinked(M.elem(rest, y), M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), y), big), ih) : {_ == relinked(M.elem(rest, y), M.lc(cl, y), big) : CL.Cell}
      %Equal.sym(CL.Cell, M.lc(SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big)), y), M.lc(cl, y), lc_other(cl, m, y, CL.with_root(M.lc(cl, m), big), eb)) : {relinked(M.elem(rest, y), _, big) == relinked(M.elem(rest, y), M.lc(cl, y), big) : CL.Cell}
      {==}

def rl_at(+ms: List<&2, Nat>, +cl: List<&2, CL.Cell>, +big: Nat, +y: Nat, +hy: {Nat.is_lt(y, SC.length(CL.Cell, cl)) == True{} : Bool}) -> {M.lc(rl(ms, cl, big), y) == relinked(M.elem(ms, y), M.lc(cl, y), big) : CL.Cell}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +rest}:
      +cl1 = SC.update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big))
      +hy1 = L.subst(Nat, q => {Nat.is_lt(y, q) == True{} : Bool}, SC.length(CL.Cell, cl), SC.length(CL.Cell, cl1), Equal.sym(Nat, SC.length(CL.Cell, cl1), SC.length(CL.Cell, cl), LL.length_update(CL.Cell, cl, m, CL.with_root(M.lc(cl, m), big))), hy)
      rl_case(m, rest, cl, big, y, Nat.is_eq(m, y), {==}, hy, rl_at(rest, cl1, big, y, hy1))

# ---- the merged cells, pointwise ----

def lc2_big(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +hb: {Nat.is_lt(big, SC.length(CL.Cell, cl)) == True{} : Bool}) -> {M.lc(cl2(cl, big, small), big) == newcell(cl, big, small) : CL.Cell}:
  lc_same(rl(M.ms(cl, small), cl, big), big, newcell(cl, big, small), L.subst(Nat, q => {Nat.is_lt(big, q) == True{} : Bool}, SC.length(CL.Cell, cl), SC.length(CL.Cell, rl(M.ms(cl, small), cl, big)), Equal.sym(Nat, SC.length(CL.Cell, rl(M.ms(cl, small), cl, big)), SC.length(CL.Cell, cl), length_rl(M.ms(cl, small), cl, big)), hb))

def lc2_other(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +y: Nat, +ne: {Nat.is_eq(big, y) == False{} : Bool}, +hy: {Nat.is_lt(y, SC.length(CL.Cell, cl)) == True{} : Bool}) -> {M.lc(cl2(cl, big, small), y) == relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big) : CL.Cell}:
  Equal.trans(CL.Cell, M.lc(cl2(cl, big, small), y), M.lc(rl(M.ms(cl, small), cl, big), y), relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big),
    lc_other(rl(M.ms(cl, small), cl, big), big, y, newcell(cl, big, small), ne),
    rl_at(M.ms(cl, small), cl, big, y, hy))

# ---- merge context ----
# H: cl satisfies the invariant for n, n fits in cl, and big, small are
# distinct representatives below n.

def H(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat) -> Bool:
  Bool.and(M.good(cl, n, n), Bool.and(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))))))

def h_good(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {M.good(cl, n, n) == True{} : Bool}:
  L.and_left(M.good(cl, n, n), Bool.and(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))))), h)

def h_r1(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Bool.and(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))))) == True{} : Bool}:
  L.and_right(M.good(cl, n, n), Bool.and(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))))), h)

def h_len(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_le(n, SC.length(CL.Cell, cl)) == True{} : Bool}:
  L.and_left(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))))), h_r1(cl, n, big, small, h))

def h_r2(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))))) == True{} : Bool}:
  L.and_right(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))))), h_r1(cl, n, big, small, h))

def h_big(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_lt(big, n) == True{} : Bool}:
  L.and_left(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))), h_r2(cl, n, big, small, h))

def h_r3(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))) == True{} : Bool}:
  L.and_right(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))), h_r2(cl, n, big, small, h))

def h_small(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_lt(small, n) == True{} : Bool}:
  L.and_left(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))), h_r3(cl, n, big, small, h))

def h_r4(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))) == True{} : Bool}:
  L.and_right(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))), h_r3(cl, n, big, small, h))

def h_rb(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_eq(M.rt(cl, big), big) == True{} : Bool}:
  L.and_left(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))), h_r4(cl, n, big, small, h))

def h_r5(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))) == True{} : Bool}:
  L.and_right(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))), h_r4(cl, n, big, small, h))

def h_rs(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_eq(M.rt(cl, small), small) == True{} : Bool}:
  L.and_left(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)), h_r5(cl, n, big, small, h))

def h_ne(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_eq(big, small) == False{} : Bool}:
  L.not_true(Nat.is_eq(big, small), L.and_right(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)), h_r5(cl, n, big, small, h)))

def h_mk(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +g: {M.good(cl, n, n) == True{} : Bool}, +hl: {Nat.is_le(n, SC.length(CL.Cell, cl)) == True{} : Bool}, +hb: {Nat.is_lt(big, n) == True{} : Bool}, +hs: {Nat.is_lt(small, n) == True{} : Bool}, +rb: {Nat.is_eq(M.rt(cl, big), big) == True{} : Bool}, +rs: {Nat.is_eq(M.rt(cl, small), small) == True{} : Bool}, +ne: {Nat.is_eq(big, small) == False{} : Bool}) -> {H(cl, n, big, small) == True{} : Bool}:
  L.and_intro(M.good(cl, n, n), Bool.and(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))))), g,
    L.and_intro(Nat.is_le(n, SC.length(CL.Cell, cl)), Bool.and(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))))), hl,
      L.and_intro(Nat.is_lt(big, n), Bool.and(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))))), hb,
        L.and_intro(Nat.is_lt(small, n), Bool.and(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)))), hs,
          L.and_intro(Nat.is_eq(M.rt(cl, big), big), Bool.and(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small))), rb,
            L.and_intro(Nat.is_eq(M.rt(cl, small), small), Bool.not(Nat.is_eq(big, small)), rs, L.not_false(Nat.is_eq(big, small), ne)))))))

# y < n implies y < |cl|.
def in_cl(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {Nat.is_lt(y, SC.length(CL.Cell, cl)) == True{} : Bool}:
  N.lt_le_trans(y, n, SC.length(CL.Cell, cl), hy, h_len(cl, n, big, small, h))

def at(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.good_at(cl, n, y) == True{} : Bool}:
  M.good_elim(cl, n, n, y, h_good(cl, n, big, small, h), hy)

def root_of_small(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {M.root_ok(True{}, cl, n, small) == True{} : Bool}:
  M.at_root(cl, n, small, at(cl, n, big, small, h, small, h_small(cl, n, big, small, h)), h_rs(cl, n, big, small, h))

def root_of_big(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {M.root_ok(True{}, cl, n, big) == True{} : Bool}:
  M.at_root(cl, n, big, at(cl, n, big, small, h, big, h_big(cl, n, big, small, h)), h_rb(cl, n, big, small, h))

# Membership in the small class is exactly "labelled small".
def in_small(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.elem(M.ms(cl, small), y) == Nat.is_eq(M.rt(cl, y), small) : Bool}:
  M.mem_elim(cl, small, M.ms(cl, small), n, y, M.root_mem(cl, n, small, root_of_small(cl, n, big, small, h)), hy)

def in_big(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.elem(M.ms(cl, big), y) == Nat.is_eq(M.rt(cl, y), big) : Bool}:
  M.mem_elim(cl, big, M.ms(cl, big), n, y, M.root_mem(cl, n, big, root_of_big(cl, n, big, small, h)), hy)

# ---- the new label of every element ----

def croot_relinked(b: Bool, +c: CL.Cell, +r: Nat) -> {CL.croot(relinked(b, c, r)) == S.swap_label(b, r, CL.croot(c)) : Nat}:
  match b:
    case True{}:
      wr_root(c, r)
    case False{}:
      {==}

# A representative other than `small` keeps its label.
def sw_root(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +r: Nat, +er: {M.rt(cl, r) == r : Nat}, +ns: {Nat.is_eq(r, small) == False{} : Bool}) -> {sw(cl, big, small, r) == r : Nat}:
  L.subst(Nat, q => {S.swap_label(Nat.is_eq(q, small), big, q) == r : Nat}, r, M.rt(cl, r), Equal.sym(Nat, M.rt(cl, r), r, er),
    %Equal.sym(Bool, Nat.is_eq(r, small), False{}, ns) : {S.swap_label(_, big, r) == r : Nat}
    {==})

def rt2_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(big, y) == b : Bool}) -> {M.rt(cl2(cl, big, small), y) == sw(cl, big, small, y) : Nat}:
  match b:
    case True{}:
      +e = N.eq_from_is_eq(big, y, eb)
      %e : {M.rt(cl2(cl, big, small), _) == sw(cl, big, small, _) : Nat}
      %Equal.sym(CL.Cell, M.lc(cl2(cl, big, small), big), newcell(cl, big, small), lc2_big(cl, big, small, in_cl(cl, n, big, small, h, big, h_big(cl, n, big, small, h)))) : {CL.croot(_) == sw(cl, big, small, big) : Nat}
      Equal.sym(Nat, sw(cl, big, small, big), big, sw_root(cl, big, small, big, N.eq_from_is_eq(M.rt(cl, big), big, h_rb(cl, n, big, small, h)), h_ne(cl, n, big, small, h)))
    case False{}:
      %Equal.sym(CL.Cell, M.lc(cl2(cl, big, small), y), relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big), lc2_other(cl, big, small, y, eb, in_cl(cl, n, big, small, h, y, hy))) : {CL.croot(_) == sw(cl, big, small, y) : Nat}
      %Equal.sym(Nat, CL.croot(relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big)), S.swap_label(M.elem(M.ms(cl, small), y), big, CL.croot(M.lc(cl, y))), croot_relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big)) : {_ == sw(cl, big, small, y) : Nat}
      %Equal.sym(Bool, M.elem(M.ms(cl, small), y), Nat.is_eq(M.rt(cl, y), small), in_small(cl, n, big, small, h, y, hy)) : {S.swap_label(_, big, M.rt(cl, y)) == sw(cl, big, small, y) : Nat}
      {==}

def rt2(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.rt(cl2(cl, big, small), y) == sw(cl, big, small, y) : Nat}:
  rt2_case(cl, n, big, small, h, y, hy, Nat.is_eq(big, y), {==})

# ---- pointwise comparisons of old and new labels ----

def ctx_ne_sym(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {Nat.is_eq(small, big) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(small, big), Nat.is_eq(big, small), False{}, M.is_eq_sym(small, big), h_ne(cl, n, big, small, h))

def pwo_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +r: Nat, +nb: {Nat.is_eq(r, big) == False{} : Bool}, +ns: {Nat.is_eq(r, small) == False{} : Bool}, cs: Bool, +ecs: {Nat.is_eq(M.rt(cl, j), small) == cs : Bool}) -> {Nat.is_eq(S.swap_label(Nat.is_eq(M.rt(cl, j), small), big, M.rt(cl, j)), r) == Nat.is_eq(M.rt(cl, j), r) : Bool}:
  match cs:
    case True{}:
      +e = N.eq_from_is_eq(M.rt(cl, j), small, ecs)
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), True{}, ecs) : {Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), r) == Nat.is_eq(M.rt(cl, j), r) : Bool}
      Equal.trans(Bool, Nat.is_eq(big, r), False{}, Nat.is_eq(M.rt(cl, j), r),
        Equal.trans(Bool, Nat.is_eq(big, r), Nat.is_eq(r, big), False{}, M.is_eq_sym(big, r), nb),
        Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), r), False{}, M.neq_trans(M.rt(cl, j), small, r, e, Equal.trans(Bool, Nat.is_eq(small, r), Nat.is_eq(r, small), False{}, M.is_eq_sym(small, r), ns))))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), False{}, ecs) : {Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), r) == Nat.is_eq(M.rt(cl, j), r) : Bool}
      {==}

# For a label r outside {big, small}, "labelled r" is unchanged.
def pw_other(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +r: Nat, +nb: {Nat.is_eq(r, big) == False{} : Bool}, +ns: {Nat.is_eq(r, small) == False{} : Bool}) -> {Nat.is_eq(M.rt(cl2(cl, big, small), j), r) == Nat.is_eq(M.rt(cl, j), r) : Bool}:
  %Equal.sym(Nat, M.rt(cl2(cl, big, small), j), sw(cl, big, small, j), rt2(cl, n, big, small, h, j, hj)) : {Nat.is_eq(_, r) == Nat.is_eq(M.rt(cl, j), r) : Bool}
  pwo_case(cl, n, big, small, h, j, r, nb, ns, Nat.is_eq(M.rt(cl, j), small), {==})

def pwm_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, cs: Bool, +ecs: {Nat.is_eq(M.rt(cl, j), small) == cs : Bool}) -> {S.eq_bit(Nat.is_eq(S.swap_label(Nat.is_eq(M.rt(cl, j), small), big, M.rt(cl, j)), big)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(Nat.is_eq(M.rt(cl, j), small))) : Nat}:
  match cs:
    case True{}:
      +e = N.eq_from_is_eq(M.rt(cl, j), small, ecs)
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), True{}, ecs) : {S.eq_bit(Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), big)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(_)) : Nat}
      %Equal.sym(Bool, Nat.is_eq(big, big), True{}, N.is_eq_refl(big)) : {S.eq_bit(_) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), 1n) : Nat}
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), big), False{}, M.neq_trans(M.rt(cl, j), small, big, e, ctx_ne_sym(cl, n, big, small, h))) : {1n == Nat.add(S.eq_bit(_), 1n) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), False{}, ecs) : {S.eq_bit(Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), big)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(_)) : Nat}
      Equal.sym(Nat, Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), 0n), S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), N.add_zero(S.eq_bit(Nat.is_eq(M.rt(cl, j), big))))

# "Labelled big" afterwards = "labelled big or small" before.
def pw_merge(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> {S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), big)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(Nat.is_eq(M.rt(cl, j), small))) : Nat}:
  %Equal.sym(Nat, M.rt(cl2(cl, big, small), j), sw(cl, big, small, j), rt2(cl, n, big, small, h, j, hj)) : {S.eq_bit(Nat.is_eq(_, big)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(Nat.is_eq(M.rt(cl, j), small))) : Nat}
  pwm_case(cl, n, big, small, h, j, Nat.is_eq(M.rt(cl, j), small), {==})

def pwb_case(+cl: List<&2, CL.Cell>, +big: Nat, +small: Nat, +j: Nat, cs: Bool, +ecs: {Nat.is_eq(M.rt(cl, j), small) == cs : Bool}) -> {M.beq(Bool.or(Nat.is_eq(M.rt(cl, j), small), Nat.is_eq(M.rt(cl, j), big)), Nat.is_eq(S.swap_label(Nat.is_eq(M.rt(cl, j), small), big, M.rt(cl, j)), big)) == True{} : Bool}:
  match cs:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), True{}, ecs) : {M.beq(Bool.or(_, Nat.is_eq(M.rt(cl, j), big)), Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), big)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(big, big), True{}, N.is_eq_refl(big)) : {M.beq(True{}, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), False{}, ecs) : {M.beq(Bool.or(_, Nat.is_eq(M.rt(cl, j), big)), Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), big)) == True{} : Bool}
      M.beq_refl(Nat.is_eq(M.rt(cl, j), big))

def pw_memb(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}) -> {M.beq(Bool.or(Nat.is_eq(M.rt(cl, j), small), Nat.is_eq(M.rt(cl, j), big)), Nat.is_eq(M.rt(cl2(cl, big, small), j), big)) == True{} : Bool}:
  %Equal.sym(Nat, M.rt(cl2(cl, big, small), j), sw(cl, big, small, j), rt2(cl, n, big, small, h, j, hj)) : {M.beq(Bool.or(Nat.is_eq(M.rt(cl, j), small), Nat.is_eq(M.rt(cl, j), big)), Nat.is_eq(_, big)) == True{} : Bool}
  pwb_case(cl, big, small, j, Nat.is_eq(M.rt(cl, j), small), {==})

def pwf_big(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +e: {M.rt(cl, j) == small : Nat}, b: Bool, +eb: {Nat.is_eq(big, j) == b : Bool}) -> {Nat.is_eq(big, j) == False{} : Bool}:
  match b:
    case True{}:
      +ej = N.eq_from_is_eq(big, j, eb)
      +er = Equal.trans(Nat, big, M.rt(cl, big), small, Equal.sym(Nat, M.rt(cl, big), big, N.eq_from_is_eq(M.rt(cl, big), big, h_rb(cl, n, big, small, h))), L.subst(Nat, q => {M.rt(cl, q) == small : Nat}, j, big, Equal.sym(Nat, big, j, ej), e))
      Empty.absurd({Nat.is_eq(big, j) == False{} : Bool}, L.true_false(Equal.trans(Bool, True{}, Nat.is_eq(big, small), False{}, Equal.sym(Bool, Nat.is_eq(big, small), True{}, M.eq_true(big, small, er)), h_ne(cl, n, big, small, h))))
    case False{}:
      eb

def pwf_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +nsj: {Nat.is_eq(j, small) == False{} : Bool}, cs: Bool, +ecs: {Nat.is_eq(M.rt(cl, j), small) == cs : Bool}) -> {Nat.is_eq(S.swap_label(Nat.is_eq(M.rt(cl, j), small), big, M.rt(cl, j)), j) == Nat.is_eq(M.rt(cl, j), j) : Bool}:
  match cs:
    case True{}:
      +e = N.eq_from_is_eq(M.rt(cl, j), small, ecs)
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), True{}, ecs) : {Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), j) == Nat.is_eq(M.rt(cl, j), j) : Bool}
      Equal.trans(Bool, Nat.is_eq(big, j), False{}, Nat.is_eq(M.rt(cl, j), j),
        pwf_big(cl, n, big, small, h, j, e, Nat.is_eq(big, j), {==}),
        Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), j), False{}, M.neq_trans(M.rt(cl, j), small, j, e, Equal.trans(Bool, Nat.is_eq(small, j), Nat.is_eq(j, small), False{}, M.is_eq_sym(small, j), nsj))))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, j), small), False{}, ecs) : {Nat.is_eq(S.swap_label(_, big, M.rt(cl, j)), j) == Nat.is_eq(M.rt(cl, j), j) : Bool}
      {==}

# Away from `small`, being a representative is unchanged.
def pw_fix(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, +nsj: {Nat.is_eq(j, small) == False{} : Bool}) -> {Nat.is_eq(M.rt(cl2(cl, big, small), j), j) == Nat.is_eq(M.rt(cl, j), j) : Bool}:
  %Equal.sym(Nat, M.rt(cl2(cl, big, small), j), sw(cl, big, small, j), rt2(cl, n, big, small, h, j, hj)) : {Nat.is_eq(_, j) == Nat.is_eq(M.rt(cl, j), j) : Bool}
  pwf_case(cl, n, big, small, h, j, nsj, Nat.is_eq(M.rt(cl, j), small), {==})

# ---- arithmetic / list helpers ----

def add_swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), N.add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), N.add_assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %N.add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  %N.add_assoc(c, b, d) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, _) : Nat}
  %N.add_comm(c, b) : {Nat.add(a, Nat.add(_, d)) == Nat.add(a, Nat.add(Nat.add(c, b), d)) : Nat}
  {==}

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def elem_append(+a: List<&2, Nat>, +b: List<&2, Nat>, +y: Nat) -> {M.elem(SC.append(Nat, a, b), y) == Bool.or(M.elem(a, y), M.elem(b, y)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, t}:
      %Equal.sym(Bool, M.elem(SC.append(Nat, t, b), y), Bool.or(M.elem(t, y), M.elem(b, y)), elem_append(t, b, y)) : {Bool.or(Nat.is_eq(x, y), _) == Bool.or(Bool.or(Nat.is_eq(x, y), M.elem(t, y)), M.elem(b, y)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(Nat.is_eq(x, y), M.elem(t, y)), M.elem(b, y)), Bool.or(Nat.is_eq(x, y), Bool.or(M.elem(t, y), M.elem(b, y))), or_assoc(Nat.is_eq(x, y), M.elem(t, y), M.elem(b, y)))

def below_append(+a: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +ha: {M.below(a, n) == True{} : Bool}, +hb: {M.below(b, n) == True{} : Bool}) -> {M.below(SC.append(Nat, a, b), n) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{x, t}:
      L.and_intro(Nat.is_lt(x, n), M.below(SC.append(Nat, t, b), n), L.and_left(Nat.is_lt(x, n), M.below(t, n), ha), below_append(t, b, n, L.and_right(Nat.is_lt(x, n), M.below(t, n), ha), hb))

def step_lt(+j: Nat, +n: Nat, +hk: {Nat.is_le(1n+j, n) == True{} : Bool}) -> {Nat.is_lt(j, n) == True{} : Bool}:
  N.succ_le_lt(j, n, hk)

def step_le(+j: Nat, +n: Nat, +hk: {Nat.is_le(1n+j, n) == True{} : Bool}) -> {Nat.is_le(j, n) == True{} : Bool}:
  N.lt_le(j, n, N.succ_le_lt(j, n, hk))

# ---- counts and member lists after the merge ----

def cnt_other(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +r: Nat, +nb: {Nat.is_eq(r, big) == False{} : Bool}, +ns: {Nat.is_eq(r, small) == False{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.cnt_r(cl2(cl, big, small), r, k) == M.cnt_r(cl, r, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Nat, M.cnt_r(cl2(cl, big, small), r, j), M.cnt_r(cl, r, j), cnt_other(cl, n, big, small, h, r, nb, ns, j, step_le(j, n, hk))) : {Nat.add(_, S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), r))) == Nat.add(M.cnt_r(cl, r, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), r))) : Nat}
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl2(cl, big, small), j), r), Nat.is_eq(M.rt(cl, j), r), pw_other(cl, n, big, small, h, j, step_lt(j, n, hk), r, nb, ns)) : {Nat.add(M.cnt_r(cl, r, j), S.eq_bit(_)) == Nat.add(M.cnt_r(cl, r, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), r))) : Nat}
      {==}

def mem_other(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +r: Nat, +nb: {Nat.is_eq(r, big) == False{} : Bool}, +ns: {Nat.is_eq(r, small) == False{} : Bool}, +m: List<&2, Nat>, +hm: {M.mem_ok(cl, r, m, n) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.mem_ok(cl2(cl, big, small), r, m, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(M.mem_ok(cl2(cl, big, small), r, m, j), M.beq(M.elem(m, j), Nat.is_eq(M.rt(cl2(cl, big, small), j), r)),
        mem_other(cl, n, big, small, h, r, nb, ns, m, hm, j, step_le(j, n, hk)),
        M.beq_of(M.elem(m, j), Nat.is_eq(M.rt(cl2(cl, big, small), j), r),
          Equal.trans(Bool, M.elem(m, j), Nat.is_eq(M.rt(cl, j), r), Nat.is_eq(M.rt(cl2(cl, big, small), j), r),
            M.mem_elim(cl, r, m, n, j, hm, step_lt(j, n, hk)),
            Equal.sym(Bool, Nat.is_eq(M.rt(cl2(cl, big, small), j), r), Nat.is_eq(M.rt(cl, j), r), pw_other(cl, n, big, small, h, j, step_lt(j, n, hk), r, nb, ns)))))

def cnt_merge(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.cnt_r(cl2(cl, big, small), big, k) == Nat.add(M.cnt_r(cl, big, k), M.cnt_r(cl, small, k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Nat, M.cnt_r(cl2(cl, big, small), big, j), Nat.add(M.cnt_r(cl, big, j), M.cnt_r(cl, small, j)), cnt_merge(cl, n, big, small, h, j, step_le(j, n, hk))) : {Nat.add(_, S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), big))) == Nat.add(Nat.add(M.cnt_r(cl, big, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), big))), Nat.add(M.cnt_r(cl, small, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), small)))) : Nat}
      %Equal.sym(Nat, S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), big)), Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(Nat.is_eq(M.rt(cl, j), small))), pw_merge(cl, n, big, small, h, j, step_lt(j, n, hk))) : {Nat.add(Nat.add(M.cnt_r(cl, big, j), M.cnt_r(cl, small, j)), _) == Nat.add(Nat.add(M.cnt_r(cl, big, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), big))), Nat.add(M.cnt_r(cl, small, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), small)))) : Nat}
      add_swap4(M.cnt_r(cl, big, j), M.cnt_r(cl, small, j), S.eq_bit(Nat.is_eq(M.rt(cl, j), big)), S.eq_bit(Nat.is_eq(M.rt(cl, j), small)))

def mem_merge(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.mem_ok(cl2(cl, big, small), big, SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +hj = step_lt(j, n, hk)
      L.and_intro(M.mem_ok(cl2(cl, big, small), big, SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), j), M.beq(M.elem(SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), j), Nat.is_eq(M.rt(cl2(cl, big, small), j), big)),
        mem_merge(cl, n, big, small, h, j, step_le(j, n, hk)),
        %Equal.sym(Bool, M.elem(SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), j), Bool.or(M.elem(M.ms(cl, small), j), M.elem(M.ms(cl, big), j)), elem_append(M.ms(cl, small), M.ms(cl, big), j)) : {M.beq(_, Nat.is_eq(M.rt(cl2(cl, big, small), j), big)) == True{} : Bool}
        %Equal.sym(Bool, M.elem(M.ms(cl, small), j), Nat.is_eq(M.rt(cl, j), small), in_small(cl, n, big, small, h, j, hj)) : {M.beq(Bool.or(_, M.elem(M.ms(cl, big), j)), Nat.is_eq(M.rt(cl2(cl, big, small), j), big)) == True{} : Bool}
        %Equal.sym(Bool, M.elem(M.ms(cl, big), j), Nat.is_eq(M.rt(cl, j), big), in_big(cl, n, big, small, h, j, hj)) : {M.beq(Bool.or(Nat.is_eq(M.rt(cl, j), small), _), Nat.is_eq(M.rt(cl2(cl, big, small), j), big)) == True{} : Bool}
        pw_memb(cl, n, big, small, h, j, hj))

# Exactly one representative (small) disappears.
def lt_succ_ne(+a: Nat, +b: Nat, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == Nat.is_lt(a, 1n+b) : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == Nat.is_lt(0n, 1n) : Bool}, L.true_false(ne))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, N.not_lt_zero(p))
    case 1n+p 1n+q:
      lt_succ_ne(p, q, ne)

def fix_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, n) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(j, small) == b : Bool}) -> {Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j))) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j)), S.eq_bit(Nat.is_lt(small, 1n+j))) : Nat}:
  match b:
    case True{}:
      +e = N.eq_from_is_eq(j, small, eb)
      %Equal.sym(Nat, j, small, e) : {Nat.add(S.eq_bit(Nat.is_lt(small, _)), S.eq_bit(Nat.is_eq(M.rt(cl, _), _))) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), _), _)), S.eq_bit(Nat.is_lt(small, 1n+_))) : Nat}
      %Equal.sym(Bool, Nat.is_lt(small, small), False{}, N.lt_irrefl(small)) : {Nat.add(S.eq_bit(_), S.eq_bit(Nat.is_eq(M.rt(cl, small), small))) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), small), small)), S.eq_bit(Nat.is_lt(small, 1n+small))) : Nat}
      %Equal.sym(Bool, Nat.is_lt(small, 1n+small), True{}, N.lt_succ(small)) : {Nat.add(0n, S.eq_bit(Nat.is_eq(M.rt(cl, small), small))) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), small), small)), S.eq_bit(_)) : Nat}
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, small), small), True{}, h_rs(cl, n, big, small, h)) : {Nat.add(0n, S.eq_bit(_)) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), small), small)), 1n) : Nat}
      %Equal.sym(Nat, M.rt(cl2(cl, big, small), small), sw(cl, big, small, small), rt2(cl, n, big, small, h, small, h_small(cl, n, big, small, h))) : {1n == Nat.add(S.eq_bit(Nat.is_eq(_, small)), 1n) : Nat}
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, small), small), True{}, h_rs(cl, n, big, small, h)) : {1n == Nat.add(S.eq_bit(Nat.is_eq(S.swap_label(_, big, M.rt(cl, small)), small)), 1n) : Nat}
      %Equal.sym(Bool, Nat.is_eq(big, small), False{}, h_ne(cl, n, big, small, h)) : {1n == Nat.add(S.eq_bit(_), 1n) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl2(cl, big, small), j), j), Nat.is_eq(M.rt(cl, j), j), pw_fix(cl, n, big, small, h, j, hj, eb)) : {Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j))) == Nat.add(S.eq_bit(_), S.eq_bit(Nat.is_lt(small, 1n+j))) : Nat}
      %lt_succ_ne(small, j, Equal.trans(Bool, Nat.is_eq(small, j), Nat.is_eq(j, small), False{}, M.is_eq_sym(small, j), eb)) : {Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j))) == Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl, j), j)), S.eq_bit(_)) : Nat}
      N.add_comm(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j)))

# a < 1 + b iff a < b, when a != b.
def cnt_fix_merge(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.cnt_fix(cl, k) == Nat.add(M.cnt_fix(cl2(cl, big, small), k), S.eq_bit(Nat.is_lt(small, k))) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(small, 0n), False{}, N.not_lt_zero(small)) : {0n == Nat.add(0n, S.eq_bit(_)) : Nat}
      {==}
    case 1n+j:
      -C2 = M.cnt_fix(cl2(cl, big, small), j)
      -a = S.eq_bit(Nat.is_lt(small, j))
      -x = S.eq_bit(Nat.is_eq(M.rt(cl, j), j))
      -x2 = S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j))
      -e2 = S.eq_bit(Nat.is_lt(small, 1n+j))
      %Equal.sym(Nat, M.cnt_fix(cl, j), Nat.add(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_lt(small, j))), cnt_fix_merge(cl, n, big, small, h, j, step_le(j, n, hk))) : {Nat.add(_, S.eq_bit(Nat.is_eq(M.rt(cl, j), j))) == Nat.add(Nat.add(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j))), S.eq_bit(Nat.is_lt(small, 1n+j))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_lt(small, j))), S.eq_bit(Nat.is_eq(M.rt(cl, j), j))), Nat.add(M.cnt_fix(cl2(cl, big, small), j), Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j)))), N.add_assoc(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j)))) : {_ == Nat.add(Nat.add(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j))), S.eq_bit(Nat.is_lt(small, 1n+j))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j))), S.eq_bit(Nat.is_lt(small, 1n+j))), Nat.add(M.cnt_fix(cl2(cl, big, small), j), Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j)), S.eq_bit(Nat.is_lt(small, 1n+j)))), N.add_assoc(M.cnt_fix(cl2(cl, big, small), j), S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j)), S.eq_bit(Nat.is_lt(small, 1n+j)))) : {Nat.add(M.cnt_fix(cl2(cl, big, small), j), Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j)))) == _ : Nat}
      Equal.cong(Nat, Nat, q => Nat.add(M.cnt_fix(cl2(cl, big, small), j), q), Nat.add(S.eq_bit(Nat.is_lt(small, j)), S.eq_bit(Nat.is_eq(M.rt(cl, j), j))), Nat.add(S.eq_bit(Nat.is_eq(M.rt(cl2(cl, big, small), j), j)), S.eq_bit(Nat.is_lt(small, 1n+j))),
        fix_case(cl, n, big, small, h, j, step_lt(j, n, hk), Nat.is_eq(j, small), {==}))

def labs_relabel(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.labs(cl2(cl, big, small), k) == S.relabel(M.labs(cl, k), small, big) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(List<&2, Nat>, S.relabel(SC.snoc(Nat, M.labs(cl, j), M.rt(cl, j)), small, big), SC.snoc(Nat, S.relabel(M.labs(cl, j), small, big), S.swap_label(Nat.is_eq(M.rt(cl, j), small), big, M.rt(cl, j))), M.relabel_snoc(M.labs(cl, j), M.rt(cl, j), small, big)) : {SC.snoc(Nat, M.labs(cl2(cl, big, small), j), M.rt(cl2(cl, big, small), j)) == _ : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, M.labs(cl2(cl, big, small), j), S.relabel(M.labs(cl, j), small, big), labs_relabel(cl, n, big, small, h, j, step_le(j, n, hk))) : {SC.snoc(Nat, _, M.rt(cl2(cl, big, small), j)) == SC.snoc(Nat, S.relabel(M.labs(cl, j), small, big), sw(cl, big, small, j)) : List<&2, Nat>}
      %Equal.sym(Nat, M.rt(cl2(cl, big, small), j), sw(cl, big, small, j), rt2(cl, n, big, small, h, j, step_lt(j, n, hk))) : {SC.snoc(Nat, S.relabel(M.labs(cl, j), small, big), _) == SC.snoc(Nat, S.relabel(M.labs(cl, j), small, big), sw(cl, big, small, j)) : List<&2, Nat>}
      {==}

# ---- the invariant after the merge ----

def G(+cx: List<&2, CL.Cell>, +n: Nat, +y: Nat, +q: Nat) -> Bool:
  Bool.and(Nat.is_lt(q, n), Bool.and(Nat.is_eq(M.rt(cx, q), q), M.root_ok(Nat.is_eq(q, y), cx, n, y)))

def RK(+cx: List<&2, CL.Cell>, +n: Nat, +y: Nat, +c: CL.Cell) -> Bool:
  Bool.and(M.below(CL.cmembers(c), n), Bool.and(M.mem_ok(cx, y, CL.cmembers(c), n), Nat.is_eq(CL.csize(c), M.cnt_r(cx, y, n))))

def rk_new(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {RK(cl2(cl, big, small), n, big, newcell(cl, big, small)) == True{} : Bool}:
  +rs = root_of_small(cl, n, big, small, h)
  +rb = root_of_big(cl, n, big, small, h)
  +e = Equal.trans(Nat, Nat.add(M.sz(cl, big), M.sz(cl, small)), Nat.add(M.cnt_r(cl, big, n), M.cnt_r(cl, small, n)), M.cnt_r(cl2(cl, big, small), big, n),
    %Equal.sym(Nat, M.sz(cl, big), M.cnt_r(cl, big, n), M.root_size(cl, n, big, rb)) : {Nat.add(_, M.sz(cl, small)) == Nat.add(M.cnt_r(cl, big, n), M.cnt_r(cl, small, n)) : Nat}
    %Equal.sym(Nat, M.sz(cl, small), M.cnt_r(cl, small, n), M.root_size(cl, n, small, rs)) : {Nat.add(M.cnt_r(cl, big, n), _) == Nat.add(M.cnt_r(cl, big, n), M.cnt_r(cl, small, n)) : Nat}
    {==},
    Equal.sym(Nat, M.cnt_r(cl2(cl, big, small), big, n), Nat.add(M.cnt_r(cl, big, n), M.cnt_r(cl, small, n)), cnt_merge(cl, n, big, small, h, n, N.le_refl(n))))
  L.and_intro(M.below(SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), n), Bool.and(M.mem_ok(cl2(cl, big, small), big, SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), n), Nat.is_eq(Nat.add(M.sz(cl, big), M.sz(cl, small)), M.cnt_r(cl2(cl, big, small), big, n))),
    below_append(M.ms(cl, small), M.ms(cl, big), n, M.root_below(cl, n, small, rs), M.root_below(cl, n, big, rb)),
    L.and_intro(M.mem_ok(cl2(cl, big, small), big, SC.append(Nat, M.ms(cl, small), M.ms(cl, big)), n), Nat.is_eq(Nat.add(M.sz(cl, big), M.sz(cl, small)), M.cnt_r(cl2(cl, big, small), big, n)),
      mem_merge(cl, n, big, small, h, n, N.le_refl(n)),
      M.eq_true(Nat.add(M.sz(cl, big), M.sz(cl, small)), M.cnt_r(cl2(cl, big, small), big, n), e)))

def rk_old(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}, +isr: {Nat.is_eq(M.rt(cl, y), y) == True{} : Bool}, +nb: {Nat.is_eq(y, big) == False{} : Bool}, +ns: {Nat.is_eq(y, small) == False{} : Bool}) -> {RK(cl2(cl, big, small), n, y, M.lc(cl, y)) == True{} : Bool}:
  +ro = M.at_root(cl, n, y, at(cl, n, big, small, h, y, hy), isr)
  L.and_intro(M.below(M.ms(cl, y), n), Bool.and(M.mem_ok(cl2(cl, big, small), y, M.ms(cl, y), n), Nat.is_eq(M.sz(cl, y), M.cnt_r(cl2(cl, big, small), y, n))),
    M.root_below(cl, n, y, ro),
    L.and_intro(M.mem_ok(cl2(cl, big, small), y, M.ms(cl, y), n), Nat.is_eq(M.sz(cl, y), M.cnt_r(cl2(cl, big, small), y, n)),
      mem_other(cl, n, big, small, h, y, nb, ns, M.ms(cl, y), M.root_mem(cl, n, y, ro), n, N.le_refl(n)),
      M.eq_true(M.sz(cl, y), M.cnt_r(cl2(cl, big, small), y, n), Equal.trans(Nat, M.sz(cl, y), M.cnt_r(cl, y, n), M.cnt_r(cl2(cl, big, small), y, n), M.root_size(cl, n, y, ro), Equal.sym(Nat, M.cnt_r(cl2(cl, big, small), y, n), M.cnt_r(cl, y, n), cnt_other(cl, n, big, small, h, y, nb, ns, n, N.le_refl(n)))))))

def rok_true(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}, +ns0: {Nat.is_eq(M.rt(cl, y), small) == False{} : Bool}, +isr: {Nat.is_eq(M.rt(cl, y), y) == True{} : Bool}, b: Bool, +eb: {Nat.is_eq(big, y) == b : Bool}) -> {M.root_ok(True{}, cl2(cl, big, small), n, y) == True{} : Bool}:
  match b:
    case True{}:
      %N.eq_from_is_eq(big, y, eb) : {M.root_ok(True{}, cl2(cl, big, small), n, _) == True{} : Bool}
      L.subst(CL.Cell, c => {RK(cl2(cl, big, small), n, big, c) == True{} : Bool}, newcell(cl, big, small), M.lc(cl2(cl, big, small), big), Equal.sym(CL.Cell, M.lc(cl2(cl, big, small), big), newcell(cl, big, small), lc2_big(cl, big, small, in_cl(cl, n, big, small, h, big, h_big(cl, n, big, small, h)))), rk_new(cl, n, big, small, h))
    case False{}:
      +ey = N.eq_from_is_eq(M.rt(cl, y), y, isr)
      +ns = L.subst(Nat, q => {Nat.is_eq(q, small) == False{} : Bool}, M.rt(cl, y), y, ey, ns0)
      +nb = Equal.trans(Bool, Nat.is_eq(y, big), Nat.is_eq(big, y), False{}, M.is_eq_sym(y, big), eb)
      +ec = Equal.trans(CL.Cell, M.lc(cl2(cl, big, small), y), relinked(M.elem(M.ms(cl, small), y), M.lc(cl, y), big), M.lc(cl, y),
        lc2_other(cl, big, small, y, eb, in_cl(cl, n, big, small, h, y, hy)),
        %Equal.sym(Bool, M.elem(M.ms(cl, small), y), Nat.is_eq(M.rt(cl, y), small), in_small(cl, n, big, small, h, y, hy)) : {relinked(_, M.lc(cl, y), big) == M.lc(cl, y) : CL.Cell}
        %Equal.sym(Bool, Nat.is_eq(M.rt(cl, y), small), False{}, ns0) : {relinked(_, M.lc(cl, y), big) == M.lc(cl, y) : CL.Cell}
        {==})
      L.subst(CL.Cell, c => {RK(cl2(cl, big, small), n, y, c) == True{} : Bool}, M.lc(cl, y), M.lc(cl2(cl, big, small), y), Equal.sym(CL.Cell, M.lc(cl2(cl, big, small), y), M.lc(cl, y), ec), rk_old(cl, n, big, small, h, y, hy, isr, nb, ns))

def rok_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}, +ns0: {Nat.is_eq(M.rt(cl, y), small) == False{} : Bool}, r: Bool, +er: {Nat.is_eq(M.rt(cl, y), y) == r : Bool}) -> {M.root_ok(Nat.is_eq(M.rt(cl, y), y), cl2(cl, big, small), n, y) == True{} : Bool}:
  match r:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, y), y), True{}, er) : {M.root_ok(_, cl2(cl, big, small), n, y) == True{} : Bool}
      rok_true(cl, n, big, small, h, y, hy, ns0, er, Nat.is_eq(big, y), {==})
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, y), y), False{}, er) : {M.root_ok(_, cl2(cl, big, small), n, y) == True{} : Bool}
      {==}

def ga_case(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}, cs: Bool, +ecs: {Nat.is_eq(M.rt(cl, y), small) == cs : Bool}) -> {G(cl2(cl, big, small), n, y, S.swap_label(Nat.is_eq(M.rt(cl, y), small), big, M.rt(cl, y))) == True{} : Bool}:
  match cs:
    case True{}:
      +e = N.eq_from_is_eq(M.rt(cl, y), small, ecs)
      +erb = Equal.trans(Nat, M.rt(cl2(cl, big, small), big), sw(cl, big, small, big), big, rt2(cl, n, big, small, h, big, h_big(cl, n, big, small, h)), sw_root(cl, big, small, big, N.eq_from_is_eq(M.rt(cl, big), big, h_rb(cl, n, big, small, h)), h_ne(cl, n, big, small, h)))
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, y), small), True{}, ecs) : {G(cl2(cl, big, small), n, y, S.swap_label(_, big, M.rt(cl, y))) == True{} : Bool}
      L.and_intro(Nat.is_lt(big, n), Bool.and(Nat.is_eq(M.rt(cl2(cl, big, small), big), big), M.root_ok(Nat.is_eq(big, y), cl2(cl, big, small), n, y)), h_big(cl, n, big, small, h),
        L.and_intro(Nat.is_eq(M.rt(cl2(cl, big, small), big), big), M.root_ok(Nat.is_eq(big, y), cl2(cl, big, small), n, y), M.eq_true(M.rt(cl2(cl, big, small), big), big, erb),
          %Equal.sym(Bool, Nat.is_eq(big, y), False{}, pwf_big(cl, n, big, small, h, y, e, Nat.is_eq(big, y), {==})) : {M.root_ok(_, cl2(cl, big, small), n, y) == True{} : Bool}
          {==}))
    case False{}:
      +g = at(cl, n, big, small, h, y, hy)
      +err = Equal.trans(Nat, M.rt(cl2(cl, big, small), M.rt(cl, y)), sw(cl, big, small, M.rt(cl, y)), M.rt(cl, y), rt2(cl, n, big, small, h, M.rt(cl, y), M.at_lt(cl, n, y, g)), sw_root(cl, big, small, M.rt(cl, y), M.at_idem(cl, n, y, g), ecs))
      %Equal.sym(Bool, Nat.is_eq(M.rt(cl, y), small), False{}, ecs) : {G(cl2(cl, big, small), n, y, S.swap_label(_, big, M.rt(cl, y))) == True{} : Bool}
      L.and_intro(Nat.is_lt(M.rt(cl, y), n), Bool.and(Nat.is_eq(M.rt(cl2(cl, big, small), M.rt(cl, y)), M.rt(cl, y)), M.root_ok(Nat.is_eq(M.rt(cl, y), y), cl2(cl, big, small), n, y)), M.at_lt(cl, n, y, g),
        L.and_intro(Nat.is_eq(M.rt(cl2(cl, big, small), M.rt(cl, y)), M.rt(cl, y)), M.root_ok(Nat.is_eq(M.rt(cl, y), y), cl2(cl, big, small), n, y), M.eq_true(M.rt(cl2(cl, big, small), M.rt(cl, y)), M.rt(cl, y), err),
          rok_case(cl, n, big, small, h, y, hy, ecs, Nat.is_eq(M.rt(cl, y), y), {==})))

def good_at2(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +y: Nat, +hy: {Nat.is_lt(y, n) == True{} : Bool}) -> {M.good_at(cl2(cl, big, small), n, y) == True{} : Bool}:
  L.subst(Nat, q => {G(cl2(cl, big, small), n, y, q) == True{} : Bool}, sw(cl, big, small, y), M.rt(cl2(cl, big, small), y), Equal.sym(Nat, M.rt(cl2(cl, big, small), y), sw(cl, big, small, y), rt2(cl, n, big, small, h, y, hy)), ga_case(cl, n, big, small, h, y, hy, Nat.is_eq(M.rt(cl, y), small), {==}))

def good2(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}, +k: Nat, +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {M.good(cl2(cl, big, small), n, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      L.and_intro(M.good(cl2(cl, big, small), n, j), M.good_at(cl2(cl, big, small), n, j), good2(cl, n, big, small, h, j, step_le(j, n, hk)), good_at2(cl, n, big, small, h, j, step_lt(j, n, hk)))

def fix_count(+cl: List<&2, CL.Cell>, +n: Nat, +big: Nat, +small: Nat, +h: {H(cl, n, big, small) == True{} : Bool}) -> {M.cnt_fix(cl, n) == 1n+M.cnt_fix(cl2(cl, big, small), n) : Nat}:
  %Equal.sym(Nat, 1n+M.cnt_fix(cl2(cl, big, small), n), Nat.add(M.cnt_fix(cl2(cl, big, small), n), 1n), Equal.trans(Nat, 1n+M.cnt_fix(cl2(cl, big, small), n), Nat.add(1n, M.cnt_fix(cl2(cl, big, small), n)), Nat.add(M.cnt_fix(cl2(cl, big, small), n), 1n), {==}, N.add_comm(1n, M.cnt_fix(cl2(cl, big, small), n)))) : {M.cnt_fix(cl, n) == _ : Nat}
  %h_small(cl, n, big, small, h) : {M.cnt_fix(cl, n) == Nat.add(M.cnt_fix(cl2(cl, big, small), n), S.eq_bit(_)) : Nat}
  cnt_fix_merge(cl, n, big, small, h, n, N.le_refl(n))
