import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC
import ../../../src/containers/balanced_search_tree.bend as M
import ./state.bend as ST
import ./path.bend as P
import ./nbr.bend as NB
import ./dj.bend as DJ
import ./spath.bend as SP
import ../../lib/nat_list.bend as NL

# The header after inserting x where the search stopped: x is the first id
# exactly when it went in before everything (the tree was empty, or it is
# the left child of the first), and the last symmetrically.
# (source: tools/generators/tm_hand/hdr.src)


def len_pos(+b: Nat, +t: List<&2, Nat>, +xs: List<&2, Nat>) -> {Nat.is_eq(SC.length(Nat, SC.append(Nat, Con{b, t}, xs)), 0n) == False{} : Bool}:
  {==}

def len_ne0(+xs: List<&2, Nat>, +q: Nat, +h: {NL.memn(q, xs) == True{} : Bool}) -> {Nat.is_eq(SC.length(Nat, xs), 0n) == False{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, L.false_true(h))
    case Con{b, t}:
      {==}

def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

def and_f2(+a: Bool, +b: Bool, +hb: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      {==}

def pick_f(+b: Bool, +x: Nat, +y: Nat, +h: {b == False{} : Bool}) -> {M.pick(Nat, b, x, y) == y : Nat}:
  %Equal.sym(Bool, b, False{}, h) : {M.pick(Nat, _, x, y) == y : Nat}
  {==}

def pick_t(+b: Bool, +x: Nat, +y: Nat, +h: {b == True{} : Bool}) -> {M.pick(Nat, b, x, y) == x : Nat}:
  %Equal.sym(Bool, b, True{}, h) : {M.pick(Nat, _, x, y) == x : Nat}
  {==}

# ---- the first id ----

# inserting before a parent on the left
def lo_t(+x: Nat, +q: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +lo: Nat, +hlo: {lo == ST.fst0(SC.append(Nat, b, Con{q, r})) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, b, Con{q, r})) : Nat}, +hnd: {NL.nodupn(SC.append(Nat, b, Con{x, Con{q, r}})) == True{} : Bool}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(True{}, Nat.is_eq(q, lo))), x, lo) == ST.fst0(SC.append(Nat, b, Con{x, Con{q, r}})) : Nat}:
  match b:
    case Nil{}:
      %Equal.sym(Nat, lo, q, hlo) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, _)), x, _) == x : Nat}
      pick_t(Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, q)), x, q, L.subst(Bool, z => {Bool.or(Nat.is_eq(n, 0n), z) == True{} : Bool}, True{}, Nat.is_eq(q, q), Equal.sym(Bool, Nat.is_eq(q, q), True{}, N.is_eq_refl(q)), NL.or_true_b(Nat.is_eq(n, 0n))))
    case Con{+b0, +bs}:
      %Equal.sym(Nat, lo, b0, hlo) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, _)), x, _) == b0 : Nat}
      %Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, Con{b0, bs}, Con{q, r})), hn) : {M.pick(Nat, Bool.or(Nat.is_eq(_, 0n), Nat.is_eq(q, b0)), x, b0) == b0 : Nat}
      +hq = DJ.nd_head(b0, SC.append(Nat, bs, Con{x, Con{q, r}}), hnd)
      +nq = DJ.ne_nm(b0, q, SC.append(Nat, bs, Con{x, Con{q, r}}), hq, DJ.mem_r(q, bs, Con{x, Con{q, r}}, DJ.mem_tl(q, x, Con{q, r}, DJ.mem_hd(q, r))))
      pick_f(Bool.or(Nat.is_eq(SC.length(Nat, SC.append(Nat, Con{b0, bs}, Con{q, r})), 0n), Nat.is_eq(q, b0)), x, b0, or_ff(Nat.is_eq(SC.length(Nat, SC.append(Nat, Con{b0, bs}, Con{q, r})), 0n), Nat.is_eq(q, b0), {==}, N.is_eq_sym_false(b0, q, nq)))

# inserting after a parent on the right (something is before)
def lo_f(+x: Nat, +q: Nat, +a: List<&2, Nat>, +bu: List<&2, Nat>, +iss: List<&2, Nat>, +n: Nat, +lo: Nat, +hlo: {lo == ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)) : Nat}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(False{}, Nat.is_eq(q, lo))), x, lo) == ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})) : Nat}:
  +e1 = LL.append_assoc(Nat, bu, iss, Con{q, Nil{}})
  +f1 = Equal.trans(Nat, ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})), ST.fst0(SC.append(Nat, SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), Con{x, a})), ST.fst0(SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}})), L.subst(List<&2, Nat>, z => {ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})) == ST.fst0(SC.append(Nat, z, Con{x, a})) : Nat}, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), e1), {==}), NB.fst0_app(SC.append(Nat, bu, iss), q, Nil{}, Con{x, a}))
  +f2 = Equal.trans(Nat, ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)), ST.fst0(SC.append(Nat, SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), a)), ST.fst0(SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}})), L.subst(List<&2, Nat>, z => {ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)) == ST.fst0(SC.append(Nat, z, a)) : Nat}, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}}), SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), e1), {==}), NB.fst0_app(SC.append(Nat, bu, iss), q, Nil{}, a))
  %Equal.sym(Nat, ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})), lo, Equal.trans(Nat, ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})), ST.fst0(SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}})), lo, f1, Equal.sym(Nat, lo, ST.fst0(SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}})), Equal.trans(Nat, lo, ST.fst0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)), ST.fst0(SC.append(Nat, SC.append(Nat, bu, iss), Con{q, Nil{}})), hlo, f2)))) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), False{}), x, lo) == _ : Nat}
  pick_f(Bool.or(Nat.is_eq(n, 0n), False{}), x, lo, or_ff(Nat.is_eq(n, 0n), False{}, L.subst(Nat, z => {Nat.is_eq(z, 0n) == False{} : Bool}, SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)), n, Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)), hn), len_ne0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a), q, DJ.mem_l(q, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a, DJ.mem_r(q, bu, SC.append(Nat, iss, Con{q, Nil{}}), DJ.mem_r(q, iss, Con{q, Nil{}}, DJ.mem_hd(q, Nil{})))))), {==}))

def lo_new(+c: List<&2, P.Fr>, +x: Nat, +n: Nat, +lo: Nat, +hlo: {lo == ST.fst0(SC.append(Nat, P.before(c), P.after(c))) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, P.before(c), P.after(c))) : Nat}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), Con{x, P.after(c)})) == True{} : Bool}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(SP.dir(c), Nat.is_eq(P.top(c), lo))), x, lo) == ST.fst0(SC.append(Nat, P.before(c), Con{x, P.after(c)})) : Nat}:
  match c:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, hn) : {M.pick(Nat, Bool.or(Nat.is_eq(_, 0n), Bool.and(False{}, Nat.is_eq(0n, lo))), x, lo) == x : Nat}
      {==}
    case Con{P.FR{+q, True{}, +s}, +u}:
      lo_t(x, q, SC.append(Nat, ST.ids(s), P.after(u)), P.before(u), n, lo, hlo, hn, hnd)
    case Con{P.FR{+q, False{}, +s}, +u}:
      lo_f(x, q, P.after(u), P.before(u), ST.ids(s), n, lo, hlo, hn)

# ---- the last id ----

def last0_mem(+t: List<&2, Nat>, +a: Nat) -> {NL.memn(ST.last0(Con{a, t}), Con{a, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      DJ.mem_hd(a, Nil{})
    case Con{+b, +u}:
      DJ.mem_tl(ST.last0(Con{b, u}), a, Con{b, u}, last0_mem(u, b))

def hi_t(+x: Nat, +q: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, +n: Nat, +hi: Nat, +hhi: {hi == ST.last0(SC.append(Nat, b, Con{q, r})) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, b, Con{q, r})) : Nat}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(False{}, Nat.is_eq(q, hi))), x, hi) == ST.last0(SC.append(Nat, b, Con{x, Con{q, r}})) : Nat}:
  +e1 = Equal.trans(Nat, ST.last0(SC.append(Nat, b, Con{x, Con{q, r}})), ST.last0(Con{x, Con{q, r}}), ST.last0(Con{q, r}), NB.last0_tail(b, x, Con{q, r}), {==})
  +e2 = Equal.trans(Nat, hi, ST.last0(SC.append(Nat, b, Con{q, r})), ST.last0(Con{q, r}), hhi, NB.last0_tail(b, q, r))
  %Equal.sym(Nat, ST.last0(SC.append(Nat, b, Con{x, Con{q, r}})), hi, Equal.trans(Nat, ST.last0(SC.append(Nat, b, Con{x, Con{q, r}})), ST.last0(Con{q, r}), hi, e1, Equal.sym(Nat, hi, ST.last0(Con{q, r}), e2))) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), False{}), x, hi) == _ : Nat}
  pick_f(Bool.or(Nat.is_eq(n, 0n), False{}), x, hi, or_ff(Nat.is_eq(n, 0n), False{}, L.subst(Nat, z => {Nat.is_eq(z, 0n) == False{} : Bool}, SC.length(Nat, SC.append(Nat, b, Con{q, r})), n, Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, b, Con{q, r})), hn), len_ne0(SC.append(Nat, b, Con{q, r}), q, DJ.mem_r(q, b, Con{q, r}, DJ.mem_hd(q, r)))), {==}))


def hi_f(+x: Nat, +q: Nat, +a: List<&2, Nat>, +bu: List<&2, Nat>, +iss: List<&2, Nat>, +n: Nat, +hi: Nat, +hhi: {hi == ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a)) : Nat}, +hnd: {NL.nodupn(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})) == True{} : Bool}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(True{}, Nat.is_eq(q, hi))), x, hi) == ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, a})) : Nat}:
  match a:
    case Nil{}:
      +e1 = Equal.trans(Nat, hi, ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Nil{})), q, hhi, L.subst(List<&2, Nat>, z => {ST.last0(z) == q : Nat}, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Nil{}), SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), LL.append_nil(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})))), NB.last0_end(bu, iss, q)))
      %Equal.sym(Nat, hi, q, e1) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, _)), x, _) == ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Nil{}})) : Nat}
      %Equal.sym(Nat, ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Nil{}})), x, NB.last0_snoc(SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), x)) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, q)), x, q) == _ : Nat}
      pick_t(Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, q)), x, q, L.subst(Bool, z => {Bool.or(Nat.is_eq(n, 0n), z) == True{} : Bool}, True{}, Nat.is_eq(q, q), Equal.sym(Bool, Nat.is_eq(q, q), True{}, N.is_eq_refl(q)), NL.or_true_b(Nat.is_eq(n, 0n))))
    case Con{+a0, +as}:
      +e2 = Equal.trans(Nat, hi, ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{a0, as})), ST.last0(Con{a0, as}), hhi, NB.last0_tail(SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), a0, as))
      +e3 = Equal.trans(Nat, ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Con{a0, as}})), ST.last0(Con{x, Con{a0, as}}), ST.last0(Con{a0, as}), NB.last0_tail(SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), x, Con{a0, as}), {==})
      +mq = DJ.mem_r(q, bu, SC.append(Nat, iss, Con{q, Nil{}}), DJ.mem_r(q, iss, Con{q, Nil{}}, DJ.mem_hd(q, Nil{})))
      +nq = DJ.dj_r(SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Con{a0, as}}, hnd, q, mq)
      +nq2 = DJ.nm_ct(q, x, Con{a0, as}, nq)
      +ne = DJ.ne_nm(q, ST.last0(Con{a0, as}), Con{a0, as}, nq2, last0_mem(as, a0))
      %Equal.sym(Nat, hi, ST.last0(Con{a0, as}), e2) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, _)), x, _) == ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Con{a0, as}})) : Nat}
      %Equal.sym(Nat, ST.last0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{x, Con{a0, as}})), ST.last0(Con{a0, as}), e3) : {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, ST.last0(Con{a0, as}))), x, ST.last0(Con{a0, as})) == _ : Nat}
      pick_f(Bool.or(Nat.is_eq(n, 0n), Nat.is_eq(q, ST.last0(Con{a0, as}))), x, ST.last0(Con{a0, as}), or_ff(Nat.is_eq(n, 0n), Nat.is_eq(q, ST.last0(Con{a0, as})), L.subst(Nat, z => {Nat.is_eq(z, 0n) == False{} : Bool}, SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{a0, as})), n, Equal.sym(Nat, n, SC.length(Nat, SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{a0, as})), hn), len_ne0(SC.append(Nat, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{a0, as}), q, DJ.mem_l(q, SC.append(Nat, bu, SC.append(Nat, iss, Con{q, Nil{}})), Con{a0, as}, mq))), ne))

def hi_new(+c: List<&2, P.Fr>, +x: Nat, +n: Nat, +hi: Nat, +hhi: {hi == ST.last0(SC.append(Nat, P.before(c), P.after(c))) : Nat}, +hn: {n == SC.length(Nat, SC.append(Nat, P.before(c), P.after(c))) : Nat}, +hnd: {NL.nodupn(SC.append(Nat, P.before(c), Con{x, P.after(c)})) == True{} : Bool}) -> {M.pick(Nat, Bool.or(Nat.is_eq(n, 0n), Bool.and(Bool.not(SP.dir(c)), Nat.is_eq(P.top(c), hi))), x, hi) == ST.last0(SC.append(Nat, P.before(c), Con{x, P.after(c)})) : Nat}:
  match c:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, hn) : {M.pick(Nat, Bool.or(Nat.is_eq(_, 0n), Bool.and(True{}, Nat.is_eq(0n, hi))), x, hi) == x : Nat}
      {==}
    case Con{P.FR{+q, True{}, +s}, +u}:
      hi_t(x, q, SC.append(Nat, ST.ids(s), P.after(u)), P.before(u), n, hi, hhi, hn)
    case Con{P.FR{+q, False{}, +s}, +u}:
      hi_f(x, q, P.after(u), P.before(u), ST.ids(s), n, hi, hhi, hn, hnd)
