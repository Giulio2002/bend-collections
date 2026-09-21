import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/u32.bend as U
import ../../spec/common.bend as SC
import ../../src/lru/fast.bend as F
import ../../src/doubly_linked_list.bend as D
import ../dlist/state.bend as DST
import ../dlist/links.bend as LK
import ../dlist/split.bend as SP
import ../dlist/retarget.bend as RT
import ../dlist/facts.bend as DF
import ../dlist/items.bend as IT
import ../dlist/mut.bend as MU
import ../graph/shift.bend as SH
import ./state.bend as ST
import ./table.bend as TB

# List facts for the LRU shadow: the ghost orders, the free chain, and the
# folds of the invariant over appended orders and under frame updates.

# ---- Nat equality is symmetric ----

def eq_sym_c(+a: Nat, +b: Nat, c: Bool, +ec: {Nat.is_eq(a, b) == c : Bool}) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match c:
    case True{}:
      +e = IT.eq_nat_true(a, b, ec)
      L.subst(Nat, z => {Nat.is_eq(a, z) == Nat.is_eq(z, a) : Bool}, a, b, e, {==})
    case False{}:
      Equal.trans(Bool, Nat.is_eq(a, b), False{}, Nat.is_eq(b, a), ec, Equal.sym(Bool, Nat.is_eq(b, a), False{}, SH.ne_flip(a, b, ec)))

def eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  eq_sym_c(a, b, Nat.is_eq(a, b), {==})

# ---- nodup under moving an element to the front ----

def or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def lmem_front(+i: Nat, +a: List<&2, Nat>, +s: Nat, +c: List<&2, Nat>) -> {DST.lmem(i, SC.append(Nat, a, Con{s, c})) == DST.lmem(i, Con{s, SC.append(Nat, a, c)}) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, i), DST.lmem(i, SC.append(Nat, t, Con{s, c}))), Bool.or(Nat.is_eq(x, i), Bool.or(Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c)))), Bool.or(Nat.is_eq(s, i), Bool.or(Nat.is_eq(x, i), DST.lmem(i, SC.append(Nat, t, c)))),
        Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, i), z), DST.lmem(i, SC.append(Nat, t, Con{s, c})), Bool.or(Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c))), lmem_front(i, t, s, c)),
        or_swap(Nat.is_eq(x, i), Nat.is_eq(s, i), DST.lmem(i, SC.append(Nat, t, c))))

def and_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def not_or(a: Bool, +b: Bool) -> {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and4_swap(a: Bool, b: Bool, c: Bool, +d: Bool) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(Bool.and(a, c), Bool.and(b, d)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def nodup_front(+a: List<&2, Nat>, +s: Nat, +c: List<&2, Nat>) -> {DST.nodup(SC.append(Nat, a, Con{s, c})) == DST.nodup(Con{s, SC.append(Nat, a, c)}) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = SC.append(Nat, t, c)
      Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, SC.append(Nat, t, Con{s, c}))), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
        Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, SC.append(Nat, t, Con{s, c}))), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(SC.append(Nat, t, Con{s, c}))), Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})),
          Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), DST.nodup(SC.append(Nat, t, Con{s, c}))), DST.lmem(x, SC.append(Nat, t, Con{s, c})), DST.lmem(x, Con{s, r}), lmem_front(x, t, s, c)),
          Equal.cong(Bool, Bool, z => Bool.and(Bool.not(DST.lmem(x, Con{s, r})), z), DST.nodup(SC.append(Nat, t, Con{s, c})), DST.nodup(Con{s, r}), nodup_front(t, s, c))),
        Equal.trans(Bool, Bool.and(Bool.not(DST.lmem(x, Con{s, r})), DST.nodup(Con{s, r})), Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
          Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.not(DST.lmem(x, Con{s, r})), Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), not_or(Nat.is_eq(s, x), DST.lmem(x, r))),
          Equal.trans(Bool, Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r))), Bool.and(Bool.not(DST.lmem(s, r)), DST.nodup(r))), Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
            and4_swap(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(x, r)), Bool.not(DST.lmem(s, r)), DST.nodup(r)),
            Equal.trans(Bool, Bool.and(Bool.and(Bool.not(Nat.is_eq(s, x)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))),
              Equal.cong(Bool, Bool, z => Bool.and(Bool.and(Bool.not(z), Bool.not(DST.lmem(s, r))), Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Nat.is_eq(s, x), Nat.is_eq(x, s), eq_sym(s, x)),
              Equal.cong(Bool, Bool, z => Bool.and(z, Bool.and(Bool.not(DST.lmem(x, r)), DST.nodup(r))), Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), Bool.not(DST.lmem(s, Con{x, r})), Equal.sym(Bool, Bool.not(DST.lmem(s, Con{x, r})), Bool.and(Bool.not(Nat.is_eq(x, s)), Bool.not(DST.lmem(s, r))), not_or(Nat.is_eq(x, s), DST.lmem(s, r))))))))
