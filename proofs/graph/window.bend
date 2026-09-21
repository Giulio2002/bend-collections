import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../lib/order.bend as O
import ../balanced_search_tree/sorted.bend as SO
import ../../spec/common.bend as SC
import ../../spec/balanced_search_tree.bend as S
import ../../types/balanced_search_tree.bend as BE
import ./state.bend as ST
import ./lb.bend as LB
import ./search.bend as SE

# The window of a block, its lower bound, and what a SORTED window gives:
# the two split predicates the binary search needs, and the equivalence
# between "the entry at the lower bound is v" and "the specification finds v".

# ---- reading through the window ----

def drop_zero(-A: Data, +xs: List<&2, A>) -> {SC.drop(A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def nil_drop(-A: Data, +n: Nat) -> {SC.drop(A, Nil{}, n) == Nil{} : List<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nil_nth(-A: Data, +i: Nat) -> {SC.nth(A, Nil{}, i) == None{} : Maybe<&2, A>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nth_drop(-A: Data, +xs: List<&2, A>, +from: Nat, +i: Nat) -> {SC.nth(A, SC.drop(A, xs, from), i) == SC.nth(A, xs, Nat.add(from, i)) : Maybe<&2, A>}:
  match xs from:
    case Nil{} f0:
      %nil_drop(A, f0) : {SC.nth(A, _, i) == SC.nth(A, Nil{}, Nat.add(f0, i)) : Maybe<&2, A>}
      %nil_nth(A, Nat.add(f0, i)) : {SC.nth(A, Nil{}, i) == _ : Maybe<&2, A>}
      nil_nth(A, i)
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      nth_drop(A, t, p, i)

def nth_win(-A: Data, +xs: List<&2, A>, +from: Nat, +k: Nat, +i: Nat, +h: {Nat.is_lt(i, k) == True{} : Bool}) -> {SC.nth(A, ST.win(A, xs, from, k), i) == SC.nth(A, xs, Nat.add(from, i)) : Maybe<&2, A>}:
  Equal.trans(Maybe<&2, A>, SC.nth(A, SC.take(A, SC.drop(A, xs, from), k), i), SC.nth(A, SC.drop(A, xs, from), i), SC.nth(A, xs, Nat.add(from, i)),
    LL.sc_nth_take(A, SC.drop(A, xs, from), k, i, h),
    nth_drop(A, xs, from, i))

# ---- the lower bound of a key list ----

def lbu(+v: U32, ws: List<&2, U32>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{+w, +t}:
      LB.lbx_step(Cmp.is_lt(U32.cmp(w, v)), lbu(v, t))

def lbu_le_go(+v: U32, +w: U32, +t: List<&2, U32>, less: Bool, +eb: {Cmp.is_lt(U32.cmp(w, v)) == less : Bool}, +ih: {Nat.is_le(lbu(v, t), SC.length(U32, t)) == True{} : Bool}) -> {Nat.is_le(lbu(v, Con{w, t}), 1n+SC.length(U32, t)) == True{} : Bool}:
  match less:
    case True{}:
      L.subst(Bool, b => {Nat.is_le(LB.lbx_step(b, lbu(v, t)), 1n+SC.length(U32, t)) == True{} : Bool}, True{}, Cmp.is_lt(U32.cmp(w, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(w, v)), True{}, eb), ih)
    case False{}:
      L.subst(Bool, b => {Nat.is_le(LB.lbx_step(b, lbu(v, t)), 1n+SC.length(U32, t)) == True{} : Bool}, False{}, Cmp.is_lt(U32.cmp(w, v)), Equal.sym(Bool, Cmp.is_lt(U32.cmp(w, v)), False{}, eb), N.zero_le(1n+SC.length(U32, t)))

def lbu_le(+v: U32, +ws: List<&2, U32>) -> {Nat.is_le(lbu(v, ws), SC.length(U32, ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      lbu_le_go(v, w, t, Cmp.is_lt(U32.cmp(w, v)), {==}, lbu_le(v, t))

# ---- the lower bound, counted over the slots ----

# The number of leading entries of the window [from, from + k) below v.
def lbs(+v: U32, +xs: List<&2, U32>, +k: Nat, +from: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+m:
      LB.lbx_step(SE.ltat(xs, from, v), lbs(v, xs, m, 1n+from))

# Everything before the lower bound is below v: true by construction.
def lbs_alllt_go(+v: U32, +xs: List<&2, U32>, +m: Nat, +from: Nat, less: Bool, +eb: {SE.ltat(xs, from, v) == less : Bool}, +ih: {SE.alllt(lbs(v, xs, m, 1n+from), xs, 1n+from, v) == True{} : Bool}) -> {SE.alllt(lbs(v, xs, 1n+m, from), xs, from, v) == True{} : Bool}:
  match less:
    case False{}:
      L.subst(Bool, b => {SE.alllt(LB.lbx_step(b, lbs(v, xs, m, 1n+from)), xs, from, v) == True{} : Bool}, False{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), False{}, eb), {==})
    case True{}:
      L.subst(Bool, b => {SE.alllt(LB.lbx_step(b, lbs(v, xs, m, 1n+from)), xs, from, v) == True{} : Bool}, True{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), True{}, eb),
        L.and_intro(SE.ltat(xs, from, v), SE.alllt(lbs(v, xs, m, 1n+from), xs, 1n+from, v), eb, ih))

# The lower bound never leaves the window.
def lbs_alllt(+v: U32, +xs: List<&2, U32>, +k: Nat, +from: Nat) -> {SE.alllt(lbs(v, xs, k, from), xs, from, v) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      lbs_alllt_go(v, xs, m, from, SE.ltat(xs, from, v), {==}, lbs_alllt(v, xs, m, 1n+from))

def lbs_le_go(+v: U32, +xs: List<&2, U32>, +m: Nat, +from: Nat, less: Bool, +eb: {SE.ltat(xs, from, v) == less : Bool}, +ih: {Nat.is_le(lbs(v, xs, m, 1n+from), m) == True{} : Bool}) -> {Nat.is_le(lbs(v, xs, 1n+m, from), 1n+m) == True{} : Bool}:
  match less:
    case False{}:
      L.subst(Bool, b => {Nat.is_le(LB.lbx_step(b, lbs(v, xs, m, 1n+from)), 1n+m) == True{} : Bool}, False{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), False{}, eb), N.zero_le(1n+m))
    case True{}:
      L.subst(Bool, b => {Nat.is_le(LB.lbx_step(b, lbs(v, xs, m, 1n+from)), 1n+m) == True{} : Bool}, True{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), True{}, eb), ih)

def lbs_le(+v: U32, +xs: List<&2, U32>, +k: Nat, +from: Nat) -> {Nat.is_le(lbs(v, xs, k, from), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      lbs_le_go(v, xs, m, from, SE.ltat(xs, from, v), {==}, lbs_le(v, xs, m, 1n+from))

# ---- sortedness over the slots ----





# x < y and NOT (x < v) give NOT (y < v).
def lt_le(+c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  L.subst(Cmp, z => {Cmp.is_le(z) == True{} : Bool}, LT{}, c, Equal.sym(Cmp, c, LT{}, O.lt_is(c, h)), {==})

# The same step, read through the slots.
def ge_step_go(+x: U32, +y: U32, +v: U32, +hxy: {Cmp.is_lt(U32.cmp(x, y)) == True{} : Bool}, +hxv: {Cmp.is_lt(U32.cmp(x, v)) == False{} : Bool}, less: Bool, +eb: {Cmp.is_lt(U32.cmp(y, v)) == less : Bool}) -> {Cmp.is_lt(U32.cmp(y, v)) == False{} : Bool}:
  match less:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Cmp.is_lt(U32.cmp(y, v)) == False{} : Bool},
        L.true_not_false(Cmp.is_lt(U32.cmp(x, v)),
          Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(x, v), LT{},
            O.u32_lt_le(x, y, v, O.lt_is(U32.cmp(x, y), hxy), lt_le(U32.cmp(y, v), eb))),
          hxv))

def ge_step(+x: U32, +y: U32, +v: U32, +hxy: {Cmp.is_lt(U32.cmp(x, y)) == True{} : Bool}, +hxv: {Cmp.is_lt(U32.cmp(x, v)) == False{} : Bool}) -> {Cmp.is_lt(U32.cmp(y, v)) == False{} : Bool}:
  ge_step_go(x, y, v, hxy, hxv, Cmp.is_lt(U32.cmp(y, v)), {==})

def ge_slot_go(+xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, +hij: {SE.ltat2(xs, i, j) == True{} : Bool}, +hiv: {SE.ltat(xs, i, v) == False{} : Bool}, mi: Maybe<&2, U32>, +ei: {SC.nth(U32, xs, i) == mi : Maybe<&2, U32>}, mj: Maybe<&2, U32>, +ej: {SC.nth(U32, xs, j) == mj : Maybe<&2, U32>}) -> {SE.ltat(xs, j, v) == False{} : Bool}:
  match mi mj:
    case Some{+x} Some{+y}:
      L.subst(Maybe<&2, U32>, m => {SE.ltm(m, v) == False{} : Bool}, Some{y}, SC.nth(U32, xs, j), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, j), Some{y}, ej),
        ge_step(x, y, v,
          L.subst(Maybe<&2, U32>, m => {SE.ltm2(Some{x}, m) == True{} : Bool}, SC.nth(U32, xs, j), Some{y}, ej,
            L.subst(Maybe<&2, U32>, m => {SE.ltm2(m, SC.nth(U32, xs, j)) == True{} : Bool}, SC.nth(U32, xs, i), Some{x}, ei, hij)),
          L.subst(Maybe<&2, U32>, m => {SE.ltm(m, v) == False{} : Bool}, SC.nth(U32, xs, i), Some{x}, ei, hiv)))
    case None{} mj0:
      Empty.absurd({SE.ltat(xs, j, v) == False{} : Bool},
        L.true_not_false(SE.ltat2(xs, i, j), hij,
          L.subst(Maybe<&2, U32>, m => {SE.ltm2(m, SC.nth(U32, xs, j)) == False{} : Bool}, None{}, SC.nth(U32, xs, i), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, i), None{}, ei), {==})))
    case Some{+x} None{}:
      Empty.absurd({SE.ltat(xs, j, v) == False{} : Bool},
        L.true_not_false(SE.ltat2(xs, i, j), hij,
          L.subst(Maybe<&2, U32>, m => {SE.ltm2(SC.nth(U32, xs, i), m) == False{} : Bool}, None{}, SC.nth(U32, xs, j), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, j), None{}, ej),
            L.subst(Maybe<&2, U32>, m => {SE.ltm2(m, None{}) == False{} : Bool}, Some{x}, SC.nth(U32, xs, i), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, i), Some{x}, ei), {==}))))

def ge_slot(+xs: List<&2, U32>, +i: Nat, +j: Nat, +v: U32, +hij: {SE.ltat2(xs, i, j) == True{} : Bool}, +hiv: {SE.ltat(xs, i, v) == False{} : Bool}) -> {SE.ltat(xs, j, v) == False{} : Bool}:
  ge_slot_go(xs, i, j, v, hij, hiv, SC.nth(U32, xs, i), {==}, SC.nth(U32, xs, j), {==})

# Everything above an entry that is not below v is not below v either.
def above_allge(+m: Nat, +xs: List<&2, U32>, +i: Nat, +from: Nat, +v: U32, +ha: {SE.above_at(m, xs, i, from) == True{} : Bool}, +hiv: {SE.ltat(xs, i, v) == False{} : Bool}) -> {SE.allge(m, xs, from, v) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+r:
      L.and_intro(Bool.not(SE.ltat(xs, from, v)), SE.allge(r, xs, 1n+from, v),
        L.not_false(SE.ltat(xs, from, v), ge_slot(xs, i, from, v, L.and_left(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from), ha), hiv)),
        above_allge(r, xs, i, 1n+from, v, L.and_right(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from), ha), hiv))

# From the lower bound on, no entry of a SORTED window is below v.
def lbs_allge_go(+v: U32, +xs: List<&2, U32>, +m: Nat, +from: Nat, +hs: {SE.asc_at(1n+m, xs, from) == True{} : Bool}, less: Bool, +eb: {SE.ltat(xs, from, v) == less : Bool}, +ih: {SE.allge(Nat.sub(m, lbs(v, xs, m, 1n+from)), xs, Nat.add(1n+from, lbs(v, xs, m, 1n+from)), v) == True{} : Bool}) -> {SE.allge(Nat.sub(1n+m, lbs(v, xs, 1n+m, from)), xs, Nat.add(from, lbs(v, xs, 1n+m, from)), v) == True{} : Bool}:
  match less:
    case True{}:
      L.subst(Bool, b => {SE.allge(Nat.sub(1n+m, LB.lbx_step(b, lbs(v, xs, m, 1n+from))), xs, Nat.add(from, LB.lbx_step(b, lbs(v, xs, m, 1n+from))), v) == True{} : Bool}, True{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), True{}, eb),
        L.subst(Nat, z => {SE.allge(Nat.sub(m, lbs(v, xs, m, 1n+from)), xs, z, v) == True{} : Bool}, Nat.add(1n+from, lbs(v, xs, m, 1n+from)), Nat.add(from, 1n+lbs(v, xs, m, 1n+from)),
          Equal.sym(Nat, Nat.add(from, 1n+lbs(v, xs, m, 1n+from)), Nat.add(1n+from, lbs(v, xs, m, 1n+from)), N.add_succ(from, lbs(v, xs, m, 1n+from))),
          ih))
    case False{}:
      L.subst(Bool, b => {SE.allge(Nat.sub(1n+m, LB.lbx_step(b, lbs(v, xs, m, 1n+from))), xs, Nat.add(from, LB.lbx_step(b, lbs(v, xs, m, 1n+from))), v) == True{} : Bool}, False{}, SE.ltat(xs, from, v), Equal.sym(Bool, SE.ltat(xs, from, v), False{}, eb),
        L.subst(Nat, z => {SE.allge(1n+m, xs, z, v) == True{} : Bool}, from, Nat.add(from, 0n), Equal.sym(Nat, Nat.add(from, 0n), from, N.add_zero(from)),
          L.and_intro(Bool.not(SE.ltat(xs, from, v)), SE.allge(m, xs, 1n+from, v),
            L.not_false(SE.ltat(xs, from, v), eb),
            above_allge(m, xs, from, 1n+from, v, L.and_left(SE.above_at(m, xs, from, 1n+from), SE.asc_at(m, xs, 1n+from), hs), eb))))

def lbs_allge(+v: U32, +xs: List<&2, U32>, +k: Nat, +from: Nat, +hs: {SE.asc_at(k, xs, from) == True{} : Bool}) -> {SE.allge(Nat.sub(k, lbs(v, xs, k, from)), xs, Nat.add(from, lbs(v, xs, k, from)), v) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      lbs_allge_go(v, xs, m, from, hs, SE.ltat(xs, from, v), {==},
        lbs_allge(v, xs, m, 1n+from, L.and_right(SE.above_at(m, xs, from, 1n+from), SE.asc_at(m, xs, 1n+from), hs)))

# ---- the slot count and the window list agree ----

def is_con(-A: Data, ys: List<&2, A>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

def nil_con(-A: Data, +h: A, +t: List<&2, A>, +e: {Nil{} == Con{h, t} : List<&2, A>}) -> Empty:
  %Equal.sym(List<&2, A>, Nil{}, Con{h, t}, e) : L.truth(is_con(A, _))
  Unit{}

def drop_head(-A: Data, +xs: List<&2, A>, +from: Nat, +h: A, +t: List<&2, A>, +e: {SC.drop(A, xs, from) == Con{h, t} : List<&2, A>}) -> {SC.nth(A, xs, from) == Some{h} : Maybe<&2, A>}:
  match xs from:
    case Nil{} f0:
      Empty.absurd({SC.nth(A, Nil{}, f0) == Some{h} : Maybe<&2, A>},
        nil_con(A, h, t, Equal.trans(List<&2, A>, Nil{}, SC.drop(A, Nil{}, f0), Con{h, t}, Equal.sym(List<&2, A>, SC.drop(A, Nil{}, f0), Nil{}, nil_drop(A, f0)), e)))
    case Con{+x, xt} 0n:
      Equal.cong(List<&2, A>, Maybe<&2, A>, ys => SC.head(A, ys), Con{x, xt}, Con{h, t}, e)
    case Con{x, xt} 1n+p:
      drop_head(A, xt, p, h, t, e)

def drop_tail(-A: Data, +xs: List<&2, A>, +from: Nat, +h: A, +t: List<&2, A>, +e: {SC.drop(A, xs, from) == Con{h, t} : List<&2, A>}) -> {SC.drop(A, xs, 1n+from) == t : List<&2, A>}:
  match xs from:
    case Nil{} f0:
      Empty.absurd({SC.drop(A, Nil{}, 1n+f0) == t : List<&2, A>},
        nil_con(A, h, t, Equal.trans(List<&2, A>, Nil{}, SC.drop(A, Nil{}, f0), Con{h, t}, Equal.sym(List<&2, A>, SC.drop(A, Nil{}, f0), Nil{}, nil_drop(A, f0)), e)))
    case Con{x, +xt} 0n:
      Equal.trans(List<&2, A>, SC.drop(A, xt, 0n), xt, t, drop_zero(A, xt),
        Equal.cong(List<&2, A>, List<&2, A>, ys => SC.tail(A, ys), Con{x, xt}, Con{h, t}, e))
    case Con{x, xt} 1n+p:
      drop_tail(A, xt, p, h, t, e)

# The slot-counted lower bound is the list lower bound of the window.
def head_drop(-A: Data, +xs: List<&2, A>, +from: Nat) -> {SC.nth(A, xs, from) == SC.head(A, SC.drop(A, xs, from)) : Maybe<&2, A>}:
  match xs from:
    case Nil{} f0:
      Equal.trans(Maybe<&2, A>, SC.nth(A, Nil{}, f0), None{}, SC.head(A, SC.drop(A, Nil{}, f0)),
        nil_nth(A, f0),
        Equal.sym(Maybe<&2, A>, SC.head(A, SC.drop(A, Nil{}, f0)), None{},
          Equal.cong(List<&2, A>, Maybe<&2, A>, ys => SC.head(A, ys), SC.drop(A, Nil{}, f0), Nil{}, nil_drop(A, f0))))
    case Con{x, xt} 0n:
      {==}
    case Con{x, xt} 1n+p:
      head_drop(A, xt, p)

def lbs_lbu_go(+v: U32, +xs: List<&2, U32>, +m: Nat, +from: Nat, ds: List<&2, U32>, +ed: {SC.drop(U32, xs, from) == ds : List<&2, U32>}, +ih: {lbs(v, xs, m, 1n+from) == lbu(v, ST.win(U32, xs, 1n+from, m)) : Nat}) -> {lbs(v, xs, 1n+m, from) == lbu(v, ST.win(U32, xs, from, 1n+m)) : Nat}:
  match ds:
    case Nil{}:
      # the window is empty: the slot read is None, so neither side counts
      L.subst(List<&2, U32>, ys => {lbs(v, xs, 1n+m, from) == lbu(v, SC.take(U32, ys, 1n+m)) : Nat}, Nil{}, SC.drop(U32, xs, from), Equal.sym(List<&2, U32>, SC.drop(U32, xs, from), Nil{}, ed),
        L.subst(Bool, b => {LB.lbx_step(b, lbs(v, xs, m, 1n+from)) == 0n : Nat}, False{}, SE.ltat(xs, from, v),
          Equal.sym(Bool, SE.ltat(xs, from, v), False{},
            L.subst(Maybe<&2, U32>, mm => {SE.ltm(mm, v) == False{} : Bool}, None{}, SC.nth(U32, xs, from),
              Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, from), None{},
                L.subst(List<&2, U32>, ys => {SC.nth(U32, xs, from) == SC.head(U32, ys) : Maybe<&2, U32>}, SC.drop(U32, xs, from), Nil{}, ed, head_drop(U32, xs, from))),
              {==})),
          {==}))
    case Con{+hh, +tt}:
      L.subst(List<&2, U32>, ys => {lbs(v, xs, 1n+m, from) == lbu(v, SC.take(U32, ys, 1n+m)) : Nat}, Con{hh, tt}, SC.drop(U32, xs, from), Equal.sym(List<&2, U32>, SC.drop(U32, xs, from), Con{hh, tt}, ed),
        L.subst(Bool, b => {LB.lbx_step(b, lbs(v, xs, m, 1n+from)) == LB.lbx_step(Cmp.is_lt(U32.cmp(hh, v)), lbu(v, SC.take(U32, tt, m))) : Nat}, Cmp.is_lt(U32.cmp(hh, v)), SE.ltat(xs, from, v),
          Equal.sym(Bool, SE.ltat(xs, from, v), Cmp.is_lt(U32.cmp(hh, v)),
            L.subst(Maybe<&2, U32>, mm => {SE.ltm(mm, v) == Cmp.is_lt(U32.cmp(hh, v)) : Bool}, Some{hh}, SC.nth(U32, xs, from),
              Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, from), Some{hh}, drop_head(U32, xs, from, hh, tt, ed)), {==})),
          Equal.cong(Nat, Nat, z => LB.lbx_step(Cmp.is_lt(U32.cmp(hh, v)), z), lbs(v, xs, m, 1n+from), lbu(v, SC.take(U32, tt, m)),
            Equal.trans(Nat, lbs(v, xs, m, 1n+from), lbu(v, ST.win(U32, xs, 1n+from, m)), lbu(v, SC.take(U32, tt, m)),
              ih,
              Equal.cong(List<&2, U32>, Nat, ys => lbu(v, SC.take(U32, ys, m)), SC.drop(U32, xs, 1n+from), tt, drop_tail(U32, xs, from, hh, tt, ed))))))

# nth is the head of the dropped tail.
def lbs_lbu(+v: U32, +xs: List<&2, U32>, +k: Nat, +from: Nat) -> {lbs(v, xs, k, from) == lbu(v, ST.win(U32, xs, from, k)) : Nat}:
  match k:
    case 0n:
      L.subst(List<&2, U32>, ys => {0n == lbu(v, ys) : Nat}, Nil{}, SC.take(U32, SC.drop(U32, xs, from), 0n),
        Equal.sym(List<&2, U32>, SC.take(U32, SC.drop(U32, xs, from), 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, xs, from))), {==})
    case 1n+m:
      lbs_lbu_go(v, xs, m, from, SC.drop(U32, xs, from), {==}, lbs_lbu(v, xs, m, 1n+from))

# ---- the specification's `find` and the lower bound ----

# The i-th key of a list, compared with v (False when i is past the end).
def eq_at(+ws: List<&2, U32>, +i: Nat, +v: U32) -> Bool:
  SE.eqm(SC.nth(U32, ws, i), v)

# Keys of the abstraction are the window itself (when the two windows have
# the same length, which the representation invariant guarantees).
def amodel_keys(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +hlen: {SC.length(U32, ks) == SC.length(AR.Tree<U32>, bs) : Nat}) -> {LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)) == ks : List<&2, U32>}:
  match ks bs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bt}:
      Empty.absurd({LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Nil{}, Con{b, bt})) == Nil{} : List<&2, U32>}, N.zero_succ(SC.length(AR.Tree<U32>, bt), hlen))
    case Con{k, kt} Nil{}:
      Empty.absurd({LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(Con{k, kt}, Nil{})) == Con{k, kt} : List<&2, U32>}, N.succ_zero(SC.length(U32, kt), hlen))
    case Con{+k, +kt} Con{+b, +bt}:
      Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{k, ys}, LB.keys_of(List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt)), kt, amodel_keys(kt, bt, N.succ_inj(SC.length(U32, kt), SC.length(AR.Tree<U32>, bt), hlen)))

# ---- sortedness transfers to the abstraction ----

def val_i(+xs: List<&2, U32>, +i: Nat) -> U32:
  L.some_value(U32, SC.nth(U32, xs, i), 0)

# A window with at least one slot is the head slot followed by the rest.
def win_cons(+xs: List<&2, U32>, +from: Nat, +m: Nat, +h: U32, +t: List<&2, U32>, +e: {SC.drop(U32, xs, from) == Con{h, t} : List<&2, U32>}) -> {ST.win(U32, xs, from, 1n+m) == Con{h, ST.win(U32, xs, 1n+from, m)} : List<&2, U32>}:
  Equal.trans(List<&2, U32>, SC.take(U32, SC.drop(U32, xs, from), 1n+m), SC.take(U32, Con{h, t}, 1n+m), Con{h, ST.win(U32, xs, 1n+from, m)},
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => SC.take(U32, ys, 1n+m), SC.drop(U32, xs, from), Con{h, t}, e),
    Equal.cong(List<&2, U32>, List<&2, U32>, ys => Con{h, SC.take(U32, ys, m)}, t, SC.drop(U32, xs, 1n+from),
      Equal.sym(List<&2, U32>, SC.drop(U32, xs, 1n+from), t, drop_tail(U32, xs, from, h, t, e))))

# The head of a nonempty window is the slot value there.
def win_head(+xs: List<&2, U32>, +from: Nat, +h: U32, +t: List<&2, U32>, +e: {SC.drop(U32, xs, from) == Con{h, t} : List<&2, U32>}) -> {val_i(xs, from) == h : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => L.some_value(U32, m, 0), SC.nth(U32, xs, from), Some{h}, drop_head(U32, xs, from, h, t, e))

# `above_at` on the slots becomes `above` on the window list.
def none_not_lt(m: Maybe<&2, U32>) -> {SE.ltm2(m, None{}) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# `ltat2(xs, i, from)` with the slot at `from` known is a plain comparison.
def slot_lt_go(+xs: List<&2, U32>, +i: Nat, +from: Nat, +hh: U32, +tt: List<&2, U32>, +ed: {SC.drop(U32, xs, from) == Con{hh, tt} : List<&2, U32>}, +h: {SE.ltat2(xs, i, from) == True{} : Bool}, mi: Maybe<&2, U32>, +ei: {SC.nth(U32, xs, i) == mi : Maybe<&2, U32>}) -> {Cmp.is_lt(U32.cmp(val_i(xs, i), hh)) == True{} : Bool}:
  match mi:
    case None{}:
      Empty.absurd({Cmp.is_lt(U32.cmp(val_i(xs, i), hh)) == True{} : Bool},
        L.true_not_false(SE.ltat2(xs, i, from), h,
          L.subst(Maybe<&2, U32>, mm => {SE.ltm2(mm, SC.nth(U32, xs, from)) == False{} : Bool}, None{}, SC.nth(U32, xs, i), Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, i), None{}, ei), {==})))
    case Some{+x}:
      L.subst(U32, z => {Cmp.is_lt(U32.cmp(z, hh)) == True{} : Bool}, x, val_i(xs, i),
        Equal.sym(U32, val_i(xs, i), x, Equal.cong(Maybe<&2, U32>, U32, mm => L.some_value(U32, mm, 0), SC.nth(U32, xs, i), Some{x}, ei)),
        L.subst(Maybe<&2, U32>, mm => {SE.ltm2(Some{x}, mm) == True{} : Bool}, SC.nth(U32, xs, from), Some{hh}, drop_head(U32, xs, from, hh, tt, ed),
          L.subst(Maybe<&2, U32>, mm => {SE.ltm2(mm, SC.nth(U32, xs, from)) == True{} : Bool}, SC.nth(U32, xs, i), Some{x}, ei, h)))

def slot_lt(+xs: List<&2, U32>, +i: Nat, +from: Nat, +hh: U32, +tt: List<&2, U32>, +ed: {SC.drop(U32, xs, from) == Con{hh, tt} : List<&2, U32>}, +h: {SE.ltat2(xs, i, from) == True{} : Bool}) -> {Cmp.is_lt(U32.cmp(val_i(xs, i), hh)) == True{} : Bool}:
  slot_lt_go(xs, i, from, hh, tt, ed, h, SC.nth(U32, xs, i), {==})

def above_win_go(+r: Nat, +xs: List<&2, U32>, +i: Nat, +from: Nat, +h: {SE.above_at(1n+r, xs, i, from) == True{} : Bool}, ds: List<&2, U32>, +ed: {SC.drop(U32, xs, from) == ds : List<&2, U32>}, +ih: {ST.above(val_i(xs, i), ST.win(U32, xs, 1n+from, r)) == True{} : Bool}) -> {ST.above(val_i(xs, i), ST.win(U32, xs, from, 1n+r)) == True{} : Bool}:
  match ds:
    case Nil{}:
      # no slot there: `ltat2` would be False, contradicting the premise
      Empty.absurd({ST.above(val_i(xs, i), ST.win(U32, xs, from, 1n+r)) == True{} : Bool},
        L.true_not_false(SE.ltat2(xs, i, from), L.and_left(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from), h),
          L.subst(Maybe<&2, U32>, mm => {SE.ltm2(SC.nth(U32, xs, i), mm) == False{} : Bool}, None{}, SC.nth(U32, xs, from),
            Equal.sym(Maybe<&2, U32>, SC.nth(U32, xs, from), None{},
              Equal.trans(Maybe<&2, U32>, SC.nth(U32, xs, from), SC.head(U32, SC.drop(U32, xs, from)), None{},
                head_drop(U32, xs, from),
                Equal.cong(List<&2, U32>, Maybe<&2, U32>, ys => SC.head(U32, ys), SC.drop(U32, xs, from), Nil{}, ed))),
            none_not_lt(SC.nth(U32, xs, i)))))
    case Con{+hh, +tt}:
      L.subst(List<&2, U32>, ys => {ST.above(val_i(xs, i), ys) == True{} : Bool}, Con{hh, ST.win(U32, xs, 1n+from, r)}, ST.win(U32, xs, from, 1n+r),
        Equal.sym(List<&2, U32>, ST.win(U32, xs, from, 1n+r), Con{hh, ST.win(U32, xs, 1n+from, r)}, win_cons(xs, from, r, hh, tt, ed)),
        L.and_intro(Cmp.is_lt(U32.cmp(val_i(xs, i), hh)), ST.above(val_i(xs, i), ST.win(U32, xs, 1n+from, r)),
          slot_lt(xs, i, from, hh, tt, ed, L.and_left(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from), h)),
          ih))

def above_win(+m: Nat, +xs: List<&2, U32>, +i: Nat, +from: Nat, +h: {SE.above_at(m, xs, i, from) == True{} : Bool}) -> {ST.above(val_i(xs, i), ST.win(U32, xs, from, m)) == True{} : Bool}:
  match m:
    case 0n:
      L.subst(List<&2, U32>, ys => {ST.above(val_i(xs, i), ys) == True{} : Bool}, Nil{}, ST.win(U32, xs, from, 0n),
        Equal.sym(List<&2, U32>, ST.win(U32, xs, from, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, xs, from))), {==})
    case 1n+r:
      above_win_go(r, xs, i, from, h, SC.drop(U32, xs, from), {==}, above_win(r, xs, i, 1n+from, L.and_right(SE.ltat2(xs, i, from), SE.above_at(r, xs, i, 1n+from), h)))

# The whole window is strictly ascending as a list.
def asc_win_go(+m: Nat, +xs: List<&2, U32>, +from: Nat, +h: {SE.asc_at(1n+m, xs, from) == True{} : Bool}, ds: List<&2, U32>, +ed: {SC.drop(U32, xs, from) == ds : List<&2, U32>}, +ih: {ST.asc(ST.win(U32, xs, 1n+from, m)) == True{} : Bool}) -> {ST.asc(ST.win(U32, xs, from, 1n+m)) == True{} : Bool}:
  match ds:
    case Nil{}:
      # the window is empty after all: take of Nil is Nil
      L.subst(List<&2, U32>, ys => {ST.asc(SC.take(U32, ys, 1n+m)) == True{} : Bool}, Nil{}, SC.drop(U32, xs, from),
        Equal.sym(List<&2, U32>, SC.drop(U32, xs, from), Nil{}, ed), {==})
    case Con{+hh, +tt}:
      L.subst(List<&2, U32>, ys => {ST.asc(ys) == True{} : Bool}, Con{hh, ST.win(U32, xs, 1n+from, m)}, ST.win(U32, xs, from, 1n+m),
        Equal.sym(List<&2, U32>, ST.win(U32, xs, from, 1n+m), Con{hh, ST.win(U32, xs, 1n+from, m)}, win_cons(xs, from, m, hh, tt, ed)),
        L.and_intro(ST.above(hh, ST.win(U32, xs, 1n+from, m)), ST.asc(ST.win(U32, xs, 1n+from, m)),
          L.subst(U32, z => {ST.above(z, ST.win(U32, xs, 1n+from, m)) == True{} : Bool}, val_i(xs, from), hh, win_head(xs, from, hh, tt, ed),
            above_win(m, xs, from, 1n+from, L.and_left(SE.above_at(m, xs, from, 1n+from), SE.asc_at(m, xs, 1n+from), h))),
          ih))

def asc_win(+k: Nat, +xs: List<&2, U32>, +from: Nat, +h: {SE.asc_at(k, xs, from) == True{} : Bool}) -> {ST.asc(ST.win(U32, xs, from, k)) == True{} : Bool}:
  match k:
    case 0n:
      L.subst(List<&2, U32>, ys => {ST.asc(ys) == True{} : Bool}, Nil{}, ST.win(U32, xs, from, 0n),
        Equal.sym(List<&2, U32>, ST.win(U32, xs, from, 0n), Nil{}, LL.sc_take_zero(U32, SC.drop(U32, xs, from))), {==})
    case 1n+m:
      asc_win_go(m, xs, from, h, SC.drop(U32, xs, from), {==},
        asc_win(m, xs, 1n+from, L.and_right(SE.above_at(m, xs, from, 1n+from), SE.asc_at(m, xs, 1n+from), h)))

# ---- the abstraction of an ascending window is a sorted association list ----

def above_amodel(+k: U32, +ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +h: {ST.above(k, ks) == True{} : Bool}) -> {SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs), k) == True{} : Bool}:
  match ks bs:
    case Nil{} bs0:
      {==}
    case Con{k0, kt} Nil{}:
      {==}
    case Con{+k0, +kt} Con{+b, +bt}:
      L.and_intro(Cmp.is_lt(U32.cmp(k, k0)), SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt), k),
        L.and_left(Cmp.is_lt(U32.cmp(k, k0)), ST.above(k, kt), h),
        above_amodel(k, kt, bt, L.and_right(Cmp.is_lt(U32.cmp(k, k0)), ST.above(k, kt), h)))

def sorted_amodel(+ks: List<&2, U32>, +bs: List<&2, AR.Tree<U32>>, +h: {ST.asc(ks) == True{} : Bool}) -> {SO.sorted(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, ST.amodel(ks, bs)) == True{} : Bool}:
  match ks bs:
    case Nil{} bs0:
      {==}
    case Con{k0, kt} Nil{}:
      {==}
    case Con{+k0, +kt} Con{+b, +bt}:
      L.and_intro(SO.above(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt), k0), SO.sorted(~U32, ~U32.cmp, List<&2, BE.Entry<U32, Unit>>, ST.amodel(kt, bt)),
        above_amodel(k0, kt, bt, L.and_left(ST.above(k0, kt), ST.asc(kt), h)),
        sorted_amodel(kt, bt, L.and_right(ST.above(k0, kt), ST.asc(kt), h)))

# The lower bound over the entries is the lower bound over the keys.
def lbx_lbu(-V: Data, +v: U32, +es: List<&2, BE.Entry<U32, V>>) -> {LB.lbx(V, v, es) == lbu(v, LB.keys_of(V, es)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      Equal.cong(Nat, Nat, z => LB.lbx_step(Cmp.is_lt(U32.cmp(BE.key(U32, V, e), v)), z), LB.lbx(V, v, t), lbu(v, LB.keys_of(V, t)), lbx_lbu(V, v, t))

# ---- small arithmetic and the `found` bridge ----

def add_mono(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      add_mono(p, a, b, h)

def eqm_same(m: Maybe<&2, U32>, +v: U32) -> {LB.eqm(m, v) == SE.eqm(m, v) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

# The length of a window that fits inside the block.
def drop_length(-A: Data, +xs: List<&2, A>, +n: Nat) -> {SC.length(A, SC.drop(A, xs, n)) == Nat.sub(SC.length(A, xs), n) : Nat}:
  match xs n:
    case Nil{} n0:
      Equal.trans(Nat, SC.length(A, SC.drop(A, Nil{}, n0)), 0n, Nat.sub(0n, n0),
        Equal.cong(List<&2, A>, Nat, ys => SC.length(A, ys), SC.drop(A, Nil{}, n0), Nil{}, nil_drop(A, n0)),
        Equal.sym(Nat, Nat.sub(0n, n0), 0n, SE.zero_sub(n0)))
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      drop_length(A, t, p)

# lo + k <= n gives k <= n - lo.
def le_sub_of_add(+k: Nat, +lo: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(lo, k), n) == True{} : Bool}) -> {Nat.is_le(k, Nat.sub(n, lo)) == True{} : Bool}:
  match lo n:
    case 0n n0:
      L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, n0, Nat.sub(n0, 0n), Equal.sym(Nat, Nat.sub(n0, 0n), n0, N.sub_zero(n0)), h)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(k, Nat.sub(0n, 1n+p)) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      le_sub_of_add(k, p, q, h)

def win_length(+xs: List<&2, U32>, +lo: Nat, +k: Nat, +h: {Nat.is_le(Nat.add(lo, k), SC.length(U32, xs)) == True{} : Bool}) -> {SC.length(U32, ST.win(U32, xs, lo, k)) == k : Nat}:
  LL.sc_length_take(U32, SC.drop(U32, xs, lo), k,
    L.subst(Nat, z => {Nat.is_le(k, z) == True{} : Bool}, Nat.sub(SC.length(U32, xs), lo), SC.length(U32, SC.drop(U32, xs, lo)),
      Equal.sym(Nat, SC.length(U32, SC.drop(U32, xs, lo)), Nat.sub(SC.length(U32, xs), lo), drop_length(U32, xs, lo)),
      le_sub_of_add(k, lo, SC.length(U32, xs), h)))

# `found_of` at the lower bound is "the window entry there is v".
def window_end(+lo: Nat, +hi: Nat, +k: Nat, +hk: {k == Nat.sub(hi, lo) : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}) -> {Nat.add(lo, k) == hi : Nat}:
  L.subst(Nat, z => {Nat.add(lo, z) == hi : Nat}, Nat.sub(hi, lo), k, Equal.sym(Nat, k, Nat.sub(hi, lo), hk), N.sub_add(hi, lo, hlo))

def add_lt(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      add_lt(p, a, b, h)

def lt_window(+lo: Nat, +hi: Nat, +k: Nat, +l: Nat, +hk: {k == Nat.sub(hi, lo) : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hl: {Nat.is_lt(l, k) == True{} : Bool}) -> {Nat.is_lt(Nat.add(lo, l), hi) == True{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(lo, l), z) == True{} : Bool}, Nat.add(lo, k), hi, window_end(lo, hi, k, hk, hlo),
    add_lt(lo, l, k, hl))

def not_lt_window(+lo: Nat, +hi: Nat, +k: Nat, +l: Nat, +hk: {k == Nat.sub(hi, lo) : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hge: {Nat.is_le(k, l) == True{} : Bool}, +hl: {Nat.is_le(l, k) == True{} : Bool}) -> {Nat.is_lt(Nat.add(lo, l), hi) == False{} : Bool}:
  L.subst(Nat, z => {Nat.is_lt(Nat.add(lo, z), hi) == False{} : Bool}, k, l, N.le_antisym(k, l, hge, hl),
    L.subst(Nat, z => {Nat.is_lt(z, hi) == False{} : Bool}, hi, Nat.add(lo, k), Equal.sym(Nat, Nat.add(lo, k), hi, window_end(lo, hi, k, hk, hlo)),
      N.lt_irrefl(hi)))

def found_bridge_go(+t: AR.Tree<U32>, +lo: Nat, +hi: Nat, +k: Nat, +l: Nat, +v: U32, +hk: {k == Nat.sub(hi, lo) : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hl: {Nat.is_le(l, k) == True{} : Bool}, +hlen: {Nat.is_le(hi, SC.length(U32, AR.slots(U32, t))) == True{} : Bool}, inside: Bool, +ein: {Nat.is_lt(l, k) == inside : Bool}) -> {SE.found_of(t, Nat.add(lo, l), hi, v) == eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v) : Bool}:
  match inside:
    case True{}:
      # inside the window: both sides read the same slot
      L.subst(Bool, b => {SE.pick(b, SE.eqat(AR.slots(U32, t), Nat.add(lo, l), v)) == eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v) : Bool}, True{}, Nat.is_lt(Nat.add(lo, l), hi),
        Equal.sym(Bool, Nat.is_lt(Nat.add(lo, l), hi), True{}, lt_window(lo, hi, k, l, hk, hlo, ein)),
        Equal.sym(Bool, eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v), SE.eqat(AR.slots(U32, t), Nat.add(lo, l), v),
          Equal.cong(Maybe<&2, U32>, Bool, m => SE.eqm(m, v), SC.nth(U32, ST.win(U32, AR.slots(U32, t), lo, k), l), SC.nth(U32, AR.slots(U32, t), Nat.add(lo, l)), nth_win(U32, AR.slots(U32, t), lo, k, l, ein))))
    case False{}:
      # l is the end of the window: neither side finds anything
      L.subst(Bool, b => {SE.pick(b, SE.eqat(AR.slots(U32, t), Nat.add(lo, l), v)) == eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v) : Bool}, False{}, Nat.is_lt(Nat.add(lo, l), hi),
        Equal.sym(Bool, Nat.is_lt(Nat.add(lo, l), hi), False{}, not_lt_window(lo, hi, k, l, hk, hlo, N.not_lt_le(l, k, ein), hl)),
        Equal.sym(Bool, eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v), False{},
          Equal.trans(Bool, eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v), SE.eqm(None{}, v), False{},
            Equal.cong(Maybe<&2, U32>, Bool, m => SE.eqm(m, v), SC.nth(U32, ST.win(U32, AR.slots(U32, t), lo, k), l), None{},
              LL.nth_none(U32, ST.win(U32, AR.slots(U32, t), lo, k), l,
                L.subst(Nat, z => {Nat.is_le(z, l) == True{} : Bool}, k, SC.length(U32, ST.win(U32, AR.slots(U32, t), lo, k)),
                  Equal.sym(Nat, SC.length(U32, ST.win(U32, AR.slots(U32, t), lo, k)), k,
                    win_length(AR.slots(U32, t), lo, k,
                      L.subst(Nat, z => {Nat.is_le(z, SC.length(U32, AR.slots(U32, t))) == True{} : Bool}, hi, Nat.add(lo, k),
                        Equal.sym(Nat, Nat.add(lo, k), hi, window_end(lo, hi, k, hk, hlo)), hlen))),
                  N.not_lt_le(l, k, ein)))),
            {==})))

# lo + k = hi
def found_bridge(+t: AR.Tree<U32>, +lo: Nat, +hi: Nat, +k: Nat, +l: Nat, +v: U32, +hk: {k == Nat.sub(hi, lo) : Nat}, +hlo: {Nat.is_le(lo, hi) == True{} : Bool}, +hl: {Nat.is_le(l, k) == True{} : Bool}, +hlen: {Nat.is_le(hi, SC.length(U32, AR.slots(U32, t))) == True{} : Bool}) -> {SE.found_of(t, Nat.add(lo, l), hi, v) == eq_at(ST.win(U32, AR.slots(U32, t), lo, k), l, v) : Bool}:
  found_bridge_go(t, lo, hi, k, l, v, hk, hlo, hl, hlen, Nat.is_lt(l, k), {==})
