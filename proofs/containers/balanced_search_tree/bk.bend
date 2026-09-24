import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32.bend as U
import ../../lib/array.bend as AR
import ../../lib/array_ext.bend as AX
import ../../lib/list.bend as LL
import ../../lib/spec_common.bend as SC

# The block of a list with a default: a perfect tree of depth d whose slots
# are the list's items followed by the default v. (mk.bend is the Maybe
# instance: items Some, default None.) The TreeMap's node store keeps one
# such block per node field.

# the first k slots: the items xs, then v
def fillv(-T: Data, +k: Nat, xs: List<&2, T>, +v: T) -> List<&2, T>:
  match k xs:
    case 0n _:
      Nil{}
    case 1n+j Nil{}:
      Con{v, fillv(T, j, Nil{}, v)}
    case 1n+j Con{x, r}:
      Con{x, fillv(T, j, r, v)}

def headv(-T: Data, xs: List<&2, T>, +v: T) -> T:
  match xs:
    case Nil{}:
      v
    case Con{x, r}:
      x

def bk(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T) -> AR.Tree<T>:
  match d:
    case 0n:
      AR.TLeaf{headv(T, xs, v)}
    case 1n+p:
      AR.TNode{bk(T, p, xs, v), bk(T, p, SC.drop(T, xs, SC.pow2(p)), v)}

def bk_perfect(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T) -> {AR.perfect(T, d, bk(T, d, xs, v)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      L.and_intro(AR.perfect(T, p, bk(T, p, xs, v)), AR.perfect(T, p, bk(T, p, SC.drop(T, xs, SC.pow2(p)), v)), bk_perfect(T, p, xs, v), bk_perfect(T, p, SC.drop(T, xs, SC.pow2(p)), v))

def fill_add(-T: Data, +a: Nat, +b: Nat, +xs: List<&2, T>, +v: T) -> {fillv(T, Nat.add(a, b), xs, v) == SC.append(T, fillv(T, a, xs, v), fillv(T, b, SC.drop(T, xs, a), v)) : List<&2, T>}:
  match a xs:
    case 0n _:
      Equal.cong(List<&2, T>, List<&2, T>, z => fillv(T, b, z, v), xs, SC.drop(T, xs, 0n), Equal.sym(List<&2, T>, SC.drop(T, xs, 0n), xs, AX.drop_zero(T, xs)))
    case 1n+j Nil{}:
      LL.cons_cong(T, v, fillv(T, Nat.add(j, b), Nil{}, v), SC.append(T, fillv(T, j, Nil{}, v), fillv(T, b, Nil{}, v)), fill_add(T, j, b, Nil{}, v))
    case 1n+j Con{+x, +r}:
      LL.cons_cong(T, x, fillv(T, Nat.add(j, b), r, v), SC.append(T, fillv(T, j, r, v), fillv(T, b, SC.drop(T, r, j), v)), fill_add(T, j, b, r, v))

def dbl(+p: Nat) -> {SC.pow2(1n+p) == Nat.add(SC.pow2(p), SC.pow2(p)) : Nat}:
  Equal.trans(Nat, Nat.double(SC.pow2(p)), Nat.add(SC.pow2(p), Nat.add(SC.pow2(p), 0n)), Nat.add(SC.pow2(p), SC.pow2(p)), U.double_pow(SC.pow2(p)), Equal.cong(Nat, Nat, z => Nat.add(SC.pow2(p), z), Nat.add(SC.pow2(p), 0n), SC.pow2(p), N.add_zero(SC.pow2(p))))

def fill_one(-T: Data, +xs: List<&2, T>, +v: T) -> {fillv(T, 1n, xs, v) == Con{headv(T, xs, v), Nil{}} : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# the slots of the block
def bk_slots(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T) -> {AR.slots(T, bk(T, d, xs, v)) == fillv(T, SC.pow2(d), xs, v) : List<&2, T>}:
  match d:
    case 0n:
      Equal.sym(List<&2, T>, fillv(T, 1n, xs, v), Con{headv(T, xs, v), Nil{}}, fill_one(T, xs, v))
    case 1n+p:
      +P = SC.pow2(p)
      %Equal.sym(List<&2, T>, AR.slots(T, bk(T, p, xs, v)), fillv(T, P, xs, v), bk_slots(T, p, xs, v)) : {SC.append(T, _, AR.slots(T, bk(T, p, SC.drop(T, xs, P), v))) == fillv(T, SC.pow2(1n+p), xs, v) : List<&2, T>}
      %Equal.sym(List<&2, T>, AR.slots(T, bk(T, p, SC.drop(T, xs, P), v)), fillv(T, P, SC.drop(T, xs, P), v), bk_slots(T, p, SC.drop(T, xs, P), v)) : {SC.append(T, fillv(T, P, xs, v), _) == fillv(T, SC.pow2(1n+p), xs, v) : List<&2, T>}
      %Equal.sym(Nat, SC.pow2(1n+p), Nat.add(P, P), dbl(p)) : {SC.append(T, fillv(T, P, xs, v), fillv(T, P, SC.drop(T, xs, P), v)) == fillv(T, _, xs, v) : List<&2, T>}
      Equal.sym(List<&2, T>, fillv(T, Nat.add(P, P), xs, v), SC.append(T, fillv(T, P, xs, v), fillv(T, P, SC.drop(T, xs, P), v)), fill_add(T, P, P, xs, v))

def fill_len(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T) -> {SC.length(T, fillv(T, k, xs, v)) == k : Nat}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      N.succ_cong(SC.length(T, fillv(T, j, Nil{}, v)), j, fill_len(T, j, Nil{}, v))
    case 1n+j Con{x, +r}:
      N.succ_cong(SC.length(T, fillv(T, j, r, v)), j, fill_len(T, j, r, v))

# a slot below the length reads the item
def fill_nth(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T, +i: Nat, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}, +hk: {Nat.is_le(SC.length(T, xs), k) == True{} : Bool}) -> {SC.nth(T, fillv(T, k, xs, v), i) == SC.nth(T, xs, i) : Maybe<&2, T>}:
  match k xs i:
    case 0n Nil{} _:
      Empty.absurd({SC.nth(T, Nil{}, i) == SC.nth(T, Nil{}, i) : Maybe<&2, T>}, N.lt_zero_absurd(i, h))
    case 0n Con{x, r} _:
      Empty.absurd({SC.nth(T, Nil{}, i) == SC.nth(T, Con{x, r}, i) : Maybe<&2, T>}, L.false_true(hk))
    case 1n+j Nil{} _:
      Empty.absurd({SC.nth(T, fillv(T, 1n+j, Nil{}, v), i) == SC.nth(T, Nil{}, i) : Maybe<&2, T>}, N.lt_zero_absurd(i, h))
    case 1n+j Con{x, r} 0n:
      {==}
    case 1n+j Con{x, +r} 1n+q:
      fill_nth(T, j, r, v, q, h, hk)

def fill_upd(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T, +i: Nat, +y: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}) -> {SC.update(T, fillv(T, k, xs, v), i, y) == fillv(T, k, SC.update(T, xs, i, y), v) : List<&2, T>}:
  match k xs i:
    case 0n _ _:
      {==}
    case 1n+j Nil{} _:
      Empty.absurd({SC.update(T, fillv(T, 1n+j, Nil{}, v), i, y) == fillv(T, 1n+j, Nil{}, v) : List<&2, T>}, N.lt_zero_absurd(i, h))
    case 1n+j Con{x, r} 0n:
      {==}
    case 1n+j Con{+x, +r} 1n+q:
      LL.cons_cong(T, x, SC.update(T, fillv(T, j, r, v), q, y), fillv(T, j, SC.update(T, r, q, y), v), fill_upd(T, j, r, v, q, y, h))

def fill_snoc(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T, +y: T, +h: {Nat.is_lt(SC.length(T, xs), k) == True{} : Bool}) -> {SC.update(T, fillv(T, k, xs, v), SC.length(T, xs), y) == fillv(T, k, SC.snoc(T, xs, y), v) : List<&2, T>}:
  match k xs:
    case 0n _:
      Empty.absurd({SC.update(T, Nil{}, SC.length(T, xs), y) == Nil{} : List<&2, T>}, N.lt_zero_absurd(SC.length(T, xs), h))
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{+x, +r}:
      LL.cons_cong(T, x, SC.update(T, fillv(T, j, r, v), SC.length(T, r), y), fillv(T, j, SC.snoc(T, r, y), v), fill_snoc(T, j, r, v, y, h))

def fill_init_c(-T: Data, +j: Nat, +x: T, +r: List<&2, T>, +v: T, +m: Nat, +hm: {SC.length(T, Con{x, r}) == 1n+m : Nat}, ih: @+m2: Nat -> @+hm2: {SC.length(T, r) == 1n+m2 : Nat} -> {SC.update(T, fillv(T, j, r, v), m2, v) == fillv(T, j, SC.init(T, r), v) : List<&2, T>}) -> {SC.update(T, fillv(T, 1n+j, Con{x, r}, v), m, v) == fillv(T, 1n+j, SC.init(T, Con{x, r}), v) : List<&2, T>}:
  match r m:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      Empty.absurd({SC.update(T, fillv(T, 1n+j, Con{x, Nil{}}, v), 1n+q, v) == fillv(T, 1n+j, SC.init(T, Con{x, Nil{}}), v) : List<&2, T>}, N.zero_succ(q, N.succ_inj(0n, 1n+q, hm)))
    case Con{y, t} 0n:
      Empty.absurd({SC.update(T, fillv(T, 1n+j, Con{x, Con{y, t}}, v), 0n, v) == fillv(T, 1n+j, SC.init(T, Con{x, Con{y, t}}), v) : List<&2, T>}, N.succ_zero(SC.length(T, t), N.succ_inj(1n+SC.length(T, t), 0n, hm)))
    case Con{+y, +t} 1n+q:
      LL.cons_cong(T, x, SC.update(T, fillv(T, j, Con{y, t}, v), q, v), fillv(T, j, SC.init(T, Con{y, t}), v), ih(q, N.succ_inj(1n+SC.length(T, t), 1n+q, hm)))

# the last item reset to the default (a pop)
def fill_init(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T, +m: Nat, +hm: {SC.length(T, xs) == 1n+m : Nat}) -> {SC.update(T, fillv(T, k, xs, v), m, v) == fillv(T, k, SC.init(T, xs), v) : List<&2, T>}:
  match k xs:
    case 0n _:
      {==}
    case 1n+j Nil{}:
      Empty.absurd({SC.update(T, fillv(T, 1n+j, Nil{}, v), m, v) == fillv(T, 1n+j, SC.init(T, Nil{}), v) : List<&2, T>}, N.zero_succ(m, hm))
    case 1n+j Con{+x, +r}:
      fill_init_c(T, j, x, r, v, m, hm, m2 => hm2 => fill_init(T, j, r, v, m2, hm2))

# ---- trees equal to blocks ----

def bk_eq(-T: Data, +d: Nat, +u: AR.Tree<T>, +xs: List<&2, T>, +v: T, +pu: {AR.perfect(T, d, u) == True{} : Bool}, +e: {AR.slots(T, u) == fillv(T, SC.pow2(d), xs, v) : List<&2, T>}) -> {u == bk(T, d, xs, v) : AR.Tree<T>}:
  AX.tree_ext(T, d, u, bk(T, d, xs, v), pu, bk_perfect(T, d, xs, v), Equal.trans(List<&2, T>, AR.slots(T, u), fillv(T, SC.pow2(d), xs, v), AR.slots(T, bk(T, d, xs, v)), e, Equal.sym(List<&2, T>, AR.slots(T, bk(T, d, xs, v)), fillv(T, SC.pow2(d), xs, v), bk_slots(T, d, xs, v))))

def bk_upd(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T, +i: Nat, +y: T, +hi: {Nat.is_lt(i, SC.pow2(d)) == True{} : Bool}, +ys: List<&2, T>, +hf: {SC.update(T, fillv(T, SC.pow2(d), xs, v), i, y) == fillv(T, SC.pow2(d), ys, v) : List<&2, T>}) -> {AR.upd(T, d, bk(T, d, xs, v), i, y) == bk(T, d, ys, v) : AR.Tree<T>}:
  +es = Equal.trans(List<&2, T>, AR.slots(T, AR.upd(T, d, bk(T, d, xs, v), i, y)), SC.update(T, AR.slots(T, bk(T, d, xs, v)), i, y), fillv(T, SC.pow2(d), ys, v), AR.upd_slots(T, d, bk(T, d, xs, v), i, y, hi, bk_perfect(T, d, xs, v)), Equal.trans(List<&2, T>, SC.update(T, AR.slots(T, bk(T, d, xs, v)), i, y), SC.update(T, fillv(T, SC.pow2(d), xs, v), i, y), fillv(T, SC.pow2(d), ys, v), Equal.cong(List<&2, T>, List<&2, T>, z => SC.update(T, z, i, y), AR.slots(T, bk(T, d, xs, v)), fillv(T, SC.pow2(d), xs, v), bk_slots(T, d, xs, v)), hf))
  bk_eq(T, d, AR.upd(T, d, bk(T, d, xs, v), i, y), ys, v, AR.upd_perfect(T, d, bk(T, d, xs, v), i, y, bk_perfect(T, d, xs, v)), es)

# a slot written below the length
def bk_set(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T, +i: Nat, +y: T, +h: {Nat.is_lt(i, SC.length(T, xs)) == True{} : Bool}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {AR.upd(T, d, bk(T, d, xs, v), i, y) == bk(T, d, SC.update(T, xs, i, y), v) : AR.Tree<T>}:
  bk_upd(T, d, xs, v, i, y, N.lt_le_trans(i, SC.length(T, xs), SC.pow2(d), h, hc), SC.update(T, xs, i, y), fill_upd(T, SC.pow2(d), xs, v, i, y, h))

# the slot at the length written (a push with room)
def bk_push(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T, +y: T, +h: {Nat.is_lt(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {AR.upd(T, d, bk(T, d, xs, v), SC.length(T, xs), y) == bk(T, d, SC.snoc(T, xs, y), v) : AR.Tree<T>}:
  bk_upd(T, d, xs, v, SC.length(T, xs), y, h, SC.snoc(T, xs, y), fill_snoc(T, SC.pow2(d), xs, v, y, h))

# the last slot reset to the default (a pop)
def bk_pop(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T, +m: Nat, +hm: {SC.length(T, xs) == 1n+m : Nat}, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {AR.upd(T, d, bk(T, d, xs, v), m, v) == bk(T, d, SC.init(T, xs), v) : AR.Tree<T>}:
  +hl = L.subst(Nat, z => {Nat.is_le(z, SC.pow2(d)) == True{} : Bool}, SC.length(T, xs), 1n+m, hm, hc)
  bk_upd(T, d, xs, v, m, v, N.lt_le_trans(m, 1n+m, SC.pow2(d), N.lt_succ(m), hl), SC.init(T, xs), fill_init(T, SC.pow2(d), xs, v, m, hm))

def fill_rep(-T: Data, +k: Nat, +v: T) -> {fillv(T, k, Nil{}, v) == SC.replicate(T, k, v) : List<&2, T>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      LL.cons_cong(T, v, fillv(T, j, Nil{}, v), SC.replicate(T, j, v), fill_rep(T, j, v))

def drop_all(-T: Data, +xs: List<&2, T>, +k: Nat, +h: {Nat.is_le(SC.length(T, xs), k) == True{} : Bool}) -> {SC.drop(T, xs, k) == Nil{} : List<&2, T>}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, r} 0n:
      Empty.absurd({Con{x, r} == Nil{} : List<&2, T>}, L.false_true(h))
    case Con{x, +r} 1n+j:
      drop_all(T, r, j, h)

def bk_empty(-T: Data, +d: Nat, +v: T) -> {AR.trep(T, d, v) == bk(T, d, Nil{}, v) : AR.Tree<T>}:
  bk_eq(T, d, AR.trep(T, d, v), Nil{}, v, AR.trep_perfect(T, d, v), Equal.trans(List<&2, T>, AR.slots(T, AR.trep(T, d, v)), SC.replicate(T, SC.pow2(d), v), fillv(T, SC.pow2(d), Nil{}, v), AR.trep_slots(T, d, v), Equal.sym(List<&2, T>, fillv(T, SC.pow2(d), Nil{}, v), SC.replicate(T, SC.pow2(d), v), fill_rep(T, SC.pow2(d), v))))

# the doubled block (the old block and a default half)
def bk_grow(-T: Data, +d: Nat, +xs: List<&2, T>, +v: T, +hc: {Nat.is_le(SC.length(T, xs), SC.pow2(d)) == True{} : Bool}) -> {AR.TNode{bk(T, d, xs, v), AR.trep(T, d, v)} == bk(T, 1n+d, xs, v) : AR.Tree<T>}:
  +e1 = Equal.trans(AR.Tree<T>, AR.trep(T, d, v), bk(T, d, Nil{}, v), bk(T, d, SC.drop(T, xs, SC.pow2(d)), v), bk_empty(T, d, v), Equal.cong(List<&2, T>, AR.Tree<T>, z => bk(T, d, z, v), Nil{}, SC.drop(T, xs, SC.pow2(d)), Equal.sym(List<&2, T>, SC.drop(T, xs, SC.pow2(d)), Nil{}, drop_all(T, xs, SC.pow2(d), hc))))
  Equal.cong(AR.Tree<T>, AR.Tree<T>, z => AR.TNode{bk(T, d, xs, v), z}, AR.trep(T, d, v), bk(T, d, SC.drop(T, xs, SC.pow2(d)), v), e1)

# the slot at the length (inside the capacity) holds the default
def fill_at_len(-T: Data, +k: Nat, +xs: List<&2, T>, +v: T, +h: {Nat.is_lt(SC.length(T, xs), k) == True{} : Bool}) -> {SC.nth(T, fillv(T, k, xs, v), SC.length(T, xs)) == Some{v} : Maybe<&2, T>}:
  match k xs:
    case 0n _:
      Empty.absurd({SC.nth(T, Nil{}, SC.length(T, xs)) == Some{v} : Maybe<&2, T>}, N.lt_zero_absurd(SC.length(T, xs), h))
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{x, +r}:
      fill_at_len(T, j, r, v, h)
