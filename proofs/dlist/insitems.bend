import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../graph/shift.bend as SH
import ../../spec/common.bend as SC
import ../../spec/doubly_linked_list.bend as DS
import ../../src/doubly_linked_list.bend as D
import ../../types/doubly_linked_list.bend as E
import ./state.bend as ST
import ./facts.bend as F
import ./links.bend as LK
import ./items.bend as IT
import ./alive.bend as AL
import ./nbrs.bend as NB
import ./mu0.bend as MU0
import ./split.bend as SP
import ./retarget.bend as RT
import ./tolist.bend as TLa
import ./rmfacts.bend as RF
import ./core.bend as K
import ./mut.bend as MU
import ./insfacts.bend as IF

# The model after splicing: the new item sits between the items of x and y,
# which is the spec's ins_before / ins_after at the handle's item.

def items_ins(-T: Data, +xs: List<&2, Maybe<&2, T>>, +x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +v: T, +hfx: {ST.lmem(f, x) == False{} : Bool}, +hfy: {ST.lmem(f, y) == False{} : Bool}, +hn: {Nat.is_lt(f, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}) -> {ST.items(T, SC.update(Maybe<&2, T>, xs, f, Some{v}), SC.append(Nat, x, Con{f, y})) == SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(f), v}, ST.items(T, xs, y)}) : List<&2, E.Item<T>>}:
  +ys = SC.update(Maybe<&2, T>, xs, f, Some{v})
  +ey = Equal.trans(List<&2, E.Item<T>>, ST.items(T, ys, Con{f, y}), Con{E.Item{U32.from_nat(f), v}, ST.items(T, ys, y)}, Con{E.Item{U32.from_nat(f), v}, ST.items(T, xs, y)},
    Equal.cong(Maybe<&2, T>, List<&2, E.Item<T>>, m => ST.itm(T, m, f, ST.items(T, ys, y)), ST.vat(T, ys, f), Some{v}, LK.vat_same(T, xs, f, Some{v}, hn)),
    LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(f), v}, ST.items(T, ys, y), ST.items(T, xs, y), MU.items_frame(T, xs, y, f, Some{v}, hfy)))
  Equal.trans(List<&2, E.Item<T>>, ST.items(T, ys, SC.append(Nat, x, Con{f, y})), SC.append(E.Item<T>, ST.items(T, ys, x), ST.items(T, ys, Con{f, y})), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(f), v}, ST.items(T, xs, y)}),
    AL.items_app(T, ys, x, Con{f, y}),
    Equal.trans(List<&2, E.Item<T>>, SC.append(E.Item<T>, ST.items(T, ys, x), ST.items(T, ys, Con{f, y})), SC.append(E.Item<T>, ST.items(T, xs, x), ST.items(T, ys, Con{f, y})), SC.append(E.Item<T>, ST.items(T, xs, x), Con{E.Item{U32.from_nat(f), v}, ST.items(T, xs, y)}),
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, z, ST.items(T, ys, Con{f, y})), ST.items(T, ys, x), ST.items(T, xs, x), MU.items_frame(T, xs, x, f, Some{v}, hfx)),
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, x), z), ST.items(T, ys, Con{f, y}), Con{E.Item{U32.from_nat(f), v}, ST.items(T, xs, y)}, ey)))

def ib_c(-T: Data, +x: Nat, +v: T, +l: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +hne: {U32.is_eq(U32.from_nat(x), i) == False{} : Bool}) -> {DS.ins_before(T, Con{E.Item{U32.from_nat(x), v}, l}, i, it) == Con{E.Item{U32.from_nat(x), v}, DS.ins_before(T, l, i, it)} : List<&2, E.Item<T>>}:
  L.subst(Bool, b => {DS.pick(T, b, Con{it, Con{E.Item{U32.from_nat(x), v}, l}}, Con{E.Item{U32.from_nat(x), v}, DS.ins_before(T, l, i, it)}) == Con{E.Item{U32.from_nat(x), v}, DS.ins_before(T, l, i, it)} : List<&2, E.Item<T>>}, False{}, U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), False{}, hne), {==})

def ia_c(-T: Data, +x: Nat, +v: T, +l: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +hne: {U32.is_eq(U32.from_nat(x), i) == False{} : Bool}) -> {DS.ins_after(T, Con{E.Item{U32.from_nat(x), v}, l}, i, it) == Con{E.Item{U32.from_nat(x), v}, DS.ins_after(T, l, i, it)} : List<&2, E.Item<T>>}:
  L.subst(Bool, b => {DS.pick(T, b, Con{E.Item{U32.from_nat(x), v}, Con{it, l}}, Con{E.Item{U32.from_nat(x), v}, DS.ins_after(T, l, i, it)}) == Con{E.Item{U32.from_nat(x), v}, DS.ins_after(T, l, i, it)} : List<&2, E.Item<T>>}, False{}, U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), False{}, hne), {==})

def ib_found(-T: Data, +x: Nat, +v: T, +l: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +he: {U32.is_eq(U32.from_nat(x), i) == True{} : Bool}) -> {DS.ins_before(T, Con{E.Item{U32.from_nat(x), v}, l}, i, it) == Con{it, Con{E.Item{U32.from_nat(x), v}, l}} : List<&2, E.Item<T>>}:
  L.subst(Bool, b => {DS.pick(T, b, Con{it, Con{E.Item{U32.from_nat(x), v}, l}}, Con{E.Item{U32.from_nat(x), v}, DS.ins_before(T, l, i, it)}) == Con{it, Con{E.Item{U32.from_nat(x), v}, l}} : List<&2, E.Item<T>>}, True{}, U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), True{}, he), {==})

def ia_found(-T: Data, +x: Nat, +v: T, +l: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +he: {U32.is_eq(U32.from_nat(x), i) == True{} : Bool}) -> {DS.ins_after(T, Con{E.Item{U32.from_nat(x), v}, l}, i, it) == Con{E.Item{U32.from_nat(x), v}, Con{it, l}} : List<&2, E.Item<T>>}:
  L.subst(Bool, b => {DS.pick(T, b, Con{E.Item{U32.from_nat(x), v}, Con{it, l}}, Con{E.Item{U32.from_nat(x), v}, DS.ins_after(T, l, i, it)}) == Con{E.Item{U32.from_nat(x), v}, Con{it, l}} : List<&2, E.Item<T>>}, True{}, U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), True{}, he), {==})

# insertion skips the items of a when i is not among its ids
def ib_skip(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +r: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, a) == True{} : Bool}, +hni: {ST.lmem(U32.to_nat(i), a) == False{} : Bool}) -> {DS.ins_before(T, SC.append(E.Item<T>, ST.items(T, xs, a), r), i, it) == SC.append(E.Item<T>, ST.items(T, xs, a), DS.ins_before(T, r, i, it)) : List<&2, E.Item<T>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha)
      +vx = AL.val_of(T, ST.vat(T, xs, x), hy)
      +hne0 = LK.or_false_l(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)
      +hne = Equal.trans(Bool, U32.is_eq(U32.from_nat(x), i), Nat.is_eq(x, U32.to_nat(i)), False{}, IT.ueq(x, i, depth, hd, IT.lt_head(x, t, SC.pow2(depth), hl)), hne0)
      +eit = AL.itm_some(T, ST.vat(T, xs, x), x, ST.items(T, xs, t), hy)
      L.subst(List<&2, E.Item<T>>, z => {DS.ins_before(T, SC.append(E.Item<T>, z, r), i, it) == SC.append(E.Item<T>, z, DS.ins_before(T, r, i, it)) : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, ST.items(T, xs, Con{x, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{x, t}), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, eit),
        Equal.trans(List<&2, E.Item<T>>, DS.ins_before(T, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), r)}, i, it), Con{E.Item{U32.from_nat(x), vx}, DS.ins_before(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it)}, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), DS.ins_before(T, r, i, it))},
          ib_c(T, x, vx, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it, hne),
          LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(x), vx}, DS.ins_before(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it), SC.append(E.Item<T>, ST.items(T, xs, t), DS.ins_before(T, r, i, it)),
            ib_skip(T, xs, t, r, i, it, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha), LK.or_false_r(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)))))

def ia_skip(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +r: List<&2, E.Item<T>>, +i: U32, +it: E.Item<T>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, a) == True{} : Bool}, +hni: {ST.lmem(U32.to_nat(i), a) == False{} : Bool}) -> {DS.ins_after(T, SC.append(E.Item<T>, ST.items(T, xs, a), r), i, it) == SC.append(E.Item<T>, ST.items(T, xs, a), DS.ins_after(T, r, i, it)) : List<&2, E.Item<T>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha)
      +vx = AL.val_of(T, ST.vat(T, xs, x), hy)
      +hne0 = LK.or_false_l(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)
      +hne = Equal.trans(Bool, U32.is_eq(U32.from_nat(x), i), Nat.is_eq(x, U32.to_nat(i)), False{}, IT.ueq(x, i, depth, hd, IT.lt_head(x, t, SC.pow2(depth), hl)), hne0)
      +eit = AL.itm_some(T, ST.vat(T, xs, x), x, ST.items(T, xs, t), hy)
      L.subst(List<&2, E.Item<T>>, z => {DS.ins_after(T, SC.append(E.Item<T>, z, r), i, it) == SC.append(E.Item<T>, z, DS.ins_after(T, r, i, it)) : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, ST.items(T, xs, Con{x, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{x, t}), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, eit),
        Equal.trans(List<&2, E.Item<T>>, DS.ins_after(T, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), r)}, i, it), Con{E.Item{U32.from_nat(x), vx}, DS.ins_after(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it)}, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), DS.ins_after(T, r, i, it))},
          ia_c(T, x, vx, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it, hne),
          LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(x), vx}, DS.ins_after(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i, it), SC.append(E.Item<T>, ST.items(T, xs, t), DS.ins_after(T, r, i, it)),
            ia_skip(T, xs, t, r, i, it, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha), LK.or_false_r(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)))))

def n_notin(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +hnd: {ST.nodup(SC.append(Nat, a, Con{n, b})) == True{} : Bool}) -> {ST.lmem(n, a) == False{} : Bool}:
  SP.disj_mem(a, Con{n, b}, n, SP.nodup_disj(a, Con{n, b}, hnd), L.subst(Bool, z => {Bool.or(z, ST.lmem(n, b)) == True{} : Bool}, True{}, Nat.is_eq(n, n), Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.is_eq_refl(n)), {==}))

def hit(+a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), SC.pow2(depth)) == True{} : Bool}) -> {U32.is_eq(U32.from_nat(U32.to_nat(i)), i) == True{} : Bool}:
  Equal.trans(Bool, U32.is_eq(U32.from_nat(U32.to_nat(i)), i), Nat.is_eq(U32.to_nat(i), U32.to_nat(i)), True{}, IT.ueq(U32.to_nat(i), i, depth, hd, IT.lt_head(U32.to_nat(i), b, SC.pow2(depth), TLa.alllt_r(a, Con{U32.to_nat(i), b}, SC.pow2(depth), hl))), N.is_eq_refl(U32.to_nat(i)))

def ib_eq(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +it: E.Item<T>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}, +hnd: {ST.nodup(SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}) -> {DS.ins_before(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i, it) == SC.append(E.Item<T>, ST.items(T, xs, a), Con{it, ST.items(T, xs, Con{U32.to_nat(i), b})}) : List<&2, E.Item<T>>}:
  +n = U32.to_nat(i)
  +hbb = AL.alive_app_r(T, xs, a, Con{n, b}, ha)
  +hyn = L.and_left(ST.is_some(T, ST.vat(T, xs, n)), AL.alive(T, xs, b), hbb)
  +vn = AL.val_of(T, ST.vat(T, xs, n), hyn)
  +eit = AL.itm_some(T, ST.vat(T, xs, n), n, ST.items(T, xs, b), hyn)
  +e3 = L.subst(List<&2, E.Item<T>>, z => {DS.ins_before(T, z, i, it) == Con{it, z} : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, ST.items(T, xs, Con{n, b}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{n, b}), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, eit),
    ib_found(T, n, vn, ST.items(T, xs, b), i, it, hit(a, b, i, depth, hd, hl)))
  Equal.trans(List<&2, E.Item<T>>, DS.ins_before(T, ST.items(T, xs, SC.append(Nat, a, Con{n, b})), i, it), DS.ins_before(T, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), i, it), SC.append(E.Item<T>, ST.items(T, xs, a), Con{it, ST.items(T, xs, Con{n, b})}),
    Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => DS.ins_before(T, z, i, it), ST.items(T, xs, SC.append(Nat, a, Con{n, b})), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), AL.items_app(T, xs, a, Con{n, b})),
    Equal.trans(List<&2, E.Item<T>>, DS.ins_before(T, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), i, it), SC.append(E.Item<T>, ST.items(T, xs, a), DS.ins_before(T, ST.items(T, xs, Con{n, b}), i, it)), SC.append(E.Item<T>, ST.items(T, xs, a), Con{it, ST.items(T, xs, Con{n, b})}),
      ib_skip(T, xs, a, ST.items(T, xs, Con{n, b}), i, it, depth, hd, TLa.alllt_l(a, Con{n, b}, SC.pow2(depth), hl), AL.alive_app(T, xs, a, Con{n, b}, ha), n_notin(a, n, b, hnd)),
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a), z), DS.ins_before(T, ST.items(T, xs, Con{n, b}), i, it), Con{it, ST.items(T, xs, Con{n, b})}, e3)))

def ia_eq(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +it: E.Item<T>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}, +hnd: {ST.nodup(SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}) -> {DS.ins_after(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i, it) == SC.append(E.Item<T>, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), Nil{}})), Con{it, ST.items(T, xs, b)}) : List<&2, E.Item<T>>}:
  +n = U32.to_nat(i)
  +hbb = AL.alive_app_r(T, xs, a, Con{n, b}, ha)
  +hyn = L.and_left(ST.is_some(T, ST.vat(T, xs, n)), AL.alive(T, xs, b), hbb)
  +vn = AL.val_of(T, ST.vat(T, xs, n), hyn)
  +eit = AL.itm_some(T, ST.vat(T, xs, n), n, ST.items(T, xs, b), hyn)
  +eone = AL.itm_some(T, ST.vat(T, xs, n), n, Nil{}, hyn)
  +e3 = L.subst(List<&2, E.Item<T>>, z => {DS.ins_after(T, z, i, it) == Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}} : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, ST.items(T, xs, Con{n, b}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{n, b}), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, eit),
    ia_found(T, n, vn, ST.items(T, xs, b), i, it, hit(a, b, i, depth, hd, hl)))
  +lhs = Equal.trans(List<&2, E.Item<T>>, DS.ins_after(T, ST.items(T, xs, SC.append(Nat, a, Con{n, b})), i, it), DS.ins_after(T, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), i, it), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}),
    Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => DS.ins_after(T, z, i, it), ST.items(T, xs, SC.append(Nat, a, Con{n, b})), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), AL.items_app(T, xs, a, Con{n, b})),
    Equal.trans(List<&2, E.Item<T>>, DS.ins_after(T, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), i, it), SC.append(E.Item<T>, ST.items(T, xs, a), DS.ins_after(T, ST.items(T, xs, Con{n, b}), i, it)), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}),
      ia_skip(T, xs, a, ST.items(T, xs, Con{n, b}), i, it, depth, hd, TLa.alllt_l(a, Con{n, b}, SC.pow2(depth), hl), AL.alive_app(T, xs, a, Con{n, b}, ha), n_notin(a, n, b, hnd)),
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a), z), DS.ins_after(T, ST.items(T, xs, Con{n, b}), i, it), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}, e3)))
  +rhs = Equal.trans(List<&2, E.Item<T>>, SC.append(E.Item<T>, ST.items(T, xs, SC.append(Nat, a, Con{n, Nil{}})), Con{it, ST.items(T, xs, b)}), SC.append(E.Item<T>, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, Nil{}})), Con{it, ST.items(T, xs, b)}), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}),
    Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, z, Con{it, ST.items(T, xs, b)}), ST.items(T, xs, SC.append(Nat, a, Con{n, Nil{}})), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, Nil{}})), AL.items_app(T, xs, a, Con{n, Nil{}})),
    Equal.trans(List<&2, E.Item<T>>, SC.append(E.Item<T>, SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, Nil{}})), Con{it, ST.items(T, xs, b)}), SC.append(E.Item<T>, ST.items(T, xs, a), SC.append(E.Item<T>, ST.items(T, xs, Con{n, Nil{}}), Con{it, ST.items(T, xs, b)})), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}),
      LL.append_assoc(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, Nil{}}), Con{it, ST.items(T, xs, b)}),
      Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a), SC.append(E.Item<T>, z, Con{it, ST.items(T, xs, b)})), ST.items(T, xs, Con{n, Nil{}}), Con{E.Item{U32.from_nat(n), vn}, Nil{}}, eone)))
  Equal.trans(List<&2, E.Item<T>>, DS.ins_after(T, ST.items(T, xs, SC.append(Nat, a, Con{n, b})), i, it), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}), SC.append(E.Item<T>, ST.items(T, xs, SC.append(Nat, a, Con{n, Nil{}})), Con{it, ST.items(T, xs, b)}),
    lhs, Equal.sym(List<&2, E.Item<T>>, SC.append(E.Item<T>, ST.items(T, xs, SC.append(Nat, a, Con{n, Nil{}})), Con{it, ST.items(T, xs, b)}), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, Con{it, ST.items(T, xs, b)}}), rhs))

# ---- head, tail and count after the splice ----

def hd_ins(+x: List<&2, Nat>, +f: Nat, +y: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(x, SC.pow2(depth)) == True{} : Bool}) -> {D.pick_end(U32.is_eq(LK.lastl(x, D.nil()), D.nil()), ST.ln(f), ST.hd(SC.append(Nat, x, y))) == ST.hd(SC.append(Nat, x, Con{f, y})) : U32}:
  match x:
    case Nil{}:
      {==}
    case Con{+x0, +t}:
      L.subst(Bool, z => {D.pick_end(z, ST.ln(f), ST.ln(x0)) == ST.ln(x0) : U32}, False{}, U32.is_eq(ST.ln(ST.lst_or(t, x0)), D.nil()), Equal.sym(Bool, U32.is_eq(ST.ln(ST.lst_or(t, x0)), D.nil()), False{}, F.ln_ne_nil(ST.lst_or(t, x0), depth, hd, RT.lst_lt(t, x0, SC.pow2(depth), hl))), {==})

def tl_ins(+x: List<&2, Nat>, +f: Nat, +y: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(y, SC.pow2(depth)) == True{} : Bool}) -> {D.pick_end(U32.is_eq(ST.hd_or(y, D.nil()), D.nil()), ST.ln(f), ST.lst(SC.append(Nat, x, y))) == ST.lst(SC.append(Nat, x, Con{f, y})) : U32}:
  match y:
    case Nil{}:
      Equal.sym(U32, ST.lst(SC.append(Nat, x, Con{f, Nil{}})), ST.ln(f), RF.lst_app_cons(x, f, Nil{}))
    case Con{+y0, +r}:
      L.subst(Bool, z => {D.pick_end(z, ST.ln(f), ST.lst(SC.append(Nat, x, Con{y0, r}))) == ST.lst(SC.append(Nat, x, Con{f, Con{y0, r}})) : U32}, False{}, U32.is_eq(ST.ln(y0), D.nil()), Equal.sym(Bool, U32.is_eq(ST.ln(y0), D.nil()), False{}, F.ln_ne_nil(y0, depth, hd, IT.lt_head(y0, r, SC.pow2(depth), hl))),
        Equal.trans(U32, ST.lst(SC.append(Nat, x, Con{y0, r})), ST.ln(ST.lst_or(r, y0)), ST.lst(SC.append(Nat, x, Con{f, Con{y0, r}})), RF.lst_app_cons(x, y0, r), Equal.sym(U32, ST.lst(SC.append(Nat, x, Con{f, Con{y0, r}})), ST.ln(ST.lst_or(Con{y0, r}, f)), RF.lst_app_cons(x, f, Con{y0, r}))))

def cnt_ins(+x: List<&2, Nat>, +f: Nat, +y: List<&2, Nat>) -> {1n+SC.length(Nat, SC.append(Nat, x, y)) == SC.length(Nat, SC.append(Nat, x, Con{f, y})) : Nat}:
  match x:
    case Nil{}:
      {==}
    case Con{+x0, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, 1n+SC.length(Nat, SC.append(Nat, t, y)), SC.length(Nat, SC.append(Nat, t, Con{f, y})), cnt_ins(t, f, y))
