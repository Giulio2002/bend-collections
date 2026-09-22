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

# Facts about cutting the id n out of the order a ++ [n] ++ b.

# ---- the value arena ----

def lmem_cut(+q: Nat, +a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +hq: {Nat.is_eq(n, q) == False{} : Bool}) -> {ST.lmem(q, SC.append(Nat, a, b)) == ST.lmem(q, SC.append(Nat, a, Con{n, b})) : Bool}:
  Equal.trans(Bool, ST.lmem(q, SC.append(Nat, a, b)), Bool.or(ST.lmem(q, a), ST.lmem(q, b)), ST.lmem(q, SC.append(Nat, a, Con{n, b})),
    SP.lmem_app(q, a, b),
    Equal.sym(Bool, ST.lmem(q, SC.append(Nat, a, Con{n, b})), Bool.or(ST.lmem(q, a), ST.lmem(q, b)),
      Equal.trans(Bool, ST.lmem(q, SC.append(Nat, a, Con{n, b})), Bool.or(ST.lmem(q, a), Bool.or(Nat.is_eq(n, q), ST.lmem(q, b))), Bool.or(ST.lmem(q, a), ST.lmem(q, b)),
        SP.lmem_app(q, a, Con{n, b}),
        Equal.cong(Bool, Bool, z => Bool.or(ST.lmem(q, a), Bool.or(z, ST.lmem(q, b))), Nat.is_eq(n, q), False{}, hq))))

def lvd_pos(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +p: Nat, +hna: {ST.lmem(n, a) == False{} : Bool}, +hnb: {ST.lmem(n, b) == False{} : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, +hold: {ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, a, Con{n, b}))) == True{} : Bool}, c: Bool, +ec: {Nat.is_eq(n, p) == c : Bool}) -> {ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), p)), ST.lmem(p, SC.append(Nat, a, b))) == True{} : Bool}:
  match c:
    case True{}:
      +en = IT.eq_nat_true(n, p, ec)
      +hab = Equal.trans(Bool, ST.lmem(n, SC.append(Nat, a, b)), Bool.or(ST.lmem(n, a), ST.lmem(n, b)), False{}, SP.lmem_app(n, a, b), SP.or_ff(ST.lmem(n, a), ST.lmem(n, b), hna, hnb))
      L.subst(Nat, z => {ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), z)), ST.lmem(z, SC.append(Nat, a, b))) == True{} : Bool}, n, p, en,
        L.subst(Maybe<&2, T>, m => {ST.beq(ST.is_some(T, m), ST.lmem(n, SC.append(Nat, a, b))) == True{} : Bool}, None{}, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), n), Equal.sym(Maybe<&2, T>, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), n), None{}, LK.vat_same(T, xs, n, None{}, hn)),
          L.subst(Bool, z => {ST.beq(False{}, z) == True{} : Bool}, False{}, ST.lmem(n, SC.append(Nat, a, b)), Equal.sym(Bool, ST.lmem(n, SC.append(Nat, a, b)), False{}, hab), {==})))
    case False{}:
      L.subst(Maybe<&2, T>, m => {ST.beq(ST.is_some(T, m), ST.lmem(p, SC.append(Nat, a, b))) == True{} : Bool}, ST.vat(T, xs, p), ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), p), Equal.sym(Maybe<&2, T>, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), p), ST.vat(T, xs, p), LK.vat_other(T, xs, n, None{}, p, ec)),
        L.subst(Bool, z => {ST.beq(ST.is_some(T, ST.vat(T, xs, p)), z) == True{} : Bool}, ST.lmem(p, SC.append(Nat, a, Con{n, b})), ST.lmem(p, SC.append(Nat, a, b)), Equal.sym(Bool, ST.lmem(p, SC.append(Nat, a, b)), ST.lmem(p, SC.append(Nat, a, Con{n, b})), lmem_cut(p, a, n, b, ec)), hold))

def lv_del(-T: Data, k: Nat, +xs: List<&2, Maybe<&2, T>>, +p: Nat, +a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +hna: {ST.lmem(n, a) == False{} : Bool}, +hnb: {ST.lmem(n, b) == False{} : Bool}, +hn: {Nat.is_lt(n, SC.length(Maybe<&2, T>, xs)) == True{} : Bool}, +h: {ST.lv(T, k, xs, p, SC.append(Nat, a, Con{n, b})) == True{} : Bool}) -> {ST.lv(T, k, SC.update(Maybe<&2, T>, xs, n, None{}), p, SC.append(Nat, a, b)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +k1:
      +h1 = L.and_left(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, a, Con{n, b}))), ST.lv(T, k1, xs, 1n+p, SC.append(Nat, a, Con{n, b})), h)
      +h2 = L.and_right(ST.beq(ST.is_some(T, ST.vat(T, xs, p)), ST.lmem(p, SC.append(Nat, a, Con{n, b}))), ST.lv(T, k1, xs, 1n+p, SC.append(Nat, a, Con{n, b})), h)
      L.and_intro(ST.beq(ST.is_some(T, ST.vat(T, SC.update(Maybe<&2, T>, xs, n, None{}), p)), ST.lmem(p, SC.append(Nat, a, b))), ST.lv(T, k1, SC.update(Maybe<&2, T>, xs, n, None{}), 1n+p, SC.append(Nat, a, b)),
        lvd_pos(T, xs, a, n, b, p, hna, hnb, hn, h1, Nat.is_eq(n, p), {==}),
        lv_del(T, k1, xs, 1n+p, a, n, b, hna, hnb, hn, h2))

# ---- the model ----

def del_c(-T: Data, +xs: List<&2, Maybe<&2, T>>, +x: Nat, +t: List<&2, Nat>, +r: List<&2, E.Item<T>>, +i: U32, +v: T, +hne: {U32.is_eq(U32.from_nat(x), i) == False{} : Bool}) -> {DS.del(T, Con{E.Item{U32.from_nat(x), v}, SC.append(E.Item<T>, ST.items(T, xs, t), r)}, i) == Con{E.Item{U32.from_nat(x), v}, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i)} : List<&2, E.Item<T>>}:
  L.subst(Bool, b => {DS.pick(T, b, SC.append(E.Item<T>, ST.items(T, xs, t), r), Con{E.Item{U32.from_nat(x), v}, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i)}) == Con{E.Item{U32.from_nat(x), v}, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i)} : List<&2, E.Item<T>>}, False{}, U32.is_eq(U32.from_nat(x), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(x), i), False{}, hne), {==})

# del skips the items of a when i is not among its ids.
def del_skip(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +r: List<&2, E.Item<T>>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, a) == True{} : Bool}, +hni: {ST.lmem(U32.to_nat(i), a) == False{} : Bool}) -> {DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, a), r), i) == SC.append(E.Item<T>, ST.items(T, xs, a), DS.del(T, r, i)) : List<&2, E.Item<T>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hy = L.and_left(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha)
      +vx = AL.val_of(T, ST.vat(T, xs, x), hy)
      +hne0 = LK.or_false_l(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)
      +hne = Equal.trans(Bool, U32.is_eq(U32.from_nat(x), i), Nat.is_eq(x, U32.to_nat(i)), False{}, IT.ueq(x, i, depth, hd, IT.lt_head(x, t, SC.pow2(depth), hl)), hne0)
      +eit = AL.itm_some(T, ST.vat(T, xs, x), x, ST.items(T, xs, t), hy)
      L.subst(List<&2, E.Item<T>>, z => {DS.del(T, SC.append(E.Item<T>, z, r), i) == SC.append(E.Item<T>, z, DS.del(T, r, i)) : List<&2, E.Item<T>>}, Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, ST.items(T, xs, Con{x, t}), Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, Con{x, t}), Con{E.Item{U32.from_nat(x), vx}, ST.items(T, xs, t)}, eit),
        Equal.trans(List<&2, E.Item<T>>, DS.del(T, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), r)}, i), Con{E.Item{U32.from_nat(x), vx}, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i)}, Con{E.Item{U32.from_nat(x), vx}, SC.append(E.Item<T>, ST.items(T, xs, t), DS.del(T, r, i))},
          del_c(T, xs, x, t, r, i, vx, hne),
          LL.cons_cong(E.Item<T>, E.Item{U32.from_nat(x), vx}, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, t), r), i), SC.append(E.Item<T>, ST.items(T, xs, t), DS.del(T, r, i)),
            del_skip(T, xs, t, r, i, depth, hd, IT.lt_tail(x, t, SC.pow2(depth), hl), L.and_right(ST.is_some(T, ST.vat(T, xs, x)), AL.alive(T, xs, t), ha), LK.or_false_r(Nat.is_eq(x, U32.to_nat(i)), ST.lmem(U32.to_nat(i), t), hni)))))

# The model after the cut is the spec's del.
def items_del(-T: Data, +xs: List<&2, Maybe<&2, T>>, +a: List<&2, Nat>, +b: List<&2, Nat>, +i: U32, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(SC.append(Nat, a, Con{U32.to_nat(i), b}), SC.pow2(depth)) == True{} : Bool}, +ha: {AL.alive(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}, +hnd: {ST.nodup(SC.append(Nat, a, Con{U32.to_nat(i), b})) == True{} : Bool}) -> {DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{U32.to_nat(i), b})), i) == ST.items(T, xs, SC.append(Nat, a, b)) : List<&2, E.Item<T>>}:
  +n = U32.to_nat(i)
  +hdisj = SP.nodup_disj(a, Con{n, b}, hnd)
  +hna = SP.disj_mem(a, Con{n, b}, n, hdisj, L.subst(Bool, z => {Bool.or(z, ST.lmem(n, b)) == True{} : Bool}, True{}, Nat.is_eq(n, n), Equal.sym(Bool, Nat.is_eq(n, n), True{}, N.is_eq_refl(n)), {==}))
  +hab = AL.alive_app(T, xs, a, Con{n, b}, ha)
  +hbb = AL.alive_app_r(T, xs, a, Con{n, b}, ha)
  +hyn = L.and_left(ST.is_some(T, ST.vat(T, xs, n)), AL.alive(T, xs, b), hbb)
  +vn = AL.val_of(T, ST.vat(T, xs, n), hyn)
  +hla = TLa.alllt_l(a, Con{n, b}, SC.pow2(depth), hl)
  +e1 = Equal.trans(List<&2, E.Item<T>>, ST.items(T, xs, SC.append(Nat, a, Con{n, b})), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, Con{n, b})), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}),
    AL.items_app(T, xs, a, Con{n, b}),
    Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a), z), ST.items(T, xs, Con{n, b}), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, AL.itm_some(T, ST.vat(T, xs, n), n, ST.items(T, xs, b), hyn)))
  +hnn = Equal.trans(Bool, U32.is_eq(U32.from_nat(n), i), Nat.is_eq(n, U32.to_nat(i)), True{}, IT.ueq(n, i, depth, hd, IT.lt_head(n, b, SC.pow2(depth), TLa.alllt_r(a, Con{n, b}, SC.pow2(depth), hl))), N.is_eq_refl(n))
  +e2 = L.subst(Bool, z => {DS.pick(T, z, ST.items(T, xs, b), Con{E.Item{U32.from_nat(n), vn}, DS.del(T, ST.items(T, xs, b), i)}) == ST.items(T, xs, b) : List<&2, E.Item<T>>}, True{}, U32.is_eq(U32.from_nat(n), i), Equal.sym(Bool, U32.is_eq(U32.from_nat(n), i), True{}, hnn), {==})
  Equal.trans(List<&2, E.Item<T>>, DS.del(T, ST.items(T, xs, SC.append(Nat, a, Con{n, b})), i), DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}), i), ST.items(T, xs, SC.append(Nat, a, b)),
    Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => DS.del(T, z, i), ST.items(T, xs, SC.append(Nat, a, Con{n, b})), SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}), e1),
    Equal.trans(List<&2, E.Item<T>>, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}), i), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, b)), ST.items(T, xs, SC.append(Nat, a, b)),
      Equal.trans(List<&2, E.Item<T>>, DS.del(T, SC.append(E.Item<T>, ST.items(T, xs, a), Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}), i), SC.append(E.Item<T>, ST.items(T, xs, a), DS.del(T, Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, i)), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, b)),
        del_skip(T, xs, a, Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, i, depth, hd, hla, hab, hna),
        Equal.cong(List<&2, E.Item<T>>, List<&2, E.Item<T>>, z => SC.append(E.Item<T>, ST.items(T, xs, a), z), DS.del(T, Con{E.Item{U32.from_nat(n), vn}, ST.items(T, xs, b)}, i), ST.items(T, xs, b), e2)),
      Equal.sym(List<&2, E.Item<T>>, ST.items(T, xs, SC.append(Nat, a, b)), SC.append(E.Item<T>, ST.items(T, xs, a), ST.items(T, xs, b)), AL.items_app(T, xs, a, b))))

# ---- head, tail and count after the cut ----

def hd_or_nil(+b: List<&2, Nat>) -> {ST.hd_or(b, D.nil()) == ST.hd(b) : U32}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      {==}

def hd_cut(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(a, SC.pow2(depth)) == True{} : Bool}) -> {D.pick_end(U32.is_eq(LK.lastl(a, D.nil()), D.nil()), ST.hd_or(b, D.nil()), ST.hd(SC.append(Nat, a, Con{n, b}))) == ST.hd(SC.append(Nat, a, b)) : U32}:
  match a:
    case Nil{}:
      hd_or_nil(b)
    case Con{+x, +t}:
      L.subst(Bool, z => {D.pick_end(z, ST.hd_or(b, D.nil()), ST.ln(x)) == ST.ln(x) : U32}, False{}, U32.is_eq(ST.ln(ST.lst_or(t, x)), D.nil()), Equal.sym(Bool, U32.is_eq(ST.ln(ST.lst_or(t, x)), D.nil()), False{}, F.ln_ne_nil(ST.lst_or(t, x), depth, hd, RT.lst_lt(t, x, SC.pow2(depth), hl))), {==})

def lo_app(+a: List<&2, Nat>, +x: Nat, +y: Nat, +r: List<&2, Nat>) -> {ST.lst_or(SC.append(Nat, a, Con{y, r}), x) == ST.lst_or(r, y) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      lo_app(t, z, y, r)

def lst_app_cons(+a: List<&2, Nat>, +y: Nat, +r: List<&2, Nat>) -> {ST.lst(SC.append(Nat, a, Con{y, r})) == ST.ln(ST.lst_or(r, y)) : U32}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat, U32, z => ST.ln(z), ST.lst_or(SC.append(Nat, t, Con{y, r}), x), ST.lst_or(r, y), lo_app(t, x, y, r))

def tl_cut(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +depth: Nat, +hd: {Nat.is_le(depth, 31n) == True{} : Bool}, +hl: {ST.alllt(b, SC.pow2(depth)) == True{} : Bool}) -> {D.pick_end(U32.is_eq(ST.hd_or(b, D.nil()), D.nil()), LK.lastl(a, D.nil()), ST.lst(SC.append(Nat, a, Con{n, b}))) == ST.lst(SC.append(Nat, a, b)) : U32}:
  match b:
    case Nil{}:
      Equal.trans(U32, LK.lastl(a, D.nil()), ST.lst(a), ST.lst(SC.append(Nat, a, Nil{})), Equal.sym(U32, ST.lst(a), LK.lastl(a, D.nil()), TLa.lst_lastl(a)), Equal.cong(List<&2, Nat>, U32, z => ST.lst(z), a, SC.append(Nat, a, Nil{}), Equal.sym(List<&2, Nat>, SC.append(Nat, a, Nil{}), a, LL.append_nil(Nat, a))))
    case Con{+y, +r}:
      L.subst(Bool, z => {D.pick_end(z, LK.lastl(a, D.nil()), ST.lst(SC.append(Nat, a, Con{n, Con{y, r}}))) == ST.lst(SC.append(Nat, a, Con{y, r})) : U32}, False{}, U32.is_eq(ST.ln(y), D.nil()), Equal.sym(Bool, U32.is_eq(ST.ln(y), D.nil()), False{}, F.ln_ne_nil(y, depth, hd, IT.lt_head(y, r, SC.pow2(depth), hl))),
        Equal.trans(U32, ST.lst(SC.append(Nat, a, Con{n, Con{y, r}})), ST.ln(ST.lst_or(Con{y, r}, n)), ST.lst(SC.append(Nat, a, Con{y, r})), lst_app_cons(a, n, Con{y, r}), Equal.sym(U32, ST.lst(SC.append(Nat, a, Con{y, r})), ST.ln(ST.lst_or(r, y)), lst_app_cons(a, y, r))))

def cnt_cut(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>) -> {Nat.sub(SC.length(Nat, SC.append(Nat, a, Con{n, b})), 1n) == SC.length(Nat, SC.append(Nat, a, b)) : Nat}:
  +la = SC.length(Nat, a)
  +lb = SC.length(Nat, b)
  Equal.trans(Nat, Nat.sub(SC.length(Nat, SC.append(Nat, a, Con{n, b})), 1n), Nat.sub(1n+Nat.add(la, lb), 1n), SC.length(Nat, SC.append(Nat, a, b)),
    Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), SC.length(Nat, SC.append(Nat, a, Con{n, b})), 1n+Nat.add(la, lb), Equal.trans(Nat, SC.length(Nat, SC.append(Nat, a, Con{n, b})), Nat.add(la, 1n+lb), 1n+Nat.add(la, lb), LL.length_append(Nat, a, Con{n, b}), N.add_succ(la, lb))),
    Equal.trans(Nat, Nat.sub(1n+Nat.add(la, lb), 1n), Nat.add(la, lb), SC.length(Nat, SC.append(Nat, a, b)), N.sub_zero(Nat.add(la, lb)), Equal.sym(Nat, SC.length(Nat, SC.append(Nat, a, b)), Nat.add(la, lb), LL.length_append(Nat, a, b))))

# ---- disjointness in both directions ----

def disj_tail(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +h: {SP.disj(a, Con{n, b}) == True{} : Bool}) -> {SP.disj(a, b) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = MU0.not_true(ST.lmem(x, Con{n, b}), L.and_left(Bool.not(ST.lmem(x, Con{n, b})), SP.disj(t, Con{n, b}), h))
      L.and_intro(Bool.not(ST.lmem(x, b)), SP.disj(t, b), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(x, b), Equal.sym(Bool, ST.lmem(x, b), False{}, LK.or_false_r(Nat.is_eq(n, x), ST.lmem(x, b), hx)), {==}),
        disj_tail(t, n, b, L.and_right(Bool.not(ST.lmem(x, Con{n, b})), SP.disj(t, Con{n, b}), h)))

def disj_flip(+a: List<&2, Nat>, +b: List<&2, Nat>, +h: {SP.disj(a, b) == True{} : Bool}) -> {SP.disj(b, a) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hy = SP.disj_mem(a, Con{y, t}, y, h, L.subst(Bool, z => {Bool.or(z, ST.lmem(y, t)) == True{} : Bool}, True{}, Nat.is_eq(y, y), Equal.sym(Bool, Nat.is_eq(y, y), True{}, N.is_eq_refl(y)), {==}))
      L.and_intro(Bool.not(ST.lmem(y, a)), SP.disj(t, a), L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, False{}, ST.lmem(y, a), Equal.sym(Bool, ST.lmem(y, a), False{}, hy), {==}), disj_flip(a, t, disj_tail(a, y, t, h)))

# ---- the links after the cut ----

def lk_parts(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(SC.append(Nat, a, Con{n, b}), D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {Bool.and(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, LK.lastl(a, D.nil()), D.nil(), ps, ns)) == True{} : Bool}:
  L.subst(Bool, z => {z == True{} : Bool}, ST.lk(SC.append(Nat, a, Con{n, b}), D.nil(), D.nil(), ps, ns), Bool.and(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, LK.lastl(a, D.nil()), D.nil(), ps, ns)), LK.lk_app(a, Con{n, b}, D.nil(), D.nil(), ps, ns), h)

def plink(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(SC.append(Nat, a, Con{n, b}), D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {ST.lat(ps, n) == LK.lastl(a, D.nil()) : U32}:
  NB.ueq_true(ST.lat(ps, n), LK.lastl(a, D.nil()), RT.lk1(n, b, LK.lastl(a, D.nil()), D.nil(), ps, ns, L.and_right(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, LK.lastl(a, D.nil()), D.nil(), ps, ns), lk_parts(a, n, b, ps, ns, h))))

def nlink(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(SC.append(Nat, a, Con{n, b}), D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {ST.lat(ns, n) == ST.hd_or(b, D.nil()) : U32}:
  NB.ueq_true(ST.lat(ns, n), ST.hd_or(b, D.nil()), RT.lk2(n, b, LK.lastl(a, D.nil()), D.nil(), ps, ns, L.and_right(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, LK.lastl(a, D.nil()), D.nil(), ps, ns), lk_parts(a, n, b, ps, ns, h))))

def lk_cut(+a: List<&2, Nat>, +n: Nat, +b: List<&2, Nat>, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {ST.nodup(SC.append(Nat, a, Con{n, b})) == True{} : Bool}, +hlp: {ST.alllt(SC.append(Nat, a, Con{n, b}), SC.length(U32, ps)) == True{} : Bool}, +hln: {ST.alllt(SC.append(Nat, a, Con{n, b}), SC.length(U32, ns)) == True{} : Bool}, +h: {ST.lk(SC.append(Nat, a, Con{n, b}), D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {ST.lk(SC.append(Nat, a, b), D.nil(), D.nil(), RT.pupd(ps, b, LK.lastl(a, D.nil())), RT.nupd(ns, a, ST.hd_or(b, D.nil()))) == True{} : Bool}:
  +p = LK.lastl(a, D.nil())
  +q = ST.hd_or(b, D.nil())
  +parts = lk_parts(a, n, b, ps, ns, h)
  +hka = L.and_left(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, p, D.nil(), ps, ns), parts)
  +hkb = RT.lk3(n, b, p, D.nil(), ps, ns, L.and_right(ST.lk(a, D.nil(), ST.ln(n), ps, ns), ST.lk(Con{n, b}, p, D.nil(), ps, ns), parts))
  +hdisj = SP.nodup_disj(a, Con{n, b}, hnd)
  +hnda = SP.nodup_app_l(a, Con{n, b}, hnd)
  +hndb = L.and_right(Bool.not(ST.lmem(n, b)), ST.nodup(b), SP.nodup_app_r(a, Con{n, b}, hnd))
  +hkA = Equal.trans(Bool, ST.lk(a, D.nil(), q, RT.pupd(ps, b, p), RT.nupd(ns, a, q)), ST.lk(a, D.nil(), q, ps, RT.nupd(ns, a, q)), True{},
    RT.lk_frame_pupd(a, D.nil(), q, ps, RT.nupd(ns, a, q), b, p, disj_flip(a, b, disj_tail(a, n, b, hdisj))),
    RT.lk_end(a, D.nil(), ST.ln(n), q, ps, ns, hnda, TLa.alllt_l(a, Con{n, b}, SC.length(U32, ns), hln), hka))
  +hkB = Equal.trans(Bool, ST.lk(b, p, D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q)), ST.lk(b, p, D.nil(), RT.pupd(ps, b, p), ns), True{},
    RT.lk_frame_nupd(b, p, D.nil(), RT.pupd(ps, b, p), ns, a, q, disj_tail(a, n, b, hdisj)),
    RT.lk_start(b, ST.ln(n), p, D.nil(), ps, ns, hndb, IT.lt_tail(n, b, SC.length(U32, ps), TLa.alllt_r(a, Con{n, b}, SC.length(U32, ps), hlp)), hkb))
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.lk(a, D.nil(), q, RT.pupd(ps, b, p), RT.nupd(ns, a, q)), ST.lk(b, p, D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q))), ST.lk(SC.append(Nat, a, b), D.nil(), D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q)),
    Equal.sym(Bool, ST.lk(SC.append(Nat, a, b), D.nil(), D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q)), Bool.and(ST.lk(a, D.nil(), q, RT.pupd(ps, b, p), RT.nupd(ns, a, q)), ST.lk(b, p, D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q))), LK.lk_app(a, b, D.nil(), D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q))),
    L.and_intro(ST.lk(a, D.nil(), q, RT.pupd(ps, b, p), RT.nupd(ns, a, q)), ST.lk(b, p, D.nil(), RT.pupd(ps, b, p), RT.nupd(ns, a, q)), hkA, hkB))
