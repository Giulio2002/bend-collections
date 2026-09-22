import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../spec/common.bend as SC
import ../spec/hash_table.bend as S
import ../math/u32div.bend as UD
import ../../src/containers/hash_table.bend as H
import ./keys.bend as K
import ./buckets.bend as B
import ./state.bend as ST

# Lookup in the abstraction: the entries of the buckets, in bucket order.

def nohb_c(+bs: List<&2, B.Bk>, +key: String, +q: Nat, +h: {Bool.and(Bool.not(B.hold(key, B.at(bs, q))), B.nohb(bs, key, q)) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, 1n+q) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, q) == c : Bool}, rec: @hlt: {Nat.is_lt(j, q) == True{} : Bool} -> {Bool.not(B.hold(key, B.at(bs, j))) == True{} : Bool}) -> {Bool.not(B.hold(key, B.at(bs, j))) == True{} : Bool}:
  match c:
    case True{}:
      L.subst(Nat, z => {Bool.not(B.hold(key, B.at(bs, z))) == True{} : Bool}, q, j, Equal.sym(Nat, j, q, N.eq_from_is_eq(j, q, hc)), L.and_left(Bool.not(B.hold(key, B.at(bs, q))), B.nohb(bs, key, q), h))
    case False{}:
      rec(N.lt_or_eq(j, q, N.lt_succ_le(j, q, hj), hc))

def nohb_inst(+bs: List<&2, B.Bk>, +key: String, +m: Nat, +h: {B.nohb(bs, key, m) == True{} : Bool}, +j: Nat, +hj: {Nat.is_lt(j, m) == True{} : Bool}) -> {Bool.not(B.hold(key, B.at(bs, j))) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Bool.not(B.hold(key, B.at(bs, j))) == True{} : Bool}, N.lt_zero_absurd(j, hj))
    case 1n+q:
      nohb_c(bs, key, q, h, j, hj, Nat.is_eq(j, q), {==}, hlt => nohb_inst(bs, key, q, L.and_right(Bool.not(B.hold(key, B.at(bs, q))), B.nohb(bs, key, q), h), j, hlt))

# bucket b (at index i, i above x) holds key, which bucket x also holds: impossible
def uq_clash(+bs: List<&2, B.Bk>, +key: String, +i: Nat, +x: Nat, +hxi: {Nat.is_lt(x, i) == True{} : Bool}, +b: B.Bk, +hu: {B.uq_b(bs, i, b) == True{} : Bool}, +hb: {B.hold(key, b) == True{} : Bool}, +hx: {B.hold(key, B.at(bs, x)) == True{} : Bool}) -> Empty:
  match b:
    case B.BE{}:
      L.false_true(hb)
    case B.BF{w, +l, +k}:
      +nb = L.and_left(B.nohb(bs, k, i), B.nolb(bs, l, i), hu)
      +nx = nohb_inst(bs, k, i, nb, x, hxi)
      +ek = K.str_eq_of(k, key, hb)
      +hx2 = L.subst(String, z => {B.hold(z, B.at(bs, x)) == True{} : Bool}, key, k, Equal.sym(String, k, key, ek), hx)
      L.false_true(L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, B.hold(k, B.at(bs, x)), True{}, hx2, nx))

def other_lt(+bs: List<&2, B.Bk>, +n: Nat, +key: String, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +x: Nat, +hx: {Nat.is_lt(x, n) == True{} : Bool}, +hne: {Nat.is_eq(x, i) == False{} : Bool}, +hkx: {B.hold(key, B.at(bs, x)) == True{} : Bool}, +b: Bool, +hb: {Nat.is_lt(x, i) == b : Bool}) -> Empty:
  match b:
    case True{}:
      uq_clash(bs, key, i, x, hb, B.at(bs, i), B.all_inst(B.PUniq{bs}, n, huq, i, hi), hki, hkx)
    case False{}:
      +hix = N.lt_or_eq(i, x, N.not_lt_le(x, i, hb), N.is_eq_sym_false(x, i, hne))
      uq_clash(bs, key, x, i, hix, B.at(bs, x), B.all_inst(B.PUniq{bs}, n, huq, x, hx), hkx, hki)

def other_c(+bs: List<&2, B.Bk>, +n: Nat, +key: String, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +x: Nat, +hx: {Nat.is_lt(x, n) == True{} : Bool}, +hne: {Nat.is_eq(x, i) == False{} : Bool}, +c: Bool, +hc: {B.hold(key, B.at(bs, x)) == c : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, other_lt(bs, n, key, huq, i, hi, hki, x, hx, hne, hc, Nat.is_lt(x, i), {==}))

# THEOREM: if bucket i holds key, no other bucket does
def other(+bs: List<&2, B.Bk>, +n: Nat, +key: String, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +x: Nat, +hx: {Nat.is_lt(x, n) == True{} : Bool}, +hne: {Nat.is_eq(x, i) == False{} : Bool}) -> {Bool.not(B.hold(key, B.at(bs, x))) == True{} : Bool}:
  L.subst(Bool, c => {Bool.not(c) == True{} : Bool}, B.hold(key, B.at(bs, x)), B.hold(key, B.at(bs, x)), {==}, other_c(bs, n, key, huq, i, hi, hki, x, hx, hne, B.hold(key, B.at(bs, x)), {==}))

# ---- lookup over the entries of a range of buckets ----

def lk_skip_m(~V: Data, +k: String, +key: String, +m: Maybe<&2, V>, +r: List<&2, S.Entry<V>>, +h: {S.str_eq(k, key) == False{} : Bool}) -> {S.lookup(~V, SC.append(S.Entry<V>, ST.ent_m(~V, k, m), r), key) == S.lookup(~V, r, key) : Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      L.subst(Bool, c => {Bool.pick(Maybe<&2, V>, c, Some{v}, S.lookup(~V, r, key)) == S.lookup(~V, r, key) : Maybe<&2, V>}, False{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), False{}, h), {==})

# a bucket not holding key adds nothing to its lookup
def lk_skip(~V: Data, +b: B.Bk, +vsl: List<&2, Maybe<&2, V>>, +key: String, +r: List<&2, S.Entry<V>>, +h: {Bool.not(B.hold(key, b)) == True{} : Bool}) -> {S.lookup(~V, SC.append(S.Entry<V>, ST.ent(~V, b, vsl), r), key) == S.lookup(~V, r, key) : Maybe<&2, V>}:
  match b:
    case B.BE{}:
      {==}
    case B.BF{w, +l, +k}:
      lk_skip_m(~V, k, key, ST.nthm(~V, vsl, UD.v(H.slot(l))), r, K.not_true_eq(S.str_eq(k, key), h))

def lk_take_m(~V: Data, +k: String, +key: String, +m: Maybe<&2, V>, +r: List<&2, S.Entry<V>>, +h: {S.str_eq(k, key) == True{} : Bool}, +hr: {S.lookup(~V, r, key) == None{} : Maybe<&2, V>}) -> {S.lookup(~V, SC.append(S.Entry<V>, ST.ent_m(~V, k, m), r), key) == m : Maybe<&2, V>}:
  match m:
    case None{}:
      hr
    case Some{+v}:
      L.subst(Bool, c => {Bool.pick(Maybe<&2, V>, c, Some{v}, S.lookup(~V, r, key)) == Some{v} : Maybe<&2, V>}, True{}, S.str_eq(k, key), Equal.sym(Bool, S.str_eq(k, key), True{}, h), {==})

# the bucket holding key decides its lookup
def lk_take(~V: Data, +b: B.Bk, +vsl: List<&2, Maybe<&2, V>>, +key: String, +r: List<&2, S.Entry<V>>, +h: {B.hold(key, b) == True{} : Bool}, +hr: {S.lookup(~V, r, key) == None{} : Maybe<&2, V>}) -> {S.lookup(~V, SC.append(S.Entry<V>, ST.ent(~V, b, vsl), r), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(b)))) : Maybe<&2, V>}:
  match b:
    case B.BE{}:
      Empty.absurd({S.lookup(~V, SC.append(S.Entry<V>, ST.ent(~V, B.BE{}, vsl), r), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.BE{})))) : Maybe<&2, V>}, L.false_true(h))
    case B.BF{w, +l, +k}:
      lk_take_m(~V, k, key, ST.nthm(~V, vsl, UD.v(H.slot(l))), r, h, hr)

# no bucket in j .. j + m - 1 holds key
def nob(+bs: List<&2, B.Bk>, +key: String, +m: Nat, +j: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.not(B.hold(key, B.at(bs, j))), nob(bs, key, p, 1n+j))

def lk_nob(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +key: String, +m: Nat, +j: Nat, +h: {nob(bs, key, m, j) == True{} : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, vsl, m, j), key) == None{} : Maybe<&2, V>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, V>, S.lookup(~V, SC.append(S.Entry<V>, ST.ent(~V, B.at(bs, j), vsl), ST.absm(~V, bs, vsl, p, 1n+j)), key), S.lookup(~V, ST.absm(~V, bs, vsl, p, 1n+j), key), None{},
        lk_skip(~V, B.at(bs, j), vsl, key, ST.absm(~V, bs, vsl, p, 1n+j), L.and_left(Bool.not(B.hold(key, B.at(bs, j))), nob(bs, key, p, 1n+j), h)),
        lk_nob(~V, bs, vsl, key, p, 1n+j, L.and_right(Bool.not(B.hold(key, B.at(bs, j))), nob(bs, key, p, 1n+j), h)))

def nob_pno(+bs: List<&2, B.Bk>, +key: String, +n: Nat, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}, +m: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, m), n) == True{} : Bool}) -> {nob(bs, key, m, j) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hjm2 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hjm)
      +hj = N.lt_le_trans(j, 1n+Nat.add(j, p), n, N.le_lt_succ(j, Nat.add(j, p), N.le_add_right(j, p)), hjm2)
      L.and_intro(Bool.not(B.hold(key, B.at(bs, j))), nob(bs, key, p, 1n+j), B.all_inst(B.PNo{bs, key}, n, hno, j, hj), nob_pno(bs, key, n, hno, p, 1n+j, hjm2))

# the buckets past the one holding key do not hold it
def nob_past(+bs: List<&2, B.Bk>, +n: Nat, +key: String, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +m: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, m), n) == True{} : Bool}, +hij: {Nat.is_lt(i, j) == True{} : Bool}) -> {nob(bs, key, m, j) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +hjm2 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hjm)
      +hj = N.lt_le_trans(j, 1n+Nat.add(j, p), n, N.le_lt_succ(j, Nat.add(j, p), N.le_add_right(j, p)), hjm2)
      +hne = N.is_eq_sym_false(i, j, N.is_eq_lt(i, j, hij))
      L.and_intro(Bool.not(B.hold(key, B.at(bs, j))), nob(bs, key, p, 1n+j), other(bs, n, key, huq, i, hi, hki, j, hj, hne), nob_past(bs, n, key, huq, i, hi, hki, p, 1n+j, hjm2, N.lt_trans(i, j, 1n+j, hij, N.lt_succ(j))))

def lk_hit_c(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +key: String, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +p: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, 1n+p), n) == True{} : Bool}, +hji: {Nat.is_le(j, i) == True{} : Bool}, +c: Bool, +hc: {Nat.is_eq(j, i) == c : Bool}, rec: @hji2: {Nat.is_le(1n+j, i) == True{} : Bool} -> {S.lookup(~V, ST.absm(~V, bs, vsl, p, 1n+j), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))) : Maybe<&2, V>}) -> {S.lookup(~V, ST.absm(~V, bs, vsl, 1n+p, j), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))) : Maybe<&2, V>}:
  match c:
    case True{}:
      +eji = N.eq_from_is_eq(j, i, hc)
      +hkj = L.subst(Nat, z => {B.hold(key, B.at(bs, z)) == True{} : Bool}, i, j, Equal.sym(Nat, j, i, eji), hki)
      +hjm2 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hjm)
      +hr = lk_nob(~V, bs, vsl, key, p, 1n+j, nob_past(bs, n, key, huq, i, hi, hki, p, 1n+j, hjm2, L.subst(Nat, z => {Nat.is_lt(z, 1n+j) == True{} : Bool}, j, i, eji, N.lt_succ(j))))
      L.subst(Nat, z => {S.lookup(~V, ST.absm(~V, bs, vsl, 1n+p, j), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, z))))) : Maybe<&2, V>}, j, i, eji, lk_take(~V, B.at(bs, j), vsl, key, ST.absm(~V, bs, vsl, p, 1n+j), hkj, hr))
    case False{}:
      +hjm2 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hjm)
      +hj = N.lt_le_trans(j, 1n+Nat.add(j, p), n, N.le_lt_succ(j, Nat.add(j, p), N.le_add_right(j, p)), hjm2)
      +hlt = N.lt_or_eq(j, i, hji, hc)
      Equal.trans(Maybe<&2, V>, S.lookup(~V, SC.append(S.Entry<V>, ST.ent(~V, B.at(bs, j), vsl), ST.absm(~V, bs, vsl, p, 1n+j)), key), S.lookup(~V, ST.absm(~V, bs, vsl, p, 1n+j), key), ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))),
        lk_skip(~V, B.at(bs, j), vsl, key, ST.absm(~V, bs, vsl, p, 1n+j), other(bs, n, key, huq, i, hi, hki, j, hj, hc)),
        rec(N.lt_succ_le_succ(j, i, hlt)))

def lk_hit(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +key: String, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}, +m: Nat, +j: Nat, +hjm: {Nat.is_le(Nat.add(j, m), n) == True{} : Bool}, +hji: {Nat.is_le(j, i) == True{} : Bool}, +him: {Nat.is_lt(i, Nat.add(j, m)) == True{} : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, vsl, m, j), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))) : Maybe<&2, V>}:
  match m:
    case 0n:
      Empty.absurd({S.lookup(~V, ST.absm(~V, bs, vsl, 0n, j), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))) : Maybe<&2, V>}, L.true_false(Equal.trans(Bool, True{}, Nat.is_le(j, i), False{}, Equal.sym(Bool, Nat.is_le(j, i), True{}, hji), N.lt_not_le(i, j, L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(j, 0n), j, N.add_zero(j), him)))))
    case 1n+p:
      +hjm2 = L.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), hjm)
      lk_hit_c(~V, bs, vsl, key, n, huq, i, hi, hki, p, j, hjm, hji, Nat.is_eq(j, i), {==}, hji2 => lk_hit(~V, bs, vsl, key, n, huq, i, hi, hki, p, 1n+j, hjm2, hji2, L.subst(Nat, z => {Nat.is_lt(i, z) == True{} : Bool}, Nat.add(j, 1n+p), 1n+Nat.add(j, p), N.add_succ(j, p), him)))

# THEOREM: with keys unique, the lookup of the key held by bucket i is the
# value in i's slot; with key held nowhere, it is None.
def lookup_hit(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +key: String, +n: Nat, +huq: {B.all_lt(B.PUniq{bs}, n) == True{} : Bool}, +i: Nat, +hi: {Nat.is_lt(i, n) == True{} : Bool}, +hki: {B.hold(key, B.at(bs, i)) == True{} : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), key) == ST.nthm(~V, vsl, UD.v(H.slot(B.lnk(B.at(bs, i))))) : Maybe<&2, V>}:
  lk_hit(~V, bs, vsl, key, n, huq, i, hi, hki, n, 0n, N.le_refl(n), N.zero_le(i), hi)

def lookup_none(~V: Data, +bs: List<&2, B.Bk>, +vsl: List<&2, Maybe<&2, V>>, +key: String, +n: Nat, +hno: {B.all_lt(B.PNo{bs, key}, n) == True{} : Bool}) -> {S.lookup(~V, ST.absm(~V, bs, vsl, n, 0n), key) == None{} : Maybe<&2, V>}:
  lk_nob(~V, bs, vsl, key, n, 0n, nob_pno(bs, key, n, hno, n, 0n, N.le_refl(n)))
