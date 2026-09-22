# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/retarget.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../lib/u32alg.bend as UA
import array_shift.bend as SH
import ../../../spec/common.bend as SC
import links_state.bend as ST
import links_links.bend as LK
import links_items.bend as IT
import links_mu0.bend as MU0
import links_split.bend as SP
import links_alive.bend as AL

def pupd(+ps: List<&2, U32>, b: List<&2, Nat>, +v: U32) -> List<&2, U32>:
  match b:
    case Nil{}:
      ps
    case Con{+y, t}:
      SC.update(U32, ps, y, v)

# the next arena with the last id of a pointing on at v (a empty: unchanged)

def nupd(+ns: List<&2, U32>, a: List<&2, Nat>, +v: U32) -> List<&2, U32>:
  match a:
    case Nil{}:
      ns
    case Con{+x, t}:
      SC.update(U32, ns, ST.lst_or(t, x), v)


def and3(+a: Bool, +b: Bool, +c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  L.and_intro(a, Bool.and(b, c), ha, L.and_intro(b, c, hb, hc))


def lk1(+x: Nat, +t: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(Con{x, t}, pv, e, ps, ns) == True{} : Bool}) -> {U32.is_eq(ST.lat(ps, x), pv) == True{} : Bool}:
  L.and_left(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, ns)), h)


def lk2(+x: Nat, +t: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(Con{x, t}, pv, e, ps, ns) == True{} : Bool}) -> {U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)) == True{} : Bool}:
  L.and_left(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, ns), L.and_right(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, ns)), h))


def lk3(+x: Nat, +t: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +h: {ST.lk(Con{x, t}, pv, e, ps, ns) == True{} : Bool}) -> {ST.lk(t, ST.ln(x), e, ps, ns) == True{} : Bool}:
  L.and_right(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, ns), L.and_right(U32.is_eq(ST.lat(ps, x), pv), Bool.and(U32.is_eq(ST.lat(ns, x), ST.hd_or(t, e)), ST.lk(t, ST.ln(x), e, ps, ns)), h))


def eq_self(+v: U32, +w: U32, +e: {w == v : U32}) -> {U32.is_eq(w, v) == True{} : Bool}:
  L.subst(U32, z => {U32.is_eq(z, v) == True{} : Bool}, v, w, Equal.sym(U32, w, v, e), UA.eq_refl(v))

# The first id of b now points back at pv2.

def lk_start(+b: List<&2, Nat>, +pv: U32, +pv2: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {ST.nodup(b) == True{} : Bool}, +hl: {ST.alllt(b, SC.length(U32, ps)) == True{} : Bool}, +h: {ST.lk(b, pv, e, ps, ns) == True{} : Bool}) -> {ST.lk(b, pv2, e, pupd(ps, b, pv2), ns) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +hyt = MU0.not_true(ST.lmem(y, t), L.and_left(Bool.not(ST.lmem(y, t)), ST.nodup(t), hnd))
      and3(U32.is_eq(ST.lat(SC.update(U32, ps, y, pv2), y), pv2), U32.is_eq(ST.lat(ns, y), ST.hd_or(t, e)), ST.lk(t, ST.ln(y), e, SC.update(U32, ps, y, pv2), ns),
        eq_self(pv2, ST.lat(SC.update(U32, ps, y, pv2), y), LK.lat_same(ps, y, pv2, IT.lt_head(y, t, SC.length(U32, ps), hl))),
        lk2(y, t, pv, e, ps, ns, h),
        Equal.trans(Bool, ST.lk(t, ST.ln(y), e, SC.update(U32, ps, y, pv2), ns), ST.lk(t, ST.ln(y), e, ps, ns), True{}, LK.lk_frame_p(t, ST.ln(y), e, ps, ns, y, pv2, hyt), lk3(y, t, pv, e, ps, ns, h)))


def lst_mem(+r: List<&2, Nat>, +y: Nat) -> {ST.lmem(ST.lst_or(r, y), Con{y, r}) == True{} : Bool}:
  match r:
    case Nil{}:
      L.subst(Bool, b => {Bool.or(b, False{}) == True{} : Bool}, True{}, Nat.is_eq(y, y), Equal.sym(Bool, Nat.is_eq(y, y), True{}, N.is_eq_refl(y)), {==})
    case Con{+z, +q}:
      AL.or_true_r(Nat.is_eq(y, ST.lst_or(q, z)), ST.lmem(ST.lst_or(q, z), Con{z, q}), lst_mem(q, z))


def lst_lt(+r: List<&2, Nat>, +y: Nat, +n: Nat, +h: {ST.alllt(Con{y, r}, n) == True{} : Bool}) -> {Nat.is_lt(ST.lst_or(r, y), n) == True{} : Bool}:
  match r:
    case Nil{}:
      IT.lt_head(y, Nil{}, n, h)
    case Con{+z, +q}:
      lst_lt(q, z, n, IT.lt_tail(y, Con{z, q}, n, h))


def LkeIH(+t: List<&2, Nat>, +x: Nat, +e: U32, +e2: U32, +ps: List<&2, U32>, +ns: List<&2, U32>) -> Type:
  @+hnd: {ST.nodup(t) == True{} : Bool} -> @+hl: {ST.alllt(t, SC.length(U32, ns)) == True{} : Bool} -> @+h: {ST.lk(t, ST.ln(x), e, ps, ns) == True{} : Bool} -> {ST.lk(t, ST.ln(x), e2, ps, nupd(ns, t, e2)) == True{} : Bool}

# The last id of a now points on at e2.


def lke_c(+x: Nat, +t: List<&2, Nat>, +pv: U32, +e: U32, +e2: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {ST.nodup(Con{x, t}) == True{} : Bool}, +hl: {ST.alllt(Con{x, t}, SC.length(U32, ns)) == True{} : Bool}, +h: {ST.lk(Con{x, t}, pv, e, ps, ns) == True{} : Bool}, ih: LkeIH(t, x, e, e2, ps, ns)) -> {ST.lk(Con{x, t}, pv, e2, ps, nupd(ns, Con{x, t}, e2)) == True{} : Bool}:
  match t:
    case Nil{}:
      and3(U32.is_eq(ST.lat(ps, x), pv), U32.is_eq(ST.lat(SC.update(U32, ns, x, e2), x), e2), True{},
        lk1(x, Nil{}, pv, e, ps, ns, h),
        eq_self(e2, ST.lat(SC.update(U32, ns, x, e2), x), LK.lat_same(ns, x, e2, IT.lt_head(x, Nil{}, SC.length(U32, ns), hl))),
        {==})
    case Con{+y, +r}:
      +z = ST.lst_or(r, y)
      +hxt = MU0.not_true(ST.lmem(x, Con{y, r}), L.and_left(Bool.not(ST.lmem(x, Con{y, r})), ST.nodup(Con{y, r}), hnd))
      +hxz = SP.ne_of_mem(x, z, Con{y, r}, hxt, lst_mem(r, y))
      and3(U32.is_eq(ST.lat(ps, x), pv), U32.is_eq(ST.lat(SC.update(U32, ns, z, e2), x), ST.ln(y)), ST.lk(Con{y, r}, ST.ln(x), e2, ps, SC.update(U32, ns, z, e2)),
        lk1(x, Con{y, r}, pv, e, ps, ns, h),
        L.subst(U32, w => {U32.is_eq(w, ST.ln(y)) == True{} : Bool}, ST.lat(ns, x), ST.lat(SC.update(U32, ns, z, e2), x), Equal.sym(U32, ST.lat(SC.update(U32, ns, z, e2), x), ST.lat(ns, x), LK.lat_other(ns, z, e2, x, SH.ne_flip(x, z, hxz))), lk2(x, Con{y, r}, pv, e, ps, ns, h)),
        ih(L.and_right(Bool.not(ST.lmem(x, Con{y, r})), ST.nodup(Con{y, r}), hnd), IT.lt_tail(x, Con{y, r}, SC.length(U32, ns), hl), lk3(x, Con{y, r}, pv, e, ps, ns, h)))


def lk_end(+a: List<&2, Nat>, +pv: U32, +e: U32, +e2: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {ST.nodup(a) == True{} : Bool}, +hl: {ST.alllt(a, SC.length(U32, ns)) == True{} : Bool}, +h: {ST.lk(a, pv, e, ps, ns) == True{} : Bool}) -> {ST.lk(a, pv, e2, ps, nupd(ns, a, e2)) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      lke_c(x, t, pv, e, e2, ps, ns, hnd, hl, h, hn2 => hl2 => h2 => lk_end(t, ST.ln(x), e, e2, ps, ns, hn2, hl2, h2))

# ---- frames for the two retargets ----


def lk_frame_pupd(+xs: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +b: List<&2, Nat>, +v: U32, +h: {SP.disj(b, xs) == True{} : Bool}) -> {ST.lk(xs, pv, e, pupd(ps, b, v), ns) == ST.lk(xs, pv, e, ps, ns) : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      LK.lk_frame_p(xs, pv, e, ps, ns, y, v, MU0.not_true(ST.lmem(y, xs), L.and_left(Bool.not(ST.lmem(y, xs)), SP.disj(t, xs), h)))


def last_notin(+t: List<&2, Nat>, +x: Nat, +ys: List<&2, Nat>, +h: {SP.disj(Con{x, t}, ys) == True{} : Bool}) -> {ST.lmem(ST.lst_or(t, x), ys) == False{} : Bool}:
  match t:
    case Nil{}:
      MU0.not_true(ST.lmem(x, ys), L.and_left(Bool.not(ST.lmem(x, ys)), True{}, h))
    case Con{+y, +r}:
      last_notin(r, y, ys, L.and_right(Bool.not(ST.lmem(x, ys)), SP.disj(Con{y, r}, ys), h))


def lk_frame_nupd(+xs: List<&2, Nat>, +pv: U32, +e: U32, +ps: List<&2, U32>, +ns: List<&2, U32>, +a: List<&2, Nat>, +v: U32, +h: {SP.disj(a, xs) == True{} : Bool}) -> {ST.lk(xs, pv, e, ps, nupd(ns, a, v)) == ST.lk(xs, pv, e, ps, ns) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LK.lk_frame_n(xs, pv, e, ps, ns, ST.lst_or(t, x), v, last_notin(t, x, xs, h))
