# Retained proof dependency: history/retired-doubly-linked-list/proofs/dlist/inslk.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../lib/list.bend as LL
import ../../../spec/common.bend as SC
import link_primitives.bend as D
import links_state.bend as ST
import links_links.bend as LK
import links_split.bend as SP
import links_retarget.bend as RT
import links_rmfacts.bend as RF

def lst_ne(+r: List<&2, Nat>, +x0: Nat, +j: Nat, +h: {ST.lmem(j, Con{x0, r}) == False{} : Bool}) -> {Nat.is_eq(ST.lst_or(r, x0), j) == False{} : Bool}:
  match r:
    case Nil{}:
      LK.or_false_l(Nat.is_eq(x0, j), False{}, h)
    case Con{+y, +r2}:
      lst_ne(r2, y, j, LK.or_false_r(Nat.is_eq(x0, j), ST.lmem(j, Con{y, r2}), h))


def lat_pupd_other(+ps: List<&2, U32>, +y: List<&2, Nat>, +v: U32, +j: Nat, +h: {ST.lmem(j, y) == False{} : Bool}) -> {ST.lat(RT.pupd(ps, y, v), j) == ST.lat(ps, j) : U32}:
  match y:
    case Nil{}:
      {==}
    case Con{+y0, +r}:
      LK.lat_other(ps, y0, v, j, LK.or_false_l(Nat.is_eq(y0, j), ST.lmem(j, r), h))


def lat_nupd_other(+ns: List<&2, U32>, +x: List<&2, Nat>, +v: U32, +j: Nat, +h: {ST.lmem(j, x) == False{} : Bool}) -> {ST.lat(RT.nupd(ns, x, v), j) == ST.lat(ns, j) : U32}:
  match x:
    case Nil{}:
      {==}
    case Con{+x0, +r}:
      LK.lat_other(ns, ST.lst_or(r, x0), v, j, lst_ne(r, x0, j, h))


def notin_l(+f: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +h: {ST.lmem(f, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.lmem(f, x) == False{} : Bool}:
  LK.or_false_l(ST.lmem(f, x), ST.lmem(f, y), Equal.trans(Bool, Bool.or(ST.lmem(f, x), ST.lmem(f, y)), ST.lmem(f, SC.append(Nat, x, y)), False{}, Equal.sym(Bool, ST.lmem(f, SC.append(Nat, x, y)), Bool.or(ST.lmem(f, x), ST.lmem(f, y)), SP.lmem_app(f, x, y)), h))


def notin_r(+f: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +h: {ST.lmem(f, SC.append(Nat, x, y)) == False{} : Bool}) -> {ST.lmem(f, y) == False{} : Bool}:
  LK.or_false_r(ST.lmem(f, x), ST.lmem(f, y), Equal.trans(Bool, Bool.or(ST.lmem(f, x), ST.lmem(f, y)), ST.lmem(f, SC.append(Nat, x, y)), False{}, Equal.sym(Bool, ST.lmem(f, SC.append(Nat, x, y)), Bool.or(ST.lmem(f, x), ST.lmem(f, y)), SP.lmem_app(f, x, y)), h))


def alllt_upd(+x: List<&2, Nat>, +ns: List<&2, U32>, +f: Nat, +v: U32, +h: {ST.alllt(x, SC.length(U32, ns)) == True{} : Bool}) -> {ST.alllt(x, SC.length(U32, SC.update(U32, ns, f, v))) == True{} : Bool}:
  L.subst(Nat, z => {ST.alllt(x, z) == True{} : Bool}, SC.length(U32, ns), SC.length(U32, SC.update(U32, ns, f, v)), Equal.sym(Nat, SC.length(U32, SC.update(U32, ns, f, v)), SC.length(U32, ns), LL.length_update(U32, ns, f, v)), h)


def lk_ins(+x: List<&2, Nat>, +y: List<&2, Nat>, +f: Nat, +ps: List<&2, U32>, +ns: List<&2, U32>, +hnd: {ST.nodup(SC.append(Nat, x, y)) == True{} : Bool}, +hf: {ST.lmem(f, SC.append(Nat, x, y)) == False{} : Bool}, +hx: {ST.alllt(x, SC.length(U32, ns)) == True{} : Bool}, +hy: {ST.alllt(y, SC.length(U32, ps)) == True{} : Bool}, +hfp: {Nat.is_lt(f, SC.length(U32, ps)) == True{} : Bool}, +hfn: {Nat.is_lt(f, SC.length(U32, ns)) == True{} : Bool}, +h: {ST.lk(SC.append(Nat, x, y), D.nil(), D.nil(), ps, ns) == True{} : Bool}) -> {ST.lk(SC.append(Nat, x, Con{f, y}), D.nil(), D.nil(), RT.pupd(SC.update(U32, ps, f, LK.lastl(x, D.nil())), y, ST.ln(f)), RT.nupd(SC.update(U32, ns, f, ST.hd_or(y, D.nil())), x, ST.ln(f))) == True{} : Bool}:
  +a = LK.lastl(x, D.nil())
  +b = ST.hd_or(y, D.nil())
  +lf = ST.ln(f)
  +p0 = SC.update(U32, ps, f, a)
  +n0 = SC.update(U32, ns, f, b)
  +pp = RT.pupd(p0, y, lf)
  +nn = RT.nupd(n0, x, lf)
  +parts = L.subst(Bool, z => {z == True{} : Bool}, ST.lk(SC.append(Nat, x, y), D.nil(), D.nil(), ps, ns), Bool.and(ST.lk(x, D.nil(), b, ps, ns), ST.lk(y, a, D.nil(), ps, ns)), LK.lk_app(x, y, D.nil(), D.nil(), ps, ns), h)
  +hka = L.and_left(ST.lk(x, D.nil(), b, ps, ns), ST.lk(y, a, D.nil(), ps, ns), parts)
  +hkb = L.and_right(ST.lk(x, D.nil(), b, ps, ns), ST.lk(y, a, D.nil(), ps, ns), parts)
  +hfx = notin_l(f, x, y, hf)
  +hfy = notin_r(f, x, y, hf)
  +dxy = SP.nodup_disj(x, y, hnd)
  +hkA = Equal.trans(Bool, ST.lk(x, D.nil(), lf, pp, nn), ST.lk(x, D.nil(), lf, p0, nn), True{},
    RT.lk_frame_pupd(x, D.nil(), lf, p0, nn, y, lf, RF.disj_flip(x, y, dxy)),
    Equal.trans(Bool, ST.lk(x, D.nil(), lf, p0, nn), ST.lk(x, D.nil(), lf, ps, nn), True{},
      LK.lk_frame_p(x, D.nil(), lf, ps, nn, f, a, hfx),
      RT.lk_end(x, D.nil(), b, lf, ps, n0, SP.nodup_app_l(x, y, hnd), alllt_upd(x, ns, f, b, hx),
        Equal.trans(Bool, ST.lk(x, D.nil(), b, ps, n0), ST.lk(x, D.nil(), b, ps, ns), True{}, LK.lk_frame_n(x, D.nil(), b, ps, ns, f, b, hfx), hka))))
  +hpf = RT.eq_self(a, ST.lat(pp, f), Equal.trans(U32, ST.lat(pp, f), ST.lat(p0, f), a, lat_pupd_other(p0, y, lf, f, hfy), LK.lat_same(ps, f, a, hfp)))
  +hnf = RT.eq_self(b, ST.lat(nn, f), Equal.trans(U32, ST.lat(nn, f), ST.lat(n0, f), b, lat_nupd_other(n0, x, lf, f, hfx), LK.lat_same(ns, f, b, hfn)))
  +hkY = Equal.trans(Bool, ST.lk(y, lf, D.nil(), pp, nn), ST.lk(y, lf, D.nil(), pp, n0), True{},
    RT.lk_frame_nupd(y, lf, D.nil(), pp, n0, x, lf, dxy),
    Equal.trans(Bool, ST.lk(y, lf, D.nil(), pp, n0), ST.lk(y, lf, D.nil(), pp, ns), True{},
      LK.lk_frame_n(y, lf, D.nil(), pp, ns, f, b, hfy),
      RT.lk_start(y, a, lf, D.nil(), p0, ns, SP.nodup_app_r(x, y, hnd), alllt_upd(y, ps, f, a, hy),
        Equal.trans(Bool, ST.lk(y, a, D.nil(), p0, ns), ST.lk(y, a, D.nil(), ps, ns), True{}, LK.lk_frame_p(y, a, D.nil(), ps, ns, f, a, hfy), hkb))))
  +hkB = RT.and3(U32.is_eq(ST.lat(pp, f), a), U32.is_eq(ST.lat(nn, f), b), ST.lk(y, lf, D.nil(), pp, nn), hpf, hnf, hkY)
  L.subst(Bool, z => {z == True{} : Bool}, Bool.and(ST.lk(x, D.nil(), lf, pp, nn), ST.lk(Con{f, y}, a, D.nil(), pp, nn)), ST.lk(SC.append(Nat, x, Con{f, y}), D.nil(), D.nil(), pp, nn),
    Equal.sym(Bool, ST.lk(SC.append(Nat, x, Con{f, y}), D.nil(), D.nil(), pp, nn), Bool.and(ST.lk(x, D.nil(), lf, pp, nn), ST.lk(Con{f, y}, a, D.nil(), pp, nn)), LK.lk_app(x, Con{f, y}, D.nil(), D.nil(), pp, nn)),
    L.and_intro(ST.lk(x, D.nil(), lf, pp, nn), ST.lk(Con{f, y}, a, D.nil(), pp, nn), hkA, hkB))
