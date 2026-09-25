import Base
import ../../lib/logic.bend as L
import ../../lib/nat.bend as N
import ../../../spec/lib/common.bend as SC
import ../../../spec/containers/lru.bend as SP
import ../hash_table/buckets.bend as B
import ../hash_table/insa.bend as IA
import ./state.bend as ST
import ./lists.bend as LS
import ./dll.bend as DL
import ../../lib/nat_list.bend as NL

# Traces of writes to link words (words 0 and 1 of a slot): what a recency
# or free-list operation does to lk, and what it leaves.

type Tr is Data:
  TNil{}
  TW{y: Nat, o: Nat, v: U32, t: Tr}

# t's writes first, then this one
def app(+ll: List<&2, U32>, tr: Tr) -> List<&2, U32>:
  match tr:
    case TNil{}:
      ll
    case TW{+y, +o, +v, +t}:
      SC.update(U32, app(ll, t), ST.off(y, o), v)

# every write is to a link word
def trlo(tr: Tr) -> Bool:
  match tr:
    case TNil{}:
      True{}
    case TW{y, +o, v, +t}:
      Bool.and(Nat.is_lt(o, 2n), trlo(t))

# every written slot is in xs / none is
def trin(tr: Tr, +xs: List<&2, Nat>) -> Bool:
  match tr:
    case TNil{}:
      True{}
    case TW{+y, o, v, +t}:
      Bool.and(NL.memn(y, xs), trin(t, xs))

def trout(tr: Tr, +xs: List<&2, Nat>) -> Bool:
  match tr:
    case TNil{}:
      True{}
    case TW{+y, o, v, +t}:
      Bool.and(Bool.not(NL.memn(y, xs)), trout(t, xs))

# b's writes, then a's
def tcat(a: Tr, b: Tr) -> Tr:
  match a:
    case TNil{}:
      b
    case TW{+y, +o, +v, +t}:
      TW{y, o, v, tcat(t, b)}

def app_cat(+ll: List<&2, U32>, +a: Tr, +b: Tr) -> {app(ll, tcat(a, b)) == app(app(ll, b), a) : List<&2, U32>}:
  match a:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => SC.update(U32, z, ST.off(y, o), v), app(ll, tcat(t, b)), app(app(ll, b), t), app_cat(ll, t, b))


def lo_cat(+a: Tr, +b: Tr, +ha: {trlo(a) == True{} : Bool}, +hb: {trlo(b) == True{} : Bool}) -> {trlo(tcat(a, b)) == True{} : Bool}:
  match a:
    case TNil{}:
      hb
    case TW{+y, +o, +v, +t}:
      L.and_intro(Nat.is_lt(o, 2n), trlo(tcat(t, b)), L.and_left(Nat.is_lt(o, 2n), trlo(t), ha), lo_cat(t, b, L.and_right(Nat.is_lt(o, 2n), trlo(t), ha), hb))

def in_cat(+a: Tr, +b: Tr, +xs: List<&2, Nat>, +ha: {trin(a, xs) == True{} : Bool}, +hb: {trin(b, xs) == True{} : Bool}) -> {trin(tcat(a, b), xs) == True{} : Bool}:
  match a:
    case TNil{}:
      hb
    case TW{+y, +o, +v, +t}:
      L.and_intro(NL.memn(y, xs), trin(tcat(t, b), xs), L.and_left(NL.memn(y, xs), trin(t, xs), ha), in_cat(t, b, xs, L.and_right(NL.memn(y, xs), trin(t, xs), ha), hb))

def lt8(+o: Nat, +h: {Nat.is_lt(o, 2n) == True{} : Bool}) -> {Nat.is_lt(o, 8n) == True{} : Bool}:
  N.lt_le_trans(o, 2n, 8n, h, {==})

# ---- what a trace leaves ----

def len_tr(+ll: List<&2, U32>, +tr: Tr) -> {SC.length(U32, app(ll, tr)) == SC.length(U32, ll) : Nat}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      Equal.trans(Nat, SC.length(U32, SC.update(U32, app(ll, t), ST.off(y, o), v)), SC.length(U32, app(ll, t)), SC.length(U32, ll), IA.len_upd(app(ll, t), ST.off(y, o), v), len_tr(ll, t))

def es_tr(~V: Data, +ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +kl: List<&2, String>, +el: List<&2, Maybe<&2, V>>, +sl: List<&2, Nat>) -> {ST.es(~V, app(ll, tr), kl, el, sl) == ST.es(~V, ll, kl, el, sl) : List<&2, SP.Ent<V>>}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      Equal.trans(List<&2, SP.Ent<V>>, ST.es(~V, SC.update(U32, app(ll, t), ST.off(y, o), v), kl, el, sl), ST.es(~V, app(ll, t), kl, el, sl), ST.es(~V, ll, kl, el, sl), DL.es_fr(~V, app(ll, t), y, o, v, lt8(o, h01), h01, kl, el, sl), es_tr(~V, ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), kl, el, sl))

def has_tr(~V: Data, +ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +bs: List<&2, B.Bk>, +m: Nat, +sl: List<&2, Nat>) -> {ST.hasall(~V, bs, m, app(ll, tr), sl) == ST.hasall(~V, bs, m, ll, sl) : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      Equal.trans(Bool, ST.hasall(~V, bs, m, SC.update(U32, app(ll, t), ST.off(y, o), v), sl), ST.hasall(~V, bs, m, app(ll, t), sl), ST.hasall(~V, bs, m, ll, sl), DL.has_fr(~V, app(ll, t), y, o, v, lt8(o, h01), h01, bs, m, sl), has_tr(~V, ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), bs, m, sl))

def bsl_tr(+ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +bs: List<&2, B.Bk>, +sl: List<&2, Nat>, +m: Nat) -> {ST.bsl(bs, sl, app(ll, tr), m) == ST.bsl(bs, sl, ll, m) : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      Equal.trans(Bool, ST.bsl(bs, sl, SC.update(U32, app(ll, t), ST.off(y, o), v), m), ST.bsl(bs, sl, app(ll, t), m), ST.bsl(bs, sl, ll, m), DL.bsl_fr(app(ll, t), y, o, v, lt8(o, h01), h01, bs, sl, m), bsl_tr(ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), bs, sl, m))

def fll_tr(+ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +fl: List<&2, Nat>, +hout: {trout(tr, fl) == True{} : Bool}) -> {ST.fll(app(ll, tr), fl) == ST.fll(ll, fl) : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      +hy = L.not_true(NL.memn(y, fl), L.and_left(Bool.not(NL.memn(y, fl)), trout(t, fl), hout))
      Equal.trans(Bool, ST.fll(SC.update(U32, app(ll, t), ST.off(y, o), v), fl), ST.fll(app(ll, t), fl), ST.fll(ll, fl), DL.fll_fs(app(ll, t), y, o, v, lt8(o, h01), fl, hy), fll_tr(ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), fl, L.and_right(Bool.not(NL.memn(y, fl)), trout(t, fl), hout)))

def seg_tr(+ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +sl: List<&2, Nat>, +p: U32, +q: U32, +hout: {trout(tr, sl) == True{} : Bool}) -> {ST.seg(app(ll, tr), sl, p, q) == ST.seg(ll, sl, p, q) : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      +hy = L.not_true(NL.memn(y, sl), L.and_left(Bool.not(NL.memn(y, sl)), trout(t, sl), hout))
      Equal.trans(Bool, ST.seg(SC.update(U32, app(ll, t), ST.off(y, o), v), sl, p, q), ST.seg(app(ll, t), sl, p, q), ST.seg(ll, sl, p, q), DL.seg_fs(app(ll, t), y, o, v, lt8(o, h01), sl, p, q, hy), seg_tr(ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), sl, p, q, L.and_right(Bool.not(NL.memn(y, sl)), trout(t, sl), hout)))

# a word of a slot the trace does not write
def lw_tr(+ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +x: Nat, +o2: Nat, +ho2: {Nat.is_lt(o2, 8n) == True{} : Bool}, +hout: {trout(tr, Con{x, Nil{}}) == True{} : Bool}) -> {ST.lw(app(ll, tr), x, o2) == ST.lw(ll, x, o2) : U32}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      +hy = NL.or_ff_l(Nat.is_eq(x, y), False{}, L.not_true(NL.memn(y, Con{x, Nil{}}), L.and_left(Bool.not(NL.memn(y, Con{x, Nil{}})), trout(t, Con{x, Nil{}}), hout)))
      Equal.trans(U32, ST.lw(SC.update(U32, app(ll, t), ST.off(y, o), v), x, o2), ST.lw(app(ll, t), x, o2), ST.lw(ll, x, o2), DL.lw_other(app(ll, t), y, o, v, lt8(o, h01), x, o2, ho2, DL.ne_slot(y, x, o, o2, NL.ne_sym(x, y, hy))), lw_tr(ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), x, o2, ho2, L.and_right(Bool.not(NL.memn(y, Con{x, Nil{}})), trout(t, Con{x, Nil{}}), hout)))

# a data word (2 <= o2) of any slot
def lw_tr_hi(+ll: List<&2, U32>, +tr: Tr, +h: {trlo(tr) == True{} : Bool}, +x: Nat, +o2: Nat, +ho2: {Nat.is_lt(o2, 8n) == True{} : Bool}, +h2: {Nat.is_le(2n, o2) == True{} : Bool}) -> {ST.lw(app(ll, tr), x, o2) == ST.lw(ll, x, o2) : U32}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h01 = L.and_left(Nat.is_lt(o, 2n), trlo(t), h)
      Equal.trans(U32, ST.lw(SC.update(U32, app(ll, t), ST.off(y, o), v), x, o2), ST.lw(app(ll, t), x, o2), ST.lw(ll, x, o2), DL.lw_hi(app(ll, t), y, o, v, lt8(o, h01), h01, x, o2, ho2, h2), lw_tr_hi(ll, t, L.and_right(Nat.is_lt(o, 2n), trlo(t), h), x, o2, ho2, h2))

def not_vac(~V: Data, +y: Nat, +fl: List<&2, Nat>, +fr: Nat, +el: List<&2, Maybe<&2, V>>, +hl: {ST.live(~V, el, y) == True{} : Bool}, +hf: {ST.flok(~V, fl, fr, el) == True{} : Bool}, +c: Bool, +hc: {NL.memn(y, fl) == c : Bool}) -> {Bool.not(c) == True{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +hv = L.and_right(Nat.is_lt(y, fr), Bool.not(ST.live(~V, el, y)), LS.sall_mem(~V, ST.PVac{fr, el}, y, fl, hf, hc))
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, L.false_true(L.subst(Bool, z => {Bool.not(z) == True{} : Bool}, ST.live(~V, el, y), True{}, hl, hv)))

# written slots are live, fl's are vacant: fl is untouched
def out_of_in(~V: Data, +tr: Tr, +sl: List<&2, Nat>, +fl: List<&2, Nat>, +fr: Nat, +el: List<&2, Maybe<&2, V>>, +hin: {trin(tr, sl) == True{} : Bool}, +hs: {ST.slok(~V, sl, fr, el) == True{} : Bool}, +hf: {ST.flok(~V, fl, fr, el) == True{} : Bool}) -> {trout(tr, fl) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +hy = L.and_left(NL.memn(y, sl), trin(t, sl), hin)
      +hl = L.and_right(Nat.is_lt(y, fr), ST.live(~V, el, y), LS.sall_mem(~V, ST.PLive{fr, el}, y, sl, hs, hy))
      L.and_intro(Bool.not(NL.memn(y, fl)), trout(t, fl), not_vac(~V, y, fl, fr, el, hl, hf, NL.memn(y, fl), {==}), out_of_in(~V, t, sl, fl, fr, el, L.and_right(NL.memn(y, sl), trin(t, sl), hin), hs, hf))


# ---- where a trace writes ----


def trin_r(+tr: Tr, +a: List<&2, Nat>, +x: List<&2, Nat>, +h: {trin(tr, x) == True{} : Bool}) -> {trin(tr, SC.append(Nat, a, x)) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      L.and_intro(NL.memn(y, SC.append(Nat, a, x)), trin(t, SC.append(Nat, a, x)), NL.mem_app_r(y, a, x, L.and_left(NL.memn(y, x), trin(t, x), h)), trin_r(t, a, x, L.and_right(NL.memn(y, x), trin(t, x), h)))

def trin_l(+tr: Tr, +a: List<&2, Nat>, +x: List<&2, Nat>, +h: {trin(tr, a) == True{} : Bool}) -> {trin(tr, SC.append(Nat, a, x)) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      L.and_intro(NL.memn(y, SC.append(Nat, a, x)), trin(t, SC.append(Nat, a, x)), NL.mem_app_l(y, a, x, L.and_left(NL.memn(y, a), trin(t, a), h)), trin_l(t, a, x, L.and_right(NL.memn(y, a), trin(t, a), h)))

def trin_cons(+tr: Tr, +s: Nat, +x: List<&2, Nat>, +h: {trin(tr, x) == True{} : Bool}) -> {trin(tr, Con{s, x}) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      L.and_intro(NL.memn(y, Con{s, x}), trin(t, Con{s, x}), NL.or_tr(Nat.is_eq(s, y), NL.memn(y, x), L.and_left(NL.memn(y, x), trin(t, x), h)), trin_cons(t, s, x, L.and_right(NL.memn(y, x), trin(t, x), h)))

# written slots all in a: none in x
def trout_r(+tr: Tr, +a: List<&2, Nat>, +x: List<&2, Nat>, +hin: {trin(tr, a) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, a, x)) == True{} : Bool}) -> {trout(tr, x) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      L.and_intro(Bool.not(NL.memn(y, x)), trout(t, x), NL.not_f(NL.memn(y, x), NL.nd_dj2(a, x, hnd, y, L.and_left(NL.memn(y, a), trin(t, a), hin))), trout_r(t, a, x, L.and_right(NL.memn(y, a), trin(t, a), hin), hnd))

# written slots all in x: none in a
def trout_l(+tr: Tr, +a: List<&2, Nat>, +x: List<&2, Nat>, +hin: {trin(tr, x) == True{} : Bool}, +hnd: {NL.nodupn(SC.append(Nat, a, x)) == True{} : Bool}) -> {trout(tr, a) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      L.and_intro(Bool.not(NL.memn(y, a)), trout(t, a), NL.not_f(NL.memn(y, a), NL.nd_dj(a, x, hnd, y, L.and_left(NL.memn(y, x), trin(t, x), hin))), trout_l(t, a, x, L.and_right(NL.memn(y, x), trin(t, x), hin), hnd))

def trout_tail(+tr: Tr, +s: Nat, +x: List<&2, Nat>, +h: {trout(tr, Con{s, x}) == True{} : Bool}) -> {trout(tr, x) == True{} : Bool}:
  match tr:
    case TNil{}:
      {==}
    case TW{+y, +o, +v, +t}:
      +h0 = L.not_true(NL.memn(y, Con{s, x}), L.and_left(Bool.not(NL.memn(y, Con{s, x})), trout(t, Con{s, x}), h))
      L.and_intro(Bool.not(NL.memn(y, x)), trout(t, x), NL.not_f(NL.memn(y, x), NL.or_ff_r(Nat.is_eq(s, y), NL.memn(y, x), h0)), trout_tail(t, s, x, L.and_right(Bool.not(NL.memn(y, Con{s, x})), trout(t, Con{s, x}), h)))
