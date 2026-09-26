import Base
import ../../../spec/containers/intrusive_doubly_linked_list/model.bend as G
import ./adapter.bend as A
import ../../../spec/containers/intrusive_doubly_linked_list/programs.bend as Spec
import ../../lib/array.bend as AR
import ../../lib/logic.bend as LG
import ../../lib/list.bend as LL
import ../../lib/u32.bend as U
import ../../lib/u32alg.bend as UA
import ../../../spec/lib/common.bend as SC
import ../../../src/containers/intrusive_links.bend as K

# The ready-made link table src/containers/intrusive_links.bend meets the
# adapter laws for EVERY size: 2^dn link slots per direction and 2^dr roots,
# dn, dr < 32. This discharges, for arbitrary sizes, what array_adapter.bend
# does for its four-node example: the exported remove and prepend are the
# model graph's remove and prepend (adapter.remove_refines/prepend_refines).
#
# A model graph is realized by writing its bindings, oldest first, into
# zeroed arrays (0 encodes "no entity"). The premises are exactly what an
# array access needs: the ids written are in range, and a link that is READ
# is not the reserved id 0 (it decodes back to itself).


def ueq(a: U32, b: U32) -> Bool:
  U32.is_eq(a, b)

def tn(+d: Nat, bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>) -> AR.Tree<U32>:
  match bs:
    case Nil{}:
      AR.trep(U32, d, 0)
    case Con{G.Binding{k, v}, rest}:
      AR.upd(U32, d, tn(d, rest), U32.to_nat(k), K.encode(v))

# The graph's frame carries the table's sizes; no operation changes it.
type Depth is Data:
  Depth{nodes: Nat, roots: Nat}

def real_at(ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, f: Depth) -> K.Links:
  match f:
    case Depth{+dn, +dr}:
      K.Links{AR.thaw(U32, tn(dn, ns)), AR.thaw(U32, tn(dn, ps)), AR.thaw(U32, tn(dr, rs))}

def real(g: G.Graph<U32,U32,Depth>) -> K.Links:
  G.Graph{ns, ps, rs, f} = g
  real_at(ns, ps, rs, f)

def dn_of(g: G.Graph<U32,U32,Depth>) -> Nat:
  match g:
    case G.Graph{ns, ps, rs, Depth{dn, dr}}:
      dn

def dr_of(g: G.Graph<U32,U32,Depth>) -> Nat:
  match g:
    case G.Graph{ns, ps, rs, Depth{dn, dr}}:
      dr

def bound(+d: Nat, +x: U32) -> Data:
  {Nat.is_lt(U32.to_nat(x), SC.pow2(d)) == True{} : Bool}

def keys_ok(+d: Nat, bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>) -> Data:
  match bs:
    case Nil{}:
      Unit
    case Con{G.Binding{k, v}, rest}:
      G.both(bound(d, k), keys_ok(d, rest))

def gok(g: G.Graph<U32,U32,Depth>) -> Data:
  match g:
    case G.Graph{ns, ps, rs, Depth{+dn, +dr}}:
      G.both(keys_ok(dn, ns), G.both(keys_ok(dn, ps), keys_ok(dr, rs)))

# A link that is read: absent, or a nonzero id.
def nz(m: Maybe<&2,U32>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{x}:
      {U32.is_eq(x, 0) == False{} : Bool}

# A link that is written through: absent, or an id in range.
def inb(+d: Nat, m: Maybe<&2,U32>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{x}:
      bound(d, x)

# ---- the realized trees ----

def tn_perfect(+d: Nat, +bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>) -> {AR.perfect(U32, d, tn(d, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      AR.trep_perfect(U32, d, 0)
    case Con{G.Binding{+k, +v}, +rest}:
      AR.upd_perfect(U32, d, tn(d, rest), U32.to_nat(k), K.encode(v), tn_perfect(d, rest))

def nth_rep(+m: Nat, +i: Nat, +h: {Nat.is_lt(i, m) == True{} : Bool}) -> {SC.nth(U32, SC.replicate(U32, m, 0), i) == Some{0} : Maybe<&2,U32>}:
  match m i:
    case 0n 0n:
      Empty.absurd({SC.nth(U32, SC.replicate(U32, 0n, 0), 0n) == Some{0} : Maybe<&2,U32>}, LG.false_true(h))
    case 0n 1n+j:
      Empty.absurd({SC.nth(U32, SC.replicate(U32, 0n, 0), 1n+j) == Some{0} : Maybe<&2,U32>}, LG.false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+ +p 1n+ +j:
      nth_rep(p, j, h)

def eq_nat(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b)) : {Cmp.is_eq(_) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}
  {==}

def ne_nat(+a: U32, +b: U32, +e: {U32.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == False{} : Bool}:
  %eq_nat(a, b) : {_ == False{} : Bool}
  e


def lt_len(+d: Nat, +n: U32, +xs: List<&2,U32>, +hl: {SC.length(U32, xs) == SC.pow2(d) : Nat}, +hn: bound(d, n)) -> {Nat.is_lt(U32.to_nat(n), SC.length(U32, xs)) == True{} : Bool}:
  %Equal.sym(Nat, SC.length(U32, xs), SC.pow2(d), hl) : {Nat.is_lt(U32.to_nat(n), _) == True{} : Bool}
  hn

# After a binding (k, v): the slot of n is v when k is n, else unchanged.
def nth_bind(+d: Nat, +k: U32, +v: Maybe<&2,U32>, +rest: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +n: U32, +xs: List<&2,U32>, +hl: {SC.length(U32, xs) == SC.pow2(d) : Nat}, +hn: bound(d, n), +ih: {SC.nth(U32, xs, U32.to_nat(n)) == Some{K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, rest, None{}))} : Maybe<&2,U32>}, +b: Bool, +eb: {U32.is_eq(k, n) == b : Bool}) -> {SC.nth(U32, SC.update(U32, xs, U32.to_nat(k), K.encode(v)), U32.to_nat(n)) == Some{K.encode(G.choose(~Maybe<&2,U32>, b, v, G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, rest, None{})))} : Maybe<&2,U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, k, n, UA.eq_of(k, n, eb)) : {SC.nth(U32, SC.update(U32, xs, U32.to_nat(_), K.encode(v)), U32.to_nat(n)) == Some{K.encode(v)} : Maybe<&2,U32>}
      LL.nth_update_same(U32, xs, U32.to_nat(n), K.encode(v), lt_len(d, n, xs, hl, hn))
    case False{}:
      %Equal.sym(Maybe<&2,U32>, SC.nth(U32, SC.update(U32, xs, U32.to_nat(k), K.encode(v)), U32.to_nat(n)), SC.nth(U32, xs, U32.to_nat(n)), LL.nth_update_other(U32, xs, U32.to_nat(k), U32.to_nat(n), K.encode(v), ne_nat(k, n, eb))) : {_ == Some{K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, rest, None{}))} : Maybe<&2,U32>}
      ih

def tn_len(+d: Nat, +bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>) -> {SC.length(U32, AR.slots(U32, tn(d, bs))) == SC.pow2(d) : Nat}:
  AR.slots_length(U32, d, tn(d, bs), tn_perfect(d, bs))

# Reading slot n of a realized tree gives the model's value for n.
def tn_nth(+d: Nat, +bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +n: U32, +hn: bound(d, n), +hk: keys_ok(d, bs)) -> {SC.nth(U32, AR.slots(U32, tn(d, bs)), U32.to_nat(n)) == Some{K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, bs, None{}))} : Maybe<&2,U32>}:
  match bs hk:
    case Nil{} _:
      %Equal.sym(List<&2,U32>, AR.slots(U32, AR.trep(U32, d, 0)), SC.replicate(U32, SC.pow2(d), 0), AR.trep_slots(U32, d, 0)) : {SC.nth(U32, _, U32.to_nat(n)) == Some{0} : Maybe<&2,U32>}
      nth_rep(SC.pow2(d), U32.to_nat(n), hn)
    case Con{G.Binding{+k, +v}, +rest} Tuple{+hb, +hr}:
      %Equal.sym(List<&2,U32>, AR.slots(U32, AR.upd(U32, d, tn(d, rest), U32.to_nat(k), K.encode(v))), SC.update(U32, AR.slots(U32, tn(d, rest)), U32.to_nat(k), K.encode(v)), AR.upd_slots(U32, d, tn(d, rest), U32.to_nat(k), K.encode(v), hb, tn_perfect(d, rest))) : {SC.nth(U32, _, U32.to_nat(n)) == Some{K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, Con{G.Binding{k, v}, rest}, None{}))} : Maybe<&2,U32>}
      nth_bind(d, k, v, rest, n, AR.slots(U32, tn(d, rest)), tn_len(d, rest), hn, tn_nth(d, rest, n, hn, hr), U32.is_eq(k, n), {==})

def dec_enc(+m: Maybe<&2,U32>, +hz: nz(m)) -> {K.decode(K.encode(m)) == m : Maybe<&2,U32>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Bool, U32.is_eq(x, 0), False{}, hz) : {K.decode_pick(x, _) == Some{x} : Maybe<&2,U32>}
      {==}

# ---- reads (on a graph given by its components) ----


def next_read(+n: U32, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +hz: nz(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{}))) -> {K.next(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), n) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{})) : K.Links & Maybe<&2,U32>}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tn(dn, ns)), n), (AR.thaw(U32, tn(dn, ns)), K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{}))), AR.get(U32, dn, tn(dn, ns), n, K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{})), hd, hn, tn_nth(dn, ns, n, hn, kn), tn_perfect(dn, ns))) : {K.next_got(AR.thaw(U32, tn(dn, ps)), AR.thaw(U32, tn(dr, rs)), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{})) : K.Links & Maybe<&2,U32>}
  %Equal.sym(Maybe<&2,U32>, K.decode(K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{}))), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{}), dec_enc(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{}), hz)) : {(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ns, None{})) : K.Links & Maybe<&2,U32>}
  {==}

def prev_read(+n: U32, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +hz: nz(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{}))) -> {K.prev(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), n) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{})) : K.Links & Maybe<&2,U32>}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tn(dn, ps)), n), (AR.thaw(U32, tn(dn, ps)), K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{}))), AR.get(U32, dn, tn(dn, ps), n, K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{})), hd, hn, tn_nth(dn, ps, n, hn, kp), tn_perfect(dn, ps))) : {K.prev_got(AR.thaw(U32, tn(dn, ns)), AR.thaw(U32, tn(dr, rs)), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{})) : K.Links & Maybe<&2,U32>}
  %Equal.sym(Maybe<&2,U32>, K.decode(K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{}))), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{}), dec_enc(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{}), hz)) : {(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, n, ps, None{})) : K.Links & Maybe<&2,U32>}
  {==}


def head_read(+r: U32, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hr: bound(dr, r), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +hz: nz(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{}))) -> {K.get_head(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), r) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{})) : K.Links & Maybe<&2,U32>}:
  %Equal.sym(Array<U32> & U32, Array.get(U32, AR.thaw(U32, tn(dr, rs)), r), (AR.thaw(U32, tn(dr, rs)), K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{}))), AR.get(U32, dr, tn(dr, rs), r, K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{})), hdr, hr, tn_nth(dr, rs, r, hr, kr), tn_perfect(dr, rs))) : {K.head_got(AR.thaw(U32, tn(dn, ns)), AR.thaw(U32, tn(dn, ps)), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{})) : K.Links & Maybe<&2,U32>}
  %Equal.sym(Maybe<&2,U32>, K.decode(K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{}))), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{}), dec_enc(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{}), hz)) : {(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), _) == (real(G.Graph{ns, ps, rs, Depth{dn, dr}}), G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, r, rs, None{})) : K.Links & Maybe<&2,U32>}
  {==}

# ---- writes ----

def set_tree(+d: Nat, +bs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +x: U32, +v: Maybe<&2,U32>, +hd0: {Nat.is_lt(d, 32n) == True{} : Bool}, +hx: bound(d, x), +kb: keys_ok(d, bs)) -> {Array.set(U32, AR.thaw(U32, tn(d, bs)), x, K.encode(v)) == AR.thaw(U32, tn(d, Con{G.Binding{x, v}, bs})) : Array<U32>}:
  AR.set(U32, d, tn(d, bs), x, K.encode(v), K.encode(G.lookup(~U32, ~Maybe<&2,U32>, ~ueq, x, bs, None{})), hd0, hx, tn_nth(d, bs, x, hx, kb), tn_perfect(d, bs))

def sn_law(+n: U32, +v: Maybe<&2,U32>, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs)) -> {K.set_next(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), n, v) == real(G.sn(~U32, ~U32, ~Depth, G.Graph{ns, ps, rs, Depth{dn, dr}}, n, v)) : K.Links}:
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tn(dn, ns)), n, K.encode(v)), AR.thaw(U32, tn(dn, Con{G.Binding{n, v}, ns})), set_tree(dn, ns, n, v, hd, hn, kn)) : {K.Links{_, AR.thaw(U32, tn(dn, ps)), AR.thaw(U32, tn(dr, rs))} == real(G.Graph{Con{G.Binding{n, v}, ns}, ps, rs, Depth{dn, dr}}) : K.Links}
  {==}

def sp_law(+n: U32, +v: Maybe<&2,U32>, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs)) -> {K.set_prev(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), n, v) == real(G.sp(~U32, ~U32, ~Depth, G.Graph{ns, ps, rs, Depth{dn, dr}}, n, v)) : K.Links}:
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tn(dn, ps)), n, K.encode(v)), AR.thaw(U32, tn(dn, Con{G.Binding{n, v}, ps})), set_tree(dn, ps, n, v, hd, hn, kp)) : {K.Links{AR.thaw(U32, tn(dn, ns)), _, AR.thaw(U32, tn(dr, rs))} == real(G.Graph{ns, Con{G.Binding{n, v}, ps}, rs, Depth{dn, dr}}) : K.Links}
  {==}

def sh_law(+r: U32, +v: Maybe<&2,U32>, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hr: bound(dr, r), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs)) -> {K.set_head(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), r, v) == real(G.sh(~U32, ~U32, ~Depth, G.Graph{ns, ps, rs, Depth{dn, dr}}, r, v)) : K.Links}:
  %Equal.sym(Array<U32>, Array.set(U32, AR.thaw(U32, tn(dr, rs)), r, K.encode(v)), AR.thaw(U32, tn(dr, Con{G.Binding{r, v}, rs})), set_tree(dr, rs, r, v, hdr, hr, kr)) : {K.Links{AR.thaw(U32, tn(dn, ns)), AR.thaw(U32, tn(dn, ps)), _} == real(G.Graph{ns, ps, Con{G.Binding{r, v}, rs}, Depth{dn, dr}}) : K.Links}
  {==}

# ---- the adapter laws, for every edit program with in-range targets ----


def tgt(+dn: Nat, +dr: Nat, e: Spec.Edit<U32,U32>) -> Data:
  match e:
    case Spec.Next{n, m}:
      bound(dn, n)
    case Spec.Prev{n, m}:
      bound(dn, n)
    case Spec.Head{i, m}:
      bound(dr, i)
    case Spec.Nonempty{i, n}:
      bound(dr, i)

def tgts(+dn: Nat, +dr: Nat, es: List<&2,Spec.Edit<U32,U32>>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{e, rest}:
      G.both(tgt(dn, dr, e), tgts(dn, dr, rest))

# Every edit program whose targets are in range is carried out exactly.
def laws_of(+es: List<&2,Spec.Edit<U32,U32>>, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +ht: tgts(dn, dr, es)) -> A.laws(~K.Links, ~U32, ~U32, ~Depth, ~U32, ~real, ~(i => i), ~K.set_next, ~K.set_prev, ~K.set_head, ~K.set_head_nonempty, es, G.Graph{ns, ps, rs, Depth{dn, dr}}):
  match es ht:
    case Nil{} _:
      Unit{}
    case Con{Spec.Next{+n, +v}, +rest} Tuple{+he, +hr}:
      (sn_law(n, v, ns, ps, rs, dn, dr, hd, hdr, he, kn, kp, kr), laws_of(rest, Con{G.Binding{n, v}, ns}, ps, rs, dn, dr, hd, hdr, (he, kn), kp, kr, hr))
    case Con{Spec.Prev{+n, +v}, +rest} Tuple{+he, +hr}:
      (sp_law(n, v, ns, ps, rs, dn, dr, hd, hdr, he, kn, kp, kr), laws_of(rest, ns, Con{G.Binding{n, v}, ps}, rs, dn, dr, hd, hdr, kn, (he, kp), kr, hr))
    case Con{Spec.Head{+i, +v}, +rest} Tuple{+he, +hr}:
      (sh_law(i, v, ns, ps, rs, dn, dr, hd, hdr, he, kn, kp, kr), laws_of(rest, ns, ps, Con{G.Binding{i, v}, rs}, dn, dr, hd, hdr, kn, kp, (he, kr), hr))
    case Con{Spec.Nonempty{+i, +n}, +rest} Tuple{+he, +hr}:
      (sh_law(i, Some{n}, ns, ps, rs, dn, dr, hd, hdr, he, kn, kp, kr), laws_of(rest, ns, ps, Con{G.Binding{i, Some{n}}, rs}, dn, dr, hd, hdr, kn, kp, (he, kr), hr))

def rm_tgts(+dn: Nat, +dr: Nat, +r: U32, +n: U32, +p: Maybe<&2,U32>, +q: Maybe<&2,U32>, +hn: bound(dn, n), +hr: bound(dr, r), +bp: inb(dn, p), +bq: inb(dn, q)) -> tgts(dn, dr, Spec.remove(U32, U32, r, n, p, q)):
  match p q:
    case None{} None{}:
      (hr, (hn, Unit{}))
    case None{} Some{+y}:
      (bq, (hr, (hn, Unit{})))
    case Some{+x} None{}:
      (bp, (hn, (hn, Unit{})))
    case Some{+x} Some{+y}:
      (bq, (bp, (hn, (hn, Unit{}))))

def pp_tgts(+dn: Nat, +dr: Nat, +r: U32, +n: U32, +h: Maybe<&2,U32>, +hn: bound(dn, n), +hr: bound(dr, r), +bh: inb(dn, h)) -> tgts(dn, dr, Spec.prepend(U32, U32, r, n, h)):
  match h:
    case None{}:
      (hn, (hr, Unit{}))
    case Some{+x}:
      (hn, (bh, (hr, Unit{})))

# ---- the exported operations are the model's, for every size ----


def remove_c(+r: U32, +n: U32, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +hr: bound(dr, r), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +zp: nz(G.prev(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n)), +zq: nz(G.next(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n)), +bp: inb(dn, G.prev(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n)), +bq: inb(dn, G.next(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n))) -> {K.remove(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), r, n) == real(G.remove(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r, n)) : K.Links}:
  A.remove_refines(~K.Links, ~U32, ~U32, ~Depth, ~U32, ~real, ~(i => i), ~K.set_next, ~K.set_prev, ~K.set_head, ~K.set_head_nonempty, ~ueq, ~K.next, ~K.prev, G.Graph{ns, ps, rs, Depth{dn, dr}}, r, n, next_read(n, ns, ps, rs, dn, dr, hd, hdr, hn, kn, kp, kr, zq), prev_read(n, ns, ps, rs, dn, dr, hd, hdr, hn, kn, kp, kr, zp), laws_of(Spec.remove(U32, U32, r, n, G.prev(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n), G.next(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n)), ns, ps, rs, dn, dr, hd, hdr, kn, kp, kr, rm_tgts(dn, dr, r, n, G.prev(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n), G.next(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, n), hn, hr, bp, bq)))

def prepend_c(+r: U32, +n: U32, +ns: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +ps: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +rs: List<&2,G.Binding<U32,Maybe<&2,U32>>>, +dn: Nat, +dr: Nat, +hd: {Nat.is_lt(dn, 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr, 32n) == True{} : Bool}, +hn: bound(dn, n), +hr: bound(dr, r), +kn: keys_ok(dn, ns), +kp: keys_ok(dn, ps), +kr: keys_ok(dr, rs), +zh: nz(G.head(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r)), +bh: inb(dn, G.head(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r))) -> {K.prepend(real(G.Graph{ns, ps, rs, Depth{dn, dr}}), r, n) == real(G.prepend(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r, n)) : K.Links}:
  A.prepend_refines(~K.Links, ~U32, ~U32, ~Depth, ~U32, ~real, ~(i => i), ~K.set_next, ~K.set_prev, ~K.set_head, ~K.set_head_nonempty, ~U32, ~ueq, ~K.get_head, G.Graph{ns, ps, rs, Depth{dn, dr}}, r, r, n, head_read(r, ns, ps, rs, dn, dr, hd, hdr, hr, kn, kp, kr, zh), laws_of(Spec.prepend(U32, U32, r, n, G.head(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r)), ns, ps, rs, dn, dr, hd, hdr, kn, kp, kr, pp_tgts(dn, dr, r, n, G.head(~U32, ~U32, ~Depth, ~ueq, G.Graph{ns, ps, rs, Depth{dn, dr}}, r), hn, hr, bh)))

# ---- the same, stated on any model graph ----


# The exported remove is the model's remove, for every table size.
def remove_refines(+r: U32, +n: U32, +g: G.Graph<U32,U32,Depth>, +hd: {Nat.is_lt(dn_of(g), 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr_of(g), 32n) == True{} : Bool}, +hk: gok(g), +hn: bound(dn_of(g), n), +hr: bound(dr_of(g), r), +zp: nz(G.prev(~U32, ~U32, ~Depth, ~ueq, g, n)), +zq: nz(G.next(~U32, ~U32, ~Depth, ~ueq, g, n)), +bp: inb(dn_of(g), G.prev(~U32, ~U32, ~Depth, ~ueq, g, n)), +bq: inb(dn_of(g), G.next(~U32, ~U32, ~Depth, ~ueq, g, n))) -> {K.remove(real(g), r, n) == real(G.remove(~U32, ~U32, ~Depth, ~ueq, g, r, n)) : K.Links}:
  match g hk:
    case G.Graph{+ns, +ps, +rs, Depth{+dn, +dr}} Tuple{+kn, Tuple{+kp, +kr}}:
      remove_c(r, n, ns, ps, rs, dn, dr, hd, hdr, hn, hr, kn, kp, kr, zp, zq, bp, bq)

# The exported prepend is the model's prepend, for every table size.
def prepend_refines(+r: U32, +n: U32, +g: G.Graph<U32,U32,Depth>, +hd: {Nat.is_lt(dn_of(g), 32n) == True{} : Bool}, +hdr: {Nat.is_lt(dr_of(g), 32n) == True{} : Bool}, +hk: gok(g), +hn: bound(dn_of(g), n), +hr: bound(dr_of(g), r), +zh: nz(G.head(~U32, ~U32, ~Depth, ~ueq, g, r)), +bh: inb(dn_of(g), G.head(~U32, ~U32, ~Depth, ~ueq, g, r))) -> {K.prepend(real(g), r, n) == real(G.prepend(~U32, ~U32, ~Depth, ~ueq, g, r, n)) : K.Links}:
  match g hk:
    case G.Graph{+ns, +ps, +rs, Depth{+dn, +dr}} Tuple{+kn, Tuple{+kp, +kr}}:
      prepend_c(r, n, ns, ps, rs, dn, dr, hd, hdr, hn, hr, kn, kp, kr, zh, bh)

# A fresh table is the empty model graph of its size.
def new_real(+dn: Nat, +dr: Nat) -> {K.new(dn, dr) == real(G.Graph{Nil{}, Nil{}, Nil{}, Depth{dn, dr}}) : K.Links}:
  %Equal.sym(Array<U32>, Array.new(U32, dn, 0), AR.thaw(U32, AR.trep(U32, dn, 0)), AR.new(U32, dn, 0)) : {K.Links{_, Array.new(U32, dn, 0), Array.new(U32, dr, 0)} == real(G.Graph{Nil{}, Nil{}, Nil{}, Depth{dn, dr}}) : K.Links}
  %Equal.sym(Array<U32>, Array.new(U32, dn, 0), AR.thaw(U32, AR.trep(U32, dn, 0)), AR.new(U32, dn, 0)) : {K.Links{AR.thaw(U32, AR.trep(U32, dn, 0)), _, Array.new(U32, dr, 0)} == real(G.Graph{Nil{}, Nil{}, Nil{}, Depth{dn, dr}}) : K.Links}
  %Equal.sym(Array<U32>, Array.new(U32, dr, 0), AR.thaw(U32, AR.trep(U32, dr, 0)), AR.new(U32, dr, 0)) : {K.Links{AR.thaw(U32, AR.trep(U32, dn, 0)), AR.thaw(U32, AR.trep(U32, dn, 0)), _} == real(G.Graph{Nil{}, Nil{}, Nil{}, Depth{dn, dr}}) : K.Links}
  {==}

# The empty graph satisfies every premise about keys.
def new_ok(+dn: Nat, +dr: Nat) -> gok(G.Graph{Nil{}, Nil{}, Nil{}, Depth{dn, dr}}):
  (Unit{}, (Unit{}, Unit{}))
