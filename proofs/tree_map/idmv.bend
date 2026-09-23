import Base
import ../lib/logic.bend as L
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ./state.bend as ST
import ./path.bend as P
import ./alls.bend as AL
import ../lib/nat_list.bend as NL


# The ids when a node with at most one child leaves the tree for the free
# chain: the tree's ids without it, the free chain with it in front; without
# repeats, in range, of the same length. (source: tools/generators/tm_hand/idmv.src)


# ---- the ids: the node moves from the tree's ids to the free chain ----

def nd_back(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +h: {NL.nodupn(SC.append(Nat, SC.append(Nat, b, Con{x, a}), t)) == True{} : Bool}) -> {NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), Con{x, t})) == True{} : Bool}:
  +h1 = L.subst(List<&2, Nat>, z => {NL.nodupn(z) == True{} : Bool}, SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), SC.append(Nat, b, Con{x, SC.append(Nat, a, t)}), AL.mv_eq(b, a, x, t), h)
  +h2 = L.subst(Bool, w => {w == True{} : Bool}, NL.nodupn(SC.append(Nat, b, Con{x, SC.append(Nat, a, t)})), Bool.and(NL.nodupn(SC.append(Nat, b, SC.append(Nat, a, t))), Bool.not(NL.memn(x, SC.append(Nat, b, SC.append(Nat, a, t))))), NL.nd_mid(b, x, SC.append(Nat, a, t)), h1)
  +h3 = L.subst(List<&2, Nat>, z => {Bool.and(NL.nodupn(z), Bool.not(NL.memn(x, z))) == True{} : Bool}, SC.append(Nat, b, SC.append(Nat, a, t)), SC.append(Nat, SC.append(Nat, b, a), t), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, b, a), t), SC.append(Nat, b, SC.append(Nat, a, t)), LL.append_assoc(Nat, b, a, t)), h2)
  L.subst(Bool, w => {w == True{} : Bool}, Bool.and(NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), t)), Bool.not(NL.memn(x, SC.append(Nat, SC.append(Nat, b, a), t)))), NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), Equal.sym(Bool, NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), Con{x, t})), Bool.and(NL.nodupn(SC.append(Nat, SC.append(Nat, b, a), t)), Bool.not(NL.memn(x, SC.append(Nat, SC.append(Nat, b, a), t)))), NL.nd_mid(SC.append(Nat, b, a), x, t)), h3)

def allin_back(+b: List<&2, Nat>, +a: List<&2, Nat>, +x: Nat, +t: List<&2, Nat>, +n: Nat, +h: {ST.allin(SC.append(Nat, SC.append(Nat, b, Con{x, a}), t), n) == True{} : Bool}) -> {ST.allin(SC.append(Nat, SC.append(Nat, b, a), Con{x, t}), n) == True{} : Bool}:
  +hbx = AL.allin_l(SC.append(Nat, b, Con{x, a}), t, n, h)
  +ht = AL.allin_r(SC.append(Nat, b, Con{x, a}), t, n, h)
  +hxa = AL.allin_r(b, Con{x, a}, n, hbx)
  +hx = L.and_left(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(a, n), hxa)
  AL.allin_app(SC.append(Nat, b, a), Con{x, t}, n, AL.allin_app(b, a, n, AL.allin_l(b, Con{x, a}, n, hbx), L.and_right(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(a, n), hxa)), L.and_intro(Bool.and(Nat.is_lt(0n, x), Nat.is_le(x, n)), ST.allin(t, n), hx, ht))

# the free chain gets the node: the ids with it moved
def mv_a(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr, +h: {NL.nodupn(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ST.TE{}, ch}), P.after(c))), flf)) == True{} : Bool}) -> {NL.nodupn(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})) == True{} : Bool}:
  nd_back(P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)), 1n+ui, flf, h)

def mv_b(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr, +h: {NL.nodupn(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), flf)) == True{} : Bool}) -> {NL.nodupn(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})) == True{} : Bool}:
  +e1 = Equal.trans(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)})), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), L.subst(List<&2, Nat>, z => {SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))) == SC.append(Nat, P.before(c), z) : List<&2, Nat>}, SC.append(Nat, SC.append(Nat, ST.ids(ch), Con{1n+ui, Nil{}}), P.after(c)), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)}), LL.append_assoc(Nat, ST.ids(ch), Con{1n+ui, Nil{}}, P.after(c)), {==}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)})), LL.append_assoc(Nat, P.before(c), ST.ids(ch), Con{1n+ui, P.after(c)})))
  +h1 = L.subst(List<&2, Nat>, z => {NL.nodupn(SC.append(Nat, z, flf)) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), e1, h)
  +h2 = nd_back(SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c), 1n+ui, flf, h1)
  L.subst(List<&2, Nat>, z => {NL.nodupn(SC.append(Nat, z, Con{1n+ui, flf})) == True{} : Bool}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), LL.append_assoc(Nat, P.before(c), ST.ids(ch), P.after(c)), h2)


# the ids with no left child, and with no right child, as a split at the node
def wb_eq(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))) == SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)})), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), L.subst(List<&2, Nat>, z => {SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))) == SC.append(Nat, P.before(c), z) : List<&2, Nat>}, SC.append(Nat, SC.append(Nat, ST.ids(ch), Con{1n+ui, Nil{}}), P.after(c)), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)}), LL.append_assoc(Nat, ST.ids(ch), Con{1n+ui, Nil{}}, P.after(c)), {==}), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), Con{1n+ui, P.after(c)})), LL.append_assoc(Nat, P.before(c), ST.ids(ch), Con{1n+ui, P.after(c)})))

def i0_eq(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)) == SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))) : List<&2, Nat>}:
  LL.append_assoc(Nat, P.before(c), ST.ids(ch), P.after(c))

def ain_a(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr, +n: Nat, +h: {ST.allin(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ST.TE{}, ch}), P.after(c))), flf), n) == True{} : Bool}) -> {ST.allin(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf}), n) == True{} : Bool}:
  allin_back(P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)), 1n+ui, flf, n, h)

def ain_b(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr, +n: Nat, +h: {ST.allin(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), flf), n) == True{} : Bool}) -> {ST.allin(SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf}), n) == True{} : Bool}:
  +h1 = L.subst(List<&2, Nat>, z => {ST.allin(SC.append(Nat, z, flf), n) == True{} : Bool}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), wb_eq(flf, c, ui, ch), h)
  L.subst(List<&2, Nat>, z => {ST.allin(SC.append(Nat, z, Con{1n+ui, flf}), n) == True{} : Bool}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), i0_eq(flf, c, ui, ch), allin_back(SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c), 1n+ui, flf, n, h1))

def len_a(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})) == SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ST.TE{}, ch}), P.after(c))), flf)) : Nat}:
  Equal.sym(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ST.TE{}, ch}), P.after(c))), flf)), SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})), AL.len_move(P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)), 1n+ui, flf))

def len_b(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})) == SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), flf)) : Nat}:
  +e0 = L.subst(List<&2, Nat>, z => {SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})) == SC.length(Nat, SC.append(Nat, z, Con{1n+ui, flf})) : Nat}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), Equal.sym(List<&2, Nat>, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), i0_eq(flf, c, ui, ch)), {==})
  +e1 = Equal.sym(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), flf)), SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), Con{1n+ui, flf})), AL.len_move(SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c), 1n+ui, flf))
  +e2 = L.subst(List<&2, Nat>, z => {SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), flf)) == SC.length(Nat, SC.append(Nat, z, flf)) : Nat}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), Equal.sym(List<&2, Nat>, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), wb_eq(flf, c, ui, ch)), {==})
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), Con{1n+ui, flf})), SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), Con{1n+ui, flf})), SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), flf)), e0, Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), Con{1n+ui, flf})), SC.length(Nat, SC.append(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), flf)), SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), flf)), e1, e2))

def sz_a(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ST.TE{}, ch}), P.after(c)))) == 1n+SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)))) : Nat}:
  AL.len_put(P.before(c), 1n+ui, SC.append(Nat, ST.ids(ch), P.after(c)))

def sz_b(+flf: List<&2, Nat>, +c: List<&2, P.Fr>, +ui: Nat, +ch: ST.Tr) -> {SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c)))) == 1n+SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)))) : Nat}:
  +e1 = L.subst(List<&2, Nat>, z => {SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c)))) == SC.length(Nat, z) : Nat}, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c))), SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)}), wb_eq(flf, c, ui, ch), {==})
  +e2 = L.subst(List<&2, Nat>, z => {1n+SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c))) == 1n+SC.length(Nat, z) : Nat}, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c)), SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c))), i0_eq(flf, c, ui, ch), {==})
  Equal.trans(Nat, SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ST.TN{1n+ui, ch, ST.TE{}}), P.after(c)))), SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)})), 1n+SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)))), e1, Equal.trans(Nat, SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), Con{1n+ui, P.after(c)})), 1n+SC.length(Nat, SC.append(Nat, SC.append(Nat, P.before(c), ST.ids(ch)), P.after(c))), 1n+SC.length(Nat, SC.append(Nat, P.before(c), SC.append(Nat, ST.ids(ch), P.after(c)))), AL.len_put(SC.append(Nat, P.before(c), ST.ids(ch)), 1n+ui, P.after(c)), e2))
