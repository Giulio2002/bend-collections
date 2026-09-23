import Base
import ./logic.bend as L
import ./nat.bend as N
import ./u32.bend as U
import ./lemmas/proofs/native_map.bend as NM

# Total-order laws for a static comparator ~cmp : A -> A -> Cmp, and their
# checked U32 (U32.cmp) and String (String.order) instances.
#   flip:    cmp(b, a) = flip(cmp(a, b))
#   antisym: cmp(a, b) = EQ  implies  a == b
#   trans:   a <= b and b <= c  implies  a <= c     (<= is cmp in {LT, EQ})

def flipc(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def lec(c: Cmp) -> Bool:
  Cmp.is_le(c)

def Order(~A: Data, ~cmp: A -> A -> Cmp) -> Type:
  (@+a: A -> @+b: A -> {cmp(b, a) == flipc(cmp(a, b)) : Cmp}) & ((@+a: A -> @+b: A -> @+e: {cmp(a, b) == EQ{} : Cmp} -> {a == b : A}) & (@+a: A -> @+b: A -> @+c: A -> @+ab: {Cmp.is_le(cmp(a, b)) == True{} : Bool} -> @+bc: {Cmp.is_le(cmp(b, c)) == True{} : Bool} -> {Cmp.is_le(cmp(a, c)) == True{} : Bool}))

def flip(~A: Data, ~cmp: A -> A -> Cmp, o: Order(~A, ~cmp), +a: A, +b: A) -> {cmp(b, a) == flipc(cmp(a, b)) : Cmp}:
  match o:
    case Tuple{f, r}:
      f(a, b)

def antisym(~A: Data, ~cmp: A -> A -> Cmp, o: Order(~A, ~cmp), +a: A, +b: A, +e: {cmp(a, b) == EQ{} : Cmp}) -> {a == b : A}:
  match o:
    case Tuple{f, Tuple{s, t}}:
      s(a, b, e)

def trans(~A: Data, ~cmp: A -> A -> Cmp, o: Order(~A, ~cmp), +a: A, +b: A, +c: A, +ab: {Cmp.is_le(cmp(a, b)) == True{} : Bool}, +bc: {Cmp.is_le(cmp(b, c)) == True{} : Bool}) -> {Cmp.is_le(cmp(a, c)) == True{} : Bool}:
  match o:
    case Tuple{f, Tuple{s, t}}:
      t(a, b, c, ab, bc)

# ---- consequences ----

def self_flip(+c: Cmp, +e: {c == flipc(c) : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.cmp_lt_gt(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.cmp_lt_gt(Equal.sym(Cmp, GT{}, LT{}, e)))

def refl(~A: Data, ~cmp: A -> A -> Cmp, ~o: Order(~A, ~cmp), +a: A) -> {cmp(a, a) == EQ{} : Cmp}:
  self_flip(cmp(a, a), flip(~A, ~cmp, o, a, a))

def le_refl(~A: Data, ~cmp: A -> A -> Cmp, ~o: Order(~A, ~cmp), +a: A) -> {Cmp.is_le(cmp(a, a)) == True{} : Bool}:
  %Equal.sym(Cmp, cmp(a, a), EQ{}, refl(~A, ~cmp, ~o, a)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def not_le_flip(+c: Cmp, +e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_le(flipc(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(flipc(LT{})) == True{} : Bool}, L.true_false(e))
    case EQ{}:
      Empty.absurd({Cmp.is_le(flipc(EQ{})) == True{} : Bool}, L.true_false(e))
    case GT{}:
      {==}

# Totality: not a <= b gives b <= a.
def total(~A: Data, ~cmp: A -> A -> Cmp, ~o: Order(~A, ~cmp), +a: A, +b: A, +e: {Cmp.is_le(cmp(a, b)) == False{} : Bool}) -> {Cmp.is_le(cmp(b, a)) == True{} : Bool}:
  %Equal.sym(Cmp, cmp(b, a), flipc(cmp(a, b)), flip(~A, ~cmp, o, a, b)) : {Cmp.is_le(_) == True{} : Bool}
  not_le_flip(cmp(a, b), e)

def both_le_eq(+c: Cmp, +e1: {Cmp.is_le(c) == True{} : Bool}, +e2: {Cmp.is_le(flipc(c)) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, L.false_true(e2))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, L.false_true(e1))

def le_antisym(~A: Data, ~cmp: A -> A -> Cmp, ~o: Order(~A, ~cmp), +a: A, +b: A, +ab: {Cmp.is_le(cmp(a, b)) == True{} : Bool}, +ba: {Cmp.is_le(cmp(b, a)) == True{} : Bool}) -> {a == b : A}:
  antisym(~A, ~cmp, o, a, b, both_le_eq(cmp(a, b), ab, L.subst(Cmp, c => {Cmp.is_le(c) == True{} : Bool}, cmp(b, a), flipc(cmp(a, b)), flip(~A, ~cmp, o, a, b), ba)))

# ---- Nat comparison ----

def nat_flip(+a: Nat, +b: Nat) -> {Nat.cmp(b, a) == flipc(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat_flip(p, q)

def nat_eq(+a: Nat, +b: Nat, +e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  N.eq_from_is_eq(a, b, L.subst(Cmp, c => {Cmp.is_eq(c) == True{} : Bool}, EQ{}, Nat.cmp(a, b), Equal.sym(Cmp, Nat.cmp(a, b), EQ{}, e), {==}))

# ---- U32 instance ----

def u32_flip(+a: U32, +b: U32) -> {U32.cmp(b, a) == flipc(U32.cmp(a, b)) : Cmp}:
  %Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b)) : {U32.cmp(b, a) == flipc(_) : Cmp}
  %Equal.sym(Cmp, U32.cmp(b, a), Nat.cmp(U32.to_nat(b), U32.to_nat(a)), U.u32_cmp(b, a)) : {_ == flipc(Nat.cmp(U32.to_nat(a), U32.to_nat(b))) : Cmp}
  nat_flip(U32.to_nat(a), U32.to_nat(b))

def u32_antisym(+a: U32, +b: U32, +e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  U.injective(a, b, nat_eq(U32.to_nat(a), U32.to_nat(b), Equal.trans(Cmp, Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U32.cmp(a, b), EQ{}, Equal.sym(Cmp, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b)), e)))

def u32_trans(+a: U32, +b: U32, +c: U32, +ab: {Cmp.is_le(U32.cmp(a, b)) == True{} : Bool}, +bc: {Cmp.is_le(U32.cmp(b, c)) == True{} : Bool}) -> {Cmp.is_le(U32.cmp(a, c)) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, c), Nat.cmp(U32.to_nat(a), U32.to_nat(c)), U.u32_cmp(a, c)) : {Cmp.is_le(_) == True{} : Bool}
  N.le_trans(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c),
    L.subst(Cmp, x => {Cmp.is_le(x) == True{} : Bool}, U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), U.u32_cmp(a, b), ab),
    L.subst(Cmp, x => {Cmp.is_le(x) == True{} : Bool}, U32.cmp(b, c), Nat.cmp(U32.to_nat(b), U32.to_nat(c)), U.u32_cmp(b, c), bc))

def u32_order() -> Order(~U32, ~U32.cmp):
  (u32_flip, (u32_antisym, u32_trans))

def nat_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}, +bc: {Cmp.is_le(Nat.cmp(b, c)) == True{} : Bool}) -> {Cmp.is_le(Nat.cmp(a, c)) == True{} : Bool}:
  N.le_trans(a, b, c, ab, bc)

def nat_order() -> Order(~Nat, ~Nat.cmp):
  (nat_flip, (nat_eq, nat_trans))

# ---- String instance (String.order, lexicographic on character codes) ----

def lex(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      r
    case GT{}:
      GT{}

def order_tag(+a: String, +b: String) -> {String.order(a, b) == NM.comparison_tag(String, String.cmp(a, b)) : Cmp}:
  %Equal.sym((String & String) & Cmp, String.cmp(a, b), ((a, b), NM.comparison_tag(String, String.cmp(a, b))), NM.string_comparison_shape(a, b)) : {String.order.fin(_) == NM.comparison_tag(String, _) : Cmp}
  {==}

def so_cons_c(+x: U32, +t1: String, +y: U32, +t2: String, +c: Cmp, +ec: {U32.cmp(x, y) == c : Cmp}) -> {String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}) == lex(c, String.order(t1, t2)) : Cmp}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(x, y), LT{}, ec) : {String.order.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), _))) == LT{} : Cmp}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(x, y), GT{}, ec) : {String.order.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), _))) == GT{} : Cmp}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(x, y), EQ{}, ec) : {String.order.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), _))) == String.order(t1, t2) : Cmp}
      %Equal.sym((String & String) & Cmp, String.cmp(t1, t2), ((t1, t2), NM.comparison_tag(String, String.cmp(t1, t2))), NM.string_comparison_shape(t1, t2)) : {String.order.fin(String.cmp.rec(Chr{x}, Chr{y}, _)) == String.order.fin(_) : Cmp}
      {==}

def so_cons(+x: U32, +t1: String, +y: U32, +t2: String) -> {String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}) == lex(U32.cmp(x, y), String.order(t1, t2)) : Cmp}:
  so_cons_c(x, t1, y, t2, U32.cmp(x, y), {==})

def flip_lex(+c: Cmp, +r: Cmp) -> {lex(flipc(c), flipc(r)) == flipc(lex(c, r)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def s_flip(+a: String, +b: String) -> {String.order(b, a) == flipc(String.order(a, b)) : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      %Equal.sym(Cmp, String.order(SCon{Chr{y}, t2}, SCon{Chr{x}, t1}), lex(U32.cmp(y, x), String.order(t2, t1)), so_cons(y, t2, x, t1)) : {_ == flipc(String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2})) : Cmp}
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}), lex(U32.cmp(x, y), String.order(t1, t2)), so_cons(x, t1, y, t2)) : {lex(U32.cmp(y, x), String.order(t2, t1)) == flipc(_) : Cmp}
      %Equal.sym(Cmp, U32.cmp(y, x), flipc(U32.cmp(x, y)), u32_flip(x, y)) : {lex(_, String.order(t2, t1)) == flipc(lex(U32.cmp(x, y), String.order(t1, t2))) : Cmp}
      %Equal.sym(Cmp, String.order(t2, t1), flipc(String.order(t1, t2)), s_flip(t1, t2)) : {lex(flipc(U32.cmp(x, y)), _) == flipc(lex(U32.cmp(x, y), String.order(t1, t2))) : Cmp}
      flip_lex(U32.cmp(x, y), String.order(t1, t2))

def s_antisym(+a: String, +b: String, +e: {String.order(a, b) == EQ{} : Cmp}) -> {a == b : String}:
  NM.string_equal_from_comparison(a, b, Equal.trans(Cmp, NM.comparison_tag(String, String.cmp(a, b)), String.order(a, b), EQ{}, Equal.sym(Cmp, String.order(a, b), NM.comparison_tag(String, String.cmp(a, b)), order_tag(a, b)), e))

def lt_is(+c: Cmp, +e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, L.false_true(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, L.false_true(e))

def u32_lt_le(+x: U32, +y: U32, +z: U32, +xy: {U32.cmp(x, y) == LT{} : Cmp}, +yz: {Cmp.is_le(U32.cmp(y, z)) == True{} : Bool}) -> {U32.cmp(x, z) == LT{} : Cmp}:
  lt_is(U32.cmp(x, z),
    L.subst(Cmp, k => {Cmp.is_lt(k) == True{} : Bool}, Nat.cmp(U32.to_nat(x), U32.to_nat(z)), U32.cmp(x, z), Equal.sym(Cmp, U32.cmp(x, z), Nat.cmp(U32.to_nat(x), U32.to_nat(z)), U.u32_cmp(x, z)),
      N.lt_le_trans(U32.to_nat(x), U32.to_nat(y), U32.to_nat(z),
        L.subst(Cmp, k => {Cmp.is_lt(k) == True{} : Bool}, LT{}, Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Equal.trans(Cmp, LT{}, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Equal.sym(Cmp, U32.cmp(x, y), LT{}, xy), U.u32_cmp(x, y)), {==}),
        L.subst(Cmp, k => {Cmp.is_le(k) == True{} : Bool}, U32.cmp(y, z), Nat.cmp(U32.to_nat(y), U32.to_nat(z)), U.u32_cmp(y, z), yz))))

# The head-character case of transitivity, given the tails' statement.
def s_trans_heads(+x: U32, +y: U32, +z: U32, +o12: Cmp, +o23: Cmp, +o13: Cmp, +cxy: Cmp, +exy: {U32.cmp(x, y) == cxy : Cmp}, +cyz: Cmp, +eyz: {U32.cmp(y, z) == cyz : Cmp}, +ab: {Cmp.is_le(lex(cxy, o12)) == True{} : Bool}, +bc: {Cmp.is_le(lex(cyz, o23)) == True{} : Bool}, ih: @+ab2: {Cmp.is_le(o12) == True{} : Bool} -> @+bc2: {Cmp.is_le(o23) == True{} : Bool} -> {Cmp.is_le(o13) == True{} : Bool}) -> {Cmp.is_le(lex(U32.cmp(x, z), o13)) == True{} : Bool}:
  match cxy cyz:
    case GT{} _:
      Empty.absurd({Cmp.is_le(lex(U32.cmp(x, z), o13)) == True{} : Bool}, L.false_true(ab))
    case _ GT{}:
      Empty.absurd({Cmp.is_le(lex(U32.cmp(x, z), o13)) == True{} : Bool}, L.false_true(bc))
    case LT{} LT{}:
      %Equal.sym(Cmp, U32.cmp(x, z), LT{}, u32_lt_le(x, y, z, exy, L.subst(Cmp, k => {Cmp.is_le(k) == True{} : Bool}, LT{}, U32.cmp(y, z), Equal.sym(Cmp, U32.cmp(y, z), LT{}, eyz), {==}))) : {Cmp.is_le(lex(_, o13)) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, U32.cmp(x, z), LT{}, u32_lt_le(x, y, z, exy, L.subst(Cmp, k => {Cmp.is_le(k) == True{} : Bool}, EQ{}, U32.cmp(y, z), Equal.sym(Cmp, U32.cmp(y, z), EQ{}, eyz), {==}))) : {Cmp.is_le(lex(_, o13)) == True{} : Bool}
      {==}
    case EQ{} LT{}:
      %Equal.sym(U32, x, y, u32_antisym(x, y, exy)) : {Cmp.is_le(lex(U32.cmp(_, z), o13)) == True{} : Bool}
      %Equal.sym(Cmp, U32.cmp(y, z), LT{}, eyz) : {Cmp.is_le(lex(_, o13)) == True{} : Bool}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(U32, x, y, u32_antisym(x, y, exy)) : {Cmp.is_le(lex(U32.cmp(_, z), o13)) == True{} : Bool}
      %Equal.sym(Cmp, U32.cmp(y, z), EQ{}, eyz) : {Cmp.is_le(lex(_, o13)) == True{} : Bool}
      ih(ab, bc)

def s_trans(+a: String, +b: String, +c: String, +ab: {Cmp.is_le(String.order(a, b)) == True{} : Bool}, +bc: {Cmp.is_le(String.order(b, c)) == True{} : Bool}) -> {Cmp.is_le(String.order(a, c)) == True{} : Bool}:
  match a b c:
    case SNil{} _ SNil{}:
      {==}
    case SNil{} _ SCon{h, t}:
      {==}
    case SCon{h, t} SNil{} _:
      Empty.absurd({Cmp.is_le(String.order(SCon{h, t}, c)) == True{} : Bool}, L.false_true(ab))
    case SCon{h1, t1} SCon{h2, t2} SNil{}:
      Empty.absurd({Cmp.is_le(String.order(SCon{h1, t1}, SNil{})) == True{} : Bool}, L.false_true(bc))
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} SCon{Chr{+z}, +t3}:
      %Equal.sym(Cmp, String.order(SCon{Chr{x}, t1}, SCon{Chr{z}, t3}), lex(U32.cmp(x, z), String.order(t1, t3)), so_cons(x, t1, z, t3)) : {Cmp.is_le(_) == True{} : Bool}
      s_trans_heads(x, y, z, String.order(t1, t2), String.order(t2, t3), String.order(t1, t3), U32.cmp(x, y), {==}, U32.cmp(y, z), {==},
        L.subst(Cmp, k => {Cmp.is_le(k) == True{} : Bool}, String.order(SCon{Chr{x}, t1}, SCon{Chr{y}, t2}), lex(U32.cmp(x, y), String.order(t1, t2)), so_cons(x, t1, y, t2), ab),
        L.subst(Cmp, k => {Cmp.is_le(k) == True{} : Bool}, String.order(SCon{Chr{y}, t2}, SCon{Chr{z}, t3}), lex(U32.cmp(y, z), String.order(t2, t3)), so_cons(y, t2, z, t3), bc),
        ab2 => bc2 => s_trans(t1, t2, t3, ab2, bc2))

def string_order() -> Order(~String, ~String.order):
  (s_flip, (s_antisym, s_trans))
