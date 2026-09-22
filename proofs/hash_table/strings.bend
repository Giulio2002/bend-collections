import Base
import ../lib/u32.bend as U
import ../spec/hash_table.bend as S
import ../../src/math/hash.bend as HS
import ../../src/containers/hash_table.bend as H

# The hash map's String walks: hashing hands the key back and folds the
# multiply-xor mix over its characters; equality is the spec's structural
# equality and hands both strings back; copying makes two equal strings.

def rr(+s: String, +acc: String) -> {H.rev_onto(H.rev_onto(s, acc), SNil{}) == H.rev_onto(acc, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rr(t, SCon{h, acc})

def rev2(+s: String) -> {H.rev_onto(H.rev_onto(s, SNil{}), SNil{}) == s : String}:
  rr(s, SNil{})

# the hash of a key: the mix folded over its character codes
def fold(s: String, +h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{+c}, t}:
      fold(t, HS.mix(h, c))

def hash_acc(+s: String, +h: U32, +acc: String) -> {H.hash_acc(s, h, acc) == (H.rev_onto(acc, s), fold(s, h)) : String & U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      hash_acc(t, HS.mix(h, c), SCon{Chr{c}, acc})

# a key's long check word
def lword(+s: String) -> U32:
  H.long_word(fold(s, 0))

def key_long(+s: String) -> {H.key_long(s) == (s, lword(s)) : String & U32}:
  Equal.cong(String & U32, String & U32, r => H.lw_fin(r), H.hash_acc(s, 0, SNil{}), (s, fold(s, 0)), hash_acc(s, 0, SNil{}))

def and_true(+e: Bool) -> {Bool.and(e, True{}) == e : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false(+e: Bool) -> {Bool.and(e, False{}) == False{} : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def and_assoc(+e: Bool, +p: Bool, +q: Bool) -> {Bool.and(Bool.and(e, p), q) == Bool.and(e, Bool.and(p, q)) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def eq_acc(+a: String, +b: String, +ra: String, +rb: String, +e: Bool) -> {H.eq_acc(a, b, ra, rb, e) == ((H.rev_onto(ra, a), H.rev_onto(rb, b)), Bool.and(e, S.str_eq(a, b))) : (String & String) & Bool}:
  match a b:
    case SNil{} SNil{}:
      Equal.cong(Bool, (String & String) & Bool, z => ((H.rev_onto(ra, SNil{}), H.rev_onto(rb, SNil{})), z), e, Bool.and(e, True{}), Equal.sym(Bool, Bool.and(e, True{}), e, and_true(e)))
    case SNil{} SCon{h, t}:
      Equal.cong(Bool, (String & String) & Bool, z => ((H.rev_onto(ra, SNil{}), H.rev_onto(rb, SCon{h, t})), z), False{}, Bool.and(e, False{}), Equal.sym(Bool, Bool.and(e, False{}), False{}, and_false(e)))
    case SCon{Chr{c}, t} SNil{}:
      Equal.cong(Bool, (String & String) & Bool, z => ((H.rev_onto(ra, SCon{Chr{c}, t}), H.rev_onto(rb, SNil{})), z), False{}, Bool.and(e, False{}), Equal.sym(Bool, Bool.and(e, False{}), False{}, and_false(e)))
    case SCon{Chr{+x}, +ta} SCon{Chr{+y}, +tb}:
      Equal.trans((String & String) & Bool, H.eq_acc(ta, tb, SCon{Chr{x}, ra}, SCon{Chr{y}, rb}, Bool.and(e, U32.is_eq(x, y))), ((H.rev_onto(ra, SCon{Chr{x}, ta}), H.rev_onto(rb, SCon{Chr{y}, tb})), Bool.and(Bool.and(e, U32.is_eq(x, y)), S.str_eq(ta, tb))), ((H.rev_onto(ra, SCon{Chr{x}, ta}), H.rev_onto(rb, SCon{Chr{y}, tb})), Bool.and(e, S.str_eq(SCon{Chr{x}, ta}, SCon{Chr{y}, tb}))),
        eq_acc(ta, tb, SCon{Chr{x}, ra}, SCon{Chr{y}, rb}, Bool.and(e, U32.is_eq(x, y))),
        Equal.cong(Bool, (String & String) & Bool, z => ((H.rev_onto(ra, SCon{Chr{x}, ta}), H.rev_onto(rb, SCon{Chr{y}, tb})), z), Bool.and(Bool.and(e, U32.is_eq(x, y)), S.str_eq(ta, tb)), Bool.and(e, Bool.and(U32.is_eq(x, y), S.str_eq(ta, tb))), and_assoc(e, U32.is_eq(x, y), S.str_eq(ta, tb))))

# THEOREM: eq is String equality, handing both strings back.
def eq(+a: String, +b: String) -> {H.eq(a, b) == ((a, b), S.str_eq(a, b)) : (String & String) & Bool}:
  eq_acc(a, b, SNil{}, SNil{}, True{})

def copy_acc(+s: String, +ra: String, +rb: String) -> {H.copy_acc(s, ra, rb) == (H.rev_onto(ra, s), H.rev_onto(rb, s)) : String & String}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+c}, t}:
      copy_acc(t, SCon{Chr{c}, ra}, SCon{Chr{c}, rb})

def str_copy(+s: String) -> {H.str_copy(s) == (s, s) : String & String}:
  copy_acc(s, SNil{}, SNil{})
