import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/u32alg.bend as UA
import ../lib/list.bend as LL
import ../spec/common.bend as SC
import ../../src/containers/bitset.bend as B

# The counting loop of src/bitset.bend (eight bits per iteration, a zero word
# skipped) computes exactly word_count(32, w), the count proofs/bitset/word
# relates to the bit model.

def mul8(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(8n, mul8(p))

# one level of re-association: (b + R) + W = b + T when R + W = T
def reassoc(+b: Nat, +r: Nat, +w: Nat, +t: Nat, +e: {Nat.add(r, w) == t : Nat}) -> {Nat.add(Nat.add(b, r), w) == Nat.add(b, t) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(b, r), w), Nat.add(b, Nat.add(r, w)), Nat.add(b, t), N.add_assoc(b, r, w), Equal.cong(Nat, Nat, z => Nat.add(b, z), Nat.add(r, w), t, e))

def push_end(+w: U32, +m: Nat) -> {Nat.add(Nat.add(B.bit_value(B.low(w)), Nat.add(B.bit_value(B.low(U32.shr(w))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))) == Nat.add(B.bit_value(B.low(w)), Nat.add(B.bit_value(B.low(U32.shr(w))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))))))) : Nat}:
  reassoc(B.bit_value(B.low(w)), Nat.add(B.bit_value(B.low(U32.shr(w))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(w))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))))))), reassoc(B.bit_value(B.low(U32.shr(w))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))))), reassoc(B.bit_value(B.low(U32.shr(U32.shr(w)))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))))), reassoc(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(w))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))))), reassoc(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(w)))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))))), reassoc(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))))), reassoc(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))), B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), Nat.add(B.bit_value(B.low(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))), B.word_count(m, U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w)))))))))), {==})))))))

def wc8(k: Nat, +w: U32, +acc: Nat) -> {B.word_count_8(k, w, acc) == Nat.add(acc, B.word_count(mul8(k), w)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, N.add_zero(acc))
    case 1n+ +p:
      +w8 = U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(U32.shr(w))))))))
      +ih = wc8(p, w8, Nat.add(acc, B.bv8(w)))
      Equal.trans(Nat, B.word_count_8(p, w8, Nat.add(acc, B.bv8(w))), Nat.add(Nat.add(acc, B.bv8(w)), B.word_count(mul8(p), w8)), Nat.add(acc, B.word_count(Nat.add(8n, mul8(p)), w)), ih,
        reassoc(acc, B.bv8(w), B.word_count(mul8(p), w8), B.word_count(Nat.add(8n, mul8(p)), w), push_end(w, mul8(p))))

def count_word_ok(+w: U32, +acc: Nat, z: Bool, +ez: {U32.is_eq(w, 0) == z : Bool}) -> {B.count_word(w, acc, z) == Nat.add(acc, B.word_count(32n, w)) : Nat}:
  match z:
    case True{}:
      %Equal.sym(U32, w, 0, UA.eq_of(w, 0, ez)) : {acc == Nat.add(acc, B.word_count(32n, _)) : Nat}
      Equal.sym(Nat, Nat.add(acc, 0n), acc, N.add_zero(acc))
    case False{}:
      wc8(4n, w, acc)

# ---- members of one word ----

def wm_app_go(b: Bool, +off: Nat, +m1: List<&2, Nat>, +m0: List<&2, Nat>, +rest: List<&2, Nat>, +ih: {m1 == SC.append(Nat, m0, rest) : List<&2, Nat>}) -> {B.member_pick(b, off, m1) == SC.append(Nat, B.member_pick(b, off, m0), rest) : List<&2, Nat>}:
  match b:
    case True{}:
      LL.cons_cong(Nat, off, m1, SC.append(Nat, m0, rest), ih)
    case False{}:
      ih

def wm_app(m: Nat, +w: U32, +off: Nat, +rest: List<&2, Nat>) -> {B.word_members(m, w, off, rest) == SC.append(Nat, B.word_members(m, w, off, Nil{}), rest) : List<&2, Nat>}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      wm_app_go(B.low(w), off, B.word_members(p, U32.shr(w), 1n+off, rest), B.word_members(p, U32.shr(w), 1n+off, Nil{}), rest, wm_app(p, U32.shr(w), 1n+off, rest))

def desc_go(b: Bool, +off: Nat, +mm: List<&2, Nat>, +acc: List<&2, Nat>) -> {SC.append(Nat, SC.reverse(Nat, mm), B.member_pick(b, off, acc)) == SC.append(Nat, SC.reverse(Nat, B.member_pick(b, off, mm)), acc) : List<&2, Nat>}:
  match b:
    case True{}:
      Equal.sym(List<&2, Nat>, SC.append(Nat, SC.snoc(Nat, SC.reverse(Nat, mm), off), acc), SC.append(Nat, SC.reverse(Nat, mm), Con{off, acc}), LL.snoc_append_cons(Nat, SC.reverse(Nat, mm), off, acc))
    case False{}:
      {==}

def desc_ok(m: Nat, +w: U32, +off: Nat, +acc: List<&2, Nat>) -> {B.word_desc(m, w, off, acc) == SC.append(Nat, SC.reverse(Nat, B.word_members(m, w, off, Nil{})), acc) : List<&2, Nat>}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(List<&2, Nat>, B.word_desc(p, U32.shr(w), 1n+off, B.member_pick(B.low(w), off, acc)), SC.append(Nat, SC.reverse(Nat, B.word_members(p, U32.shr(w), 1n+off, Nil{})), B.member_pick(B.low(w), off, acc)), SC.append(Nat, SC.reverse(Nat, B.member_pick(B.low(w), off, B.word_members(p, U32.shr(w), 1n+off, Nil{}))), acc),
        desc_ok(p, U32.shr(w), 1n+off, B.member_pick(B.low(w), off, acc)),
        desc_go(B.low(w), off, B.word_members(p, U32.shr(w), 1n+off, Nil{}), acc))

def members_word_ok(+w: U32, +off: Nat, +rest: List<&2, Nat>, z: Bool, +ez: {U32.is_eq(w, 0) == z : Bool}) -> {B.members_word(w, off, rest, z) == B.word_members(32n, w, off, rest) : List<&2, Nat>}:
  match z:
    case True{}:
      %Equal.sym(U32, w, 0, UA.eq_of(w, 0, ez)) : {rest == B.word_members(32n, _, off, rest) : List<&2, Nat>}
      {==}
    case False{}:
      +mm = B.word_members(32n, w, off, Nil{})
      %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, B.word_desc(32n, w, off, Nil{}), rest), SC.append(Nat, SC.reverse(Nat, B.word_desc(32n, w, off, Nil{})), rest), LL.base_rev_go(Nat, B.word_desc(32n, w, off, Nil{}), rest)) : {_ == B.word_members(32n, w, off, rest) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, B.word_desc(32n, w, off, Nil{}), SC.append(Nat, SC.reverse(Nat, mm), Nil{}), desc_ok(32n, w, off, Nil{})) : {SC.append(Nat, SC.reverse(Nat, _), rest) == B.word_members(32n, w, off, rest) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SC.append(Nat, SC.reverse(Nat, mm), Nil{}), SC.reverse(Nat, mm), LL.append_nil(Nat, SC.reverse(Nat, mm))) : {SC.append(Nat, SC.reverse(Nat, _), rest) == B.word_members(32n, w, off, rest) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SC.reverse(Nat, SC.reverse(Nat, mm)), mm, LL.spec_rev_rev(Nat, mm)) : {SC.append(Nat, _, rest) == B.word_members(32n, w, off, rest) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, B.word_members(32n, w, off, rest), SC.append(Nat, mm, rest), wm_app(32n, w, off, rest))
