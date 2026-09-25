import Base
import ../../lib/array.bend as AR
import ../../../spec/containers/lru.bend as SP
import ../../../src/containers/lru.bend as LR
import ./state.bend as ST
import ../../lib/words32.bend as W32

# new: the implementation's new is the specification's new.

def empty(~V: Data, +cap: U32) -> ST.Sh<V>:
  ST.LS{cap, 0, 0, 0, 0, AR.freeze(U32, LR.meta0()), 1n, 0n, AR.freeze(U32, Array.new(U32, 2n, 0)), AR.freeze(String, Array.new(String, 0n, "")), AR.TLeaf{None{}}, AR.freeze(U32, Array.new(U32, 3n, 0)), Nil{}, Nil{}}

def MadeOK(~V: Data, r: LR.Made<&2, V>, s: SP.Made<V>) -> Type:
  match r s:
    case LR.Made{f} SP.Made{l}:
      Sigma<&1, &1, ST.Sh<V>, sh => {f == ST.real(~V, sh) : LR.LRU<&2, V>} & ({l == ST.model(~V, sh) : SP.Lru<V>} & {ST.good(~V, sh) == True{} : Bool})>
    case LR.Made{f} SP.Rejected{b}:
      Empty
    case LR.Rejected{a} SP.Made{l}:
      Empty
    case LR.Rejected{a} SP.Rejected{b}:
      {a == b : String}

def good_empty(~V: Data, +cap: U32, +hz: {U32.is_eq(cap, 0) == False{} : Bool}) -> {ST.good(~V, empty(~V, cap)) == True{} : Bool}:
  +m = AR.freeze(U32, LR.meta0())
  +t = AR.freeze(U32, Array.new(U32, 2n, 0))
  +kt = AR.freeze(String, Array.new(String, 0n, ""))
  +l = AR.freeze(U32, Array.new(U32, 3n, 0))
  +kl = AR.slots(String, kt)
  +pk = AR.perfect(String, 0n, kt)
  +e = {AR.TLeaf{None{}} : AR.Tree<Maybe<&2, V>>}
  ST.good_intro(~V, cap, 0, 0, 0, 0, W32.nth0(AR.slots(U32, m), 0n), W32.nth0(AR.slots(U32, m), 1n), W32.nth0(AR.slots(U32, m), 2n), W32.nth0(AR.slots(U32, m), 6n), W32.nth0(AR.slots(U32, m), 7n), AR.perfect(U32, 5n, m), 1n, 0n, t, kl, pk, e, l, Nil{}, Nil{}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, Equal.cong(Bool, Bool, b => Bool.not(b), U32.is_eq(cap, 0), False{}, hz), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def new_c(~V: Data, +cap: U32, +z: Bool, +hz: {U32.is_eq(cap, 0) == z : Bool}, +r: Bool) -> MadeOK(~V, LR.new_checked(&2, V, cap, z, r), SP.new_c(~V, cap, z, r)):
  match z r:
    case True{} r2:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      (empty(~V, cap), ({==}, ({==}, good_empty(~V, cap, hz))))

# THEOREM: new rejects what the specification rejects, with its reason, and
# otherwise builds the specification's empty cache.
def new_ok(~V: Data, +cap: U32) -> MadeOK(~V, LR.new(&2, V, cap), SP.new(~V, cap)):
  new_c(~V, cap, U32.is_eq(cap, 0), {==}, U32.is_eq(cap, 4294967295))
