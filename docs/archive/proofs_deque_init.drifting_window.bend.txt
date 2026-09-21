import Base
import ../lib/logic.bend as L
import ../lib/nat.bend as N
import ../lib/list.bend as LL
import ../lib/array.bend as AR
import ../../spec/common.bend as SC
import ../../src/deque.bend as DQ
import ../dynamic_array/layout.bend as LY
import ./layout.bend as WN
import ./state.bend as ST

# The constructor: one empty slot, an empty window.

def initial(-T: Data) -> ST.Shadow<T>:
  {ST.Sh{0n, 0n, 0n, AR.trep(Maybe<&2, T>, 0n, None{})} : ST.Shadow<T>}

def new_real(-T: Data) -> {DQ.new(T) == ST.real(T, initial(T)) : DQ.Deque<T>}:
  Equal.cong(Array<Maybe<&2, T>>, DQ.Deque<T>, a => DQ.DQ{0n, 1n, 0n, 0n, a},
    DQ.empty_slots(T, 0n), AR.thaw(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})),
    ST.empty_eq(T, 0n))

def new_good(-T: Data) -> {ST.good(T, initial(T)) == True{} : Bool}:
  ST.good_intro(T, 0n, 0n, 0n, AR.trep(Maybe<&2, T>, 0n, None{}),
    {==},
    AR.trep_perfect(Maybe<&2, T>, 0n, None{}),
    L.subst(List<&2, Maybe<&2, T>>, zs => {WN.win(T, zs, 0n, 0n) == True{} : Bool}, SC.replicate(Maybe<&2, T>, SC.pow2(0n), None{}), AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})), Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(0n), None{}), AR.trep_slots(Maybe<&2, T>, 0n, None{})),
      WN.lay_win(T, SC.replicate(Maybe<&2, T>, SC.pow2(0n), None{}), 0n, LY.lay_rep(T, SC.pow2(0n)))))

def new_model(-T: Data) -> {ST.model(T, initial(T)) == Nil{} : List<&2, T>}:
  %Equal.sym(List<&2, Maybe<&2, T>>, AR.slots(Maybe<&2, T>, AR.trep(Maybe<&2, T>, 0n, None{})), SC.replicate(Maybe<&2, T>, SC.pow2(0n), None{}), AR.trep_slots(Maybe<&2, T>, 0n, None{})) : {LY.somes(T, _) == Nil{} : List<&2, T>}
  LY.somes_rep(T, SC.pow2(0n))

def new_depth(-T: Data) -> {ST.Sh{0n, 0n, 0n, AR.trep(Maybe<&2, T>, 0n, None{})} == initial(T) : ST.Shadow<T>}:
  {==}
