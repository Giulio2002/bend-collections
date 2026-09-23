import Base
import ../../lib/array.bend as AR
import ./spec.bend as S
import ../../../src/containers/hash_table.bend as H
import ./state.bend as ST

# new: the empty map is a good shadow with the empty model.

def empty(~V: Data) -> ST.Sh<V>:
  ST.HS{0, 1n, 2, 0, 1, 0n, 0, 0, AR.trep(U32, 2n, 0), AR.trep(String, 0n, ""), AR.trep(Maybe<&2, V>, 0n, None{}), AR.trep(U32, 0n, 0)}

# THEOREM: new is the shadow of the empty specification map
def new_ok(~V: Data) -> {H.new(&2, V) == ST.real(~V, empty(~V)) : H.HashMap<&2, V>} & ({ST.good(~V, empty(~V)) == True{} : Bool} & {ST.model(~V, empty(~V)) == Nil{} : List<&2, S.Entry<V>>}):
  ({==}, ({==}, {==}))
