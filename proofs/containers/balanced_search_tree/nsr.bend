import Base
import ../../../spec/lib/common.bend as SC
import ../../lib/array.bend as AR
import ../../../src/containers/balanced_search_tree.bend as M
import ./bk.bend as BK

# The TreeMap's node store realized from a node list: the links array of two
# halves, each a block (bk.bend) of depth 1 + d holding two fields of every
# node side by side (nleft and nright in the low half, ntag and nparent in
# the high one), and the key block (nkey), all padded with the encoding of
# Free{0}.


def lrs(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{M.nleft(~K, x), Con{M.nright(~K, x), lrs(~K, r)}}

def tps(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, r}:
      Con{M.ntag(~K, x), Con{M.nparent(~K, x), tps(~K, r)}}


def keys(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Maybe<&2, K>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.nkey(~K, x), keys(~K, r)}

def real(~K: Data, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>) -> M.NodeStore<K>:
  M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, nl), AR.thaw(Nat, AR.TNode{BK.bk(Nat, 1n+d, lrs(~K, nl), 0n), BK.bk(Nat, 1n+d, tps(~K, nl), 0n)}), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, keys(~K, nl), None{}))}
