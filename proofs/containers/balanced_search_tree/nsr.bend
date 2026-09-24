import Base
import ../../lib/spec_common.bend as SC
import ../../lib/array.bend as AR
import ../../../src/containers/balanced_search_tree.bend as M
import ./bk.bend as BK

# The TreeMap's node store realized from a node list: one block per field
# (bk.bend), each holding that field of every node (ntag, nleft, nright,
# nparent, nkey) padded with the encoding of Free{0}.


def tags(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.ntag(~K, x), tags(~K, r)}

def lefts(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.nleft(~K, x), lefts(~K, r)}

def rights(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.nright(~K, x), rights(~K, r)}

def parents(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.nparent(~K, x), parents(~K, r)}

def keys(~K: Data, xs: List<&2, M.Node<K>>) -> List<&2, Maybe<&2, K>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{M.nkey(~K, x), keys(~K, r)}


def real(~K: Data, +l: Nat, +d: Nat, +nl: List<&2, M.Node<K>>) -> M.NodeStore<K>:
  M.NS{l, d, SC.pow2(d), SC.length(M.Node<K>, nl), AR.thaw(Nat, BK.bk(Nat, d, tags(~K, nl), 0n)), AR.thaw(Nat, BK.bk(Nat, d, lefts(~K, nl), 0n)), AR.thaw(Nat, BK.bk(Nat, d, rights(~K, nl), 0n)), AR.thaw(Nat, BK.bk(Nat, d, parents(~K, nl), 0n)), AR.thaw(Maybe<&2, K>, BK.bk(Maybe<&2, K>, d, keys(~K, nl), None{}))}
