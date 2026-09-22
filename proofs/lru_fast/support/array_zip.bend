# Retained proof dependency: bend-collections@87deb98^:proofs/graph/zip.bend
# Only declarations needed by the LRU refinement are kept; no retired runtime is imported.
# Proof-only dependency extracted from retained LRU support; no retired collection API.
import Base
import ../../lib/logic.bend as L
import ../../../spec/common.bend as SC

def vget(-T: Data, +d: T, +xs: List<&2, T>, +i: Nat) -> T:
  L.some_value(T, SC.nth(T, xs, i), d)
