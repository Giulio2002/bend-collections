import Base
import ../lib/numeric.bend as N
import ../../src/math/hash.bend as H

# Specification of src/math/hash.bend: every bucket index a hash can take
# lies inside its table.
#
#   function   clauses                  proved in
#   bucket     Bucket.le, Bucket.lt     proofs/math/proof.bend (hash_bucket_le/lt)

# bucket(w, mask) never exceeds the mask
def Bucket.le(+w: U32, +mask: U32) -> Type:
  {Nat.is_le(U32.to_nat(H.bucket(w, mask)), U32.to_nat(mask)) == True{} : Bool}

# with mask = 2^k - 1 (the low k bits) the bucket indexes a table of 2^k
def Bucket.lt(+w: U32, +k: Nat, +mask: U32, +hm: {mask == U32{N.mask(32n, k)} : U32}) -> Type:
  {Nat.is_lt(U32.to_nat(H.bucket(w, mask)), N.scale_binary(k, 1n)) == True{} : Bool}
