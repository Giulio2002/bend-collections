import Base
import ./laws.bend as Laws
import ./permutation.bend as P
import ./api.bend as A
import ./sponge.bend as S

def Laws.permutation_rounds(n,i,s): P.rounds_correct(n,i,s)
def Laws.digest_size(s): A.digest_size(s)
def Laws.capacity_rejection(a,n,capacity,invalid): A.capacity_gate(a,n,capacity,invalid)

def Laws.packed_sponge_correct(r,a,length): S.hash_correct(r,a,length)
def Laws.ethereum_round_count(a,length): S.ethereum_round_count(a,length)
def Laws.ethereum_keccak256(a,length): S.public_correct(a,length)
