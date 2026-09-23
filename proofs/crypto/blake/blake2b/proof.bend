import Base
import ./laws.bend as Laws
import ./compress.bend as C
import ./blocks.bend as B
import ./api.bend as A

# Gate for the BLAKE2b-512 package: `bend proofs/crypto/blake/blake2b/proof.bend`
# prints "All terms check." when every law of laws.bend holds.
def Laws.blake2b_correct(words,byte_length): B.blake2b_correct(words,byte_length)
def Laws.compress_correct(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31): C.compress_correct(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31)
def Laws.compress_last_correct(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31): C.compress_last_correct(h,t,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15,w16,w17,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27,w28,w29,w30,w31)
def Laws.digest_size(h): A.digest_size(h)
def Laws.capacity_rejection(a,n,capacity,invalid): A.capacity_gate(a,n,capacity,invalid)
