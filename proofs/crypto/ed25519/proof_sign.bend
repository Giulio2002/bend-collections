import Base
import ../../../spec/crypto/curve25519/field.bend as FS
import ../../../spec/crypto/ed25519.bend as SE
import ./tsigncore.bend as TK
import ./pbase.bend as PB
import ./fbspec.bend as FB

# Gate: Ed25519.sign and Ed25519.sign_key (Ed25519.sign_ctx is proved in
# tsigncore.bend, shared with proof_sign_facade.bend).

def ed_sign(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}) -> SE.Ed25519.sign(one, h1, seed, msg, hs):
  TK.ed_sign_one(one, h1, seed, msg, hs)

def ed_sign_key(+one: Nat, +h1: {one == 1n : Nat}, +seed: List<&2, U32>, +msg: List<&2, U32>, +hs: {FS.tight(seed) == True{} : Bool}, lw1: FB.LawE(one, PB.pp1(one)), lw2: FB.LawE(one, PB.pp1(one))) -> SE.Ed25519.sign_key(one, h1, seed, msg, hs):
  TK.ed_sign_ctx(one, h1, seed, seed, msg, hs, lw1, lw2)
