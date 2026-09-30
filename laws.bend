import Base

# bend-collections-laws: every proved clause of bend-collections, in one entry.
#
# Importing this file checks every proof root of the library (proofs/prove.py
# --list), so a package that imports it gets all the laws: the containers'
# SPARK-style contracts, the math contracts, and the crypto and random
# refinements (each implementation equal to its standard's executable
# specification, for every input). Import a single package's laws by its
# root instead, e.g.
#
#   import bend-collections-laws@1.0.0.0/proofs/crypto/aead/proof.bend as AeadLaws
#
# What is and is not proved is listed in docs/*_CONTRACTS.md.

import ./proofs/END_TO_END.bend as ENDTOEND
import ./proofs/PROOF.bend as PROOF
import ./proofs/containers/balanced_search_tree/components.bend as ContainersBalancedSearchTreeComponents
import ./proofs/containers/balanced_search_tree/proof.bend as ContainersBalancedSearchTreeProof
import ./proofs/containers/balanced_search_tree/range.bend as ContainersBalancedSearchTreeRange
import ./proofs/containers/bitlist/proof.bend as ContainersBitlistProof
import ./proofs/containers/bitset/proof.bend as ContainersBitsetProof
import ./proofs/containers/deque/proof.bend as ContainersDequeProof
import ./proofs/containers/dlist_iterator/proof.bend as ContainersDlistIteratorProof
import ./proofs/containers/doubly_linked_list/direct_laws.bend as ContainersDoublyLinkedListDirectLaws
import ./proofs/containers/doubly_linked_list/proof.bend as ContainersDoublyLinkedListProof
import ./proofs/containers/dynamic_array/proof.bend as ContainersDynamicArrayProof
import ./proofs/containers/hash_table/proof.bend as ContainersHashTableProof
import ./proofs/containers/intrusive_doubly_linked_list/proof.bend as ContainersIntrusiveDoublyLinkedListProof
import ./proofs/containers/lru/proof.bend as ContainersLruProof
import ./proofs/containers/priority_queue/proof.bend as ContainersPriorityQueueProof
import ./proofs/containers/simple_queue/proof.bend as ContainersSimpleQueueProof
import ./proofs/containers/stack/components.bend as ContainersStackComponents
import ./proofs/crypto/aead/proof.bend as CryptoAeadProof
import ./proofs/crypto/aes/proof.bend as CryptoAesProof
import ./proofs/crypto/argon2/proof.bend as CryptoArgon2Proof
import ./proofs/crypto/blake/proof.bend as CryptoBlakeProof
import ./proofs/crypto/chacha/proof.bend as CryptoChachaProof
import ./proofs/crypto/curve25519/proof.bend as CryptoCurve25519Proof
import ./proofs/crypto/ed25519/proof.bend as CryptoEd25519Proof
import ./proofs/crypto/hash/proof.bend as CryptoHashProof
import ./proofs/crypto/kdf/proof.bend as CryptoKdfProof
import ./proofs/crypto/mac/proof.bend as CryptoMacProof
import ./proofs/crypto/poly1305/proof.bend as CryptoPoly1305Proof
import ./proofs/crypto/random/proof.bend as CryptoRandomProof
import ./proofs/crypto/secp256k1/proof.bend as CryptoSecp256k1Proof
import ./proofs/crypto/secp256k1/proof_recover.bend as CryptoSecp256k1ProofRecover
import ./proofs/crypto/secp256k1/proof_schnorr.bend as CryptoSecp256k1ProofSchnorr
import ./proofs/crypto/secp256k1/proof_sign.bend as CryptoSecp256k1ProofSign
import ./proofs/crypto/secp256k1/proof_verify.bend as CryptoSecp256k1ProofVerify
import ./proofs/crypto/sha/packed/proof.bend as CryptoShaPackedProof
import ./proofs/crypto/sha/proof.bend as CryptoShaProof
import ./proofs/crypto/sha3/proof.bend as CryptoSha3Proof
import ./proofs/crypto/sha512/proof.bend as CryptoSha512Proof
import ./proofs/lib/array2.bend as LibArray2
import ./proofs/lib/flat.bend as LibFlat
import ./proofs/lib/lemmas/proofs/public_trace.bend as LibLemmasPublicTrace
import ./proofs/lib/u32seq.bend as LibU32seq
import ./proofs/lib/vec.bend as LibVec
import ./proofs/math/number/proof.bend as MathNumberProof
import ./proofs/math/proof.bend as MathProof
import ./proofs/math/random/proof.bend as MathRandomProof
import ./proofs/math/random/proof_draws.bend as MathRandomProofDraws
import ./proofs/math/random/proof_float.bend as MathRandomProofFloat
import ./proofs/math/random/proof_pcg.bend as MathRandomProofPcg
import ./proofs/math/typed/examples.bend as MathTypedExamples
import ./proofs/math/typed/f64close.bend as MathTypedF64close
import ./proofs/math/typed/f64divc.bend as MathTypedF64divc
import ./proofs/math/typed/f64fmod.bend as MathTypedF64fmod
import ./proofs/math/typed/f64misc.bend as MathTypedF64misc
import ./proofs/math/typed/f64modf.bend as MathTypedF64modf
import ./proofs/math/typed/f64next.bend as MathTypedF64next
import ./proofs/math/typed/f64ofnat.bend as MathTypedF64ofnat
import ./proofs/math/typed/f64ratio.bend as MathTypedF64ratio
import ./proofs/math/typed/f64sqc.bend as MathTypedF64sqc
import ./proofs/math/typed/float.bend as MathTypedFloat
import ./spec/containers/balanced_search_tree/recursive.bend as SpecContainersBalancedSearchTreeRecursive
