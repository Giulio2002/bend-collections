import Base

# bend-collections-laws-crypto: the proved laws of bend-collections' crypto and random: hashes, MAC, KDF, AEAD, password hashing, X25519, Ed25519, secp256k1, CSPRNG.
# Importing this file checks every proof root below; see docs/*_CONTRACTS.md
# for what each clause states and what is not proved. Part of
# bend-collections-laws (laws.bend imports all three parts by name).

import ./proofs/crypto/aead/proof.bend as CryptoAeadProof
import ./proofs/crypto/aead/safe.bend as CryptoAeadSafe
import ./proofs/crypto/aead/safe_open.bend as CryptoAeadSafeOpen
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
import ./proofs/crypto/poly1305/safe.bend as CryptoPoly1305Safe
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
