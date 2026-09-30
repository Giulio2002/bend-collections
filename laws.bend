import Base

# bend-collections-laws: every proved clause of bend-collections, in one entry.
#
# The laws are published in three parts (BendHub caps a package at 16 MiB);
# importing this file imports all three, which checks every proof root of the
# library: the containers' SPARK-style contracts, the math contracts, and the
# crypto and random refinements (each implementation equal to its standard's
# executable specification, for every input). Import one part, or one
# package's root inside it, when you need only those laws, e.g.
#
#   import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/aead/proof.bend as AeadLaws
#
# What is and is not proved is listed in docs/*_CONTRACTS.md.

import bend-collections-laws-containers@1.0.0.0/laws_containers.bend as Containers
import bend-collections-laws-math@1.0.0.0/laws_math.bend as Math
import bend-collections-laws-crypto@1.0.0.0/laws_crypto.bend as Crypto
