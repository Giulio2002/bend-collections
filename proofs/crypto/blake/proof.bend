import Base
import ./blake2s/proof.bend as Blake2s
import ./blake2b/proof.bend as Blake2b
import ./blake3/proof.bend as Blake3

# The BLAKE package: BLAKE2s, BLAKE2b and BLAKE3, each proved equal to its
# independent specification (RFC 7693, the BLAKE3 specification) for every
# packed input array and byte length.
