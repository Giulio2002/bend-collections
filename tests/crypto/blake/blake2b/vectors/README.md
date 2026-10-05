`blake2b-kat.txt`: the keyed BLAKE2b-512 known-answer tests of the BLAKE2 reference
implementation (github.com/BLAKE2/BLAKE2 `testvectors/blake2b-kat.txt`, commit
ed1974ea83433eba7b2d95c5dcd9ac33cb847913, CC0 1.0): key 00..3f, input 00..(n-1) for
n = 0..255. Read by `tools/generators/blake2b_gen.py` for `tests/crypto/blake/blake2b/params.bend`.
