import Base
import ../../../src/crypto/aes/aes.bend as AES
import ../../../src/crypto/aesgcm.bend as GCM

# FIPS 197 Appendix C.1-C.3 and GCM test cases 2 and 14 of the GCM
# specification (McGrew-Viega; also NIST's): expected
#   69c4e0d86a7b0430d8cdb78070b4c55a
#   dda97ca4864cdfe06eaf70a0ec0d7191
#   8ea2b7ca516745bfeafc49904b496089
#   0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf
#   cea7403d4d606b6e074ec5d3baf39d18d0d1c8a799996bf0265b98b5d48ab919
#   00000000000000000000000000000000
# (the last: decrypting test case 2 gives the zero block back).
# Full vector and differential tests: tools/check_aes.py.

def hexs(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{bs}:
      AES.hex(bs)

def run_with(m: Maybe<&2, AES.Schedule>, block: List<&2, U32>) -> String:
  match m:
    case None{}:
      "badkey"
    case Some{s}:
      hexs(AES.encrypt_block(s, block))

def run(+key: List<&2, U32>, block: List<&2, U32>) -> String:
  run_with(AES.expand_key(key), block)

def reopen(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{ct}:
      hexs(GCM.aes128_gcm_decrypt(List.replicate(U32, 16n, 0), List.replicate(U32, 12n, 0), Nil{}, ct))

def main() -> IO(Unit):
  +pt = {[0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255] : List<&2, U32>}
  +z = {List.replicate(U32, 32n, 0) : List<&2, U32>}
  +z16 = {List.replicate(U32, 16n, 0) : List<&2, U32>}
  +z12 = {List.replicate(U32, 12n, 0) : List<&2, U32>}
  do IO<Unit>:
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], pt))
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], pt))
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], pt))
    IO.print(hexs(GCM.aes128_gcm_encrypt(z16, z12, Nil{}, z16)))
    IO.print(hexs(GCM.aes256_gcm_encrypt(z, z12, Nil{}, z16)))
    IO.print(reopen(GCM.aes128_gcm_encrypt(z16, z12, Nil{}, z16)))
