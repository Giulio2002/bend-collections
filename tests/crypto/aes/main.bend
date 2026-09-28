import Base
import ../../../src/crypto/aes/aes.bend as AES

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

def main() -> IO(Unit):
  +pt = {[0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255] : List<&2, U32>}
  do IO<Unit>:
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], pt))
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], pt))
    IO.print(run([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], pt))
