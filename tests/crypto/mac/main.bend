import Base
import ../../../src/crypto/mac.bend as MAC
import ../bytes.bend as B

# RFC 4231 section 4: HMAC-SHA-256 test cases 1-7 (case 5 truncated to
# 128 bits, as in the RFC), and verify on the RFC tags. Prints one
# "ok <name>" line per check; any "FAIL" line is a failure.

def tc(+name: String, +key: List<&2, U32>, +msg: List<&2, U32>, +want: String) -> IO(Unit):
  +tag = MAC.sign(key, msg)
  do IO<Unit>:
    B.check(name, B.hex(tag), want)
    B.check(name ++ " verify", B.show_bool(MAC.verify(key, msg, tag)), "true")
    B.check(name ++ " verify rfc tag", B.show_bool(MAC.verify(key, msg, B.unhex(want))), "true")

def flip(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> t:
      U32.xor(b, 1) <> t

def main() -> IO(Unit):
  +k1 = B.replicate(20n, 11)
  +m1 = B.ascii("Hi There")
  +t1 = MAC.sign(k1, m1)
  +k6 = B.replicate(131n, 170)
  do IO<Unit>:
    tc("rfc4231 case 1", k1, m1, "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
    tc("rfc4231 case 2", B.ascii("Jefe"), B.ascii("what do ya want for nothing?"), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
    tc("rfc4231 case 3", B.replicate(20n, 170), B.replicate(50n, 221), "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe")
    tc("rfc4231 case 4", B.unhex("0102030405060708090a0b0c0d0e0f10111213141516171819"), B.replicate(50n, 205), "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b")
    B.check("rfc4231 case 5 (128-bit truncation)", B.hex(List.take(&2, U32, MAC.sign(B.replicate(20n, 12), B.ascii("Test With Truncation")), 16n)), "a3b6167473100ee06e0c796c2955552b")
    tc("rfc4231 case 6", k6, B.ascii("Test Using Larger Than Block-Size Key - Hash Key First"), "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")
    tc("rfc4231 case 7", k6, B.ascii("This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."), "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")
    B.check("verify rejects a flipped bit", B.show_bool(MAC.verify(k1, m1, flip(t1))), "false")
    B.check("verify rejects a truncated tag", B.show_bool(MAC.verify(k1, m1, List.take(&2, U32, t1, 31n))), "false")
    B.check("verify rejects an extended tag", B.show_bool(MAC.verify(k1, m1, List.append(&2, U32, t1, [0]))), "false")
    B.check("verify rejects the empty tag", B.show_bool(MAC.verify(k1, m1, [])), "false")
    B.check("verify rejects another key", B.show_bool(MAC.verify(B.replicate(20n, 12), m1, t1)), "false")
    B.check("empty key and message", B.hex(MAC.sign([], [])), "b613679a0814d9ec772f95d778c35fc5ff1697c493715653c6c712144292c5ad")
    B.check("64-byte key is used as is", B.hex(MAC.sign(B.replicate(64n, 170), m1)), "ebef34e13d0a0fe04593d043bc7a865106db0604211d404c18206d862e5d7852")
    B.check("65-byte key is hashed", B.hex(MAC.sign(B.replicate(65n, 170), m1)), "00af6c42340b99e2e1d9a1cdf1547be431fe2e9bab3215c68d013ba858891927")
