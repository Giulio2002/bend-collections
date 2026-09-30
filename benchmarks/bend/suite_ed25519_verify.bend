import Base
import ./suite.bend as S
import ../../src/crypto/sign.bend as E
import ../../src/crypto/ed25519/ed25519.bend as ED

# Ed25519 verification (src/crypto/sign.bend verify_ctx): every message is
# signed under a fixed seed (pattern(32, 13, 7)) before the timed region,
# then every signature is verified; the output is 1 byte (valid or not). The
# curve constants and the base point (context) are computed once before the
# timed region, as C keeps them in static tables; the public key is decoded
# in every call, as in C.
# C: Monocypher 4.0.2 crypto_ed25519_check.

def public(m: Maybe<&2, E.Keypair>) -> List<&2, U32>:
  match m:
    case None{}:
      [256]
    case Some{E.Keypair{sk, pk}}:
      pk

def sigs(xs: List<&2, List<&2, U32>>, +sk: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      S.unwrap(E.sign(sk, h)) <> sigs(t, sk)

def run(xs: List<&2, List<&2, U32>>, ss: List<&2, List<&2, U32>>, +ctx: ED.Ctx, +pk: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs ss:
    case h <> t g <> u:
      run(t, u, ctx, pk, S.bit(E.verify_ctx(ctx, pk, h, g)) <> acc)
    case _ _:
      acc

def main() -> IO(Unit):
  do IO<Unit>:
    inputs : List<&2, List<&2, U32>> <- S.messages()
    msgs : List<&2, List<&2, U32>> <- S.messages()
    +sk : List<&2, U32> = S.pattern(32n, 13, 7)
    +pk : List<&2, U32> = public(E.generate_keypair(sk))
    signatures : List<&2, List<&2, U32>> = sigs(inputs, sk)
    +ctx : ED.Ctx = E.context(Nil{})
    start : Nat <- IO.now()
    outs : List<&2, List<&2, U32>> = run(msgs, signatures, ctx, pk, Nil{})
    stop : Nat <- IO.now()
    S.report(start, stop, outs)
