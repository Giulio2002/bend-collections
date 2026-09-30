import Base
import ../../../lib/lemmas/proofs/nat_algebra.bend as NA
import ../../../lib/logic.bend as Lg
import ../../../lib/nat.bend as N
import ../../../../spec/lib/common.bend as C
import ../../../../spec/crypto/secp256k1/field.bend as FS
import ../../../../spec/crypto/secp256k1/curve.bend as CS
import ../../../../spec/crypto/secp256k1/ecdsa.bend as ES
import ./enco.bend as EO
import ./ecda.bend as AR

# The specification's ECDSA functions (spec/crypto/secp256k1/ecdsa.bend)
# step by step: the octets of a signature r || s || v, and verify / recover
# reduced to their checks once the lengths, the decoded key, the scalars
# and the recovery id are known. No group law here.

# r || s and r || s || v
def s64(+r: Nat, +sl: Nat) -> LU:
  List.append(&2, U32, CS.i2osp(32n, r), CS.i2osp(32n, sl))

def sg(+r: Nat, +sl: Nat, +v: U32) -> LU:
  ES.cat(ES.i2osp32(r), ES.cat(ES.i2osp32(sl), [v]))

def b_first64(+r: Nat, +sl: Nat, +v: U32) -> {CS.first(64n, sg(r, sl, v)) == s64(r, sl) : LU}:
  ETR(LU, CS.first(64n, sg(r, sl, v)), List.append(&2, U32, CS.i2osp(32n, r), CS.first(32n, List.append(&2, U32, CS.i2osp(32n, sl), [v]))), s64(r, sl),
    AR.first_cat(CS.i2osp(32n, r), 32n, 32n, List.append(&2, U32, CS.i2osp(32n, sl), [v]), EO.len_i2(32n, r)),
    Equal.cong(LU, LU, l => List.append(&2, U32, CS.i2osp(32n, r), l), CS.first(32n, List.append(&2, U32, CS.i2osp(32n, sl), [v])), CS.i2osp(32n, sl), EO.first_app(CS.i2osp(32n, sl), 32n, [v], EO.len_i2(32n, sl))))

def b_r(+r: Nat, +sl: Nat, +hf: {C.fits(256n, r) == True{} : Bool}) -> {CS.os2ip(CS.first(32n, s64(r, sl))) == r : Nat}:
  ETR(Nat, CS.os2ip(CS.first(32n, s64(r, sl))), CS.os2ip(CS.i2osp(32n, r)), r, Equal.cong(LU, Nat, l => CS.os2ip(l), CS.first(32n, s64(r, sl)), CS.i2osp(32n, r), EO.first_app(CS.i2osp(32n, r), 32n, CS.i2osp(32n, sl), EO.len_i2(32n, r))), EO.os_i2_32(r, hf))

def b_s(+r: Nat, +sl: Nat, +hf: {C.fits(256n, sl) == True{} : Bool}) -> {CS.os2ip(CS.after(32n, s64(r, sl))) == sl : Nat}:
  ETR(Nat, CS.os2ip(CS.after(32n, s64(r, sl))), CS.os2ip(CS.i2osp(32n, sl)), sl, Equal.cong(LU, Nat, l => CS.os2ip(l), CS.after(32n, s64(r, sl)), CS.i2osp(32n, sl), EO.after_app(CS.i2osp(32n, r), 32n, CS.i2osp(32n, sl), EO.len_i2(32n, r))), EO.os_i2_32(sl, hf))

def b_len64(+r: Nat, +sl: Nat) -> {CS.length_is(64n, s64(r, sl)) == True{} : Bool}:
  %ESYM(Nat, List.length(&2, U32, s64(r, sl)), Nat.add(List.length(&2, U32, CS.i2osp(32n, r)), List.length(&2, U32, CS.i2osp(32n, sl))), AR.len_app(CS.i2osp(32n, r), CS.i2osp(32n, sl))) : {Nat.is_eq(_, 64n) == True{} : Bool}
  %ESYM(Nat, List.length(&2, U32, CS.i2osp(32n, r)), 32n, EO.len_i2(32n, r)) : {Nat.is_eq(Nat.add(_, List.length(&2, U32, CS.i2osp(32n, sl))), 64n) == True{} : Bool}
  %ESYM(Nat, List.length(&2, U32, CS.i2osp(32n, sl)), 32n, EO.len_i2(32n, sl)) : {Nat.is_eq(Nat.add(32n, _), 64n) == True{} : Bool}
  {==}

def b_r2(+r: Nat, +sl: Nat, +v: U32, +hf: {C.fits(256n, r) == True{} : Bool}) -> {CS.os2ip(CS.first(32n, sg(r, sl, v))) == r : Nat}:
  ETR(Nat, CS.os2ip(CS.first(32n, sg(r, sl, v))), CS.os2ip(CS.i2osp(32n, r)), r, Equal.cong(LU, Nat, l => CS.os2ip(l), CS.first(32n, sg(r, sl, v)), CS.i2osp(32n, r), EO.first_app(CS.i2osp(32n, r), 32n, List.append(&2, U32, CS.i2osp(32n, sl), [v]), EO.len_i2(32n, r))), EO.os_i2_32(r, hf))

def b_mid(+r: Nat, +sl: Nat, +v: U32) -> {CS.first(32n, CS.after(32n, sg(r, sl, v))) == CS.i2osp(32n, sl) : LU}:
  %ESYM(LU, CS.after(32n, sg(r, sl, v)), List.append(&2, U32, CS.i2osp(32n, sl), [v]), EO.after_app(CS.i2osp(32n, r), 32n, List.append(&2, U32, CS.i2osp(32n, sl), [v]), EO.len_i2(32n, r))) : {CS.first(32n, _) == CS.i2osp(32n, sl) : LU}
  EO.first_app(CS.i2osp(32n, sl), 32n, [v], EO.len_i2(32n, sl))

def b_s2(+r: Nat, +sl: Nat, +v: U32, +hf: {C.fits(256n, sl) == True{} : Bool}) -> {CS.os2ip(CS.first(32n, CS.after(32n, sg(r, sl, v)))) == sl : Nat}:
  ETR(Nat, CS.os2ip(CS.first(32n, CS.after(32n, sg(r, sl, v)))), CS.os2ip(CS.i2osp(32n, sl)), sl, Equal.cong(LU, Nat, l => CS.os2ip(l), CS.first(32n, CS.after(32n, sg(r, sl, v))), CS.i2osp(32n, sl), b_mid(r, sl, v)), EO.os_i2_32(sl, hf))

def b_v(+r: Nat, +sl: Nat, +v: U32) -> {CS.head(CS.after(64n, sg(r, sl, v))) == v : U32}:
  %ESYM(LU, CS.after(64n, sg(r, sl, v)), CS.after(32n, List.append(&2, U32, CS.i2osp(32n, sl), [v])), AR.after_cat(CS.i2osp(32n, r), 32n, 32n, List.append(&2, U32, CS.i2osp(32n, sl), [v]), EO.len_i2(32n, r))) : {CS.head(_) == v : U32}
  %ESYM(LU, CS.after(32n, List.append(&2, U32, CS.i2osp(32n, sl), [v])), [v], EO.after_app(CS.i2osp(32n, sl), 32n, [v], EO.len_i2(32n, sl))) : {CS.head(_) == v : U32}
  {==}

def b_len65(+r: Nat, +sl: Nat, +v: U32) -> {CS.length_is(65n, sg(r, sl, v)) == True{} : Bool}:
  %ESYM(Nat, List.length(&2, U32, sg(r, sl, v)), Nat.add(List.length(&2, U32, CS.i2osp(32n, r)), List.length(&2, U32, List.append(&2, U32, CS.i2osp(32n, sl), [v]))), AR.len_app(CS.i2osp(32n, r), List.append(&2, U32, CS.i2osp(32n, sl), [v]))) : {Nat.is_eq(_, 65n) == True{} : Bool}
  %ESYM(Nat, List.length(&2, U32, List.append(&2, U32, CS.i2osp(32n, sl), [v])), Nat.add(List.length(&2, U32, CS.i2osp(32n, sl)), 1n), AR.len_app(CS.i2osp(32n, sl), [v])) : {Nat.is_eq(Nat.add(List.length(&2, U32, CS.i2osp(32n, r)), _), 65n) == True{} : Bool}
  %ESYM(Nat, List.length(&2, U32, CS.i2osp(32n, r)), 32n, EO.len_i2(32n, r)) : {Nat.is_eq(Nat.add(_, Nat.add(List.length(&2, U32, CS.i2osp(32n, sl)), 1n)), 65n) == True{} : Bool}
  %ESYM(Nat, List.length(&2, U32, CS.i2osp(32n, sl)), 32n, EO.len_i2(32n, sl)) : {Nat.is_eq(Nat.add(32n, Nat.add(_, 1n)), 65n) == True{} : Bool}
  {==}

# ---- verify, from its parts ----

def ver_g(+one: Nat, +q: CS.SPoint, +h: LU, +strict: Bool, +r: Nat, +sl: Nat, +hok: {OK3(r, sl, strict) == True{} : Bool}, +hv: {ES.verify_rs(one, q, HS, r, sl) == True{} : Bool}) -> {ES.verify_ok(one, q, HS, r, sl, OK3(r, sl, strict)) == True{} : Bool}:
  %ESYM(Bool, OK3(r, sl, strict), True{}, hok) : {ES.verify_ok(one, q, HS, r, sl, _) == True{} : Bool}
  hv

def ver_q(+one: Nat, +q: CS.SPoint, +h: LU, +sig: LU, +strict: Bool, +r: Nat, +sl: Nat, +hr: {CS.os2ip(CS.first(32n, sig)) == r : Nat}, +hs: {CS.os2ip(CS.after(32n, sig)) == sl : Nat}, +hok: {OK3(r, sl, strict) == True{} : Bool}, +hv: {ES.verify_rs(one, q, HS, r, sl) == True{} : Bool}) -> {ES.verify_q(one, h, sig, strict, Some{q}) == True{} : Bool}:
  Lg.subst(Nat, z => {ES.verify_ok(one, q, HS, z, CS.os2ip(CS.after(32n, sig)), OK3(z, CS.os2ip(CS.after(32n, sig)), strict)) == True{} : Bool}, r, CS.os2ip(CS.first(32n, sig)), ESYM(Nat, CS.os2ip(CS.first(32n, sig)), r, hr),
    Lg.subst(Nat, z => {ES.verify_ok(one, q, HS, r, z, OK3(r, z, strict)) == True{} : Bool}, sl, CS.os2ip(CS.after(32n, sig)), ESYM(Nat, CS.os2ip(CS.after(32n, sig)), sl, hs), ver_g(one, q, h, strict, r, sl, hok, hv)))

def ver_a(+one: Nat, +pk: LU, +h: LU, +sig: LU, +strict: Bool, +q: CS.SPoint, +hl: {Bool.and(CS.length_is(32n, h), CS.length_is(64n, sig)) == True{} : Bool}, +hdec: {CS.decode(ES.p(one), pk) == Some{q} : Maybe<&2, CS.SPoint>}, +hq: {ES.verify_q(one, h, sig, strict, Some{q}) == True{} : Bool}) -> {ES.verify(one, pk, h, sig, strict) == True{} : Bool}:
  %ESYM(Bool, Bool.and(CS.length_is(32n, h), CS.length_is(64n, sig)), True{}, hl) : {ES.verify_len(one, pk, h, sig, strict, _) == True{} : Bool}
  %ESYM(MSP, CS.decode(ES.p(one), pk), Some{q}, hdec) : {ES.verify_q(one, h, sig, strict, _) == True{} : Bool}
  hq

# ---- recover, from its parts ----

# the recovery sum [-e / r] G + [s / r] R
def qrO(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +pr: CS.SPoint) -> CS.SPoint:
  CS.padd(ES.p(one), CS.pmul(ES.p(one), FS.mmul(ES.n(one), FS.mneg(ES.n(one), e), FS.minv(ES.n(one), r)), CS.g(one)), CS.pmul(ES.p(one), FS.mmul(ES.n(one), s, FS.minv(ES.n(one), r)), pr))

def rec_e(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +pr: CS.SPoint, +enc: LU, +hinf: {CS.is_inf(qrO(one, e, r, s, pr)) == False{} : Bool}, +henc: {CS.encode_uncompressed(ES.p(one), qrO(one, e, r, s, pr)) == enc : LU}) -> {ES.recover_r(one, e, r, s, Some{pr}) == Some{enc} : Maybe<&2, LU>}:
  %ESYM(Bool, CS.is_inf(qrO(one, e, r, s, pr)), False{}, hinf) : {ES.recover_q_if(one, qrO(one, e, r, s, pr), _) == Some{enc} : Maybe<&2, LU>}
  Equal.cong(LU, Maybe<&2, LU>, z => Some{z}, CS.encode_uncompressed(ES.p(one), qrO(one, e, r, s, pr)), enc, henc)

def rec_d1(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat, +x: Nat, +pr: CS.SPoint, +res: Maybe<&2, LU>, +hlt: {Nat.is_lt(x, ES.p(one)) == True{} : Bool}, +hdc: {CS.decompress(ES.p(one), x, Nat.mod(id, 2n)) == Some{pr} : Maybe<&2, CS.SPoint>}, +hr: {ES.recover_r(one, e, r, s, Some{pr}) == res : Maybe<&2, LU>}) -> {ES.recover_x_if(one, e, r, s, id, x, Nat.is_lt(x, ES.p(one))) == res : Maybe<&2, LU>}:
  %ESYM(Bool, Nat.is_lt(x, ES.p(one)), True{}, hlt) : {ES.recover_x_if(one, e, r, s, id, x, _) == res : Maybe<&2, LU>}
  %ESYM(MSP, CS.decompress(ES.p(one), x, Nat.mod(id, 2n)), Some{pr}, hdc) : {ES.recover_r(one, e, r, s, _) == res : Maybe<&2, LU>}
  hr

def rec_d(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat, +x: Nat, +pr: CS.SPoint, +res: Maybe<&2, LU>, +hxp: {Nat.add(r, Nat.mul(Nat.div(id, 2n), ES.n(one))) == x : Nat}, +hlt: {Nat.is_lt(x, ES.p(one)) == True{} : Bool}, +hdc: {CS.decompress(ES.p(one), x, Nat.mod(id, 2n)) == Some{pr} : Maybe<&2, CS.SPoint>}, +hr: {ES.recover_r(one, e, r, s, Some{pr}) == res : Maybe<&2, LU>}) -> {ES.recover_x(one, e, r, s, id) == res : Maybe<&2, LU>}:
  Lg.subst(Nat, z => {ES.recover_x_if(one, e, r, s, id, z, Nat.is_lt(z, ES.p(one))) == res : Maybe<&2, LU>}, x, Nat.add(r, Nat.mul(Nat.div(id, 2n), ES.n(one))), ESYM(Nat, Nat.add(r, Nat.mul(Nat.div(id, 2n), ES.n(one))), x, hxp), rec_d1(one, e, r, s, id, x, pr, res, hlt, hdc, hr))

def rec_c(+one: Nat, +e: Nat, +r: Nat, +s: Nat, +id: Nat, +res: Maybe<&2, LU>, +hok: {OKR(r, s, id) == True{} : Bool}, +hx: {ES.recover_x(one, e, r, s, id) == res : Maybe<&2, LU>}) -> {ES.recover_ok(one, e, r, s, id, OKR(r, s, id)) == res : Maybe<&2, LU>}:
  %ESYM(Bool, OKR(r, s, id), True{}, hok) : {ES.recover_ok(one, e, r, s, id, _) == res : Maybe<&2, LU>}
  hx

def rec_a(+one: Nat, +h: LU, +sig: LU, +r: Nat, +s: Nat, +id: Nat, +res: Maybe<&2, LU>, +hl: {Bool.and(CS.length_is(32n, h), CS.length_is(65n, sig)) == True{} : Bool}, +hr: {CS.os2ip(CS.first(32n, sig)) == r : Nat}, +hs: {CS.os2ip(CS.first(32n, CS.after(32n, sig))) == s : Nat}, +hid: {U32.to_nat(CS.head(CS.after(64n, sig))) == id : Nat}, +hk: {ES.recover_ok(one, HS, r, s, id, OKR(r, s, id)) == res : Maybe<&2, LU>}) -> {ES.recover(one, h, sig) == res : Maybe<&2, LU>}:
  %ESYM(Bool, Bool.and(CS.length_is(32n, h), CS.length_is(65n, sig)), True{}, hl) : {ES.recover_len(one, h, sig, _) == res : Maybe<&2, LU>}
  Lg.subst(Nat, z => {ES.recover_ok(one, HS, z, CS.os2ip(CS.first(32n, CS.after(32n, sig))), U32.to_nat(CS.head(CS.after(64n, sig))), OKR(z, CS.os2ip(CS.first(32n, CS.after(32n, sig))), U32.to_nat(CS.head(CS.after(64n, sig))))) == res : Maybe<&2, LU>}, r, CS.os2ip(CS.first(32n, sig)), ESYM(Nat, CS.os2ip(CS.first(32n, sig)), r, hr),
    Lg.subst(Nat, z => {ES.recover_ok(one, HS, r, z, U32.to_nat(CS.head(CS.after(64n, sig))), OKR(r, z, U32.to_nat(CS.head(CS.after(64n, sig))))) == res : Maybe<&2, LU>}, s, CS.os2ip(CS.first(32n, CS.after(32n, sig))), ESYM(Nat, CS.os2ip(CS.first(32n, CS.after(32n, sig))), s, hs),
      Lg.subst(Nat, z => {ES.recover_ok(one, HS, r, s, z, OKR(r, s, z)) == res : Maybe<&2, LU>}, id, U32.to_nat(CS.head(CS.after(64n, sig))), ESYM(Nat, U32.to_nat(CS.head(CS.after(64n, sig))), id, hid), hk)))

# ---- small facts ----

def or_f_l(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def or_f_r(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, Lg.true_false(h))
    case False{}:
      h

# the key bytes of a successful public_key are pk_of of [d] G
def pk_c(+one: Nat, +c: Bool, +d: Nat, +pk: LU, ok: Bool, +h: {ES.public_d(one, c, d, ok) == Some{pk} : Maybe<&2, LU>}) -> {ES.pk_of(one, c, CS.pmul(ES.p(one), d, CS.g(one))) == pk : LU}:
  match ok:
    case True{}:
      Lg.some_inj(LU, ES.pk_of(one, c, CS.pmul(ES.p(one), d, CS.g(one))), pk, h)
    case False{}:
      Empty.absurd({ES.pk_of(one, c, CS.pmul(ES.p(one), d, CS.g(one))) == pk : LU}, Lg.none_some(LU, pk, h))

def pk_eq(+one: Nat, +sk: LU, +c: Bool, +pk: LU, +h: {ES.public_key(one, sk, c) == Some{pk} : Maybe<&2, LU>}) -> {ES.pk_of(one, c, CS.pmul(ES.p(one), CS.os2ip(sk), CS.g(one))) == pk : LU}:
  pk_c(one, c, CS.os2ip(sk), pk, Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk))), h)

def sign_c(+one: Nat, +k0: LU, +v0: LU, +h: LU, +d: Nat, +sig: LU, ok: Bool, +hs: {ES.sign_d(one, k0, v0, h, d, ok) == Some{sig} : Maybe<&2, LU>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Lg.none_some(LU, sig, hs))

# a successful sign had a 32-byte hash and a 32-byte key in [1, n - 1]
def sign_ok(+one: Nat, +sk: LU, +h: LU, +sig: LU, +hs: {ES.sign(one, sk, h) == Some{sig} : Maybe<&2, LU>}) -> {Bool.and(CS.length_is(32n, h), Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk)))) == True{} : Bool}:
  sign_c(one, ES.fill(32n, 0), ES.fill(32n, 1), h, CS.os2ip(sk), sig, Bool.and(CS.length_is(32n, h), Bool.and(CS.length_is(32n, sk), ES.scalar_ok(one, CS.os2ip(sk)))), hs)
