import Base
import ./gb.bend as GB
import ./blamka.bend as BL
import ./hash.bend as HS
import ./memory.bend as MEM
import ./access.bend as XP
import ./blocks.bend as BK
import ./hprime.bend as HP
import ./index.bend as IX
import ./fill.bend as FL
import ./run.bend as RN
import ./top.bend as TOP
import ./phc.bend as PP
import ./password.bend as PWP
import ../../../spec/lib/common.bend as SC
import ../../lib/u32.bend as U
import ../../lib/logic.bend as L
import ./laws.bend as Laws

# Gate for the Argon2id package: `bend proofs/crypto/argon2/proof.bend`
# prints ALL PROOFS CHECK when every law of laws.bend holds.
def Laws.gb_correct(a, b, c, d): GB.gb_correct(a, b, c, d)
def Laws.p_correct(v): BL.p_correct(v)
def Laws.compress_correct(x, y): BL.compress_correct(x, y)
def Laws.compress_xor_correct(x, y, old): BL.compress_xor_correct(x, y, old)
def Laws.hash_correct(nn, bs): HS.hash_eq(nn, bs)
def Laws.hprime_correct(tl, x): HS.hprime_eq(tl, x)
def Laws.h0_correct(p, tl, m, t, pw, salt, key, ad): HS.h0_eq(p, tl, m, t, pw, salt, key, ad)
def Laws.rel_correct(w, j1, k, hk, hw): IX.rel_eq(w, j1, k, hk, L.subst(Nat, z => {Nat.is_lt(w, z) == True{} : Bool}, Nat.pow(2n, k), SC.pow2(k), Equal.sym(Nat, SC.pow2(k), Nat.pow(2n, k), U.pow2_pow(k)), hw))
def Laws.addresses_correct(r, l, s, mm, t, ctr): IX.addresses_eq(r, l, s, mm, t, ctr)
def Laws.argon2id_correct(pw, salt, key, ad, t, m, p, tl, hf): TOP.argon2id_correct(pw, salt, key, ad, t, m, p, tl, hf)
def Laws.parse_format(m, t, p, salt, hash, hs, hh): PP.parse_format(m, t, p, salt, hash, hs, hh)
def Laws.verify_hash(pw, salt, params, hs): PWP.verify_hash(pw, salt, params, hs)
def Laws.rehash_hash(pw, salt, params, hs, hl): PWP.rehash_hash(pw, salt, params, hs, hl)
def Laws.tag_length(tl, x): PWP.hprime_len(tl, x)
def Laws.tag_bytes(tl, x): PWP.hprime_ok(tl, x)
