#!/usr/bin/env python3
"""The scalar identities of ECDSA (proofs/crypto/secp256k1/group/ecd_id.bend), by
reflection over any modulus 1 + mp (used with the group order n): with
s = k^-1 (e + r d), s w == 1 gives e w + (r w) d == k, and r ri == 1 gives
(-e) ri + (s ri) k == d; the same with -s and -k.

  python3 tools/generators/secp256k1_group/gen_ecd_ids.py
"""
import gen_ids as g


def main():
    c = g.Ctx(['e', 'r', 'd', 'k', 'ki', 'w', 'ri'])
    e, r, d, k, ki, w, ri = [c.var(i) for i in range(7)]
    one, zero = c.const(1), c.zero()
    erd = c.add(e, c.mul(r, d))
    s = c.mul(ki, erd)
    ns, nk, ne = c.sub(zero, s), c.sub(zero, k), c.sub(zero, e)
    u = c.add(c.mul(e, w), c.mul(c.mul(r, w), d))
    c.conseq('sv_pos', c.sub(u, k), [(one, c.mul(k, ki), c.mul(w, erd)), (c.mul(s, w), one, k)], (),
             'k ki == 1, s w == 1 (s = ki (e + r d)): e w + (r w) d - k == 0')
    c.conseq('sv_neg', c.add(u, k), [(one, c.mul(k, ki), c.mul(w, erd)), (c.mul(ns, w), one, nk)], (),
             'k ki == 1, (-s) w == 1: e w + (r w) d + k == 0')
    cof = c.sub(zero, c.mul(erd, ri))
    c.conseq('sr_pos', c.sub(c.add(c.mul(ne, ri), c.mul(c.mul(s, ri), k)), d), [(one, c.mul(k, ki), cof), (c.mul(r, ri), one, d)], (),
             'k ki == 1, r ri == 1: (-e) ri + (s ri) k - d == 0')
    c.conseq('sr_neg', c.sub(c.add(c.mul(ne, ri), c.mul(c.mul(ns, ri), nk)), d), [(one, c.mul(k, ki), cof), (c.mul(r, ri), one, d)], (),
             'the same with -s and -k')
    c.write('ecd_id.bend', '# The scalar identities of ECDSA verification and recovery.\n')


if __name__ == '__main__':
    main()
