#!/usr/bin/env python3
"""Writes the sources of the ECDSA proofs (tools/generators/secp256k1_group/ecd*.src
from the templates ecd*.tpl beside this script) by expanding a few macros,
then runs rw.py on them (proofs/crypto/secp256k1/group/ecd*.bend).

  python3 tools/generators/secp256k1_group/gen_ecd.py [names...]

Macros (whole words): FPD/FPA the field facts of glaw1.bend as parameters /
arguments; function-like: MN(a, b), AN(a, b), SN(a, b), IN(a) the scalar
product, sum, difference, inverse modulo 1 + nm; MP, IP modulo 1 + mp;
V(a) / E(a, b) valid / equiv modulo 1 + mp as equations; PA(a, b), PM(k, a),
SM(k, a) the specification's padd, pmul and GS.smul modulo 1 + mp.
"""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')

FPD = '+mp: Nat, +hp: PM.Prime(1n+mp), +h3: {Nat.mod(mp, 3n) == 0n : Nat}, +hnc: {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+mp, 7n), Nat.div(mp, 3n)), 1n+mp), 1n) == False{} : Bool}, +h21: {Nat.is_lt(21n, 1n+mp) == True{} : Bool}'
WORDS = {
    'FPD': FPD, 'FPA': 'mp, hp, h3, hnc, h21',
    'NQD': '+nm: Nat, +hq: PM.Prime(1n+nm)', 'NQA': 'nm, hq',
    'GD': '+g: CS.SPoint, +vg: {GS.valid(1n+mp, g) == True{} : Bool}, +hng: {GS.equiv(1n+mp, GS.smul(1n+mp, 1n+nm, g), CS.infinity()) == True{} : Bool}, +hgo: {GS.equiv(1n+mp, g, CS.infinity()) == False{} : Bool}',
    'GA': 'g, vg, hng, hgo',
    'OD': '+one: Nat, +h1: {one == 1n : Nat}, +hn256: {Nat.is_le(1n+nm, C.shift(256n, one)) == True{} : Bool}', 'OA': 'one, h1, hn256',
    'ED': '+s4: Nat, +he: {Nat.add(1n+mp, 1n) == Nat.mul(s4, 4n) : Nat}, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, +h256: {Nat.is_le(1n+mp, C.shift(256n, one)) == True{} : Bool}', 'EA': 's4, he, hodd, h256',
    'SS': 'FS.mmul(1n+nm, FS.minv(1n+nm, k), FS.madd(1n+nm, e, FS.mmul(1n+nm, r, d)))',
    'RV': 'Nat.mod(CS.aff_x(CS.to_affine(1n+mp, kp)), 1n+nm)',
    'KH': '+k0: {Nat.is_eq(k, 0n) == False{} : Bool}, +kl: {Nat.is_lt(k, 1n+nm) == True{} : Bool}',
    'DH': '+d0: {Nat.is_eq(d, 0n) == False{} : Bool}, +dl: {Nat.is_lt(d, 1n+nm) == True{} : Bool}',
    'HD1': '+one: Nat, +h1: {one == 1n : Nat}, +hp: PM.Prime(FS.prime(one)), +hc: {Nat.is_eq(FS.mpow(FS.prime(one), Nat.sub(FS.prime(one), 7n), Nat.div(Nat.sub(FS.prime(one), 1n), 3n)), 1n) == False{} : Bool}, +hq: PM.Prime(FS.order(one)), +hg: {GS.valid(FS.prime(one), CS.g(one)) == True{} : Bool}, +hng: {GS.equiv(FS.prime(one), GS.smul(FS.prime(one), FS.order(one), CS.g(one)), CS.infinity()) == True{} : Bool}',
    'HA1': 'one, h1, hp, hc, hq, hg, hng',
    'P1': 'FS.prime(one)', 'N1': 'FS.order(one)', 'G1': 'CS.g(one)',
    'HS': 'ES.hash_scalar(one, h)',
    'QP': 'CS.pmul(FS.prime(one), d, CS.g(one))',
    'LU': 'List<&2, U32>', 'MSP': 'Maybe<&2, CS.SPoint>', 'MLU': 'Maybe<&2, List<&2, U32>>',
    'INF': 'CS.infinity()', 'TT': 'True{}', 'FF': 'False{}',
}
FUNCS = {
    'MN': lambda a, b: 'FS.mmul(1n+nm, %s, %s)' % (a, b),
    'AN': lambda a, b: 'FS.madd(1n+nm, %s, %s)' % (a, b),
    'SN': lambda a, b: 'FS.msub(1n+nm, %s, %s)' % (a, b),
    'IN': lambda a: 'FS.minv(1n+nm, %s)' % a,
    'SSF': lambda r: 'FS.mmul(1n+nm, FS.minv(1n+nm, k), FS.madd(1n+nm, e, FS.mmul(1n+nm, %s, d)))' % r,
    'RRH': lambda sl: 'CS.padd(1n+mp, CS.pmul(1n+mp, FS.mmul(1n+nm, e, FS.minv(1n+nm, %s)), g), CS.pmul(1n+mp, FS.mmul(1n+nm, RV, FS.minv(1n+nm, %s)), EG.nrm(1n+mp, qp)))' % (sl, sl),
    'QRH': lambda sl, pr: 'CS.padd(1n+mp, CS.pmul(1n+mp, FS.mmul(1n+nm, FS.msub(1n+nm, 0n, e), FS.minv(1n+nm, RV)), g), CS.pmul(1n+mp, FS.mmul(1n+nm, %s, FS.minv(1n+nm, RV)), %s))' % (sl, pr),
    'NN': lambda a: 'FS.msub(1n+nm, 0n, %s)' % a,
    'DN': lambda a: 'Nat.mod(%s, 1n+nm)' % a,
    'MP': lambda a, b: 'FS.mmul(1n+mp, %s, %s)' % (a, b),
    'IP': lambda a: 'FS.minv(1n+mp, %s)' % a,
    'DP': lambda a: 'Nat.mod(%s, 1n+mp)' % a,
    'V': lambda a: '{GS.valid(1n+mp, %s) == True{} : Bool}' % a,
    'E': lambda a, b: '{GS.equiv(1n+mp, %s, %s) == True{} : Bool}' % (a, b),
    'PA': lambda a, b: 'CS.padd(1n+mp, %s, %s)' % (a, b),
    'PM': lambda k, a: 'CS.pmul(1n+mp, %s, %s)' % (k, a),
    'SM': lambda k, a: 'GS.smul(1n+mp, %s, %s)' % (k, a),
    'NG': lambda a: 'GS.neg(1n+mp, %s)' % a,
    'TA': lambda a: 'CS.to_affine(1n+mp, %s)' % a,
    'V1': lambda a: '{GS.valid(FS.prime(one), %s) == True{} : Bool}' % a,
    'E1': lambda a, b: '{GS.equiv(FS.prime(one), %s, %s) == True{} : Bool}' % (a, b),
    'SM1': lambda k, a: 'GS.smul(FS.prime(one), %s, %s)' % (k, a),
    'PM1': lambda k, a: 'CS.pmul(FS.prime(one), %s, %s)' % (k, a),
    'PA1': lambda a, b: 'CS.padd(FS.prime(one), %s, %s)' % (a, b),
    'SOK': lambda x: '{ES.scalar_ok(one, %s) == True{} : Bool}' % x,
    'OK3': lambda r, s, st: 'Bool.and(Bool.and(ES.scalar_ok(one, %s), ES.scalar_ok(one, %s)), Bool.or(Bool.not(%s), Bool.not(Nat.is_lt(ES.n(one), Nat.double(%s)))))' % (r, s, st, s),
    'OKR': lambda r, s, i: 'Bool.and(Bool.and(ES.scalar_ok(one, %s), ES.scalar_ok(one, %s)), Nat.is_lt(%s, 4n))' % (r, s, i),
    'NZP': lambda a: 'F.NZ(mp, %s)' % a,
    'NZN': lambda a: 'F.NZ(nm, %s)' % a,
    'LTN': lambda a: '{Nat.is_lt(%s, 1n+nm) == True{} : Bool}' % a,
    'TR': lambda a, b, c, vb, h1, h2: 'G2.e_trans(mp, hp, %s, %s, %s, %s, %s, %s)' % (a, b, c, vb, h1, h2),
    'SY': lambda a, b, h: 'G2.e_sym(mp, %s, %s, %s)' % (a, b, h),
    'ESYM': lambda t, a, b, h: 'Equal.sym(%s, %s, %s, %s)' % (t, a, b, h),
    'ETR': lambda t, a, b, c, h1, h2: 'Equal.trans(%s, %s, %s, %s, %s, %s)' % (t, a, b, c, h1, h2),
}


def split_args(s):
    args, cur, depth = [], '', 0
    for ch in s:
        if ch in '({[':
            depth += 1
        elif ch in ')}]':
            depth -= 1
        if ch == ',' and depth == 0:
            args.append(cur.strip())
            cur = ''
        else:
            cur += ch
    args.append(cur.strip())
    return args


def expand(s, extra_words=None, extra_funcs=None):
    words = dict(WORDS)
    words.update(extra_words or {})
    funcs = dict(FUNCS)
    funcs.update(extra_funcs or {})
    changed = True
    while changed:
        changed = False
        for name, fn in funcs.items():
            pat = re.compile(r'(?<![A-Za-z0-9_.])%s\(' % name)
            while True:
                m = pat.search(s)
                if not m:
                    break
                i = m.end()
                depth = 1
                j = i
                while depth > 0:
                    ch = s[j]
                    if ch in '({[':
                        depth += 1
                    elif ch in ')}]':
                        depth -= 1
                    j += 1
                s = s[:m.start()] + fn(*split_args(s[i:j - 1])) + s[j:]
                changed = True
        for k in sorted(words, key=len, reverse=True):
            s2 = re.sub(r'(?<![A-Za-z0-9_.])%s(?![A-Za-z0-9_({])' % k, lambda _m, k=k: words[k], s)
            if s2 != s:
                s, changed = s2, True
    return s


def main():
    names = sys.argv[1:] or sorted(f[:-4] for f in os.listdir(HERE) if f.startswith('ecd') and f.endswith('.tpl'))
    for n in names:
        tpl = open(os.path.join(HERE, n + '.tpl')).read()
        src = os.path.join(HERE, n + '.src')
        open(src, 'w').write(expand(tpl))
        subprocess.check_call([sys.executable, os.path.join(HERE, '..', 'rw.py'), src, os.path.join(ROOT, 'proofs', 'crypto', 'secp256k1', 'group', n + '.bend')])


if __name__ == '__main__':
    main()
