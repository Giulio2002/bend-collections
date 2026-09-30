#!/usr/bin/env python3
"""Writes the sources of the BIP-340 proofs (proofs/crypto/secp256k1/group/sch*.bend):
the identity instance sch_id.bend (through gen_ids) and schg.src / schs.src,
which are macro-expanded here and then expanded by tools/generators/rw.py.

  python3 tools/generators/secp256k1_group/gen_sch.py
"""
import os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
sys.path.insert(0, HERE)
import gen_ids as g

FPD = '+mp: Nat, +hp: PM.Prime(1n+mp), +h3: {Nat.mod(mp, 3n) == 0n : Nat}, +hnc: {Nat.is_eq(Nat.mod(Nat.pow(Nat.sub(1n+mp, 7n), Nat.div(mp, 3n)), 1n+mp), 1n) == False{} : Bool}, +h21: {Nat.is_lt(21n, 1n+mp) == True{} : Bool}'
FPA = 'mp, hp, h3, hnc, h21'
# the group order 1 + nq (prime), the generator g (valid, [n] g equiv O, g not O)
GD = '+nq: Nat, +hq: PM.Prime(1n+nq), +g: CS.SPoint, +vg: {GS.valid(1n+mp, g) == True{} : Bool}, +hng: {GS.equiv(1n+mp, GS.smul(1n+mp, 1n+nq, g), CS.infinity()) == True{} : Bool}, +hgo: {GS.equiv(1n+mp, g, CS.infinity()) == False{} : Bool}'
GA = 'nq, hq, g, vg, hng, hgo'


def expand_calls(s, name, fn):
    pat = re.compile(r'(?<![A-Za-z0-9_.])' + name + r'\(')
    while True:
        m = pat.search(s)
        if not m:
            return s
        i = m.start()
        j = m.end()
        depth = 1
        args = []
        cur = ''
        while True:
            ch = s[j]
            if ch in '({[':
                depth += 1
            elif ch in ')}]':
                depth -= 1
                if depth == 0:
                    break
            if ch == ',' and depth == 1:
                args.append(cur.strip())
                cur = ''
            else:
                cur += ch
            j += 1
        args.append(cur.strip())
        s = s[:i] + fn(*args) + s[j + 1:]


MACROS = {
    'V': lambda a: '{GS.valid(1n+mp, %s) == True{} : Bool}' % a,
    'E': lambda a, b: '{GS.equiv(1n+mp, %s, %s) == True{} : Bool}' % (a, b),
    'PA': lambda a, b: 'CS.padd(1n+mp, %s, %s)' % (a, b),
    'SM': lambda k, a: 'GS.smul(1n+mp, %s, %s)' % (k, a),
    'PMU': lambda k, a: 'CS.pmul(1n+mp, %s, %s)' % (k, a),
    'NEG': lambda a: 'GS.neg(1n+mp, %s)' % a,
    'MP': lambda a, b: 'FS.mmul(1n+mp, %s, %s)' % (a, b),
    'MN': lambda a, b: 'FS.mmul(1n+nq, %s, %s)' % (a, b),
    'AN': lambda a, b: 'FS.madd(1n+nq, %s, %s)' % (a, b),
    'TR': lambda a, b, c, vb, h1, h2: 'G2.e_trans(mp, hp, %s, %s, %s, %s, %s, %s)' % (a, b, c, vb, h1, h2),
    'SY': lambda a, b, h: 'G2.e_sym(mp, %s, %s, %s)' % (a, b, h),
    'LT': lambda a, b: '{Nat.is_lt(%s, %s) == True{} : Bool}' % (a, b),
}
SQD = '+one: Nat, +h1: {one == 1n : Nat}, +s: Nat, +he: {Nat.add(1n+mp, 1n) == Nat.mul(s, 4n) : Nat}, +hodd: {Nat.mod(1n+mp, 2n) == 1n : Nat}, +h256: {Nat.is_le(1n+mp, C.shift(256n, one)) == True{} : Bool}'
SQA = 'one, h1, s, he, hodd, h256'
DEC = 'one, h1, mp, hp, s, he, hodd, h256'
ZI = 'FS.minv(1n+mp, z)'
AXV = 'FS.mmul(1n+mp, x, FS.minv(1n+mp, z))'
AYV = 'FS.mmul(1n+mp, y, FS.minv(1n+mp, z))'
CONSTS = {'FPD': FPD, 'FPA': FPA, 'GD': GD, 'GA': GA, 'INF': 'CS.infinity()', 'SQD': SQD, 'SQA': SQA, 'DEC': DEC, 'AXV': AXV, 'AYV': AYV,
          'PXYZ': 'CS.SPoint{x, y, z}', 'NAP': 'CS.SPoint{%s, %s, 1n}' % (AXV, AYV), 'EYV': 'FS.mneg(1n+mp, %s)' % AYV,
          'NEP': 'CS.SPoint{%s, FS.mneg(1n+mp, %s), 1n}' % (AXV, AYV), 'MSP': 'Maybe<&2, CS.SPoint>'}


def expand(src):
    for k in sorted(CONSTS, key=len, reverse=True):
        src = re.sub(r'(?<![A-Za-z0-9_.])%s(?![A-Za-z0-9_(])' % k, CONSTS[k], src)
    for k in MACROS:
        src = expand_calls(src, k, MACROS[k])
    return src


def gen_id():
    c = g.Ctx(['k', 'e', 'd'])
    k, e, d = [c.var(i) for i in range(3)]
    c.ident('sc_k', c.add(c.add(k, c.mul(e, d)), c.mul(c.sub(c.zero(), e), d)), k, (), '(k + e d) + (-e) d == k')
    c.write('sch_id.bend', '# The scalar identity of BIP-340 verification.\n')


def main():
    gen_id()
    for name in ('schg', 'schs'):
        p = os.path.join(HERE, name + '.tpl')
        if not os.path.exists(p):
            continue
        src = expand(open(p).read())
        open(os.path.join(HERE, name + '.src'), 'w').write(src)
        subprocess.check_call([sys.executable, os.path.join(HERE, '..', 'rw.py'), os.path.join(HERE, name + '.src'),
                               os.path.join(ROOT, 'proofs', 'crypto', 'secp256k1', 'group', name + '.bend')])


if __name__ == '__main__':
    main()
