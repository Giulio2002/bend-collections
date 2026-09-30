"""Symbolic evaluation of U32 bit operations the way Bend's checker reduces
them (every Bool operation matches its first argument), for the generators
of the bit-level AES proofs. A bit is an expression tree; a word is a list of
32 bits, index 0 the least significant."""

F, T = ('c', False), ('c', True)


def var(name):
    return ('v', name)


def bnot(a):
    if a == F:
        return T
    if a == T:
        return F
    return ('not', a)


def band(a, b):
    if a == F:
        return F
    if a == T:
        return b
    return ('and', a, b)


def bor(a, b):
    if a == F:
        return b
    if a == T:
        return T
    return ('or', a, b)


def bxor(a, b):
    if a == F:
        return b
    if a == T:
        return bnot(b)
    return ('xor', a, b)


def const(k):
    return [T if (k >> i) & 1 else F for i in range(32)]


def wand(a, b):
    return [band(x, y) for x, y in zip(a, b)]


def wor(a, b):
    return [bor(x, y) for x, y in zip(a, b)]


def wxor(a, b):
    return [bxor(x, y) for x, y in zip(a, b)]


def shl(a, n):
    return [F] * n + a[:32 - n]


def shr(a, n):
    return a[n:] + [F] * n


def show(e):
    k = e[0]
    if k == 'c':
        return 'True{}' if e[1] else 'False{}'
    if k == 'v':
        return e[1]
    if k == 'not':
        return 'Bool.not(%s)' % show(e[1])
    return 'Bool.%s(%s, %s)' % (k, show(e[1]), show(e[2]))


def leaves(e, acc=None):
    if acc is None:
        acc = []
    if e[0] == 'v':
        if e[1] not in acc:
            acc.append(e[1])
    elif e[0] != 'c':
        for s in e[1:]:
            leaves(s, acc)
    return acc


def subst(e, name, by):
    if e[0] == 'v':
        return by if e[1] == name else e
    if e[0] == 'c':
        return e
    return (e[0],) + tuple(subst(s, name, by) for s in e[1:])


def word(bits):
    s = 'WNil{}'
    for b in reversed(bits):
        s = 'WCon{%s, %s}' % (b, s)
    return 'U32{%s}' % s


def evaluate(e, env):
    k = e[0]
    if k == 'c':
        return e[1]
    if k == 'v':
        return env[e[1]]
    if k == 'not':
        return not evaluate(e[1], env)
    a, b = evaluate(e[1], env), evaluate(e[2], env)
    return {'and': a and b, 'or': a or b, 'xor': a != b}[k]
