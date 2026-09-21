"""Generate a Bool conjunction def with its constructor and projection lemmas.

Usage (as a module): conj(name, params, args, conjuncts, names) -> Bend source.
  params  : the parameter list text, e.g. "~V: Data, +a: Nat"
  args    : the argument list text used to call the def, e.g. "~V, a"
  conjuncts: list of Bool expressions (over the parameters)
  names   : one projection name per conjunct
Proof-development helper only; it writes ordinary checked Bend terms.
"""

def conj(name, params, args, cs, names):
    k = len(cs)
    def rest(i):  # conjunction of cs[i:]
        if i == k - 1:
            return cs[i]
        return 'Bool.and(%s, %s)' % (cs[i], rest(i + 1))
    out = []
    out.append('def %s(%s) -> Bool:\n  %s\n' % (name, params, rest(0)))
    hyp = '+h: {%s(%s) == True{} : Bool}' % (name, args)
    # projections
    for i in range(k):
        # h_j : rest(j) == True ; h_0 = h
        e = 'h'
        for j in range(i):
            e = 'L.and_right(%s, %s, %s)' % (cs[j], rest(j + 1), e)
        if i < k - 1:
            e = 'L.and_left(%s, %s, %s)' % (cs[i], rest(i + 1), e)
        out.append('def %s(%s, %s) -> {%s == True{} : Bool}:\n  %s\n' % (names[i], params, hyp, cs[i], e))
    # constructor
    hs = ', '.join('+h%d: {%s == True{} : Bool}' % (i, cs[i]) for i in range(k))
    e = 'h%d' % (k - 1)
    for i in range(k - 2, -1, -1):
        e = 'L.and_intro(%s, %s, h%d, %s)' % (cs[i], rest(i + 1), i, e)
    out.append('def %s_mk(%s, %s) -> {%s(%s) == True{} : Bool}:\n  %s\n' % (name, params, hs, name, args, e))
    return '\n'.join(out)
