#!/usr/bin/env python3
"""Rewrite-step generator for Bend proofs (used by the secp256k1 proofs).

  python3 tools/generators/rw.py in.src out.bend
  python3 tools/generators/rw.py --all DIR OUTDIR   every DIR/*.src to OUTDIR/*.bend

Imports in a .src are relative to its output .bend.

Bend has no tactics: an equation is proved by rewriting the goal step by
step (`%e : P`, P the goal with `_` at the rewritten position). This tool
expands a few directives in a .src proof file into such steps, so that the
file holds the proof's intent and the generated .bend holds every step the
checker verifies (nothing here is trusted: a wrong step fails the check).

Directives (each on its own line, indented like the body it is in):

  %goal {A == B : T}     set the current goal (the def's own return type is
                         taken automatically when the def returns an
                         equation)
  %rw CALL               rewrite with the equation of CALL, a call of a def
                         whose type is {L == R : T} (looked up in the file's
                         imports or the file itself): the first occurrence of
                         L becomes R; `%rw <- CALL` rewrites R into L;
                         `%rw@2 CALL` takes the second occurrence
  %rwh TERM : {L == R : T}   the same with a proof term whose equation is given
  %norm                  normalize both sides of a Nat equation as
                         commutative-semiring polynomials (distribute, hoist
                         C.shift, sort sums and products), then close it
  %close                 close the goal with {==}
  %show                  print the current goal (a comment)

The normalizer uses lemmas of proofs/lib/lemmas/proofs/nat_algebra.bend (NA),
proofs/math/typed/width.bend (WW) and proofs/crypto/secp256k1/semiring.bend
(SR); a file using %norm must import them under these names.
"""
import os, re, sys

# ------------------------------------------------------------------ terms
# ('app', f, [args])  f a name; ('ctr', K, [args]); ('var', x); ('lit', text)
# ('list', [items]); ('cons', h, t); ('succ', k, t) for `kn+t`; ('eq', a, b, T)
# ('hole',); ('lam', text) for anything we keep verbatim


class P:
    def __init__(self, s):
        self.s, self.i = s, 0

    def ws(self):
        while self.i < len(self.s) and self.s[self.i] in ' \t\n':
            self.i += 1

    def peek(self, t):
        self.ws()
        return self.s.startswith(t, self.i)

    def eat(self, t):
        self.ws()
        if not self.s.startswith(t, self.i):
            raise SyntaxError('expected %r at %r' % (t, self.s[self.i:self.i + 40]))
        self.i += len(t)

    def expr(self):
        a = self.atom()
        self.ws()
        if self.s.startswith('<>', self.i):
            self.i += 2
            return ('cons', a, self.expr())
        return a

    def args(self, close):
        out = []
        if self.peek(close):
            self.eat(close)
            return out
        while True:
            out.append(self.expr())
            if self.peek(','):
                self.eat(',')
                continue
            self.eat(close)
            return out

    def atom(self):
        self.ws()
        s, i = self.s, self.i
        if s.startswith('{', i):
            self.i += 1
            a = self.expr()
            self.eat('==')
            b = self.expr()
            self.eat(':')
            j = self.i
            depth = 0
            while True:
                c = s[self.i]
                if c in '({[<':
                    depth += 1
                elif c in ')}]>':
                    if depth == 0 and c == '}':
                        break
                    depth -= 1
                self.i += 1
            T = s[j:self.i].strip()
            self.eat('}')
            return ('eq', a, b, T)
        if s.startswith('(', i):
            self.i += 1
            a = self.expr()
            self.eat(')')
            return a
        if s.startswith('[', i):
            self.i += 1
            return ('list', self.args(']'))
        if s.startswith('_', i) and not re.match(r'[A-Za-z0-9_]', s[i + 1:i + 2] or ' '):
            self.i += 1
            return ('hole',)
        m = re.compile(r'\d+n?').match(s, i)
        if m:
            self.i = m.end()
            t = m.group(0)
            if t.endswith('n') and s.startswith('+', self.i):
                self.i += 1
                if s.startswith(' ', self.i):
                    self.i += 1
                return canon(('succ', t, self.atom()))
            return ('lit', t)
        m = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*').match(s, i)
        if not m:
            raise SyntaxError('bad term at %r' % s[i:i + 40])
        self.i = m.end()
        name = m.group(0)
        if s.startswith('(', self.i):
            self.i += 1
            return ('app', name, self.args(')'))
        if s.startswith('{', self.i):
            self.i += 1
            return ('ctr', name, self.args('}'))
        return ('var', name)


def parse(s):
    p = P(s)
    t = p.expr()
    p.ws()
    if p.i != len(s):
        raise SyntaxError('trailing text %r' % s[p.i:])
    return t


def show(t):
    k = t[0]
    if k == 'app':
        return '%s(%s)' % (t[1], ', '.join(show(a) for a in t[2]))
    if k == 'ctr':
        return '%s{%s}' % (t[1], ', '.join(show(a) for a in t[2]))
    if k in ('var', 'lit'):
        return t[1]
    if k == 'list':
        return '[%s]' % ', '.join(show(a) for a in t[1])
    if k == 'cons':
        h = show(t[1])
        return '%s <> %s' % (('(%s)' % h) if t[1][0] == 'cons' else h, show(t[2]))
    if k == 'succ':
        return '%s+%s' % (t[1], show(t[2]) if t[2][0] != 'cons' else '(%s)' % show(t[2]))
    if k == 'eq':
        return '{%s == %s : %s}' % (show(t[1]), show(t[2]), t[3])
    if k == 'hole':
        return '_'
    raise ValueError(t)


def canon(t):
    # `kn+ln` is the literal k + l, as Bend reads it; a sum or product of
    # two small literals is written as its value (the checker computes it)
    if t[0] == 'app' and t[1] in ('Nat.add', 'Nat.mul') and len(t[2]) == 2 and all(a[0] == 'lit' and a[1].endswith('n') for a in t[2]):
        a, b = int(t[2][0][1][:-1]), int(t[2][1][1][:-1])
        v = a + b if t[1] == 'Nat.add' else a * b
        if v <= 4096:
            return ('lit', '%dn' % v)
    if t[0] == 'succ':
        inner = canon(t[2])
        if inner[0] == 'lit' and inner[1].endswith('n'):
            return ('lit', '%dn' % (int(t[1][:-1]) + int(inner[1][:-1])))
        return ('succ', t[1], inner)
    return t


def subst(t, env):
    return canon(subst0(t, env))


def subst0(t, env):
    k = t[0]
    if k == 'var':
        return env.get(t[1], t)
    if k in ('app', 'ctr'):
        return canon((k, t[1], [subst(a, env) for a in t[2]]))
    if k == 'list':
        return ('list', [subst(a, env) for a in t[1]])
    if k == 'cons':
        return ('cons', subst(t[1], env), subst(t[2], env))
    if k == 'succ':
        return canon(('succ', t[1], subst(t[2], env)))
    if k == 'eq':
        return ('eq', subst(t[1], env), subst(t[2], env), t[3])
    return t


def positions(t, path=()):
    yield path, t
    k = t[0]
    if k in ('app', 'ctr'):
        for i, a in enumerate(t[2]):
            yield from positions(a, path + (i,))
    elif k == 'list':
        for i, a in enumerate(t[1]):
            yield from positions(a, path + (i,))
    elif k == 'cons':
        yield from positions(t[1], path + (0,))
        yield from positions(t[2], path + (1,))
    elif k == 'succ':
        yield from positions(t[2], path + (0,))
    elif k == 'eq':
        yield from positions(t[1], path + (0,))
        yield from positions(t[2], path + (1,))


def get(t, path):
    for i in path:
        k = t[0]
        if k in ('app', 'ctr'):
            t = t[2][i]
        elif k == 'list':
            t = t[1][i]
        elif k == 'cons':
            t = t[1 + i]
        elif k == 'succ':
            t = t[2]
        elif k == 'eq':
            t = t[1 + i]
    return t


def put(t, path, v):
    if not path:
        return v
    i, rest = path[0], path[1:]
    k = t[0]
    if k in ('app', 'ctr'):
        a = list(t[2])
        a[i] = put(a[i], rest, v)
        return (k, t[1], a)
    if k == 'list':
        a = list(t[1])
        a[i] = put(a[i], rest, v)
        return ('list', a)
    if k == 'cons':
        return ('cons', put(t[1], rest, v), t[2]) if i == 0 else ('cons', t[1], put(t[2], rest, v))
    if k == 'succ':
        return ('succ', t[1], put(t[2], rest, v))
    if k == 'eq':
        return ('eq', put(t[1], rest, v), t[2], t[3]) if i == 0 else ('eq', t[1], put(t[2], rest, v), t[3])
    raise ValueError


# ------------------------------------------------------------------ lemma table
def strip_types(params):
    names = []
    depth = 0
    cur = ''
    for c in params + ',':
        if c in '(<{[':
            depth += 1
        elif c in ')>}]':
            depth -= 1
        if c == ',' and depth == 0:
            names.append(cur.strip())
            cur = ''
        else:
            cur += c
    out = []
    for n in names:
        if not n:
            continue
        n = n.split(':')[0].strip().lstrip('+-~')
        out.append(n)
    return out


DEF = re.compile(r'^def ([A-Za-z0-9_.]+)\((.*)\) -> (\{.*\}):\s*$')
LAW = re.compile(r'^law ([A-Za-z0-9_.]+):\s*$')


def imports_of(path):
    d = os.path.dirname(os.path.abspath(path))
    text = open(path).read()
    return {m.group(2): os.path.normpath(os.path.join(d, m.group(1))) for m in re.finditer(r'^import (\S+\.bend) as (\w+)$', text, re.M)}


def local_names(path):
    text = open(path).read()
    names = set(re.findall(r'^(?:def|law) ([A-Za-z0-9_.]+)', text, re.M))
    names |= set(re.findall(r'^type ([A-Za-z0-9_]+)', text, re.M))
    names |= set(re.findall(r'^  ([A-Z][A-Za-z0-9_]*)\{', text, re.M))
    return names


def rename(t, f):
    k = t[0]
    if k == 'var':
        return ('var', f(t[1]))
    if k in ('app', 'ctr'):
        return (k, f(t[1]), [rename(a, f) for a in t[2]])
    if k == 'list':
        return ('list', [rename(a, f) for a in t[1]])
    if k == 'cons':
        return ('cons', rename(t[1], f), rename(t[2], f))
    if k == 'succ':
        return ('succ', t[1], rename(t[2], f))
    if k == 'eq':
        return ('eq', rename(t[1], f), rename(t[2], f), t[3])
    return t


def lemmas_of(path, cache={}):
    if path in cache:
        return cache[path]
    table = {}
    lines = open(path).read().split('\n')
    for idx, line in enumerate(lines):
        m = DEF.match(line)
        if m:
            try:
                table[m.group(1)] = (strip_types(m.group(2)), parse(m.group(3)))
            except SyntaxError:
                pass
        m = LAW.match(line)
        if m:
            params, j = [], idx + 1
            while j < len(lines) and lines[j].strip().startswith('for '):
                params.append(lines[j].strip()[4:].split(':')[0].strip().lstrip('+-~'))
                j += 1
            try:
                table[m.group(1)] = (params, parse(lines[j].strip()))
            except (SyntaxError, IndexError):
                pass
    cache[path] = table
    return table


class Ctx:
    def __init__(self, src_path, text):
        self.dir = os.path.dirname(os.path.abspath(src_path))
        self.imports = {}
        for m in re.finditer(r'^import (\S+\.bend) as (\w+)$', text, re.M):
            self.imports[m.group(2)] = os.path.normpath(os.path.join(self.dir, m.group(1)))
        self.local = {}

    def lookup(self, name):
        if '.' in name:
            alias, rest = name.split('.', 1)
            if alias in self.imports:
                path = self.imports[alias]
                t = lemmas_of(path)
                if rest in t:
                    params, eq = t[rest]
                    theirs = imports_of(path)
                    mine = {p: a for a, p in self.imports.items()}
                    locs = local_names(path)

                    def f(n, alias=alias, theirs=theirs, mine=mine, locs=locs, params=params):
                        if n in params:
                            return n
                        if '.' in n:
                            a, r = n.split('.', 1)
                            if a in theirs and theirs[a] in mine:
                                return mine[theirs[a]] + '.' + r
                        if n in locs:
                            return alias + '.' + n
                        return n
                    return params, rename(eq, f)
        if name in self.local:
            return self.local[name]
        raise KeyError('no equation lemma %s' % name)

    def instance(self, call):
        c = parse(call)
        assert c[0] == 'app', call
        params, eq = self.lookup(c[1])
        if len(params) != len(c[2]):
            raise SystemExit('%s: %d params, %d args' % (c[1], len(params), len(c[2])))
        eq = subst(eq, dict(zip(params, c[2])))
        return eq


# ------------------------------------------------------------------ rewriting
class Goal:
    def __init__(self, eq, out, indent):
        self.g = eq
        self.out = out
        self.indent = indent

    def emit_rw(self, path, new, proof_of_new_eq_old, T):
        """Replace the subterm at path by `new`, given a proof of {new == old}."""
        old = get(self.g, path)
        motive = put(self.g, path, ('hole',))
        self.out.append('%s%%%s : %s' % (self.indent, proof_of_new_eq_old, show(motive)))
        self.g = put(self.g, path, new)

    def rewrite(self, L, R, proof, T, occ=1, where=None):
        """Rewrite an occurrence of L into R, `proof` proving {L == R : T}."""
        n = 0
        for path, sub in positions(self.g):
            if not path:
                continue
            if where is not None and path[0] != where:
                continue
            if sub == L:
                n += 1
                if n == occ:
                    self.emit_rw(path, R, 'Equal.sym(%s, %s, %s, %s)' % (T, show(L), show(R), proof), T)
                    return
        raise SystemExit('rewrite: no occurrence %d of %s in %s' % (occ, show(L), show(self.g)))


# ------------------------------------------------------------------ semiring normalizer
def is_lit(t):
    return t[0] == 'lit' and t[1].endswith('n')


def litv(t):
    return int(t[1][:-1])


def A(a, b):
    return ('app', 'Nat.add', [a, b])


def M(a, b):
    return ('app', 'Nat.mul', [a, b])


def S(k, x):
    return ('app', 'C.shift', [k, x])


def isop(t, name):
    return t[0] == 'app' and t[1] == name and len(t[2]) == 2


def atom_key(t):
    # literals after every other atom (so a match on a literal never leads)
    return (1 if is_lit(t) else 0, show(t))


def prod_atoms(t):
    if isop(t, 'Nat.mul'):
        return prod_atoms(t[2][0]) + prod_atoms(t[2][1])
    return [t]


def mono_key(t):
    if isop(t, 'C.shift') and is_lit(t[2][0]):
        return (tuple(sorted(atom_key(a) for a in prod_atoms(t[2][1]))), litv(t[2][0]))
    return (tuple(sorted(atom_key(a) for a in prod_atoms(t))), 0)


ZERO = ('lit', '0n')
ONE = ('lit', '1n')


def step_rules(t):
    """One rewrite at the root of t: (new, proof of {t == new}) or None."""
    if t[0] == 'succ':
        k = int(t[1][:-1])
        return A(t[2], ('lit', '%dn' % k)), 'SR.succ_add(%s, %s)' % (t[1], show(t[2]))
    if isop(t, 'Nat.double') if False else (t[0] == 'app' and t[1] == 'Nat.double' and len(t[2]) == 1):
        x = t[2][0]
        return A(x, x), 'NA.double_self(%s)' % show(x)
    if isop(t, 'Nat.add'):
        a, b = t[2]
        if is_lit(a) and is_lit(b) and litv(a) + litv(b) <= 4096:
            return ('lit', '%dn' % (litv(a) + litv(b))), '{==}'
        if is_lit(a) and isop(b, 'Nat.add') and is_lit(b[2][0]) and litv(a) + litv(b[2][0]) <= 4096:
            return A(('lit', '%dn' % (litv(a) + litv(b[2][0]))), b[2][1]), '{==}'
        if a == ZERO:
            return b, 'SR.zero_add(%s)' % show(b)
        if b == ZERO:
            return a, 'NA.add_zero(%s)' % show(a)
        if isop(a, 'Nat.add'):
            return A(a[2][0], A(a[2][1], b)), 'NA.add_assoc(%s, %s, %s)' % (show(a[2][0]), show(a[2][1]), show(b))
        if isop(b, 'Nat.add'):
            c, d = b[2]
            if mono_key(c) < mono_key(a):
                return A(c, A(a, d)), 'NA.add_swap(%s, %s, %s)' % (show(a), show(c), show(d))
            return None
        if mono_key(b) < mono_key(a):
            return A(b, a), 'NA.add_comm(%s, %s)' % (show(a), show(b))
        return None
    if isop(t, 'Nat.mul'):
        a, b = t[2]
        if is_lit(a) and is_lit(b) and litv(a) * litv(b) <= 4096:
            return ('lit', '%dn' % (litv(a) * litv(b))), '{==}'
        if a == ZERO:
            return ZERO, 'SR.zero_mul(%s)' % show(b)
        if b == ZERO:
            return ZERO, 'NA.mul_zero(%s)' % show(a)
        if a == ONE:
            return b, 'SR.one_mul(%s)' % show(b)
        if b == ONE:
            return a, 'NA.mul_one(%s)' % show(a)
        if isop(b, 'Nat.add'):
            return A(M(a, b[2][0]), M(a, b[2][1])), 'NA.mul_add_left(%s, %s, %s)' % (show(a), show(b[2][0]), show(b[2][1]))
        if isop(a, 'Nat.add'):
            return A(M(a[2][0], b), M(a[2][1], b)), 'NA.mul_add_right(%s, %s, %s)' % (show(a[2][0]), show(a[2][1]), show(b))
        if isop(a, 'C.shift'):
            return S(a[2][0], M(a[2][1], b)), 'WW.shift_mul_l(%s, %s, %s)' % (show(a[2][0]), show(a[2][1]), show(b))
        if isop(b, 'C.shift'):
            return S(b[2][0], M(a, b[2][1])), 'WW.shift_mul_r(%s, %s, %s)' % (show(b[2][0]), show(a), show(b[2][1]))
        if isop(a, 'Nat.mul'):
            return M(a[2][0], M(a[2][1], b)), 'NA.mul_assoc(%s, %s, %s)' % (show(a[2][0]), show(a[2][1]), show(b))
        if isop(b, 'Nat.mul'):
            c, d = b[2]
            if atom_key(c) < atom_key(a):
                return M(c, M(a, d)), 'SR.mul_swap(%s, %s, %s)' % (show(a), show(c), show(d))
            return None
        if atom_key(b) < atom_key(a):
            return M(b, a), 'NA.mul_comm(%s, %s)' % (show(a), show(b))
        return None
    if isop(t, 'C.shift'):
        k, x = t[2]
        if k == ZERO:
            return x, 'SR.shift0(%s)' % show(x)
        if x == ZERO:
            return ZERO, 'WW.shift_zero(%s)' % show(k)
        if isop(x, 'Nat.add'):
            return A(S(k, x[2][0]), S(k, x[2][1])), 'WW.shift_add(%s, %s, %s)' % (show(k), show(x[2][0]), show(x[2][1]))
        if isop(x, 'C.shift') and is_lit(k) and is_lit(x[2][0]):
            s = ('lit', '%dn' % (litv(k) + litv(x[2][0])))
            return S(s, x[2][1]), 'SR.shift_shift(%s, %s, %s)' % (show(k), show(x[2][0]), show(x[2][1]))
        return None
    return None


def first_redex(t, path=()):
    """Leftmost-innermost redex: (path, new, proof)."""
    k = t[0]
    if k == 'succ':
        r = first_redex(t[2], path + (0,))
        if r:
            return r
        r = step_rules(t)
        return (path, r[0], r[1])
    if k == 'app' and t[1] in ('Nat.add', 'Nat.mul', 'C.shift', 'Nat.double'):
        for i, a in enumerate(t[2]):
            if t[1] == 'C.shift' and i == 0:
                continue
            r = first_redex(a, path + (i,))
            if r:
                return r
        r = step_rules(t)
        if r:
            return (path, r[0], r[1])
    return None


def normalize(goal, max_steps=4000, close=True):
    for side in (0, 1):
        n = 0
        while True:
            sub = get(goal.g, (side,))
            r = first_redex(sub)
            if not r:
                break
            path, new, proof = r
            old = get(sub, path)
            full = (side,) + path
            # proof : {old == new}; emit_rw wants a proof of {new == old}
            goal.emit_rw(full, new, 'Equal.sym(Nat, %s, %s, %s)' % (show(old), show(new), proof), 'Nat')
            n += 1
            if n > max_steps:
                raise SystemExit('normalize: no fixpoint on %s' % show(goal.g))
    if not close:
        return
    if goal.g[1] != goal.g[2]:
        raise SystemExit('normalize: sides differ:\n  %s\n  %s' % (show(goal.g[1]), show(goal.g[2])))
    goal.out.append(goal.indent + '{==}')


# ------------------------------------------------------------------ driver
def expand(src_path, text, dst_path=None):
    ctx = Ctx(dst_path or src_path, text)
    # local lemmas of this file
    for line in text.split('\n'):
        m = DEF.match(line)
        if m:
            try:
                ctx.local[m.group(1)] = (strip_types(m.group(2)), parse(m.group(3)))
            except SyntaxError:
                pass
    out = []
    goal = None
    for line in text.split('\n'):
        m = DEF.match(line)
        if m:
            try:
                goal = parse(m.group(3))
            except SyntaxError:
                goal = None
        s = line.strip()
        indent = line[:len(line) - len(line.lstrip())]
        if not re.match(r'%(rw|rwh|goal|norm|nf|close|show)(@|\b)', s):
            out.append(line)
            continue
        m = re.match(r'%goal (.*)$', s)
        if m:
            goal = parse(m.group(1))
            continue
        if goal is None:
            raise SystemExit('no goal for: ' + s)
        G = Goal(goal, out, indent)
        m = re.match(r'%rw(@\d+)?(@[lr])? (<- )?(.*)$', s)
        if m:
            occ = int(m.group(1)[1:]) if m.group(1) else 1
            where = {'@l': 0, '@r': 1}.get(m.group(2))
            call = m.group(4)
            eq = ctx.instance(call)
            L, R, T = eq[1], eq[2], eq[3]
            if m.group(3):
                G.rewrite(R, L, 'Equal.sym(%s, %s, %s, %s)' % (T, show(L), show(R), call), T, occ, where)
            else:
                G.rewrite(L, R, call, T, occ, where)
            goal = G.g
            continue
        m = re.match(r'%rwh(@\d+)?(@[lr])? (<- )?(.*?) : (\{.*\})$', s)
        if m:
            occ = int(m.group(1)[1:]) if m.group(1) else 1
            where = {'@l': 0, '@r': 1}.get(m.group(2))
            eq = parse(m.group(5))
            L, R, T = eq[1], eq[2], eq[3]
            term = m.group(4)
            if m.group(3):
                G.rewrite(R, L, 'Equal.sym(%s, %s, %s, %s)' % (T, show(L), show(R), term), T, occ, where)
            else:
                G.rewrite(L, R, term, T, occ, where)
            goal = G.g
            continue
        if s == '%norm':
            normalize(G)
            goal = None
            continue
        if s == '%nf':
            normalize(G, close=False)
            goal = G.g
            continue
        if s == '%close':
            out.append(indent + '{==}')
            goal = None
            continue
        if s == '%show':
            out.append(indent + '# goal: ' + show(goal))
            continue
        raise SystemExit('unknown directive: ' + s)
    return '\n'.join(out)


def gen(src, dst):
    text = open(src).read()
    res = expand(src, text, dst)
    new = '# GENERATED by tools/generators/rw.py from %s; edit the .src\n' % os.path.relpath(src, os.path.dirname(os.path.abspath(dst))) + res + ('' if res.endswith('\n') else '\n')
    if not os.path.exists(dst) or open(dst).read() != new:
        open(dst, 'w').write(new)
        print('wrote', dst)


if __name__ == '__main__' and sys.argv[1] == '--all':
    d, od = sys.argv[2], sys.argv[3]
    for name in sorted(os.listdir(d)):
        if name.endswith('.src'):
            gen(os.path.join(d, name), os.path.join(od, name[:-4] + '.bend'))
    sys.exit(0)

if __name__ == '__main__':
    src, dst = sys.argv[1], sys.argv[2]
    text = open(src).read()
    res = expand(src, text, dst)
    open(dst, 'w').write('# GENERATED by tools/generators/rw.py from %s; edit the .src\n' % os.path.relpath(src, os.path.dirname(os.path.abspath(dst))) + res + ('' if res.endswith('\n') else '\n'))
