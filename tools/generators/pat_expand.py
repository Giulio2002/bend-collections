# Case-row expansion for the proof generators: a match whose rows overlap
# (a later row repeating what an earlier one caught, like a trailing `_`)
# becomes disjoint constructor rows, each with the body of the first
# original row matching it. The checker reduces a function only on a row
# its scrutinees fit, so the proofs need every row to name its shape.
import re

BUILTIN = {
    "True": ("Bool", 0), "False": ("Bool", 0),
    "None": ("Maybe", 0), "Some": ("Maybe", 1),
    "Done": ("Result", 1), "Fail": ("Result", 1),
    "LT": ("Cmp", 0), "EQ": ("Cmp", 0), "GT": ("Cmp", 0),
    "Tuple": ("Tuple", 2), "Nil": ("List", 0), "Con": ("List", 2),
    "Unit": ("Unit", 0),
}


def split_top(s, sep=","):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "({[<":
            depth += 1
        elif ch in ")}]>":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def load_types(text):
    # constructor -> (type, arity) from `type Name ...:` blocks
    cons = dict(BUILTIN)
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        m = re.match(r"^type (\w+)", lines[i])
        if not m:
            i += 1
            continue
        t = m.group(1)
        i += 1
        buf = ""
        while i < len(lines) and lines[i].startswith(" "):
            buf += " " + lines[i].strip()
            if buf.count("{") == buf.count("}"):
                c = re.match(r"^\s*(\w+)\{(.*)\}\s*$", buf)
                if c:
                    cons[c.group(1)] = (t, len(split_top(c.group(2))) if c.group(2).strip() else 0)
                buf = ""
            i += 1
    return cons


class Var:
    def __init__(self, name, plus):
        self.name, self.plus = name, plus


class Con:
    def __init__(self, c, subs):
        self.c, self.subs = c, subs


class Zero:
    pass


class Succ:
    def __init__(self, k, sub):
        self.k, self.sub = k, sub


def parse(p):
    p = p.strip()
    m = re.match(r"^(\d+)n\+\s*(.*)$", p)
    if m:
        return Succ(int(m.group(1)), parse(m.group(2)))
    if re.match(r"^\d+n$", p):
        n = int(p[:-1])
        r = Zero()
        for _ in range(n):
            r = Succ(1, r)
        return r
    m = re.match(r"^([A-Za-z_][\w.]*)\{(.*)\}$", p, re.S)
    if m:
        return Con(m.group(1), [parse(x) for x in split_top(m.group(2))] if m.group(2).strip() else [])
    if p.startswith("(") and p.endswith(")"):
        return Con("Tuple", [parse(x) for x in split_top(p[1:-1])])
    plus = p.startswith("+")
    return Var(p.lstrip("+").strip(), plus)


def show(p):
    if isinstance(p, Var):
        return ("+" if p.plus else "") + p.name
    if isinstance(p, Zero):
        return "0n"
    if isinstance(p, Succ):
        s = show(p.sub)
        return "%dn+%s" % (p.k, (" " + s) if s.startswith("+") else s)
    return p.c + "{" + ", ".join(show(x) for x in p.subs) + "}"


def term(p):
    if isinstance(p, Var):
        return p.name
    if isinstance(p, Zero):
        return "0n"
    if isinstance(p, Succ):
        return "%dn+%s" % (p.k, term(p.sub))
    return p.c + "{" + ", ".join(term(x) for x in p.subs) + "}"


class Ctx:
    def __init__(self, cons):
        self.cons = cons
        self.n = 0

    def fresh(self):
        self.n += 1
        return Var("px%d" % self.n, False)

    def siblings(self, c):
        base = c.split(".")[-1]
        pre = c[: len(c) - len(base)]
        t = self.cons[base][0]
        return [(pre + k, a) for k, (tt, a) in self.cons.items() if tt == t]

    def expand_var(self, like):
        # the shapes a variable can take, following the pattern `like`
        if isinstance(like, (Zero, Succ)):
            k = like.k if isinstance(like, Succ) else 1
            out = []
            for j in range(k):
                z = Zero()
                for _ in range(j):
                    z = Succ(1, z)
                out.append(z)
            out.append(Succ(k, self.fresh()))
            return out
        return [Con(c, [self.fresh() for _ in range(a)]) for c, a in self.siblings(like.c)]

    def meet(self, p, q, sub):
        # p: vector pattern (fresh names), q: row pattern. returns
        # (intersection or None, [differences]); the intersection keeps p's
        # names, and sub maps q's variables to terms over them
        if isinstance(q, Var):
            if q.name != "_":
                sub[q.name] = (term(p), q.plus)
            return p, []
        if isinstance(p, Var):
            inter, diff = None, []
            for s in self.expand_var(q):
                i2, d2 = self.meet(s, q, sub)
                if i2 is not None:
                    inter = i2
                diff += d2
            return inter, diff
        if isinstance(p, Zero):
            return (p, []) if isinstance(q, Zero) else (None, [p])
        if isinstance(p, Succ):
            if isinstance(q, Zero):
                return None, [p]
            if p.k != q.k:
                return self.meet(unfold(p), unfold(q), sub)
            i, d = self.meet(p.sub, q.sub, sub)
            return (Succ(p.k, i) if i is not None else None), [Succ(p.k, x) for x in d]
        if isinstance(q, (Zero, Succ)) or p.c.split(".")[-1] != q.c.split(".")[-1]:
            return None, [p]
        ints, diffs = self.meet_vec(p.subs, q.subs, sub)
        return (Con(p.c, ints) if ints is not None else None), [Con(p.c, d) for d in diffs]

    def meet_vec(self, ps, qs, sub):
        ints, diffs = [], []
        for i, (p, q) in enumerate(zip(ps, qs)):
            it, df = self.meet(p, q, sub)
            for d in df:
                diffs.append(ints + [d] + list(ps[i + 1:]))
            if it is None:
                return None, diffs
            ints.append(it)
        return ints, diffs


def mark(p, names):
    if isinstance(p, Var):
        p.plus = p.name in names
    elif isinstance(p, Succ):
        mark(p.sub, names)
    elif isinstance(p, Con):
        for x in p.subs:
            mark(x, names)


def copy(p):
    if isinstance(p, Var):
        return Var(p.name, p.plus)
    if isinstance(p, Succ):
        return Succ(p.k, copy(p.sub))
    if isinstance(p, Con):
        return Con(p.c, [copy(x) for x in p.subs])
    return p


def unfold(p):
    if isinstance(p, Succ) and p.k > 1:
        return Succ(1, Succ(p.k - 1, p.sub))
    return p


def overlapping(ctx, rows):
    for i in range(len(rows)):
        for j in range(i):
            it, _ = ctx.meet_vec([parse(x) for x in rows[j]], [parse(x) for x in rows[i]], {})
            if it is not None:
                return True
    return False


def paths(p, pre, acc):
    # the positions where a pattern names a shape
    if isinstance(p, Var):
        return
    if isinstance(p, (Zero, Succ)):
        acc.setdefault(pre, p)
        if isinstance(p, Succ):
            paths(p.sub, pre + ("S",), acc)
        return
    acc.setdefault(pre, p)
    for i, x in enumerate(p.subs):
        paths(x, pre + (p.c.split(".")[-1], i), acc)


def splits(ctx, like):
    # a position worth splitting: a sum type (records other than pairs stay)
    if isinstance(like, (Zero, Succ)):
        return True
    base = like.c.split(".")[-1]
    return base == "Tuple" or len(ctx.siblings(like.c)) > 1


def refine(ctx, p, pre, acc):
    # every variable at a position some row splits becomes each shape
    if isinstance(p, Var):
        if pre in acc and splits(ctx, acc[pre]):
            out = []
            for s in ctx.expand_var(acc[pre]):
                for q, sub in refine(ctx, s, pre, acc):
                    out.append((q, dict(sub, **{p.name: term(q)})))
            return out
        return [(p, {})]
    if isinstance(p, Zero):
        return [(p, {})]
    if isinstance(p, Succ):
        return [(Succ(p.k, q), sub) for q, sub in refine(ctx, p.sub, pre + ("S",), acc)]
    res = [([], {})]
    for i, x in enumerate(p.subs):
        opts = refine(ctx, x, pre + (p.c.split(".")[-1], i), acc)
        res = [(qs + [q], dict(s1, **s2)) for qs, s1 in res for q, s2 in opts]
    return [(Con(p.c, qs), sub) for qs, sub in res]


def refine_vec(ctx, ps, acc):
    res = [([], {})]
    for i, x in enumerate(ps):
        opts = refine(ctx, x, (i,), acc)
        res = [(qs + [q], dict(s1, **s2)) for qs, s1 in res for q, s2 in opts]
    return res


def resub(sub, inner):
    # sub's terms with the refined variables replaced
    if not inner:
        return sub
    pat = r"(?<![\w.])(" + "|".join(re.escape(k) for k in sorted(inner, key=len, reverse=True)) + r")(?!\w)"
    return {k: re.sub(pat, lambda m: inner[m.group(1)], t) for k, t in sub.items()}


def expand(cons, rows):
    # rows: [(pats, body)]; returns [(pats, subst, body)] disjoint, every
    # position a row splits split in every row, subst mapping the original
    # row's variables to terms over the new names
    if len(rows) < 2:
        return [(pats, {}, body) for pats, body in rows]
    ctx = Ctx(cons)
    acc = {}
    for pats, _ in rows:
        for i, x in enumerate(pats):
            paths(parse(x), (i,), acc)
    n = len(rows[0][0])
    remaining = [[ctx.fresh() for _ in range(n)]]
    out = []
    for pats, body in rows:
        qs = [parse(x) for x in pats]
        nxt = []
        for v in remaining:
            sub = {}
            it, df = ctx.meet_vec(v, qs, sub)
            if it is not None:
                for it2, inner in refine_vec(ctx, it, acc):
                    it2 = [copy(x) for x in it2]
                    sub2 = resub({k: t for k, (t, _) in sub.items()}, inner)
                    plus = set()
                    for k, (t, pl) in sub.items():
                        if pl:
                            plus |= set(re.findall(r"px\d+", sub2[k]))
                    for x in it2:
                        mark(x, plus)
                    out.append(([show(x) for x in it2], sub2, body))
            nxt += df
        remaining = nxt
    return out
