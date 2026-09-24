#!/usr/bin/env python3
"""Generate the TreeMap's shadow mirror and its simulation proofs.

Reads src/containers/balanced_search_tree.bend and writes, in source order:

  proofs/containers/balanced_search_tree/mirror.bend  one mirror function per implementation
                               function, over ST.Sh (the shadow) in place of
                               the TreeMap, MCursor/MView/MInvalid in place of
                               its cursors and views
  proofs/containers/balanced_search_tree/sim.bend     for each mirrored function f, the lemmas
                                 f_g   the mirror keeps the arrays' layout
                                       (dag) whenever its inputs do
                                 f_s   M.f on the realizations of mirror
                                       values is the realization of the
                                       mirror's result

The array-level primitives (reads, writes, exchanges, appends, raw-array
walks) are written by hand in proofs/containers/balanced_search_tree/gen/*.part and inserted
at their place in source order.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "src/containers/balanced_search_tree.bend"
sys.path.insert(0, str(ROOT / "tools/generators"))
import pat_expand as PE
CONS = PE.load_types(SRC.read_text())
HAND = ROOT / "proofs/containers/balanced_search_tree/gen"
OUT_MIRROR = ROOT / "proofs/containers/balanced_search_tree/mirror.bend"
OUT_SIM = ROOT / "proofs/containers/balanced_search_tree/sim.bend"

TA = "~K, ~V, ~cmp"
TP = "~K: Data, ~V: Data, ~cmp: K -> K -> Cmp"

# ---------------------------------------------------------------- parsing

def split_top(s, sep=","):
    out, depth, cur = [], 0, ""
    prev = ""
    for ch in s:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}" or (ch == ">" and prev not in "-="):
            depth -= 1
        prev = ch
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


class Fn:
    def __init__(self, name, params, result, body):
        self.name, self.params, self.result, self.body = name, params, result, body


def parse_params(s):
    ps = []
    for p in split_top(s):
        m = re.match(r"^([~+\-]?)([A-Za-z_]\w*)\s*:\s*(.*)$", p)
        if not m:
            raise ValueError("param: " + p)
        ps.append((m.group(1), m.group(2), m.group(3).strip()))
    return ps


def find_sig_end(line):
    # the ') -> R:' closing the parameter list
    depth = 0
    for i, ch in enumerate(line):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i
    raise ValueError(line)


def parse_source(text):
    fns = []
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("def "):
            j = find_sig_end(line)
            head = line[4:line.index("(")]
            params = line[line.index("(") + 1:j]
            rest = line[j + 1:].strip()
            assert rest.startswith("->") and rest.endswith(":"), line
            result = rest[2:-1].strip()
            body = []
            i += 1
            while i < len(lines) and (lines[i].startswith(" ") or lines[i].strip() == ""):
                if lines[i].strip():
                    body.append(lines[i])
                i += 1
            fns.append(Fn(head, parse_params(params), result, body))
        else:
            i += 1
    return fns


# body tree: ("let", pat, expr, rest) | ("match", scruts, [(pats, body)]) | ("expr", e)
def indent(l):
    return len(l) - len(l.lstrip(" "))


def subst_str(t, sub):
    if not sub:
        return t
    pat = r"(?<![\w.])(" + "|".join(re.escape(k) for k in sorted(sub, key=len, reverse=True)) + r")(?!\w)"
    return re.sub(pat, lambda m: sub[m.group(1)], t)


def subst_body(b, sub):
    # rename the variables of a case body after row expansion
    if not sub:
        return b
    if b[0] == "expr":
        return ("expr", subst_str(b[1], sub))
    if b[0] == "let":
        return ("let", b[1], subst_str(b[2], sub), subst_body(b[3], sub))
    scr = [subst_str(x, sub) for x in b[1]]
    for x in scr:
        assert re.match(r"^\w+$", x), ("expanded scrutinee", x)
    return ("match", scr, [(pats, subst_body(body, sub)) for pats, body in b[2]])


def parse_body(lines):
    if not lines:
        raise ValueError("empty body")
    base = indent(lines[0])
    first = lines[0].strip()
    if first.startswith("match "):
        scruts = split_top(first[len("match "):-1], " ")
        cases = []
        k = 1
        while k < len(lines):
            l = lines[k]
            assert indent(l) == base + 2 and l.strip().startswith("case "), l
            pats = [x.replace("\x01", " +") for x in split_top(re.sub(r"(\d+n)\+ \+", "\\1+\x01", l.strip()[len("case "):-1]), " ")]
            k += 1
            blk = []
            while k < len(lines) and indent(lines[k]) > base + 2:
                blk.append(lines[k])
                k += 1
            cases.append((pats, parse_body(blk)))
        return ("match", scruts, [(pats, subst_body(body, sub)) for pats, sub, body in PE.expand(CONS, cases)])
    m = re.match(r"^(.*?)\s=\s(.*)$", first)
    if m and not first.startswith("(") or (m and re.match(r"^\(.*\)\s=\s", first)):
        if m and len(lines) > 1:
            return ("let", m.group(1).strip(), m.group(2).strip(), parse_body(lines[1:]))
    assert len(lines) == 1, lines
    return ("expr", first)


# ---------------------------------------------------------------- expressions

TOKEN = re.compile(r"\s*(~?[A-Za-z_][\w.]*|\d+n\+|\d+n|\d+|[(){}<>,&+:]|->|=>)")


class E:
    pass


class Call(E):
    def __init__(self, f, args):
        self.f, self.args = f, args


class Con(E):
    def __init__(self, c, args):
        self.c, self.args = c, args


class Tup(E):
    def __init__(self, a, b):
        self.a, self.b = a, b


class Atom(E):
    def __init__(self, s):
        self.s = s


class Succ(E):
    def __init__(self, k, e):
        self.k, self.e = k, e


def parse_expr(s):
    s = s.strip()
    # 1n+x
    m = re.match(r"^(\d+n)\+\s*(.*)$", s)
    if m and balanced(m.group(2)):
        return Succ(m.group(1), parse_expr(m.group(2)))
    if s.startswith("(") and s.endswith(")") and matching_paren(s, 0) == len(s) - 1:
        parts = split_top(s[1:-1])
        if len(parts) == 2:
            return Tup(parse_expr(parts[0]), parse_expr(parts[1]))
        if len(parts) == 1:
            return parse_expr(parts[0])
        raise ValueError(s)
    m = re.match(r"^([~A-Za-z_][\w.]*)\((.*)\)$", s, re.S)
    if m and matching_paren(s, s.index("(")) == len(s) - 1:
        return Call(m.group(1), [parse_expr(a) for a in split_top(m.group(2))])
    m = re.match(r"^([A-Za-z_][\w.]*)\{(.*)\}$", s, re.S)
    if m and matching_brace(s, s.index("{")) == len(s) - 1:
        inner = m.group(2).strip()
        return Con(m.group(1), [parse_expr(a) for a in split_top(inner)] if inner else [])
    return Atom(s)


def balanced(s):
    d = 0
    for ch in s:
        if ch in "([{":
            d += 1
        elif ch in ")]}":
            d -= 1
            if d < 0:
                return False
    return d == 0


def matching_paren(s, i):
    d = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            d += 1
        elif s[j] == ")":
            d -= 1
            if d == 0:
                return j
    return -1


def matching_brace(s, i):
    d = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            d += 1
        elif s[j] == "}":
            d -= 1
            if d == 0:
                return j
    return -1


# ---------------------------------------------------------------- kinds

MAPT = "TreeMap<K, V, cmp>"
CURT = "Cursor<K, V, cmp>"
VIEWT = "View<K, V, cmp>"
INVT = "InvalidView<K, V, cmp>"
REST = "Result<&1, &1, InvalidView<K, V, cmp>, View<K, V, cmp>>"


def kind(t):
    t = t.strip()
    if t == MAPT:
        return ("map", None)
    if t == CURT:
        return ("cur", None)
    if t == VIEWT:
        return ("view", None)
    if t == INVT:
        return ("inv", None)
    if t == REST:
        return ("res", None)
    parts = split_top(t, "&")
    if len(parts) >= 2:
        first = parts[0].strip()
        rest = " & ".join(parts[1:]).strip()
        k = kind(first)[0]
        if k in ("map", "cur", "view"):
            return ("p" + k, rest)
    return ("plain", None)


def is_mapkind(t):
    return kind(t)[0] != "plain"


IMPL_TYPES = ["Node", "Entry", "Error", "Rejected", "Search", "Fix", "Ascend", "DeleteFix", "Bound"]
IMPL_CONS = ["Free", "N", "Entry", "CapacityExceeded", "OutOfRange", "NoCurrent", "InvalidBounds",
             "Rejected", "Search", "Fix", "Ascend", "DF", "Unbounded", "Inclusive", "Exclusive"]


def qual(t):
    # impl datatypes and constructors, qualified
    for n in IMPL_TYPES:
        t = re.sub(r"(?<![\w.])" + n + r"(?![\w])", "M." + n, t)
    for n in IMPL_CONS:
        t = re.sub(r"(?<![\w.])" + n + r"(?=\{)", "M." + n, t)
    return t


def mtype(t):
    # the mirror's type of an impl type
    t = t.replace(REST, "Result<&1, &1, MInvalid<K, V>, MView<K, V>>")
    t = t.replace(MAPT, "ST.Sh<K, V>").replace(CURT, "MCursor<K, V>").replace(VIEWT, "MView<K, V>").replace(INVT, "MInvalid<K, V>")
    return qual(t)


def itype(t):
    # the impl type, qualified for use outside the impl module
    t = t.replace(REST, "Result<&1, &1, M.InvalidView<K, V, cmp>, M.View<K, V, cmp>>")
    t = re.sub(r"(?<![\w.])(TreeMap|Cursor|View|InvalidView)(?=<)", r"M.\1", t)
    return qual(t)


# ---------------------------------------------------------------- classification

HANDF = {"new", "with_limit", "clear", "read", "write", "exchange", "get_id", "append", "neighbor_node", "set_left", "set_right", "set_parent", "set_red", "search", "navigate", "iterator_next"}
SKIP = {"read_finish", "write_finish", "exchange_finish", "append_rollback", "get_id_finish", "node_slot_done",
        "neighbor_slots_finish", "append_values", "node_slot_checked", "ascend_slots_step", "node_slot",
        "extreme_slots_probe", "ascend_slots_loop", "extreme_slots_loop", "append_nodes", "append_count",
        "neighbor_slots", "neighbor_used", "side_at", "ascend_par", "ascend_side", "ascend_tag", "ascend_at", "extreme_tag", "extreme_at", "search_key", "search_probe", "search_down2", "search_down", "search_fast", "search_fin", "nav_fast", "nav_end", "iter_child", "iter_link", "iter_valid", "iter_kv", "iter_key", "iter_value", "iter_at"}


def classify(fns):
    mapped, pure = set(), set()
    for f in fns:
        tys = [t for _, _, t in f.params] + [f.result]
        if f.name in SKIP:
            continue
        if f.name in HANDF or any(is_mapkind(t) for t in tys):
            mapped.add(f.name)
        else:
            pure.add(f.name)
    return mapped, pure


# ---------------------------------------------------------------- printing

class Ctx:
    def __init__(self, mapped, pure):
        self.mapped, self.pure = mapped, pure
        self.tm = {}      # nodes var -> suffix, payloads var -> suffix


def tm_fields(sfx):
    return [f"l{sfx}", f"d{sfx}", f"nl{sfx}", f"pl{sfx}", f"t{sfx}", f"fl{sfx}"]


def mpat(p, cx, sfx_counter):
    # translate a pattern for the mirror
    p = p.strip()
    m = re.match(r"^TM\{(.*)\}$", p)
    if m:
        fs = split_top(m.group(1))
        assert len(fs) == 7, p
        sfx = "_%d" % sfx_counter[0]
        sfx_counter[0] += 1
        cx.tm[fs[5].lstrip("+")] = ("nodes", sfx)
        cx.tm[fs[6].lstrip("+")] = ("pays", sfx)
        head = ["+" + x.lstrip("+") for x in fs[:5]]
        return "ST.SH{" + ", ".join(head + ["+" + x for x in tm_fields(sfx)]) + "}"
    m = re.match(r"^([A-Za-z_][\w.]*)\{(.*)\}$", p)
    if m:
        c = m.group(1)
        inner = [mpat(x, cx, sfx_counter) for x in split_top(m.group(2))] if m.group(2).strip() else []
        c2 = {"Cursor": "MC", "View": "MV", "InvalidView": "MI"}.get(c, None)
        if c2 is None:
            c2 = ("M." + c) if c in IMPL_CONS else c
        return c2 + "{" + ", ".join(inner) + "}"
    if p.startswith("(") and p.endswith(")"):
        inner = split_top(p[1:-1])
        return "(" + ", ".join(mpat(x, cx, sfx_counter) for x in inner) + ")"
    return p


def mexpr(e, cx):
    # mirror-side printing of an impl expression
    if isinstance(e, Atom):
        return e.s
    if isinstance(e, Succ):
        return e.k + "+" + mexpr(e.e, cx)
    if isinstance(e, Tup):
        return "(" + mexpr(e.a, cx) + ", " + mexpr(e.b, cx) + ")"
    if isinstance(e, Con):
        if e.c == "TM":
            a = [mexpr(x, cx) for x in e.args]
            nv = e.args[5].s if isinstance(e.args[5], Atom) else None
            pv = e.args[6].s if isinstance(e.args[6], Atom) else None
            assert nv in cx.tm and pv in cx.tm and cx.tm[nv][1] == cx.tm[pv][1], "TM rebuild"
            return "ST.SH{" + ", ".join(a[:5] + tm_fields(cx.tm[nv][1])) + "}"
        c2 = {"Cursor": "MC", "View": "MV", "InvalidView": "MI"}.get(e.c, None)
        if c2 is None:
            c2 = ("M." + e.c) if e.c in IMPL_CONS else e.c
        return c2 + "{" + ", ".join(mexpr(x, cx) for x in e.args) + "}"
    if isinstance(e, Call):
        f = e.f
        args = ", ".join(mexpr(x, cx) for x in e.args)
        if f in cx.pure:
            return "M." + f + "(" + args + ")"
        if f in cx.mapped:
            return f + "(" + args + ")"
        return qual_call(f) + "(" + args + ")"
    raise ValueError(e)


def qual_call(f):
    # a type used as an argument (pick's T, Array element types)
    if f in IMPL_TYPES:
        return "M." + f
    return f


def fix_types_in_args(s):
    return mtype(s)


def mirror_body(b, cx, ind, sc):
    pad = " " * ind
    if b[0] == "expr":
        return pad + fix_types_in_args(mexpr(parse_expr(b[1]), cx)) + "\n"
    if b[0] == "let":
        pat, ex, rest = b[1], b[2], b[3]
        pm = mpat(pat, cx, sc)
        if pm.startswith("ST.SH{") or pm.startswith("MV{ST.SH{"):
            # destructuring of the map: a match (fields are Data)
            return pad + "match " + ex + ":\n" + pad + "  case " + pm + ":\n" + mirror_body(rest, cx, ind + 4, sc)
        return pad + pm + " = " + fix_types_in_args(mexpr(parse_expr(ex), cx)) + "\n" + mirror_body(rest, cx, ind, sc)
    if b[0] == "match":
        out = pad + "match " + " ".join(b[1]) + ":\n"
        for pats, body in b[2]:
            out += pad + "  case " + " ".join(mpat(p, cx, sc) for p in pats) + ":\n"
            out += mirror_body(body, cx, ind + 4, sc)
        return out
    raise ValueError(b)


def mirror_fn(f, cx):
    ps = ", ".join((m + n + ": " + mtype(t)) for m, n, t in f.params)
    sig = f"def {f.name}({ps}) -> {mtype(f.result)}:\n"
    cx.tm = {}
    return sig + mirror_body(parse_body(f.body), cx, 2, [0])


def gen_mirror(fns):
    mapped, pure = classify(fns)
    cx = Ctx(mapped, pure)
    head = (HAND_DIR_TEXT("mirror_head.part"))
    out = [head]
    for f in fns:
        if f.name in mapped and f.name not in HANDF:
            out.append(mirror_fn(f, cx))
        elif f.name in HANDF and (HAND / "mirror" / (f.name + ".part")).exists():
            # a hand-written mirror placed at its function's source position
            out.append((HAND / "mirror" / (f.name + ".part")).read_text())
    return "\n".join(out)


def HAND_DIR_TEXT(name):
    return (HAND / name).read_text()


# ---------------------------------------------------------------- simulation lemmas

LIFT = {"map": "ST.real({TA}, {e})", "cur": "MI.rc({TA}, {e})", "view": "MI.rv({TA}, {e})",
        "inv": "MI.ri({TA}, {e})", "res": "MI.rr({TA}, {e})",
        "pmap": "MI.rp({TA}, {X}, {e})", "pcur": "MI.rcp({TA}, {X}, {e})", "pview": "MI.rvp({TA}, {X}, {e})"}
DAG = {"map": "MI.dg(K, V, {e})", "cur": "MI.dgc(K, V, {e})", "view": "MI.dgv(K, V, {e})",
       "inv": "MI.dgi(K, V, {e})", "res": "MI.dgr(K, V, {e})",
       "pmap": "MI.dgp(K, V, {X}, {e})", "pcur": "MI.dgcp(K, V, {X}, {e})", "pview": "MI.dgvp(K, V, {X}, {e})"}


def lift(k, X, e):
    return LIFT[k].format(TA=TA, X=mtype(X) if X else "", e=e)


def dagt(k, X, e):
    return DAG[k].format(X=mtype(X) if X else "", e=e)


class Node:
    pass


class PG:
    """Proof generation for one function."""

    def __init__(self, f, fns, mapped, pure):
        self.f, self.fns, self.mapped, self.pure = f, fns, mapped, pure
        self.ctx = {}      # var -> (kind, X, dagproof)
        self.tm = {}       # nodes/pays var -> (sfx, dagproof)
        self.sc = [0]
        self.ptypes = {n: t for m, n, t in f.params}

    # ---- node annotation ----
    def sside(self, e):
        if isinstance(e, Atom):
            return qual(e.s) if re.match(r"^[A-Z]\w*<", e.s) else e.s
        if isinstance(e, Succ):
            return e.k + "+" + self.sside(e.e)
        if isinstance(e, Tup):
            return "(" + self.sside(e.a) + ", " + self.sside(e.b) + ")"
        if isinstance(e, Con):
            if e.c == "TM":
                a = [self.sside(x) for x in e.args]
                sfx = self.tm[e.args[5].s][0]
                return "ST.SH{" + ", ".join(a[:5] + tm_fields(sfx)) + "}"
            c2 = {"Cursor": "MI.MC", "View": "MI.MV", "InvalidView": "MI.MI"}.get(e.c)
            if c2 is None:
                c2 = ("M." + e.c) if e.c in IMPL_CONS else e.c
            return c2 + "{" + ", ".join(self.sside(x) for x in e.args) + "}"
        if isinstance(e, Call):
            args = ", ".join(self.sside(x) for x in e.args)
            if e.f in self.mapped:
                return "MI." + e.f + "(" + args + ")"
            if e.f in self.pure:
                return "M." + e.f + "(" + args + ")"
            return qual_call(e.f) + "(" + args + ")"
        raise ValueError(e)

    def kind_of(self, e):
        if isinstance(e, Atom):
            if e.s in self.ctx:
                return self.ctx[e.s][0], self.ctx[e.s][1]
            return "plain", None
        if isinstance(e, Call):
            if e.f in self.mapped:
                g = self.fns[e.f]
                return kind(g.result)
            return "plain", None
        if isinstance(e, Tup):
            k, X = self.kind_of(e.a)
            if k in ("map", "cur", "view"):
                return "p" + k, "?"
            return "plain", None
        if isinstance(e, Con):
            if e.c == "TM":
                return "map", None
            if e.c == "Cursor":
                return "cur", None
            if e.c == "View":
                return "view", None
            if e.c == "InvalidView":
                return "inv", None
            if e.c in ("Done", "Fail") and e.args and self.kind_of(e.args[0])[0] in ("view", "inv"):
                return "res", None
            return "plain", None
        return "plain", None

    def dagproof(self, e):
        if isinstance(e, Atom):
            return self.ctx[e.s][2]
        if isinstance(e, Call):
            g = self.fns[e.f]
            sargs = [self.sside(x) for x in e.args]
            dags = [self.dagproof(x) for (m, n, t), x in zip(g.params, e.args) if is_mapkind(t)]
            return e.f + "_g(" + ", ".join(sargs + dags) + ")"
        if isinstance(e, Tup):
            return self.dagproof(e.a)
        if isinstance(e, Con):
            if e.c == "TM":
                return self.tm[e.args[5].s][1]
            return self.dagproof(e.args[0])
        raise ValueError(e)

    # the M-side printing, with rewritten calls replaced by their lifts
    def mside(self, e, done):
        if id(e) in done:
            return done[id(e)]
        if isinstance(e, Atom):
            if e.s in self.ctx:
                k, X, _ = self.ctx[e.s]
                return lift(k, X, e.s)
            return qual(e.s) if re.match(r"^[A-Z]\w*<", e.s) else e.s
        if isinstance(e, Succ):
            return e.k + "+" + self.mside(e.e, done)
        if isinstance(e, Tup):
            return "(" + self.mside(e.a, done) + ", " + self.mside(e.b, done) + ")"
        if isinstance(e, Con):
            if e.c == "TM":
                return "ST.real(" + TA + ", " + self.sside(e) + ")"
            c2 = {"Cursor": "M.Cursor", "View": "M.View", "InvalidView": "M.InvalidView"}.get(e.c)
            if c2 is None:
                c2 = ("M." + e.c) if e.c in IMPL_CONS else e.c
            return c2 + "{" + ", ".join(self.mside(x, done) for x in e.args) + "}"
        if isinstance(e, Call):
            return ("M." + e.f if (e.f in self.mapped or e.f in self.pure) else qual_call(e.f)) + "(" + ", ".join(self.mside(x, done) for x in e.args) + ")"
        raise ValueError(e)

    def lemma_call(self, e):
        g = self.fns[e.f]
        sargs = [self.sside(x) for x in e.args]
        dags = [self.dagproof(x) for (m, n, t), x in zip(g.params, e.args) if is_mapkind(t)]
        return e.f + "_s(" + ", ".join(sargs + dags) + ")"

    def mapcalls(self, e, acc):
        # post-order list of mapped calls
        if isinstance(e, Call):
            for x in e.args:
                self.mapcalls(x, acc)
            if e.f in self.mapped:
                acc.append(e)
        elif isinstance(e, Tup):
            self.mapcalls(e.a, acc)
            self.mapcalls(e.b, acc)
        elif isinstance(e, Con):
            for x in e.args:
                self.mapcalls(x, acc)
        elif isinstance(e, Succ):
            self.mapcalls(e.e, acc)

    def prove_expr(self, e, rhs, rtype, ind):
        pad = " " * ind
        calls = []
        self.mapcalls(e, calls)
        done = {}
        out = ""
        for c in calls:
            if c is e:
                break
            g = self.fns[c.f]
            k, X = kind(g.result)
            before = self.mside(c, done)
            after = lift(k, X, self.sside(c))
            done[id(c)] = "_"
            goal = self.mside(e, done)
            done[id(c)] = after
            out += pad + "%Equal.sym(" + itype(g.result) + ", " + before + ", " + after + ", " + self.lemma_call(c) + ") : {" + goal + " == " + rhs + " : " + rtype + "}\n"
        if calls and calls[-1] is e:
            out += pad + self.lemma_call(e) + "\n"
        else:
            out += pad + "{==}\n"
        return out

    # ---- patterns ----
    def bind_pat(self, pat, k, X, dagp):
        # bind the variables of an impl pattern for a value of kind k
        pat = pat.strip()
        if k == "map":
            m = re.match(r"^TM\{(.*)\}$", pat)
            if m:
                fs = split_top(m.group(1))
                sfx = "_%d" % self.sc[0]
                self.sc[0] += 1
                self.tm[fs[5].lstrip("+")] = (sfx, dagp)
                self.tm[fs[6].lstrip("+")] = (sfx, dagp)
                head = ["+" + x.lstrip("+") for x in fs[:5]]
                return "ST.SH{" + ", ".join(head + ["+" + x for x in tm_fields(sfx)]) + "}"
            v = pat.lstrip("+")
            self.ctx[v] = ("map", None, dagp)
            return "+" + v
        if k in ("pmap", "pcur", "pview"):
            inner = split_top(pat[1:-1]) if pat.startswith("(") else split_top(re.match(r"^Tuple\{(.*)\}$", pat).group(1))
            a = self.bind_pat(inner[0], k[1:], None, dagp)
            b = mpat_q(inner[1], X, 1)
            return "Tuple{" + a + ", " + b + "}"
        if k == "cur":
            m = re.match(r"^Cursor\{(.*)\}$", pat)
            if m:
                fs = split_top(m.group(1))
                a = self.bind_pat(fs[0], "map", None, dagp)
                return "MI.MC{" + ", ".join([a] + [mpat_q(x) for x in fs[1:]]) + "}"
            v = pat.lstrip("+")
            self.ctx[v] = ("cur", None, dagp)
            return "+" + v
        if k == "view":
            m = re.match(r"^View\{(.*)\}$", pat)
            if m:
                fs = split_top(m.group(1))
                a = self.bind_pat(fs[0], "map", None, dagp)
                return "MI.MV{" + ", ".join([a] + [mpat_q(x) for x in fs[1:]]) + "}"
            v = pat.lstrip("+")
            self.ctx[v] = ("view", None, dagp)
            return "+" + v
        return mpat_q(pat)

    def rebuild(self, patm):
        # the expression of a (mirror) pattern
        return re.sub(r"(^|[\s{(,])\+", r"\1", patm)

    def body(self, b, vals, rhs_f, rtype, ind, dag_mode):
        pad = " " * ind
        if b[0] == "expr":
            e = parse_expr(b[1])
            if dag_mode:
                return pad + self.dagproof(e) + "\n"
            return self.prove_expr(e, rhs_f(vals), rtype, ind)
        if b[0] == "let":
            pat, ex, rest = b[1], b[2], b[3]
            exs = ex.strip()
            if exs in self.ctx and (pat.startswith("(") or re.match(r"^(TM|Cursor|View)\{", pat)):
                k, X, dagp = self.ctx[exs]
                pm = self.bind_pat(pat, k, X, dagp)
                nv = dict(vals)
                nv[exs] = self.rebuild(pm)
                return pad + "match " + exs + ":\n" + pad + "  case " + pm + ":\n" + self.body(rest, nv, rhs_f, rtype, ind + 4, dag_mode)
            m = re.match(r"^\+?(\w+)$", pat)
            assert m, (self.f.name, pat)
            v = m.group(1)
            e = parse_expr(ex)
            k, X = self.kind_of(e)
            line = pad + "+" + v + " = " + self.sside(e) + "\n"
            if k != "plain":
                raise ValueError("map let " + self.f.name)
            return line + self.body(rest, vals, rhs_f, rtype, ind, dag_mode)
        if b[0] == "match":
            scr = b[1]
            out = pad + "match " + " ".join(scr) + ":\n"
            for pats, body in b[2]:
                nv = dict(vals)
                pm = []
                for s_, p in zip(scr, pats):
                    if s_ in self.ctx:
                        k, X, dagp = self.ctx[s_]
                        q = self.bind_pat(p, k, X, dagp)
                    else:
                        q = mpat_q(p, self.ptypes.get(s_))
                    pm.append(q)
                    nv[s_] = self.rebuild(q)
                out += pad + "  case " + " ".join(pm) + ":\n"
                out += self.body(body, nv, rhs_f, rtype, ind + 4, dag_mode)
            return out
        raise ValueError(b)

    def emit(self):
        f = self.f
        rk, rX = kind(f.result)
        params, hyps, names = [], [], []
        for m, n, t in f.params:
            if m == "~":
                params.append("~" + n + ": " + t)
                names.append(n)
                continue
            k, X = kind(t)
            params.append(("" if (len(split_top(mtype(t), "&")) > 1 or "Array<" in mtype(t)) else "+") + n + ": " + mtype(t).replace("ST.Sh", "ST.Sh").replace("MCursor", "MI.MCursor").replace("MView", "MI.MView").replace("MInvalid", "MI.MInvalid"))
            names.append(n)
            if k != "plain":
                hyps.append((n, k, X))
        out = ""
        base_ctx = {}
        for n, k, X in hyps:
            base_ctx[n] = (k, X, "g_" + n)
        hyp_s = ["+g_" + n + ": {" + dagt(k, X, n) + " == True{} : Bool}" for n, k, X in hyps]
        tpl = ", ".join(("~" if m == "~" else "") + n for m, n, t in f.params)

        def call_s(vals):
            return "MI." + f.name + "(" + ", ".join((("~" + n) if m == "~" else vals.get(n, n)) for m, n, t in f.params) + ")"

        def lhs(vals):
            return "M." + f.name + "(" + ", ".join((("~" + n) if m == "~" else (lift(kind(t)[0], kind(t)[1], vals.get(n, n)) if is_mapkind(t) else vals.get(n, n))) for m, n, t in f.params) + ")"
        sig = ", ".join(params + hyp_s)
        rtype = itype(f.result)
        # the dag lemma
        if rk != "plain":
            self.ctx = dict(base_ctx)
            self.tm = {}
            self.sc = [0]
            out += f"def {f.name}_g({sig}) -> {{{dagt(rk, rX, call_s({}))} == True{{}} : Bool}}:\n"
            out += self.body(parse_body(f.body), {}, None, None, 2, True)
            out += "\n"
        self.ctx = dict(base_ctx)
        self.tm = {}
        self.sc = [0]
        rhs_f = (lambda vals: lift(rk, rX, call_s(vals))) if rk != "plain" else (lambda vals: call_s(vals))
        out += f"def {f.name}_s({sig}) -> {{{lhs({})} == {rhs_f({})} : {rtype}}}:\n"
        out += self.body(parse_body(f.body), {}, rhs_f, rtype, 2, False)
        return out + "\n"


def mpat_q(p, t=None, depth=0):
    # an impl pattern of plain data, qualified; t: its type when known (a
    # variable of a pair or array type stays affine), depth: the tuples
    # around it (a variable directly inside a nested pair stays affine too:
    # the checker cannot type an unrestricted binder there)
    p = p.strip()
    m = re.match(r"^([A-Za-z_][\w.]*)\{(.*)\}$", p)
    subs = None
    if m:
        c = m.group(1)
        subs = split_top(m.group(2)) if m.group(2).strip() else []
        if c != "Tuple":
            c2 = ("M." + c) if c in IMPL_CONS else c
            return c2 + "{" + ", ".join(mpat_q(x) for x in subs) + "}"
    elif p.startswith("(") and p.endswith(")"):
        subs = split_top(p[1:-1])
    if subs is not None:
        return "Tuple{" + ", ".join(mpat_q(x, y, depth + 1) for x, y in zip(subs, tuple_types(t, len(subs)))) + "}"
    if re.match(r"^\+?[a-z_]\w*$", p) and p != "_":
        v = p.lstrip("+")
        if depth >= 2:
            return v
        if t is not None and (len(split_top(t, "&")) > 1 or "Array<" in t or (t.startswith("(") and "&" in t)):
            return v
        return "+" + v
    m = re.match(r"^(\d+n)\+\s*\+?([a-z_]\w*)$", p)
    if m:
        return m.group(1) + "+ +" + m.group(2)
    return p


def tuple_types(t, n):
    if t is None:
        return [None] * n
    t = t.strip()
    while t.startswith("(") and matching_paren(t, 0) == len(t) - 1:
        t = t[1:-1].strip()
    parts = split_top(t, "&")
    if len(parts) < 2:
        return [None] * n
    return [parts[0].strip(), " & ".join(x.strip() for x in parts[1:])] + [None] * (n - 2)


def gen_sim(fns):
    mapped, pure = classify(fns)
    byname = {f.name: f for f in fns}
    out = [HAND_DIR_TEXT("sim_head.part")]
    errs = 0
    for f in fns:
        if f.name in mapped and f.name not in HANDF:
            try:
                out.append(PG(f, byname, mapped, pure).emit())
            except Exception as ex:
                errs += 1
                out.append("# FAILED " + f.name + ": " + str(ex) + "\n")
        elif f.name in HANDF and (HAND / "sim" / (f.name + ".part")).exists():
            out.append((HAND / "sim" / (f.name + ".part")).read_text())
    import mac
    return mac.expand("\n".join(out).split("\n")), errs


if __name__ == "__main__":
    fns = parse_source(SRC.read_text())
    OUT_MIRROR.write_text(gen_mirror(fns))
    txt, errs = gen_sim(fns)
    OUT_SIM.write_text(txt)
    # hand-written parts sit at their function's source position; a callee
    # can still follow its caller there, so order both files by dependency
    import subprocess
    for out in (OUT_MIRROR, OUT_SIM):
        subprocess.run([sys.executable, str(ROOT / "tools/toposort.py"), str(out)], check=True)
    print("mirror and sim written;", errs, "functions failed")
