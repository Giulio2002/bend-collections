#!/usr/bin/env python3
"""Generate the TreeMap's shadow mirror and its simulation proofs.

Reads src/containers/balanced_search_tree.bend and writes, in source order:

  proofs/tree_map/mirror.bend  one mirror function per implementation
                               function, over ST.Sh (the shadow) in place of
                               the TreeMap, MCursor/MView/MInvalid in place of
                               its cursors and views
  proofs/tree_map/sim.bend     for each mirrored function f, the lemmas
                                 f_g   the mirror keeps the arrays' layout
                                       (dag) whenever its inputs do
                                 f_s   M.f on the realizations of mirror
                                       values is the realization of the
                                       mirror's result

The array-level primitives (reads, writes, exchanges, appends, raw-array
walks) are written by hand in tools/generators/tm_hand/*.bend and inserted
at their place in source order.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SRC = ROOT / "src/containers/balanced_search_tree.bend"
HAND = ROOT / "tools/generators/tm_hand"
OUT_MIRROR = ROOT / "proofs/tree_map/mirror.bend"
OUT_SIM = ROOT / "proofs/tree_map/sim.bend"

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
            pats = split_top(l.strip()[len("case "):-1], " ")
            k += 1
            blk = []
            while k < len(lines) and indent(lines[k]) > base + 2:
                blk.append(lines[k])
                k += 1
            cases.append((pats, parse_body(blk)))
        return ("match", scruts, cases)
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

HANDF = {"new", "with_limit", "clear", "read", "write", "exchange", "get_id", "append", "neighbor_node"}
SKIP = {"read_finish", "write_finish", "exchange_finish", "append_rollback", "get_id_finish", "node_slot_done",
        "neighbor_slots_finish", "append_values", "node_slot_checked", "ascend_slots_step", "node_slot",
        "extreme_slots_probe", "ascend_slots_loop", "extreme_slots_loop", "append_nodes", "append_count",
        "neighbor_slots"}


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
    head = (HAND_DIR_TEXT("mirror_head.bend"))
    out = [head]
    for f in fns:
        if f.name in mapped and f.name not in HANDF:
            out.append(mirror_fn(f, cx))
    return "\n".join(out)


def HAND_DIR_TEXT(name):
    return (HAND / name).read_text()


if __name__ == "__main__":
    fns = parse_source(SRC.read_text())
    OUT_MIRROR.write_text(gen_mirror(fns))
    print("mirror written")
