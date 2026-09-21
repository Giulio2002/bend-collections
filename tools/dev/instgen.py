#!/usr/bin/env python3
"""Dev helper: emit concrete instantiations of `~V` template defs.

  python3 tools/dev/instgen.py proofs/lru_fast/remove.bend RM U32 remove_real remove_inv

For each named def (signature on one line), prints

  def <name>_<ty>(<params without ~V>) -> <result with V := ty>:
    <MOD>.<name>(~<ty>, <params>)

qualifying the module's own defs with MOD. Instantiating is what makes the
checker check a template (see docs/lru-compat.md); nothing else is generated.
"""
import re
import sys


def split_params(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '({<[':
            depth += 1
        elif ch in ')}>]':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def main():
    path, mod, ty = sys.argv[1:4]
    names = sys.argv[4:]
    src = open(path).read()
    local = set(re.findall(r'^def (\w+)', src, re.M))
    for name in names:
        m = re.search(r'^def %s\((.*)\) -> (.*):$' % re.escape(name), src, re.M)
        if not m:
            sys.exit('no one-line signature for %s' % name)
        params, ret = m.group(1), m.group(2)
        ps = split_params(params)
        assert ps[0] == '~V: Data', ps[0]
        ps = ps[1:]

        def subst(t):
            t = re.sub(r'(?<![\w.])V(?!\w)', ty, t)
            t = re.sub(r'(?<![\w.])(%s)\(' % '|'.join(sorted(local, key=len, reverse=True)), mod + r'.\1(', t)
            return t
        ps2 = [subst(p) for p in ps]
        args = [p.split(':')[0].lstrip('+-~ ').strip() for p in ps]
        print('def %s_%s(%s) -> %s:' % (name, ty.lower(), ', '.join(ps2), subst(ret)))
        print('  %s.%s(~%s, %s)' % (mod, name, ty, ', '.join(args)))
        print()


if __name__ == '__main__':
    main()
