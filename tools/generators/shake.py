#!/usr/bin/env python3
"""Pruned copies of the proof libraries a proof tree imports.

  python3 tools/generators/shake.py

The secp256k1 proofs use about fifty lemmas of proofs/lib and proofs/math,
whose files import each other widely (maps, caches, division, words): a root
that imports them checks and keeps some 850 definitions it never uses. This
tool writes, under proofs/crypto/secp256k1/lite/, a copy of every library
file restricted to the definitions (laws with their proofs, defs, types)
the secp256k1 proofs reach, with the imports the kept definitions need. The
text of every kept definition is the library's, unchanged; nothing is
trusted: the copies are checked like any other proof file.

The secp256k1 proof sources import the copies (`./lite/lib/nat.bend` for
`../../lib/nat.bend`). proofs/lib/logic.bend is small and shared with the
SHA-256 and HMAC proofs, so it is imported as it is.

Run it again after changing which library lemmas the proofs use (a missing
lemma is an unknown name for the checker).
"""
import os, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CONS = ROOT / 'proofs/crypto/secp256k1'          # the consumers
LITE = CONS / 'lite'
KEEP = {'proofs/lib/logic.bend'}                 # imported as it is

IDENT = r'[A-Za-z_][A-Za-z0-9_]*'
DOTTED = re.compile(r'(?<![A-Za-z0-9_.])(%s(?:\.%s)*)' % (IDENT, IDENT))


def rel(p):
    return os.path.relpath(p, ROOT)


def is_lib(r):
    return (r.startswith('proofs/lib/') or r.startswith('proofs/math/')) and r not in KEEP


def lite_path(r):
    return LITE / r[len('proofs/'):]


class File:
    def __init__(self, r):
        self.r = r
        text = (ROOT / r).read_text()
        self.imports = {}        # alias -> repo-relative target
        self.import_lines = {}   # alias -> original line
        self.blocks = []         # (name or None, text)
        self.names = {}          # name -> [block indexes]
        cur, pend = None, []
        def flush():
            nonlocal cur, pend
            if cur is not None:
                name, lines = cur
                i = len(self.blocks)
                self.blocks.append((name, '\n'.join(lines).rstrip('\n') + '\n'))
                self.names.setdefault(name, []).append(i)
            cur = None
        for line in text.split('\n'):
            m = re.match(r'(def|law|type)\s+(%s(?:\.%s)*)' % (IDENT, IDENT), line)
            mi = re.match(r'import\s+(\S+)(?:\s+as\s+(\w+))?', line)
            if mi and not line.startswith(' '):
                flush(); pend = []
                tgt = mi.group(1)
                if tgt.endswith('.bend'):
                    t = rel(os.path.normpath(os.path.join(ROOT / os.path.dirname(r), tgt)))
                    self.imports[mi.group(2)] = t
                    self.import_lines[mi.group(2)] = line
                continue
            if m and not line.startswith(' '):
                flush()
                cur = (m.group(2), pend + [line]); pend = []
            elif cur is not None:
                if line.startswith('#') or (line.strip() == '' ):
                    # a comment or blank at column 0 may belong to the next block
                    pend.append(line)
                    continue
                if pend:
                    cur[1].extend(pend); pend = []
                cur[1].append(line)
            else:
                pend.append(line) if line.startswith('#') else None
        flush()


def main():
    files = {}
    def get(r):
        if r not in files:
            files[r] = File(r)
        return files[r]

    need = set()          # (file, name)
    work = []
    def want(r, name):
        f = get(r)
        # the longest dotted prefix that is a definition of the file
        parts = name.split('.')
        for k in range(len(parts), 0, -1):
            n = '.'.join(parts[:k])
            if n in f.names:
                if (r, n) not in need:
                    need.add((r, n)); work.append((r, n))
                return True
        return False

    def scan(text, imports, own):
        """references of a text: alias-qualified ones into library files, and
        (for a library file) its own definitions"""
        for tok in DOTTED.findall(text):
            head = tok.split('.')[0]
            if head in imports and '.' in tok:
                t = imports[head]
                if is_lib(t):
                    want(t, tok[len(head) + 1:])
            elif own is not None:
                want(own, tok)

    # the consumers: every proof file of the tree (not the copies)
    for p in sorted(CONS.glob('*.bend')):
        text = p.read_text()
        imports = {}
        for mi in re.finditer(r'^import\s+(\S+\.bend)\s+as\s+(\w+)', text, re.M):
            t = mi.group(1).replace('./lite/', '../../')
            imports[mi.group(2)] = rel(os.path.normpath(os.path.join(CONS, t)))
        scan(text, imports, None)
    while work:
        r, n = work.pop()
        f = get(r)
        for i in f.names[n]:
            scan(f.blocks[i][1], f.imports, r)

    # write the copies
    if LITE.exists():
        for p in sorted(LITE.rglob('*.bend')):
            p.unlink()
    kept = {}
    for (r, n) in need:
        kept.setdefault(r, set()).add(n)
    total = 0
    for r, names in sorted(kept.items()):
        f = files[r]
        out = lite_path(r)
        out.parent.mkdir(parents=True, exist_ok=True)
        body = [b for (n, b) in f.blocks if n in names]
        text = '\n'.join(body)
        lines = ['# GENERATED by tools/generators/shake.py from %s (the definitions the' % r,
                 '# secp256k1 proofs reach, unchanged); edit the library, then run the tool.', 'import Base']
        for alias, t in f.imports.items():
            if alias is None or not re.search(r'(?<![A-Za-z0-9_.])%s\.' % re.escape(alias), text):
                continue
            if is_lib(t):
                if t not in kept:
                    continue
                tp = lite_path(t)
            else:
                tp = ROOT / t
            rp = os.path.relpath(tp, out.parent)
            if not rp.startswith('.'):
                rp = './' + rp
            lines.append('import %s as %s' % (rp, alias))
        out.write_text('\n'.join(lines) + '\n\n' + text)
        total += len(body)
    print('lite: %d files, %d definitions (of %d files read)' % (len(kept), total, len(files)))


if __name__ == '__main__':
    main()
