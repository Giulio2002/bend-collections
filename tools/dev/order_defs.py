"""Dev helper: reorder top-level defs so each def precedes its first user."""
import re, sys
p = sys.argv[1]
s = open(p).read()
blocks = re.split(r'\n(?=def |# )', s)
changed = True
while changed:
    changed = False
    for i, b in enumerate(blocks):
        m = re.match(r'def ([\w.]+)\(', b)
        if not m:
            continue
        n = m.group(1)
        for j in range(i):
            body = blocks[j].split('\n', 1)[1] if '\n' in blocks[j] else ''
            if blocks[j].startswith('def ') and re.search(r'(?<![\w.])' + re.escape(n) + r'\(', body):
                blocks.insert(j, blocks.pop(i)); changed = True; break
        if changed:
            break
open(p, 'w').write('\n'.join(blocks))
