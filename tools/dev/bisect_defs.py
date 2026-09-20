"""Dev helper: find the first top-level block of a .bend file whose addition breaks checking."""
import re, subprocess, sys, os
p = sys.argv[1]
s = open(p).read()
blocks = re.split(r'\n(?=def |# |law |type )', s)
d = os.path.dirname(os.path.abspath(p))
tmp = os.path.join(d, '_bisect_tmp.bend')
def ok(n):
    open(tmp, 'w').write('\n'.join(blocks[:n]) + '\n')
    r = subprocess.run(['bend', tmp], capture_output=True, text=True)
    return 'All terms check' in r.stdout, (r.stdout + r.stderr)[-600:]
lo, hi = 1, len(blocks)
while lo < hi:
    mid = (lo + hi) // 2
    if ok(mid)[0]: lo = mid + 1
    else: hi = mid
good, out = ok(lo)
os.remove(tmp)
print('first failing block index', lo, 'of', len(blocks))
print(blocks[lo - 1][:300])
print(out)
