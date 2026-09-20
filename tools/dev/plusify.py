"""Dev helper: mark Data-typed parameters of *proof* defs (those returning an
equality/Empty/Or proposition) reusable (+). Executable defs are untouched."""
import re, sys
TYPES = sys.argv[2].split(',') if len(sys.argv) > 2 else ['Nat', 'Bool']
p = sys.argv[1]
s = open(p).read()
def fix(m):
    sig = m.group(0)
    ret = sig.rsplit('->', 1)[-1].strip()
    if not (ret.startswith('{') or ret.startswith('Empty') or ret.startswith('Or(') or ret.startswith('L.') or ret.startswith('(')):
        return re.sub(r'(\(|, )\+([a-z_][a-z0-9_]*): ', lambda k: k.group(1) + k.group(2) + ': ', sig)
    return re.sub(r'(\(|, )([a-z_][a-z0-9_]*): (%s)(?=[,)])' % '|'.join(re.escape(t) for t in TYPES),
                  lambda k: k.group(1) + '+' + k.group(2) + ': ' + k.group(3), sig)
s = re.sub(r'^def [^\n]*$', fix, s, flags=re.M)
if '--eq' in sys.argv:
    def fixeq(m):
        sig = m.group(0)
        ret = sig.rsplit('->', 1)[-1].strip()
        if not (ret.startswith('{') or ret.startswith('Empty') or ret.startswith('Or(') or ret.startswith('(')):
            return sig
        return re.sub(r'(\(|, )([a-z_][a-z0-9_]*): \{', lambda k: k.group(1) + '+' + k.group(2) + ': {', sig)
    s = re.sub(r'^def [^\n]*$', fixeq, s, flags=re.M)
open(p, 'w').write(s)
