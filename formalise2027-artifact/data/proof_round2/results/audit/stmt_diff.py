"""Compare theorem/lemma statements between two git revisions of lean_type_sound/LeanTypeSound."""
import re, subprocess, sys
sys.stdout.reconfigure(encoding='utf-8')

repo, base, head = sys.argv[1:4]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)', re.M)


def files(rev):
    out = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, 'lean_type_sound/LeanTypeSound/'],
                         capture_output=True, text=True, encoding='utf-8').stdout.split()
    return [f for f in out if f.endswith('.lean')]


def strip_comments(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', s)


def decls(rev):
    d = {}
    for f in files(rev):
        src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True,
                             encoding='utf-8').stdout
        src = strip_comments(src)
        ns = []
        for m in DECL.finditer(src):
            rest = src[m.end():]
            i = rest.find(':=')
            j = re.search(r'\n\s*\|', rest)  # equation-style definitions
            if j and (i < 0 or j.start() < i):
                i = j.start()
            stmt = ' '.join(rest[:i].split())
            d.setdefault(m.group(2), []).append((f.split('/')[-1], stmt))
    return d


b, h = decls(base), decls(head)
missing = [n for n in b if n not in h]
changed = [n for n in b if n in h and {s for _, s in b[n]} != {s for _, s in h[n]}]
moved = [n for n in b if n in h and n not in changed and {f for f, _ in b[n]} != {f for f, _ in h[n]}]
print(f'base theorems: {len(b)}, head theorems: {len(h)}, new in head: {len([n for n in h if n not in b])}')
print(f'missing in head: {len(missing)}')
for n in missing:
    print('  MISSING', b[n][0][0], n)
print(f'statement changed: {len(changed)}')
for n in changed:
    print('  CHANGED', b[n][0][0], n)
    print('    base:', b[n][0][1][:400])
    print('    head:', h[n][0][1][:400])
print(f'moved to another file (same statement): {len(moved)}')
for n in moved:
    print('  MOVED', n, b[n][0][0], '->', ','.join(f for f, _ in h[n]))
