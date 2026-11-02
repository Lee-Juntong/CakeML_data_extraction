"""List definitions (def/inductive/structure/abbrev/class/instance/opaque/axiom) whose text changed between two revisions."""
import re, subprocess, sys
sys.stdout.reconfigure(encoding='utf-8')

repo, base, head = sys.argv[1:4]
TOP = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+|mutual\b|end\b|theorem\b|lemma\b|def\b|inductive\b|structure\b|abbrev\b|class\b|instance\b|opaque\b|axiom\b|namespace\b|section\b|open\b|variable\b|set_option\b|attribute\b|#|termination_by\b|decreasing_by\b)', re.M)
DEF = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*)(def|inductive|structure|abbrev|class|instance|opaque|axiom)\s+(\S+)', re.M)


def strip_comments(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', s)


def defs(rev):
    out = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, 'lean_type_sound/LeanTypeSound/'],
                         capture_output=True, text=True, encoding='utf-8').stdout.split()
    d = {}
    for f in [x for x in out if x.endswith('.lean')]:
        src = strip_comments(subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True,
                                            text=True, encoding='utf-8').stdout)
        starts = [m.start() for m in TOP.finditer(src)] + [len(src)]
        for m in DEF.finditer(src):
            nxt = min(s for s in starts if s > m.start())
            body = src[m.start():nxt]
            # Keep the termination clause with the definition.
            k = nxt
            while k < len(src) and re.match(r'(termination_by|decreasing_by)', src[k:k + 14]):
                k2 = min(s for s in starts if s > k)
                body += src[k:k2]
                k = k2
            d.setdefault((m.group(2), m.group(3)), []).append((f.split('/')[-1], m.group(1).strip(), ' '.join(body.split())))
    return d


b, h = defs(base), defs(head)
print('base defs:', len(b), 'head defs:', len(h))
for k in b:
    if k not in h:
        print('MISSING', k, b[k][0][0])
for k in h:
    if k not in b:
        print('NEW', k, h[k][0][0], h[k][0][1])
for k in b:
    if k in h and [x[2] for x in b[k]] != [x[2] for x in h[k]]:
        print('CHANGED', k, b[k][0][0], '->', h[k][0][0], '| modifiers', b[k][0][1] or '-', '->', h[k][0][1] or '-')
