"""Table IX, the round 2 version of Table VII: Local, Mod., Aud., Unch. on the canonical theorems of de795c9f6.

Local: the theorem declaration has no sorry/admit (scripts/counter.py of the artifact).
Aud.:  Lean.collectAxioms has no sorryAx and only the three standard axioms.
Mod.:  local, and every sorry root in the closure is a definition (or a termination/instance obligation)
       that is admitted in the baseline de795c9f6; no admitted theorem is reached.
Unch.: Mod. with unchanged statement text (whitespace-insensitive).
"""
import sys, os, re, json, collections
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
# Usage: python table_r2.py [CAKEML] [AUDIT_DIR] [EXTRA_REF]
#   CAKEML: a clone of https://github.com/Lee-Juntong/cakeml with the lean-translate* branches
#           (default: the CAKEML environment variable, else ./cakeml)
#   AUDIT_DIR: the folder holding <workflow>/axioms.tsv (default: this script's folder)
ARTIFACT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ARTIFACT / 'scripts'))
from counter import declarations_at_ref

repo = Path(sys.argv[1] if len(sys.argv) > 1 else os.environ.get('CAKEML', 'cakeml'))
audit = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).resolve().parent
BASE = 'de795c9f6'
base, _ = declarations_at_ref(repo, BASE)
canon = [d for d in base if d.group == 'theorem']
B = {d.key: d for d in base}
print('canonical theorems at', BASE, len(canon))


def load_tsv(path):
    rows = []
    for line in open(path, encoding='utf-8'):
        p = line.rstrip('\n').split('\t')
        while len(p) < 4:
            p.append('')
        rows.append(dict(module=p[0], name=p[1], axioms=[a for a in p[2].split(',') if a],
                         roots=[r for r in p[3].split(';') if r]))
    return rows


def resolve(rows, d):
    mod = 'LeanTypeSound.' + d.file[:-5]
    return [r for r in rows if r['module'] == mod and (r['name'] == d.name or r['name'].endswith('.' + d.name))]


# Attributes such as @[simp] are neither statement nor body edits, as in scripts/analysis.py.
ATTR = re.compile(r"^@\[[^\]\n]*\]\s*")


def norm_stmt(d):
    return re.sub(r'\s+', '', ATTR.sub('', d.content).split(':=', 1)[0])


def norm_body(d):
    t = re.split(r'\b(termination_by|decreasing_by)\b', ATTR.sub('', d.content))[0]
    return re.sub(r'\s+', '', re.sub(r'\bsorry\b', '', t))


# Constants that mention sorryAx directly in the baseline would need a baseline audit; instead, an admitted
# theorem root is any root of kind thm that is not an auxiliary proof term.
def is_aux(n):
    return any(p.startswith('_') or re.fullmatch(r'proof_\d+', p) for p in n.split('.'))


# Branches of the GitHub fork; ../proof_round2.bundle has the same heads under the names proof2-*.
runs = {'Skills': ('skills', 'lean-translate-Lean-Skills-Official'),
        'Docs': ('docs', 'lean-translate-lean4skills(prove)-docAccess'),
        'Second pass': ('second-pass', 'lean-translate-skills(prove)-docAccess-2pass'),
        'Hybrid': ('hybrid', 'lean-translate-CC-aristotle'),
        'Direct': ('direct', 'lean-translate-direct-aristotle')}
if len(sys.argv) > 3:
    runs['Direct (stage 2)'] = ('direct', sys.argv[3])
table = {}
sets = collections.defaultdict(set)
for label, (folder, ref) in runs.items():
    tsv = audit / folder / 'axioms.tsv'
    if not tsv.exists():
        print(label, 'no axioms.tsv'); continue
    rows = load_tsv(tsv)
    decls, _ = declarations_at_ref(repo, ref)
    S = {d.key: d for d in decls}
    c = collections.Counter()
    notes = []
    for d in canon:
        s = S.get(d.key)
        if s is None:
            alt = [x for x in decls if x.group == 'theorem' and x.name == d.name]
            if len(alt) == 1:
                s = alt[0]; c['moved'] += 1
            else:
                c['Miss.'] += 1; continue
        same = norm_stmt(s) == norm_stmt(d)
        if not same:
            c['S.ed.'] += 1
        if not s.theorem_proved:
            continue
        c['Local'] += 1; sets[label, 'Local'].add(d.key)
        r = resolve(rows, s)
        if len(r) != 1:
            notes.append(('unresolved', d.name, len(r))); continue
        r = r[0]
        nonstd = [a for a in r['axioms'] if a not in ('propext', 'Classical.choice', 'Quot.sound', 'sorryAx')]
        if nonstd:
            notes.append(('nonstandard axioms', d.name, nonstd))
        if 'sorryAx' not in r['axioms'] and not nonstd:
            c['Aud.'] += 1; sets[label, 'Aud.'].add(d.key)
            mod = True
        else:
            thm_roots = [x.split(':', 1)[1] for x in r['roots']
                         if x.startswith('thm:') and x.split(':', 1)[1] != r['name'] and not is_aux(x.split(':', 1)[1])]
            mod = not thm_roots and not nonstd
            if not mod:
                notes.append(('via admitted theorem', d.name, thm_roots[:3]))
        if mod:
            c['Mod.'] += 1; sets[label, 'Mod.'].add(d.key)
            if same:
                c['Unch.'] += 1
    for k, s in S.items():
        if k in B and B[k].group == 'definition' and norm_body(s) != norm_body(B[k]):
            c['D.ed.'] += 1
    names = {d.name for d in canon}
    c['Help.'] = sum(1 for k, s in S.items() if s.group == 'theorem' and s.name not in names)
    table[label] = dict(c)
    print(f"{label:16s}", ' '.join(f"{k}={c.get(k, 0)}" for k in ['Local', 'Mod.', 'Aud.', 'Unch.', 'S.ed.', 'D.ed.', 'Help.', 'Miss.', 'moved']))
    for n in notes[:12]:
        print('    ', n)
    if len(notes) > 12:
        print('     ...', len(notes) - 12, 'more notes')
main = [l for l in runs if not l.startswith('Direct (')]
for m in ['Local', 'Mod.', 'Aud.']:
    print('Any', m, len(set().union(*[sets[l, m] for l in main])))
json.dump(table, open(audit / 'table_r2.json', 'w'), indent=1)
