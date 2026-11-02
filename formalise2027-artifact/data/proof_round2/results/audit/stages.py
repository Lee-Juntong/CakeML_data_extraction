import sys
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
sys.path.insert(0, r'E:\NUS\mcomp\Dissertation\publication\formalise2027\scripts\transitive_audit')
from count_translation_progress import declarations_at_ref

repo = Path(r'E:\NUS\mcomp\Dissertation\CML_Proof\cakeml')
canon = [d for d in declarations_at_ref(repo, 'de795c9f6')[0] if d.group == 'theorem']
for st, ref in [(1, '38acfb491d'), (2, 'dae9881896'), (3, 'e0384c714c'), (4, '8f73cac87f'), (5, '904068958d')]:
    decls = declarations_at_ref(repo, ref)[0]
    S = {d.key: d for d in decls}
    byname = {}
    for x in decls:
        if x.group == 'theorem':
            byname.setdefault(x.name, []).append(x)
    n = miss = 0
    for d in canon:
        s = S.get(d.key) or (byname.get(d.name, [None])[0] if len(byname.get(d.name, [])) == 1 else None)
        if s is None:
            miss += 1
        elif s.theorem_proved:
            n += 1
    print(f'stage {st} {ref}: local {n} of 269, missing {miss}')
