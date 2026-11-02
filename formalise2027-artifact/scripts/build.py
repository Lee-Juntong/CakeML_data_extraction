import os, re, subprocess, sys, time
# usage: build.py LEAN_BIN OUTDIR root:dir [root:dir ...] -- Module1 Module2 ...
lean = sys.argv[1]; out = sys.argv[2]
args = sys.argv[3:]
sep = args.index('--'); roots = [a.split(':',1) for a in args[:sep]]; targets = args[sep+1:]
def find(mod):
    rel = mod.replace('.', '/') + '.lean'
    for prefix, d in roots:
        if mod == prefix or mod.startswith(prefix + '.'):
            p = os.path.join(d, rel)
            if os.path.exists(p): return p, d
    return None
def imports(path):
    src = open(path, encoding='utf-8').read()
    # strip comments roughly
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    res = []
    for line in src.splitlines():
        m = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w\.]+)', line)
        if m: res.append(m.group(1))
    return res
order = []; seen = set()
def visit(mod):
    if mod in seen: return
    seen.add(mod)
    found = find(mod)
    if found is None: return  # core module (Init/Std/Lean)
    p, root = found
    for i in imports(p): visit(i)
    order.append((mod, p, root))
for t in targets: visit(t)
env = dict(os.environ); env['LEAN_PATH'] = out
os.makedirs(out, exist_ok=True)
for mod, p, root in order:
    o = os.path.join(out, mod.replace('.', '/') + '.olean')
    if os.path.exists(o) and os.path.getmtime(o) > os.path.getmtime(p):
        continue
    os.makedirs(os.path.dirname(o), exist_ok=True)
    t = time.time()
    # Lean requires each source file to lie under the package root (-R).
    r = subprocess.run([lean, '-R', root, '-o', o, '-i', o[:-6] + '.ilean', p], env=env, capture_output=True, text=True)
    status = 'OK' if r.returncode == 0 else 'FAIL'
    print(f'{status} {mod} {time.time()-t:.1f}s', flush=True)
    msgs = (r.stdout + r.stderr).strip()
    if msgs:
        lines = [l for l in msgs.splitlines() if 'error' in l.lower()]
        print('\n'.join(lines or msgs.splitlines()[:5])[:4000], flush=True)
    if r.returncode != 0 and '--keep-going' not in os.environ.get('BUILD_FLAGS',''):
        print('STOP'); break
print('DONE', len(order))
