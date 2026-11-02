import subprocess,re,sys
repo=r'E:\NUS\mcomp\Dissertation\CML_Proof\cakeml'
G=['git','-c','safe.directory=*','-C',repo]
KW=r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(inductive|structure|instance|class|abbrev)\b'
TOP=r'^(?:@\[|/-|--|theorem|lemma|def|noncomputable|private|protected|partial|inductive|structure|instance|class|abbrev|mutual|end|namespace|section|open|set_option|attribute|variable|#|import|macro|syntax|example|termination_by|decreasing_by)'
def blocks(ref):
    files=subprocess.run(G+['ls-tree','-r','--name-only',ref,'lean_type_sound/LeanTypeSound/'],capture_output=True,text=True).stdout.split()
    out={}
    for f in files:
        if not f.endswith('.lean'): continue
        t=subprocess.run(G+['show',f'{ref}:{f}'],capture_output=True,text=True,encoding='utf-8').stdout
        t=re.sub(r'/-.*?-/','',t,flags=re.S)
        L=t.splitlines(); i=0
        while i<len(L):
            m=re.match(KW,L[i])
            if m:
                j=i+1
                while j<len(L) and not re.match(TOP,L[j]): j+=1
                body='\n'.join(L[i:j])
                body=re.sub(r'deriving[^\n]*','',body); body=re.sub(r'--[^\n]*','',body)
                key=(m.group(1),re.sub(r'\s+',' ',L[i]).strip()[:120])
                out[key]=re.sub(r'\s+','',body); i=j
            else: i+=1
    return out
for base,heads in [('252eab2cf',['0d1173557','88927cb6f','9f5188d63','aef82615e','41c815090']),('4841f993e',['proof2-skills','proof2-docs','proof2-second-pass','proof2-hybrid','proof2-direct'])]:
    B=blocks(base); print(base,len(B),{k:sum(1 for x in B if x[0]==k) for k in ['inductive','structure','instance','class','abbrev']})
    for h in heads:
        S=blocks(h)
        ch=[k for k in B if k in S and S[k]!=B[k]]; miss=[k for k in B if k not in S]
        print(' ',h,'changed',len(ch),[k[1][:70] for k in ch][:6],'missing',len(miss),[k[1][:60] for k in miss][:6])
