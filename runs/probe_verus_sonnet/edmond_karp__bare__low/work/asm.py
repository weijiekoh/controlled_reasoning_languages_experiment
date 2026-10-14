t=open('/work/template.rs').read()
def rep(t,a,b,txt):
    i=t.index(a)+len(a); j=t.index(b)
    return t[:i]+"\n"+txt+"\n"+t[j:]
t=rep(t,"// <helpers>","// </helpers>",open('/work/helpers.rs').read())
t=rep(t,"// <proofs>","// </proofs>",open('/work/proofs.rs').read())
t=rep(t,"// <code>","// </code>",open('/work/code.rs').read())
open('/work/edmond_karp.rs','w').write(t)
