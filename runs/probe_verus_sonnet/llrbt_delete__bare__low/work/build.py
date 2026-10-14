import re
s=open('orig.rs').read()
def rep(tag,f):
    global s
    a=s.index('// <%s>'%tag)+len('// <%s>'%tag); b=s.index('// </%s>'%tag)
    s=s[:a]+'\n'+open(f).read()+'\n    '+s[b:]
rep('helpers','helpers.txt'); rep('proofs','proofs.txt'); rep('code','code.txt')
open('llrbt_delete.rs','w').write(s)
