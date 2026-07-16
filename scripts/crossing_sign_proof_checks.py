#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Proof-step verification for the crossing-sign factorization lemma.

THEOREM.  G^Sp(pi,sg) := sum_i Delta'_pi(i) Delta'_sg(i)
                       = eps(pi) eps(sg) (-1)^k (-2M)^loops(pi,sg),
          eps = (-1)^crossings,  J the standard 2M x 2M symplectic form.

Proof structure, each step checked exhaustively below:
  PS1  Pfaffian sign: sgn(canonical word a1 b1 a2 b2 ...) = (-1)^crossings   k<=5
  PS2  Gauge invariance: sgn(word).prod(J) independent of pair order and
       orientation (orientation flip = adjacent transposition x antisymmetry;
       reorder = even block permutation)                                     k=3, all 48 gauges
  PS3  Loop trace: sum over loop indices of the cyclic J-product
       = tr(J^{2m}) = (-1)^m . 2M   (from J^2 = -I)                          m<=3 brute, m<=6 matrix
  PS5  SIGN LEMMA (walk form, no index sums): D(pi,sg) == cr(pi)+cr(sg)+loops (mod 2),
       D = # traversal-vs-canonical orientation disagreements               k<=4 exhaustive, k=5 sampled
  PS4  Assembly via the gauge-invariant object:
       sum_i Phi_pi Phi_sg == (-1)^(k+loops) (2M)^loops                      (M,k) in {(1,2),(1,3),(2,2)}
  PS6  Consequences now theorem-grade: role-swap sum rules of pinv(G^Sp)
       eps-row sums: eps(pi)/prod(2M-2j) above (M>=k), EXACTLY 0 below (M<k);
       eps-det sums: nonzero 1/prod(2M+j) pattern at all M>=1
"""
from fractions import Fraction as F
from itertools import permutations, product
import random, sys
fails=[]
def check(name, ok):
    print(("PASS  " if ok else "FAIL  ")+name)
    if not ok: fails.append(name)
def comp(s,t): return tuple(s[t[x]] for x in range(len(s)))
def cyc(s):
    n=len(s); seen=[False]*n; c=0
    for x in range(n):
        if not seen[x]:
            c+=1; y=x
            while not seen[y]: seen[y]=True; y=s[y]
    return c
def sgnp(s): return -1 if (len(s)-cyc(s))%2 else 1
def pairings(el):
    if not el:
        yield (); return
    a=el[0]
    for i in range(1,len(el)):
        b=el[i]; rest=el[1:i]+el[i+1:]
        for p in pairings(rest): yield ((a,b),)+p
def to_inv(p,m):
    t=list(range(m))
    for a,b in p: t[a],t[b]=b,a
    return tuple(t)
def pairs_of(inv): return tuple(sorted((a,inv[a]) for a in range(len(inv)) if a<inv[a]))
def crossings(prs):
    c=0
    for x in range(len(prs)):
        for y in range(x+1,len(prs)):
            a,b=prs[x]; cc,d=prs[y]
            if a<cc<b<d or cc<a<d<b: c+=1
    return c
def loops(a,b): return cyc(comp(a,b))//2
def J_entry(x,y,M):
    if y==x+M: return F(1)
    if x==y+M: return F(-1)
    return F(0)

# PS1: Pfaffian sign = crossing parity, exhaustively k<=5
for k in (1,2,3,4,5):
    ok=True
    for p in pairings(tuple(range(2*k))):
        prs=tuple(sorted((min(a,b),max(a,b)) for a,b in p))
        word=tuple(x for pr in prs for x in pr)   # permutation: position -> letter
        ok &= (sgnp(word)==(-1)**crossings(prs))
    check(f"PS1 (k={k}) sgn(canonical word) = (-1)^crossings  [{sum(1 for _ in pairings(tuple(range(2*k))))} pairings]", ok)

# PS2: gauge invariance at k=3 (all 8 orientations x 6 orders = 48 gauges per pairing)
k=3; m2=2*k
P=[to_inv(p,m2) for p in pairings(tuple(range(m2)))]
ok=True
for M,Is in ((1,list(product(range(2),repeat=m2))),(2,None)):
    if Is is None:
        rng=random.Random(7); Is=[tuple(rng.randrange(4) for _ in range(m2)) for _ in range(200)]
    for pi in P:
        base=pairs_of(pi)
        gauges=[]
        for order in permutations(range(k)):
            for ori in product((0,1),repeat=k):
                prs=[(base[t][1],base[t][0]) if ori[t] else base[t] for t in order]
                word=tuple(x for pr in prs for x in pr)
                gauges.append((sgnp(word),prs))
        for i in Is:
            vals=set()
            for sg,prs in gauges:
                v=F(sg)
                for a,b in prs:
                    e=J_entry(i[a],i[b],M)
                    if e==0: v=F(0); break
                    v*=e
                vals.add(v)
            ok &= (len(vals)==1)
check("PS2 gauge invariance of sgn(word).prod(J): all 48 gauges agree (k=3; M=1 all 64 i, M=2 sampled)", ok)

# PS3: loop trace = (-1)^m 2M
ok=True
for M in (1,2,3):
    for m in (1,2,3):
        tot=F(0)
        for x in product(range(2*M),repeat=2*m):
            v=F(1)
            for j in range(2*m):
                e=J_entry(x[j],x[(j+1)%(2*m)],M)
                if e==0: v=F(0); break
                v*=e
            tot+=v
        ok &= (tot==F(-1)**m*2*M)
    # matrix-power confirmation to m=6
    Jm=[[J_entry(x,y,M) for y in range(2*M)] for x in range(2*M)]
    Pw=[row[:] for row in Jm]
    for m in range(1,7):
        if m>1:
            Pw=[[sum(Pw[i][t]*Jm[t][j] for t in range(2*M)) for j in range(2*M)] for i in range(2*M)]
            Pw=[[sum(Pw[i][t]*Jm[t][j] for t in range(2*M)) for j in range(2*M)] for i in range(2*M)] if False else Pw
    # simpler: direct power
    def matmulq(A,B): return [[sum(A[i][t]*B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
    Pw=Jm
    for m in range(1,7):
        P2=matmulq(Pw,Jm) if m>0 else Pw
        # tr(J^(2m)): build incrementally
    Pw=Jm
    for m in range(1,7):
        Pw=matmulq(Pw,Jm)          # J^(2m) after m more... rebuild cleanly:
    Pw=[[F(i==j) for j in range(2*M)] for i in range(2*M)]
    for m in range(1,7):
        Pw=matmulq(matmulq(Pw,Jm),Jm)   # multiply J twice -> J^(2m)
        ok &= (sum(Pw[i][i] for i in range(2*M))==F(-1)**m*2*M)
check("PS3 cyclic loop contraction = tr(J^(2m)) = (-1)^m.2M  (m<=3 brute force, m<=6 matrix powers; M<=3)", ok)

# PS5: the Sign Lemma in walk form, no index sums
def D_of(pi,sg):
    n=len(pi); seen=[False]*n; D=0; ell=0
    for v0 in range(n):
        if seen[v0]: continue
        ell+=1; v=v0
        while True:
            w=pi[v]; seen[v]=True; seen[w]=True
            if v>w: D+=1            # pi-edge traversal (v,w) vs canonical (min,max)
            u=sg[w]
            if w>u: D+=1            # sg-edge traversal (w,u)
            v=u
            if v==v0: break
    return D,ell
for k in (2,3,4):
    m2=2*k
    P=[to_inv(p,m2) for p in pairings(tuple(range(m2)))]
    eps={pi:(-1)**crossings(pairs_of(pi)) for pi in P}
    ok=all(((-1)**D_of(a,b)[0])==eps[a]*eps[b]*((-1)**D_of(a,b)[1]) for a in P for b in P)
    check(f"PS5 (k={k}) Sign Lemma: (-1)^D = eps(pi)eps(sg)(-1)^loops  [{len(P)**2} pairs, exhaustive]", ok)
k=5; m2=10
P5=[to_inv(p,m2) for p in pairings(tuple(range(m2)))]
eps5={pi:(-1)**crossings(pairs_of(pi)) for pi in P5}
rng=random.Random(42); ok=True
for _ in range(50000):
    a=P5[rng.randrange(len(P5))]; b=P5[rng.randrange(len(P5))]
    D,ell=D_of(a,b)
    ok &= ((-1)**D==eps5[a]*eps5[b]*(-1)**ell)
check("PS5 (k=5) Sign Lemma: 50000 random pairs (seeded), sampled", ok)

# PS4: assembly identity via the gauge-invariant object
for (M,k) in [(1,2),(1,3),(2,2)]:
    m2=2*k
    P=[to_inv(p,m2) for p in pairings(tuple(range(m2)))]
    Is=list(product(range(2*M),repeat=m2))
    ok=True
    for a in P:
        for b in P:
            tot=F(0)
            pa=pairs_of(a); pb=pairs_of(b)
            ea=F((-1)**crossings(pa)); eb=F((-1)**crossings(pb))
            for i in Is:
                va=F(1)
                for x,y in pa:
                    e=J_entry(i[x],i[y],M)
                    if e==0: va=F(0); break
                    va*=e
                if va==0: continue
                vb=F(1)
                for x,y in pb:
                    e=J_entry(i[x],i[y],M)
                    if e==0: vb=F(0); break
                    vb*=e
                tot+=ea*va*eb*vb            # Phi_a(i) Phi_b(i)
            ell=loops(a,b)
            ok &= (tot==F(-1)**(k+ell)*(2*M)**ell)
    check(f"PS4 (M={M},k={k}) sum_i Phi.Phi = (-1)^(k+loops).(2M)^loops  [{len(P)**2} pairs]", ok)

# PS6: role-swap sum rules of the certified pseudo-inverse (consequence, now theorem-grade)
def matmul(A,B): return [[sum(A[i][t]*B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def matvec(A,v): return [sum(A[i][t]*v[t] for t in range(len(v))) for i in range(len(A))]
def invmat(Mx):
    n=len(Mx); A=[r[:]+[F(i==j) for j in range(n)] for i,r in enumerate(Mx)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=0); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[x/pv for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                fp=A[r][c]; A[r]=[xr-fp*xc for xr,xc in zip(A[r],A[c])]
    return [r[n:] for r in A]
def pinv_via_kernelfree(G):
    # deflate-by-known-kernel not assumed; small sizes: eigen route via charpoly on basis
    # here: use (G + P_ker)^-1 - P_ker is unavailable generally; use minimal route:
    # G symmetric small => compute via solving on range using rational ops: do full spectral
    # by integer-root scan of the characteristic polynomial of the matrix on Krylov of ALL basis vectors
    n=len(G)
    roots=set()
    I=[[F(i==j) for j in range(n)] for i in range(n)]
    # matrix minimal polynomial via annihilation over candidate integer roots harvested from many seeds
    seeds=[[F(3*i+1,2) for i in range(n)],[F((5*i*i+3*i+7)%9973+1,3) for i in range(n)],
           [F((11*i**3+2*i+13)%7919+1,4) for i in range(n)],[F((17*i+1)*((i%7)+2),5) for i in range(n)]]
    def kroots(u,win=6000):
        K=[u[:]]
        while True:
            K.append(matvec(G,K[-1])); d=len(K)-1
            rows=[[K[j][i] for j in range(d)]+[K[d][i]] for i in range(n)]
            r=0; piv=[]
            for c in range(d):
                pr=next((i for i in range(r,n) if rows[i][c]!=0),None)
                if pr is None: continue
                rows[r],rows[pr]=rows[pr],rows[r]; pv=rows[r][c]
                rows[r]=[x/pv for x in rows[r]]
                for i in range(n):
                    if i!=r and rows[i][c]!=0:
                        fp=rows[i][c]; rows[i]=[xi-fp*xc for xi,xc in zip(rows[i],rows[r])]
                piv.append(c); r+=1
            if all(rows[i][d]==0 for i in range(r,n)):
                sol=[F(0)]*d
                for rr,c in enumerate(piv): sol[c]=rows[rr][d]
                mp=[-s for s in sol]+[F(1)]; break
        co=mp[:]; z=0
        while co[0]==0: co=co[1:]; z+=1
        def ev(x):
            s=F(0)
            for c in reversed(co): s=s*x+c
            return s
        rs=set([0] if z else []); rs.update(r for r in range(-6000,6001) if r!=0 and ev(F(r))==0)
        return rs
    def annih(rs):
        T=I
        for rr in sorted(rs):
            Gm=[[G[i][j]-(F(rr) if i==j else F(0)) for j in range(n)] for i in range(n)]
            T=matmul(T,Gm)
        return all(x==0 for row in T for x in row)
    for s in seeds:
        roots|=kroots(s)
        if annih(roots): break
    assert annih(roots)
    nz=[r for r in roots if r!=0]
    W=[[F(0)]*n for _ in range(n)]
    for lam in nz:
        T=I
        for mu in roots:
            if mu==lam: continue
            Gmu=[[G[i][j]-(F(mu) if i==j else F(0)) for j in range(n)] for i in range(n)]
            T=matmul(T,Gmu); den=F(lam-mu)
            T=[[x/den for x in row] for row in T]
        W=[[W[i][j]+T[i][j]/F(lam) for j in range(n)] for i in range(n)]
    assert matmul(matmul(G,W),G)==G and matmul(matmul(W,G),W)==W
    return W
ok=True
for (M,k) in [(1,2),(1,3),(2,2),(2,3),(3,2)]:
    m2=2*k
    P=[to_inv(p,m2) for p in pairings(tuple(range(m2)))]
    Sk=list(permutations(range(k)))
    def q_of(r): return to_inv(tuple((a,k+r[a]) for a in range(k)),m2)
    Q={q_of(r):r for r in Sk}
    eps=[F((-1)**crossings(pairs_of(pi))) for pi in P]
    G=[[eps[a]*eps[b]*F((-1)**k)*(F(-2*M)**loops(P[a],P[b])) for b in range(len(P))] for a in range(len(P))]
    W=pinv_via_kernelfree(G)
    t1=F(1); t2=F(1)
    for j in range(k): t1*=(2*M-2*j); t2*=(2*M+j)
    for a in range(len(P)):
        row=sum(eps[b]*W[a][b] for b in range(len(P)))
        ok &= (row==(eps[a]/t1 if t1!=0 else F(0)))
        det=sum(F(sgnp(Q[P[b]]))*eps[b]*W[a][b] for b in range(len(P)) if P[b] in Q)
        tgt=(eps[a]*F(sgnp(Q[P[a]])) if P[a] in Q else F(0))/t2
        ok &= (det==tgt)
    tag = "below threshold (M<k): eps-rows = 0" if M<k else f"above: eps-rows = eps/[{t1}]"
    print(f"      (M={M},k={k}) {tag}; eps-det rows = (eps.v)/[{t2}]")
check("PS6 role-swap sum rules of certified pinv(G^Sp): all five (M,k) cells, every row, exact", ok)

print()
print("ALL CROSSING-SIGN PROOF CHECKS PASSED" if not fails else "FAILURES: "+", ".join(fails))
sys.exit(0 if not fails else 1)
