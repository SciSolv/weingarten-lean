#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Brauer/orthogonal exploration: does the two-line Penrose trick transfer to O(N)?

Setup: pairings P2(2k) index the orthogonal Gram matrix G(pi,sg) = N^loops(pi,sg),
loops = cycles(pi*sg)/2 for pairings-as-fixed-point-free-involutions.  Wg^O = MP
pseudo-inverse (standard convention).  Tests, exact rationals throughout:

  BO1  ones-absorption:   G.1 = r(N).1   with r(N) = N(N+2)...(N+2k-2)        k<=4
  BO1n negative control:  naive Pfaffian-sign vector is NOT absorbing (k=2)
  BO2  det-absorption:    G.v = f(N).v   with f(N) = N(N-1)...(N-k+1)         k<=4
       where v = sum_rho sgn(rho) e_{q_rho},  q_rho pairs a <-> k+rho(a)
  BO3  above threshold (exact inverse): row sums = 1/r(N);
       signed sum  sum_rho sgn(rho) Wg(p0, q_rho) = 1/f(N)                    k<=3
  BO4  below threshold (exact MP via minimal polynomial + Lagrange):
       Penrose certified; row sums = 1/r(N) persist; SIGNED SUM = 0 EXACTLY;
       v is an explicit kernel vector of G                                    k<=3
"""
from fractions import Fraction as F
from itertools import permutations
import sys
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

def matvec(M,v): return [sum(M[i][j]*v[j] for j in range(len(v))) for i in range(len(M))]
def matmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def invmat(M):
    n=len(M); A=[r[:]+[F(i==j) for j in range(n)] for i,r in enumerate(M)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=0); A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[x/pv for x in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                fpiv=A[r][c]; A[r]=[xr-fpiv*xc for xr,xc in zip(A[r],A[c])]
    return [r[n:] for r in A]

def rising(k,N):
    out=F(1)
    for j in range(k): out*= (N+2*j)
    return out
def falling(k,N):
    out=F(1)
    for j in range(k): out*= (N-j)
    return out

def setup(k):
    m=2*k
    P=[to_inv(p,m) for p in pairings(tuple(range(m)))]
    idx={p:i for i,p in enumerate(P)}
    Sk=list(permutations(range(k)))
    def q_of(rho):
        pr=tuple((a,k+rho[a]) for a in range(k))
        return to_inv(pr,m)
    v=[F(0)]*len(P)
    for rho in Sk: v[idx[q_of(rho)]]+=F(sgnp(rho))
    p0=idx[q_of(tuple(range(k)))]
    return P,idx,v,p0,Sk,q_of
def gram(P,N): return [[N**(cyc(comp(a,b))//2) for b in P] for a in P]

Ngrid=[F(3),F(5),F(7),F(9),F(11)]

for k in (2,3,4):
    P,idx,v,p0,Sk,q_of=setup(k)
    okR=okF=True
    for N in Ngrid[:k+1]:
        G=gram(P,N)
        u=matvec(G,[F(1)]*len(P))
        okR &= all(x==rising(k,N) for x in u)
        w=matvec(G,v)
        okF &= all(w[i]==falling(k,N)*v[i] for i in range(len(P)))
    check(f"BO1 ones-absorption G.1 = (N(N+2)...(N+2k-2)).1, k={k} ({len(P)} pairings)", okR)
    check(f"BO2 det-absorption  G.v = (N(N-1)...(N-k+1)).v,  k={k}", okF)

# BO1n: negative control, k=2 Pfaffian signs (+1,-1,+1) are NOT absorbing
P,idx,v,p0,Sk,q_of=setup(2)
pf=[F(1),F(-1),F(1)]
G=gram(P,F(5))
w=matvec(G,pf)
notprop = not all(w[i]*pf[0]==w[0]*pf[i] for i in range(3))
check("BO1n negative control: naive Pfaffian-sign vector fails absorption (k=2)", notprop)

# BO3: above threshold, exact inverse
for k in (2,3):
    P,idx,v,p0,Sk,q_of=setup(k)
    ok=True
    for N in (F(k)+1, F(k)+3):
        G=gram(P,N); W=invmat(G)
        ok &= all(sum(W[i])==1/rising(k,N) for i in range(len(P)))
        signed=sum(F(sgnp(r))*W[p0][idx[q_of(r)]] for r in Sk)
        ok &= signed==1/falling(k,N)
    check(f"BO3 above threshold: row sums 1/rising; signed det-sum = 1/falling, k={k}", ok)

# BO4: below threshold, exact MP pseudo-inverse via minimal polynomial
def minpoly(G):
    n=len(G); u=[F(3*i+1,2) for i in range(n)]
    K=[u[:]]
    while True:
        K.append(matvec(G,K[-1]))
        d=len(K)-1
        A=[[K[j][i] for j in range(d)] for i in range(n)]  # solve A c = K[d]
        AA=[row[:]+[K[d][i]] for i,row in enumerate(A)]
        # gaussian elim least-effort: try to solve; if consistent -> dependence
        rows=AA; piv=[]; r=0
        for c in range(d):
            pr=next((i for i in range(r,n) if rows[i][c]!=0),None)
            if pr is None: continue
            rows[r],rows[pr]=rows[pr],rows[r]
            pv=rows[r][c]; rows[r]=[x/pv for x in rows[r]]
            for i in range(n):
                if i!=r and rows[i][c]!=0:
                    fpiv=rows[i][c]; rows[i]=[xi-fpiv*xc for xi,xc in zip(rows[i],rows[r])]
            piv.append(c); r+=1
        consistent = all(rows[i][d]==0 for i in range(r,n))
        if consistent:
            sol=[F(0)]*d
            for rr,c in enumerate(piv): sol[c]=rows[rr][d]
            # monic minimal polynomial: x^d - sum sol_j x^j
            return [-s for s in sol]+[F(1)]
def polyroots_int(coeffs, lo=-700, hi=700):
    # strip zero roots
    z=0
    while coeffs[0]==0: coeffs=coeffs[1:]; z+=1
    roots=[0]*z if z else []
    def ev(x):
        s=F(0)
        for c in reversed(coeffs): s=s*x+c
        return s
    found=[r for r in range(lo,hi+1) if r!=0 and ev(F(r))==0]
    return roots+found
for k,Nints in ((2,[1]),(3,[1,2])):
    P,idx,v,p0,Sk,q_of=setup(k)
    for N in Nints:
        N=F(N); G=gram(P,N)
        mp=minpoly(G); roots=polyroots_int(mp[:])
        assert len(roots)==len(mp)-1, "minpoly not split/simple as expected"
        nz=[r for r in roots if r!=0]
        # Lagrange p with p(0)=0, p(lam)=1/lam
        n=len(P); W=[[F(0)]*n for _ in range(n)]
        I=[[F(i==j) for j in range(n)] for i in range(n)]
        for lam in nz:
            # term: (1/lam) * prod_{mu != lam, mu in roots\{lam}} (G - mu I)/(lam - mu)
            T=I
            for mu in roots:
                if mu==lam: continue
                T=matmul(T,[[ (G[i][j]-(F(mu) if i==j else 0)) if True else 0 for j in range(n)] for i in range(n)])
                # fix: subtract mu only on diagonal
            # rebuild properly:
            T=I
            for mu in roots:
                if mu==lam: continue
                Gmu=[[G[i][j]-(F(mu) if i==j else F(0)) for j in range(n)] for i in range(n)]
                T=matmul(T,Gmu)
                den=F(lam-mu)
                T=[[x/den for x in row] for row in T]
            W=[[W[i][j]+T[i][j]/F(lam) for j in range(n)] for i in range(n)]
        ok = matmul(matmul(G,W),G)==G and matmul(matmul(W,G),W)==W
        ok &= all(sum(W[i])==1/rising(k,N) for i in range(n))
        signed=sum(F(sgnp(r))*W[p0][idx[q_of(r)]] for r in Sk)
        ok &= signed==0
        ok &= all(x==0 for x in matvec(G,v))
        check(f"BO4 below threshold (k={k}, N={N}): MP certified; rows 1/rising; SIGNED SUM = 0; v in ker G", ok)

print()
print("ALL BRAUER/ORTHOGONAL CHECKS PASSED" if not fails else "FAILURES: "+", ".join(fails))
sys.exit(0 if not fails else 1)
