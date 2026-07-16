#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Clean-room adjudication of the reviewing session's claims.

Built from first principles in THIS container:
  A1  Symplectic Gram via brute-force J-contractions equals the claimed
      factorization  G^Sp(m,n) = eps(m)eps(n)(-1)^k(-2M)^loops(m,n),
      eps = (-1)^crossings, at (M,k) in {(1,2),(1,3),(2,2),(2,3),(1,4)}
  A2  The quoted falsifier matrix [[4,2,-2],[2,4,2],[-2,2,4]] at (M,k)=(1,2)
  A3  Twisted absorptions: G^Sp.(eps) = prod(2M-2j).(eps)  and
      G^Sp.(eps*v_det) = prod(2M+j).(eps*v_det)
  A4  Entrywise twist:  pinv(G^Sp) = (-1)^k diag(eps) pinv(G^O(-2M)) diag(eps)
  A5  GROUND TRUTH: all 256 (k=2) and all 4096 (k=3) Haar-Sp(2)=SU(2) moments
      by direct exact integration  ==  Weingarten formula with pinv(G^Sp)
  A6  Condition-number identity (unitary, above threshold):
      sum Wg / sum|Wg| = C(N,n)/C(N+n-1,n) = falling/rising,
      with the CMN strict sign pattern re-checked at each cell
  A7  Gram spectral extremes = (rising, falling)-type pairs: U(3,5), O(k=3,N=5),
      Sp(M=3,k=2)
  A8  Orthogonal fixed-N sign pattern  sign Wg^O(rho;N) = (-1)^(k-len(rho)),
      k<=3, N = k+1..k+7   [empirical support for their k<=4 claim]
"""
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial, comb
import sys
fails=[]
def check(name, ok):
    print(("PASS  " if ok else "FAIL  ")+name)
    if not ok: fails.append(name)

def comp(s,t): return tuple(s[t[x]] for x in range(len(s)))
def invp(s):
    t=[0]*len(s)
    for x,y in enumerate(s): t[y]=x
    return tuple(t)
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
def loops(a,b): return cyc(comp(a,b))//2
def pairs_of(inv):
    return tuple(sorted((a,inv[a]) for a in range(len(inv)) if a<inv[a]))
def crossings(prs):
    c=0
    for x in range(len(prs)):
        for y in range(x+1,len(prs)):
            a,b=prs[x]; cc,d=prs[y]
            if a<cc<b<d or cc<a<d<b: c+=1
    return c
def rising2(k,z):
    out=F(1)
    for j in range(k): out*=(z+2*j)
    return out
def falling(k,z):
    out=F(1)
    for j in range(k): out*=(z-j)
    return out
# exact MP pseudo-inverse of a symmetric rational matrix with integer spectrum
def matmul(A,B): return [[sum(A[i][t]*B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def matvec(A,v): return [sum(A[i][t]*v[t] for t in range(len(v))) for i in range(len(A))]
def _krylov_roots(G,u,win):
    n=len(G); K=[u[:]]
    while True:
        K.append(matvec(G,K[-1]))
        d=len(K)-1
        rows=[[K[j][i] for j in range(d)]+[K[d][i]] for i in range(n)]
        r=0; piv=[]
        for c in range(d):
            pr=next((i for i in range(r,n) if rows[i][c]!=0),None)
            if pr is None: continue
            rows[r],rows[pr]=rows[pr],rows[r]
            pv=rows[r][c]; rows[r]=[x/pv for x in rows[r]]
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
    rs=set([0] if z else [])
    rs.update(r for r in range(-win,win+1) if r!=0 and ev(F(r))==0)
    return rs

def pinv_minpoly(G, win=6000):
    # Robust exact MP pseudo-inverse: multi-seed Krylov for the spectrum,
    # matrix-annihilation completeness test, mandatory Penrose certificate.
    # (Single structured seeds can miss isotypic components -- a lex-ordered
    #  arithmetic probe over S_4 has zero sign-component, found 2026-06-12.)
    n=len(G); roots=set()
    seeds=[[F(3*i+1,2) for i in range(n)],
           [F((5*i*i+3*i+7)%9973+1,3) for i in range(n)],
           [F((11*i*i*i+2*i+13)%7919+1,4) for i in range(n)],
           [F((17*i+1)*( (i%7)+2 ),5) for i in range(n)]]
    I=[[F(i==j) for j in range(n)] for i in range(n)]
    def annihilates(rset):
        T=I
        for rr in sorted(rset):
            Gm=[[G[i][j]-(F(rr) if i==j else F(0)) for j in range(n)] for i in range(n)]
            T=matmul(T,Gm)
        return all(x==0 for row in T for x in row)
    for s in seeds:
        roots|=_krylov_roots(G,s,win)
        if annihilates(roots): break
    assert annihilates(roots), "spectrum incomplete after multi-seed Krylov"
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
    assert matmul(matmul(G,W),G)==G and matmul(matmul(W,G),W)==W, "Penrose certificate failed"
    return W, sorted(roots)

def setup(k):
    m=2*k
    P=[to_inv(p,m) for p in pairings(tuple(range(m)))]
    Sk=list(permutations(range(k)))
    def q_of(r): return to_inv(tuple((a,k+r[a]) for a in range(k)), m)
    Q={q_of(r):r for r in Sk}
    eps=[F((-1)**crossings(pairs_of(pi))) for pi in P]
    v=[F(sgnp(Q[pi])) if pi in Q else F(0) for pi in P]
    return P,Sk,q_of,Q,eps,v

def J_entry(x,y,M):
    if y==x+M: return F(1)
    if x==y+M: return F(-1)
    return F(0)
def gram_sp(P,M,k):
    dim=2*M; I=list(product(range(dim),repeat=2*k))
    D=[]
    for pi in P:
        prs=pairs_of(pi)
        D.append([prodJ(prs,i,M) for i in I])
    n=len(P)
    G=[[sum(D[a][t]*D[b][t] for t in range(len(I))) for b in range(n)] for a in range(n)]
    return G, D, I
def prodJ(prs,i,M):
    out=F(1)
    for a,b in prs:
        e=J_entry(i[a],i[b],M)
        if e==0: return F(0)
        out*=e
    return out

# ---------- A1 / A2 / A3 ----------
for (M,k) in [(1,2),(1,3),(2,2),(2,3),(1,4)]:
    P,Sk,q_of,Q,eps,v=setup(k)
    G,D,I=gram_sp(P,M,k)
    ok=all(G[a][b]==eps[a]*eps[b]*F((-1)**k)*(F(-2*M)**loops(P[a],P[b])) for a in range(len(P)) for b in range(len(P)))
    check(f"A1 (M={M},k={k}) G^Sp from J-contractions == eps.eps.(-1)^k.(-2M)^loops  [{len(P)}x{len(P)}]", ok)
    if (M,k)==(1,2):
        check("A2 quoted falsifier matrix [[4,2,-2],[2,4,2],[-2,2,4]] reproduced", G==[[F(4),F(2),F(-2)],[F(2),F(4),F(2)],[F(-2),F(2),F(4)]])
    e1=matvec(G,eps); tw=[eps[i]*v[i] for i in range(len(P))]; e2=matvec(G,tw)
    r1=rising2(k,F(2*M))-0  # prod(2M+2j)? careful: claim is prod(2M-2j)
    t1=F(1)
    for j in range(k): t1*=(2*M-2*j)
    t2=F(1)
    for j in range(k): t2*=(2*M+j)
    ok3=all(e1[i]==t1*eps[i] for i in range(len(P))) and all(e2[i]==t2*tw[i] for i in range(len(P)))
    check(f"A3 (M={M},k={k}) twisted absorptions: eps-ones -> prod(2M-2j)={t1}; eps-det -> prod(2M+j)={t2}", ok3)

# ---------- A4 / A5 (M=1) ----------
for k in (2,3):
    M=1
    P,Sk,q_of,Q,eps,v=setup(k)
    G,D,I=gram_sp(P,M,k)
    W,roots=pinv_minpoly(G)
    Gneg=[[F(-2*M)**loops(a,b) for b in P] for a in P]
    Wneg,_=pinv_minpoly(Gneg)
    ok4=all(W[a][b]==F((-1)**k)*eps[a]*eps[b]*Wneg[a][b] for a in range(len(P)) for b in range(len(P)))
    check(f"A4 (M=1,k={k}) pinv(G^Sp) == (-1)^k diag(eps) pinv(G^O(-2)) diag(eps)   spectrum={roots}", ok4)
    # SU(2) ground truth: U=[[a,b],[-conj b, conj a]]
    ent={(0,0):(1,(1,0,0,0)),(0,1):(1,(0,0,1,0)),(1,0):(-1,(0,0,0,1)),(1,1):(1,(0,1,0,0))}
    def moment(ii,jj):
        s=1; c=[0,0,0,0]
        for t in range(2*k):
            sg,mono=ent[(ii[t],jj[t])]
            s*=sg
            for x in range(4): c[x]+=mono[x]
        if c[0]!=c[1] or c[2]!=c[3]: return F(0)
        return F(s)*F(factorial(c[0])*factorial(c[2]), factorial(c[0]+c[2]+1))
    # Weingarten side: R = A^T W A with A[m][t]=Delta'_m(I[t])
    T=[[sum(W[a][b]*D[b][t] for b in range(len(P))) for t in range(len(I))] for a in range(len(P))]
    good=0; tot=0
    for ti,ii in enumerate(I):
        for tj,jj in enumerate(I):
            rhs=sum(D[a][ti]*T[a][tj] for a in range(len(P)))
            tot+=1
            if rhs==moment(ii,jj): good+=1
    check(f"A5 (Sp(2)=SU(2), k={k}) direct exact Haar moments vs Weingarten/pinv: {good}/{tot} match", good==tot)

# ---------- A6 ----------
def gram_u(n,N):
    Sn=list(permutations(range(n)))
    return Sn, [[F(N)**cyc(comp(invp(a),b)) for b in Sn] for a in Sn]
ok6=True
for (n,N) in [(2,2),(2,3),(3,3),(3,4),(4,4),(4,6)]:
    Sn,G=gram_u(n,N)
    Winv,_=pinv_minpoly(G)
    i0=Sn.index(tuple(range(n)))
    sW=sum(Winv[i0][j] for j in range(len(Sn)))
    aW=sum(abs(Winv[i0][j]) for j in range(len(Sn)))
    pat=all((Winv[i0][j]>0)==(sgnp(Sn[j])>0) and Winv[i0][j]!=0 for j in range(len(Sn)))
    ok6 &= pat and (sW/aW == F(comb(N,n),comb(N+n-1,n))) and (sW/aW == falling(n,F(N))/ (F(1)*__import__('functools').reduce(lambda x,y:x*y,[F(N+j) for j in range(n)],F(1))))
check("A6 avg sign = C(N,n)/C(N+n-1,n) = falling/rising, with strict CMN sign pattern, 6 cells", ok6)

# ---------- A7 ----------
Sn,Gu=gram_u(3,5); _,ru=pinv_minpoly(Gu)
P3,_,_,_,_,_=setup(3)
Go=[[F(5)**loops(a,b) for b in P3] for a in P3]; _,ro=pinv_minpoly(Go)
P2s,_,_,_,eps2,_=setup(2)
Gs,_,_=gram_sp(P2s,3,2); _,rs=pinv_minpoly(Gs)
ok7=(max(ru)==210 and min(r for r in ru if r!=0)==60 and 60==falling(3,F(5)) and
     max(ro)==315 and min(r for r in ro if r!=0)==60 and 315==rising2(3,F(5)) and
     max(rs)==42 and min(r for r in rs if r!=0)==24)
print(f"      spectra: U(3,5)={ru}  O(k=3,N=5)={ro}  Sp(M=3,k=2)={rs}")
check("A7 spectral extremes = (rising, falling) pairs incl. Sp {24,42}=(prod(2M-2j),prod(2M+j))", ok7)

# ---------- A8 ----------
ok8=True
for k in (2,3):
    P,Sk,q_of,Q,eps,v=setup(k)
    p0=P.index(q_of(tuple(range(k))))
    for N in range(k+1,k+8):
        Go=[[F(N)**loops(a,b) for b in P] for a in P]
        Wo,_=pinv_minpoly(Go)
        for b in range(len(P)):
            ell=loops(P[p0],P[b])  # number of loops = parts of coset type
            want=(-1)**(k-ell)
            ok8 &= (Wo[p0][b]!=0) and ((Wo[p0][b]>0)==(want>0))
check("A8 orthogonal fixed-N sign pattern sign Wg^O = (-1)^(k-#loops), k<=3, N=k+1..k+7", ok8)

print()
print("ALL ADJUDICATION CHECKS PASSED" if not fails else "FAILURES: "+", ".join(fails))
sys.exit(0 if not fails else 1)
