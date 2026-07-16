#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Proof-step verification for the orthogonal det-absorption lemma.

LEMMA (det-absorption).  For every pairing pi of {0,...,2k-1}:
    sum_{rho in S_k} sgn(rho) N^{loops(pi, q_rho)}  =  N(N-1)...(N-k+1) * v_pi
where q_rho pairs a <-> k+rho(a),  v_pi = sgn(tau) if pi = q_tau else 0.

PROOF (two cases), each step checked exhaustively below:
 A) pi not permutation-like  =>  pi has a top-top pair {a,b} (PL2);
    rho -> rho∘(ab) is a sign-reversing involution preserving loops (PL3);
    terms cancel in pairs, sum = 0 (PL5).
 B) pi = q_tau:  loops(q_tau, q_rho) = c(tau^{-1} rho)   (PL1);
    the sum becomes sgn(tau) * sum_mu sgn(mu) N^{c(mu)}
                  = sgn(tau) * shat(unitary Gram element)
                  = sgn(tau) * N(N-1)...(N-k+1)            (PL4)
    by the SAME Jucys factorization already used in the unitary note.
ONES-ABSORPTION:  r_k = (N+2k-2) r_{k-1}, r_1 = N  =>  prod (N+2j)   (PL6).
POLYNOMIAL IDENTITY: absorption holds at negative arguments too      (PL7),
feeding the symplectic twist arithmetic                               (PL8).
"""
from fractions import Fraction as F
from itertools import permutations
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
def falling(k,N):
    out=F(1)
    for j in range(k): out*=(N-j)
    return out
def rising2(k,N):
    out=F(1)
    for j in range(k): out*=(N+2*j)
    return out

for k in (2,3,4):
    m=2*k
    P=[to_inv(p,m) for p in pairings(tuple(range(m)))]
    Sk=list(permutations(range(k)))
    def q_of(r): return to_inv(tuple((a,k+r[a]) for a in range(k)), m)
    Q={q_of(r):r for r in Sk}

    # PL1: loops(q_tau, q_rho) = c(tau^{-1} rho)
    ok=all(loops(q_of(t),q_of(r))==cyc(comp(invp(t),r)) for t in Sk for r in Sk)
    check(f"PL1 (k={k}) loops(q_tau,q_rho) = c(tau^-1 rho)  [{len(Sk)**2} cases]", ok)

    # PL2: pi is not permutation-like  <=>  pi has a top-top pair; and #TT = #BB
    ok=True
    for pi in P:
        TT=[(a,pi[a]) for a in range(k) if pi[a]<k and pi[a]>a]
        BB=[(a,pi[a]) for a in range(k,m) if pi[a]>=k and pi[a]>a]
        ok &= (len(TT)==len(BB)) and ((pi in Q) == (len(TT)==0))
    check(f"PL2 (k={k}) off-block <=> top-top pair exists; #TT=#BB  [{len(P)} pairings]", ok)

    # PL3: the involution rho -> rho∘(ab) preserves loops for every off-block pi
    ok=True; cnt=0
    for pi in P:
        if pi in Q: continue
        a=next(x for x in range(k) if pi[x]<k and pi[x]!=x); b=pi[a]
        for r in Sk:
            r2=list(r); r2[a],r2[b]=r[b],r[a]; r2=tuple(r2)
            ok &= loops(pi,q_of(r))==loops(pi,q_of(r2)); cnt+=1
    check(f"PL3 (k={k}) sign-reversing involution preserves loops  [{cnt} cases]", ok)

    # PL4/PL5: block sums, several N incl. negative
    for N in (F(3),F(7),F(-1),F(-3)):
        ok4=all(sum(F(sgnp(r))*N**loops(q_of(t),q_of(r)) for r in Sk)==F(sgnp(t))*falling(k,N) for t in Sk)
        ok5=all(sum(F(sgnp(r))*N**loops(pi,q_of(r)) for r in Sk)==0 for pi in P if pi not in Q)
        check(f"PL4 (k={k},N={N}) on-block sum = sgn(tau)*falling", ok4)
        check(f"PL5 (k={k},N={N}) off-block sum = 0", ok5)

# PL6: ones-absorption recursion and closed form, k<=5
prev={}
for N in (F(3),F(5),F(7)):
    prev[N]=None
for k in (1,2,3,4,5):
    m=2*k
    P=[to_inv(p,m) for p in pairings(tuple(range(m)))]
    beta=P[0]
    ok=True
    for N in (F(3),F(5),F(7)):
        rk=sum(N**loops(beta,s) for s in P)
        ok &= rk==rising2(k,N)
        if prev[N] is not None: ok &= rk==(N+2*k-2)*prev[N]
        prev[N]=rk
    check(f"PL6 (k={k}) row sum = prod(N+2j) and r_k=(N+2k-2)r_(k-1)  [{len(P)} pairings]", ok)

# PL7: full det-absorption at negative arguments (polynomial identity)
for k in (2,3,4):
    m=2*k
    P=[to_inv(p,m) for p in pairings(tuple(range(m)))]
    Sk=list(permutations(range(k)))
    def q_of(r): return to_inv(tuple((a,k+r[a]) for a in range(k)), m)
    Q={q_of(r):r for r in Sk}
    v=[F(sgnp(Q[pi])) if pi in Q else F(0) for pi in P]
    ok=True
    for N in (F(-1),F(-2),F(-4)):
        Gv=[sum((N**loops(P[i],P[j]))*v[j] for j in range(len(P))) for i in range(len(P))]
        ok &= all(Gv[i]==falling(k,N)*v[i] for i in range(len(P)))
    check(f"PL7 (k={k}) absorption G.v = falling(N).v at N = -1,-2,-4", ok)

# PL8: symplectic twist arithmetic (role swap under N -> -2M)
ok=True
for k in (2,3,4):
    for M in range(1,6):
        ok &= rising2(k,F(-2*M))==F(-2)**k*falling(k,F(M))
        ok &= falling(k,F(-2*M))==F(-1)**k*F(1)*__import__('math').prod(range(2*M,2*M+k))
check("PL8 even-rising(-2M) = (-2)^k * falling(M);  falling(-2M) = ±(2M)(2M+1)...(2M+k-1)", ok)

print()
print("ALL PROOF-STEP CHECKS PASSED" if not fails else "FAILURES: "+", ".join(fails))
sys.exit(0 if not fails else 1)
