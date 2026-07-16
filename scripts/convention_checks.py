#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Executable convention checks for the weingarten-lean blueprint.

Exact arithmetic only (fractions.Fraction); stdlib only; exit 0 iff all pass.

These pin every convention decision shared by the blueprint and the Lean skeleton:

  C1  the model of Equiv.Perm.decomposeFin.symm is a bijection
      Fin (n+1) x Perm (Fin n) -> Perm (Fin (n+1)),                    n+1 <= 6
  C2  splice rule: cycleCount (symm (p,e)) = cycleCount e + [p = 0],   n+1 <= 6 (exhaustive)
  C3  dual Jucys identity  sum_s N^c(s) s = (N+K_0)(N+K_1)...(N+K_{n-1}),  n <= 5, three N
  C4  character images: eps(K_i) = n-1-i  and  sgn-hom(K_i) = -(n-1-i),    n <= 6
  C5  shortest slot-word recursion (witness for lem:exists_monotone),      n <= 5, all sigma
  C6  Cell23: four Penrose identities, symmetry, row sums 1/24, signed row sums 0
  B1  alternating-element absorption  alt * x = sgnHom(x) * alt,           n <= 4
  B2  aug(G) = rising factorial, sgnHom(G) = falling factorial, all N,     n <= 5
  B3  kernel witness alt * G = falling(N) * alt (zero iff integer N < n)
  B3b regular-representation Gram matrix singular at (2,3) and (1,2)
  B4  cell coherence: aug(W) = 1/24 = 1/aug(G), sgnHom(W) = 0, AvgSign = 3/17
  B5  stable (3,3) cross-check by exact inversion: 1/60, 1/6, parity, 1/10

Conventions (must match the Lean files exactly):
  permutations are tuples p with p[i] = sigma(i); composition comp(s,t)(x) = s(t(x)),
  matching Lean's Equiv.Perm multiplication; the group-algebra product of basis
  elements is composition in that order; K(n,i) = sum_{j>i} (i j); the cycle count
  includes fixed points.
"""

from fractions import Fraction
from itertools import permutations
import sys

FAILURES = []

def check(name, ok):
    print(("PASS  " if ok else "FAIL  ") + name)
    if not ok:
        FAILURES.append(name)

# --- permutation primitives ---------------------------------------------------

def comp(s, t):
    return tuple(s[t[x]] for x in range(len(s)))

def identity(n):
    return tuple(range(n))

def swap(n, a, b):
    p = list(range(n))
    p[a], p[b] = p[b], p[a]
    return tuple(p)

def inv(s):
    t = [0] * len(s)
    for x, y in enumerate(s):
        t[y] = x
    return tuple(t)

def cyc_count(s):
    n, seen, c = len(s), [False] * len(s), 0
    for x in range(n):
        if not seen[x]:
            c += 1
            y = x
            while not seen[y]:
                seen[y] = True
                y = s[y]
    return c

def sgn(s):
    return -1 if (len(s) - cyc_count(s)) % 2 else 1

# --- decomposeFin model ---------------------------------------------------------

def iota(e):
    """Embed Perm (Fin n) into Perm (Fin (n+1)): fix 0, act on successors."""
    return (0,) + tuple(e[x] + 1 for x in range(len(e)))

def decompose_symm(p, e):
    """Model of Equiv.Perm.decomposeFin.symm (p, e) = swap 0 p * iota e."""
    return comp(swap(len(e) + 1, 0, p), iota(e))

# C1 + C2
for m in range(2, 7):                       # m = n + 1
    n = m - 1
    perms_n = list(permutations(range(n)))
    images = {}
    bij_ok, splice_ok = True, True
    for p in range(m):
        for e in perms_n:
            s = decompose_symm(p, e)
            if s in images:
                bij_ok = False
            images[s] = (p, e)
            want = cyc_count(e) + (1 if p == 0 else 0)
            if cyc_count(s) != want:
                splice_ok = False
    bij_ok = bij_ok and len(images) == len(list(permutations(range(m))))
    check("C1 decomposeFin model is a bijection, n+1=%d" % m, bij_ok)
    check("C2 splice rule exhaustive,            n+1=%d" % m, splice_ok)

# --- group algebra over Fraction -------------------------------------------------

def alg_mul(A, B):
    C = {}
    for s, a in A.items():
        for t, b in B.items():
            st = comp(s, t)
            C[st] = C.get(st, Fraction(0)) + a * b
    return {k: v for k, v in C.items() if v != 0}

def K(n, i):
    """Dual Jucys-Murphy element K_i = sum_{j>i} (i j) as an algebra element."""
    return {swap(n, i, j): Fraction(1) for j in range(i + 1, n)}

# C3
for n in range(1, 6):
    for Nval in (Fraction(5), Fraction(7), Fraction(31, 3)):
        G = {s: Nval ** cyc_count(s) for s in permutations(range(n))}
        P = {identity(n): Fraction(1)}
        for i in range(n):
            factor = dict(K(n, i))
            factor[identity(n)] = factor.get(identity(n), Fraction(0)) + Nval
            P = alg_mul(P, factor)          # ordered: (N+K_0)(N+K_1)...
        check("C3 dual Jucys identity n=%d, N=%s" % (n, Nval), P == G)

# C4
for n in range(1, 7):
    eps_ok = all(sum(K(n, i).values()) == n - 1 - i for i in range(n))
    sgn_ok = all(sum(c * sgn(s) for s, c in K(n, i).items()) == -(n - 1 - i)
                 for i in range(n))
    check("C4 character images on K_i, n=%d" % n, eps_ok and sgn_ok)

# C5 shortest slot-word recursion (mirrors the Lean exists_min_word witness)
def min_word(s):
    n = len(s)
    if n == 0:
        return []
    p = s[0]
    ie = comp(swap(n, 0, p), s)             # fixes 0
    assert ie[0] == 0
    e = tuple(ie[x + 1] - 1 for x in range(n - 1))
    sub = [(i + 1, j + 1) for (i, j) in min_word(e)]
    return ([] if p == 0 else [(0, p)]) + sub

for n in range(1, 6):
    ok = True
    for s in permutations(range(n)):
        w = min_word(s)
        slots = [i for i, _ in w]
        ok &= all(i < j for i, j in w)                                   # letters from K_i
        ok &= slots == sorted(slots) and len(set(slots)) == len(slots)   # <=1 per slot
        prod = identity(n)
        for i, j in w:
            prod = comp(prod, swap(n, i, j))                             # ordered product
        ok &= prod == s
        ok &= len(w) == n - cyc_count(s)                                 # minimal length
    check("C5 shortest slot-word for every sigma, n=%d" % n, ok)

# C6 Cell23: exact Penrose + symmetry + row sums
S3 = list(permutations(range(3)))

def wval(s):
    if s == identity(3):
        return Fraction(17, 144)
    return Fraction(1, 144) if sgn(s) == -1 else Fraction(-7, 144)

G6 = [[Fraction(2) ** cyc_count(comp(inv(a), b)) for b in S3] for a in S3]
W6 = [[wval(comp(inv(a), b)) for b in S3] for a in S3]

def mat_mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(6)) for j in range(6)]
            for i in range(6)]

def mat_T(A):
    return [[A[j][i] for j in range(6)] for i in range(6)]

GW, WG = mat_mul(G6, W6), mat_mul(W6, G6)
pen = (mat_mul(GW, G6) == G6 and mat_mul(WG, W6) == W6
       and mat_T(GW) == GW and mat_T(WG) == WG)
check("C6a Cell23 Penrose identities (exact, 6x6 over Q)", pen)
check("C6b Cell23 G and W symmetric", mat_T(G6) == G6 and mat_T(W6) == W6)
rows = all(sum(W6[a]) == Fraction(1, 24) for a in range(6))
srows = all(sum(sgn(S3[b]) * W6[a][b] for b in range(6)) == 0 for a in range(6))
check("C6c Cell23 row sums 1/24 and signed row sums 0", rows and srows)



# ------------------------------------------------------------------------
# B-suite: below-threshold package checks B1-B5 (blueprint ch:below; added 12 June)
# ------------------------------------------------------------------------
F = Fraction
def comp(s,t): return tuple(s[t[x]] for x in range(len(s)))
def ident(n): return tuple(range(n))
def inv(s):
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
def sgn(s): return -1 if (len(s)-cyc(s))%2 else 1
def amul(A,B):
    C={}
    for s,a in A.items():
        for t,b in B.items():
            st=comp(s,t); C[st]=C.get(st,F(0))+a*b
    return {k:v for k,v in C.items() if v!=0}
def eps(x): return sum(x.values())
def shat(x): return sum(sgn(s)*v for s,v in x.items())
def gram(n,N): return {s: N**cyc(s) for s in permutations(range(n))}
def alt(n): return {s: F(sgn(s)) for s in permutations(range(n))}
def rising(n,N):
    r=F(1)
    for m in range(n): r*=(N+m)
    return r
def falling(n,N):
    r=F(1)
    for m in range(n): r*=(N-m)
    return r

# B1: absorption alt*x = shat(x)*alt  (all single g, n<=4; plus a messy x)
for n in range(1,5):
    ok=True
    a=alt(n)
    for g in permutations(range(n)):
        lhs=amul(a,{g:F(1)})
        rhs={s:F(sgn(g))*v for s,v in a.items()}
        ok&= lhs==rhs
    x={s: F(3*i+1, i+2) for i,s in enumerate(permutations(range(n)))}
    lhs=amul(a,x); sh=shat(x)
    rhs={s: sh*v for s,v in a.items() if sh*v!=0}
    ok&= lhs==rhs
    check("B1 alternating absorption alt*x = shat(x)*alt, n=%d"%n, ok)

# B2: eps/shat of gram = rising/falling factorials, ALL N incl. below threshold + fractional
for n in range(1,6):
    ok=True
    for N in (F(1),F(2),F(3),F(7),F(1,2)):
        G=gram(n,N)
        ok&= eps(G)==rising(n,N) and shat(G)==falling(n,N)
    check("B2 eps(G)=rising, shat(G)=falling (all N), n=%d"%n, ok)

# B3: alt*G = falling*alt; in particular =0 exactly when falling=0 (integer 0<=N<n)
ok=True
for n in range(2,5):
    for N in range(1,n+1):
        a=alt(n); G=gram(n,F(N))
        prod=amul(a,G); f=falling(n,F(N))
        want={} if f==0 else {s:f*v for s,v in a.items()}
        ok&= prod==want
        ok&= (f==0) == (1<=N<n or N==0)
check("B3 alt*G = falling(N)*alt; kernel witness iff N<n", ok)

# B3b: det of regular Gram matrix vanishes at (2,3) and (1,2)
def detF(M):
    M=[row[:] for row in M]; n=len(M); sign=1
    for c in range(n):
        p=next((r for r in range(c,n) if M[r][c]!=0), None)
        if p is None: return F(0)
        if p!=c: M[c],M[p]=M[p],M[c]; sign=-sign
        for r in range(c+1,n):
            f=M[r][c]/M[c][c]
            for cc in range(c,n): M[r][cc]-=f*M[c][cc]
    d=F(sign)
    for i in range(n): d*=M[i][i]
    return d
S3=list(permutations(range(3)))
G23=[[F(2)**cyc(comp(inv(a),b)) for b in S3] for a in S3]
S2=list(permutations(range(2)))
G12=[[F(1)**cyc(comp(inv(a),b)) for b in S2] for a in S2]
check("B3b det G = 0 at (N,n)=(2,3) and (1,2)", detF(G23)==0 and detF(G12)==0)

# B4: cell coherence: eps(W)=1/24=1/eps(G), shat(W)=0, AvgSign = 3/17
def wval(s):
    if s==ident(3): return F(17,144)
    return F(1,144) if sgn(s)==-1 else F(-7,144)
W={s:wval(s) for s in S3}
G={s:F(2)**cyc(s) for s in S3}
ok = eps(W)==F(1,24)==1/eps(G) and shat(W)==0==shat(G)
ratio = eps(W)/sum(abs(v) for v in W.values())
ok &= ratio==F(3,17)
check("B4 cell (2,3): eps(W)=1/24=1/eps(G), shat(W)=0, AvgSign=3/17", ok)

# B5: stable cross-check n=3,N=3 -- invert G exactly, verify rules + parity + ratio
def invmat(M):
    n=len(M); A=[row[:]+[F(1) if i==j else F(0) for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=next(r for r in range(c,n) if A[r][c]!=0)
        A[c],A[p]=A[p],A[c]
        pv=A[c][c]; A[c]=[v/pv for v in A[c]]
        for r in range(n):
            if r!=c and A[r][c]!=0:
                f=A[r][c]; A[r]=[vr-f*vc for vr,vc in zip(A[r],A[c])]
    return [row[n:] for row in A]
G33=[[F(3)**cyc(comp(inv(a),b)) for b in S3] for a in S3]
Wi=invmat(G33)
i0=S3.index(ident(3))
wg={s: Wi[i0][S3.index(s)] for s in S3}
ok = sum(wg.values())==1/rising(3,F(3)) and sum(sgn(s)*v for s,v in wg.items())==1/falling(3,F(3))
ok &= all((1 if (3-cyc(s))%2==0 else -1)*wg[s]>0 for s in S3)   # strict parity
ok &= sum(wg.values())/sum(abs(v) for v in wg.values()) == F(3*2*1, 3*4*5)  # 1/10
check("B5 stable (3,3): rules 1/60 & 1/6, strict parity, ratio 1/10", ok)

print()
if FAILURES:
    print("%d FAILURE(S):" % len(FAILURES))
    for f in FAILURES:
        print("  " + f)
    sys.exit(1)
print("ALL CONVENTION CHECKS PASSED")
sys.exit(0)
