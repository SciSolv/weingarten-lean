#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Independent exact-arithmetic cross-check of the UNITARY spine of weingarten-lean.

Standard library ONLY: fractions.Fraction (exact rationals) and itertools (enumeration).
No floats, no numpy, no sympy. Every check compares two GENUINELY INDEPENDENT
computations -- brute-force enumeration of S_n versus a closed product formula, or
exhaustive Gram inversion versus a sign predicate -- never a value against itself.

Conventions (must match the Lean source / blueprint ch:jm, ch:cycle, ch:wg, ch:closed):
  * a permutation is a tuple p with p[i] = sigma(i);
  * group-algebra / composition order is comp(s,t)(x) = s(t(x)), i.e. Lean's
    Equiv.Perm multiplication and MonoidAlgebra convolution delta_s delta_t = delta_{st};
  * cycle count c(sigma) counts orbits (fixed points included);
  * dual Jucys-Murphy element K_i = sum_{j>i} (i j)  (Definition def:jm); K_{n-1}=0;
  * Gram element  G_n(N) = sum_s N^c(s) . delta_s   (def:gram);
  * Weingarten element  W = G^{-1}  for integer N >= n  (def:wgElement, thm:gram_mul);
  * Wg(sigma,N) = delta_sigma-coefficient of W.

Theorems cross-checked here (one printed line each):
  jucys         thm:jucys / Weingarten.gram_eq_prod
  rising_sum    aug_gram half / Weingarten.aug_gram, anchor of thm:rising
  falling_sum   sgnHom_gram half / Weingarten.sgnHom_gram, anchor of thm:falling
  sign_pattern  thm:parity / Weingarten.wg_sign  (exact Gram inversion)
  closed_form   thm:closed_form / Weingarten.cancellation_ratio + sum_abs_wg
"""

from fractions import Fraction as F
from itertools import permutations
import sys

FAILURES = []

def report(name, ok, detail=""):
    if ok:
        print("PASS " + name)
    else:
        print("FAIL %s: %s" % (name, detail))
        FAILURES.append(name)

# --- permutation primitives ---------------------------------------------------

def comp(s, t):
    """Group product / composition: comp(s,t)(x) = s(t(x))."""
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

# --- group algebra over Fraction (or any ring of coefficients) -----------------

def alg_mul(A, B):
    C = {}
    for s, a in A.items():
        for t, b in B.items():
            st = comp(s, t)
            C[st] = C.get(st, F(0)) + a * b
    return {k: v for k, v in C.items() if v != 0}

def K(n, i):
    """Dual Jucys-Murphy element K_i = sum_{j>i} (i j)."""
    return {swap(n, i, j): F(1) for j in range(i + 1, n)}

# ==============================================================================
# jucys -- thm:jucys :  sum_s N^c(s) . s  ==  prod_{i=0}^{n-1} (N + K_i)
#
# INDEPENDENT?  LHS is built by enumerating S_n and assigning each element the
# scalar N^c(s) (brute force).  RHS is built by multiplying n group-algebra
# factors in the algebra (no cycle counts touched).  Two different constructions.
#
# Polynomial-in-N identity, degree n in N.  Pin it by agreeing at >= n+2 distinct
# integer N values per element, then also confirm full structural equality at a
# generic rational N.  Anchor n=2 verified literally:  N^2.e + N.(12).
# ==============================================================================
def jucys_check():
    detail = ""
    ok = True
    for n in range(1, 6):
        Svals = list(permutations(range(n)))
        # sample at enough points to pin a degree-n polynomial per element
        pts = [F(k) for k in range(-1, n + 4)]    # n+5 >= n+2 distinct points
        assert len(pts) >= n + 2
        for Nval in pts:
            # LHS: brute-force enumeration
            lhs = {s: Nval ** cyc_count(s) for s in Svals}
            # RHS: product of algebra factors, increasing index order
            rhs = {identity(n): F(1)}
            for i in range(n):
                factor = dict(K(n, i))
                factor[identity(n)] = factor.get(identity(n), F(0)) + Nval
                rhs = alg_mul(rhs, factor)
            # normalise (drop zero coeffs already dropped in alg_mul; do same for lhs)
            lhs = {k: v for k, v in lhs.items() if v != 0}
            if lhs != rhs:
                ok = False
                detail = "n=%d N=%s mismatch" % (n, Nval)
                return ok, detail
    # explicit anchor n=2 : N^2 e + N (12)
    n = 2
    e, t = identity(2), swap(2, 0, 1)
    for Nval in (F(2), F(5), F(-3), F(7, 2)):
        rhs = {e: F(1)}
        for i in range(n):
            factor = dict(K(n, i)); factor[e] = factor.get(e, F(0)) + Nval
            rhs = alg_mul(rhs, factor)
        want = {k: v for k, v in {e: Nval ** 2, t: Nval}.items() if v != 0}
        if rhs != want:
            ok = False
            detail = "anchor n=2 failed at N=%s" % Nval
            return ok, detail
    return ok, "n=1..5, %d+ pts each (deg-n poly pinned); anchor N^2.e+N.(12)" % (n + 5)

ok, d = jucys_check()
report("jucys", ok, d)

# ==============================================================================
# rising_sum --  sum_{s in S_n} N^c(s)  ==  prod_{j=0}^{n-1} (N + j)
#
# INDEPENDENT?  LHS sums N^c(s) over a brute-force enumeration of S_n.
# RHS is the rising factorial product -- a closed form that never enumerates S_n.
# Degree-n polynomial in N; pin at >= n+2 integer points (here negatives too).
# Anchor n=3 : N(N+1)(N+2).
# ==============================================================================
def rising_sum_check():
    for n in range(1, 8):
        pts = [F(k) for k in range(-2, n + 4)]   # n+6 distinct points
        assert len(pts) >= n + 2
        for Nval in pts:
            lhs = sum(Nval ** cyc_count(s) for s in permutations(range(n)))
            rhs = F(1)
            for j in range(n):
                rhs *= (Nval + j)
            if lhs != rhs:
                return False, "n=%d N=%s : %s != %s" % (n, Nval, lhs, rhs)
    # anchor n=3 : N(N+1)(N+2)
    for Nval in (F(4), F(-5), F(10, 3)):
        lhs = sum(Nval ** cyc_count(s) for s in permutations(range(3)))
        if lhs != Nval * (Nval + 1) * (Nval + 2):
            return False, "anchor n=3 N=%s" % Nval
    return True, "n=1..7, deg-n poly pinned at n+6 pts; anchor N(N+1)(N+2)"

report("rising_sum", *rising_sum_check())

# ==============================================================================
# falling_sum -- sum_{s} sgn(s) N^c(s) == prod_{j=0}^{n-1} (N - j)
#
# INDEPENDENT?  LHS: signed brute-force enumeration of S_n.  RHS: falling
# factorial closed form.  Anchor n=3 : N(N-1)(N-2).
# ==============================================================================
def falling_sum_check():
    for n in range(1, 8):
        pts = [F(k) for k in range(-2, n + 4)]
        assert len(pts) >= n + 2
        for Nval in pts:
            lhs = sum(sgn(s) * Nval ** cyc_count(s) for s in permutations(range(n)))
            rhs = F(1)
            for j in range(n):
                rhs *= (Nval - j)
            if lhs != rhs:
                return False, "n=%d N=%s : %s != %s" % (n, Nval, lhs, rhs)
    for Nval in (F(4), F(-5), F(10, 3)):
        lhs = sum(sgn(s) * Nval ** cyc_count(s) for s in permutations(range(3)))
        if lhs != Nval * (Nval - 1) * (Nval - 2):
            return False, "anchor n=3 N=%s" % Nval
    return True, "n=1..7, deg-n poly pinned at n+6 pts; anchor N(N-1)(N-2)"

report("falling_sum", *falling_sum_check())

# --- exact dense matrix tools over Fraction (for sign_pattern & closed_form) ---

def mat_inv(M):
    """Exact inverse via Gauss-Jordan over Fraction; raises if singular."""
    n = len(M)
    A = [list(M[i]) + [F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            raise ZeroDivisionError("singular")
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [vr - f * vc for vr, vc in zip(A[r], A[c])]
    return [row[n:] for row in A]

def gram_matrix(Svals, Nval):
    """Unitary Gram G(s,t) = N^{c(s t^{-1})}.  (s^{-1} t and s t^{-1} agree as
    class functions on the diagonal structure; we use the def:gram23 convention
    G(s,t)=N^{c(s^{-1} t)} used in the Lean cell.)"""
    return [[Nval ** cyc_count(comp(inv(s), t)) for t in Svals] for s in Svals]

# ==============================================================================
# sign_pattern -- thm:parity / Weingarten.wg_sign :
#   for integer N >= n,  sign(Wg(s,N)) == sgn(s)  for every s,
#   equivalently (-1)^|s| Wg(s,N) > 0.
#
# INDEPENDENT?  Wg is obtained by EXACT INVERSION of the n!xn! Gram matrix
# (a construction that never mentions parity).  The predicate it is compared
# against -- sgn(s) computed from cycle structure -- is a completely separate
# computation.  We assert strict positivity of (-1)^|s| Wg(s).
# Anchor n=2, N=3 : Wg(e)=1/8, Wg((12))=-1/24.
# ==============================================================================
def sign_pattern_check():
    import time
    detail_parts = []
    for n in range(2, 6):
        if n == 5:
            # n=5 -> 120x120 exact inverse; guard with a wall-clock budget
            t0 = time.time()
        Svals = list(permutations(range(n)))
        e_idx = Svals.index(identity(n))
        for Nval in [F(N) for N in range(n, n + 4)]:
            G = gram_matrix(Svals, Nval)
            Winv = mat_inv(G)
            # Wg(sigma) = coefficient of delta_sigma in W = G^{-1}.  Row e of W.
            wrow = Winv[e_idx]
            for j, s in enumerate(Svals):
                val = wrow[j]
                par = 1 if (n - cyc_count(s)) % 2 == 0 else -1   # (-1)^|s|
                if not (par * val > 0):
                    return False, "n=%d N=%s sigma=%s : (-1)^|s| Wg = %s not > 0" % (
                        n, Nval, s, par * val)
                # sign(Wg) must equal sgn(s)
                wg_sign = 1 if val > 0 else (-1 if val < 0 else 0)
                if wg_sign != sgn(s):
                    return False, "n=%d N=%s sigma=%s sign mismatch" % (n, Nval, s)
        if n == 5 and time.time() - t0 > 90:
            detail_parts.append("n=5 slow")
    # anchor n=2, N=3 : Wg(e)=1/8, Wg((12))=-1/24
    Svals = list(permutations(range(2)))
    G = gram_matrix(Svals, F(3))
    W = mat_inv(G)
    e_idx = Svals.index(identity(2))
    t_idx = Svals.index(swap(2, 0, 1))
    if W[e_idx][e_idx] != F(1, 8) or W[e_idx][t_idx] != F(-1, 24):
        return False, "anchor (2,3): Wg(e)=%s Wg((12))=%s" % (W[e_idx][e_idx], W[e_idx][t_idx])
    return True, "n=2..5 exact-inverted, N=n..n+3; anchor Wg(e)=1/8, Wg((12))=-1/24"

report("sign_pattern", *sign_pattern_check())

# ==============================================================================
# closed_form -- thm:closed_form / Weingarten.cancellation_ratio & sum_abs_wg :
#   sum_s |Wg(s,N)|              == prod_{m=0}^{n-1} 1/(N - m)
#   (sum_s Wg) / (sum_s |Wg|)    == prod_{j=0}^{n-1} (N - j)/(N + j)
#
# INDEPENDENT?  LEFT sides are computed from the EXACT GRAM INVERSE (enumerate
# S_n, build G, invert, read row e, sum / abs-sum).  RIGHT sides are the closed
# product formulas, computed without any matrix.  Two independent routes.
# Also independently confirms sum_s Wg == prod 1/(N+m) (rising sum rule on Wg).
# ==============================================================================
def closed_form_check():
    for n in range(2, 6):
        Svals = list(permutations(range(n)))
        e_idx = Svals.index(identity(n))
        for Nval in [F(N) for N in range(n, n + 4)]:
            G = gram_matrix(Svals, Nval)
            W = mat_inv(G)
            wrow = W[e_idx]
            wg = {s: wrow[j] for j, s in enumerate(Svals)}

            sum_wg = sum(wg.values())
            sum_abs = sum(abs(v) for v in wg.values())

            rising_inv = F(1)
            for m in range(n):
                rising_inv *= F(1, 1) / (Nval + m)
            falling_inv = F(1)
            for m in range(n):
                falling_inv *= F(1, 1) / (Nval - m)
            ratio_closed = F(1)
            for j in range(n):
                ratio_closed *= (Nval - j) / (Nval + j) if (Nval + j) != 0 else None

            if sum_wg != rising_inv:
                return False, "n=%d N=%s sum Wg = %s != %s" % (n, Nval, sum_wg, rising_inv)
            if sum_abs != falling_inv:
                return False, "n=%d N=%s sum|Wg| = %s != %s" % (n, Nval, sum_abs, falling_inv)
            if sum_wg / sum_abs != ratio_closed:
                return False, "n=%d N=%s ratio = %s != %s" % (
                    n, Nval, sum_wg / sum_abs, ratio_closed)
            # cross-check that |Wg(s)| = sgn(s) Wg(s) per element (parity feeding closed form)
            for j, s in enumerate(Svals):
                if abs(wg[s]) != sgn(s) * wg[s]:
                    return False, "n=%d N=%s |Wg| != sgn.Wg at %s" % (n, Nval, s)
    return True, "n=2..5, N=n..n+3: sum|Wg|=prod 1/(N-m), ratio=prod (N-j)/(N+j)"

report("closed_form", *closed_form_check())

print()
if FAILURES:
    print("%d FAILURE(S): %s" % (len(FAILURES), ", ".join(FAILURES)))
    sys.exit(1)
print("ALL UNITARY CROSS-CHECKS PASSED")
sys.exit(0)
