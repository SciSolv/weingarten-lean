#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Independent exact-arithmetic cross-check of the per-eigenvalue Penrose rules.

This is NOT a re-proof. Every check pits two genuinely independent computations
against each other (brute-force enumeration over pair partitions / permutations
vs. hand-written closed forms). Exact rationals only (fractions.Fraction),
stdlib only. No floats, no numpy, no sympy. None of the checks compares a value
to itself.

Project conventions (matched against Weingarten/OrthogonalGram.lean,
Weingarten/BelowThreshold.lean and Weingarten/Gram.lean):

  * orthGram GO(p,q) = N^loops(p,q) on pair partitions of {0,..,2n-1}, with
    loops counted by union-find on the overlay graph (as in
    verify_orthogonal.py).
  * IsCommPenrosePartner W of G: GWG = G, WGW = W, WG = GW.
  * The per-eigenvalue rule (smul_vecMul_eq_of_vecMul_eq_smul): if y G = lam y
    with lam invertible then lam (y W) = y -- no invertibility of G itself.
  * evenRising r_n(N) = prod_{j<n}(N+2j); fallingFact f_n(N) = prod_{j<n}(N-j).
  * The unitary group-algebra Gram at n = 2 over S_2 has entries
    N^cycleCount(sigma tau^{-1}); its integer singular set is the full band
    {-(n-1),..,n-1} = {-1,0,1} (not_isUnit_gram + not_isUnit_gram_neg).

Checks (at the genuinely singular orthogonal cell n = 2, N = 1, where the
IsUnit-Gram hypotheses of the older conditional rules are unavailable):

  penrose_eigen_singular_cell  GO at n=2, N=1 (built from pairings + union-find)
                               equals the hand-written all-ones 3x3 matrix J;
                               the hand-written W = J/9 satisfies both Penrose
                               equations AND commutation exactly, while GO is
                               exactly singular (det = 0).
  eigen_row_sums               row sums of W are each 1/3 = 1/r_2(1), with
                               r_2 built independently as prod (N+2j) --
                               the per-eigenvalue even-rising rule
                               (evenRising_smul_vecMul_one_of_partner).
  det_vanish_at_cell           f_2(1) = 0 and the signed determinant covector
                               kills W exactly (v^T W = 0) -- the vanishing
                               complement (vecMul_detVec_eq_zero).
  unitary_band                 det of the unitary n=2 Gram [[N^2,N],[N,N^2]]
                               (entries rebuilt from cycleCount over S_2) by
                               brute 2x2 cofactor vs. the closed product
                               r(N)*f(N) = N(N+1)*N(N-1); the determinant
                               vanishes EXACTLY at N in {-1,0,1} over integers
                               scanned on [-10,10] -- the full singular band
                               (not_isUnit_gram, not_isUnit_gram_neg).

Prints exactly one "PASS <name>" / "FAIL <name>: <detail>" line per check.
Exit 0 iff all checks pass.
"""

from fractions import Fraction
from itertools import permutations
import sys

FAILS = []

def report(name, ok, detail=""):
    if ok:
        print("PASS " + name)
    else:
        print("FAIL %s: %s" % (name, detail))
        FAILS.append(name)

# ---------------------------------------------------------------------------
# Pair partitions and loops (as in verify_orthogonal.py -- union-find overlay)
# ---------------------------------------------------------------------------

def pair_partitions(twon):
    pts = tuple(range(twon))
    def rec(remaining):
        if not remaining:
            yield ()
            return
        a = remaining[0]
        for i in range(1, len(remaining)):
            b = remaining[i]
            rest = remaining[1:i] + remaining[i+1:]
            for tail in rec(rest):
                yield ((a, b),) + tail
    yield from rec(pts)

def loops_unionfind(p_match, q_match, twon):
    parent = list(range(twon))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[rx] = ry
    for a, b in p_match:
        union(a, b)
    for a, b in q_match:
        union(a, b)
    return len({find(x) for x in range(twon)})

def qpair_matching(rho):
    k = len(rho)
    return tuple((a, k + rho[a]) for a in range(k))

def perm_cyc_count(s):
    n = len(s)
    seen = [False] * n
    c = 0
    for x in range(n):
        if not seen[x]:
            c += 1
            y = x
            while not seen[y]:
                seen[y] = True
                y = s[y]
    return c

def perm_sgn(s):
    return -1 if (len(s) - perm_cyc_count(s)) % 2 else 1

# ---------------------------------------------------------------------------
# Closed-form eigenvalues (independent of any Gram entry)
# ---------------------------------------------------------------------------

def even_rising(n, N):
    r = Fraction(1)
    for j in range(n):
        r *= (N + 2 * j)
    return r

def falling_fact(n, N):
    r = Fraction(1)
    for j in range(n):
        r *= (N - j)
    return r

# ---------------------------------------------------------------------------
# Exact linear algebra helpers
# ---------------------------------------------------------------------------

def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]

def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))

# ---------------------------------------------------------------------------
# The singular cell: n = 2, N = 1. GO is the all-ones 3x3 matrix J; the
# Moore-Penrose pseudo-inverse of J is J/9 (hand-written closed form; J has
# the single nonzero eigenvalue 3 on the ones-line, and (J/9) J (J/9) = J/9
# since J^2 = 3J). W = J/9 is the exact object the Lean predicate
# IsCommPenrosePartner accepts at this cell.
# ---------------------------------------------------------------------------

def build_singular_cell():
    """GO at n=2, N=1 from pairings + union-find (side one), the hand-written
    J and W = J/9 (side two)."""
    twon, Nv = 4, Fraction(1)
    parts = list(pair_partitions(twon))
    GO = [[Nv ** loops_unionfind(p, q, twon) for q in parts] for p in parts]
    J = [[Fraction(1)] * 3 for _ in range(3)]
    W = [[Fraction(1, 9)] * 3 for _ in range(3)]
    return parts, GO, J, W

def check_penrose_eigen_singular_cell():
    parts, GO, J, W = build_singular_cell()
    if len(parts) != 3:
        return False, "expected 3 pair partitions of 4 points, got %d" % len(parts)
    # Two independent constructions of the Gram must agree.
    if GO != J:
        return False, "union-find Gram at n=2, N=1 != all-ones J"
    # The cell is genuinely singular: the older IsUnit-Gram rules do not apply.
    if det3(GO) != 0:
        return False, "det GO = %s != 0 (cell not singular?)" % det3(GO)
    # Both Penrose equations and commutation, exactly.
    GW = mat_mul(GO, W)
    WG = mat_mul(W, GO)
    if mat_mul(GW, GO) != GO:
        return False, "GWG != G"
    if mat_mul(WG, W) != W:
        return False, "WGW != W"
    if WG != GW:
        return False, "WG != GW"
    return True, ""

def check_eigen_row_sums():
    _, GO, _, W = build_singular_cell()
    lam = even_rising(2, Fraction(1))       # independent closed form: 1*(1+2)
    if lam != 3:
        return False, "evenRising(2,1) = %s != 3" % lam
    ones = [Fraction(1)] * 3
    # y G = lam y for the all-ones covector (brute matrix product).
    yG = [sum(ones[p] * GO[p][q] for p in range(3)) for q in range(3)]
    if yG != [lam * o for o in ones]:
        return False, "1^T G != r_2(1) * 1^T"
    # The per-eigenvalue rule: lam * (1^T W) = 1^T, i.e. every row sum is 1/3.
    for i in range(3):
        s = sum(W[i])
        if s != Fraction(1, 3):
            return False, "row %d sum = %s != 1/3" % (i, s)
        if lam * s != 1:
            return False, "r_2(1) * rowsum = %s != 1" % (lam * s)
    return True, ""

def check_det_vanish_at_cell():
    parts, _, _, W = build_singular_cell()
    mu = falling_fact(2, Fraction(1))       # 1*(1-1) = 0: NOT a unit here
    if mu != 0:
        return False, "fallingFact(2,1) = %s != 0" % mu
    # Alternating covector v on the qPair pairings, signs from permutation
    # parity (independent of any Gram data).
    index = {m: i for i, m in enumerate(parts)}
    v = [Fraction(0)] * 3
    for rho in permutations(range(2)):
        v[index[qpair_matching(rho)]] = Fraction(perm_sgn(rho))
    vW = [sum(v[p] * W[p][q] for p in range(3)) for q in range(3)]
    if vW != [Fraction(0)] * 3:
        return False, "v^T W = %s != 0" % vW
    return True, ""

def check_unitary_band():
    band = {-1, 0, 1}
    for Nint in range(-10, 11):
        Nv = Fraction(Nint)
        # Side one: Gram entries from cycleCount over S_2, brute 2x2 cofactor.
        perms = list(permutations(range(2)))
        def compose_inv(s, t):
            # sigma o tau^{-1} as a tuple
            tinv = [0] * 2
            for i in range(2):
                tinv[t[i]] = i
            return tuple(s[tinv[x]] for x in range(2))
        G = [[Nv ** perm_cyc_count(compose_inv(s, t)) for t in perms]
             for s in perms]
        if G != [[Nv ** 2, Nv], [Nv, Nv ** 2]]:
            return False, "N=%d Gram != [[N^2,N],[N,N^2]]" % Nint
        det_brute = G[0][0] * G[1][1] - G[0][1] * G[1][0]
        # Side two: the closed product rising * falling = N(N+1) * N(N-1).
        det_closed = (Nv * (Nv + 1)) * (Nv * (Nv - 1))
        if det_brute != det_closed:
            return False, ("N=%d det brute=%s != rising*falling=%s"
                           % (Nint, det_brute, det_closed))
        # The singular set on the scan is exactly the band {-1, 0, 1}.
        if (det_brute == 0) != (Nint in band):
            return False, ("N=%d det=%s inconsistent with band {-1,0,1}"
                           % (Nint, det_brute))
    return True, ""

# ===========================================================================

def main():
    report("penrose_eigen_singular_cell", *check_penrose_eigen_singular_cell())
    report("eigen_row_sums", *check_eigen_row_sums())
    report("det_vanish_at_cell", *check_det_vanish_at_cell())
    report("unitary_band", *check_unitary_band())
    if FAILS:
        sys.exit(1)
    sys.exit(0)

if __name__ == "__main__":
    main()
