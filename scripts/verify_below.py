#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Independent exact-arithmetic cross-check of the below-threshold package.

Package: below-threshold (blueprint ch:below, Weingarten/BelowThreshold.lean,
Weingarten/Cell23.lean).

Conventions pinned to the Lean source:
  * permutations are tuples p with p[i] = sigma(i); comp(s,t)(x) = s(t(x))
    is Lean's Equiv.Perm multiplication (s * t).
  * cycleCount c(sigma) = number of orbits (fixed points included).
  * Gram MATRIX over Q:  G(sigma, tau) = N ^ c(sigma^{-1} tau).
  * Below threshold = integer 1 <= N < n: G is singular.
  * W = Moore-Penrose pseudo-inverse: the UNIQUE matrix with
        G W G = G,  W G W = W,  (G W)^T = G W,  (W G)^T = W G.
  * sgn character: sgn(sigma) = (-1)^{n - c(sigma)}.

INDEPENDENCE.  The pseudo-inverse W is NOT taken from the Lean files' candidate
values.  It is constructed from scratch by exact rational linear algebra: G is a
real-symmetric (here rational-symmetric) matrix, so it is orthogonally
diagonalizable and its Moore-Penrose inverse is the polynomial p(G) that inverts
G on its column space and kills its kernel.  We build that polynomial from the
exact characteristic / minimal data of G over Q (Gram-Schmidt-free: we use the
fact that for symmetric G, W = G * (G^3)^+ ... ) -- concretely we compute the
pseudo-inverse via the limit-free identity

        W = lim_{e->0} (G^2 + e I)^{-1} G

evaluated EXACTLY as a rational function of e and taking the constant term that
survives (the projection onto the column space).  We implement this by the
standard exact route: diagonalize is avoided; instead we use that for symmetric
G the pseudo-inverse equals  G^T (G G^T)^+  and bootstrap (G G^T)^+ on the
nonsingular part via the adjugate of the restriction of G to its row space.

Each check then compares this independently-built W against the Penrose
equations and the Lean anchors (17/144 etc.), which were NEVER used to build W.

Output: one line per theorem, "PASS <name>" or "FAIL <name>: <detail>".
"""

from fractions import Fraction as F
from itertools import permutations
import sys

# ----------------------------------------------------------------------------
# permutation primitives (match Lean Equiv.Perm conventions)
# ----------------------------------------------------------------------------

def comp(s, t):                      # (s * t)(x) = s(t(x))
    return tuple(s[t[x]] for x in range(len(s)))

def ident(n):
    return tuple(range(n))

def inv(s):
    t = [0] * len(s)
    for x, y in enumerate(s):
        t[y] = x
    return tuple(t)

def cyc(s):
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
    return -1 if (len(s) - cyc(s)) % 2 else 1

# ----------------------------------------------------------------------------
# exact rational matrix algebra
# ----------------------------------------------------------------------------

def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]

def mat_T(A):
    return [[A[j][i] for j in range(len(A))] for i in range(len(A[0]))]

def mat_eq(A, B):
    return A == B

def ident_mat(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]

def rref(M):
    """Reduced row echelon form (exact); returns (R, pivot_columns)."""
    R = [row[:] for row in M]
    rows, cols = len(R), len(R[0])
    pivots = []
    r = 0
    for c in range(cols):
        # find pivot
        piv = next((i for i in range(r, rows) if R[i][c] != 0), None)
        if piv is None:
            continue
        R[r], R[piv] = R[piv], R[r]
        pv = R[r][c]
        R[r] = [v / pv for v in R[r]]
        for i in range(rows):
            if i != r and R[i][c] != 0:
                f = R[i][c]
                R[i] = [a - f * b for a, b in zip(R[i], R[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    return R, pivots

def rank(M):
    _, p = rref(M)
    return len(p)

def inv_mat(M):
    """Exact inverse of a nonsingular square matrix; raises if singular."""
    n = len(M)
    A = [M[i][:] + [F(1) if i == j else F(0) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None:
            raise ZeroDivisionError("singular")
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [row[n:] for row in A]

# ----------------------------------------------------------------------------
# Moore-Penrose pseudo-inverse of a SYMMETRIC rational matrix,
# built INDEPENDENTLY of any candidate Weingarten values.
#
# For symmetric G:  column space = row space = orthogonal complement of kernel.
# Pick a maximal set B of independent columns of G (a basis of the column space
# = range).  Let C = G[:, B] (n x r, full column rank r), and since G is
# symmetric range = row space, the rows indexed by B also span the row space.
# The Moore-Penrose inverse is
#       G^+ = C (C^T C)^{-1} (C^T C)^{-1} C^T  ... NO -- that is for G = C C^T.
#
# Cleanest exact route for symmetric G:  G^+ = G ( G^3 )^+ is circular.
# Use instead the projector route:
#   Let P = orthogonal projector onto range(G) (range = col space of G).
#   On range(G), G restricts to an invertible operator; G^+ is its inverse on
#   range(G), zero on ker(G).  Concretely, choose an orthonormal-free basis:
#   columns U = G[:, B] form a basis of range(G).  Then
#       P = U (U^T U)^{-1} U^T          (orthogonal projector onto range, exact)
#   and G^+ = P G^+ P with G G^+ = P, so on the basis U:  G (U a) spans range,
#   and we solve G^+ = U (U^T G U)^{-1} U^T   BECAUSE for symmetric G the
#   compression U^T G U is invertible and  G^+ = U (U^T G U)^{-1} U^T  is the
#   unique Penrose inverse (verified below by the four Penrose equations, which
#   are an INDEPENDENT test of this construction).
# ----------------------------------------------------------------------------

def col_space_basis(G):
    """Indices of a maximal independent set of columns of G."""
    _, piv = rref(mat_T(G))   # pivots of rows of G^T = independent columns of G
    return piv

def pinv_symmetric(G):
    """Moore-Penrose pseudo-inverse of symmetric rational G, built from
    scratch via  G^+ = U (U^T G U)^{-1} U^T  with U a basis of range(G)."""
    n = len(G)
    B = col_space_basis(G)
    if not B:
        return [[F(0)] * n for _ in range(n)]
    U = [[G[i][b] for b in B] for i in range(n)]          # n x r
    UT = mat_T(U)                                         # r x n
    M = mat_mul(mat_mul(UT, G), U)                        # r x r compression
    Minv = inv_mat(M)
    return mat_mul(mat_mul(U, Minv), UT)                  # n x n

# ----------------------------------------------------------------------------
# Gram matrix and group enumeration
# ----------------------------------------------------------------------------

def perms(n):
    return list(permutations(range(n)))

def gram_matrix(n, N):
    S = perms(n)
    return [[N ** cyc(comp(inv(a), b)) for b in S] for a in S]

# ----------------------------------------------------------------------------
# reporting
# ----------------------------------------------------------------------------

FAILURES = []
def report(name, ok, detail=""):
    if ok:
        print("PASS " + name)
    else:
        print("FAIL " + name + ": " + detail)
        FAILURES.append(name)

# ============================================================================
# penrose_pair: the independently-built pseudo-inverse W satisfies all four
# Penrose equations for several (n, N), including below threshold.
# ============================================================================

def check_penrose_pair():
    cases = []
    # n=2: N=1 (below threshold), N=3,4 (stable)
    cases += [(2, F(1)), (2, F(3)), (2, F(4))]
    # n=3: N=1,2 (below threshold), N=3,5 (stable)
    cases += [(3, F(1)), (3, F(2)), (3, F(3)), (3, F(5))]
    ok_all = True
    bad = None
    for (n, N) in cases:
        G = gram_matrix(n, N)
        W = pinv_symmetric(G)
        e1 = mat_eq(mat_mul(mat_mul(G, W), G), G)
        e2 = mat_eq(mat_mul(mat_mul(W, G), W), W)
        GW = mat_mul(G, W)
        WG = mat_mul(W, G)
        e3 = mat_eq(mat_T(GW), GW)
        e4 = mat_eq(mat_T(WG), WG)
        if not (e1 and e2 and e3 and e4):
            ok_all = False
            bad = (n, str(N), e1, e2, e3, e4)
            break
    if ok_all:
        report("penrose_pair", True)
    else:
        report("penrose_pair", False,
               "n=%d N=%s GWG=%s WGW=%s GWsym=%s WGsym=%s" % bad)

# ============================================================================
# vanish_below: signed sum  sum_sigma sgn(sigma) Wg(sigma) = 0  for every
# integer 1 <= N < n.  Wg(sigma) = W[id_row][col(sigma)] (first row of the
# class-function pseudo-inverse: Wg(sigma) is the W-value at sigma).
# Computed via the independently-built pseudo-inverse.
# ============================================================================

def wg_row(n, N):
    """Return dict sigma -> Wg(sigma) from the pseudo-inverse.
    W is a class function W(a,b)=w(a^{-1}b); read off the identity row:
    W[id][b] = w(b)."""
    S = perms(n)
    G = gram_matrix(n, N)
    W = pinv_symmetric(G)
    i0 = S.index(ident(n))
    return {b: W[i0][S.index(b)] for b in S}

def check_vanish_below():
    ok_all = True
    detail = ""
    sizes = [2, 3, 4]
    for n in sizes:
        for N in range(1, n):           # integer 1 <= N < n
            wg = wg_row(n, F(N))
            s = sum(sgn(b) * v for b, v in wg.items())
            if s != 0:
                ok_all = False
                detail = "n=%d N=%d signed-sum=%s" % (n, N, s)
                break
        if not ok_all:
            break
    report("vanish_below", ok_all, detail)

# ============================================================================
# sign_breakdown: below threshold the STRICT parity pattern
#     0 < (-1)^{n - c(sigma)} Wg(sigma)   for all sigma
# CANNOT hold.  Exhibit a concrete violation: a sigma whose
# (-1)^{|sigma|} Wg(sigma) <= 0.  (At (2,3): transpositions have positive Wg
# yet sign -1, so (-1)^{|sigma|} Wg = (-1)*positive < 0.)
# Independent: derived from the pseudo-inverse, then checked against the
# parity predicate.
# ============================================================================

def check_sign_breakdown():
    # use (N,n)=(2,3): canonical below-threshold cell
    n, N = 3, F(2)
    wg = wg_row(n, N)
    # the strict pattern would require every term strictly positive;
    # find a concrete violator
    violator = None
    for s, v in wg.items():
        term = (F(-1) ** ((n - cyc(s)) % 2)) * v
        if not (term > 0):
            violator = (s, term, v)
            break
    # also confirm the signed sum is exactly 0 (so pattern is impossible),
    # AND that at least one term is strictly positive (nonempty positive part)
    signed = sum(sgn(s) * v for s, v in wg.items())
    has_pos = any((F(-1) ** ((n - cyc(s)) % 2)) * v > 0 for s, v in wg.items())
    ok = (violator is not None) and (signed == 0) and has_pos
    if ok:
        report("sign_breakdown", True)
    else:
        report("sign_breakdown", False,
               "violator=%s signed_sum=%s has_pos=%s" % (violator, signed, has_pos))

# ============================================================================
# cell_23: reproduce the certified (N,n)=(2,3) pseudo-inverse cell values
#   w(id) = 17/144, w(transposition) = 1/144, w(3-cycle) = -7/144
# and average sign sum(w)/sum|w| = 3/17, by EXACT pseudo-inverse computation.
# Anchor: those exact values (from the Lean file -- used ONLY as the target to
# match, never to build W).
# ============================================================================

def check_cell_23():
    n, N = 3, F(2)
    wg = wg_row(n, N)
    expect = {}
    for s in perms(n):
        if s == ident(n):
            expect[s] = F(17, 144)
        elif sgn(s) == -1:           # transposition
            expect[s] = F(1, 144)
        else:                        # 3-cycle
            expect[s] = F(-7, 144)
    val_ok = (wg == expect)
    # average sign anchor 3/17
    total = sum(wg.values())
    absS = sum(abs(v) for v in wg.values())
    avg = total / absS
    avg_ok = (avg == F(3, 17))
    # rising value anchor: sum w = 1/24
    rise_ok = (total == F(1, 24))
    ok = val_ok and avg_ok and rise_ok
    if ok:
        report("cell_23", True)
    else:
        report("cell_23", False,
               "values_match=%s avg=%s(want 3/17) sum=%s(want 1/24)"
               % (val_ok, avg, total))

# ============================================================================
# Extra independent guard (not a Lean theorem on its own, but strengthens the
# pseudo-inverse construction's credibility): cross-check the STABLE-range
# pseudo-inverse against the genuine matrix inverse where G is nonsingular.
# Two genuinely independent computations: pinv_symmetric vs full inv_mat.
# ============================================================================

def check_pinv_vs_inverse_stable():
    ok_all = True
    detail = ""
    for (n, N) in [(2, F(3)), (2, F(5)), (3, F(4)), (3, F(7)), (3, F(10))]:
        G = gram_matrix(n, N)
        if rank(G) != len(G):
            ok_all = False
            detail = "G unexpectedly singular n=%d N=%s" % (n, N)
            break
        W_pinv = pinv_symmetric(G)
        W_inv = inv_mat(G)
        if W_pinv != W_inv:
            ok_all = False
            detail = "pinv != inverse n=%d N=%s" % (n, N)
            break
    report("pinv_eq_inverse_stable", ok_all, detail)

# ============================================================================
# run
# ============================================================================

if __name__ == "__main__":
    check_penrose_pair()
    check_vanish_below()
    check_sign_breakdown()
    check_cell_23()
    check_pinv_vs_inverse_stable()
    print()
    if FAILURES:
        print("%d FAILURE(S): %s" % (len(FAILURES), ", ".join(FAILURES)))
        sys.exit(1)
    print("ALL BELOW-THRESHOLD CHECKS PASSED")
    sys.exit(0)
