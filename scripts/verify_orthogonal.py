#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Independent exact-arithmetic cross-check of the orthogonal-Gram theorems.

This is NOT a re-proof. Every check pits two genuinely independent computations
against each other (brute-force enumeration over pair partitions vs. a closed
formula, or matrix inversion vs. a sign sum). Exact rationals only
(fractions.Fraction), stdlib only. No floats, no numpy, no sympy.

Project conventions (matched against Weingarten/Pairings.lean and
Weingarten/OrthogonalGram.lean):

  * A pairing of {0,..,2n-1} is a perfect matching (fixed-point-free involution).
  * loops(p,q) = cycleCount(p o q) / 2, where p,q are the involution permutations
    and cycleCount counts ALL cycles of the product (fixed points included).
    Here, with both p,q involutions over the SAME ground set, we compute
    connected components of the overlay graph p u q by union-find -- which equals
    cycleCount(p o q)/2 for two perfect matchings.
  * orthGram GO(p,q) = N^loops(p,q); diagonal GO(p,p) = N^n.
  * evenRising  N(N+2)...(N+2n-2) = prod_{j<n}(N+2j).
  * fallingFact N(N-1)...(N-n+1) = prod_{j<n}(N-j).
  * qPair rho pairs lower-half a (0..n-1) with upper-half n+rho(a).
  * detVec (alternating vector v) is supported on the qPair pairings with weight
    sgn(rho).

Checks (exhaustive over pair partitions up to the stated bound):

  orth_gram_entry    GO(p,q) = N^loops(p,q) for 2n=4,6,8, with loops computed
                     independently by union-find on the overlay graph; diagonal
                     must be N^n.
  ones_absorb        GO . 1 = lambda . 1, lambda = even-rising factorial,
                     by exact matrix-vector product, 2n=4,6,8,10, several N.
  alt_absorb         GO . v = mu . v, mu = falling factorial, v the alternating
                     vector on qPair, 2n=4,6,8.
  orth_vanish_below  sum_rho sgn(rho) WgO(q_id, q_rho) = 0 for integer
                     1 <= N <= k-1, via the Moore-Penrose pseudo-inverse of GO.

Prints exactly one "PASS <name>" / "FAIL <name>: <detail>" line per theorem.
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
# Pair partitions (perfect matchings) of {0,..,2n-1}
# ---------------------------------------------------------------------------

def pair_partitions(twon):
    """Yield every perfect matching of range(twon) as a tuple of frozenset pairs,
    canonicalized: sorted list of sorted 2-tuples. Recursive enumeration."""
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

def matching_to_involution(matching, twon):
    """Perfect matching -> involution permutation as a tuple p with p[x] = partner(x)."""
    p = [0] * twon
    for a, b in matching:
        p[a] = b
        p[b] = a
    return tuple(p)

# ---------------------------------------------------------------------------
# loops via union-find on the overlay graph (INDEPENDENT of any cycleCount code)
# ---------------------------------------------------------------------------

def loops_unionfind(p_match, q_match, twon):
    """Number of connected components (loops) when matchings p and q are overlaid.
    Each loop alternates p- and q-edges; #loops = (#components of the union of the
    two matchings' edge sets). Computed with a fresh union-find -- no permutation
    composition, no cycleCount."""
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
    roots = {find(x) for x in range(twon)}
    return len(roots)

def loops_via_product(p_perm, q_perm, twon):
    """Second, independent loops computation: count cycles of the product
    permutation p o q (as functions x -> p[q[x]]) and halve. This is a DIFFERENT
    construction (permutation cycle decomposition) used only to cross-check the
    union-find loops, never to define the Gram on both sides."""
    prod = tuple(p_perm[q_perm[x]] for x in range(twon))
    seen = [False] * twon
    c = 0
    for x in range(twon):
        if not seen[x]:
            c += 1
            y = x
            while not seen[y]:
                seen[y] = True
                y = prod[y]
    assert c % 2 == 0, "cycle count of product of two matchings must be even"
    return c // 2

# ---------------------------------------------------------------------------
# Permutation helpers (over the SMALL symmetric group S_k used for qPair)
# ---------------------------------------------------------------------------

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

def qpair_matching(rho):
    """qPair rho: pairs lower-half a (0..k-1) with upper-half k+rho(a)."""
    k = len(rho)
    return tuple((a, k + rho[a]) for a in range(k))

# ---------------------------------------------------------------------------
# Closed-form eigenvalues (the "formula" side -- independent of the Gram entries)
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
# Exact linear algebra over Q (for the pseudo-inverse check)
# ---------------------------------------------------------------------------

def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)]
            for i in range(n)]

def mat_T(A):
    return [list(col) for col in zip(*A)]

def identity_mat(n):
    return [[Fraction(1) if i == j else Fraction(0) for j in range(n)]
            for i in range(n)]

def pseudo_inverse(A):
    """Moore-Penrose pseudo-inverse of a real (rational) symmetric matrix A,
    computed independently of any Weingarten formula. Uses A^+ = A (A^3)^{-1} A
    when A^3 is invertible on the column space; here we instead use the robust
    construction via the rank-revealing approach: for symmetric A, restrict to a
    maximal independent set of columns. We implement the general formula
    A^+ = lim, but exactly: use A^+ = V where we solve on column space.

    Simpler exact route for symmetric A: pick a maximal linearly independent set
    of columns C (indices), let B = A[:,C] (full column rank). Then
    A^+ = (B^T B)^{-1} B^T  ... is the pinv of B, and A^+ = R^T (B^+)^T-style.

    To stay fully general and exact we use the SVD-free formula valid for any A:
        A^+ = A^T (A A^T)^+ , recursing; instead we use the closed exact method:
    For symmetric A with A = sum lambda_i P_i, A^+ = sum_{lambda_i != 0} lambda_i^{-1} P_i.
    We obtain it via: choose basis of row space, etc.

    Implementation below: full-rank-factorization A = F G with F (n x r) full
    column rank, G (r x n) full row rank, then
        A^+ = G^T (G G^T)^{-1} (F^T F)^{-1} F^T.
    This is the exact Moore-Penrose pseudo-inverse for ANY matrix over a field
    with an inner product (here the standard rational inner product)."""
    n = len(A)
    # Full-rank factorization via reduced row echelon form.
    F, G = full_rank_factorization(A)
    r = len(G)
    if r == 0:
        return [[Fraction(0)] * n for _ in range(n)]
    Ft = mat_T(F)
    Gt = mat_T(G)
    FtF = mat_mul(Ft, F)          # r x r, invertible
    GGt = mat_mul(G, Gt)          # r x r, invertible
    FtF_inv = mat_inv(FtF)
    GGt_inv = mat_inv(GGt)
    # A^+ = G^T (G G^T)^{-1} (F^T F)^{-1} F^T
    return mat_mul(Gt, mat_mul(GGt_inv, mat_mul(FtF_inv, Ft)))

def full_rank_factorization(A):
    """Return (F, G) with A = F G, F = independent columns of A (n x r),
    G = r x n matrix expressing all columns in that basis (rows = RREF nonzero
    rows of the coefficient encoding). Built from RREF of A."""
    n = len(A)
    R, pivots = rref(A)
    r = len(pivots)
    # F: the pivot columns of the ORIGINAL A.
    F = [[A[i][pc] for pc in pivots] for i in range(n)]
    # G: the nonzero rows of the RREF (each is a column-combination row).
    G = [R[i][:] for i in range(r)]
    return F, G

def rref(A):
    """Reduced row echelon form over Q. Returns (R, pivot_columns)."""
    M = [row[:] for row in A]
    rows = len(M)
    cols = len(M[0]) if rows else 0
    pivots = []
    pr = 0
    for pc in range(cols):
        # find pivot
        sel = None
        for r in range(pr, rows):
            if M[r][pc] != 0:
                sel = r
                break
        if sel is None:
            continue
        M[pr], M[sel] = M[sel], M[pr]
        pv = M[pr][pc]
        M[pr] = [x / pv for x in M[pr]]
        for r in range(rows):
            if r != pr and M[r][pc] != 0:
                f = M[r][pc]
                M[r] = [a - f * b for a, b in zip(M[r], M[pr])]
        pivots.append(pc)
        pr += 1
        if pr == rows:
            break
    return M[:pr], pivots

def mat_inv(A):
    """Exact inverse of a square invertible matrix over Q."""
    n = len(A)
    M = [A[i][:] + [Fraction(1) if i == j else Fraction(0) for j in range(n)]
         for i in range(n)]
    for c in range(n):
        sel = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[sel] = M[sel], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [row[n:] for row in M]

# ===========================================================================
# CHECK 1: orth_gram_entry  --  GO(p,q) = N^loops(p,q), loops by union-find.
# Independent sides: LEFT = N**loops_unionfind (graph components);
# the union-find result is itself cross-checked against the permutation-product
# cycle count (a second, distinct construction). Diagonal must be N**n.
# ===========================================================================

def check_orth_gram_entry():
    ok = True
    detail = ""
    for twon in (4, 6, 8):
        n = twon // 2
        parts = list(pair_partitions(twon))
        invs = [matching_to_involution(m, twon) for m in parts]
        for i, mp in enumerate(parts):
            for j, mq in enumerate(parts):
                L_uf = loops_unionfind(mp, mq, twon)
                L_pr = loops_via_product(invs[i], invs[j], twon)
                if L_uf != L_pr:
                    ok = False
                    detail = ("2n=%d loops mismatch uf=%d prod=%d"
                              % (twon, L_uf, L_pr))
                    return ok, detail
                # Two genuinely independent loop computations must agree for
                # every (p,q): union-find on the overlaid edge sets vs. cycle
                # decomposition of the permutation product p o q (halved). That
                # agreement IS the Gram-entry content, since GO(p,q) = N^loops.
            # diagonal: overlay of p with itself => n loops (each chord its own).
            if loops_unionfind(mp, mp, twon) != n:
                ok = False
                detail = "2n=%d diagonal loops != n" % twon
                return ok, detail
    return ok, detail

# ===========================================================================
# CHECK 2: ones_absorb  --  GO . 1 = even-rising . 1.
# LEFT  (brute): for each row p, sum over q of N^loops(p,q) by union-find.
# RIGHT (formula): even-rising factorial N(N+2)...(N+2n-2), built independently.
# Polynomial in N of degree n; we test several integer N >> n to over-determine.
# ===========================================================================

def check_ones_absorb():
    for twon in (4, 6, 8, 10):
        n = twon // 2
        parts = list(pair_partitions(twon))
        # loops matrix (integers) computed once by union-find.
        loops_mat = [[loops_unionfind(p, q, twon) for q in parts] for p in parts]
        for Nv in (Fraction(-3), Fraction(0), Fraction(1), Fraction(2),
                   Fraction(5), Fraction(7), Fraction(13)):
            lam = even_rising(n, Nv)            # independent closed form
            # anchor: 2n=4 eigenvalue is literally N(N+2) (hand-written, not the loop)
            if twon == 4 and lam != Nv * (Nv + 2):
                return False, "anchor 2n=4: evenRising != N(N+2)"
            for r, row in enumerate(loops_mat):
                rowsum = sum(Nv ** L for L in row)   # brute matrix-vector
                if rowsum != lam:
                    return False, ("2n=%d N=%s row %d sum=%s != evenRising=%s"
                                   % (twon, Nv, r, rowsum, lam))
    return True, ""

# ===========================================================================
# CHECK 3: alt_absorb  --  GO . v = falling . v, v = alternating vector on qPair.
# LEFT  (brute): (GO v)(p) = sum_q N^loops(p,q) v(q), v supported on qPair rho
#                with weight sgn(rho); loops by union-find.
# RIGHT (formula): falling-factorial * v(p), falling built independently.
# Verified at every pairing p (both qPair rows and non-qPair rows, where v=0 and
# the signed loop-sum must vanish), for several integer N over-determining the
# degree-n polynomial identity.
# ===========================================================================

def check_alt_absorb():
    for twon in (4, 6, 8):
        n = twon // 2
        parts = list(pair_partitions(twon))
        index = {m: i for i, m in enumerate(parts)}
        # alternating vector v over all pairings
        v = [Fraction(0)] * len(parts)
        for rho in permutations(range(n)):
            m = qpair_matching(rho)
            v[index[m]] = Fraction(perm_sgn(rho))
        loops_mat = [[loops_unionfind(p, q, twon) for q in parts] for p in parts]
        for Nv in (Fraction(-2), Fraction(0), Fraction(1), Fraction(2),
                   Fraction(3), Fraction(6), Fraction(11)):
            mu = falling_fact(n, Nv)            # independent closed form
            # anchor: n=2 eigenvalue is literally N(N-1) (hand-written)
            if n == 2 and mu != Nv * (Nv - 1):
                return False, "anchor n=2: fallingFact != N(N-1)"
            for pi in range(len(parts)):
                lhs = sum((Nv ** loops_mat[pi][qi]) * v[qi]
                          for qi in range(len(parts)))
                rhs = mu * v[pi]
                if lhs != rhs:
                    return False, ("2n=%d N=%s p=%d lhs=%s rhs=%s"
                                   % (twon, Nv, pi, lhs, rhs))
    return True, ""

# ===========================================================================
# CHECK 4: orth_vanish_below  --  sum_rho sgn(rho) WgO(q_id, q_rho) = 0
# for integer 1 <= N <= k-1 (where fallingFact(k,N) = 0).
# WgO is the Moore-Penrose pseudo-inverse of GO, built by full-rank
# factorization + exact inverses (independent of any Weingarten closed form).
# The row q_id is selected; we sum its qPair entries weighted by sgn(rho).
# As an independent sanity anchor we also verify WgO satisfies the Penrose
# relations GWG=G, WGW=W and is symmetric.
# ===========================================================================

def check_orth_vanish_below():
    for k in (2, 3):                 # 2n = 2k = 4, 6
        twon = 2 * k
        parts = list(pair_partitions(twon))
        index = {m: i for i, m in enumerate(parts)}
        loops_mat = [[loops_unionfind(p, q, twon) for q in parts] for p in parts]
        id_perm = tuple(range(k))
        id_match = qpair_matching(id_perm)
        i_id = index[id_match]
        # qPair indices and signs
        qrows = []
        for rho in permutations(range(k)):
            qrows.append((index[qpair_matching(rho)], perm_sgn(rho)))
        for Nint in range(1, k):     # 1 <= N <= k-1 : fallingFact vanishes
            Nv = Fraction(Nint)
            GO = [[Nv ** loops_mat[p][q] for q in range(len(parts))]
                  for p in range(len(parts))]
            W = pseudo_inverse(GO)
            # independent Penrose sanity (pseudo-inverse correctness)
            GWG = mat_mul(mat_mul(GO, W), GO)
            WGW = mat_mul(mat_mul(W, GO), W)
            if GWG != GO:
                return False, "k=%d N=%d GWG != G" % (k, Nint)
            if WGW != W:
                return False, "k=%d N=%d WGW != W" % (k, Nint)
            if mat_T(W) != W:
                return False, "k=%d N=%d W not symmetric" % (k, Nint)
            # the signed sum over rho of WgO(q_id, q_rho)
            s = sum(sgn * W[i_id][qi] for (qi, sgn) in qrows)
            if s != 0:
                return False, ("k=%d N=%d signed pinv sum=%s != 0"
                               % (k, Nint, s))
    return True, ""

# ===========================================================================

def main():
    report("orth_gram_entry", *check_orth_gram_entry())
    report("ones_absorb", *check_ones_absorb())
    report("alt_absorb", *check_alt_absorb())
    report("orth_vanish_below", *check_orth_vanish_below())
    if FAILS:
        sys.exit(1)
    sys.exit(0)

if __name__ == "__main__":
    main()
