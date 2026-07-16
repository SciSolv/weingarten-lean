#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Independent exact-arithmetic cross-check of the symplectic Gram development.

Standard library only (fractions.Fraction, itertools). NO floats/numpy/sympy.

Every check compares two GENUINELY INDEPENDENT computations: a brute-force
enumeration (sum over index assignments, or a direct crossing count) against the
closed formula proved in Weingarten/SymplecticGram.lean. Parameter-polynomial
identities are pinned by evaluating both sides at >= deg+2 distinct integers.

Conventions, read off the Lean sources (must match exactly):
  Pairing n         : fixed-point-free involution on {0..2n-1}.
  loops(p,q)        : cycleCount(p o q)/2, cycleCount counting ALL cycles
                      (Pairing.loops, def:loops).
  crossings(p)      : # ordered pairs (a,c) with a<p(a), c<p(c), a<c<p(a)<p(c)
                      (Pairing.crossings, def:crossings).
  eps(p)            : (-1)^crossings(p)            (epsSign, def:eps_sign).
  Jform M           : on {0..2M-1}, J(x,y)=+1 if y=x+M, -1 if x=y+M, else 0
                      (def:j_form).
  deltaContr(M,p,i) : prod over canonical chords (a,p(a)) with a<p(a) of
                      J(i(a), i(p(a)))                (def:delta_contr).
  sympGramContr     : sum_{i:{0..2n-1}->{0..2M-1}} deltaContr(p,i)*deltaContr(q,i)
                      (def:symp_gram_contr).
  sympGramClosed    : eps(p) eps(q) (-1)^n (-2M)^loops(p,q)  (def:symp_gram_closed).
  evenFalling(M,n)  : prod_{j<n} (2M - 2j)  =  2M(2M-2)...(2M-2n+2).
  risingShift(M,n)  : prod_{j<n} (2M + j)   =  2M(2M+1)...(2M+n-1).
  qStarFun(p,q)     : on Pairing(n+1) with p(0) != q(0); see def in SymplecticGram.lean.
  flipExp(p,q)      : 0 if (p(0) < q(p(0)) <-> q(0) < q(p(0))) else 1  (def flipExp).
"""

from fractions import Fraction
from itertools import product
import sys

FAILURES = []

def check(name, ok, detail=""):
    if ok:
        print("PASS " + name)
    else:
        print("FAIL " + name + ": " + detail)
        FAILURES.append(name)

# ---------------------------------------------------------------------------
# Pair-partition enumeration on {0..2n-1}
# ---------------------------------------------------------------------------

def pair_partitions(twon):
    """All fixed-point-free involutions of {0..twon-1}, as tuples p with p[x]=partner."""
    pts = list(range(twon))
    def rec(rem):
        if not rem:
            yield {}
            return
        a = rem[0]
        for k in range(1, len(rem)):
            b = rem[k]
            rest = rem[1:k] + rem[k+1:]
            for m in rec(rest):
                m2 = dict(m); m2[a] = b; m2[b] = a
                yield m2
    for m in rec(pts):
        p = [0]*twon
        for x in range(twon):
            p[x] = m[x]
        yield tuple(p)

def cycle_count(perm):
    """Number of cycles (incl. fixed points) of a permutation given as tuple perm[x]=img."""
    n = len(perm)
    seen = [False]*n
    c = 0
    for x in range(n):
        if not seen[x]:
            c += 1
            y = x
            while not seen[y]:
                seen[y] = True
                y = perm[y]
    return c

def compose(p, q):
    """(p o q)[x] = p[q[x]] — matches Lean p.1 * q.1 acting as (p*q) x = p (q x)."""
    return tuple(p[q[x]] for x in range(len(q)))

def loops(p, q):
    return cycle_count(compose(p, q)) // 2

def crossings(p):
    twon = len(p)
    cnt = 0
    for a in range(twon):
        if not (a < p[a]):
            continue
        for c in range(twon):
            if not (c < p[c]):
                continue
            if a < c and c < p[a] and p[a] < p[c]:
                cnt += 1
    return cnt

def eps(p):
    return -1 if (crossings(p) % 2) else 1

# ---------------------------------------------------------------------------
# Jform and the canonical contraction (brute force, fully independent of formula)
# ---------------------------------------------------------------------------

def Jform(M, x, y):
    if y == x + M:
        return 1
    if x == y + M:
        return -1
    return 0

def delta_contr(M, p, i):
    """prod over canonical chords (a,p[a]) with a<p[a] of J(i[a], i[p[a]])."""
    prod = 1
    twon = len(p)
    for a in range(twon):
        if a < p[a]:
            prod *= Jform(M, i[a], i[p[a]])
            if prod == 0:
                return 0
    return prod

def symp_gram_contr(M, n, p, q):
    """Brute-force sum_{i:{0..2n-1}->{0..2M-1}} deltaContr(p,i)*deltaContr(q,i)."""
    twon = 2*n
    dim = 2*M
    total = 0
    for i in product(range(dim), repeat=twon):
        dp = delta_contr(M, p, i)
        if dp == 0:
            continue
        dq = delta_contr(M, q, i)
        if dq == 0:
            continue
        total += dp*dq
    return total

def symp_gram_closed(M, n, p, q):
    return eps(p)*eps(q)*((-1)**n)*((-2*M)**loops(p, q))

# ---------------------------------------------------------------------------
# Check 1: symp_gram_entry  (brute J-contraction vs closed formula)
# ---------------------------------------------------------------------------

def check_symp_gram_entry():
    # 2n in {4,6}; 2n=8 is feasible for small M only -> include M=1 there.
    cases = [
        (2, [1, 2]),   # n=2 (2n=4): M values 1,2
        (3, [1, 2]),   # n=3 (2n=6): M values 1,2
    ]
    bad = None
    for n, Ms in cases:
        parts = list(pair_partitions(2*n))
        for M in Ms:
            for p in parts:
                for q in parts:
                    lhs = symp_gram_contr(M, n, p, q)
                    rhs = symp_gram_closed(M, n, p, q)
                    if lhs != rhs:
                        bad = "n=%d M=%d p=%s q=%s lhs=%s rhs=%s" % (n, M, p, q, lhs, rhs)
                        break
                if bad: break
            if bad: break
        if bad: break
    # 2n=8 feasible subset: n=4, M=1 (dim 2). Brute over 2^8=256 indices per pairing pair.
    if not bad:
        n = 4; M = 1
        parts8 = list(pair_partitions(2*n))
        # 105 pairings -> 105^2 ~ 11025 pairs * 256 indices: fine.
        for p in parts8:
            for q in parts8:
                lhs = symp_gram_contr(M, n, p, q)
                rhs = symp_gram_closed(M, n, p, q)
                if lhs != rhs:
                    bad = "n=4 M=1 p=%s q=%s lhs=%s rhs=%s" % (p, q, lhs, rhs)
                    break
            if bad: break
    check("symp_gram_entry", bad is None,
          (bad or "") + "  (2n=4,6 for M in {1,2}; 2n=8 for M=1)")

# ---------------------------------------------------------------------------
# Check 2: crossing_parity
#   eps(p) = (-1)^crossings is the sign relating the canonical contraction to an
#   even-permutation representative.  Independent computation: build the canonical
#   interleaving word w_p (a permutation of {0..2n-1}) listing, in chord order, the
#   left endpoint then its partner; eps(p) must equal sign(w_p).  sign computed by
#   the parity of the permutation (cycle decomposition) -- wholly independent of
#   the crossing count.
# ---------------------------------------------------------------------------

def perm_sign(perm):
    """Sign of a permutation tuple via parity of (n - #cycles)."""
    n = len(perm)
    return -1 if ((n - cycle_count(perm)) % 2) else 1

def canonical_word(p):
    """w_p : position -> point. Left endpoints a_0<a_1<...; word lists (a_k, p[a_k]).
    Returns tuple where index 2k -> a_k, index 2k+1 -> p[a_k]."""
    twon = len(p)
    lefts = sorted(a for a in range(twon) if a < p[a])
    w = []
    for a in lefts:
        w.append(a)
        w.append(p[a])
    return tuple(w)

def check_crossing_parity():
    bad = None
    for n in (2, 3, 4):
        for p in pair_partitions(2*n):
            w = canonical_word(p)
            s = perm_sign(w)
            if s != eps(p):
                bad = "n=%d p=%s sign(word)=%d eps=%d" % (n, p, s, eps(p))
                break
        if bad: break
    check("crossing_parity", bad is None, bad or "  (2n=4,6,8: sign(canonicalWord)=eps)")

# ---------------------------------------------------------------------------
# Check 3: eps_ones_absorb
#   (sympGramClosed).mulVec(eps) = evenFalling(M,n) * eps, i.e. for every p:
#       sum_q sympGramClosed(p,q) eps(q) = evenFalling(M,n) eps(p).
#   Independent: LHS uses the closed Gram + eps enumeration; RHS uses the falling
#   product 2M(2M-2)...(2M-2n+2).  Also check the eigenvalue 2M(2M-2)..(2M-2n+2)
#   and its vanishing for integer M < n.
#   Polynomial in M of degree n -> verify the row-identity at n+2 distinct M.
# ---------------------------------------------------------------------------

def even_falling(M, n):
    prod = 1
    for j in range(n):
        prod *= (2*M - 2*j)
    return prod

def check_eps_ones_absorb():
    bad = None
    for n in (1, 2, 3):
        parts = list(pair_partitions(2*n))
        # pin the degree-n polynomial in M at n+2 distinct integer values
        for M in range(1, n+3):
            ev = even_falling(M, n)
            for p in parts:
                lhs = sum(symp_gram_closed(M, n, p, q)*eps(q) for q in parts)
                rhs = ev*eps(p)
                if lhs != rhs:
                    bad = "n=%d M=%d p=%s lhs=%s rhs=%s" % (n, M, p, lhs, rhs)
                    break
            if bad: break
        if bad: break
    # vanishing for integer M < n: even_falling(M,n)=0
    vanish_ok = all(even_falling(M, n) == 0
                    for n in (1, 2, 3, 4) for M in range(0, n))
    nonvanish_ok = all(even_falling(M, n) != 0
                       for n in (1, 2, 3, 4) for M in range(n, n+4))
    check("eps_ones_absorb", bad is None and vanish_ok and nonvanish_ok,
          (bad or "")
          + ("" if vanish_ok else " evenFalling did not vanish for some M<n")
          + ("" if nonvanish_ok else " evenFalling vanished for some M>=n")
          + "  (eigenvalue 2M(2M-2)..(2M-2n+2), pinned at n+2 M-values)")

# ---------------------------------------------------------------------------
# Check 4: eps_det_absorb
#   (sympGramClosed).mulVec(epsDetVec) = risingShift(M,n) * epsDetVec, with
#   epsDetVec(p) = eps(p) * detVec(p), detVec the signed permutation indicator:
#   detVec(qPair rho) = sign(rho), 0 on non-permutation-type pairings.
#   Independent: LHS = closed Gram applied to the enumerated epsDetVec; RHS uses
#   the rising product 2M(2M+1)...(2M+n-1).  Degree-n poly in M -> n+2 points.
# ---------------------------------------------------------------------------

def qpair(rho):
    """Pairing on {0..2n-1} pairing a <-> n+rho(a).  rho is a tuple perm of {0..n-1}."""
    n = len(rho)
    p = [0]*(2*n)
    for a in range(n):
        b = n + rho[a]
        p[a] = b
        p[b] = a
    return tuple(p)

def all_perms(n):
    from itertools import permutations
    return list(permutations(range(n)))

def det_vec(p):
    """sign(rho) if p == qPair(rho) for some rho, else 0.  qPair is injective."""
    n = len(p)//2
    for rho in all_perms(n):
        if qpair(rho) == p:
            return perm_sign(rho)
    return 0

def eps_det_vec(p):
    return eps(p)*det_vec(p)

def rising_shift(M, n):
    prod = 1
    for j in range(n):
        prod *= (2*M + j)
    return prod

def check_eps_det_absorb():
    bad = None
    for n in (1, 2, 3):
        parts = list(pair_partitions(2*n))
        for M in range(1, n+3):  # n+2 distinct values >=1
            rs = rising_shift(M, n)
            for p in parts:
                lhs = sum(symp_gram_closed(M, n, p, q)*eps_det_vec(q) for q in parts)
                rhs = rs*eps_det_vec(p)
                if lhs != rhs:
                    bad = "n=%d M=%d p=%s lhs=%s rhs=%s" % (n, M, p, lhs, rhs)
                    break
            if bad: break
        if bad: break
    nonzero_ok = all(rising_shift(M, n) != 0
                     for n in (1, 2, 3, 4) for M in range(1, 6))
    check("eps_det_absorb", bad is None and nonzero_ok,
          (bad or "")
          + ("" if nonzero_ok else " risingShift vanished for some M>=1")
          + "  (eigenvalue 2M(2M+1)..(2M+n-1), pinned at n+2 M-values)")

# ---------------------------------------------------------------------------
# Check 5: qStar_sign
#   qStar.crossings = q.crossings + 1 + flipExp  (mod 2), for every admissible
#   (p,q) in Pairing(n+1) with p(0) != q(0).
#   qStarFun(p,q)(v): 0->p(0), p(0)->0, q(0)->q(p(0)), q(p(0))->q(0), else q(v).
#   flipExp = 0 if (p(0)<q(p(0)) <-> q(0)<q(p(0))) else 1.
#   Brute force over all pairs; both sides computed independently (qStar's own
#   crossing count vs q's crossing count + parity correction).
# ---------------------------------------------------------------------------

def qstar(p, q):
    twon = len(p)
    b = p[0]; c = q[0]; d = q[b]
    out = [0]*twon
    for v in range(twon):
        if v == 0:
            out[v] = b
        elif v == b:
            out[v] = 0
        elif v == c:
            out[v] = d
        elif v == d:
            out[v] = c
        else:
            out[v] = q[v]
    return tuple(out)

def flip_exp(p, q):
    b = p[0]; c = q[0]; d = q[b]
    cond = ((b < d) == (c < d))
    return 0 if cond else 1

def check_qStar_sign():
    bad = None
    for nn in (1, 2, 3):           # Pairing(n+1) with n+1 = nn  -> 2*(nn) points
        twon = 2*nn
        parts = list(pair_partitions(twon))
        for p in parts:
            for q in parts:
                if p[0] == q[0]:
                    continue
                qs = qstar(p, q)
                # sanity: qStar is a fixed-point-free involution
                if any(qs[qs[v]] != v or qs[v] == v for v in range(twon)):
                    bad = "qStar not fpf-involution: nn=%d p=%s q=%s qs=%s" % (nn, p, q, qs)
                    break
                lhs = crossings(qs) % 2
                rhs = (crossings(q) + 1 + flip_exp(p, q)) % 2
                if lhs != rhs:
                    bad = "nn=%d p=%s q=%s qsCr=%d qCr=%d flip=%d" % (
                        nn, p, q, crossings(qs), crossings(q), flip_exp(p, q))
                    break
            if bad: break
        if bad: break
    check("qStar_sign", bad is None,
          (bad or "") + "  (Pairing(n+1), 2(n+1)=2,4,6; qStar.cr = q.cr+1+flipExp mod 2)")

# ---------------------------------------------------------------------------
# (sanity, not a separate ledger line) loops symmetry / eps^2=1 underpin above.
# ---------------------------------------------------------------------------

def main():
    check_symp_gram_entry()
    check_crossing_parity()
    check_eps_ones_absorb()
    check_eps_det_absorb()
    check_qStar_sign()
    if FAILURES:
        print("\n%d FAILURE(S): %s" % (len(FAILURES), ", ".join(FAILURES)))
        sys.exit(1)
    print("\nALL CHECKS PASS")
    sys.exit(0)

if __name__ == "__main__":
    main()
