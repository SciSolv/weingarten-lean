# Independent verification ledger

These scripts **do not prove** anything — the Lean development is the proof, and is
`sorry`-free and axiom-clean (`#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`). What they add is an
**independent** check: each formalized computational theorem is recomputed from
scratch in **exact rational arithmetic** (Python standard library only —
`fractions.Fraction`, `itertools`; no floats/numpy/sympy) and compared against a
second, **genuinely independent** computation, **exhaustively over all cases up to a
size bound**. Every check pits two unrelated computations against each other; none
compares a value to itself.

Run everything:

```
python scripts/verify_all.py
```

Each `verify_<package>.py` prints one `PASS <theorem>` line per theorem below.

## Unitary spine — `verify_unitary.py`

| Theorem (Lean / blueprint) | Independent check | Bound | Status |
|---|---|---|---|
| `jucys` (`gram_eq_prod`, thm:jucys) | brute `S_n` enumeration `Σ N^c(σ)·σ` vs. group-algebra product `∏(N+K_i)` | `n=1..5`, ≥`n+5` values of `N` | PASS |
| `rising_sum` (`aug_gram`, lem:gram_eval; consumed by thm:rising) | brute `Σ N^c(σ)` vs. rising factorial `∏(N+j)` | `n=1..7` | PASS |
| `falling_sum` (`sgnHom_gram`, lem:gram_eval; consumed by thm:falling) | brute `Σ sgn(σ)N^c(σ)` vs. falling factorial `∏(N−j)` | `n=1..7` | PASS |
| `sign_pattern` (`wg_sign`, thm:parity) | exact Gauss–Jordan inverse of the `n!×n!` Gram vs. `sgn(σ)` from cycle structure | `n=2..5`, `N=n..n+3` | PASS |
| `closed_form` (`cancellation_ratio`, thm:closed_form) | sums read off the exact Gram inverse vs. closed products `∏1/(N±m)`, `∏(N−j)/(N+j)` | `n=2..5`, `N=n..n+3` | PASS |

## Below threshold — `verify_below.py`

| Theorem | Independent check | Bound | Status |
|---|---|---|---|
| `penrose_pair` | independently built pseudo-inverse (column-space compression) satisfies `GWG=G`, `WGW=W`, `(GW)ᵀ=GW`, `(WG)ᵀ=WG` | `n=2,3` incl. below-threshold `N` | PASS |
| `vanish_below` | `Σ sgn(σ)Wg(σ,N)=0` via the exact pseudo-inverse | `n=2,3,4`, every integer `1≤N<n` | PASS |
| `sign_breakdown` | strict sign pattern exhibited to fail below threshold | `(N,n)=(2,3)` | PASS |
| `cell_23` | exact pseudo-inverse reproduces `17/144, 1/144, −7/144`, avg sign `3/17`, `Σw=1/24` | `(N,n)=(2,3)` | PASS |
| `pinv_eq_inverse_stable` | pseudo-inverse equals genuine inverse on nonsingular Gram (independence guard) | `n=2,3` stable `N` | PASS |

## Orthogonal Gram — `verify_orthogonal.py`

| Theorem | Independent check | Bound | Status |
|---|---|---|---|
| `orth_gram_entry` | `Gᴼ(p,q)=N^loops` with `loops` by union-find on the overlay vs. cycle decomposition of `p∘q` | `2n=4,6,8` (all matchings) | PASS |
| `ones_absorb` (`orthGram_mulVec_one`) | brute row sum vs. even-rising `N(N+2)…(N+2n−2)` | `2n=4,6,8,10` | PASS |
| `alt_absorb` (`orthGram_mulVec_detVec`) | `Gᴼ·v=μ·v`, `v` the alternating vector, vs. falling `N(N−1)…(N−n+1)` | `2n=4,6,8` | PASS |
| `orth_vanish_below` | `Σ sgn(ρ)Wgᴼ(q_id,q_ρ)=0` via independent pseudo-inverse | `k=2,3`, `1≤N≤k−1` | PASS |

## Symplectic Gram — `verify_symplectic.py`

| Theorem | Independent check | Bound | Status |
|---|---|---|---|
| `symp_gram_entry` (`sympGramContr_eq_closed`) | **direct `J`-form contraction** `Σ_i δ(p,i)δ(q,i)` over all index assignments vs. closed `ε(π)ε(σ)(−1)ⁿ(−2M)^loops` | `2n=4,6` (`M=1,2`), `2n=8` (`M=1`) | PASS |
| `crossing_parity` | `ε=(−1)^crossings` vs. `sign(canonicalWord)` by permutation parity | `2n=4,6,8` | PASS |
| `eps_ones_absorb` | ε-twisted all-ones absorption = even-falling `2M(2M−2)…`; vanishes for integer `M<n` | `n=1,2,3` | PASS |
| `eps_det_absorb` | ε-twisted determinant absorption = shifted-rising `2M(2M+1)…(2M+n−1)` | `n=1,2,3` | PASS |
| `qStar_sign` | `crossings(qStar) ≡ crossings(q)+1+flipExp (mod 2)`, both counted independently | Pairing(n+1), `2(n+1)=2,4,6` | PASS |

## Haar bridge — `Weingarten/Haar/`

**Provenance.** The authoritative copy of this layer lives in this
repository; the proofs have been byte-stable since 2026-07-12.

**A new category: anchor-checked only.** The headline theorems below are
general-`N` **measure-theoretic** statements about the Haar expectation on
`U(N)`. There is no finite case list to enumerate, and a general-`N` numeric
check of the integral values would have to compute them *through the
Weingarten formula* — i.e. it would be circular against the very statements
being checked. What exists instead is independent exact coverage **at the
anchors** in the existing suites: the finite Weingarten-side values these
integrals produce are pinned by `verify_unitary.py` (exact Gram inverses,
`n = 1..5`, many `N` including the small-`N` anchors), and the suite family
carries a direct low-rank integration anchor (`PF0` in
`pfaffian_reading_checks.py` — exact `SU(2)` integration; the `U(1)` case is
the `N = 1` specialization of the `n = 1` table, `E|U₁₁|² = 1`). Beyond
those anchors the measure-theoretic content is certified by the Lean kernel
alone: **anchor-checked only**.

| Theorem (Lean, `Weingarten/Haar/`) | Statement | Category |
|---|---|---|
| `haarExpectation` (`HaarConstruction`) | the invariance interface inhabited for all `N` from Mathlib's Haar measure | Lean-only (structural) |
| `integral_entry_mul_star_entry` (`MatrixEntryIntegrals`) | `E[U_ij · conj(U_kl)] = δ_ik δ_jl / N` — the complete `n = 1` table | anchor-checked only |
| `integral_trace`, `integral_trace_mul_star_trace` | `E[Tr U] = 0`; `E|Tr U|² = 1` (`N ≥ 1`) | anchor-checked only |
| `integral_entry_crossed`, `integral_absSq_sq`, … (`EntryIntegralsTwo`) | the `n = 2` fourth-moment table | anchor-checked only |
| `integral_absTrace_pow_four` (`EntryIntegralsTwo`) | `E|Tr U|⁴ = 2` (`N ≥ 2`) | anchor-checked only |
| `wg_one_apply`, `wg_two_one`, `wg_two_swap` (`WeingartenValues`) | `Wg = 1/N` (`n = 1`); `1/(N²−1)`, `−1/(N(N²−1))` (`n = 2`) | exact — already covered by the unitary suite (values implied by the checked sum rules / Gram inverses) |
| `w1_eq` … `w4_eq`, `one_matrix_model_coeffs` (`OneMatrixModel`) | `w₁ = 1/2`, `w₂ = w₃ = w₄ = 0` (`N ≥ 2`) | anchor-checked only |
| `honestZ_pos`, `honestZ_eq_cosh`, `honestLamF_eq_sinh`, `honestLamF_lt_honestZ` (`HonestKernel`) | `Z(β) > 0`, cosh/sinh forms, `λ_F < Z` (`N ≥ 1`) | Lean-only (analytic) |
| `pairHaarExpectation_*`, `productHaar_*` (`PairHaar`, `ProductHaar`) | product-Haar factorization and marginals | Lean-only (structural) |

No new `verify_*.py` suite accompanies this section, by design: the honest
options are an anchor check (already present in the existing suites) or a
circular one (rejected).

## Lean-only (no finite enumerable content)

These are genuinely analytic or structural; there is no finite computation to
enumerate. Where they have a finite numeric *consequence*, that consequence is
exercised above (noted in parentheses).

- **ℓ¹ / Neumann invertibility** in the stable range — Banach-algebra geometric
  series. (Consequence `Wg = exact Gram inverse` is checked by `sign_pattern`,
  `closed_form`.)
- **`tsum` / Cauchy-product expansions** — absolutely-convergent multi-index
  regrouping.
- **Moore–Penrose existence / uniqueness theory** (`penrose_unique`,
  `pseudoinverse_unique`) — a concrete exact pseudo-inverse is exhibited and its
  Penrose equations checked instead (`penrose_pair`, `orth_vanish_below`).
- **Expected-Pfaffian compression** and the **`O(N)`/`Sp(M)` Haar-integral
  readings** — structural / prose-level (incl. the `eps_det` conjecture, a
  `Remark`). The `U(N)` Haar bridge is now in-repo, machine-checked at the
  formalized degrees — see the Haar bridge section above.
