# weingarten-lean

A Lean 4 / Mathlib formalization of the algebraic foundations of **Weingarten calculus** across all three classical series — the unitary group `U(N)`, the orthogonal group `O(N)`, and the symplectic group `Sp(N)` — together with the `U(N)` Haar-integration bridge at the formalized degrees.

Every result here is machine-checked down to the logical axioms. To the best of a careful (but finite) search, this is the first end-to-end, computer-verified account of this foundational layer in any proof assistant.

## Build Instructions

Requires [Lean 4](https://leanprover.github.io/) and [Mathlib](https://github.com/leanprover-community/mathlib4). The pinned versions are:

- **Lean:** `leanprover/lean4:v4.31.0`
- **Mathlib:** commit [`94fba23`](https://github.com/leanprover-community/mathlib4/commit/94fba23a1390006d2c960739fec79a580e947d85) (tracking `master`)

The remaining dependencies (Batteries, Aesop, Qq, ProofWidgets, and others) are pulled in transitively by Mathlib and pinned in `lake-manifest.json`. The one direct non-Mathlib dependency is [`checkdecls`](https://github.com/PatrickMassot/checkdecls), used to audit the declared results.

To build:

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

The exact Mathlib commit is pinned in `lake-manifest.json`, so the build is reproducible. Note that `lake exe cache get` only retrieves prebuilt artifacts while the pinned commit remains in Mathlib's cache; for an older commit the cache may be unavailable, in which case `lake build` will compile Mathlib from source (slow, but produces an identical result).

A clean `lake build` with no errors is a complete verification of every result described below. The development is fully `sorry`-free — no result depends on an unproved assumption — which can be confirmed by running `checkdecls` or by searching the source (`grep -rn sorry`).


## Blueprint

A paper-level write-up of every definition and proof — with the per-node Lean correspondence — is kept under [`docs/`](docs/), so it is available without building the web version:

- **[`docs/blueprint.pdf`](docs/blueprint.pdf)** — the full blueprint as a PDF.
- **[`docs/dependency_graph.pdf`](docs/dependency_graph.pdf)** ([preview](docs/dependency_graph.png)) — the theorem dependency graph (121 nodes, 219 edges); every theorem-class node is Lean-verified (`leanok`) or Mathlib-provided (`mathlibok`) — the five prose remarks carry no proof obligation and are marked as such in the graph legend.

The `blueprint/src/` LaTeX sources are kept intact for the interactive web blueprint (the eventual GitHub Pages target); see [`docs/README.md`](docs/README.md) to regenerate.

## What is Weingarten calculus?

The field answers one question: if you draw a matrix uniformly at random from a classical compact group, how do products of its entries behave *on average*? Concretely, you want quantities like

> the `(i,j)` entry times the conjugate of the `(k,l)` entry times … , averaged over the whole group.

That average is an integral over a curved, high-dimensional space, and is intractable head-on. Weingarten calculus turns it into finite combinatorial bookkeeping over **permutations** (for `U(N)`) or **pairing diagrams** (for `O(N)` and `Sp(N)`).

The pipeline rests on three classical ideas:

- **Schur–Weyl duality.** Permuting the slots of a tensor and rotating it by a group element are dual operations. Averaging over the group projects onto the rotation-invariant part, and that projection is assembled out of permutations — so the combinatorics is forced by the symmetry, not bolted on.
- **The Weingarten function.** Carrying the duality through, each average becomes a sum: for every way of matching indices you get a product of Kronecker deltas times a universal number `Wg(σ, τ, N)`. That number is the inverse of the **Gram matrix** `G`, whose entries are `N^(loops)` — `N` raised to the number of loops formed when two diagrams are overlaid. All the difficulty of the subject lives inside that one matrix inversion.
- **Jucys–Murphy factorization.** The Gram element factors as

  ```
  Gₙ(N) = (N + J₁)(N + J₂) ⋯ (N + Jₙ)
  ```

  where each `Jₖ` is the sum of transpositions swapping `k` with each earlier point. This factorization is the spine that makes clean formulas possible at all. (In the Lean source the factorization is implemented through the equivalent *dual* elements `Kᵢ = Σ_{j>i} (i j)` — a deliberate convention choice, recorded and validated in the blueprint’s design record.)

## What is this project?

This project is a formalization of the algebraic foundations of Weingarten calculus. The mathematics is classical. The contribution here is not new theorems but a reconstruction, inside Lean 4 / Mathlib, of the algebraic core plus the `U(N)` Haar-integration bridge at the formalized degrees, machine-checked down to the logical axioms. (A formal proof certifies that the theorems follow from the definitions; the definitions themselves — the loop count, the crossing parity, the pairing encoding — are stated to match the standard literature, and the references below are where to check that match.) Specifically, the project machine-checks:

- the **Jucys–Murphy factorization** of the Gram element;
- the two **sum rules** obtained by pushing the trivial character and the sign character through that factorization;
- the **sign pattern**: in the stable range (`N ≥ n`), the sign of the Weingarten function is exactly the sign of the permutation;
- a **closed-form ratio** `∏(N−j)/(N+j)` governing how the cancellations balance;
- the **below-threshold regime** (`N < n`), where the Gram matrix is singular and the naive formula breaks down — here the signed sums are shown to vanish exactly (conditionally, for any Penrose partner — see below), via a character-table-free route valid at every `N`;
- the **orthogonal and symplectic analogues**, including the hardest single component: the crossing-sign factorization of the symplectic Gram matrix;
- the **`U(N)` Haar-integration bridge at the formalized degrees** (`Weingarten/Haar/`): the Haar expectation constructed for all `N` from Mathlib's Haar measure, the `n = 1` and `n = 2` entry-integral tables, `E|Tr U|² = 1` and `E|Tr U|⁴ = 2`, the `n = 1, 2` Weingarten values, and the one-matrix-model coefficients `w₁ = 1/2`, `w₂ = w₃ = w₄ = 0` (for `N ≥ 2`). The general-`n` Collins–Śniady moment formula remains out of scope.

## The architecture: a character-table-free route

The standard development of Weingarten functions runs through zonal polynomials and symmetric-group character expansions. That machinery is rather heavy, and it really only delivers the **above-threshold** object — it presupposes the Gram matrix is invertible.

This project instead characterizes the Weingarten function `W` via the two **Penrose equations**

```
G W G = G        W G W = W
```

These make sense at *every* `N`, invertible or not. The **Moore–Penrose pseudo-inverse** satisfies both (as does the genuine inverse when it exists), but the two equations alone do not pin down a unique `W`; the full four-equation Moore–Penrose uniqueness is certified in the `(2,3)` cell (`Weingarten.Cell23`) and follows in general for symmetric commuting pairs (`penrose_unique_of_symm_comm`). This pseudo-inverse characterization is the one used by Zinn-Justin and by Collins–Matsumoto; what "character-table-free" means here is that the spectral data enters through Young idempotents and box contents (`∏(N + content)`) rather than through explicit irreducible-character tables or zonal-polynomial expansions — it is still representation theory, in a lighter and more computable disguise. On this footing, the below-threshold facts become short arguments. For example, the signed sum vanishes below threshold in a few lines: the sign character sends `G` to the falling factorial `N(N−1)⋯(N−n+1)`, which hits zero when `1 ≤ N < n`, and `W G W = W` then forces the signed sum of `W` to zero.

## The orthogonal and symplectic cases

This is the most technically demanding part of the project, and it follows from a single change in the combinatorics. The orthogonal and symplectic groups have no separate conjugate entries, so the bookkeeping objects are **pairings** (Brauer diagrams) — ways of matching `2n` points into `n` pairs — rather than permutations. There are `(2n−1)!!` of them, and they do **not** form a group.

Two ingredients drive everything:

- **Loops → the orthogonal Gram.** Overlaying two pairings `p` and `q` and tracing the strands yields some number of closed loops. The orthogonal Gram entry is `Gᴼ(p,q) = N^(loops)`, and the orthogonal Weingarten function is its pseudo-inverse. Its two sum rules reappear as **absorption identities**: the all-ones vector is absorbed with eigenvalue the even-rising factorial `N(N+2)⋯(N+2n−2)`, and an alternating vector with eigenvalue the falling factorial `N(N−1)⋯(N−n+1)`.
- **Crossings → the symplectic sign.** The symplectic form is antisymmetric, so contracting entries along the chords of a pairing picks up an orientation sign on every backward traversal. These signs reorganize into the **crossing parity** `ε(p) = (−1)^(crossings)`, which is invisible orthogonally and is the entire source of difficulty symplectically.

The symplectic case is tied to the orthogonal one by Brauer's negative-dimension duality: `Sp(M)` behaves like "orthogonal at dimension `−2M`." The capstone theorem collapses all of the sign bookkeeping into one clean entrywise formula:

```
G^Sp(π, σ) = ε(π) · ε(σ) · (−1)ⁿ · (−2M)^(loops(π,σ))
```

The `(−2M)^loops` is the negative-dimension duality; the `ε(π)ε(σ)` is the antisymmetry of the form made explicit at the level of individual entries. This ε-twisted symplectic Weingarten function — and the two-argument Gram itself — is due to Matsumoto (2013, [arXiv:1301.5401](https://arxiv.org/abs/1301.5401)), who builds it through the twisted Gelfand pair `(S₂ₖ, Hₖ, ε)`: his `Wg^Sp(σ;z) = (−1)ⁿ ε(σ) Wg^O(σ;−2z)`, and his Theorem 2.4 / eq. (2.15) give the Gram `G = (T^Sp(σ⁻¹τ))` directly, with `ε` the permutation signature. The underlying function-level duality `Wg^Sp = ± Wg^O` under `N ↦ −2N` is also classical (Coulter–Do Remark 2.13; Collins–Śniady §6 give the substitution as d ↦ −d in their own normalization). What the formalization adds is not the object but an **elementary, character-free proof** of it — by direct J-contraction and a crossing-count induction rather than twisted zonal spherical functions — with the per-pairing crossing parity `ε(π)ε(σ)` exposed entrywise (the signature of the canonical representative being exactly the crossing parity). (The repository uses `M` for the symplectic rank, so the substitution reads `N ↦ −2M`; Matsumoto and Coulter–Do write it as `N ↦ −2N`.)

The payoff is a clean role swap. The orthogonal absorption identities are polynomial in the parameter `N`, so they remain valid at `N = −2M` with no further work. Under that substitution the two factorials trade places, and the two special vectors swap which one vanishes:

| Special vector | Orthogonal (parameter `N`) | Symplectic (`N = −2M`, ε-twisted) |
| --- | --- | --- |
| all-ones | even-rising `N(N+2)⋯(N+2n−2)` | even-falling `2M(2M−2)⋯` — vanishes when `M < n` |
| alternating | falling `N(N−1)⋯(N−n+1)` | shifted rising `2M(2M+1)⋯` — never vanishes (`M ≥ 1`) |

A single polynomial identity is proved once and yields both the orthogonal and symplectic consequences.

### Why is this side harder to formalize?

- **No group.** Pairings form only a monoid (the Brauer monoid, under diagram concatenation with loop removal — not under composition as permutations); the relevant symmetry is the Gelfand pair `(S₂ₙ, Hₙ)` with the hyperoctahedral group. The Jucys–Murphy factorization is replaced by one over the *odd-indexed* elements — `∑ Wgᴼ(𝔪) 𝔪 = ∏ᵢ (N + J₂ᵢ₋₁)⁻¹ · 𝔢ₖ` (Matsumoto 2011) — and zonal spherical functions play the role characters did in the unitary case.
- **The antisymmetric sign.** Proving that the contraction signs reorganize into exactly `ε(π)ε(σ)` is a delicate parity argument, and it contains the single hardest leaf of the development.
- **A merge-induction.** The symplectic factorization is proved by inducting on `n`, summing out one vertex at a time and showing the loop count and the sign each transform correctly under the merge — every step carrying a sign the orthogonal case never sees.

## The Haar-integration bridge: `Weingarten/Haar/`

The measure-theoretic layer that connects this algebra to genuine integrals over `U(N)` lives under `Weingarten/Haar/`. The module family:

- `HaarExpectation` — the invariance interface: a normalized, two-sided translation-invariant expectation on `C(U(N), ℂ)`;
- `HaarConstruction` (with `SecondCountableShim`) — the interface inhabited for **all** `N` from Mathlib's Haar measure on the compact group `U(N)`;
- `MatrixEntryIntegrals` — the complete `n = 1` entry table `E[U_ij · conj(U_kl)] = δ_ik δ_jl / N`, plus `E[Tr U] = 0` and `E|Tr U|² = 1`;
- `EntryIntegralsTwo` — the `n = 2` fourth-moment table (matched, crossed, and diagonal index patterns) and `E|Tr U|⁴ = 2` for `N ≥ 2`;
- `WeingartenValues` — the unitary Weingarten values at `n = 1, 2` (`1/N`; `1/(N²−1)` and `−1/(N(N²−1))`), derived from the sum rules formalized here;
- `BridgeSummary` — the vocabulary map onto this repository's own Gram and Weingarten declarations;
- `ConjugationInvariance`, `StarReal` — conjugation-invariance and star-reality transport for observables;
- `PairHaar`, `ProductHaar` — the two-copy and `k`-copy product-Haar expectations and their factorization laws;
- `TraceEntryMoments` — mixed trace–entry moments;
- `OneMatrixModel` — the one-matrix-model coefficients `w₁ = 1/2`, `w₂ = w₃ = w₄ = 0` (for `N ≥ 2`);
- `HonestKernel` — the one-link exponential kernel: `Z(β) = ∫ e^{β·Re Tr U} dU > 0`, its cosh/sinh forms, and `λ_F(β) < Z(β)`.

The claim is deliberately bounded: this is **the `U(N)` Haar-integration bridge at the formalized degrees** — the degrees appearing in the tables above — not a full Haar-integration formalization. The general-`n` Collins–Śniady moment formula is not formalized here, under any name.

## Why does this project matter?

Random matrices model generic high-dimensional systems: when the details are unknown, assume the system is typical. Weingarten calculus is the computational engine for the classical-group version of that idea, and it routes through an unusual number of fields:

- **Quantum information** — random circuits, entanglement and scrambling, the decoupling theorem, randomized benchmarking of real hardware, unitary `t`-designs, classical shadows. This is the main modern driver.
- **Theoretical physics** — Weingarten introduced it in 1978 for lattice gauge theory; it remains in use across random-matrix models and QCD.
- **Free probability** — Weingarten calculus is the finite-`N` engine whose large-`N` limit is Voiculescu's theory of non-commutative randomness.
- **Statistics** — Wishart matrices and multivariate analysis.

The mathematics spread widely enough that Collins, Matsumoto, and Novak wrote the survey [*The Weingarten Calculus*](https://arxiv.org/abs/2109.14890) (Notices of the AMS, 2022). This repository is a machine-checked formalization of a core algebraic layer underlying Weingarten calculus: Jucys–Murphy elements, Gram operators, Weingarten pseudo-inverses, signed sum rules, and the unitary, orthogonal, and symplectic extensions treated in the standard literature. It follows the framework surveyed by Collins, Matsumoto, and Novak, while isolating a Lean-verifiable spine of definitions and identities that can be inspected independently of the surrounding analytic and representation-theoretic applications. The Haar-integration bridge that consumes this algebraic layer is now machine-checked in-repo under `Weingarten/Haar/`: the Haar expectation on `U(N)` is constructed for all `N` from Mathlib's Haar measure; the `n = 1` and `n = 2` entry-integral tables are proved from invariance alone; `E|Tr U|² = 1` and `E|Tr U|⁴ = 2`; and the one-matrix-model coefficients come out as `w₁ = 1/2`, `w₂ = w₃ = w₄ = 0` (for `N ≥ 2`) — the bridge at the formalized degrees. The general-`n` Collins–Śniady moment formula remains out of scope.

The project should be read as a verification artifact rather than as a claim of new mathematics. Its usefulness to the field is for others to judge; its purpose is to make a classical algebraic layer of the theory explicit, reproducible, and machine-checkable.

## Verification

The verification standard for the repository is the Lean development itself: all theorems are intended to build without `sorry` or `native_decide`, and the stated axiom profile is checked with `#print axioms`.  As a second, independent line of defense — against a definition that quietly fails to match the literature, or a transcription slip in a statement — the `scripts/` directory recomputes the finite content of every computational theorem from scratch, in exact rational arithmetic (Python standard library only — no floats, no external packages), and checks it against a genuinely independent computation.

The checks are **exhaustive up to a size bound**: all of `Sₙ` for `n ≤ 5` (the sum rules to `n ≤ 7`), and all `(2n−1)!!` pairings for `2n ≤ 8`. Each one pits two unrelated computations against each other rather than re-running one formula twice. For instance, the symplectic capstone contracts the symplectic form directly along every index assignment of the two pairings and compares the raw result to the closed `ε(π)·ε(σ)·(−1)ⁿ·(−2M)^loops` formula; the unitary spine compares a brute-force sum over `Sₙ` to the Jucys–Murphy product, and an exact Gram inverse to the sign-of-permutation predicate. The genuinely analytic statements (the `ℓ¹`/Neumann invertibility, the `tsum` expansions) have no finite content to enumerate and are exercised only through their finite numeric consequences.

Run the whole suite:

```sh
python scripts/verify_all.py
```

It executes all ten suites — four per-theorem suites plus the original convention and proof-step checks — and prints a `PASS` line per theorem. [`scripts/VERIFICATION.md`](scripts/VERIFICATION.md) is the per-theorem ledger: what each check computes, the bound it covers, and which statements are Lean-only.

## Reproducibility

The project is reproducible by following the Lean 4 / Mathlib project build instructions above.

## AI assistance

This project was developed with assistance from AI coding and writing tools. Those tools were used for literature-search support, draft prose, refactoring suggestions, and Lean proof-engineering. The accompanying prose, bibliography, and informal mathematical explanations are provided to document intent and context, but they should not be treated as professional, legal, engineering, financial, medical, or safety-critical advice.

The software and documentation are provided as-is, without warranty.

## Attribution and bibliography corrections

This repository is intended to credit the Weingarten-calculus literature accurately and conservatively. Some formalized statements are presented as elementary consequences of standard results rather than as new mathematics; where an identity appears explicitly in the literature, I would prefer to cite the original source.

If you notice an error, omission, earlier source, incorrect attribution, or bibliographic ambiguity, please open a GitHub issue or pull request. Especially helpful reports include:

- the statement or file location affected;
- the source that should be added, corrected, or preferred;
- the relevant theorem, proposition, lemma, definition, equation, or page number;
- whether the correction changes only attribution/bibliography or also the mathematical statement.

## References

The survey is the canonical entry point; the remaining works are the specific sources the formalization rests on.

- B. Collins, S. Matsumoto, J. Novak. *The Weingarten calculus.* Notices Amer. Math. Soc. **69** (2022), no. 5, 734–745. [arXiv:2109.14890](https://arxiv.org/abs/2109.14890).
- A.-A. A. Jucys. *Symmetric polynomials and the center of the symmetric group ring.* Rep. Math. Phys. **5** (1974), no. 1, 107–112.
- D. Weingarten. *Asymptotic behavior of group integrals in the limit of infinite rank.* J. Math. Phys. **19** (1978), no. 5, 999–1001. [doi:10.1063/1.523807](https://doi.org/10.1063/1.523807).
- B. Collins. *Moments and cumulants of polynomial random variables on unitary groups, the Itzykson–Zuber integral, and free probability.* Int. Math. Res. Not. (2003), no. 17, 953–982. [arXiv:math-ph/0205010](https://arxiv.org/abs/math-ph/0205010).
- B. Collins, P. Śniady. *Integration with respect to the Haar measure on unitary, orthogonal and symplectic group.* Comm. Math. Phys. **264** (2006), no. 3, 773–795. [arXiv:math-ph/0402073](https://arxiv.org/abs/math-ph/0402073). *(§6 gives the symplectic substitution `d ↦ −d` and the explicit sign.)*
- B. Collins, S. Matsumoto. *On some properties of orthogonal Weingarten functions.* J. Math. Phys. **50** (2009), no. 11, 113516. [arXiv:0903.5143](https://arxiv.org/abs/0903.5143).
- B. Collins, S. Matsumoto. *Weingarten calculus via orthogonality relations: new applications.* ALEA Lat. Am. J. Probab. Math. Stat. **14** (2017), no. 1, 631–656. [arXiv:1701.04493](https://arxiv.org/abs/1701.04493). *(Orthogonality-relations route; also states `±Wg^Sp(𝔪,d) = Wg^O(𝔪,−2d)`.)*
- S. Matsumoto. *Jucys–Murphy elements, orthogonal matrix integrals, and Jack measures.* Ramanujan J. **26** (2011), no. 1, 69–107. [arXiv:1001.2345](https://arxiv.org/abs/1001.2345). *(Odd-Jucys–Murphy factorization of the orthogonal Gram.)*
- S. Matsumoto. *Weingarten calculus for matrix ensembles associated with compact symmetric spaces.* Random Matrices Theory Appl. **2** (2013), no. 2, 1350001. [arXiv:1301.5401](https://arxiv.org/abs/1301.5401). *(ε-twisted symplectic Weingarten via the twisted Gelfand pair; the two-argument symplectic Gram in Theorem 2.4 / eq. (2.15).)*
- X. Coulter, N. Do. *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements.* [arXiv:2506.04002](https://arxiv.org/abs/2506.04002). *(Remark 2.13 / Remark 3.14: the symplectic Weingarten function is `± Wg^O|_{N ↦ −2N}`; the unitary/orthogonal/symplectic cases sit at `b = 0, 1, −1/2`.)*
- P. Zinn-Justin. *Jucys–Murphy elements and Weingarten matrices.* [arXiv:0907.2719](https://arxiv.org/abs/0907.2719). *(Pseudo-inverse / Jucys–Murphy derivation of the orthogonal Weingarten matrix.)*

## License

Licensed under the Apache License, Version 2.0. See [`LICENSE`](LICENSE) for the full text.
