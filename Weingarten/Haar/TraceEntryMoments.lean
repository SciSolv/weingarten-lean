/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.ConjugationInvariance
import Weingarten.Haar.OneMatrixModel

/-!
# Trace–entry moments against a conjugation-invariant weight

Everything here is symmetry
bookkeeping, not integration: **no new Haar integral is evaluated in this file**;
every value reduces to the `mMoment`/`zMoment` tables of `OneMatrixModel`.

## The key lemma

`HaarExpectation.integral_entry_mul_conjInv` (hypothesis-parametric, valid for every
weight `f` invariant under unitary conjugation):

`E (U_{ij} · f) = δ_{ij} · N⁻¹ · E (Tr U · f)`.

Proof by the conjugation symmetry supplied by
`Weingarten.Haar.ConjugationInvariance`: for `i ≠ j`, conjugating by the
diagonal phase `diag(1, …, I, …, 1)` at position `i` fixes `f` and rescales the entry
by `I ≠ 1`, so the conjugation charge kill fires; on the diagonal, conjugating by a
transposition equalizes `E (U_{aa} · f)` over `a`, and summing against
`Tr U = ∑_a U_{aa}` normalizes the common value. Specializing `f := R^k`
(`R = Re Tr U`, a class function) yields the **per-order eigenvector equations** of
the one-matrix kernel weight: the structural identities hold for *all* `k`
(only the `mMoment` value theorems are capped at `k ≤ 4`).

## Provenance of the kernel reading (PDF-verified)

In the originating development these are the matrix elements
`⟨column | K_β | character⟩` of the single-link kernel `K(U,V) = e^{β Re Tr(U⁻¹V)}`:
Lüscher, Comm. Math. Phys. 54 (1977) 283,
Eq. (21); Creutz, Phys. Rev. D 15 (1977) 1128, p. 1131 (author's self-archived
scan). Its diagonalization on characters is Drouffe–Zuber, Phys. Rep. 102 (1983),
Eqs. (3.17)/(3.28). The `δ_{ij}/N` shape is the `n = 1` Weingarten contraction
(Collins–Śniady, arXiv:math-ph/0402073, eq. (11)) upgraded by a conjugation-invariant
spectator weight.

`integral_star_trace_mul_reTrace_pow` records the reflection symmetry
`E (conj(Tr U) · R^k) = m_k` for `k ≤ 4` (`N ≥ 2`): the starred numerator moments
coincide with the plain ones by balanced-term matching under the binomial expansion.
-/

namespace Weingarten.Haar

open Matrix

variable {N : ℕ}

/-! ### Observable expansions and composition bridges -/

/-- The trace observable is the sum of the diagonal entry observables. -/
theorem traceObs_eq_sum_entryObs : traceObs N = ∑ i, entryObs N i i := by
  ext U
  simp only [traceObs_apply, ContinuousMap.sum_apply, entryObs_apply]
  rfl

/-- The trace observable `Tr(A·U)` expanded into weighted entry observables:
`Tr(A·U) = ∑_{i,p} A_{ip} U_{pi}`. -/
theorem traceMulObs_eq_sum (A : Matrix (Fin N) (Fin N) ℂ) :
    traceMulObs N A = ∑ i, ∑ p, A i p • entryObs N p i := by
  ext U
  simp only [traceMulObs_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    entryObs_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Matrix.mul_apply

/-- The conjugate trace observable `Tr(B·U*)` expanded into weighted starred entries:
`Tr(B·U*) = ∑_{i,l} B_{il} conj(U_{il})`. -/
theorem traceMulStarObs_eq_sum (B : Matrix (Fin N) (Fin N) ℂ) :
    traceMulStarObs N B = ∑ i, ∑ l, B i l • star (entryObs N i l) := by
  ext U
  simp only [traceMulStarObs_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.star_apply, entryObs_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (B * star U.1) i i = _
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [Matrix.star_apply]

/-- **Left-translation bridge**: the translated trace is the trace pairing,
`(V ↦ Tr(U·V)) = traceMulObs N U`. This is Lüscher's change of variables
`V = U⁻¹U′` (CMP 54 (1977), the substitution displayed in Eq. (23)) as an
observable identity. -/
theorem traceObs_comp_mulLeft (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (traceObs N).comp (ContinuousMap.mulLeft U) = traceMulObs N U.1 := by
  ext V
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, traceObs_apply,
    traceMulObs_apply, Matrix.UnitaryGroup.mul_val]

/-- **Left-translation bridge, starred**: `(V ↦ conj Tr(U·V)) = traceMulStarObs N U*`. -/
theorem star_traceObs_comp_mulLeft (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (star (traceObs N)).comp (ContinuousMap.mulLeft U)
      = traceMulStarObs N (star U.1) := by
  ext V
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.star_apply, traceObs_apply, traceMulStarObs_apply,
    Matrix.UnitaryGroup.mul_val]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.trace_mul_comm,
    ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose]

/-- Pointwise star commutes with precomposition. -/
private theorem star_comp (h : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
    (c : C(Matrix.unitaryGroup (Fin N) ℂ, Matrix.unitaryGroup (Fin N) ℂ)) :
    (star h).comp c = star (h.comp c) := by
  ext U; rfl

namespace HaarExpectation

private theorem I_ne_one : Complex.I ≠ 1 := by
  intro h
  have h' := congrArg Complex.im h
  simp at h'

private theorem star_I_ne_one : star Complex.I ≠ 1 := by
  intro h
  have h' := congrArg Complex.im h
  simp at h'

/-- **The entry–class-function contraction** (hypothesis-parametric key lemma): for any observable `f` invariant under unitary conjugation,

`E (U_{ij} · f) = δ_{ij} · N⁻¹ · E (Tr U · f)`.

Off-diagonal kill: conjugation by the diagonal phase `I` at position `i` fixes `f`
and rescales `U_{ij}` by `I ≠ 1` (conjugation charge kill). Diagonal: transposition
conjugations equalize `E (U_{aa} · f)` over `a`; summing against `Tr U = ∑_a U_{aa}`
pins the common value to `N⁻¹ · E (Tr U · f)`. Symmetry bookkeeping only — no
integral is evaluated. -/
theorem integral_entry_mul_conjInv (E : HaarExpectation N) [NeZero N] (i j : Fin N)
    {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    (hf : ∀ g : Matrix.unitaryGroup (Fin N) ℂ, f.comp (conjMap N g) = f) :
    E (entryObs N i j * f)
      = if i = j then (N : ℂ)⁻¹ * E (traceObs N * f) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have heq : ∀ a : Fin N,
        E (entryObs N a a * f) = E (entryObs N i i * f) := by
      intro a
      have hcomp : (entryObs N i i * f).comp
            (conjMap N (permUnitary N (Equiv.swap a i)))
          = entryObs N a a * f := by
        rw [ContinuousMap.mul_comp, entryObs_comp_conj_perm, hf,
          Equiv.swap_apply_right]
      calc E (entryObs N a a * f)
          = E ((entryObs N i i * f).comp
              (conjMap N (permUnitary N (Equiv.swap a i)))) := by rw [hcomp]
        _ = E (entryObs N i i * f) := E.map_conj _ _
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hkey : E (traceObs N * f) = (N : ℂ) * E (entryObs N i i * f) := by
      have hobs : traceObs N * f = ∑ a, entryObs N a a * f := by
        rw [← Finset.sum_mul, ← traceObs_eq_sum_entryObs]
      rw [hobs, E.map_sum, Finset.sum_congr rfl fun a _ => heq a, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hkey, inv_mul_cancel_left₀ hN]
  · rw [if_neg hij]
    refine E.integral_eq_zero_of_charge_conj
      (g := phaseUnitary N i Complex.I I_mul_star_I) (w := Complex.I) I_ne_one ?_
    rw [ContinuousMap.mul_comp, entryObs_comp_conj_phase, hf, if_pos rfl,
      if_neg (Ne.symm hij), mul_one, smul_mul_assoc]

/-- **The starred entry–class-function contraction**:
`E (conj(U_{ij}) · f) = δ_{ij} · N⁻¹ · E (conj(Tr U) · f)` for conjugation-invariant
`f`. Mirror of `integral_entry_mul_conjInv` (the kill weight is `conj I ≠ 1`). -/
theorem integral_star_entry_mul_conjInv (E : HaarExpectation N) [NeZero N]
    (i j : Fin N) {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    (hf : ∀ g : Matrix.unitaryGroup (Fin N) ℂ, f.comp (conjMap N g) = f) :
    E (star (entryObs N i j) * f)
      = if i = j then (N : ℂ)⁻¹ * E (star (traceObs N) * f) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have heq : ∀ a : Fin N,
        E (star (entryObs N a a) * f) = E (star (entryObs N i i) * f) := by
      intro a
      have hcomp : (star (entryObs N i i) * f).comp
            (conjMap N (permUnitary N (Equiv.swap a i)))
          = star (entryObs N a a) * f := by
        rw [ContinuousMap.mul_comp, star_comp, entryObs_comp_conj_perm, hf,
          Equiv.swap_apply_right]
      calc E (star (entryObs N a a) * f)
          = E ((star (entryObs N i i) * f).comp
              (conjMap N (permUnitary N (Equiv.swap a i)))) := by rw [hcomp]
        _ = E (star (entryObs N i i) * f) := E.map_conj _ _
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hkey : E (star (traceObs N) * f)
        = (N : ℂ) * E (star (entryObs N i i) * f) := by
      have hobs : star (traceObs N) * f = ∑ a, star (entryObs N a a) * f := by
        rw [← Finset.sum_mul, traceObs_eq_sum_entryObs, star_sum]
      rw [hobs, E.map_sum, Finset.sum_congr rfl fun a _ => heq a, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hkey, inv_mul_cancel_left₀ hN]
  · rw [if_neg hij]
    refine E.integral_eq_zero_of_charge_conj
      (g := phaseUnitary N i Complex.I I_mul_star_I) (w := star Complex.I)
      star_I_ne_one ?_
    rw [ContinuousMap.mul_comp, star_comp, entryObs_comp_conj_phase, hf, if_pos rfl,
      if_neg (Ne.symm hij), mul_one, star_smul, smul_mul_assoc]

end HaarExpectation

open HaarExpectation

/-! ### `R` and its powers are class functions -/

/-- `R = Re Tr U` is a class function: conjugation fixes it. -/
theorem reTraceObs_comp_conj (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (reTraceObs N).comp (conjMap N g) = reTraceObs N := by
  have h : translateConj N g (reTraceObs N) = reTraceObs N := by
    rw [reTraceObs, map_smul, map_add, map_star]
    simp only [translateConj_apply, traceObs_comp_conj]
  simpa only [translateConj_apply] using h

/-- Powers of `R` are class functions. -/
theorem reTraceObs_pow_comp_conj (k : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    ((reTraceObs N) ^ k).comp (conjMap N g) = (reTraceObs N) ^ k := by
  have h : translateConj N g ((reTraceObs N) ^ k) = (reTraceObs N) ^ k := by
    rw [map_pow, translateConj_apply, reTraceObs_comp_conj]
  simpa only [translateConj_apply] using h

/-! ### The per-order eigenvector equations (structural: all `k`) -/

/-- **Entry column of the kernel, per β-order**: for every `k`,
`E (R^k · U_{ij}) = δ_{ij} · N⁻¹ · m_k` where `m_k = mMoment E k = E (Tr U · R^k)`.
Structural identity valid for ALL `k` — only the `mMoment` *value* theorems are
capped at `k ≤ 4` (the degree-5 moment ceiling). -/
theorem integral_reTracePow_mul_entry (E : HaarExpectation N) [NeZero N] (k : ℕ)
    (i j : Fin N) :
    E ((reTraceObs N) ^ k * entryObs N i j)
      = if i = j then (N : ℂ)⁻¹ * mMoment E k else 0 := by
  rw [mul_comm ((reTraceObs N) ^ k) (entryObs N i j),
    E.integral_entry_mul_conjInv i j (reTraceObs_pow_comp_conj k)]
  rfl

/-- **Starred entry column of the kernel, per β-order**: for every `k`,
`E (R^k · conj(U_{ij})) = δ_{ij} · N⁻¹ · E (conj(Tr U) · R^k)`. -/
theorem integral_reTracePow_mul_star_entry (E : HaarExpectation N) [NeZero N]
    (k : ℕ) (i j : Fin N) :
    E ((reTraceObs N) ^ k * star (entryObs N i j))
      = if i = j then (N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k)
        else 0 := by
  rw [mul_comm ((reTraceObs N) ^ k) (star (entryObs N i j)),
    E.integral_star_entry_mul_conjInv i j (reTraceObs_pow_comp_conj k)]

/-! ### The starred numerator moments coincide with the plain ones (`k ≤ 4`) -/

/-- `E` against small numeral multiples — thin wrappers over the public
`HaarExpectation.map_natCast_mul` (numeral bridged by `Nat.cast_ofNat`). -/
private theorem map_two_mul (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (2 * f) = 2 * E f := by
  have h := E.map_natCast_mul 2 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_three_mul (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (3 * f) = 3 * E f := by
  have h := E.map_natCast_mul 3 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_four_mul (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (4 * f) = 4 * E f := by
  have h := E.map_natCast_mul 4 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_six_mul (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (6 * f) = 6 * E f := by
  have h := E.map_natCast_mul 6 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

/-- **Reflection symmetry of the numerator moments**:
`E (conj(Tr U) · R^k) = m_k` for `k ≤ 4`, `N ≥ 2` — the starred m-moments equal the
plain ones, term by term: the binomial expansion of `conj(T)·(T + conj T)^k` pairs
each balanced word with the balanced word of `T·(T + conj T)^k` at the mirrored
binomial coefficient, and unbalanced words die by the ζ-charge kill. -/
theorem integral_star_trace_mul_reTrace_pow (E : HaarExpectation N) (hN : 2 ≤ N)
    {k : ℕ} (hk : k ≤ 4) :
    E (star (traceObs N) * (reTraceObs N) ^ k) = mMoment E k := by
  interval_cases k
  · rw [mMoment_zero E hN, pow_zero, mul_one,
      show star (traceObs N)
        = (traceObs N) ^ 0 * (star (traceObs N)) ^ 1 from by ring,
      integral_trace_pow_mul_star_pow E hN (by omega)]
    norm_num
  · rw [mMoment_one E hN, pow_one, reTraceObs, mul_smul_comm, E.map_smul,
      show star (traceObs N) * (traceObs N + star (traceObs N))
        = (traceObs N) ^ 1 * (star (traceObs N)) ^ 1
          + (traceObs N) ^ 0 * (star (traceObs N)) ^ 2 from by ring,
      E.map_add, integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega)]
    norm_num
  · rw [mMoment_two E hN, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
      show star (traceObs N) * (traceObs N + star (traceObs N)) ^ 2
        = (traceObs N) ^ 2 * (star (traceObs N)) ^ 1
          + (2 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 2)
          + (traceObs N) ^ 0 * (star (traceObs N)) ^ 3 from by ring,
      E.map_add, E.map_add, map_two_mul E,
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega)]
    norm_num
  · rw [mMoment_three E hN, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
      show star (traceObs N) * (traceObs N + star (traceObs N)) ^ 3
        = (traceObs N) ^ 3 * (star (traceObs N)) ^ 1
          + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 2)
          + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 3)
          + (traceObs N) ^ 0 * (star (traceObs N)) ^ 4 from by ring,
      E.map_add, E.map_add, E.map_add, map_three_mul E, map_three_mul E,
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega)]
    norm_num
  · rw [mMoment_four E hN, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
      show star (traceObs N) * (traceObs N + star (traceObs N)) ^ 4
        = (traceObs N) ^ 4 * (star (traceObs N)) ^ 1
          + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 3 * (star (traceObs N)) ^ 2)
          + (6 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 3)
          + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
            * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 4)
          + (traceObs N) ^ 0 * (star (traceObs N)) ^ 5 from by ring,
      E.map_add, E.map_add, E.map_add, E.map_add, map_four_mul E, map_six_mul E,
      map_four_mul E,
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega),
      integral_trace_pow_mul_star_pow E hN (by omega)]
    norm_num

/-! ### Packaged trace contractions (structural: all `k`) -/

/-- **The `Tr(A·U)` contraction against `R^k`**: for every `k` and deterministic
`A`, `E (R^k · Tr(A·U)) = N⁻¹ · m_k · Tr A`. Finite weighted sum over the entry
column. -/
theorem integral_reTracePow_mul_traceMul (E : HaarExpectation N) [NeZero N] (k : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    E ((reTraceObs N) ^ k * traceMulObs N A)
      = (N : ℂ)⁻¹ * mMoment E k * A.trace := by
  have hexp : (reTraceObs N) ^ k * traceMulObs N A
      = ∑ i, ∑ p, A i p • ((reTraceObs N) ^ k * entryObs N p i) := by
    rw [traceMulObs_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => mul_smul_comm _ _ _
  rw [hexp, E.map_sum]
  calc ∑ i, E (∑ p, A i p • ((reTraceObs N) ^ k * entryObs N p i))
      = ∑ i, ∑ p, A i p * E ((reTraceObs N) ^ k * entryObs N p i) :=
        Finset.sum_congr rfl fun i _ => E.map_weighted_sum _ _ _
    _ = ∑ i, ∑ p, A i p * (if p = i then (N : ℂ)⁻¹ * mMoment E k else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
        rw [integral_reTracePow_mul_entry E k p i]
    _ = ∑ i, A i i * ((N : ℂ)⁻¹ * mMoment E k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i
          (fun p _ hpi => by rw [if_neg hpi, mul_zero])
          (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    _ = (∑ i, A i i) * ((N : ℂ)⁻¹ * mMoment E k) := (Finset.sum_mul _ _ _).symm
    _ = (N : ℂ)⁻¹ * mMoment E k * A.trace := by
        rw [show A.trace = ∑ i, A i i from rfl]; ring

/-- **The `Tr(B·U*)` contraction against `R^k`**: for every `k` and
deterministic `B`, `E (R^k · Tr(B·U*)) = N⁻¹ · E (conj(Tr U) · R^k) · Tr B`. -/
theorem integral_reTracePow_mul_traceMulStar (E : HaarExpectation N) [NeZero N]
    (k : ℕ) (B : Matrix (Fin N) (Fin N) ℂ) :
    E ((reTraceObs N) ^ k * traceMulStarObs N B)
      = (N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k) * B.trace := by
  have hexp : (reTraceObs N) ^ k * traceMulStarObs N B
      = ∑ i, ∑ l, B i l • ((reTraceObs N) ^ k * star (entryObs N i l)) := by
    rw [traceMulStarObs_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
  rw [hexp, E.map_sum]
  calc ∑ i, E (∑ l, B i l • ((reTraceObs N) ^ k * star (entryObs N i l)))
      = ∑ i, ∑ l, B i l * E ((reTraceObs N) ^ k * star (entryObs N i l)) :=
        Finset.sum_congr rfl fun i _ => E.map_weighted_sum _ _ _
    _ = ∑ i, ∑ l, B i l
          * (if i = l then (N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k)
             else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        rw [integral_reTracePow_mul_star_entry E k i l]
    _ = ∑ i, B i i
          * ((N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i
          (fun l _ hli => by rw [if_neg (Ne.symm hli), mul_zero])
          (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    _ = (∑ i, B i i)
          * ((N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k)) :=
        (Finset.sum_mul _ _ _).symm
    _ = (N : ℂ)⁻¹ * E (star (traceObs N) * (reTraceObs N) ^ k) * B.trace := by
        rw [show B.trace = ∑ i, B i i from rfl]; ring

/-- **Committed cross-check**: specializing the `Tr(A·U)` contraction to `A = 1`
must reproduce the numerator moment exactly — `E (R^k · Tr U) = m_k`. -/
example (E : HaarExpectation N) [NeZero N] (k : ℕ) :
    E ((reTraceObs N) ^ k * traceMulObs N (1 : Matrix (Fin N) (Fin N) ℂ))
      = mMoment E k := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [integral_reTracePow_mul_traceMul, Matrix.trace_one, Fintype.card_fin]
  field_simp

end Weingarten.Haar
