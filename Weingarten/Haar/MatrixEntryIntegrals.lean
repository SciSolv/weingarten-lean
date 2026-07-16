/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.HaarExpectation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix-entry integrals

Exact Haar integrals of low-degree polynomials in matrix entries over a single `U(N)`
factor, proved **conditionally** on an abstract Haar expectation
`E : Weingarten.Haar.HaarExpectation N` (linearity + normalization + bi-invariance on the
algebra of continuous observables `C(U(N), ℂ)`; no positivity, no measure theory — see
`Weingarten.Haar.HaarExpectation`).

## Observables

The integrands are named elements of the function algebra `C(U(N), ℂ)`:
`entryObs N i j` is `U ↦ U i j`, `traceObs N` is `U ↦ Tr U`, and
`traceMulObs N A` / `traceMulStarObs N B` are the trace pairings `U ↦ Tr (A U)` /
`U ↦ Tr (B U*)`. Products, stars and (weighted) sums of observables are formed inside
`C(U(N), ℂ)`, so higher moments (`n = 2` products of four observables,
β-expansions) compose mechanically from these building blocks.

## Main results

* `HaarExpectation.integral_entry_mul_star_entry` (**n = 1 entry integral**):
  `E (entryObs N i j * star (entryObs N k l)) = δ_{ik} δ_{jl} / N`.
* `HaarExpectation.integral_trace`: `E (traceObs N) = 0`.
* `HaarExpectation.integral_trace_mul_star_trace`: `E (|Tr U|²) = 1`.
* `HaarExpectation.integral_trace_mul_trace_star` (**trace-pairing formula**):
  `E (traceMulObs N A * traceMulStarObs N B) = N⁻¹ * Tr(A B)`.

## Provenance (PDF-verified citations)

* The value `E |U_{ij}|² = 1/N` is the `n = 1` Weingarten function: it is displayed as
  `Wg^U([1], d) = 1/d` in Collins–Matsumoto, *Weingarten calculus via orthogonality
  relations: new applications*, arXiv:1701.04493, Example 2.3 (PDF-verified). The
  general moment formula it instantiates is Collins–Śniady, arXiv:math-ph/0402073,
  Cor. 2.4 / eq. (11) (PDF-verified). At `n = 1` this matches this repository's
  `Weingarten.wg` in the stable range `N > 0` (documentation-level tie-in only; no code
  dependency at this tier).
* `E (Tr U) = 0` is the phase/invariance argument of Collins–Śniady,
  arXiv:math-ph/0402073, eq. (12) (PDF-verified), specialized to the scalar unitary
  `-1`: left translation by `scalarUnitary N (-1)` negates `traceObs N`, so the factored
  sign-trick lemma applies.
* The shared-link contraction `E (Tr(A U) Tr(B U*)) = N⁻¹ Tr(A B)` is the termwise
  application of the `n = 1` entry integral (Collins–Śniady eq. (11)); it is the
  workhorse consumed by the β-expansion coefficients (`OneMatrixModel`).

## Proof technique

Everything is elementary and character-free: sign matrices `diagonal (±1)` and
permutation matrices realize enough unitaries to (a) kill off-diagonal moments by the
factored sign trick `integral_eq_zero_of_neg_comp` and (b) equalize `E |U_{ij}|²` over
all entries; row unitarity `∑_j U_{ij} conj(U_{ij}) = 1` then pins the common value to
`1/N`. Linearity enters only through `map_sum` / `map_weighted_sum`.
-/

namespace Weingarten.Haar

open Matrix

variable {N : ℕ}

/-! ### Structured unitaries: sign matrices and permutation matrices -/

/-- The diagonal sign matrix with `-1` in position `i` and `+1` elsewhere, as an element
of the unitary group. Left multiplication by it flips the sign of row `i`; right
multiplication flips the sign of column `i`. -/
def signUnitary (N : ℕ) (i : Fin N) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Matrix.diagonal fun r => if r = i then (-1 : ℂ) else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext r
    by_cases h : r = i <;> simp [h]⟩

@[simp] theorem signUnitary_val (N : ℕ) (i : Fin N) :
    (signUnitary N i).1 = Matrix.diagonal fun r => if r = i then (-1 : ℂ) else 1 := rfl

/-- Left multiplication by `signUnitary N i` rescales row `i` by `-1`. -/
theorem signUnitary_mul_apply (i : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (a b : Fin N) :
    (signUnitary N i * U).1 a b = (if a = i then (-1 : ℂ) else 1) * U.1 a b := by
  rw [Matrix.UnitaryGroup.mul_val, signUnitary_val, Matrix.diagonal_mul]

/-- Right multiplication by `signUnitary N j` rescales column `j` by `-1`. -/
theorem mul_signUnitary_apply (j : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (a b : Fin N) :
    (U * signUnitary N j).1 a b = U.1 a b * (if b = j then (-1 : ℂ) else 1) := by
  rw [Matrix.UnitaryGroup.mul_val, signUnitary_val, Matrix.mul_diagonal]

/-- The diagonal phase matrix with `z` (a unit-circle scalar) in position `i` and `+1`
elsewhere, as an element of the unitary group — the generalization of `signUnitary`
needed at `n = 2`: sign matrices cannot kill *even-charge* integrands (e.g.
`U₁₁² conj(U₁₂)²`, which is invariant under every `±1` diagonal), whereas one phase
entry `z = i` rescales such an integrand by `z² = −1` and the charge lemma fires. -/
def phaseUnitary (N : ℕ) (i : Fin N) (z : ℂ) (hz : z * star z = 1) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Matrix.diagonal fun r => if r = i then z else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext r
    have hz' : z * (starRingEnd ℂ) z = 1 := hz
    by_cases h : r = i
    · simp [h, hz']
    · simp [h]⟩

@[simp] theorem phaseUnitary_val (N : ℕ) (i : Fin N) (z : ℂ) (hz : z * star z = 1) :
    (phaseUnitary N i z hz).1 = Matrix.diagonal fun r => if r = i then z else 1 := rfl

/-- Left multiplication by `phaseUnitary N i z hz` rescales row `i` by `z`. -/
theorem phaseUnitary_mul_apply {i : Fin N} {z : ℂ} {hz : z * star z = 1}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (a b : Fin N) :
    (phaseUnitary N i z hz * U).1 a b = (if a = i then z else 1) * U.1 a b := by
  rw [Matrix.UnitaryGroup.mul_val, phaseUnitary_val, Matrix.diagonal_mul]

/-- Right multiplication by `phaseUnitary N j z hz` rescales column `j` by `z`. -/
theorem mul_phaseUnitary_apply {j : Fin N} {z : ℂ} {hz : z * star z = 1}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (a b : Fin N) :
    (U * phaseUnitary N j z hz).1 a b = U.1 a b * (if b = j then z else 1) := by
  rw [Matrix.UnitaryGroup.mul_val, phaseUnitary_val, Matrix.mul_diagonal]

/-- The permutation matrix of `σ : Equiv.Perm (Fin N)`, as an element of the unitary
group (a real orthogonal `0/1` matrix). -/
def permUnitary (N : ℕ) (σ : Equiv.Perm (Fin N)) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]⟩

/-- Left multiplication by `permUnitary N σ` permutes rows: entry `(a, b)` of the
product reads entry `(σ a, b)` of `U`. -/
theorem permUnitary_mul_apply (σ : Equiv.Perm (Fin N)) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (a b : Fin N) : (permUnitary N σ * U).1 a b = U.1 (σ a) b := by
  have h : (permUnitary N σ * U).1 = σ.toPEquiv.toMatrix * U.1 := rfl
  rw [h, PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- Right multiplication by `permUnitary N σ` permutes columns: entry `(a, b)` of the
product reads entry `(a, σ.symm b)` of `U`. -/
theorem mul_permUnitary_apply (σ : Equiv.Perm (Fin N)) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (a b : Fin N) : (U * permUnitary N σ).1 a b = U.1 a (σ.symm b) := by
  have h : (U * permUnitary N σ).1 = U.1 * σ.toPEquiv.toMatrix := rfl
  rw [h, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-! ### The plane rotation: the one genuinely non-monomial unitary

The `n = 2` moment system is *underdetermined* by the monomial unitaries above
(diagonal phases, signs, permutations): they leave a one-parameter family of candidate
moment values. The π/4 rotation in one coordinate plane supplies the missing equation
(`E |U₁₁|⁴ = 2·E (|U₁₁|²|U₁₂|²)`). Its entries are `±(√2)⁻¹` — no trigonometry. -/

/-- `(√2)⁻¹` as a complex scalar: the entry of the π/4 rotation block. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem invSqrtTwo_star : star invSqrtTwo = invSqrtTwo := by
  rw [invSqrtTwo, star_inv₀]
  norm_num [Complex.star_def, Complex.conj_ofReal]

theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [invSqrtTwo, ← mul_inv, h]

/-- The π/4 rotation in the `(i,j)`-coordinate plane: the identity outside, and the
block `[[s, s], [−s, s]]` on rows/columns `i, j`, with `s = (√2)⁻¹`. -/
noncomputable def planeRot (N : ℕ) (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b =>
    if a = i then (if b = i then invSqrtTwo else if b = j then invSqrtTwo else 0)
    else if a = j then (if b = i then -invSqrtTwo else if b = j then invSqrtTwo else 0)
    else if a = b then 1 else 0

/-! Point values of the plane rotation. `hij : i ≠ j` is required exactly where the
branch order matters. -/

theorem planeRot_ii {i j : Fin N} : planeRot N i j i i = invSqrtTwo := by
  simp [planeRot]

theorem planeRot_ij {i j : Fin N} (hij : i ≠ j) : planeRot N i j i j = invSqrtTwo := by
  simp [planeRot, Ne.symm hij]

theorem planeRot_ji {i j : Fin N} (hij : i ≠ j) : planeRot N i j j i = -invSqrtTwo := by
  simp [planeRot, Ne.symm hij]

theorem planeRot_jj {i j : Fin N} (hij : i ≠ j) : planeRot N i j j j = invSqrtTwo := by
  simp [planeRot, Ne.symm hij]

/-- Row `i` vanishes outside columns `i, j`. -/
theorem planeRot_fst_other {i j c : Fin N} (hci : c ≠ i) (hcj : c ≠ j) :
    planeRot N i j i c = 0 := by
  simp [planeRot, hci, hcj]

/-- Row `j` vanishes outside columns `i, j`. -/
theorem planeRot_snd_other {i j c : Fin N} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j) :
    planeRot N i j j c = 0 := by
  simp [planeRot, Ne.symm hij, hci, hcj]

/-- Rows outside `{i, j}` are standard basis rows. -/
theorem planeRot_other_row {i j a : Fin N} (hai : a ≠ i) (haj : a ≠ j) (c : Fin N) :
    planeRot N i j a c = if a = c then 1 else 0 := by
  simp [planeRot, hai, haj]

section PlaneRotMem

private theorem planeRot_hs : invSqrtTwo * star invSqrtTwo = (2 : ℂ)⁻¹ := by
  rw [invSqrtTwo_star]; exact invSqrtTwo_mul_self

/-- ⟨row i, row i⟩ = 1. -/
private theorem planeRot_dot_ii {i j : Fin N} (hij : i ≠ j) :
    ∑ c, planeRot N i j i c * star (planeRot N i j i c) = 1 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by rw [planeRot_fst_other hc.1 hc.2, zero_mul])]
  rw [planeRot_ii, planeRot_ij hij, planeRot_hs]
  norm_num

/-- ⟨row i, row j⟩ = 0. -/
private theorem planeRot_dot_ij {i j : Fin N} (hij : i ≠ j) :
    ∑ c, planeRot N i j i c * star (planeRot N i j j c) = 0 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by rw [planeRot_fst_other hc.1 hc.2, zero_mul])]
  rw [planeRot_ii, planeRot_ij hij, planeRot_ji hij, planeRot_jj hij, star_neg,
    mul_neg, planeRot_hs]
  ring

/-- ⟨row j, row i⟩ = 0. -/
private theorem planeRot_dot_ji {i j : Fin N} (hij : i ≠ j) :
    ∑ c, planeRot N i j j c * star (planeRot N i j i c) = 0 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by rw [planeRot_snd_other hij hc.1 hc.2, zero_mul])]
  rw [planeRot_ii, planeRot_ij hij, planeRot_ji hij, planeRot_jj hij, neg_mul,
    planeRot_hs]
  ring

/-- ⟨row j, row j⟩ = 1. -/
private theorem planeRot_dot_jj {i j : Fin N} (hij : i ≠ j) :
    ∑ c, planeRot N i j j c * star (planeRot N i j j c) = 1 := by
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by rw [planeRot_snd_other hij hc.1 hc.2, zero_mul])]
  rw [planeRot_ji hij, planeRot_jj hij, star_neg, neg_mul_neg, planeRot_hs]
  norm_num

/-- ⟨row i, standard row b⟩ = 0 for `b ∉ {i, j}`. -/
private theorem planeRot_dot_fst_other {i j b : Fin N} (hbi : b ≠ i) (hbj : b ≠ j) :
    ∑ c, planeRot N i j i c * star (planeRot N i j b c) = 0 := by
  rw [Finset.sum_eq_single b
    (fun c _ hcb => by
      rw [planeRot_other_row hbi hbj, if_neg (Ne.symm hcb), star_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ b) h)]
  rw [planeRot_other_row hbi hbj, if_pos rfl, star_one, mul_one,
    planeRot_fst_other hbi hbj]

/-- ⟨row j, standard row b⟩ = 0 for `b ∉ {i, j}`. -/
private theorem planeRot_dot_snd_other {i j b : Fin N} (hij : i ≠ j) (hbi : b ≠ i)
    (hbj : b ≠ j) :
    ∑ c, planeRot N i j j c * star (planeRot N i j b c) = 0 := by
  rw [Finset.sum_eq_single b
    (fun c _ hcb => by
      rw [planeRot_other_row hbi hbj, if_neg (Ne.symm hcb), star_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ b) h)]
  rw [planeRot_other_row hbi hbj, if_pos rfl, star_one, mul_one,
    planeRot_snd_other hij hbi hbj]

/-- ⟨standard row a, row b⟩ = δ_{ab} for `a ∉ {i, j}` and any `b`. -/
private theorem planeRot_dot_other_row {i j a : Fin N} (hij : i ≠ j) (hai : a ≠ i)
    (haj : a ≠ j) (b : Fin N) :
    ∑ c, planeRot N i j a c * star (planeRot N i j b c)
      = if a = b then 1 else 0 := by
  rw [Finset.sum_eq_single a
    (fun c _ hca => by
      rw [planeRot_other_row hai haj, if_neg (Ne.symm hca), zero_mul])
    (fun h => absurd (Finset.mem_univ a) h)]
  rw [planeRot_other_row hai haj, if_pos rfl, one_mul]
  rcases eq_or_ne b i with hb | hbi
  · rw [hb, planeRot_fst_other hai haj, star_zero, if_neg hai]
  · rcases eq_or_ne b j with hb | hbj
    · rw [hb, planeRot_snd_other hij hai haj, star_zero, if_neg haj]
    · rw [planeRot_other_row hbi hbj]
      by_cases hab : a = b
      · rw [if_pos hab.symm, if_pos hab, star_one]
      · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]

/-- The plane rotation is unitary: rows `i` and `j` are orthonormal (squared norm
`2·(1/2) = 1`, inner product `−1/2 + 1/2 = 0`), rows outside the plane are standard
basis vectors orthogonal to everything else. -/
theorem planeRot_mem {i j : Fin N} (hij : i ≠ j) :
    planeRot N i j ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  rcases eq_or_ne a i with ha | hai
  · rcases eq_or_ne b i with hb | hbi
    · rw [ha, hb, if_pos rfl]; exact planeRot_dot_ii hij
    · rcases eq_or_ne b j with hb | hbj
      · rw [ha, hb, if_neg hij]; exact planeRot_dot_ij hij
      · rw [ha, if_neg (Ne.symm hbi)]; exact planeRot_dot_fst_other hbi hbj
  · rcases eq_or_ne a j with ha | haj
    · rcases eq_or_ne b i with hb | hbi
      · rw [ha, hb, if_neg (Ne.symm hij)]; exact planeRot_dot_ji hij
      · rcases eq_or_ne b j with hb | hbj
        · rw [ha, hb, if_pos rfl]; exact planeRot_dot_jj hij
        · rw [ha, if_neg (Ne.symm hbj)]; exact planeRot_dot_snd_other hij hbi hbj
    · exact planeRot_dot_other_row hij hai haj b

end PlaneRotMem

/-- The π/4 plane rotation as an element of the unitary group. -/
noncomputable def planeUnitary (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨planeRot N i j, planeRot_mem hij⟩

@[simp] theorem planeUnitary_val (N : ℕ) (i j : Fin N) (hij : i ≠ j) :
    (planeUnitary N i j hij).1 = planeRot N i j := rfl

/-- Right multiplication by the plane rotation mixes column `i`:
`(U·R)_{a i} = s·U_{a i} − s·U_{a j}`. -/
theorem mul_planeUnitary_fst {i j : Fin N} (hij : i ≠ j)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (a : Fin N) :
    (U * planeUnitary N i j hij).1 a i
      = invSqrtTwo * U.1 a i - invSqrtTwo * U.1 a j := by
  rw [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
  simp only [planeUnitary_val]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by
      rw [planeRot_other_row hc.1 hc.2, if_neg hc.1, mul_zero])]
  rw [planeRot_ii, planeRot_ji hij]
  ring

/-- Right multiplication by the plane rotation mixes column `j`:
`(U·R)_{a j} = s·U_{a i} + s·U_{a j}`. -/
theorem mul_planeUnitary_snd {i j : Fin N} (hij : i ≠ j)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (a : Fin N) :
    (U * planeUnitary N i j hij).1 a j
      = invSqrtTwo * U.1 a i + invSqrtTwo * U.1 a j := by
  rw [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
  simp only [planeUnitary_val]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    (fun c _ hc => by
      rw [planeRot_other_row hc.1 hc.2, if_neg hc.2, mul_zero])]
  rw [planeRot_ij hij, planeRot_jj hij]
  ring

/-- Right multiplication by the plane rotation leaves the other columns unchanged. -/
theorem mul_planeUnitary_other {i j b : Fin N} (hij : i ≠ j) (hbi : b ≠ i) (hbj : b ≠ j)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (a : Fin N) :
    (U * planeUnitary N i j hij).1 a b = U.1 a b := by
  rw [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
  simp only [planeUnitary_val]
  rw [Finset.sum_eq_single b
    (fun c _ hcb => by
      rcases eq_or_ne c i with hc | hci
      · rw [hc, planeRot_fst_other hbi hbj, mul_zero]
      · rcases eq_or_ne c j with hc | hcj
        · rw [hc, planeRot_snd_other hij hbi hbj, mul_zero]
        · rw [planeRot_other_row hci hcj, if_neg hcb, mul_zero])
    (fun h => absurd (Finset.mem_univ b) h)]
  rw [planeRot_other_row hbi hbj, if_pos rfl, mul_one]

/-! ### The observables, as elements of `C(U(N), ℂ)`

Continuity is by composition: the subtype inclusion into matrices is continuous, matrix
entries/products/traces are continuous in the entrywise (pi) topology
(`Mathlib.Topology.Instances.Matrix`), and `star` is continuous on `ℂ` and on
matrices. -/

/-- The matrix-entry observable `U ↦ U_{ij}`, as a continuous map on `U(N)`. -/
def entryObs (N : ℕ) (i j : Fin N) : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => U.1 i j, continuous_subtype_val.matrix_elem i j⟩

@[simp] theorem entryObs_apply (i j : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    entryObs N i j U = U.1 i j := rfl

/-- The trace observable `U ↦ Tr U`, as a continuous map on `U(N)`. -/
def traceObs (N : ℕ) : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => (U.1).trace, continuous_subtype_val.matrix_trace⟩

@[simp] theorem traceObs_apply (U : Matrix.unitaryGroup (Fin N) ℂ) :
    traceObs N U = (U.1).trace := rfl

/-- The trace observable `U ↦ Tr (A U)` for a deterministic matrix `A`, as a
continuous map on `U(N)`. -/
def traceMulObs (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => (A * U.1).trace,
    (continuous_const.matrix_mul continuous_subtype_val).matrix_trace⟩

@[simp] theorem traceMulObs_apply (A : Matrix (Fin N) (Fin N) ℂ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    traceMulObs N A U = (A * U.1).trace := rfl

/-- The conjugate trace observable `U ↦ Tr (B U*)` for a deterministic matrix
`B`, as a continuous map on `U(N)`. -/
def traceMulStarObs (N : ℕ) (B : Matrix (Fin N) (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => (B * star U.1).trace,
    (continuous_const.matrix_mul continuous_subtype_val.star).matrix_trace⟩

@[simp] theorem traceMulStarObs_apply (B : Matrix (Fin N) (Fin N) ℂ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    traceMulStarObs N B U = (B * star U.1).trace := rfl

/-! ### Translating entry observables

Composing an entry observable with a translation expands it as a weighted sum of entry
observables — this is the single move that turns invariance arguments for polynomial
moments (via the ⋆-homomorphisms `translateLeft`/`translateRight`) into
`map_weighted_sum` bookkeeping. -/

/-- Left translation of an entry observable: `(U ↦ (g·U)_{ab}) = ∑ c, g_{ac} • (U ↦ U_{cb})`. -/
theorem entryObs_comp_mulLeft (g : Matrix.unitaryGroup (Fin N) ℂ) (a b : Fin N) :
    (entryObs N a b).comp (ContinuousMap.mulLeft g)
      = ∑ c, g.1 a c • entryObs N c b := by
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, entryObs_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]

/-- Right translation of an entry observable: `(U ↦ (U·g)_{ab}) = ∑ c, g_{cb} • (U ↦ U_{ac})`. -/
theorem entryObs_comp_mulRight (g : Matrix.unitaryGroup (Fin N) ℂ) (a b : Fin N) :
    (entryObs N a b).comp (ContinuousMap.mulRight g)
      = ∑ c, g.1 c b • entryObs N a c := by
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight, entryObs_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

namespace HaarExpectation

/-! ### The sign trick: off-diagonal moments vanish -/

/-- **Sign trick, rows.** If `i ≠ k`, then `E (U_{ij} conj(U_{kl})) = 0`: left
translation by the row-sign unitary at `i` negates the integrand, so the factored
sign-trick lemma applies. (Collins–Śniady, arXiv:math-ph/0402073, eq. (12)-style
invariance argument.) -/
theorem integral_entry_mul_star_eq_zero_of_row_ne (E : HaarExpectation N)
    {i k : Fin N} (j l : Fin N) (h : i ≠ k) :
    E (entryObs N i j * star (entryObs N k l)) = 0 := by
  refine E.integral_eq_zero_of_neg_comp (g := signUnitary N i) ?_
  ext U
  have h1 : (signUnitary N i * U).1 i j = -(U.1 i j) := by
    rw [signUnitary_mul_apply]; simp
  have h2 : (signUnitary N i * U).1 k l = U.1 k l := by
    rw [signUnitary_mul_apply]; simp [Ne.symm h]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, ContinuousMap.neg_apply, entryObs_apply, h1, h2]
  ring

/-- **Sign trick, columns.** If `j ≠ l`, then `E (U_{ij} conj(U_{kl})) = 0`, by right
translation with the column-sign unitary at `j`. -/
theorem integral_entry_mul_star_eq_zero_of_col_ne (E : HaarExpectation N)
    (i k : Fin N) {j l : Fin N} (h : j ≠ l) :
    E (entryObs N i j * star (entryObs N k l)) = 0 := by
  refine E.integral_eq_zero_of_neg_comp_right (g := signUnitary N j) ?_
  ext U
  have h1 : (U * signUnitary N j).1 i j = -(U.1 i j) := by
    rw [mul_signUnitary_apply]; simp
  have h2 : (U * signUnitary N j).1 k l = U.1 k l := by
    rw [mul_signUnitary_apply]; simp [Ne.symm h]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, ContinuousMap.neg_apply, entryObs_apply, h1, h2]
  ring

/-! ### Equalization and the diagonal value -/

/-- Bi-invariance under permutation unitaries equalizes all the moments
`E |U_{ij}|²`: rows are exchanged by a left swap, columns by a right swap. -/
theorem integral_normSq_entry_eq (E : HaarExpectation N) (i j i' j' : Fin N) :
    E (entryObs N i j * star (entryObs N i j))
      = E (entryObs N i' j' * star (entryObs N i' j')) := by
  -- Row exchange `i ↔ i'` at fixed column `j`.
  have hrow : E (entryObs N i j * star (entryObs N i j))
      = E (entryObs N i' j * star (entryObs N i' j)) := by
    have hswap : (entryObs N i' j * star (entryObs N i' j)).comp
          (ContinuousMap.mulLeft (permUnitary N (Equiv.swap i i')))
        = entryObs N i j * star (entryObs N i j) := by
      ext U
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, entryObs_apply]
      rw [permUnitary_mul_apply, Equiv.swap_apply_right]
    rw [← hswap, E.map_left_mul]
  -- Column exchange `j ↔ j'` at fixed row `i'`.
  have hcol : E (entryObs N i' j * star (entryObs N i' j))
      = E (entryObs N i' j' * star (entryObs N i' j')) := by
    have hswap : (entryObs N i' j' * star (entryObs N i' j')).comp
          (ContinuousMap.mulRight (permUnitary N (Equiv.swap j j')))
        = entryObs N i' j * star (entryObs N i' j) := by
      ext U
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, entryObs_apply]
      rw [mul_permUnitary_apply, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [← hswap, E.map_right_mul]
  exact hrow.trans hcol

/-- **The diagonal value**: `E |U_{ij}|² = 1/N`. Row unitarity
`∑_b U_{ib} conj(U_{ib}) = (U U*)_{ii} = 1` plus equalization over the `N` columns pins
the common moment to `1/N`. (`N > 0` is automatic from `i : Fin N`.) -/
theorem integral_normSq_entry (E : HaarExpectation N) (i j : Fin N) :
    E (entryObs N i j * star (entryObs N i j)) = (N : ℂ)⁻¹ := by
  -- Row unitarity: the observable `∑_b |U_{ib}|²` is the constant `1` in `C(U(N), ℂ)`.
  have hrow : (∑ b, entryObs N i b * star (entryObs N i b))
      = (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) := by
    ext U
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
      entryObs_apply, ContinuousMap.one_apply]
    have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
    calc ∑ b, U.1 i b * star (U.1 i b)
        = (U.1 * star U.1) i i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => by rw [Matrix.star_apply]
      _ = (1 : Matrix (Fin N) (Fin N) ℂ) i i := by rw [hU]
      _ = 1 := Matrix.one_apply_eq i
  have h1 : E (∑ b, entryObs N i b * star (entryObs N i b)) = 1 := by
    rw [hrow, E.map_one]
  have h2 : E (∑ b, entryObs N i b * star (entryObs N i b))
      = ∑ b, E (entryObs N i b * star (entryObs N i b)) :=
    E.map_sum Finset.univ _
  have h3 : ∑ b, E (entryObs N i b * star (entryObs N i b))
      = (N : ℂ) * E (entryObs N i j * star (entryObs N i j)) := by
    rw [Finset.sum_congr rfl fun b _ => integral_normSq_entry_eq E i b i j,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos i).ne'
  have hkey : (N : ℂ) * E (entryObs N i j * star (entryObs N i j)) = 1 := by
    rw [← h3, ← h2, h1]
  exact mul_left_cancel₀ hN (hkey.trans (mul_inv_cancel₀ hN).symm)

/-! ### The bridge theorems -/

/-- **The `n = 1` matrix-entry integral**:
`E (entryObs N i j * star (entryObs N k l)) = δ_{ik} δ_{jl} / N`.

This is the `n = 1` Weingarten moment: the value `1/N` is `Wg^U([1], d) = 1/d` as
displayed in Collins–Matsumoto, arXiv:1701.04493, Example 2.3 (PDF-verified); the
general moment formula it instantiates is Collins–Śniady, arXiv:math-ph/0402073,
Cor. 2.4 / eq. (11) (PDF-verified). At `n = 1` it agrees with this repository's `Weingarten.wg`
at the trivial permutation in the stable range `N > 0`
(documentation-level correspondence; no code dependency). -/
theorem integral_entry_mul_star_entry (E : HaarExpectation N) (i j k l : Fin N) :
    E (entryObs N i j * star (entryObs N k l))
      = if i = k ∧ j = l then (N : ℂ)⁻¹ else 0 := by
  by_cases hik : i = k
  · by_cases hjl : j = l
    · subst hik; subst hjl
      rw [if_pos ⟨rfl, rfl⟩]
      exact integral_normSq_entry E i j
    · rw [if_neg fun hc => hjl hc.2]
      exact integral_entry_mul_star_eq_zero_of_col_ne E i k hjl
  · rw [if_neg fun hc => hik hc.1]
    exact integral_entry_mul_star_eq_zero_of_row_ne E j l hik

/-- **The trace has mean zero**: `E (traceObs N) = 0`. Left translation by the scalar
unitary `-1` negates the trace (the phase argument of Collins–Śniady,
arXiv:math-ph/0402073, eq. (12), PDF-verified, specialized to the central element `-1`
via the factored sign-trick lemma). -/
theorem integral_trace (E : HaarExpectation N) : E (traceObs N) = 0 := by
  refine E.integral_eq_zero_of_neg_comp
    (g := scalarUnitary N (-1) (by rw [star_neg, star_one]; ring)) ?_
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft, ContinuousMap.neg_apply,
    traceObs_apply, scalarUnitary_mul_val, Matrix.trace_smul]
  exact neg_one_smul ℂ (U.1).trace

/-- **Second moment of the trace**: `E (|Tr U|²) = 1`. Expanding both traces into
entries inside `C(U(N), ℂ)`, the `n = 1` entry integral (Collins–Śniady,
arXiv:math-ph/0402073, eq. (11), PDF-verified) collapses the double sum to
`∑_i 1/N = 1`. Requires `N ≠ 0` (for `N = 0` the trace is `0` and the statement would
fail), recorded as `[NeZero N]`. -/
theorem integral_trace_mul_star_trace (E : HaarExpectation N) [NeZero N] :
    E (traceObs N * star (traceObs N)) = 1 := by
  have hexp : traceObs N * star (traceObs N)
      = ∑ i, ∑ k, entryObs N i i * star (entryObs N k k) := by
    ext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, traceObs_apply,
      ContinuousMap.sum_apply, entryObs_apply]
    have ht : (U.1).trace = ∑ i, U.1 i i := rfl
    rw [ht, star_sum, Finset.sum_mul_sum]
  rw [hexp, E.map_sum]
  calc ∑ i, E (∑ k, entryObs N i i * star (entryObs N k k))
      = ∑ i : Fin N, ∑ k : Fin N, if i = k then (N : ℂ)⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [E.map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_entry_mul_star_entry E i i k k]
        simp
    _ = ∑ _i : Fin N, (N : ℂ)⁻¹ := Finset.sum_congr rfl fun i _ => by simp
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- **The trace-pairing workhorse**: for deterministic `A B : Matrix (Fin N) (Fin N) ℂ`,

`E (traceMulObs N A * traceMulStarObs N B) = N⁻¹ * Tr(A B)`.

Reading: two trace factors sharing the single Haar unitary `U` contract into one, at
the cost of `1/N` — the elementary move consumed by the β-expansion coefficients. Mathematically this is the termwise application of the `n = 1` entry
integral (Collins–Śniady, arXiv:math-ph/0402073, Cor. 2.4 / eq. (11), PDF-verified):
`Tr(A U) = ∑_{i,p} A_{ip} U_{pi}` and `Tr(B U*) = ∑_{k,l} B_{kl} conj(U_{kl})`, and the
`δ_{pk} δ_{il} / N` contraction leaves `(1/N) ∑_{i,p} A_{ip} B_{pi} = N⁻¹ Tr(A B)`.
(No `[NeZero N]`: at `N = 0` both sides are `0`.) -/
theorem integral_trace_mul_trace_star (E : HaarExpectation N)
    (A B : Matrix (Fin N) (Fin N) ℂ) :
    E (traceMulObs N A * traceMulStarObs N B) = (N : ℂ)⁻¹ * (A * B).trace := by
  -- Expand both traces into a weighted sum of entry observables inside `C(U(N), ℂ)`.
  have hexp : traceMulObs N A * traceMulStarObs N B
      = ∑ i, ∑ k, ∑ j, ∑ l,
          (A i j * B k l) • (entryObs N j i * star (entryObs N k l)) := by
    ext U
    simp only [ContinuousMap.mul_apply, traceMulObs_apply, traceMulStarObs_apply,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousMap.star_apply,
      entryObs_apply, smul_eq_mul]
    have h1 : (A * U.1).trace = ∑ i, ∑ j, A i j * U.1 j i :=
      Finset.sum_congr rfl fun i _ => Matrix.mul_apply
    have h2 : (B * star U.1).trace = ∑ k, ∑ l, B k l * star (U.1 k l) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      show (B * star U.1) k k = _
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.star_apply]
    rw [h1, h2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      mul_mul_mul_comm _ _ _ _
  -- Linearity: `map_sum` through the outer three sums, `map_weighted_sum` innermost.
  have hlin : E (∑ i, ∑ k, ∑ j, ∑ l,
        (A i j * B k l) • (entryObs N j i * star (entryObs N k l)))
      = ∑ i, ∑ k, ∑ j, ∑ l,
          A i j * B k l * E (entryObs N j i * star (entryObs N k l)) := by
    rw [E.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [E.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [E.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact E.map_weighted_sum Finset.univ _ _
  rw [hexp, hlin]
  -- The Kronecker deltas collapse the quadruple sum to `N⁻¹ * Tr(A B)`.
  calc ∑ i, ∑ k, ∑ j, ∑ l, A i j * B k l * E (entryObs N j i * star (entryObs N k l))
      = ∑ i, ∑ k, ∑ j, ∑ l, A i j * B k l
          * (if j = k ∧ i = l then (N : ℂ)⁻¹ else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [integral_entry_mul_star_entry E j i k l]
    _ = ∑ i, ∑ k, A i k * B k i * (N : ℂ)⁻¹ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        have hj : ∀ j : Fin N,
            ∑ l, A i j * B k l * (if j = k ∧ i = l then (N : ℂ)⁻¹ else 0)
              = if j = k then A i j * B k i * (N : ℂ)⁻¹ else 0 := by
          intro j
          by_cases hjk : j = k
          · subst hjk; simp
          · simp [hjk]
        rw [Finset.sum_congr rfl fun j _ => hj j]
        simp
    _ = (N : ℂ)⁻¹ * (A * B).trace := by
        have htr : (A * B).trace = ∑ i, ∑ k, A i k * B k i :=
          Finset.sum_congr rfl fun i _ => Matrix.mul_apply
        rw [htr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end HaarExpectation

end Weingarten.Haar
