/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.MatrixEntryIntegrals

/-!
# Conjugation invariance for the Haar expectation

Conjugation `U ↦ g·U·g⁻¹` composes the two invariance fields of
`Weingarten.Haar.HaarExpectation`, so the Haar state is conjugation-invariant with **no new
axiom**: `E (f ∘ conj_g) = E f` (`HaarExpectation.map_conj`). In the lattice
transfer-matrix application that motivated this file, this is the observable side of
the Gauss-law symmetry — the transfer operator commutes with time-independent gauge
transformations: Creutz, *Gauge fixing, the transfer
matrix, and confinement on a lattice*, Phys. Rev. D 15 (1977) 1128, Eqs. (5.29)–(5.30)
(author's self-archived scan, PDF-verified), and Lüscher, *Construction of a
selfadjoint, strictly positive transfer matrix for Euclidean lattice gauge theories*,
Comm. Math. Phys. 54 (1977) 283, Proposition 1(b) (open-access PDF, verified).

## Contents

* `conjMap N g` — conjugation by `g` as a continuous self-map of `U(N)`, and
  `translateConj N g` — precomposition with it, as a ⋆-algebra homomorphism of the
  observable algebra (so it distributes over products, powers, stars and sums for
  free, exactly like `translateLeft`/`translateRight`).
* `HaarExpectation.map_conj` / `map_translateConj` — conjugation invariance.
* `HaarExpectation.integral_eq_zero_of_charge_conj` — the **conjugation charge kill**:
  if conjugating by some `g` rescales an observable by a factor `w ≠ 1`, its
  expectation vanishes. This is the workhorse behind the entry classification of
  `Weingarten.Haar.TraceEntryMoments`: conjugation by a diagonal phase
  leaves class functions fixed while rescaling an off-diagonal entry factor.
* Transformation laws of the generating observables under conjugation by the
  structured unitaries: `entryObs_comp_conj_phase`, `entryObs_comp_conj_perm`, and
  `traceObs_comp_conj` (the trace is a class function).
-/

namespace Weingarten.Haar

open Matrix

variable {N : ℕ}

/-! ### Conjugation as a continuous map and as a ⋆-homomorphism -/

/-- Conjugation `U ↦ g·U·g⁻¹` by a fixed unitary `g`, as a continuous self-map of
`U(N)` — the composition of left translation by `g` with right translation by `g⁻¹`.
Physically: a time-independent gauge transformation acting on a single link
(Creutz PRD 15 (1977), Eqs. (5.29)–(5.30); Lüscher CMP 54 (1977), Prop. 1(b)). -/
noncomputable def conjMap (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, Matrix.unitaryGroup (Fin N) ℂ) :=
  (ContinuousMap.mulLeft g).comp (ContinuousMap.mulRight g⁻¹)

@[simp] theorem conjMap_apply (N : ℕ) (g U : Matrix.unitaryGroup (Fin N) ℂ) :
    conjMap N g U = g * U * g⁻¹ :=
  (mul_assoc g U g⁻¹).symm

/-- Conjugation translation `f ↦ f ∘ (g · g⁻¹)`, as a ⋆-algebra homomorphism of
observables — the conjugation sibling of `translateLeft`/`translateRight`. -/
noncomputable def translateConj (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) →⋆ₐ[ℂ] C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ (conjMap N g)

@[simp] theorem translateConj_apply (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    translateConj N g f = f.comp (conjMap N g) := rfl

namespace HaarExpectation

/-- **Conjugation invariance** of the Haar expectation: `E (f ∘ conj_g) = E f`.
No new axiom — the conjugation is the composite of the two recorded invariances.
This is the Haar-state face of the Gauss-law commutation `[T, R(V)] = 0`
(Creutz PRD 15 (1977), Eqs. (5.29)–(5.30); Lüscher CMP 54 (1977), Prop. 1(b)). -/
theorem map_conj (E : HaarExpectation N) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (f.comp (conjMap N g)) = E f := by
  have h : f.comp (conjMap N g)
      = (f.comp (ContinuousMap.mulLeft g)).comp (ContinuousMap.mulRight g⁻¹) := rfl
  rw [h, E.map_right_mul, E.map_left_mul]

/-- Conjugation invariance, phrased through the bundled ⋆-homomorphism. -/
theorem map_translateConj (E : HaarExpectation N) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (translateConj N g f) = E f :=
  E.map_conj g f

/-- **The conjugation charge kill**: if conjugation by some unitary `g` merely
rescales the observable by a factor `w ≠ 1`, then its expectation vanishes.
Same algebra as `integral_eq_zero_of_charge`, powered by `map_conj`. -/
theorem integral_eq_zero_of_charge_conj (E : HaarExpectation N)
    {g : Matrix.unitaryGroup (Fin N) ℂ} {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    {w : ℂ} (hw : w ≠ 1) (h : f.comp (conjMap N g) = w • f) : E f = 0 := by
  have h1 : E f = w * E f := by
    calc E f = E (f.comp (conjMap N g)) := (E.map_conj g f).symm
      _ = E (w • f) := by rw [h]
      _ = w * E f := E.map_smul w f
  have h2 : (w - 1) * E f = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hw
  · exact h3

end HaarExpectation

/-! ### Inverses of the structured unitaries

Conjugation needs `g⁻¹` in entry coordinates; for the diagonal phase and permutation
unitaries the inverses are again of the same shape. -/

/-- The inverse of a diagonal phase unitary is the diagonal phase at the conjugate
scalar: `(phaseUnitary N r z)⁻¹ = phaseUnitary N r (star z)`. -/
theorem phaseUnitary_inv (N : ℕ) (r : Fin N) (z : ℂ) (hz : z * star z = 1) :
    (phaseUnitary N r z hz)⁻¹
      = phaseUnitary N r (star z) (by rw [star_star, mul_comm]; exact hz) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.UnitaryGroup.mul_val, phaseUnitary_val, phaseUnitary_val,
    Matrix.diagonal_mul_diagonal, Matrix.UnitaryGroup.one_val, ← Matrix.diagonal_one]
  congr 1
  funext x
  have hz' : z * (starRingEnd ℂ) z = 1 := hz
  by_cases h : x = r
  · simp [h, hz']
  · simp [h]

@[simp] theorem permUnitary_val (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (permUnitary N σ).1 = σ.permMatrix ℂ := rfl

/-- The inverse of a permutation unitary is the permutation unitary of the inverse
permutation. -/
theorem permUnitary_inv (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (permUnitary N σ)⁻¹ = permUnitary N σ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.UnitaryGroup.mul_val, permUnitary_val, permUnitary_val,
    Matrix.UnitaryGroup.one_val, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

/-! ### Transformation laws of the generating observables under conjugation -/

/-- Conjugating an entry observable by a diagonal phase at position `r` rescales it
by the net charge weight: row `i` picks up `z` when `i = r`, column `j` picks up
`star z` when `j = r`. Off-diagonal entries (`i ≠ j`) therefore acquire a nontrivial
phase while every class function stays fixed — the input to the conjugation charge
kill. -/
theorem entryObs_comp_conj_phase (r i j : Fin N) (z : ℂ) (hz : z * star z = 1) :
    (entryObs N i j).comp (conjMap N (phaseUnitary N r z hz))
      = ((if i = r then z else 1) * (if j = r then star z else 1)) • entryObs N i j := by
  ext U
  simp only [ContinuousMap.comp_apply, conjMap_apply, ContinuousMap.smul_apply,
    entryObs_apply, smul_eq_mul, phaseUnitary_inv]
  rw [mul_phaseUnitary_apply, phaseUnitary_mul_apply]
  ring

/-- Conjugating an entry observable by a permutation unitary permutes both indices:
`(U ↦ (σ·U·σ⁻¹)_{ij}) = (U ↦ U_{σ(i), σ(j)})`. -/
theorem entryObs_comp_conj_perm (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    (entryObs N i j).comp (conjMap N (permUnitary N σ))
      = entryObs N (σ i) (σ j) := by
  ext U
  simp only [ContinuousMap.comp_apply, conjMap_apply, entryObs_apply, permUnitary_inv]
  rw [mul_permUnitary_apply, permUnitary_mul_apply, Equiv.Perm.inv_def,
    Equiv.symm_symm]

/-- **The trace is a class function**: conjugation by any unitary fixes `traceObs`.
Cyclicity of the trace, pointwise. -/
theorem traceObs_comp_conj (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (traceObs N).comp (conjMap N g) = traceObs N := by
  ext U
  simp only [ContinuousMap.comp_apply, conjMap_apply, traceObs_apply,
    Matrix.UnitaryGroup.mul_val]
  rw [Matrix.trace_mul_cycle]
  have h : (g⁻¹ : Matrix.unitaryGroup (Fin N) ℂ).1 * g.1 = 1 := by
    rw [← Matrix.UnitaryGroup.mul_val, inv_mul_cancel, Matrix.UnitaryGroup.one_val]
  rw [h, one_mul]

/-- The starred trace is a class function as well (via the ⋆-homomorphism). -/
theorem star_traceObs_comp_conj (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (star (traceObs N)).comp (conjMap N g) = star (traceObs N) := by
  have h : translateConj N g (star (traceObs N))
      = star (translateConj N g (traceObs N)) :=
    map_star (translateConj N g) (traceObs N)
  simpa only [translateConj_apply, traceObs_comp_conj g] using h

end Weingarten.Haar
