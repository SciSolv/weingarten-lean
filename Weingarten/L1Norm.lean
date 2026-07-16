/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Homs

/-!
# The scoped ℓ¹ structure and Neumann invertibility

All statements below are proved and elaborated against Mathlib (`#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`). Blueprint: `def:l1`, `lem:jm_norm`,
`lem:unit`.

Mathlib has no normed structure on `MonoidAlgebra`. Following the `Matrix` precedent of
norms-as-non-instances, **every** ℓ¹ instance of this module is *scoped* to the namespace
`Weingarten.L1` — the norm `L1.instNorm` (`‖x‖ = ∑ σ, |x σ|`), the normed-ring structure
`instL1NormedRing` (submultiplicative by the finite Young inequality for group
convolution, `L1.l1_norm_mul_le`), the normed-space structure `instL1NormedSpace`, and
the completeness instance `instL1Complete` (`SymAlg ℝ n` is finite-dimensional, hence
complete). None of them is global; consumers activate all four via
`open scoped Weingarten.L1`.

Since `‖K i‖ = n - 1 - i ≤ n - 1 < N`, every `N + K i` is a unit by the Neumann
(geometric) series, and the Gram element is a unit through the factorization.
-/

open scoped BigOperators
open Equiv

namespace Weingarten

namespace L1

/-- ℓ¹ norm on the group algebra: `‖x‖ = ∑ σ, |x σ|`. Scoped to `Weingarten.L1`
(`Matrix` norms-as-non-instances precedent); activate via `open scoped Weingarten.L1`. -/
noncomputable scoped instance instNorm (n : ℕ) : Norm (SymAlg ℝ n) :=
  ⟨fun x => ∑ σ : Equiv.Perm (Fin n), |x σ|⟩

@[simp] lemma norm_eq (n : ℕ) (x : SymAlg ℝ n) :
    ‖x‖ = ∑ σ : Equiv.Perm (Fin n), |x σ| := rfl

/-- The four normed-space core axioms for the ℓ¹ norm. -/
lemma core (n : ℕ) : NormedSpace.Core ℝ (SymAlg ℝ n) where
  norm_nonneg x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  norm_smul c x := by
    rw [norm_eq, norm_eq, Real.norm_eq_abs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (c • x) σ = c * x σ from rfl, abs_mul]
  norm_triangle x y := by
    rw [norm_eq, norm_eq, norm_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [show (x + y) σ = x σ + y σ from rfl]
    exact abs_add_le (x σ) (y σ)
  norm_eq_zero_iff x := by
    rw [norm_eq, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _]
    constructor
    · intro h; ext σ
      show x σ = 0
      exact abs_eq_zero.mp (h σ (Finset.mem_univ σ))
    · intro h σ _; rw [h]; exact abs_eq_zero.mpr rfl

/-- Convolution formula for the group algebra over the (Fintype) group `Perm (Fin n)`. -/
lemma mul_apply_conv (n : ℕ) (x y : SymAlg ℝ n) (τ : Equiv.Perm (Fin n)) :
    (x * y) τ = ∑ a : Equiv.Perm (Fin n), x a * y (a⁻¹ * τ) := by
  rw [MonoidAlgebra.mul_apply, Finsupp.sum_fintype _ _ (fun a => by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.sum_fintype _ _ (fun b => by simp)]
  rw [Fintype.sum_eq_single (a⁻¹ * τ)]
  · simp
  · intro b hb
    have : a * b ≠ τ := fun h => hb (by rw [← h]; group)
    simp [this]

/-- **Submultiplicativity** of the ℓ¹ norm: the finite Young inequality for convolution. -/
lemma l1_norm_mul_le (n : ℕ) (x y : SymAlg ℝ n) :
    (∑ τ : Equiv.Perm (Fin n), |(x * y) τ|)
      ≤ (∑ σ : Equiv.Perm (Fin n), |x σ|) * (∑ σ : Equiv.Perm (Fin n), |y σ|) := by
  calc ∑ τ : Equiv.Perm (Fin n), |(x * y) τ|
      = ∑ τ : Equiv.Perm (Fin n), |∑ a : Equiv.Perm (Fin n), x a * y (a⁻¹ * τ)| := by
        simp_rw [mul_apply_conv]
    _ ≤ ∑ τ : Equiv.Perm (Fin n), ∑ a : Equiv.Perm (Fin n), |x a| * |y (a⁻¹ * τ)| :=
        Finset.sum_le_sum fun τ _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (by simp_rw [abs_mul]; rfl)
    _ = ∑ a : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), |x a| * |y (a⁻¹ * τ)| :=
        Finset.sum_comm
    _ = ∑ a : Equiv.Perm (Fin n), |x a| * ∑ τ : Equiv.Perm (Fin n), |y (a⁻¹ * τ)| := by
        simp_rw [← Finset.mul_sum]
    _ = ∑ a : Equiv.Perm (Fin n), |x a| * ∑ τ : Equiv.Perm (Fin n), |y τ| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft a⁻¹) (fun τ => |y τ|)
    _ = (∑ σ : Equiv.Perm (Fin n), |x σ|) * ∑ σ : Equiv.Perm (Fin n), |y σ| := by
        rw [← Finset.sum_mul]

end L1

open L1 in
/-- ℓ¹ normed-ring structure on `SymAlg ℝ n`. Deliberately **not** a global instance
(Mathlib `Matrix` precedent); activate via `open scoped Weingarten.L1`. Blueprint:
`def:l1`. -/
@[reducible] noncomputable def instL1NormedRing (n : ℕ) : NormedRing (SymAlg ℝ n) :=
  { NormedAddCommGroup.ofCore (L1.core n), (inferInstance : Ring (SymAlg ℝ n)) with
    norm_mul_le := fun x y => L1.l1_norm_mul_le n x y }

scoped[Weingarten.L1] attribute [instance] Weingarten.instL1NormedRing

open scoped Weingarten.L1

/-- Companion normed-`ℝ`-space structure (same norm), giving completeness. Scoped to
`Weingarten.L1` like the ring structure; activate via `open scoped Weingarten.L1`. -/
@[reducible] noncomputable def instL1NormedSpace (n : ℕ) : NormedSpace ℝ (SymAlg ℝ n) :=
  NormedSpace.ofCore (L1.core n)

scoped[Weingarten.L1] attribute [instance] Weingarten.instL1NormedSpace

open scoped Weingarten.L1

/-- Completeness of the (finite-dimensional) ℓ¹ algebra. Scoped to `Weingarten.L1`
(it presupposes the scoped metric); activate via `open scoped Weingarten.L1`. -/
@[reducible] def instL1Complete (n : ℕ) : CompleteSpace (SymAlg ℝ n) :=
  FiniteDimensional.complete ℝ (SymAlg ℝ n)

scoped[Weingarten.L1] attribute [instance] Weingarten.instL1Complete

open scoped Weingarten.L1

/-- `‖K i‖ = #{j > i} = n - 1 - i` (cardinality form avoids ℕ-subtraction).
Blueprint: `lem:jm_norm`. -/
theorem jm_norm (n : ℕ) (i : Fin n) :
    ‖jm ℝ n i‖ = ((Finset.Ioi i).card : ℝ) := by
  rw [L1.norm_eq]
  have hnn : ∀ σ, 0 ≤ (jm ℝ n i) σ := by
    intro σ
    unfold Weingarten.jm
    rw [show (∑ j ∈ Finset.Ioi i, MonoidAlgebra.of ℝ (Perm (Fin n)) (swap i j)) σ
        = ∑ j ∈ Finset.Ioi i, (MonoidAlgebra.of ℝ (Perm (Fin n)) (swap i j)) σ from
      Finsupp.finsetSum_apply _ _ _]
    apply Finset.sum_nonneg
    intro j _
    rw [MonoidAlgebra.of_apply, Finsupp.single_apply]
    split <;> norm_num
  rw [Finset.sum_congr rfl (fun σ _ => abs_of_nonneg (hnn σ))]
  rw [← aug_apply, aug_jm]

/-- The key Neumann bound `‖N⁻¹ • K i‖ < 1` in the stable range. Reused by
`isUnit_add_jm` and by the parity package's per-factor geometric series. -/
theorem norm_smul_jm_lt_one (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (i : Fin n) :
    ‖(N⁻¹ : ℝ) • jm ℝ n i‖ < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast i.pos
  have hNpos : 0 < N := by linarith
  rw [norm_smul, jm_norm, Real.norm_eq_abs, abs_inv, abs_of_pos hNpos,
    ← div_eq_inv_mul, div_lt_one hNpos, Fin.card_Ioi]
  have hcast : ((n - 1 - (i : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
    calc ((n - 1 - (i : ℕ) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ = (n : ℝ) - 1 := by rw [Nat.cast_sub (by exact_mod_cast i.pos), Nat.cast_one]
  linarith

/-- Each `N + K i` is a unit once `n - 1 < N` (Neumann series, `‖K i / N‖ < 1`).
Blueprint: `lem:unit`. -/
theorem isUnit_add_jm (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (i : Fin n) :
    IsUnit (algebraMap ℝ (SymAlg ℝ n) N + jm ℝ n i) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast i.pos
  have hN0 : N ≠ 0 := ne_of_gt (by linarith)
  have hfac : algebraMap ℝ (SymAlg ℝ n) N + jm ℝ n i
      = algebraMap ℝ (SymAlg ℝ n) N * (1 - (-(N⁻¹ • jm ℝ n i))) := by
    rw [mul_sub, mul_one, mul_neg, sub_neg_eq_add, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  rw [hfac]
  apply IsUnit.mul
  · exact (isUnit_iff_ne_zero.mpr hN0).map (algebraMap ℝ (SymAlg ℝ n))
  · refine (Units.oneSub _ ?_).isUnit
    rw [norm_neg]
    exact norm_smul_jm_lt_one n N hN i

/-- The Gram element is a unit in the stable range (product of units, via
`gram_eq_prod`). -/
theorem isUnit_gram (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    IsUnit (gram ℝ n N) := by
  rw [gram_eq_prod]
  unfold Weingarten.gramProd
  apply List.prod_isUnit
  intro m hm
  rw [List.mem_map] at hm
  obtain ⟨i, _, rfl⟩ := hm
  exact isUnit_add_jm n N hN i

end Weingarten
