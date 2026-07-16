/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Parity

/-!
# Absolute sum and the cancellation ratio

Proved and elaborated (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
Blueprint: `thm:closed_form`.

The parity sign theorem (`wg_sign`) gives `|Wg σ| = sgn(σ) · Wg σ`, which converts the
falling sum rule into `∑ |Wg| = ∏ (N - j)⁻¹`; dividing the rising rule by this absolute sum
yields the exact cancellation ratio `∏ (N - j) / (N + j)`. Stable range only: the companion
note's below-threshold `N = 2` anchors for `n ≥ 3` use the restricted definition and are out
of scope here (only the `(2,3)` cell is certified, in `Cell23.lean`).
-/

namespace Weingarten

open scoped BigOperators
open Equiv Equiv.Perm

/-- Per-`σ` parity identity: `|Wg σ| = sgn(σ) · Wg σ`, since `(-1)^|σ| Wg σ > 0` (`wg_sign`)
and `(sgn σ : ℝ) = (-1)^|σ|` (`sign_eq_neg_one_pow`). -/
theorem abs_wg_eq (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    |wg n N hN σ| = ((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ := by
  have hsign : ((Equiv.Perm.sign σ : ℤ) : ℝ) = (-1 : ℝ) ^ (n - cycleCount n σ) := by
    rw [sign_eq_neg_one_pow n σ]; push_cast; ring
  have hpos : 0 < ((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ := by
    rw [hsign]; exact wg_sign n N hN σ
  have habs1 : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  calc |wg n N hN σ|
      = |((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ| := by
            rw [abs_mul, habs1, one_mul]
    _ = ((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ := abs_of_pos hpos

/-- `∑ σ, |Wg σ| = ∏ (N - j)⁻¹` (falling rule + parity). Blueprint: `thm:closed_form`. -/
theorem sum_abs_wg (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    ∑ σ : Equiv.Perm (Fin n), |wg n N hN σ|
      = ∏ j ∈ Finset.range n, (N - (j : ℝ))⁻¹ := by
  rw [Finset.sum_congr rfl (fun σ _ => abs_wg_eq n N hN σ)]
  exact sum_sgn_wg n N hN

/-- **Cancellation ratio in closed form.** Blueprint: `thm:closed_form`. -/
theorem cancellation_ratio (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    (∑ σ : Equiv.Perm (Fin n), wg n N hN σ)
        / (∑ σ : Equiv.Perm (Fin n), |wg n N hN σ|)
      = ∏ j ∈ Finset.range n, (N - (j : ℝ)) / (N + (j : ℝ)) := by
  rw [sum_wg n N hN, sum_abs_wg n N hN, Finset.prod_div_distrib,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib, inv_div_inv]

end Weingarten
