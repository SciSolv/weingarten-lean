/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.SumRules

/-!
# Small-`n` values of the unitary Weingarten function

Explicit evaluations of this repository's Weingarten function `Weingarten.wg` at
`n = 1` and `n = 2`:

* `Wg(1, N) = N⁻¹`;
* `Wg(id, N) = (N² − 1)⁻¹` and `Wg((0 1), N) = −(N (N² − 1))⁻¹`.

The `n = 2` values are obtained by solving the 2×2 linear system formed by the two
character sum rules of `Weingarten.SumRules` — `Weingarten.sum_wg`
(`Σ_σ Wg(σ) = ∏ (N + m)⁻¹`) and `Weingarten.sum_sgn_wg`
(`Σ_σ sgn(σ)·Wg(σ) = ∏ (N − m)⁻¹`) — over the two-element group `Perm (Fin 2)`:
no characters, no matrix inversion.

Values verified against the literature (all PDF-verified): Collins–Matsumoto,
arXiv:1701.04493, Example 2.3 (`Wg([1,2], d) = 1/(d²−1)`,
`Wg([2,1], d) = −1/(d(d²−1))`); Collins–Śniady, arXiv:math-ph/0402073, p. 6 worked
example (`∫ |U₁₁|⁴ = 2/(d(d+1))`, reproduced as the cross-check below); Drouffe–Zuber,
Phys. Rep. 102 (1983), Table (A.26). These constants are exactly what the `n = 2`
Haar-moment bridge consumes.
-/

namespace Weingarten.Haar

open Weingarten

/-- The two-element group `Perm (Fin 2)` is exactly `{1, swap 0 1}`. -/
theorem perm_fin_two_univ :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide

/-- `Wg(σ, N) = N⁻¹` at `n = 1` (every `σ : Perm (Fin 1)` is the identity). -/
theorem wg_one_apply (N : ℝ) (hN : ((1 : ℕ) : ℝ) - 1 < N) (σ : Equiv.Perm (Fin 1)) :
    wg 1 N hN σ = N⁻¹ := by
  have hσ : σ = 1 := Equiv.ext fun x => Subsingleton.elim (σ x) x
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by decide
  have hS := sum_wg 1 N hN
  rw [huniv, Finset.sum_singleton, Finset.prod_range_one] at hS
  rw [hσ, hS]
  norm_num

/-- Nonzero denominators in the stable range `1 < N`. -/
private theorem denoms (N : ℝ) (h1 : 1 < N) :
    N ≠ 0 ∧ N - 1 ≠ 0 ∧ N + 1 ≠ 0 ∧ N ^ 2 - 1 ≠ 0 := by
  have h0 : N ≠ 0 := by linarith
  have hm : N - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hp : N + 1 ≠ 0 := by intro h; linarith [eq_neg_of_add_eq_zero_left h]
  refine ⟨h0, hm, hp, ?_⟩
  have hfac : N ^ 2 - 1 = (N - 1) * (N + 1) := by ring
  rw [hfac]; exact mul_ne_zero hm hp

/-- The 2×2 linear system for the two `n = 2` Weingarten values, extracted from the
rising and falling sum rules. -/
private theorem wg_two_system (N : ℝ) (hN : ((2 : ℕ) : ℝ) - 1 < N) :
    wg 2 N hN 1 + wg 2 N hN (Equiv.swap 0 1) = N⁻¹ * (N + 1)⁻¹ ∧
    wg 2 N hN 1 - wg 2 N hN (Equiv.swap 0 1) = N⁻¹ * (N - 1)⁻¹ := by
  have hS := sum_wg 2 N hN
  have hD := sum_sgn_wg 2 N hN
  rw [perm_fin_two_univ, Finset.sum_insert (by decide), Finset.sum_singleton] at hS hD
  have hprod_add : ∏ m ∈ Finset.range 2, (N + (m : ℝ))⁻¹ = N⁻¹ * (N + 1)⁻¹ := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    norm_num
  have hprod_sub : ∏ m ∈ Finset.range 2, (N - (m : ℝ))⁻¹ = N⁻¹ * (N - 1)⁻¹ := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    norm_num
  rw [hprod_add] at hS
  rw [hprod_sub, Equiv.Perm.sign_one, Equiv.Perm.sign_swap (by decide)] at hD
  push_cast at hD
  refine ⟨hS, ?_⟩
  linarith

/-- **`Wg(id, N) = (N² − 1)⁻¹` at `n = 2`** (Collins–Matsumoto arXiv:1701.04493,
Example 2.3; derived here from the upstream sum rules). -/
theorem wg_two_one (N : ℝ) (hN : ((2 : ℕ) : ℝ) - 1 < N) :
    wg 2 N hN 1 = (N ^ 2 - 1)⁻¹ := by
  obtain ⟨hS, hD⟩ := wg_two_system N hN
  have h1 : (1 : ℝ) < N := by push_cast at hN; linarith
  obtain ⟨h0, hm, hp, hq⟩ := denoms N h1
  have hx : wg 2 N hN 1 = (N⁻¹ * (N + 1)⁻¹ + N⁻¹ * (N - 1)⁻¹) / 2 := by linarith
  rw [hx]
  field_simp
  ring

/-- **`Wg((0 1), N) = −(N (N² − 1))⁻¹` at `n = 2`** (Collins–Matsumoto
arXiv:1701.04493, Example 2.3; derived here from the upstream sum rules). -/
theorem wg_two_swap (N : ℝ) (hN : ((2 : ℕ) : ℝ) - 1 < N) :
    wg 2 N hN (Equiv.swap 0 1) = -(N * (N ^ 2 - 1))⁻¹ := by
  obtain ⟨hS, hD⟩ := wg_two_system N hN
  have h1 : (1 : ℝ) < N := by push_cast at hN; linarith
  obtain ⟨h0, hm, hp, hq⟩ := denoms N h1
  have hy : wg 2 N hN (Equiv.swap 0 1)
      = (N⁻¹ * (N + 1)⁻¹ - N⁻¹ * (N - 1)⁻¹) / 2 := by linarith
  rw [hy]
  field_simp
  ring

/-- Cross-check against Collins–Śniady arXiv:math-ph/0402073, p. 6:
`2·Wg(id) + 2·Wg(swap) = 2/(N(N+1))` — the Weingarten evaluation of `∫ |U₁₁|⁴`. -/
example (N : ℝ) (hN : ((2 : ℕ) : ℝ) - 1 < N) :
    2 * wg 2 N hN 1 + 2 * wg 2 N hN (Equiv.swap 0 1) = 2 * (N * (N + 1))⁻¹ := by
  rw [wg_two_one N hN, wg_two_swap N hN]
  have h1 : (1 : ℝ) < N := by push_cast at hN; linarith
  obtain ⟨h0, hm, hp, hq⟩ := denoms N h1
  field_simp
  ring

/-- The signs `Wg(id) > 0` and `Wg(swap) < 0` in the stable range — re-proved here from
the closed forms, consistent with (though not invoking) the upstream parity theorem
`Weingarten.wg_sign`. -/
example (N : ℝ) (hN : ((2 : ℕ) : ℝ) - 1 < N) :
    0 < wg 2 N hN 1 ∧ wg 2 N hN (Equiv.swap 0 1) < 0 := by
  have h1 : (1 : ℝ) < N := by push_cast at hN; linarith
  constructor
  · rw [wg_two_one N hN]
    have h2 : (0 : ℝ) < N ^ 2 - 1 := by nlinarith
    exact inv_pos.mpr h2
  · rw [wg_two_swap N hN]
    have h2 : (0 : ℝ) < N * (N ^ 2 - 1) := by nlinarith
    exact neg_lt_zero.mpr (inv_pos.mpr h2)

/-- Numeric spot check at `N = 3`: `Wg(id, 3) = 1/8` and `Wg((0 1), 3) = −1/24` —
exercises both values independently of the sum rules' algebraic form. -/
example : wg 2 (3 : ℝ) (by norm_num) 1 = 1 / 8 := by
  rw [wg_two_one]; norm_num

example : wg 2 (3 : ℝ) (by norm_num) (Equiv.swap 0 1) = -(1 / 24) := by
  rw [wg_two_swap]; norm_num

end Weingarten.Haar
