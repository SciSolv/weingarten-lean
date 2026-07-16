/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.WeingartenFunction
import Weingarten.BelowThreshold

/-!
# The two sum rules in the stable range

Proved and elaborated (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
Blueprint: `lem:penrose_of_unit`, `thm:rising`, `thm:falling`.

After the P0b restructure the stable-range sum rules are corollaries of the
Penrose-conditional rules of `BelowThreshold.lean`: a unit's inverse trivially
satisfies both Penrose equations, and in the stable range `n - 1 < N` both the rising
and falling factorials are strictly positive. The analytic chapter (`L1Norm.lean`)
is thereby needed only for *existence* of the inverse and for the parity theorem.
-/

open scoped BigOperators

namespace Weingarten

/-- The stable Weingarten element is a Penrose partner of the Gram element — a unit's
inverse satisfies both equations trivially. Blueprint: `lem:penrose_of_unit`. -/
theorem isPenrosePair_wgElement (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    IsPenrosePair (gram ℝ n N) (wgElement n N hN) := by
  refine ⟨?_, ?_⟩
  · rw [gram_mul_wgElement, one_mul]
  · rw [wgElement_mul_gram, one_mul]

/-- **Rising sum rule.** Blueprint: `thm:rising` (instantiates
`sum_wg_of_penrose` at `isPenrosePair_wgElement`; `∏ (N + m) > 0` in the stable
range). -/
theorem sum_wg (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    ∑ σ : Equiv.Perm (Fin n), wg n N hN σ
      = ∏ m ∈ Finset.range n, (N + (m : ℝ))⁻¹ := by
  have hr : ∏ m ∈ Finset.range n, (N + (m : ℝ)) ≠ 0 := by
    refine ne_of_gt (Finset.prod_pos fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hn : 1 ≤ n := by omega
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have key := sum_wg_of_penrose (isPenrosePair_wgElement n N hN) hr
  rw [aug_apply] at key
  rw [show (∑ σ : Equiv.Perm (Fin n), wg n N hN σ)
        = ∑ σ : Equiv.Perm (Fin n), (wgElement n N hN) σ from rfl, key,
    Finset.prod_inv_distrib]

/-- **Falling sum rule.** Blueprint: `thm:falling` (instantiates
`sum_sgn_wg_of_penrose`; `∏ (N - m) > 0` in the stable range). -/
theorem sum_sgn_wg (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ
      = ∏ m ∈ Finset.range n, (N - (m : ℝ))⁻¹ := by
  have hf : ∏ m ∈ Finset.range n, (N - (m : ℝ)) ≠ 0 := by
    refine ne_of_gt (Finset.prod_pos fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hmn : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  have key := sum_sgn_wg_of_penrose (isPenrosePair_wgElement n N hN) hf
  rw [sgnHom_apply] at key
  rw [show (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * wg n N hN σ)
        = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (wgElement n N hN) σ
        from rfl, key, Finset.prod_inv_distrib]

end Weingarten
