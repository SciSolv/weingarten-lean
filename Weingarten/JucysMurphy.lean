/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Mathlib

/-!
# The symmetric-group algebra and Jucys–Murphy elements (dual convention)

`jm_comm` below is proved and elaborated against Mathlib (`#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`); the repository-wide verification record
is maintained in `scripts/VERIFICATION.md`.

Blueprint nodes: `def:symAlg`, `def:jm`, `rem:dual`, `lem:jm_comm`.

Design record (pinned by `scripts/convention_checks.py`, checks C1–C5): we use the
*dual* Jucys–Murphy elements `K i = ∑_{j > i} (i j)`, so `K (n-1) = 0`. This is the
image of the textbook `J_{n-1-i}` under conjugation by the order-reversing permutation.
The dual convention is chosen because Mathlib's `Equiv.Perm.decomposeFin` splits a
permutation of `Fin (n+1)` at `0`, which makes the Gram-factorization induction
(`Weingarten.gram_eq_prod`) native: the freshly split factor is `N + K 0` on the left,
and the successor embedding shifts `K i ↦ K (i+1)`.

P0b refactor: the coefficient ring is an arbitrary commutative ring `k` (the Jucys
identity is combinatorial — it lives over `ℤ[N]`). Only the ℓ¹ chapter and the parity
chapter pin `k := ℝ`; the below-threshold package (`BelowThreshold.lean`) exploits the
generality, e.g. at `k := ℚ` for the certified cell.
-/

namespace Weingarten

open Equiv Equiv.Perm

/-- The group algebra of the symmetric group on `Fin n` over a commutative ring `k`.
Blueprint: `def:symAlg`. -/
abbrev SymAlg (k : Type*) [CommRing k] (n : ℕ) :=
  MonoidAlgebra k (Equiv.Perm (Fin n))

/-- Dual Jucys–Murphy element `K i = ∑_{j > i} (i j)` in `SymAlg k n`; `K (n-1) = 0`
(empty sum) and `K 0` has `n - 1` terms. Blueprint: `def:jm`. -/
noncomputable def jm (k : Type*) [CommRing k] (n : ℕ) (i : Fin n) : SymAlg k n :=
  ∑ j ∈ Finset.Ioi i, MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i j)

/-- A permutation `τ` fixing every point `≤ i` commutes (in the group algebra) with
`K i = ∑_{m > i} (i m)`: conjugation by `τ` sends `(i m)` to `(i (τ m))`, and `τ`
permutes the index set `Ioi i`, so the defining sum is preserved. The pairwise
non-commuting transpositions making up `K i` only commute with `τ` *as a sum*. -/
private lemma commute_of_fixing (k : Type*) [CommRing k] (n : ℕ) (i : Fin n)
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ m, m ≤ i → τ m = m) :
    Commute (MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ) (jm k n i) := by
  have hfix' : ∀ x, τ x ≤ i → x ≤ i := fun x hx => (τ.injective (hτ (τ x) hx)) ▸ hx
  have hmaps : ∀ m, i < m → i < τ m := by
    intro m hm
    by_contra h
    exact absurd (hfix' m (not_lt.mp h)) (not_le.mpr hm)
  have himg : (Finset.Ioi i).image τ = Finset.Ioi i := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      rw [Finset.mem_Ioi] at hm ⊢
      exact hmaps m hm
    · exact le_of_eq (Finset.card_image_of_injective _ τ.injective).symm
  show MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ * jm k n i
    = jm k n i * MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ
  unfold jm
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ m ∈ Finset.Ioi i, MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ
          * MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i m)
      = ∑ m ∈ Finset.Ioi i, MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i (τ m))
          * MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← map_mul, mul_swap_eq_swap_mul, hτ i (le_refl i), map_mul]
    _ = ∑ x ∈ (Finset.Ioi i).image τ,
          MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i x)
          * MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ :=
        (Finset.sum_image (f := fun x => MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i x)
          * MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ) τ.injective.injOn).symm
    _ = ∑ m ∈ Finset.Ioi i, MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i m)
          * MonoidAlgebra.of k (Equiv.Perm (Fin n)) τ := by rw [himg]

/-- The dual Jucys–Murphy elements commute pairwise. Used only to reorder factors in
the Neumann expansion (`Weingarten.wg_expansion`); the factorization fixes one order
and never needs it. Blueprint: `lem:jm_comm`. -/
theorem jm_comm (k : Type*) [CommRing k] (n : ℕ) (i j : Fin n) :
    Commute (jm k n i) (jm k n j) := by
  have comm_lt : ∀ a b : Fin n, a < b → Commute (jm k n a) (jm k n b) := by
    intro a b hab
    refine Commute.sum_right (Finset.Ioi b) _ (jm k n a) ?_
    intro l hl
    rw [Finset.mem_Ioi] at hl
    refine (commute_of_fixing k n a (Equiv.swap b l) ?_).symm
    intro m hm
    exact Equiv.swap_apply_of_ne_of_ne (ne_of_lt (lt_of_le_of_lt hm hab))
      (ne_of_lt (lt_of_le_of_lt hm (lt_trans hab hl)))
  rcases lt_trichotomy i j with h | h | h
  · exact comm_lt i j h
  · subst h; exact Commute.refl _
  · exact (comm_lt j i h).symm

end Weingarten
