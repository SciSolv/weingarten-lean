/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Mathlib

/-!
# Cycle count and the `decomposeFin` splice rule

`cycleCount n σ` is the number of orbits of `σ` on `Fin n`, with fixed points counted
as 1-cycles, so `cycleCount n 1 = n`. Mathlib's `Equiv.Perm.cycleType` excludes fixed
points, hence the sum of two terms below.

The splice rule is the hardest purely combinatorial step of the project, verified
exhaustively for `n + 1 ≤ 6` by check C2: writing
`σ = Equiv.Perm.decomposeFin.symm (p, e)`, the point `0` either becomes a fresh fixed
point (`p = 0`, one extra orbit) or is spliced into the orbit of `p` (`p ≠ 0`, count
unchanged).

The proof factors `decomposeFin.symm (p, e) = swap 0 p · ι(e)` where `ι` fixes `0` and
acts on successors. `ι` preserves the cycle type (`cycleType_iota`); the splice itself is
the merge lemma `cycleCount_swap_mul`: left-multiplying by a transposition through a fixed
point lowers the orbit count by exactly one. The merge argument is proved once, in its
natural generality (any fintype), as `gcount_swap_mul`; the `Fin` form and the `RSS`
re-exports in `Weingarten.OrthogonalGram` derive from it.
-/

namespace Weingarten

open Equiv Equiv.Perm

/-- Number of orbits of `σ` on `Fin n`, counting fixed points.
Blueprint: `def:cycleCount`. -/
def cycleCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun x => σ x = x).card + σ.cycleType.card

/-- Sanity anchor: the identity has `n` orbits. -/
theorem cycleCount_one (n : ℕ) : cycleCount n 1 = n := by
  simp [cycleCount, Equiv.Perm.cycleType_one]

/-- Reformulation: `cycleCount n σ = (n - cycleType.sum) + cycleType.card`, manifestly a
function of the cycle type alone (the fixed-point count is `n - support.card =
n - cycleType.sum`). -/
theorem cycleCount_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cycleCount n σ = (n - σ.cycleType.sum) + σ.cycleType.card := by
  unfold cycleCount
  congr 1
  have hsupp : σ.support = Finset.univ.filter (fun a => ¬ (σ a = a)) := by
    ext x; simp [Equiv.Perm.mem_support]
  have hcard : (Finset.univ.filter fun x => σ x = x).card
      + σ.support.card = Fintype.card (Fin n) := by
    rw [hsupp]
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun a => σ a = a)
  rw [Equiv.Perm.sum_cycleType]
  simp only [Fintype.card_fin] at hcard
  omega

/-! ### The generic orbit count `gcount` and the merge lemma

The orbit count and the merge lemma in their natural generality (an arbitrary fintype),
so that the ~85-line merge argument is proved exactly once. `cycleCount_swap_mul` below
is the `Fin (n+1)` specialization; `Weingarten.OrthogonalGram` re-exports the generic
forms under its `RSS` namespace for the partner-fiber recursion and the symplectic
consumers. -/

/-- Orbit count of a permutation of any fintype (fixed points + cycles). -/
def gcount {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter fun x => σ x = x).card + σ.cycleType.card

/-- `gcount σ = (card α - cycleType.sum) + cycleType.card`, manifestly a function of the
cycle type alone. -/
theorem gcount_eq {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    gcount σ = (Fintype.card α - σ.cycleType.sum) + σ.cycleType.card := by
  unfold gcount; congr 1
  have hsupp : σ.support = Finset.univ.filter (fun a => ¬ (σ a = a)) := by
    ext x; simp [Equiv.Perm.mem_support]
  have hcard : (Finset.univ.filter fun x => σ x = x).card + σ.support.card
      = Fintype.card α := by
    rw [hsupp]
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset α)) (p := fun a => σ a = a)
  rw [Equiv.Perm.sum_cycleType]; omega

/-- On `Fin N` the generic orbit count coincides with `cycleCount`. -/
theorem cycleCount_eq_gcount (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    cycleCount N σ = gcount σ := by
  rw [cycleCount_eq, gcount_eq, Fintype.card_fin]

/-- **Merge lemma** (generic form): left-multiplying by a transposition through a fixed
point lowers the orbit count by exactly one — the fixed point `a` is absorbed into the
orbit of `b`. -/
theorem gcount_swap_mul {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (a b : α) (ha : σ a = a) (hab : a ≠ b) :
    gcount (Equiv.swap a b * σ) + 1 = gcount σ := by
  rw [gcount_eq, gcount_eq]
  have hbnd_swap : (Equiv.swap a b * σ).cycleType.sum ≤ Fintype.card α :=
    Equiv.Perm.sum_cycleType_le _
  have hbnd_sig : σ.cycleType.sum ≤ Fintype.card α := Equiv.Perm.sum_cycleType_le _
  by_cases hb : σ b = b
  · -- `b` is also fixed: `swap a b` is a disjoint 2-cycle, count drops by one.
    have hdisj : Disjoint (Equiv.swap a b) σ := by
      intro x
      by_cases hxa : x = a
      · right; rw [hxa]; exact ha
      · by_cases hxb : x = b
        · right; rw [hxb]; exact hb
        · left; exact Equiv.swap_apply_of_ne_of_ne hxa hxb
    have hct : (Equiv.swap a b * σ).cycleType = (Equiv.swap a b).cycleType + σ.cycleType :=
      hdisj.cycleType_mul
    have hswapct : (Equiv.swap a b).cycleType = {2} := by
      rw [(isCycle_swap hab).cycleType, card_support_swap hab]
    have hsum : (Equiv.swap a b * σ).cycleType.sum = 2 + σ.cycleType.sum := by
      rw [hct, hswapct, Multiset.sum_add, Multiset.sum_singleton]
    have hcard : (Equiv.swap a b * σ).cycleType.card = 1 + σ.cycleType.card := by
      rw [hct, hswapct, Multiset.card_add, Multiset.card_singleton]
    rw [hsum, hcard]; omega
  · -- `b` moves: splice `a` into the cycle of `b`.
    set τ := Equiv.swap a b * σ with hτdef
    have hσeq : σ = Equiv.swap a b * τ := by
      rw [hτdef, ← mul_assoc, Equiv.swap_mul_self, one_mul]
    have hτa : τ a = b := by rw [hτdef, Equiv.Perm.mul_apply, ha, Equiv.swap_apply_left]
    have hτa_ne : τ a ≠ a := by rw [hτa]; exact (Ne.symm hab)
    have hσb_ne_a : σ b ≠ a := by
      intro h; apply hb
      have : σ b = σ a := by rw [h, ha]
      exact absurd (σ.injective this).symm hab
    have hτb : τ b = σ b := by
      rw [hτdef, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hσb_ne_a hb]
    have hτb_ne_a : τ b ≠ a := by rw [hτb]; exact hσb_ne_a
    set c := τ.cycleOf a with hcdef
    have hccyc : IsCycle c := isCycle_cycleOf τ hτa_ne
    have hca : c a = b := by rw [hcdef, cycleOf_apply_self, hτa]
    have hsc : τ.SameCycle a b := ⟨1, by simp [hτa]⟩
    have hcb : c b = τ b := by rw [hcdef]; exact hsc.cycleOf_apply
    have hcb_ne_a : c b ≠ a := by rw [hcb]; exact hτb_ne_a
    have hccaa : c (c a) ≠ a := by rw [hca]; exact hcb_ne_a
    have hmem : c ∈ τ.cycleFactorsFinset :=
      cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hτa_ne)
    set rr := τ * c⁻¹ with hrdef
    have hdr : Disjoint rr c := disjoint_mul_inv_of_mem_cycleFactorsFinset hmem
    have hτcr : τ = c * rr := by
      rw [hrdef]
      have hcomm : Commute c (τ * c⁻¹) := (hdr.symm).commute
      rw [hcomm.eq, mul_assoc, inv_mul_cancel, mul_one]
    set g := Equiv.swap a b * c with hgdef
    have hswap_eq : Equiv.swap a (c a) = Equiv.swap a b := by rw [hca]
    have hgcyc : IsCycle g := by
      rw [hgdef, ← hswap_eq]; exact hccyc.swap_mul (by rw [hca]; exact (Ne.symm hab)) hccaa
    have hgsupp : g.support = c.support \ {a} := by
      rw [hgdef, ← hswap_eq]; exact support_swap_mul_eq c a hccaa
    have ha_mem : a ∈ c.support := by rw [mem_support, hca]; exact (Ne.symm hab)
    have hσgr : σ = g * rr := by rw [hσeq, hτcr, hgdef, ← mul_assoc]
    have hgr_supp : g.support ≤ c.support := by rw [hgsupp]; exact sdiff_le
    have hdgr : Disjoint g rr := (hdr.symm).mono hgr_supp (le_refl rr.support)
    have hτct : τ.cycleType = c.cycleType + rr.cycleType := by
      rw [hτcr]; exact (hdr.symm).cycleType_mul
    have hσct : σ.cycleType = g.cycleType + rr.cycleType := by
      rw [hσgr]; exact hdgr.cycleType_mul
    set csa := c.support.card with hcsa
    have hcct : c.cycleType = {csa} := hccyc.cycleType
    have hcsa_ge : 2 ≤ csa := hccyc.two_le_card_support
    have hgcard : g.support.card = csa - 1 := by
      rw [hgsupp, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ha_mem),
        Finset.card_singleton]
    have hgct : g.cycleType = {csa - 1} := by rw [hgcyc.cycleType, hgcard]
    have hτsum : τ.cycleType.sum = csa + rr.cycleType.sum := by
      rw [hτct, Multiset.sum_add, hcct, Multiset.sum_singleton]
    have hτcard : τ.cycleType.card = 1 + rr.cycleType.card := by
      rw [hτct, Multiset.card_add, hcct, Multiset.card_singleton]
    have hσsum : σ.cycleType.sum = (csa - 1) + rr.cycleType.sum := by
      rw [hσct, Multiset.sum_add, hgct, Multiset.sum_singleton]
    have hσcard : σ.cycleType.card = 1 + rr.cycleType.card := by
      rw [hσct, Multiset.card_add, hgct, Multiset.card_singleton]
    rw [hτsum, hτcard, hσsum, hσcard]
    rw [hτsum] at hbnd_swap
    omega

/-- `ι(e) = decomposeFin.symm (0, e)` fixes `0` and acts by `e` on successors, hence
preserves the cycle type. -/
private theorem cycleType_iota (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (decomposeFin.symm ((0 : Fin (n + 1)), e)).cycleType = e.cycleType := by
  set i : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩ with hi
  have heq : decomposeFin.symm ((0 : Fin (n + 1)), e) = e.viaEmbedding i := by
    ext x
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [decomposeFin_symm_apply_zero]
      rw [viaEmbedding_apply_of_notMem]
      rintro ⟨y, hy⟩
      exact Fin.succ_ne_zero y hy
    · rw [decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
      have hva : (e.viaEmbedding i) j.succ = i (e j) := viaEmbedding_apply e i j
      rw [hva]
      rfl
  rw [heq, viaEmbedding]
  convert cycleType_extendDomain (Equiv.ofInjective i.1 i.2) (g := e) using 3

/-- Factorisation `decomposeFin.symm (p, e) = swap 0 p · ι(e)`. -/
theorem decomposeFin_symm_eq (n : ℕ) (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    decomposeFin.symm (p, e) = swap 0 p * decomposeFin.symm ((0 : Fin (n + 1)), e) := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x <;>
    simp [Perm.mul_apply, decomposeFin_symm_apply_zero, decomposeFin_symm_apply_succ,
      Equiv.swap_apply_left, Equiv.swap_self]

/-- **Merge lemma.** Left-multiplying by a transposition `swap a b` through a fixed point
`a` lowers the orbit count by exactly one. This is the combinatorial heart of the splice
rule: the fixed point `a` is absorbed into the orbit of `b`. `Fin`-specialization of the
generic `gcount_swap_mul` above. -/
private theorem cycleCount_swap_mul (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1)) (ha : σ a = a) (hab : a ≠ b) :
    cycleCount (n + 1) (swap a b * σ) + 1 = cycleCount (n + 1) σ := by
  rw [cycleCount_eq_gcount, cycleCount_eq_gcount]
  exact gcount_swap_mul σ a b ha hab

/-- **Splice rule** along `Equiv.Perm.decomposeFin`.
Blueprint: `lem:cycleCount_decompose`; exhaustively checked for `n + 1 ≤ 6` (C2). -/
theorem cycleCount_decomposeFin (n : ℕ) (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    cycleCount (n + 1) (Equiv.Perm.decomposeFin.symm (p, e)) =
      cycleCount n e + if p = 0 then 1 else 0 := by
  by_cases hp : p = 0
  · subst hp
    rw [if_pos rfl, cycleCount_eq, cycleCount_eq, cycleType_iota]
    have : e.cycleType.sum ≤ n := by have := sum_cycleType_le e; simpa using this
    omega
  · rw [if_neg hp, decomposeFin_symm_eq]
    have hfix : decomposeFin.symm ((0 : Fin (n + 1)), e) 0 = 0 :=
      decomposeFin_symm_apply_zero 0 e
    have hmerge := cycleCount_swap_mul n (decomposeFin.symm (0, e)) 0 p hfix (Ne.symm hp)
    have hiota : cycleCount (n + 1) (decomposeFin.symm ((0 : Fin (n + 1)), e))
        = cycleCount n e + 1 := by
      rw [cycleCount_eq, cycleCount_eq, cycleType_iota]
      have : e.cycleType.sum ≤ n := by have := sum_cycleType_le e; simpa using this
      omega
    omega

/-- The sign of `σ` equals `(-1)` to the reflection length `n - cycleCount n σ` (the
minimal number of transpositions in a factorization). Used by the parity and
below-threshold packages. -/
theorem sign_eq_neg_one_pow (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (n - cycleCount n σ) := by
  have hcard_le_sum : Multiset.card σ.cycleType ≤ σ.cycleType.sum := by
    have h2 : ∀ x ∈ σ.cycleType, 1 ≤ x := fun x hx =>
      le_trans (by norm_num) (Equiv.Perm.two_le_of_mem_cycleType hx)
    calc Multiset.card σ.cycleType = Multiset.card σ.cycleType • 1 := by simp
      _ ≤ σ.cycleType.sum := Multiset.card_nsmul_le_sum h2
  have hsum_le_n : σ.cycleType.sum ≤ n := by
    have := sum_cycleType_le σ; simpa using this
  have hcc : n - cycleCount n σ = σ.cycleType.sum - Multiset.card σ.cycleType := by
    rw [cycleCount_eq]; omega
  rw [hcc, Equiv.Perm.sign_of_cycleType, Units.val_pow_eq_pow_val]
  have hu : ((-1 : ℤˣ) : ℤ) = -1 := rfl
  rw [hu, show σ.cycleType.sum + Multiset.card σ.cycleType
        = (σ.cycleType.sum - Multiset.card σ.cycleType) + 2 * Multiset.card σ.cycleType from by
    omega, pow_add, pow_mul]
  simp

/-- The orbit count is at most `n` (there are at most `n` orbits on `Fin n`). -/
theorem cycleCount_le (n : ℕ) (σ : Equiv.Perm (Fin n)) : cycleCount n σ ≤ n := by
  have hcard : Multiset.card σ.cycleType ≤ σ.cycleType.sum :=
    calc Multiset.card σ.cycleType = Multiset.card σ.cycleType • 1 := by simp
      _ ≤ σ.cycleType.sum := Multiset.card_nsmul_le_sum fun x hx =>
          le_trans (by norm_num) (Equiv.Perm.two_le_of_mem_cycleType hx)
  have hsum : σ.cycleType.sum ≤ n := by simpa using sum_cycleType_le σ
  rw [cycleCount_eq]
  omega

/-! ### `cycleCount` is a class function

`cycleCount` depends only on the cycle type (`cycleCount_eq`), hence is invariant under
inversion and conjugation. Reused by the certified cell (`Cell23.lean`) and the pairing
bridge (`Pairings.lean`). -/

/-- `cycleCount` is invariant under inversion. -/
theorem cycleCount_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    cycleCount n σ⁻¹ = cycleCount n σ := by
  rw [cycleCount_eq, cycleCount_eq, Equiv.Perm.cycleType_inv]

/-- `cycleCount` is invariant under conjugation. -/
theorem cycleCount_conj (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    cycleCount n (τ * σ * τ⁻¹) = cycleCount n σ := by
  rw [cycleCount_eq, cycleCount_eq, Equiv.Perm.cycleType_conj]

/-- The inverse-symmetry `c(a b⁻¹) = c(a⁻¹ b)` (each is a conjugate of the other's
inverse). -/
theorem cycleCount_mul_inv_comm (n : ℕ) (a b : Equiv.Perm (Fin n)) :
    cycleCount n (a * b⁻¹) = cycleCount n (a⁻¹ * b) := by
  have h1 : a⁻¹ * b = a⁻¹ * (b * a⁻¹) * (a⁻¹)⁻¹ := by group
  have h2 : (a * b⁻¹)⁻¹ = b * a⁻¹ := by group
  rw [h1, cycleCount_conj, ← h2, cycleCount_inv]

end Weingarten
