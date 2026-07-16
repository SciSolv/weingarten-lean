/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Gram

/-!
# The two one-dimensional characters and their Gram values

All six character lemmas below are proved and elaborated against Mathlib
(`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`).
Blueprint: `lem:hom_coeffsum`, `lem:aug`, `lem:gram_eval`.

The trivial and sign characters of `S_n` lift through `MonoidAlgebra.lift` to
`k`-algebra homomorphisms `aug` (the coefficient sum) and `sgnHom` (the signed
coefficient sum). Their values on the Jucys–Murphy elements are `±(n - 1 - i)`
(check C4), so by the Jucys factorization — a polynomial identity, no invertibility —
their values on the Gram element are the rising and falling factorials for **every**
`N` in **every** commutative ring (check B2). These two evaluations drive the entire
below-threshold package.
-/

namespace Weingarten

open Equiv Equiv.Perm MonoidAlgebra

/-- Augmentation: the algebra homomorphism induced by the trivial character. -/
noncomputable def aug (k : Type*) [CommRing k] (n : ℕ) : SymAlg k n →ₐ[k] k :=
  MonoidAlgebra.lift k k (Equiv.Perm (Fin n)) 1

/-- The sign character with values in `k`. -/
def signCoeff (k : Type*) [CommRing k] (n : ℕ) : Equiv.Perm (Fin n) →* k :=
  (Units.coeHom k).comp
    ((Units.map (Int.castRingHom k).toMonoidHom).comp Equiv.Perm.sign)

/-- The sign homomorphism on the group algebra. -/
noncomputable def sgnHom (k : Type*) [CommRing k] (n : ℕ) : SymAlg k n →ₐ[k] k :=
  MonoidAlgebra.lift k k (Equiv.Perm (Fin n)) (signCoeff k n)

/-- `signCoeff` is the sign of the permutation, cast `ℤ → k`. -/
private lemma signCoeff_apply (k : Type*) [CommRing k] (n : ℕ) (a : Equiv.Perm (Fin n)) :
    signCoeff k n a = ((Equiv.Perm.sign a : ℤ) : k) := by
  simp [signCoeff, Units.coeHom, Units.coe_map]

/-- `aug` is the coefficient sum. Blueprint: `lem:hom_coeffsum`. -/
theorem aug_apply (k : Type*) [CommRing k] (n : ℕ) (x : SymAlg k n) :
    aug k n x = ∑ σ : Equiv.Perm (Fin n), x σ := by
  rw [aug, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp [MonoidHom.one_apply]

/-- `sgnHom` is the sign-weighted coefficient sum. Blueprint: `lem:hom_coeffsum`. -/
theorem sgnHom_apply (k : Type*) [CommRing k] (n : ℕ) (x : SymAlg k n) :
    sgnHom k n x = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * x σ := by
  rw [sgnHom, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [signCoeff_apply, smul_eq_mul, mul_comm]

/-- `ε (K i) = n - 1 - i`. Blueprint: `lem:aug` (check C4). -/
theorem aug_jm (k : Type*) [CommRing k] (n : ℕ) (i : Fin n) :
    aug k n (jm k n i) = ((Finset.Ioi i).card : k) := by
  unfold Weingarten.jm
  rw [map_sum]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : k)) (fun j _ => by
    simp only [aug, MonoidAlgebra.lift_of, MonoidHom.one_apply])]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `ŝ (K i) = -(n - 1 - i)`. Blueprint: `lem:aug` (check C4). -/
theorem sgn_jm (k : Type*) [CommRing k] (n : ℕ) (i : Fin n) :
    sgnHom k n (jm k n i) = -((Finset.Ioi i).card : k) := by
  unfold Weingarten.jm
  rw [map_sum]
  rw [Finset.sum_congr rfl (g := fun _ => (-1 : k)) (fun j hj => by
    rw [Finset.mem_Ioi] at hj
    have hij : i ≠ j := ne_of_lt hj
    simp only [sgnHom, MonoidAlgebra.lift_of, signCoeff_apply, Equiv.Perm.sign_swap hij]
    push_cast
    ring)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]

/-- `ε (gram) = N (N+1) ⋯ (N+n-1)` — the rising factorial, ALL `N`, no invertibility.
Blueprint: `lem:gram_eval` (check B2). -/
theorem aug_gram (k : Type*) [CommRing k] (n : ℕ) (N : k) :
    aug k n (gram k n N) = ∏ m ∈ Finset.range n, (N + (m : k)) := by
  rw [gram_eq_prod]
  unfold Weingarten.gramProd
  rw [map_list_prod, List.map_map]
  have hfac : ∀ i : Fin n,
      (aug k n ∘ fun i => algebraMap k (SymAlg k n) N + jm k n i) i
        = N + ((n - 1 - (i : ℕ) : ℕ) : k) := by
    intro i
    simp only [Function.comp_apply, map_add, AlgHom.commutes,
      Algebra.algebraMap_self_apply, aug_jm, Fin.card_Ioi]
  rw [List.map_congr_left (fun i _ => hfac i)]
  rw [← Fin.prod_univ_def (fun i : Fin n => N + ((n - 1 - (i : ℕ) : ℕ) : k))]
  rw [Fin.prod_univ_eq_prod_range (fun j => N + ((n - 1 - j : ℕ) : k)) n]
  exact Finset.prod_range_reflect (fun j => N + (j : k)) n

/-- `ŝ (gram) = N (N-1) ⋯ (N-n+1)` — the falling factorial, ALL `N`.
Blueprint: `lem:gram_eval` (check B2). -/
theorem sgnHom_gram (k : Type*) [CommRing k] (n : ℕ) (N : k) :
    sgnHom k n (gram k n N) = ∏ m ∈ Finset.range n, (N - (m : k)) := by
  rw [gram_eq_prod]
  unfold Weingarten.gramProd
  rw [map_list_prod, List.map_map]
  have hfac : ∀ i : Fin n,
      (sgnHom k n ∘ fun i => algebraMap k (SymAlg k n) N + jm k n i) i
        = N - ((n - 1 - (i : ℕ) : ℕ) : k) := by
    intro i
    simp only [Function.comp_apply, map_add, AlgHom.commutes,
      Algebra.algebraMap_self_apply, sgn_jm, Fin.card_Ioi, ← sub_eq_add_neg]
  rw [List.map_congr_left (fun i _ => hfac i)]
  rw [← Fin.prod_univ_def (fun i : Fin n => N - ((n - 1 - (i : ℕ) : ℕ) : k))]
  rw [Fin.prod_univ_eq_prod_range (fun j => N - ((n - 1 - j : ℕ) : k)) n]
  exact Finset.prod_range_reflect (fun j => N - (j : k)) n

end Weingarten
