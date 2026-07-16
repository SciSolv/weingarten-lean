/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Homs

/-!
# The below-threshold package: Penrose-conditional sum rules

All statements below are proved and elaborated against Mathlib (`#print axioms`:
`propext`, `Classical.choice`, `Quot.sound`). Blueprint: `def:alt`, `lem:alt_mul`,
`thm:gram_singular`, `def:ones`, `lem:ones_mul`, `thm:gram_singular_neg`,
`def:penrose_pair`, `lem:penrose_comm_unique`, `thm:gram_penrose_unique`,
`thm:rising_conditional`, `thm:falling_conditional`, `thm:vanish_below`,
`thm:sign_breakdown`.

Below threshold (integer `1 ≤ N < n`) the Gram element is singular, so the Weingarten
data cannot be its inverse. Instead of defining it (which classically needs
partition-indexed character theory), we *characterize* it by the two Penrose equations
`G * W * G = G`, `W * G * W = W` and prove the sum rules **conditionally**: any Penrose
partner has coefficient sum `(∏ (N + m))⁻¹` whenever the rising factorial is nonzero
(every `N > 0`), and signed coefficient sum `0` whenever the falling factorial is zero
(every integer `1 ≤ N < n`) — the proofs are one-line homomorphism evaluations through
`aug_gram` / `sgnHom_gram`. The forced breakdown of the strict parity pattern follows
from the vanishing alone. The alternating element gives an explicit zero-divisor
witness that `gram` is not a unit below threshold. Character theory, Schur functions,
spectral theory: none, anywhere. Checks B1–B5 pin every identity.

This is a formalization-design route, not a claim of new theorems. The Penrose characterization
is the literature's standard definition of
the below-threshold Weingarten function (Collins–Śniady, Comm. Math. Phys. 264
(2006); recorded in this two-equation form by Zinn-Justin, arXiv:0907.2719); the
invertibility root set {0, …, n−1} is stated as known by Collins–Matsumoto,
arXiv:2510.21186. The two-line character evaluations, the conditional formulation,
and the alternating-element witness are unlocated in print (reference request
outstanding).
-/

namespace Weingarten

open Equiv Equiv.Perm MonoidAlgebra

/-- The alternating element `∑ σ, sgn σ • σ`. Blueprint: `def:alt`. -/
noncomputable def alt (k : Type*) [CommRing k] (n : ℕ) : SymAlg k n :=
  ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : k) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ

/-- `sgnHom` on a basis element is the sign of the permutation. -/
theorem sgnHom_of (k : Type*) [CommRing k] (n : ℕ) (m : Equiv.Perm (Fin n)) :
    sgnHom k n (MonoidAlgebra.of k (Equiv.Perm (Fin n)) m)
      = ((Equiv.Perm.sign m : ℤ) : k) := by
  rw [sgnHom_apply]
  rw [Finset.sum_eq_single m]
  · rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_apply, if_pos rfl, mul_one]
  · intro b _ hbm
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_apply, if_neg (Ne.symm hbm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ m) h

/-- Absorption: `alt` soaks up right multiplication into the sign homomorphism.
Blueprint: `lem:alt_mul` (check B1). -/
theorem alt_mul (k : Type*) [CommRing k] (n : ℕ) (x : SymAlg k n) :
    alt k n * x = sgnHom k n x • alt k n := by
  have key : ∀ g : Equiv.Perm (Fin n),
      alt k n * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
        = ((Equiv.Perm.sign g : ℤ) : k) • alt k n := by
    intro g
    unfold Weingarten.alt
    rw [Finset.sum_mul]
    have step : ∀ σ : Equiv.Perm (Fin n),
        (((Equiv.Perm.sign σ : ℤ) : k) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
            * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
          = ((Equiv.Perm.sign σ : ℤ) : k)
              • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (σ * g) := by
      intro σ
      rw [smul_mul_assoc, ← map_mul]
    rw [Finset.sum_congr rfl (fun σ _ => step σ)]
    have reindex :
        (∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : k) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (σ * g))
          = ∑ ρ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign (ρ * g⁻¹) : ℤ) : k) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) ρ := by
      rw [← Equiv.sum_comp (Equiv.mulRight g) (fun ρ =>
          ((Equiv.Perm.sign (ρ * g⁻¹) : ℤ) : k) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) ρ)]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Equiv.coe_mulRight, mul_inv_cancel_right]
    rw [reindex, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, smul_smul]
    push_cast
    ring_nf
  induction x using MonoidAlgebra.induction_on with
  | hM m => rw [key, sgnHom_of]
  | hadd x y hx hy => rw [mul_add, map_add, hx, hy, add_smul]
  | hsmul r x hx => rw [mul_smul_comm, map_smul, hx, smul_assoc]

/-- **Gram singularity below threshold**: for integer `1 ≤ N < n` the Gram element is
not a unit — `alt` is an explicit kernel witness, since `alt * gram = (falling
factorial) • alt = 0` while `alt ≠ 0` in characteristic zero.
Blueprint: `thm:gram_singular` (checks B3, B3b). -/
theorem not_isUnit_gram {n N : ℕ} (_h1 : 1 ≤ N) (h2 : N < n) :
    ¬ IsUnit (gram ℚ n (N : ℚ)) := by
  intro hu
  have hzero : alt ℚ n * gram ℚ n (N : ℚ) = 0 := by
    rw [alt_mul, sgnHom_gram]
    have hp : (∏ m ∈ Finset.range n, ((N : ℚ) - (m : ℚ))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr h2) (sub_self _)
    rw [hp, zero_smul]
  have hsgn_alt : sgnHom ℚ n (alt ℚ n)
      = (Fintype.card (Equiv.Perm (Fin n)) : ℚ) := by
    rw [alt, map_sum]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ)) (fun σ _ => by
      rw [map_smul, smul_eq_mul, sgnHom_of]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        rw [h] <;> norm_num)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hne : alt ℚ n ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsgn_alt
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℚ) ≠ 0 := by
      simp [Fintype.card_perm, Nat.factorial_ne_zero]
    exact hcard hsgn_alt.symm
  exact hne ((IsUnit.mul_left_eq_zero hu).mp hzero)

/-- The all-ones element `∑ σ, σ` — the augmentation twin of `alt`.
Blueprint: `def:ones`. -/
noncomputable def ones (k : Type*) [CommRing k] (n : ℕ) : SymAlg k n :=
  ∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ

/-- Absorption: `ones` soaks up right multiplication into the augmentation — the
all-ones mirror of `alt_mul`. Blueprint: `lem:ones_mul`. -/
theorem ones_mul (k : Type*) [CommRing k] (n : ℕ) (x : SymAlg k n) :
    ones k n * x = aug k n x • ones k n := by
  have key : ∀ g : Equiv.Perm (Fin n),
      ones k n * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g = ones k n := by
    intro g
    unfold Weingarten.ones
    rw [Finset.sum_mul]
    have step : ∀ σ : Equiv.Perm (Fin n),
        MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ
            * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
          = MonoidAlgebra.of k (Equiv.Perm (Fin n)) (σ * g) :=
      fun σ => (map_mul (MonoidAlgebra.of k (Equiv.Perm (Fin n))) σ g).symm
    rw [Finset.sum_congr rfl (fun σ _ => step σ)]
    exact Fintype.sum_equiv (Equiv.mulRight g)
      (fun σ => MonoidAlgebra.of k (Equiv.Perm (Fin n)) (σ * g))
      (fun ρ => MonoidAlgebra.of k (Equiv.Perm (Fin n)) ρ)
      (fun σ => by simp only [Equiv.coe_mulRight])
  induction x using MonoidAlgebra.induction_on with
  | hM m =>
    rw [key]
    simp only [aug, MonoidAlgebra.lift_of, MonoidHom.one_apply, one_smul]
  | hadd x y hx hy => rw [mul_add, map_add, hx, hy, add_smul]
  | hsmul r x hx => rw [mul_smul_comm, map_smul, hx, smul_assoc]

/-- **Gram singularity at negative integer parameters**: for integer `0 ≤ m ≤ n − 1`
the Gram element at `N = -m` is not a unit — `ones` is an explicit kernel witness,
since `ones * gram = (rising factorial at -m) • ones = 0` while `ones ≠ 0` in
characteristic zero. Together with `not_isUnit_gram` this exhibits the full integer
singular band `{-(n-1), …, n-1}` of the group-algebra Gram.
Blueprint: `thm:gram_singular_neg`. -/
theorem not_isUnit_gram_neg {n m : ℕ} (h : m < n) :
    ¬ IsUnit (gram ℚ n (-(m : ℚ))) := by
  intro hu
  have hzero : ones ℚ n * gram ℚ n (-(m : ℚ)) = 0 := by
    rw [ones_mul, aug_gram]
    have hp : (∏ j ∈ Finset.range n, (-(m : ℚ) + (j : ℚ))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr h) (neg_add_cancel _)
    rw [hp, zero_smul]
  have haug_ones : aug ℚ n (ones ℚ n)
      = (Fintype.card (Equiv.Perm (Fin n)) : ℚ) := by
    rw [ones, map_sum]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ)) (fun σ _ => by
      simp only [aug, MonoidAlgebra.lift_of, MonoidHom.one_apply])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hne : ones ℚ n ≠ 0 := by
    intro h0
    rw [h0, map_zero] at haug_ones
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℚ) ≠ 0 := by
      simp [Fintype.card_perm, Nat.factorial_ne_zero]
    exact hcard haug_ones.symm
  exact hne ((IsUnit.mul_left_eq_zero hu).mp hzero)

/-- Penrose-partner predicate: just the two product identities. The Moore–Penrose
pseudo-inverse satisfies both; so does the genuine inverse when it exists.
Blueprint: `def:penrose_pair`. -/
def IsPenrosePair {k : Type*} [CommRing k] {n : ℕ} (g w : SymAlg k n) : Prop :=
  g * w * g = g ∧ w * g * w = w

/-- **Group-inverse uniqueness at monoid level**: two Penrose partners of the same
element `g` that both commute with `g` coincide — the standard five-identity chain
(`w₁ = w₁²g`, `w₂ = g w₂²`, then insert `g = g w₂ g` and `g = g w₁ g` to get
`w₁ = w₁ w₂ g = w₂`). Associativity only: no inverses, no commutativity of the
ambient monoid. Blueprint: `lem:penrose_comm_unique`. -/
theorem penrose_partner_unique {M : Type*} [Monoid M] {g w₁ w₂ : M}
    (hg₁ : g * w₁ * g = g) (hw₁ : w₁ * g * w₁ = w₁) (hc₁ : w₁ * g = g * w₁)
    (hg₂ : g * w₂ * g = g) (hw₂ : w₂ * g * w₂ = w₂) (hc₂ : w₂ * g = g * w₂) :
    w₁ = w₂ := by
  have e₁ : w₁ = w₁ * w₁ * g := by
    conv_lhs => rw [← hw₁]
    rw [mul_assoc, ← hc₁, ← mul_assoc]
  have e₂ : w₂ = g * (w₂ * w₂) := by
    conv_lhs => rw [← hw₂]
    rw [hc₂, mul_assoc]
  have e₃ : w₁ = w₁ * (w₂ * g) :=
    calc w₁ = w₁ * w₁ * g := e₁
      _ = w₁ * w₁ * (g * w₂ * g) := by rw [hg₂]
      _ = (w₁ * w₁ * g) * (w₂ * g) := by simp only [mul_assoc]
      _ = w₁ * (w₂ * g) := by rw [← e₁]
  have e₄ : w₂ = w₁ * (w₂ * g) :=
    calc w₂ = g * (w₂ * w₂) := e₂
      _ = (g * w₁ * g) * (w₂ * w₂) := by rw [hg₁]
      _ = (g * w₁) * (g * (w₂ * w₂)) := by simp only [mul_assoc]
      _ = (g * w₁) * w₂ := by rw [← e₂]
      _ = (w₁ * g) * w₂ := by rw [hc₁]
      _ = w₁ * (w₂ * g) := by rw [mul_assoc, ← hc₂]
  exact e₃.trans e₄.symm

/-- **Uniqueness of Penrose partners of the Gram element**: the commutation is free
by centrality (`gram_central`), so any two Penrose partners of `gram k n N`
coincide — the below-threshold Weingarten data, characterized by the two Penrose
equations, is canonical whenever it exists. Blueprint: `thm:gram_penrose_unique`. -/
theorem gram_penrose_partner_unique {k : Type*} [CommRing k] {n : ℕ} {N : k}
    {w₁ w₂ : SymAlg k n} (h₁ : IsPenrosePair (gram k n N) w₁)
    (h₂ : IsPenrosePair (gram k n N) w₂) : w₁ = w₂ :=
  penrose_partner_unique h₁.1 h₁.2 (gram_central k n N w₁).symm.eq
    h₂.1 h₂.2 (gram_central k n N w₂).symm.eq

/-- **Conditional rising rule, all `N`**: apply `aug` to `G W G = G`.
Blueprint: `thm:rising_conditional`. -/
theorem sum_wg_of_penrose {k : Type*} [Field k] {n : ℕ} {N : k} {w : SymAlg k n}
    (h : IsPenrosePair (gram k n N) w)
    (hr : ∏ m ∈ Finset.range n, (N + (m : k)) ≠ 0) :
    aug k n w = (∏ m ∈ Finset.range n, (N + (m : k)))⁻¹ := by
  have e := congrArg (aug k n) h.1
  rw [map_mul, map_mul, aug_gram] at e
  set r := ∏ m ∈ Finset.range n, (N + (m : k)) with hrdef
  refine eq_inv_of_mul_eq_one_left ?_
  have h1 : r * (aug k n w * r) = r * 1 := by rw [mul_one, ← mul_assoc]; exact e
  exact mul_left_cancel₀ hr h1

/-- **Conditional falling rule off the root set**: apply `sgnHom` to `G W G = G`.
Blueprint: `thm:falling_conditional`. -/
theorem sum_sgn_wg_of_penrose {k : Type*} [Field k] {n : ℕ} {N : k} {w : SymAlg k n}
    (h : IsPenrosePair (gram k n N) w)
    (hf : ∏ m ∈ Finset.range n, (N - (m : k)) ≠ 0) :
    sgnHom k n w = (∏ m ∈ Finset.range n, (N - (m : k)))⁻¹ := by
  have e := congrArg (sgnHom k n) h.1
  rw [map_mul, map_mul, sgnHom_gram] at e
  set r := ∏ m ∈ Finset.range n, (N - (m : k)) with hrdef
  refine eq_inv_of_mul_eq_one_left ?_
  have h1 : r * (sgnHom k n w * r) = r * 1 := by rw [mul_one, ← mul_assoc]; exact e
  exact mul_left_cancel₀ hf h1

/-- **Exact vanishing below threshold**: needs only the second Penrose identity and
works over any commutative ring. Two lines: `ŝ w = ŝ w * ŝ G * ŝ w = ŝ w * 0 * ŝ w = 0`.
Blueprint: `thm:vanish_below`. -/
theorem sgnHom_eq_zero_of_penrose {k : Type*} [CommRing k] {n : ℕ} {N : k}
    {w : SymAlg k n} (h : w * gram k n N * w = w)
    (hf : ∏ m ∈ Finset.range n, (N - (m : k)) = 0) :
    sgnHom k n w = 0 := by
  have e := congrArg (sgnHom k n) h
  rw [map_mul, map_mul, sgnHom_gram, hf] at e
  simpa using e.symm

/-- **Forced breakdown of the strict parity pattern** below threshold: a nonempty sum
of strictly positive terms cannot vanish. Blueprint: `thm:sign_breakdown`. -/
theorem sign_breakdown_of_penrose {n : ℕ} {N : ℝ} {w : SymAlg ℝ n}
    (h : w * gram ℝ n N * w = w)
    (hf : ∏ m ∈ Finset.range n, (N - (m : ℝ)) = 0) :
    ¬ ∀ σ : Equiv.Perm (Fin n), 0 < (-1 : ℝ) ^ (n - cycleCount n σ) * w σ := by
  intro hpos
  have hzero : sgnHom ℝ n w = 0 := sgnHom_eq_zero_of_penrose h hf
  rw [sgnHom_apply] at hzero
  have hpos' : 0 < ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * w σ := by
    refine Finset.sum_pos (fun σ _ => ?_) Finset.univ_nonempty
    have hcast : ((Equiv.Perm.sign σ : ℤ) : ℝ) = (-1 : ℝ) ^ (n - cycleCount n σ) := by
      rw [sign_eq_neg_one_pow]; push_cast; ring
    rw [hcast]
    exact hpos σ
  rw [hzero] at hpos'
  exact lt_irrefl 0 hpos'

end Weingarten
