/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.CycleCount

/-!
# Pair partitions: loops, crossings, and the twisted vectors

Fully elaborated and `sorry`-free; `#print axioms` of every declaration is
`propext, Classical.choice, Quot.sound`. The Pfaffian sign identity `sign_canonicalWord`
is proved by inversion counting: `sign σ = ∏` over position pairs (`sign_eq_prod_prod_Iio`),
reindexed to chord coordinates (`posEquiv`), where each chord pair contributes
`(-1) ^ crossInd` and `∑ crossInd = crossings` — so the nesting contributions cancel in
pairs and the sign is the crossing parity.
Blueprint: `def:pairing`, `def:loops`, `def:crossings`, `def:eps_sign`,
`def:q_pairing`, `lem:q_pairing_inj`, `lem:loops_q_q`, `def:det_vector`,
`def:eps_vector`, `def:canonical_word`, `lem:sign_canonical_word`.

Pair partitions of `Fin (2 * n)` are encoded as fixed-point-free involutions.
`loops` is half the full cycle count of the product of two pairings;
`crossings` counts crossing chords in the canonical diagram; `epsSign` is the
crossing parity, identified by `sign_canonicalWord` with the sign of the
canonical interleaving word — the Pfaffian sign. The permutation-like pairings
`qPair ρ` (pairing `a ↔ n + ρ a`) carry the determinant vector, and
`loops_qPair_qPair` is the bridge `loops (q τ) (q ρ) = c (τ⁻¹ρ)` back to the
unitary Gram data of `Weingarten.CycleCount` / `Weingarten.Gram`.
-/

namespace Weingarten

/-- A pair partition of `Fin (2 * n)`: a fixed-point-free involution.
Blueprint: `def:pairing`. -/
def Pairing (n : ℕ) : Type :=
  {p : Equiv.Perm (Fin (2 * n)) // p * p = 1 ∧ ∀ x, p x ≠ x}

namespace Pairing

variable {n : ℕ}

instance : DecidableEq (Pairing n) := by
  unfold Pairing; infer_instance

instance : Fintype (Pairing n) := by
  unfold Pairing; infer_instance

/-- Loop count of two pairings: half the full cycle count (fixed points
included) of their product. Blueprint: `def:loops`. -/
def loops (p q : Pairing n) : ℕ :=
  cycleCount (2 * n) (p.1 * q.1) / 2

/-- Crossing number: the number of pairs of canonical chords `(a, p a)`,
`(c, p c)` with `a < c < p a < p c`. Blueprint: `def:crossings`. -/
def crossings (p : Pairing n) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n) × Fin (2 * n))).filter fun ac =>
    ac.1 < p.1 ac.1 ∧ ac.2 < p.1 ac.2 ∧
    ac.1 < ac.2 ∧ ac.2 < p.1 ac.1 ∧ p.1 ac.1 < p.1 ac.2).card

end Pairing

/-- The crossing parity of a pairing — the Pfaffian sign.
Blueprint: `def:eps_sign`. -/
def epsSign {n : ℕ} (p : Pairing n) : ℤ := (-1) ^ p.crossings

section qPairConstruction
open Equiv

/-- The identification `Fin (2n) ≃ Fin n ⊕ Fin n` (lower half / upper half). -/
def pairEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (finCongr (two_mul n)).trans finSumFinEquiv.symm

/-- The swap-across involution on `Fin n ⊕ Fin n`: `inl a ↦ inr (ρ a)`, `inr b ↦ inl (ρ⁻¹ b)`. -/
def swapAcross {n : ℕ} (ρ : Perm (Fin n)) : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | Sum.inl a => Sum.inr (ρ a)
  | Sum.inr b => Sum.inl (ρ⁻¹ b)

theorem swapAcross_involutive {n : ℕ} (ρ : Perm (Fin n)) :
    Function.Involutive (swapAcross ρ) := by
  intro x
  cases x with
  | inl a => simp [swapAcross]
  | inr b => simp [swapAcross]

/-- `swapAcross ρ` as a permutation of `Fin n ⊕ Fin n`. -/
def swapAcrossPerm {n : ℕ} (ρ : Perm (Fin n)) : Perm (Fin n ⊕ Fin n) :=
  (swapAcross_involutive ρ).toPerm

@[simp] theorem swapAcrossPerm_inl {n : ℕ} (ρ : Perm (Fin n)) (a : Fin n) :
    swapAcrossPerm ρ (Sum.inl a) = Sum.inr (ρ a) := rfl
@[simp] theorem swapAcrossPerm_inr {n : ℕ} (ρ : Perm (Fin n)) (b : Fin n) :
    swapAcrossPerm ρ (Sum.inr b) = Sum.inl (ρ⁻¹ b) := rfl

theorem swapAcrossPerm_sq {n : ℕ} (ρ : Perm (Fin n)) :
    swapAcrossPerm ρ * swapAcrossPerm ρ = 1 := by
  ext x; simp only [Perm.mul_apply, Perm.one_apply]; exact swapAcross_involutive ρ x

end qPairConstruction

/-- The permutation-like pairing attached to `ρ`: it pairs `a ↔ n + ρ(a)`, realized as the
conjugate of `swapAcrossPerm ρ` through `pairEquiv`. Blueprint: `def:q_pairing`. -/
def qPair {n : ℕ} (ρ : Equiv.Perm (Fin n)) : Pairing n :=
  ⟨(pairEquiv n).symm.permCongr (swapAcrossPerm ρ), by
    rw [← Equiv.permCongr_mul, swapAcrossPerm_sq]; ext x; simp [Equiv.permCongr_apply], by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, ne_eq, Equiv.symm_apply_eq]
    cases hz : (pairEquiv n) x with
    | inl a => simp [swapAcrossPerm_inl]
    | inr b => simp [swapAcrossPerm_inr]⟩

/-- `qPair ρ` acts as `pairEquiv⁻¹ ∘ swapAcrossPerm ρ ∘ pairEquiv`. -/
theorem qPair_apply {n : ℕ} (ρ : Equiv.Perm (Fin n)) (x : Fin (2 * n)) :
    (qPair ρ).1 x = (pairEquiv n).symm (swapAcrossPerm ρ ((pairEquiv n) x)) := by
  simp [qPair, Equiv.permCongr_apply]

/-- Distinct permutations give distinct pairings. Blueprint: `lem:q_pairing_inj`. -/
theorem qPair_injective {n : ℕ} :
    Function.Injective (qPair : Equiv.Perm (Fin n) → Pairing n) := by
  intro ρ ρ' h
  have h2 : swapAcrossPerm ρ = swapAcrossPerm ρ' :=
    ((pairEquiv n).symm.permCongr).injective (Subtype.ext_iff.mp h)
  apply Equiv.ext; intro a
  have key : swapAcrossPerm ρ (Sum.inl a) = swapAcrossPerm ρ' (Sum.inl a) := by rw [h2]
  rw [swapAcrossPerm_inl, swapAcrossPerm_inl] at key
  exact Sum.inr_injective key

section CycleTypeTransfer
open Equiv Equiv.Perm
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `cycleType` is invariant under extending a permutation along an embedding (no new
moved points, so the cycle structure is unchanged). -/
theorem cycleType_viaEmbedding (e : Perm α) (i : α ↪ β) :
    (e.viaEmbedding i).cycleType = e.cycleType := by
  rw [Equiv.Perm.viaEmbedding]
  convert Equiv.Perm.cycleType_extendDomain (Equiv.ofInjective i.toFun i.inj') (g := e) using 3

/-- `cycleType` is invariant under transport along an equivalence of the underlying type. -/
theorem cycleType_permCongr (e : α ≃ β) (P : Perm α) :
    (e.permCongr P).cycleType = P.cycleType := by
  have heq : e.permCongr P = P.viaEmbedding e.toEmbedding := by
    ext y
    have hv : (P.viaEmbedding e.toEmbedding) (e.toEmbedding (e.symm y))
        = e.toEmbedding (P (e.symm y)) := Equiv.Perm.viaEmbedding_apply P e.toEmbedding (e.symm y)
    simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] at hv
    rw [Equiv.permCongr_apply, hv]
  rw [heq, cycleType_viaEmbedding]

theorem cycleType_sumCongr_left (a : Perm α) :
    Equiv.Perm.cycleType (Equiv.sumCongr a (1 : Perm β)) = a.cycleType := by
  have heq : (Equiv.sumCongr a (1 : Perm β) : Perm (α ⊕ β))
      = a.viaEmbedding ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    cases x with
    | inl a' =>
      show Sum.inl (a a') = _
      exact (Equiv.Perm.viaEmbedding_apply a ⟨Sum.inl, Sum.inl_injective⟩ a').symm
    | inr b' =>
      show Sum.inr ((1 : Perm β) b') = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
      · rfl
      · rintro ⟨y, hy⟩; exact Sum.inl_ne_inr hy
  rw [heq, cycleType_viaEmbedding]

theorem cycleType_sumCongr_right (b : Perm β) :
    Equiv.Perm.cycleType (Equiv.sumCongr (1 : Perm α) b) = b.cycleType := by
  have heq : (Equiv.sumCongr (1 : Perm α) b : Perm (α ⊕ β))
      = b.viaEmbedding ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x
    cases x with
    | inl a' =>
      show Sum.inl ((1 : Perm α) a') = _
      rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
      · rfl
      · rintro ⟨y, hy⟩; exact Sum.inr_ne_inl hy
    | inr b' =>
      show Sum.inr (b b') = _
      exact (Equiv.Perm.viaEmbedding_apply b ⟨Sum.inr, Sum.inr_injective⟩ b').symm
  rw [heq, cycleType_viaEmbedding]

/-- The cycle type of a block-diagonal permutation is the (multiset) sum of the blocks'. -/
theorem cycleType_sumCongr (a : Perm α) (b : Perm β) :
    Equiv.Perm.cycleType (Equiv.sumCongr a b) = a.cycleType + b.cycleType := by
  have hsplit : (Equiv.sumCongr a b : Perm (α ⊕ β))
      = (Equiv.sumCongr a (1 : Perm β) : Perm (α ⊕ β))
        * (Equiv.sumCongr (1 : Perm α) b : Perm (α ⊕ β)) := by
    ext x; cases x <;> simp [Equiv.sumCongr_apply]
  have hdisj : Equiv.Perm.Disjoint (Equiv.sumCongr a (1 : Perm β) : Perm (α ⊕ β))
      (Equiv.sumCongr (1 : Perm α) b : Perm (α ⊕ β)) := by
    intro x
    cases x with
    | inl a' => right; simp [Equiv.sumCongr_apply]
    | inr b' => left; simp [Equiv.sumCongr_apply]
  rw [hsplit, hdisj.cycleType_mul, cycleType_sumCongr_left, cycleType_sumCongr_right]

end CycleTypeTransfer

/-- Bridge to the unitary Gram data: `loops (qPair τ) (qPair ρ) = c (τ⁻¹ * ρ)`. The product
`qPair τ * qPair ρ` is block-diagonal `sumCongr (τ⁻¹ρ) (τρ⁻¹)` through `pairEquiv`, so its
cycle count splits as `c(τ⁻¹ρ) + c(τρ⁻¹) = 2 c(τ⁻¹ρ)` (the two blocks are inverse-symmetric,
`cycleCount_mul_inv_comm`); halving gives the loop count. Blueprint: `lem:loops_q_q`
(check PL1). -/
theorem loops_qPair_qPair {n : ℕ} (τ ρ : Equiv.Perm (Fin n)) :
    (qPair τ).loops (qPair ρ) = cycleCount n (τ⁻¹ * ρ) := by
  have hprod : swapAcrossPerm τ * swapAcrossPerm ρ
      = Equiv.sumCongr (τ⁻¹ * ρ) (τ * ρ⁻¹) := by
    ext x
    cases x with
    | inl a => simp [Equiv.Perm.mul_apply, Equiv.sumCongr_apply]
    | inr b => simp [Equiv.Perm.mul_apply, Equiv.sumCongr_apply]
  have hQ : (qPair τ).1 * (qPair ρ).1
      = (pairEquiv n).symm.permCongr (Equiv.sumCongr (τ⁻¹ * ρ) (τ * ρ⁻¹)) := by
    show (pairEquiv n).symm.permCongr (swapAcrossPerm τ)
        * (pairEquiv n).symm.permCongr (swapAcrossPerm ρ) = _
    rw [← Equiv.permCongr_mul, hprod]
  have hct : ((qPair τ).1 * (qPair ρ).1).cycleType
      = (τ⁻¹ * ρ).cycleType + (τ * ρ⁻¹).cycleType := by
    rw [hQ, cycleType_permCongr, cycleType_sumCongr]
  have hs1 : (τ⁻¹ * ρ).cycleType.sum ≤ n := by
    have := Equiv.Perm.sum_cycleType_le (τ⁻¹ * ρ); simpa using this
  have hs2 : (τ * ρ⁻¹).cycleType.sum ≤ n := by
    have := Equiv.Perm.sum_cycleType_le (τ * ρ⁻¹); simpa using this
  have hcc : cycleCount (2 * n) ((qPair τ).1 * (qPair ρ).1)
      = cycleCount n (τ⁻¹ * ρ) + cycleCount n (τ * ρ⁻¹) := by
    rw [cycleCount_eq, cycleCount_eq, cycleCount_eq, hct,
      Multiset.card_add, Multiset.sum_add]
    omega
  show cycleCount (2 * n) ((qPair τ).1 * (qPair ρ).1) / 2 = cycleCount n (τ⁻¹ * ρ)
  rw [hcc, cycleCount_mul_inv_comm n τ ρ]
  omega

/-- The determinant vector: supported on the permutation-like pairings, with
sign weights. Blueprint: `def:det_vector`. -/
def detVec (k : Type*) [CommRing k] {n : ℕ} : Pairing n → k := fun p =>
  ∑ ρ : Equiv.Perm (Fin n),
    if p = qPair ρ then ((Equiv.Perm.sign ρ : ℤ) : k) else 0

/-- The ε vector: crossing parities as ring elements. Blueprint:
`def:eps_vector`. -/
def epsVec (k : Type*) [CommRing k] {n : ℕ} : Pairing n → k := fun p =>
  ((epsSign p : ℤ) : k)

section CanonicalWord

/-- A pairing is an involution: `p (p x) = x`. -/
theorem pairing_invol {n : ℕ} (p : Pairing n) (x : Fin (2 * n)) : p.1 (p.1 x) = x := by
  have h : (p.1 * p.1) x = x := by rw [p.2.1]; rfl
  rwa [Equiv.Perm.mul_apply] at h

/-- A pairing of `Fin (2n)` has exactly `n` left endpoints. -/
theorem leftEnds_card {n : ℕ} (p : Pairing n) :
    (Finset.univ.filter (fun x => x < p.1 x)).card = n := by
  set L := Finset.univ.filter (fun x : Fin (2 * n) => x < p.1 x) with hL
  set R := Finset.univ.filter (fun x : Fin (2 * n) => p.1 x < x) with hR
  have hcover : L ∪ R = Finset.univ := by
    ext x
    simp only [hL, hR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy x (p.1 x) with h | h | h
    · exact Or.inl h
    · exact absurd h.symm (p.2.2 x)
    · exact Or.inr h
  have hdisj : Disjoint L R := by
    simp only [Finset.disjoint_left, hL, hR, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x h1 h2; exact absurd h1 (not_lt.mpr h2.le)
  have himg : L.image p.1 = R := by
    ext y
    simp only [hL, hR, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [pairing_invol p x]; exact hx
    · intro hy; exact ⟨p.1 y, by rw [pairing_invol p y]; exact hy, pairing_invol p y⟩
  have hcardR : R.card = L.card := by
    rw [← himg, Finset.card_image_of_injective _ p.1.injective]
  have htot : L.card + R.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ, Fintype.card_fin]
  omega

/-- The `i`-th smallest left endpoint `a_0 < a_1 < ⋯ < a_{n-1}`. -/
def leftEndEmb {n : ℕ} (p : Pairing n) : Fin n ↪o Fin (2 * n) :=
  (Finset.univ.filter (fun x => x < p.1 x)).orderEmbOfFin (leftEnds_card p)

theorem leftEndEmb_lt {n : ℕ} (p : Pairing n) (i : Fin n) :
    leftEndEmb p i < p.1 (leftEndEmb p i) := by
  have h := Finset.orderEmbOfFin_mem (Finset.univ.filter (fun x => x < p.1 x))
    (leftEnds_card p) i
  rw [Finset.mem_filter] at h
  exact h.2

/-- The interleaving map `(i, 0) ↦ a_i`, `(i, 1) ↦ p(a_i)`. -/
def cwMap {n : ℕ} (p : Pairing n) (q : Fin n × Fin 2) : Fin (2 * n) :=
  if q.2 = 0 then leftEndEmb p q.1 else p.1 (leftEndEmb p q.1)

theorem cwMap_injective {n : ℕ} (p : Pairing n) : Function.Injective (cwMap p) := by
  intro q q' h
  by_cases hq : q.2 = 0 <;> by_cases hq' : q'.2 = 0 <;>
    simp only [cwMap, hq, hq', if_true, if_false] at h
  · exact Prod.ext ((leftEndEmb p).injective h) (by rw [hq, hq'])
  · exfalso
    have h1 := leftEndEmb_lt p q.1
    rw [h, pairing_invol] at h1
    exact absurd (leftEndEmb_lt p q'.1) (not_lt.mpr h1.le)
  · exfalso
    have h1 := leftEndEmb_lt p q'.1
    rw [← h, pairing_invol] at h1
    exact absurd (leftEndEmb_lt p q.1) (not_lt.mpr h1.le)
  · exact Prod.ext ((leftEndEmb p).injective (p.1.injective h)) (by omega)

theorem cwMap_bij {n : ℕ} (p : Pairing n) : Function.Bijective (cwMap p) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨cwMap_injective p, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- `Fin (2n) ≃ Fin n × Fin 2`, position `2*i + j ↦ (i, j)`. -/
def posEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (show 2 * n = n * 2 by ring)).trans finProdFinEquiv.symm

/-- The canonical interleaving word of a pairing: the permutation sending
`(0, 1, 2, 3, …)` to `(a₀, b₀, a₁, b₁, …)`, the pairs listed with `aᵢ < bᵢ`
and `a₀ < a₁ < ⋯`. Blueprint: `def:canonical_word`. -/
noncomputable def canonicalWord {n : ℕ} (p : Pairing n) : Equiv.Perm (Fin (2 * n)) :=
  (posEquiv n).trans (Equiv.ofBijective (cwMap p) (cwMap_bij p))

theorem canonicalWord_apply {n : ℕ} (p : Pairing n) (y : Fin (2 * n)) :
    canonicalWord p y = cwMap p (posEquiv n y) := by
  simp [canonicalWord]

end CanonicalWord

section SignCanonicalWord
open Equiv Equiv.Perm Finset

variable {n : ℕ}

-- value of (posEquiv n).symm (i,u) is 2*i + u
theorem posEquiv_symm_val (i : Fin n) (u : Fin 2) :
    ((posEquiv n).symm (i, u) : Fin (2*n)).val = 2 * i.val + u.val := by
  simp only [posEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
    finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
  ring

-- canonicalWord at posEquiv.symm
theorem canonicalWord_posEquiv_symm (p : Pairing n) (i : Fin n) (u : Fin 2) :
    canonicalWord p ((posEquiv n).symm (i, u)) = cwMap p (i, u) := by
  rw [canonicalWord_apply, Equiv.apply_symm_apply]

-- Step A: flat filtered product form of the sign.
theorem sign_flat (σ : Equiv.Perm (Fin (2*n))) :
    ((σ.sign : ℤ)) =
      ∏ q ∈ (univ : Finset (Fin (2*n) × Fin (2*n))).filter (fun q => q.1 < q.2),
        (if σ q.1 < σ q.2 then (1:ℤ) else -1) := by
  rw [σ.sign_eq_prod_prod_Iio]
  push_cast
  rw [Finset.prod_finset_product_right' (β := ℤ)
      (univ.filter (fun q : Fin (2*n) × Fin (2*n) => q.1 < q.2))
      univ (fun c => Iio c)
      (by intro p; simp [Finset.mem_filter, Finset.mem_Iio])
      (f := fun a c => if σ a < σ c then (1:ℤ) else -1)]
  apply Finset.prod_congr rfl; intro x _
  apply Finset.prod_congr rfl; intro i _
  split <;> simp

-- Step A': full (unfiltered) product form.
theorem sign_full (σ : Equiv.Perm (Fin (2*n))) :
    ((σ.sign : ℤ)) =
      ∏ q : Fin (2*n) × Fin (2*n),
        (if q.1 < q.2 ∧ σ q.2 < σ q.1 then (-1:ℤ) else 1) := by
  rw [sign_flat σ, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q.1 < q.2
  · simp only [h, true_and, if_true]
    have hne : σ q.1 ≠ σ q.2 := fun he => (ne_of_lt h) (σ.injective he)
    by_cases h2 : σ q.1 < σ q.2
    · rw [if_pos h2, if_neg (by exact not_lt.mpr h2.le)]
    · rw [if_neg h2, if_pos (lt_of_le_of_ne (not_lt.mp h2) (fun he => hne he.symm))]
  · simp [h]

/-- The "interleaving factor" for the chord pair `(i,j)`: the product over the two parities
`u,v` of the inversion sign for positions `posEquiv.symm (i,u)` vs `posEquiv.symm (j,v)`. -/
def chordFactor (σ : Equiv.Perm (Fin (2*n))) (i j : Fin n) : ℤ :=
  ∏ u : Fin 2, ∏ v : Fin 2,
    (if ((posEquiv n).symm (i,u) < (posEquiv n).symm (j,v)
        ∧ σ ((posEquiv n).symm (j,v)) < σ ((posEquiv n).symm (i,u))) then (-1:ℤ) else 1)

-- Step B: reindex to chord coordinates, grouped per chord pair.
theorem sign_chord (σ : Equiv.Perm (Fin (2*n))) :
    ((σ.sign : ℤ)) = ∏ i : Fin n, ∏ j : Fin n, chordFactor σ i j := by
  rw [sign_full σ]
  rw [← Equiv.prod_comp (Equiv.prodCongr (posEquiv n).symm (posEquiv n).symm)
        (fun q => if q.1 < q.2 ∧ σ q.2 < σ q.1 then (-1:ℤ) else 1)]
  simp only [Equiv.prodCongr_apply]
  rw [Fintype.prod_prod_type]
  unfold chordFactor
  rw [show (∏ i : Fin n, ∏ j : Fin n, ∏ u : Fin 2, ∏ v : Fin 2,
        (if ((posEquiv n).symm (i,u) < (posEquiv n).symm (j,v)
          ∧ σ ((posEquiv n).symm (j,v)) < σ ((posEquiv n).symm (i,u))) then (-1:ℤ) else 1))
      = ∏ P1 : Fin n × Fin 2, ∏ P2 : Fin n × Fin 2,
          (if ((posEquiv n).symm P1 < (posEquiv n).symm P2
            ∧ σ ((posEquiv n).symm P2) < σ ((posEquiv n).symm P1)) then (-1:ℤ) else 1) from ?_]
  · rfl
  · rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl; intro i _
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl; intro j _
    rw [Fintype.prod_prod_type]

-- position comparison: posEquiv.symm (i,u) < posEquiv.symm (j,v) ↔ 2i+u < 2j+v
theorem posEquiv_symm_lt (i j : Fin n) (u v : Fin 2) :
    (posEquiv n).symm (i,u) < (posEquiv n).symm (j,v) ↔ 2 * i.val + u.val < 2 * j.val + v.val := by
  rw [Fin.lt_def, posEquiv_symm_val, posEquiv_symm_val]

-- cwMap values
theorem cwMap_zero (p : Pairing n) (i : Fin n) : cwMap p (i, 0) = leftEndEmb p i := by
  simp [cwMap]
theorem cwMap_one (p : Pairing n) (i : Fin n) : cwMap p (i, 1) = p.1 (leftEndEmb p i) := by
  simp [cwMap]

-- expand the product over Fin 2 × Fin 2
theorem chordFactor_expand (σ : Equiv.Perm (Fin (2*n))) (i j : Fin n) :
    chordFactor σ i j =
      (if ((posEquiv n).symm (i,0) < (posEquiv n).symm (j,0)
          ∧ σ ((posEquiv n).symm (j,0)) < σ ((posEquiv n).symm (i,0))) then (-1:ℤ) else 1)
    * (if ((posEquiv n).symm (i,0) < (posEquiv n).symm (j,1)
          ∧ σ ((posEquiv n).symm (j,1)) < σ ((posEquiv n).symm (i,0))) then (-1:ℤ) else 1)
    * (if ((posEquiv n).symm (i,1) < (posEquiv n).symm (j,0)
          ∧ σ ((posEquiv n).symm (j,0)) < σ ((posEquiv n).symm (i,1))) then (-1:ℤ) else 1)
    * (if ((posEquiv n).symm (i,1) < (posEquiv n).symm (j,1)
          ∧ σ ((posEquiv n).symm (j,1)) < σ ((posEquiv n).symm (i,1))) then (-1:ℤ) else 1) := by
  unfold chordFactor
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  ring

-- abbreviations
theorem leftEndEmb_lt_iff (p : Pairing n) {i j : Fin n} :
    leftEndEmb p i < leftEndEmb p j ↔ i < j := (leftEndEmb p).lt_iff_lt

-- chordFactor of canonicalWord, case i < j
theorem chordFactor_lt (p : Pairing n) {i j : Fin n} (hij : i < j) :
    chordFactor (canonicalWord p) i j =
      (if leftEndEmb p j < p.1 (leftEndEmb p i) then (-1:ℤ) else 1)
    * (if p.1 (leftEndEmb p j) < p.1 (leftEndEmb p i) then (-1:ℤ) else 1) := by
  rw [chordFactor_expand]
  have hAA : leftEndEmb p i < leftEndEmb p j := (leftEndEmb_lt_iff p).mpr hij
  have hpos : ∀ u v : Fin 2, (posEquiv n).symm (i,u) < (posEquiv n).symm (j,v) := by
    intro u v
    rw [posEquiv_symm_lt]
    have : i.val < j.val := hij
    have hu : u.val < 2 := u.isLt
    have hv : v.val ≤ v.val := le_refl _
    omega
  simp only [canonicalWord_posEquiv_symm, cwMap_zero, cwMap_one,
    hpos, true_and]
  have hAi_lt_Bi : leftEndEmb p i < p.1 (leftEndEmb p i) := leftEndEmb_lt p i
  have hAj_lt_Bj : leftEndEmb p j < p.1 (leftEndEmb p j) := leftEndEmb_lt p j
  rw [if_neg (by exact not_lt.mpr hAA.le)]
  rw [if_neg (by exact not_lt.mpr (hAA.trans hAj_lt_Bj).le)]
  ring

-- chordFactor of canonicalWord, case j ≤ i  (vanishes to 1)
theorem chordFactor_ge (p : Pairing n) {i j : Fin n} (hji : j ≤ i) :
    chordFactor (canonicalWord p) i j = 1 := by
  rw [chordFactor_expand]
  simp only [canonicalWord_posEquiv_symm, cwMap_zero, cwMap_one]
  have hAi_lt_Bi : leftEndEmb p i < p.1 (leftEndEmb p i) := leftEndEmb_lt p i
  have hv0 : (0 : Fin 2).val = 0 := rfl
  have hv1 : (1 : Fin 2).val = 1 := rfl
  by_cases he : i = j
  · subst he
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i i 0 0).mp hc.1; omega)]
    rw [if_neg (fun hc => absurd hc.2 (not_lt.mpr hAi_lt_Bi.le))]
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i i 1 0).mp hc.1; omega)]
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i i 1 1).mp hc.1; omega)]
    ring
  · have hji' : j.val < i.val := lt_of_le_of_ne hji (fun h => he (Fin.ext h.symm))
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i j 0 0).mp hc.1; omega)]
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i j 0 1).mp hc.1; omega)]
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i j 1 0).mp hc.1; omega)]
    rw [if_neg (fun hc => by
      have h := (posEquiv_symm_lt i j 1 1).mp hc.1; omega)]
    ring

/-- The crossing indicator for the chord pair `(i,j)`: `1` if `i < j` and the chords
`(A i, B i)`, `(A j, B j)` cross, else `0`. -/
def crossInd (p : Pairing n) (i j : Fin n) : ℕ :=
  if (i < j ∧ leftEndEmb p i < leftEndEmb p j
      ∧ leftEndEmb p j < p.1 (leftEndEmb p i)
      ∧ p.1 (leftEndEmb p i) < p.1 (leftEndEmb p j)) then 1 else 0

theorem chordFactor_eq_pow (p : Pairing n) (i j : Fin n) :
    chordFactor (canonicalWord p) i j = (-1 : ℤ) ^ (crossInd p i j) := by
  unfold crossInd
  by_cases hij : i < j
  · rw [chordFactor_lt p hij]
    have hAA : leftEndEmb p i < leftEndEmb p j := (leftEndEmb_lt_iff p).mpr hij
    have hAi_lt_Bi : leftEndEmb p i < p.1 (leftEndEmb p i) := leftEndEmb_lt p i
    have hAj_lt_Bj : leftEndEmb p j < p.1 (leftEndEmb p j) := leftEndEmb_lt p j
    have hBne : p.1 (leftEndEmb p i) ≠ p.1 (leftEndEmb p j) := by
      intro h; exact (ne_of_lt hAA) (p.1.injective h)
    by_cases h1 : leftEndEmb p j < p.1 (leftEndEmb p i)
    · by_cases h2 : p.1 (leftEndEmb p j) < p.1 (leftEndEmb p i)
      · rw [if_pos h1, if_pos h2]
        rw [if_neg (by rintro ⟨_,_,_,h4⟩; exact absurd h4 (not_lt.mpr h2.le))]
        norm_num
      · rw [if_pos h1, if_neg h2]
        have hBiBj : p.1 (leftEndEmb p i) < p.1 (leftEndEmb p j) :=
          lt_of_le_of_ne (not_lt.mp h2) hBne
        rw [if_pos ⟨hij, hAA, h1, hBiBj⟩]
        norm_num
    · have h2 : ¬ p.1 (leftEndEmb p j) < p.1 (leftEndEmb p i) := by
        intro h2
        have : p.1 (leftEndEmb p j) < leftEndEmb p j := lt_of_lt_of_le h2 (not_lt.mp h1)
        exact absurd this (not_lt.mpr hAj_lt_Bj.le)
      rw [if_neg h1, if_neg h2]
      rw [if_neg (by rintro ⟨_,_,h3,_⟩; exact absurd h3 h1)]
      norm_num
  · rw [chordFactor_ge p (not_lt.mp hij)]
    rw [if_neg (by rintro ⟨h,_⟩; exact absurd h hij)]
    norm_num

-- every left endpoint is in the range of leftEndEmb
theorem exists_leftEndEmb (p : Pairing n) {a : Fin (2*n)} (ha : a < p.1 a) :
    ∃ i, leftEndEmb p i = a := by
  have : a ∈ Set.range (leftEndEmb p) := by
    rw [leftEndEmb, Finset.range_orderEmbOfFin]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ha
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

-- the bridge: Σ_{i,j} crossInd = crossings
theorem sum_crossInd_eq_crossings (p : Pairing n) :
    ∑ i : Fin n, ∑ j : Fin n, crossInd p i j = p.crossings := by
  have hLHS : ∑ i : Fin n, ∑ j : Fin n, crossInd p i j
      = ((univ : Finset (Fin n × Fin n)).filter (fun ij =>
          ij.1 < ij.2 ∧ leftEndEmb p ij.1 < leftEndEmb p ij.2
          ∧ leftEndEmb p ij.2 < p.1 (leftEndEmb p ij.1)
          ∧ p.1 (leftEndEmb p ij.1) < p.1 (leftEndEmb p ij.2))).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rfl
  rw [hLHS, Pairing.crossings]
  apply Finset.card_bij (fun ij _ => (leftEndEmb p ij.1, leftEndEmb p ij.2))
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hij
    exact ⟨leftEndEmb_lt p i, leftEndEmb_lt p j, h2, h3, h4⟩
  · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext ((leftEndEmb p).injective heq.1) ((leftEndEmb p).injective heq.2)
  · rintro ⟨a, c⟩ hac
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hac
    obtain ⟨ha, hc, hac', hcpa, hpapc⟩ := hac
    obtain ⟨i, rfl⟩ := exists_leftEndEmb p ha
    obtain ⟨j, rfl⟩ := exists_leftEndEmb p hc
    refine ⟨(i, j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hij : i < j := (leftEndEmb_lt_iff p).mp hac'
    exact ⟨hij, hac', hcpa, hpapc⟩

/-- The sign of the canonical word is the crossing parity — the Pfaffian sign
identity. Blueprint: `lem:sign_canonical_word`. -/
theorem sign_canonicalWord (p : Pairing n) :
    ((Equiv.Perm.sign (canonicalWord p) : ℤ)) = (-1) ^ p.crossings := by
  rw [sign_chord (canonicalWord p)]
  have : ∀ i : Fin n, ∏ j : Fin n, chordFactor (canonicalWord p) i j
      = (-1 : ℤ) ^ (∑ j : Fin n, crossInd p i j) := by
    intro i
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl; intro j _
    exact chordFactor_eq_pow p i j
  simp_rw [this]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← sum_crossInd_eq_crossings p]

end SignCanonicalWord


end Weingarten
