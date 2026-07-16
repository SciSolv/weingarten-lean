/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.JucysMurphy
import Weingarten.CycleCount

/-!
# The Gram element and the Jucys factorization

The factorization `gram_eq_prod` is proved over any commutative ring and any `N`
(`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`).
Blueprint: `def:gram`, `thm:jucys`, `lem:gram_central`.

`gram k n N = ∑ σ, N ^ cycleCount σ • σ` collects the Gram data of the
Haar-orthogonality pairing, over an arbitrary commutative ring `k`. The keystone is the
factorization `gram k n N = (N + K 0) * (N + K 1) * ⋯ * (N + K (n-1))`, by induction on
`n`: `Equiv.Perm.decomposeFin` peels off `(N + K 0)` on the left and the successor
embedding sends `K i ↦ K (i+1)`, with exponents handled by the splice rule
`cycleCount_decomposeFin`. The identity is polynomial in `N` and needs no
invertibility, division, or order — this is what powers the below-threshold package.
Numerically verified for `n ≤ 5` at several rational `N`, including `N < n` and
fractional `N` (checks C3, B2).
-/

namespace Weingarten

open Equiv Equiv.Perm MonoidAlgebra

/-- Gram element `∑ σ, N ^ cycleCount σ • σ`. Blueprint: `def:gram`. -/
noncomputable def gram (k : Type*) [CommRing k] (n : ℕ) (N : k) : SymAlg k n :=
  ∑ σ : Equiv.Perm (Fin n),
    (N ^ cycleCount n σ) • MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ

/-- Ordered product `(N + K 0) * (N + K 1) * ⋯ * (N + K (n-1))`, increasing index left
to right. -/
noncomputable def gramProd (k : Type*) [CommRing k] (n : ℕ) (N : k) : SymAlg k n :=
  ((List.finRange n).map fun i => algebraMap k (SymAlg k n) N + jm k n i).prod

/-- Coefficient extraction for the Gram element: the `σ`-coefficient of `gram k n N` is
`N ^ cycleCount n σ`. -/
theorem gram_apply (k : Type*) [CommRing k] (n : ℕ) (N : k) (σ : Equiv.Perm (Fin n)) :
    (gram k n N) σ = N ^ cycleCount n σ := by
  let L : SymAlg k n →ₗ[k] k := Finsupp.lapply σ
  have hlap : ∀ x : SymAlg k n, x σ = L x := fun x =>
    (Finsupp.lapply_apply σ x).symm
  rw [hlap]
  unfold gram
  rw [map_sum]
  rw [Finset.sum_eq_single σ]
  · rw [map_smul]
    show _ • L (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) = _
    rw [show L (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
          = (MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ) σ from Finsupp.lapply_apply σ _,
      MonoidAlgebra.of_apply, MonoidAlgebra.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [map_smul]
    show _ • L (MonoidAlgebra.of k (Equiv.Perm (Fin n)) b) = _
    rw [show L (MonoidAlgebra.of k (Equiv.Perm (Fin n)) b)
          = (MonoidAlgebra.of k (Equiv.Perm (Fin n)) b) σ from Finsupp.lapply_apply σ _,
      MonoidAlgebra.of_apply, MonoidAlgebra.single_apply, if_neg hb, smul_zero]
  · intro h; exact absurd (Finset.mem_univ σ) h

section Factorization

variable (k : Type*) [CommRing k]

/-- Successor embedding `Fin n ↪ Fin (n+1)`. -/
private def emb (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩

@[simp] private lemma emb_apply (n : ℕ) (x : Fin n) : emb n x = x.succ := rfl

/-- The algebra map `SymAlg k n →ₐ SymAlg k (n+1)` induced by `ι` ("fix 0, act on
successors"). -/
private noncomputable def iotaAlg (n : ℕ) : SymAlg k n →ₐ[k] SymAlg k (n + 1) :=
  MonoidAlgebra.mapDomainAlgHom k k (Equiv.Perm.viaEmbeddingHom (emb n))

/-- `ι` on a basis element: `ι(e) = decomposeFin.symm (0, e)`. -/
private lemma iota_of (n : ℕ) (e : Equiv.Perm (Fin n)) :
    iotaAlg k n (MonoidAlgebra.of k (Equiv.Perm (Fin n)) e)
      = MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) (decomposeFin.symm (0, e)) := by
  rw [iotaAlg, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.mapDomain_single, ← MonoidAlgebra.of_apply]
  congr 1
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  symm
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [decomposeFin_symm_apply_zero, viaEmbedding_apply_of_notMem]
    rintro ⟨y, hy⟩
    exact Fin.succ_ne_zero y hy
  · rw [decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    have hva : (e.viaEmbedding (emb n)) j.succ = (emb n) (e j) := viaEmbedding_apply e (emb n) j
    rw [hva, emb_apply]

/-- `ι` sends the transposition `(i j)` to `(i.succ j.succ)`. -/
private lemma iota_swap (n : ℕ) (i j : Fin n) :
    decomposeFin.symm ((0 : Fin (n + 1)), Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  ext x
  refine Fin.cases ?_ (fun m => ?_) x
  · rw [decomposeFin_symm_apply_zero, Equiv.swap_apply_of_ne_of_ne
      (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  · rw [decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      ← (Fin.succ_injective n).map_swap]

private lemma image_succ_Ioi (n : ℕ) (i : Fin n) :
    (Finset.Ioi i).image Fin.succ = Finset.Ioi i.succ := by
  ext l
  simp only [Finset.mem_image, Finset.mem_Ioi]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact Fin.succ_lt_succ_iff.mpr hj
  · intro hl
    have hl0 : l ≠ 0 := ((Fin.succ_pos i).trans hl).ne'
    refine ⟨l.pred hl0, ?_, Fin.succ_pred l hl0⟩
    rwa [Fin.lt_pred_iff]

/-- `ι` shifts Jucys–Murphy elements: `ι_*(K i) = K (i+1)`. -/
private lemma iota_K (n : ℕ) (i : Fin n) :
    iotaAlg k n (jm k n i) = jm k (n + 1) i.succ := by
  unfold Weingarten.jm
  rw [map_sum]
  have : ∀ j, iotaAlg k n (MonoidAlgebra.of k (Equiv.Perm (Fin n)) (Equiv.swap i j))
      = MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) (Equiv.swap i.succ j.succ) := by
    intro j; rw [iota_of, iota_swap]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  rw [← image_succ_Ioi, Finset.sum_image (fun x _ y _ h => Fin.succ_injective n h)]

/-- The splice step on the Gram element: `decomposeFin` peels off `(N + K 0)` on the
left, the rest being `ι_*` of the lower Gram element. -/
private lemma gram_succ (n : ℕ) (N : k) :
    gram k (n + 1) N
      = (algebraMap k (SymAlg k (n + 1)) N + jm k (n + 1) 0)
        * iotaAlg k n (gram k n N) := by
  have hiota : iotaAlg k n (gram k n N) = ∑ e : Equiv.Perm (Fin n),
      N ^ cycleCount n e •
        MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) (decomposeFin.symm (0, e)) := by
    unfold Weingarten.gram
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul, iota_of]
  have hcompl : ({(0 : Fin (n + 1))}ᶜ : Finset (Fin (n + 1))) = Finset.Ioi 0 := by
    ext p
    rw [Finset.mem_compl, Finset.mem_singleton, Finset.mem_Ioi, Fin.pos_iff_ne_zero]
  have hleft : (∑ p : Fin (n + 1), (if p = 0 then N else 1) •
      MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) (Equiv.swap 0 p))
        = algebraMap k (SymAlg k (n + 1)) N + jm k (n + 1) 0 := by
    rw [Fintype.sum_eq_add_sum_compl 0]
    congr 1
    · rw [if_pos rfl, Equiv.swap_self]
      show N • MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) 1 = _
      rw [map_one, Algebra.algebraMap_eq_smul_one]
    · unfold Weingarten.jm
      rw [hcompl]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_Ioi] at hp
      have hp0 : p ≠ 0 := (Fin.pos_iff_ne_zero.mp hp)
      rw [if_neg hp0, one_smul]
  rw [← hleft, hiota]
  rw [Finset.sum_mul_sum]
  unfold Weingarten.gram
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := n)).symm
        (fun σ => N ^ cycleCount (n + 1) σ •
          MonoidAlgebra.of k (Equiv.Perm (Fin (n + 1))) σ)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro e _
  have hexp : N ^ (if p = 0 then 1 else 0) = if p = 0 then N else 1 := by
    by_cases h : p = 0 <;> simp [h]
  rw [Weingarten.cycleCount_decomposeFin, pow_add, hexp]
  rw [Weingarten.decomposeFin_symm_eq, map_mul]
  rw [smul_mul_smul_comm]
  rw [mul_comm (N ^ cycleCount n e) (if p = 0 then N else 1)]

/-- The matching splice step on the formal product `(N + K 0) ⋯`. -/
private lemma prod_succ (n : ℕ) (N : k) :
    gramProd k (n + 1) N
      = (algebraMap k (SymAlg k (n + 1)) N + jm k (n + 1) 0)
        * iotaAlg k n (gramProd k n N) := by
  set tail : SymAlg k (n + 1) :=
    ((List.finRange n).map
      (fun j => algebraMap k (SymAlg k (n + 1)) N + jm k (n + 1) j.succ)).prod
      with htail_def
  have hLHS : gramProd k (n + 1) N
      = (algebraMap k (SymAlg k (n + 1)) N + jm k (n + 1) 0) * tail := by
    unfold Weingarten.gramProd
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    rfl
  have hRHS : iotaAlg k n (gramProd k n N) = tail := by
    unfold Weingarten.gramProd
    rw [map_list_prod, List.map_map, htail_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, map_add, AlgHom.commutes, iota_K]
  rw [hLHS, hRHS]

/-- **Jucys factorization, dual form**, valid over any commutative ring and any `N`.
Blueprint: `thm:jucys` (check C3). -/
theorem gram_eq_prod (n : ℕ) (N : k) :
    gram k n N = gramProd k n N := by
  induction n with
  | zero =>
    rw [gram, gramProd]
    simp only [List.finRange_zero, List.map_nil, List.prod_nil]
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 0))]
    simp [cycleCount, MonoidAlgebra.one_def]
  | succ n ih => rw [gram_succ, ih, ← prod_succ]

end Factorization

/-- The "fix `0`, act on successors" embedding `Perm (Fin n) →* Perm (Fin (n+1))` as a
monoid homomorphism; `iotaHom n e = decomposeFin.symm (0, e)` (`iotaHom_apply`). Reused
by the parity package's shortest-slot-word construction. -/
noncomputable def iotaHom (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.viaEmbeddingHom ⟨Fin.succ, Fin.succ_injective n⟩

theorem iotaHom_apply (n : ℕ) (e : Equiv.Perm (Fin n)) :
    iotaHom n e = Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), e) := by
  set i : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩ with hi
  show e.viaEmbedding i = _
  symm
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [decomposeFin_symm_apply_zero, viaEmbedding_apply_of_notMem]
    rintro ⟨y, hy⟩
    exact Fin.succ_ne_zero y hy
  · rw [decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    have hva : (e.viaEmbedding i) j.succ = i (e j) := viaEmbedding_apply e i j
    rw [hva]; rfl

/-- `ι` sends the transposition `(i j)` to `(i.succ j.succ)`. -/
theorem iotaHom_swap (n : ℕ) (i j : Fin n) :
    iotaHom n (Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  rw [iotaHom_apply]
  ext x
  refine Fin.cases ?_ (fun m => ?_) x
  · rw [decomposeFin_symm_apply_zero, Equiv.swap_apply_of_ne_of_ne
      (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  · rw [decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
      ← (Fin.succ_injective n).map_swap]

/-- **Centrality of the Gram element**: `cycleCount` is a class function
(`cycleCount_conj`), so `gram k n N` commutes with every element of the group
algebra. On a basis element `g` both products reindex to `∑ ρ, N ^ c(ρ) • ρ`-shaped
sums whose exponents `c(ρ g⁻¹)` and `c(g⁻¹ ρ)` agree by conjugation invariance.
This supplies, for free, the commutation hypothesis of Penrose-partner uniqueness
(`gram_penrose_partner_unique` in `Weingarten.BelowThreshold`).
Blueprint: `lem:gram_central`. -/
theorem gram_central (k : Type*) [CommRing k] (n : ℕ) (N : k) (x : SymAlg k n) :
    Commute (gram k n N) x := by
  have key : ∀ g : Equiv.Perm (Fin n),
      gram k n N * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
        = MonoidAlgebra.of k (Equiv.Perm (Fin n)) g * gram k n N := by
    intro g
    unfold Weingarten.gram
    rw [Finset.sum_mul, Finset.mul_sum]
    have stepR : ∀ σ : Equiv.Perm (Fin n),
        (N ^ cycleCount n σ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
            * MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
          = N ^ cycleCount n σ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (σ * g) := by
      intro σ
      rw [smul_mul_assoc, ← map_mul]
    have stepL : ∀ σ : Equiv.Perm (Fin n),
        MonoidAlgebra.of k (Equiv.Perm (Fin n)) g
            * (N ^ cycleCount n σ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) σ)
          = N ^ cycleCount n σ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (g * σ) := by
      intro σ
      rw [mul_smul_comm, ← map_mul]
    rw [Finset.sum_congr rfl (fun σ _ => stepR σ),
      Finset.sum_congr rfl (fun σ _ => stepL σ)]
    rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)
        (fun ρ => N ^ cycleCount n ρ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (ρ * g)),
      ← Equiv.sum_comp (Equiv.mulLeft g⁻¹)
        (fun ρ => N ^ cycleCount n ρ • MonoidAlgebra.of k (Equiv.Perm (Fin n)) (g * ρ))]
    simp only [Equiv.coe_mulRight, Equiv.coe_mulLeft, inv_mul_cancel_right,
      mul_inv_cancel_left]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    have h1 : g⁻¹ * ρ = g⁻¹ * (ρ * g⁻¹) * (g⁻¹)⁻¹ := by group
    rw [h1, cycleCount_conj]
  induction x using MonoidAlgebra.induction_on with
  | hM m => exact key m
  | hadd x y hx hy => exact hx.add_right hy
  | hsmul r x hx => exact hx.smul_right r

end Weingarten
