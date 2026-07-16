/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.SumRules

/-!
# The parity sign theorem in the stable range

Blueprint: `lem:sign_word`, `lem:expansion`, `lem:exists_monotone`, `thm:parity`.

All four are proved and elaborated: `sign_prod_swaps` (`lem:sign_word`),
`exists_min_word` (`lem:exists_monotone`, the shortest-slot-word witness verified by
check C5), the Neumann expansion `wg_expansion` (`lem:expansion`) — distributing the `n`
Neumann series of `𝒲 = ∏(N+Kᵢ)⁻¹` in the Banach algebra and extracting the
`δ_σ`-coefficient with uniform sign (`sign_prod_swaps`) and nonnegative integer counts —
and the parity theorem `wg_sign` (`thm:parity`), a one-line positivity
(`Summable.tsum_pos`) from `wg_expansion`'s nonvanishing minimal term
(`exists_min_word`).
-/

namespace Weingarten

open scoped BigOperators
open Equiv Equiv.Perm

/-- The sign of a product of transpositions is `(-1) ^ length`. Blueprint:
`lem:sign_word`. -/
theorem sign_prod_swaps (n : ℕ) (l : List (Equiv.Perm (Fin n)))
    (hl : ∀ τ ∈ l, τ.IsSwap) :
    Equiv.Perm.sign l.prod = (-1) ^ l.length :=
  Equiv.Perm.sign_prod_list_swap hl

/-- **A shortest slot word exists**: slot `i` carries at most one transposition
`(i, f i)` with `i < f i`, the ordered product is `σ`, and exactly
`n - cycleCount σ` slots are used. Blueprint: `lem:exists_monotone` (check C5
constructs this witness for every `σ` with `n ≤ 5`). -/
theorem exists_min_word (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ f : Fin n → Option (Fin n),
      (∀ i j, f i = some j → i < j) ∧
      ((List.finRange n).map
        fun i => ((f i).map fun j => Equiv.swap i j).getD 1).prod = σ ∧
      (Finset.univ.filter fun i => (f i).isSome).card = n - cycleCount n σ := by
  induction n with
  | zero =>
    refine ⟨fun i => i.elim0, ?_, ?_, ?_⟩
    · intro i j _; exact i.elim0
    · simp [List.finRange_zero]
      exact Subsingleton.elim 1 σ
    · simp
  | succ n ih =>
    set p := (decomposeFin σ).1 with hp_def
    set e := (decomposeFin σ).2 with he_def
    have hσ : σ = decomposeFin.symm (p, e) := by
      have : (p, e) = decomposeFin σ := by rw [hp_def, he_def]
      rw [this, Equiv.symm_apply_apply]
    obtain ⟨f', hmono', hprod', hcount'⟩ := ih e
    set f : Fin (n + 1) → Option (Fin (n + 1)) :=
      Fin.cases (if p = 0 then none else some p) (fun j => (f' j).map Fin.succ) with hf_def
    have hf0 : f 0 = if p = 0 then none else some p := by simp [hf_def]
    have hfs : ∀ j : Fin n, f j.succ = (f' j).map Fin.succ := by intro j; simp [hf_def]
    refine ⟨f, ?_, ?_, ?_⟩
    · -- monotone
      intro i k
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hik
        rw [hf0] at hik
        by_cases hp : p = 0
        · rw [if_pos hp] at hik; exact absurd hik (by simp)
        · rw [if_neg hp] at hik
          rw [Option.some_inj] at hik
          rw [← hik]
          exact Fin.pos_iff_ne_zero.mpr hp
      · intro hik
        rw [hfs] at hik
        rw [Option.map_eq_some_iff] at hik
        obtain ⟨a, ha, hak⟩ := hik
        have hja : j < a := hmono' j a ha
        rw [← hak]
        exact Fin.succ_lt_succ_iff.mpr hja
    · -- product
      rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
      have hhead : ((f 0).map fun j => Equiv.swap (0 : Fin (n + 1)) j).getD 1
          = Equiv.swap (0 : Fin (n + 1)) p := by
        rw [hf0]
        by_cases hp : p = 0
        · rw [if_pos hp, hp]; simp [Equiv.swap_self]; rfl
        · rw [if_neg hp]; simp
      have htail : ∀ j : Fin n,
          ((fun i => ((f i).map fun j' => Equiv.swap i j').getD 1) ∘ Fin.succ) j
            = iotaHom n (((f' j).map fun k => Equiv.swap j k).getD 1) := by
        intro j
        simp only [Function.comp_apply]
        rw [hfs]
        cases hfj : f' j with
        | none => simp [map_one]
        | some k =>
          simp only [Option.map_some, Option.getD_some]
          rw [iotaHom_swap]
      rw [hhead]
      rw [List.map_congr_left (fun j _ => htail j)]
      rw [show (fun j : Fin n => iotaHom n (((f' j).map fun k => Equiv.swap j k).getD 1))
            = (iotaHom n) ∘ (fun j : Fin n => ((f' j).map fun k => Equiv.swap j k).getD 1)
          from rfl]
      rw [← List.map_map, ← map_list_prod (iotaHom n), hprod', iotaHom_apply]
      rw [hσ, decomposeFin_symm_eq n p e]
    · -- count
      rw [Finset.card_filter, Fin.sum_univ_succ]
      have hhead : (if (f 0).isSome = true then 1 else 0) = (if p = 0 then 0 else 1) := by
        rw [hf0]; by_cases hp : p = 0 <;> simp [hp]
      have htail : (∑ j : Fin n, if (f j.succ).isSome = true then 1 else 0)
          = (∑ j : Fin n, if (f' j).isSome = true then 1 else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hfs, Option.isSome_map]
      rw [hhead, htail, ← Finset.card_filter, hcount']
      have hcc : cycleCount (n + 1) σ = cycleCount n e + (if p = 0 then 1 else 0) := by
        rw [hσ, cycleCount_decomposeFin]
      have hle : cycleCount n e ≤ n := cycleCount_le n e
      rw [hcc]
      by_cases hp : p = 0
      · rw [if_pos hp, if_pos hp]; omega
      · rw [if_neg hp, if_neg hp]; omega

/-! ### Analytic foundation for the Neumann expansion

The following two lemmas are the verified analytic core of `lem:expansion`. They reduce
the Weingarten element to an `n`-fold product of absolutely convergent geometric series,
which is the starting point for the coefficient-extraction argument below. -/

open scoped Weingarten.L1

/-- The Weingarten element is the ring inverse of the Gram element: `𝒲 = (gram)⁻¹`.
A clean restatement of `def:wgElement` in terms of `Ring.inverse`, suitable for the
Neumann/geometric-series machinery. -/
theorem wgElement_eq_inverse (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN = Ring.inverse (gram ℝ n N) := by
  rw [wgElement, ← Ring.inverse_unit (isUnit_gram n N hN).unit, IsUnit.unit_spec]

/-- **Single-factor Neumann series.** Each Gram factor's inverse is the absolutely
convergent geometric series `(N + Kᵢ)⁻¹ = N⁻¹ ∑ₖ (-N⁻¹ Kᵢ)ᵏ` (valid since
`‖N⁻¹ Kᵢ‖ < 1` in the stable range). This is the per-slot building block of the full
expansion: `gram = ∏ᵢ (N + Kᵢ)` (`gram_eq_prod`), so `𝒲 = ∏ᵢ (N + Kᵢ)⁻¹` distributes
into a product of these series. -/
theorem inverse_add_jm_eq_tsum (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (i : Fin n) :
    Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N + jm ℝ n i)
      = (N⁻¹ : ℝ) • ∑' k : ℕ, (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast i.pos
  have hNpos : 0 < N := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  set x : SymAlg ℝ n := -((N⁻¹ : ℝ) • jm ℝ n i) with hx
  have hxnorm : ‖x‖ < 1 := by rw [hx, norm_neg]; exact norm_smul_jm_lt_one n N hN i
  have hu : IsUnit (algebraMap ℝ (SymAlg ℝ n) N) := (isUnit_iff_ne_zero.mpr hN0).map _
  have hmul : algebraMap ℝ (SymAlg ℝ n) N * ((N⁻¹ : ℝ) • (1 : SymAlg ℝ n)) = 1 := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_inv_cancel₀ hN0, one_smul]
  have hinvA : Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N) = (N⁻¹ : ℝ) • (1 : SymAlg ℝ n) := by
    calc Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N)
        = Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N)
            * (algebraMap ℝ (SymAlg ℝ n) N * ((N⁻¹ : ℝ) • 1)) := by rw [hmul, mul_one]
      _ = (Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N) * algebraMap ℝ (SymAlg ℝ n) N)
            * ((N⁻¹ : ℝ) • 1) := by rw [mul_assoc]
      _ = 1 * ((N⁻¹ : ℝ) • 1) := by rw [Ring.inverse_mul_cancel _ hu]
      _ = (N⁻¹ : ℝ) • 1 := one_mul _
  have hkey : algebraMap ℝ (SymAlg ℝ n) N * ((N⁻¹ : ℝ) • jm ℝ n i) = jm ℝ n i := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_inv_cancel₀ hN0, one_smul]
  have hfac : algebraMap ℝ (SymAlg ℝ n) N + jm ℝ n i
      = algebraMap ℝ (SymAlg ℝ n) N * (1 - x) := by
    rw [hx, mul_sub, mul_one, mul_neg, sub_neg_eq_add, hkey]
  rw [hfac, Ring.inverse_mul (Or.inl hu), ← geom_series_eq_inverse x hxnorm, hinvA,
    mul_smul_comm, mul_one]

/-- **Inverse of a product of pairwise-commuting units.** For a list whose entries are
units and pairwise commute, the inverse of the product is the product of the inverses,
*in the same order* — no reversal, since `Ring.inverse`'s anti-homomorphism reversal is
undone by commutativity. A general ring lemma, used here to invert the Gram factorization
`∏ᵢ (N + Kᵢ)`. -/
theorem inverse_list_prod_of_commute {M : Type*} [Ring M] (l : List M)
    (hu : ∀ x ∈ l, IsUnit x) (hc : ∀ x ∈ l, ∀ y ∈ l, Commute x y) :
    Ring.inverse l.prod = (l.map Ring.inverse).prod := by
  induction l with
  | nil => simp [Ring.inverse_one]
  | cons a l ih =>
    have hcomm : Commute a l.prod :=
      Commute.list_prod_right l a fun y hy => hc a (by simp) y (by simp [hy])
    have ihl : Ring.inverse l.prod = (l.map Ring.inverse).prod :=
      ih (fun x hx => hu x (by simp [hx])) fun x hx y hy =>
        hc x (by simp [hx]) y (by simp [hy])
    rw [List.prod_cons, Ring.mul_inverse_rev' hcomm, List.map_cons, List.prod_cons, ← ihl]
    exact (hcomm.ringInverse_ringInverse).symm.eq

/-- **Product form of the Weingarten element.** Inverting the Jucys factorization
`gram = ∏ᵢ (N + Kᵢ)` (`gram_eq_prod`) factor-by-factor: since the `N + Kᵢ` are units
(`isUnit_add_jm`) and pairwise commute (`jm_comm`, with `algebraMap N` central),
`𝒲 = ∏ᵢ (N + Kᵢ)⁻¹` in the natural slot order. -/
theorem wgElement_eq_prod_inverse (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN
      = ((List.finRange n).map fun i =>
          Ring.inverse (algebraMap ℝ (SymAlg ℝ n) N + jm ℝ n i)).prod := by
  rw [wgElement_eq_inverse, gram_eq_prod, gramProd,
    inverse_list_prod_of_commute _ ?hu ?hc, List.map_map, Function.comp_def]
  case hu =>
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact isUnit_add_jm n N hN i
  case hc =>
    intro x hx y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact Commute.add_left (Algebra.commute_algebraMap_left N _)
      ((Algebra.commute_algebraMap_right N (jm ℝ n i)).add_right (jm_comm ℝ n i j))

/-- **The Weingarten element as a product of Neumann series.** Expanding each factor of
`wgElement_eq_prod_inverse` by `inverse_add_jm_eq_tsum`:
`𝒲 = ∏ᵢ (N⁻¹ ∑ₖ (-N⁻¹ Kᵢ)ᵏ)`. This `n`-fold product of absolutely convergent geometric
series is the precise analytic input to the Cauchy-product / coefficient-extraction
core of `wg_expansion` (proved below). -/
theorem wgElement_eq_prod_tsum (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN
      = ((List.finRange n).map fun i =>
          (N⁻¹ : ℝ) • ∑' k : ℕ, (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k).prod := by
  rw [wgElement_eq_prod_inverse]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  exact inverse_add_jm_eq_tsum n N hN i

/-- The cons-step pointwise identity used to distribute an `(n+1)`-fold product of series:
splitting a multi-index `κ : Fin (n+1) → ℕ` (via `Fin.consEquiv`) into a head `z.1` and a
tail `z.2`, the slot product factors as the head term times the `n`-fold tail product. The
shared crux of `summable_list_prod_norm` and `list_prod_tsum`. -/
private theorem crux_cons {R : Type*} [NormedRing R] (n : ℕ) (f : Fin (n + 1) → ℕ → R)
    (z : ℕ × (Fin n → ℕ)) :
    ((List.finRange (n + 1)).map fun i => f i ((Fin.consEquiv (fun _ => ℕ)) z i)).prod
      = f 0 z.1 * ((List.finRange n).map fun j => f j.succ (z.2 j)).prod := by
  have h0 : (Fin.consEquiv (fun _ => ℕ)) z 0 = z.1 := by
    simp [Fin.consEquiv_apply, Fin.cons_zero]
  have hsucc : ∀ j : Fin n, (Fin.consEquiv (fun _ => ℕ)) z j.succ = z.2 j := by
    intro j; simp [Fin.consEquiv_apply, Fin.cons_succ]
  rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map, h0]
  refine congrArg (f 0 z.1 * ·) (congrArg List.prod (List.map_congr_left ?_))
  intro j _
  simp only [Function.comp_apply]
  rw [hsucc j]

/-- **Absolute summability of the multi-index slot product.** In a complete normed ring,
if each slot family `f i` is absolutely summable then so is the multi-indexed product
`κ ↦ ∏ᵢ f i (κ i)` over `κ : Fin n → ℕ`. This is the side-condition that licenses the
`n`-fold Cauchy product in `list_prod_tsum`. -/
theorem summable_list_prod_norm {R : Type*} [NormedRing R] [CompleteSpace R]
    (n : ℕ) (f : Fin n → ℕ → R) (hf : ∀ i, Summable fun k => ‖f i k‖) :
    Summable fun κ : Fin n → ℕ => ‖((List.finRange n).map fun i => f i (κ i)).prod‖ := by
  induction n with
  | zero =>
    exact Summable.of_finite
  | succ n ih =>
    have hf' : ∀ j : Fin n, Summable fun k => ‖f j.succ k‖ := fun j => hf j.succ
    have htail := ih (fun j => f j.succ) hf'
    have hprod : Summable fun z : ℕ × (Fin n → ℕ) =>
        ‖f 0 z.1 * ((List.finRange n).map fun j => f j.succ (z.2 j)).prod‖ := by
      convert Summable.mul_norm (hf 0) htail using 2 with z
    have key : (fun κ : Fin (n + 1) → ℕ =>
        ‖((List.finRange (n + 1)).map fun i => f i (κ i)).prod‖)
        ∘ (Fin.consEquiv (fun _ => ℕ))
          = fun z : ℕ × (Fin n → ℕ) =>
              ‖f 0 z.1 * ((List.finRange n).map fun j => f j.succ (z.2 j)).prod‖ := by
      funext z
      simp only [Function.comp_apply]
      rw [crux_cons n f z]
    exact (Equiv.summable_iff (Fin.consEquiv (fun _ => ℕ))).mp (key ▸ hprod)

/-- **The `n`-fold Cauchy product as a sum over multi-indices.** In a complete normed
ring, an ordered product of absolutely convergent series distributes into a single sum
over multi-indices `κ : Fin n → ℕ`:
`∏ᵢ (∑ₖ f i k) = ∑_κ ∏ᵢ f i (κ i)`.
The order of the slot product is preserved (no commutativity needed). Proved by induction
on `n`, applying the binary Cauchy product `tsum_mul_tsum_of_summable_norm` at each step
with `summable_list_prod_norm` for the tail. -/
theorem list_prod_tsum {R : Type*} [NormedRing R] [CompleteSpace R]
    (n : ℕ) (f : Fin n → ℕ → R) (hf : ∀ i, Summable fun k => ‖f i k‖) :
    ((List.finRange n).map fun i => ∑' k : ℕ, f i k).prod
      = ∑' κ : Fin n → ℕ, ((List.finRange n).map fun i => f i (κ i)).prod := by
  induction n with
  | zero =>
    simp only [List.finRange_zero, List.map_nil, List.prod_nil]
    rw [tsum_fintype]
    simp
  | succ n ih =>
    have hf' : ∀ j : Fin n, Summable fun k => ‖f j.succ k‖ := fun j => hf j.succ
    have hRHS : (∑' κ : Fin (n + 1) → ℕ,
        ((List.finRange (n + 1)).map fun i => f i (κ i)).prod)
          = ∑' z : ℕ × (Fin n → ℕ),
              f 0 z.1 * ((List.finRange n).map fun j => f j.succ (z.2 j)).prod := by
      rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ => ℕ))
        (fun κ => ((List.finRange (n + 1)).map fun i => f i (κ i)).prod)]
      exact tsum_congr fun z => crux_cons n f z
    have hLHS : ((List.finRange (n + 1)).map fun i => ∑' k : ℕ, f i k).prod
          = (∑' k : ℕ, f 0 k)
              * ((List.finRange n).map fun j => ∑' k : ℕ, f j.succ k).prod := by
      rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map,
        Function.comp_def]
    rw [hLHS, hRHS]
    rw [ih (fun j => f j.succ) hf']
    rw [tsum_mul_tsum_of_summable_norm (hf 0)
      (summable_list_prod_norm n (fun j => f j.succ) hf')]

/-! ### Shared per-slot summability setup

The three expansion lemmas below (`wgElement_eq_tsum`, `wg_eq_tsum_coeff`,
`summable_wg_word_coeff`) all rest on the same per-slot geometric summability in the
stable range; it is set up once here. -/

/-- Per-slot geometric summability: the Neumann series of slot `i` is summable in the
ℓ¹ algebra, since `‖N⁻¹ Kᵢ‖ < 1` in the stable range. -/
private lemma summable_geom_slot (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (i : Fin n) :
    Summable fun k : ℕ => (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k :=
  summable_geometric_of_norm_lt_one
    (by rw [norm_neg]; exact norm_smul_jm_lt_one n N hN i)

/-- Per-slot absolute summability of the scaled Neumann terms. -/
private lemma summable_norm_slot (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (i : Fin n) :
    Summable fun k : ℕ => ‖(N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k‖ :=
  (((summable_geom_slot n N hN i).const_smul (N⁻¹ : ℝ)).norm)

/-- Multi-index (absolute) summability of the slot-product terms, via
`summable_list_prod_norm`. -/
private lemma summable_word_prod (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    Summable (fun κ : Fin n → ℕ =>
      ((List.finRange n).map fun i =>
        (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ (κ i)).prod) :=
  (summable_list_prod_norm n (fun i k => (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k)
    (fun i => summable_norm_slot n N hN i)).of_norm

/-- **The Weingarten element as a single sum over multi-indices.** Distributing the
`n`-fold product of Neumann series (`wgElement_eq_prod_tsum`) by the Cauchy product
(`list_prod_tsum`):
`𝒲 = ∑_{κ : Fin n → ℕ} ∏ᵢ (N⁻¹ • (-N⁻¹ Kᵢ)^(κ i))`.
Each multi-index `κ` records a slot-degree; this is the linearized form on which the
coefficient-extraction step of `wg_expansion` (proved below) operates. -/
theorem wgElement_eq_tsum (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN
      = ∑' κ : Fin n → ℕ,
          ((List.finRange n).map fun i =>
            (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ (κ i)).prod := by
  set f : Fin n → ℕ → SymAlg ℝ n :=
    fun i k => (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ k with hfdef
  have hrw : wgElement n N hN
      = ((List.finRange n).map fun i => ∑' k : ℕ, f i k).prod := by
    rw [wgElement_eq_prod_tsum]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    rw [← Summable.tsum_const_smul (N⁻¹ : ℝ) (summable_geom_slot n N hN i)]
  rw [hrw, list_prod_tsum n f (fun i => summable_norm_slot n N hN i)]

/-- **Pull per-factor scalars out of an ordered list product.** In an `R`-algebra,
`∏ᵢ (cᵢ • gᵢ) = (∏ᵢ cᵢ) • ∏ᵢ gᵢ`: the per-factor scalars collect into a single scalar
acting on the product of the algebra factors, with the (possibly noncommutative) factor
order preserved. A general algebra lemma. -/
theorem list_prod_map_smul {ι R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (l : List ι) (c : ι → R) (g : ι → A) :
    (l.map fun i => c i • g i).prod = (l.map c).prod • (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, ih, smul_mul_smul_comm]

/-- **Per-slot scalar/word separation.** A single multi-index term of `wgElement_eq_tsum`
separates into a scalar (depending only on the total degree `|κ| = ∑ᵢ κ i`) times the
swap-word product `∏ᵢ Kᵢ^(κ i)`:
`∏ᵢ (N⁻¹ • (-N⁻¹ Kᵢ)^(κ i)) = (-1)^|κ| (N⁻¹)^(n+|κ|) • ∏ᵢ Kᵢ^(κ i)`.
A pure algebra identity, valid for every real `N`. -/
theorem prod_smul_pow_eq (n : ℕ) (N : ℝ) (κ : Fin n → ℕ) :
    ((List.finRange n).map fun i => (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ (κ i)).prod
      = ((-1 : ℝ) ^ (∑ i, κ i) * (N⁻¹) ^ (n + ∑ i, κ i))
          • ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod := by
  -- (a) per-factor: `N⁻¹ • (-(N⁻¹ Kᵢ))^k = ((-1)^k (N⁻¹)^(k+1)) • Kᵢ^k`
  have ha : ∀ i : Fin n,
      (N⁻¹ : ℝ) • (-((N⁻¹ : ℝ) • jm ℝ n i)) ^ (κ i)
        = ((-1 : ℝ) ^ (κ i) * (N⁻¹) ^ (κ i + 1)) • (jm ℝ n i) ^ (κ i) := by
    intro i
    rw [← neg_smul, smul_pow, smul_smul, neg_pow]
    congr 1
    rw [pow_succ']
    ring
  rw [List.map_congr_left (fun i _ => ha i)]
  -- (b) pull the scalars out of the ordered product
  rw [list_prod_map_smul]
  congr 1
  -- (c) the scalar product is `(-1)^|κ| (N⁻¹)^(n+|κ|)`
  rw [← List.ofFn_eq_map, List.prod_ofFn]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, add_comm]

/-- **Scalar/word separation.** Pulling the scalars out of each multi-index term of
`wgElement_eq_tsum` (`prod_smul_pow_eq`): writing `|κ| = ∑ᵢ κ i`,
`𝒲 = ∑_{κ : Fin n → ℕ} ((-1)^|κ| (N⁻¹)^(n+|κ|)) • ∏ᵢ Kᵢ^(κ i)`.
Each term is now a scalar `(-1)^|κ| N^{-(n+|κ|)}` times a *swap-word product* `∏ᵢ Kᵢ^(κ i)`
— a nonnegative-integer combination of permutations. The sign and the power of `N` depend
only on the total degree `|κ|`; this is the form on which the remaining `δ_σ`-coefficient
extraction of `wg_expansion` operates. -/
theorem wgElement_eq_word_tsum (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN
      = ∑' κ : Fin n → ℕ,
          ((-1 : ℝ) ^ (∑ i, κ i) * (N⁻¹) ^ (n + ∑ i, κ i))
            • ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod := by
  rw [wgElement_eq_tsum]
  exact tsum_congr fun κ => prod_smul_pow_eq n N κ

/-- **Coordinate-coefficient linearization.** Taking the `δ_σ`-coordinate of the
scalar/word-separated expansion, pushing the (continuous, since `SymAlg ℝ n` is
finite-dimensional) coordinate functional `x ↦ x σ` through the `tsum`:
`Wg(σ, N) = ∑_{κ : Fin n → ℕ} (-1)^|κ| N^{-(n+|κ|)} · (∏ᵢ Kᵢ^(κ i)) σ`.
The coefficient `(∏ᵢ Kᵢ^(κ i)) σ` is the (nonnegative-integer) `σ`-count of the swap-word
product; this real-valued series is the form on which the regrouping and parity steps of
`wg_expansion` operate. -/
theorem wg_eq_tsum_coeff (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    wg n N hN σ
      = ∑' κ : Fin n → ℕ,
          (-1 : ℝ) ^ (∑ i, κ i) * (N⁻¹) ^ (n + ∑ i, κ i)
            * (((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod σ) := by
  have hfsum := summable_word_prod n N hN
  -- the continuous coordinate functional `φ x = x σ` (continuity is free in finite dim)
  have hFin : FiniteDimensional ℝ (SymAlg ℝ n) := Module.Finite.finsupp
  let φ : SymAlg ℝ n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (Finsupp.lapply σ)
  have hφ : ∀ x : SymAlg ℝ n, φ x = x σ := fun x => Finsupp.lapply_apply σ x
  -- push the coordinate through the sum, then strip the scalar off each term
  rw [show wg n N hN σ = wgElement n N hN σ from rfl, ← hφ (wgElement n N hN),
    wgElement_eq_tsum, φ.map_tsum hfsum]
  refine tsum_congr fun κ => ?_
  rw [hφ, prod_smul_pow_eq n N κ, MonoidAlgebra.smul_apply, smul_eq_mul]

/-- The Jucys–Murphy element with `ℕ` coefficients, `K_i = ∑_{j>i} (i j)` in
`MonoidAlgebra ℕ (Perm (Fin n))`. The swap-word products built from `jmNat` have genuine
natural-number coefficients; `word_coeff_eq_natCast` identifies the real swap-word
coefficients as `Nat.cast` of these counts. (A separate `ℕ` definition is needed because
`jm` requires a `CommRing` coefficient ring, which `ℕ` is not.) -/
noncomputable def jmNat (n : ℕ) (i : Fin n) : MonoidAlgebra ℕ (Equiv.Perm (Fin n)) :=
  ∑ j ∈ Finset.Ioi i, MonoidAlgebra.of ℕ (Equiv.Perm (Fin n)) (Equiv.swap i j)

/-- **Integrality of the swap-word coefficients.** The `σ`-coefficient of the real
swap-word product `∏ᵢ Kᵢ^(κ i)` is `Nat.cast` of the same word's coefficient over `ℕ`:
`(∏ᵢ Kᵢ^(κ i)) σ = ((∏ᵢ jmNatᵢ^(κ i)) σ : ℝ)`, a nonnegative integer. Proved via the
coefficient-change ring hom `MonoidAlgebra.mapRingHom (Nat.castRingHom ℝ)`, which acts
coefficient-wise and fixes basis elements (so `jmNat i ↦ K_i` and the word maps across). -/
theorem word_coeff_eq_natCast (n : ℕ) (κ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod σ
      = (((List.finRange n).map fun i => (jmNat n i) ^ (κ i)).prod σ : ℝ) := by
  set Φ := MonoidAlgebra.mapRingHom (Equiv.Perm (Fin n)) (Nat.castRingHom ℝ) with hΦ
  have hof : ∀ τ : Equiv.Perm (Fin n),
      Φ (MonoidAlgebra.of ℕ (Equiv.Perm (Fin n)) τ)
        = MonoidAlgebra.of ℝ (Equiv.Perm (Fin n)) τ := by
    intro τ
    simp [hΦ, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single]
  have hjm : ∀ i : Fin n, Φ (jmNat n i) = jm ℝ n i := by
    intro i
    rw [jmNat, jm, map_sum]
    exact Finset.sum_congr rfl (fun j _ => hof _)
  have hword : Φ (((List.finRange n).map fun i => (jmNat n i) ^ (κ i)).prod)
      = ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod := by
    rw [map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left (fun i _ => ?_))
    rw [Function.comp_apply, map_pow, hjm]
  rw [← hword, hΦ, MonoidAlgebra.mapRingHom_apply]
  rfl

/-- **The Weingarten function as a series with explicit ℕ-valued coefficients.** Combining
`wg_eq_tsum_coeff` with `word_coeff_eq_natCast`:
`Wg(σ,N) = ∑_{κ : Fin n → ℕ} (-1)^|κ| N^{-(n+|κ|)} · (c_κ(σ) : ℝ)`, where the count
`c_κ(σ) = (∏ᵢ jmNatᵢ^(κ i)) σ : ℕ` is a nonnegative integer. This is the form the
degree-regrouping and parity steps of `wg_expansion` operate on. -/
theorem wg_eq_tsum_natCount (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    wg n N hN σ
      = ∑' κ : Fin n → ℕ,
          (-1 : ℝ) ^ (∑ i, κ i) * (N⁻¹) ^ (n + ∑ i, κ i)
            * (((List.finRange n).map fun i => (jmNat n i) ^ (κ i)).prod σ : ℝ) := by
  rw [wg_eq_tsum_coeff]
  refine tsum_congr (fun κ => ?_)
  rw [word_coeff_eq_natCast n κ σ]

/-- **Absolute summability of the coefficient series.** The real series
`κ ↦ (-1)^|κ| N^{-(n+|κ|)} · (∏ᵢ Kᵢ^(κ i)) σ` is summable: it is the image of the summable
word product (`summable_list_prod_norm`) under the continuous `δ_σ`-coordinate functional.
Needed to regroup the sum by total degree. -/
theorem summable_wg_word_coeff (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    Summable (fun κ : Fin n → ℕ =>
      (-1:ℝ)^(∑ i, κ i) * (N⁻¹)^(n + ∑ i, κ i)
        * (((List.finRange n).map fun i => (jmNat n i)^(κ i)).prod σ : ℝ)) := by
  have hfsum := summable_word_prod n N hN
  have hFin : FiniteDimensional ℝ (SymAlg ℝ n) := Module.Finite.finsupp
  let φ : SymAlg ℝ n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (Finsupp.lapply σ)
  have hφ : ∀ x : SymAlg ℝ n, φ x = x σ := fun x => Finsupp.lapply_apply σ x
  refine (φ.summable hfsum).congr (fun κ => ?_)
  rw [hφ, prod_smul_pow_eq n N κ, MonoidAlgebra.smul_apply, smul_eq_mul,
    word_coeff_eq_natCast n κ σ]

/-- The degree-`k` count `m_k(σ) = ∑_{|κ|=k} c_κ(σ)`: the total number of factorizations of
`σ` as an ordered product of transpositions distributed across the slots with total length
`k`, summed over slot-degree multi-indices `κ` of degree `k` (the finite fiber
`Finset.Nat.antidiagonalTuple n k`). This is the `m` of `wg_expansion`. -/
noncomputable def mCount (n : ℕ) (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  ∑ κ ∈ Finset.Nat.antidiagonalTuple n k,
    ((List.finRange n).map fun i => (jmNat n i)^(κ i)).prod σ

/-- **Degree-regrouped `HasSum`** — the shared fiberwise-regrouping core of
`wg_eq_tsum_degree` and `wg_expansion`: grouping the multi-index coefficient series by
total degree `k = |κ|` (the finite fibers `Finset.Nat.antidiagonalTuple n k`) sums to the
Weingarten value. -/
private lemma hasSum_wg_degree (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N)
    (σ : Equiv.Perm (Fin n)) :
    HasSum (fun k : ℕ => (-1:ℝ)^k * (N⁻¹)^(n+k) * (mCount n σ k : ℝ)) (wg n N hN σ) := by
  rw [wg_eq_tsum_natCount n N hN σ]
  set h : (Fin n → ℕ) → ℝ := fun κ =>
    (-1:ℝ)^(∑ i, κ i) * (N⁻¹)^(n + ∑ i, κ i)
      * (((List.finRange n).map fun i => (jmNat n i)^(κ i)).prod σ : ℝ) with hh
  have hsum : Summable h := summable_wg_word_coeff n N hN σ
  have hfib := hsum.hasSum.tsum_fiberwise (fun κ : Fin n → ℕ => ∑ i, κ i)
  have hterm : ∀ k : ℕ,
      (∑' κ : (fun κ : Fin n → ℕ => ∑ i, κ i) ⁻¹' {k}, h κ)
        = (-1:ℝ)^k * (N⁻¹)^(n+k) * (mCount n σ k : ℝ) := by
    intro k
    have hset : (fun κ : Fin n → ℕ => ∑ i, κ i) ⁻¹' {k}
        = (↑(Finset.Nat.antidiagonalTuple n k) : Set (Fin n → ℕ)) := by
      ext κ
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
    rw [hset, Finset.tsum_subtype' (Finset.Nat.antidiagonalTuple n k) h]
    rw [Finset.sum_congr rfl (fun κ hκ => ?_)]
    · rw [← Finset.mul_sum, mCount, Nat.cast_sum]
    · have : ∑ i, κ i = k := Finset.Nat.mem_antidiagonalTuple.mp hκ
      rw [hh]
      simp only [this]
  rw [← hfib.tsum_eq, tsum_congr hterm]
  exact (hfib.summable.congr hterm).hasSum

/-- **Degree regrouping.** Grouping the multi-index series `wg_eq_tsum_natCount` by total
degree `k = |κ|` (the finite fibers `Finset.Nat.antidiagonalTuple n k`):
`Wg(σ,N) = ∑_{k} (-1)^k N^{-(n+k)} · (m_k(σ) : ℝ)`, a single sum over `k : ℕ` with the
`ℕ`-valued counts `m_k(σ) = mCount n σ k`. The series shape is now exactly that of
`wg_expansion` (up to the `(-1)^|σ|` sign and the parity restriction). -/
theorem wg_eq_tsum_degree (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    wg n N hN σ = ∑' k : ℕ, (-1:ℝ)^k * (N⁻¹)^(n+k) * (mCount n σ k : ℝ) :=
  (hasSum_wg_degree n N hN σ).tsum_eq.symm

/-- A `SymAlg ℝ n` element is *sign-homogeneous* of sign `s` if every permutation in its
support has sign `s`. Internal to the parity argument: each `K i` is sign-homogeneous of
sign `-1` (supported on transpositions), so the swap-word product is sign-homogeneous of
sign `(-1)^|κ|`. -/
private def IsSignHom {n : ℕ} (s : ℤ) (x : SymAlg ℝ n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), x σ ≠ 0 → (Equiv.Perm.sign σ : ℤ) = s

private lemma isSignHom_zero {n : ℕ} (s : ℤ) : IsSignHom s (0 : SymAlg ℝ n) := by
  intro σ hσ
  exact absurd (Finsupp.zero_apply (a := σ)) hσ

private lemma isSignHom_one {n : ℕ} : IsSignHom 1 (1 : SymAlg ℝ n) := by
  intro σ hσ
  rw [MonoidAlgebra.one_def] at hσ
  have : σ ∈ (MonoidAlgebra.single (1 : Equiv.Perm (Fin n)) (1 : ℝ)).support :=
    Finsupp.mem_support_iff.mpr hσ
  have hsub := Finsupp.support_single_subset this
  rw [Finset.mem_singleton] at hsub
  subst hsub
  simp

private lemma isSignHom_add {n : ℕ} {s : ℤ} {x y : SymAlg ℝ n}
    (hx : IsSignHom s x) (hy : IsSignHom s y) : IsSignHom s (x + y) := by
  intro σ hσ
  have hval : (x + y) σ = x σ + y σ := Finsupp.add_apply x y σ
  rw [hval] at hσ
  by_cases h : x σ = 0
  · exact hy σ (by rw [h, zero_add] at hσ; exact hσ)
  · exact hx σ h

private lemma isSignHom_sum {n : ℕ} {ι : Type*} {s : ℤ} (S : Finset ι) (g : ι → SymAlg ℝ n)
    (hg : ∀ j ∈ S, IsSignHom s (g j)) : IsSignHom s (∑ j ∈ S, g j) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isSignHom_zero s
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact isSignHom_add (hg a (Finset.mem_insert_self a S))
      (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

private lemma isSignHom_mul {n : ℕ} {s t : ℤ} {x y : SymAlg ℝ n}
    (hx : IsSignHom s x) (hy : IsSignHom t y) : IsSignHom (s * t) (x * y) := by
  classical
  intro σ hσ
  have hmem : σ ∈ (x * y).support := Finsupp.mem_support_iff.mpr hσ
  have hsub := MonoidAlgebra.support_mul x y hmem
  rw [Finset.mem_mul] at hsub
  obtain ⟨a, ha, b, hb, hab⟩ := hsub
  have hxa : (Equiv.Perm.sign a : ℤ) = s := hx a (Finsupp.mem_support_iff.mp ha)
  have hyb : (Equiv.Perm.sign b : ℤ) = t := hy b (Finsupp.mem_support_iff.mp hb)
  rw [← hab, Equiv.Perm.sign_mul]
  push_cast
  rw [hxa, hyb]

private lemma isSignHom_pow {n : ℕ} {s : ℤ} {x : SymAlg ℝ n}
    (hx : IsSignHom s x) : ∀ m, IsSignHom (s ^ m) (x ^ m) := by
  intro m
  induction m with
  | zero => simpa using isSignHom_one
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact isSignHom_mul ih hx

private lemma isSignHom_of_swap {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    IsSignHom (-1) (MonoidAlgebra.of ℝ (Equiv.Perm (Fin n)) (Equiv.swap i j)) := by
  intro σ hσ
  rw [MonoidAlgebra.of_apply] at hσ
  have hmem : σ ∈ (MonoidAlgebra.single (Equiv.swap i j) (1 : ℝ)).support :=
    Finsupp.mem_support_iff.mpr hσ
  have hsub := Finsupp.support_single_subset hmem
  rw [Finset.mem_singleton] at hsub
  subst hsub
  rw [Equiv.Perm.sign_swap h]
  rfl

private lemma isSignHom_jm {n : ℕ} (i : Fin n) : IsSignHom (-1) (jm ℝ n i) := by
  rw [jm]
  refine isSignHom_sum _ _ (fun j hj => ?_)
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  exact isSignHom_of_swap i j hij

/-- Sign-homogeneity of an ordered list product: if every factor `f a` is sign-homogeneous
of sign `s a`, then the product is sign-homogeneous of sign `(l.map s).prod`. -/
private lemma isSignHom_list_prod {n : ℕ} {ι : Type*} (l : List ι) (s : ι → ℤ)
    (f : ι → SymAlg ℝ n) (hf : ∀ a ∈ l, IsSignHom (s a) (f a)) :
    IsSignHom (l.map s).prod ((l.map f).prod) := by
  induction l with
  | nil => simpa using isSignHom_one
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    exact isSignHom_mul (hf a (List.mem_cons_self ..))
      (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

/-- **The swap-word support has uniform sign.** If the swap-word product `∏ᵢ Kᵢ^(κ i)` has
a nonzero `σ`-coefficient, then `σ` is a product of `|κ| = ∑ᵢ κ i` transpositions, so its
sign is `(-1)^|κ|`. -/
theorem word_support_sign (n : ℕ) (κ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod σ ≠ 0
      → (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (∑ i, κ i) := by
  have hprod : IsSignHom
      (((List.finRange n).map fun i => (-1 : ℤ) ^ (κ i)).prod)
      (((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod) := by
    apply isSignHom_list_prod (List.finRange n) (fun i => (-1 : ℤ) ^ (κ i))
      (fun i => (jm ℝ n i) ^ (κ i))
    intro i _
    exact isSignHom_pow (isSignHom_jm i) (κ i)
  have hscalar : ((List.finRange n).map fun i => (-1 : ℤ) ^ (κ i)).prod
      = (-1 : ℤ) ^ (∑ i, κ i) := by
    rw [← List.ofFn_eq_map, List.prod_ofFn, Finset.prod_pow_eq_pow_sum]
  rw [hscalar] at hprod
  intro hσ
  exact hprod σ hσ

/-- **The degree-`k` count vanishes off the parity class.** A nonzero `mCount n σ k`
exhibits `σ` as a product of `k` transpositions (`word_support_sign`), so
`sign σ = (-1)^k`; against `sign σ = (-1)^(n - cycleCount σ)` (`sign_eq_neg_one_pow`) this
forces `k ≡ n - cycleCount σ (mod 2)`. -/
theorem mCount_parity (n : ℕ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    mCount n σ k ≠ 0 → k % 2 = (n - cycleCount n σ) % 2 := by
  intro h
  rw [mCount] at h
  obtain ⟨κ, hκmem, hκne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hsumκ : ∑ i, κ i = k := Finset.Nat.mem_antidiagonalTuple.mp hκmem
  have hreal : ((List.finRange n).map fun i => (jm ℝ n i) ^ (κ i)).prod σ ≠ 0 := by
    rw [word_coeff_eq_natCast n κ σ]
    exact Nat.cast_ne_zero.mpr hκne
  have hsign : (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (∑ i, κ i) :=
    word_support_sign n κ σ hreal
  rw [hsumκ] at hsign
  have hsign2 : (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (n - cycleCount n σ) :=
    sign_eq_neg_one_pow n σ
  rw [hsign2] at hsign
  rcases Nat.even_or_odd k with hk | hk <;>
    rcases Nat.even_or_odd (n - cycleCount n σ) with hm | hm
  · rw [Nat.even_iff.mp hk, Nat.even_iff.mp hm]
  · exfalso
    rw [hk.neg_one_pow, hm.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  · exfalso
    rw [hk.neg_one_pow, hm.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  · rw [Nat.odd_iff.mp hk, Nat.odd_iff.mp hm]

/-- A single factorization term lower-bounds a product coefficient in `MonoidAlgebra ℕ G`:
the `(b, c)` pair contributes exactly `P b * Q c` to the convolution sum `(P * Q) (b * c)`,
and every term of that sum is a nonnegative natural. (No order instance on `MonoidAlgebra`
fires, so this is proved directly from `MonoidAlgebra.mul_apply`.) -/
private lemma coeff_mul_ge {G : Type*} [DecidableEq G] [Monoid G]
    (P Q : MonoidAlgebra ℕ G) (b c : G) :
    P b * Q c ≤ (P * Q) (b * c) := by
  rw [MonoidAlgebra.mul_apply]
  rcases eq_or_ne (P b) 0 with hPb | hPb
  · simp [hPb]
  rcases eq_or_ne (Q c) 0 with hQc | hQc
  · simp [hQc]
  have hb : b ∈ P.support := Finsupp.mem_support_iff.mpr hPb
  have hc : c ∈ Q.support := Finsupp.mem_support_iff.mpr hQc
  have houter :
      (Q.sum fun m₂ r₂ => if b * m₂ = b * c then P b * r₂ else 0)
        ≤ P.sum (fun m₁ r₁ => Q.sum fun m₂ r₂ => if m₁ * m₂ = b * c then r₁ * r₂ else 0) := by
    rw [Finsupp.sum]
    exact Finset.single_le_sum
      (f := fun m₁ => Q.sum fun m₂ r₂ => if m₁ * m₂ = b * c then P m₁ * r₂ else 0)
      (by intro i _; exact Nat.zero_le _) hb
  refine le_trans ?_ houter
  rw [Finsupp.sum]
  have heq : P b * Q c = (fun m₂ => if b * m₂ = b * c then P b * Q m₂ else 0) c := by simp
  rw [heq]
  exact Finset.single_le_sum
    (f := fun m₂ => if b * m₂ = b * c then P b * Q m₂ else 0)
    (by intro i _; positivity) hc

/-- List version of `coeff_mul_ge`: the product of the factor-coefficients lower-bounds the
coefficient of the product at the product of the points. -/
private lemma coeff_list_prod_ge {G : Type*} [DecidableEq G] [Monoid G] {ι : Type*}
    (l : List ι) (V : ι → MonoidAlgebra ℕ G) (a : ι → G) :
    (l.map fun i => V i (a i)).prod ≤ ((l.map V).prod) ((l.map a).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [MonoidAlgebra.one_def, Finsupp.single_apply]
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    calc V x (a x) * (xs.map fun i => V i (a i)).prod
        ≤ V x (a x) * ((xs.map V).prod) ((xs.map a).prod) := Nat.mul_le_mul le_rfl ih
      _ ≤ (V x * (xs.map V).prod) (a x * (xs.map a).prod) := coeff_mul_ge _ _ _ _

/-- The coefficient of `jmNat n i` at the transposition `swap i v` is `1` whenever `i < v`
(`swap i v` appears once, with coefficient one, in `∑_{j > i} of (swap i j)`). -/
private lemma jmNat_coeff_swap (n : ℕ) (i v : Fin n) (hiv : i < v) :
    (jmNat n i) (Equiv.swap i v) = 1 := by
  rw [jmNat]
  rw [show (∑ j ∈ Finset.Ioi i, (MonoidAlgebra.of ℕ (Perm (Fin n))) (swap i j)) (swap i v)
        = ∑ j ∈ Finset.Ioi i, ((MonoidAlgebra.of ℕ (Perm (Fin n))) (swap i j)) (swap i v) from
      Finset.sum_apply' _]
  rw [Finset.sum_eq_single v]
  · rw [MonoidAlgebra.of_apply, Finsupp.single_apply]; simp
  · intro j hj hjv
    rw [MonoidAlgebra.of_apply, Finsupp.single_apply, if_neg]
    intro heq
    apply hjv
    have := congrArg (fun e => e i) heq
    simpa [Equiv.swap_apply_left] using this
  · intro hcon
    exact absurd (Finset.mem_Ioi.mpr hiv) hcon

/-- **The minimal-term lemma.** The count at the minimal degree `n - cycleCount σ` is
nonzero: the monotone word from `exists_min_word` is one length-`(n - cycleCount σ)`
factorization of `σ`, contributing `≥ 1` to the count, which is a sum of naturals. This is
the nonvanishing minimal term `m_{|σ|} ≥ 1` of `wg_expansion`. -/
theorem mCount_min_ne_zero (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    mCount n σ (n - cycleCount n σ) ≠ 0 := by
  obtain ⟨f, hmono, hprod, hcard⟩ := exists_min_word n σ
  set a : Fin n → Equiv.Perm (Fin n) :=
    fun i => ((f i).map fun j => Equiv.swap i j).getD 1 with ha
  set κ : Fin n → ℕ := fun i => if (f i).isSome then 1 else 0 with hκ
  have hmem : κ ∈ Finset.Nat.antidiagonalTuple n (n - cycleCount n σ) := by
    rw [Finset.Nat.mem_antidiagonalTuple, ← hcard, Finset.card_filter]
  have hfactor : ∀ i : Fin n, ((jmNat n i) ^ (κ i)) (a i) = 1 := by
    intro i
    rcases hfi : f i with _ | v
    · have hκi : κ i = 0 := by simp [hκ, hfi]
      have hai : a i = 1 := by simp [ha, hfi]
      rw [hκi, pow_zero, hai, MonoidAlgebra.one_def, Finsupp.single_apply]; simp
    · have hiv : i < v := hmono i v hfi
      have hκi : κ i = 1 := by simp [hκ, hfi]
      have hai : a i = Equiv.swap i v := by simp [ha, hfi]
      rw [hκi, pow_one, hai]
      exact jmNat_coeff_swap n i v hiv
  have hterm : 1 ≤ ((List.finRange n).map fun i => (jmNat n i) ^ (κ i)).prod σ := by
    have key := coeff_list_prod_ge (List.finRange n)
      (fun i => (jmNat n i) ^ (κ i)) a
    rw [show ((List.finRange n).map a).prod = σ from hprod] at key
    rw [show ((List.finRange n).map fun i => ((jmNat n i) ^ (κ i)) (a i)).prod = 1 from by
      apply List.prod_eq_one
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hfactor i] at key
    exact key
  rw [mCount]
  intro hzero
  have hle : ((List.finRange n).map fun i => (jmNat n i) ^ (κ i)).prod σ
      ≤ ∑ κ' ∈ Finset.Nat.antidiagonalTuple n (n - cycleCount n σ),
          ((List.finRange n).map fun i => (jmNat n i) ^ (κ' i)).prod σ :=
    Finset.single_le_sum
      (f := fun κ' => ((List.finRange n).map fun i => (jmNat n i) ^ (κ' i)).prod σ)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hzero] at hle
  omega

/-- Per-`k` identity: the signed degree-term times the uniform sign `(-1)^(n-cycleCount σ)`
equals the nonnegative term `(mCount n σ k)/N^(n+k)`. On the off-parity class both sides are
`0`; on the parity class `(-1)^(n-cycleCount σ) (-1)^k = 1` (`mCount_parity`). -/
private lemma term_eq (n : ℕ) (N : ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    (-1 : ℝ) ^ (n - cycleCount n σ)
        * ((-1) ^ k * (N⁻¹) ^ (n + k) * (mCount n σ k : ℝ))
      = (mCount n σ k : ℝ) / N ^ (n + k) := by
  by_cases hk : mCount n σ k = 0
  · simp [hk]
  · have hpar : k % 2 = (n - cycleCount n σ) % 2 := mCount_parity n σ k hk
    have heven : Even ((n - cycleCount n σ) + k) := by
      rw [Nat.even_add, Nat.even_iff, Nat.even_iff, hpar]
    have hsign : (-1 : ℝ) ^ (n - cycleCount n σ) * (-1) ^ k = 1 := by
      rw [← pow_add]
      exact heven.neg_one_pow
    rw [div_eq_mul_inv, ← inv_pow]
    calc (-1 : ℝ) ^ (n - cycleCount n σ) * ((-1) ^ k * (N⁻¹) ^ (n + k) * (mCount n σ k : ℝ))
        = ((-1 : ℝ) ^ (n - cycleCount n σ) * (-1) ^ k)
            * ((N⁻¹) ^ (n + k) * (mCount n σ k : ℝ)) := by ring
      _ = (mCount n σ k : ℝ) * (N⁻¹) ^ (n + k) := by rw [hsign, one_mul, mul_comm]

/-- **Nonnegative expansion / Neumann expansion with uniform sign.** Blueprint:
`lem:expansion`. For `n - 1 < N`, with `m k = mCount n σ k ∈ ℕ`,
`(-1)^|σ| Wg(σ,N) = ∑_k m_k / N^(n+k)`, where `m_k = 0` unless `k ≡ |σ| (mod 2)` and the
minimal term `m_{|σ|} ≠ 0`. Assembled from `wg_eq_tsum_degree` (the series), `mCount_parity`
(the parity restriction, used via `term_eq` to fix the uniform sign), and `mCount_min_ne_zero`
(the nonvanishing minimal term, from `exists_min_word`). -/
theorem wg_expansion (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    ∃ m : ℕ → ℕ,
      (∀ k, m k ≠ 0 → k % 2 = (n - cycleCount n σ) % 2) ∧
      m (n - cycleCount n σ) ≠ 0 ∧
      Summable (fun k : ℕ => (m k : ℝ) / N ^ (n + k)) ∧
      (-1 : ℝ) ^ (n - cycleCount n σ) * wg n N hN σ
        = ∑' k : ℕ, (m k : ℝ) / N ^ (n + k) := by
  -- the degree-regrouped series (shared with `wg_eq_tsum_degree`), then multiply by
  -- `(-1)^|σ|` and rewrite each term via `term_eq`
  have hHS0 : HasSum (fun k : ℕ => (-1)^k * (N⁻¹)^(n+k) * (mCount n σ k : ℝ))
      (wg n N hN σ) := hasSum_wg_degree n N hN σ
  have hHS : HasSum (fun k : ℕ => (mCount n σ k : ℝ) / N ^ (n + k))
      ((-1:ℝ) ^ (n - cycleCount n σ) * wg n N hN σ) :=
    (hHS0.mul_left ((-1:ℝ) ^ (n - cycleCount n σ))).congr_fun (fun k => (term_eq n N σ k).symm)
  exact ⟨mCount n σ, fun k => mCount_parity n σ k, mCount_min_ne_zero n σ,
    hHS.summable, hHS.tsum_eq.symm⟩

/-- **Parity sign theorem**: throughout the stable range, `Wg (σ, N) ≠ 0` and its sign
is `sgn σ`, strictly. Blueprint: `thm:parity`. Follows from `wg_expansion` by
positivity of a convergent nonnegative series with a strictly positive term. -/
theorem wg_sign (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) (σ : Equiv.Perm (Fin n)) :
    0 < (-1 : ℝ) ^ (n - cycleCount n σ) * wg n N hN σ := by
  obtain ⟨m, hpar, hmin, hsum, heq⟩ := wg_expansion n N hN σ
  rw [heq]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: `N` may be ≤ 0, but every surviving term has even exponent.
    subst hn0
    refine hsum.tsum_pos ?_ (0 - cycleCount 0 σ) ?_
    · intro k
      by_cases hk : m k = 0
      · simp [hk]
      · have hpar : k % 2 = (0 - cycleCount 0 σ) % 2 := hpar k hk
        rw [Nat.zero_sub, Nat.zero_mod] at hpar
        have hke : Even (0 + k) := by rw [Nat.even_iff]; simpa using hpar
        exact div_nonneg (Nat.cast_nonneg _) (hke.pow_nonneg _)
    · have hd0 : (0 : ℕ) - cycleCount 0 σ = 0 := Nat.zero_sub _
      have hm0 : m (0 - cycleCount 0 σ) ≠ 0 := hmin
      rw [hd0] at hm0 ⊢
      have : (m 0 : ℝ) / N ^ (0 + 0) = (m 0 : ℝ) := by simp
      rw [this]
      exact_mod_cast Nat.pos_of_ne_zero hm0
  · have hNpos : 0 < N := by
      have : (0 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        linarith
      linarith
    refine hsum.tsum_pos ?_ (n - cycleCount n σ) ?_
    · intro k
      exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg hNpos.le _)
    · apply div_pos
      · exact_mod_cast Nat.pos_of_ne_zero hmin
      · exact pow_pos hNpos _

end Weingarten
