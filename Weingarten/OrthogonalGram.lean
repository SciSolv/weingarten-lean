/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Pairings
import Weingarten.Homs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The orthogonal Gram: absorption and the below-threshold package

Fully elaborated and `sorry`-free (`lake env lean` on this file is EXIT 0 with no
`sorry` warnings; `#print axioms` of every declaration gives only `propext`,
`Classical.choice`, `Quot.sound` — no `native_decide`). Blueprint: `def:orth_gram`,
`def:even_rising`, `def:falling_fact`, `thm:orth_ones_absorb`,
`thm:orth_det_absorb`, `def:comm_penrose`, `lem:penrose_eigen`,
`lem:orth_two_line`, `thm:orth_det_vanish`, `thm:orth_ker_witness`,
`thm:orth_not_unit`, `thm:orth_rising_rule`, `thm:orth_falling_rule`,
`thm:orth_rising_rule_eigen`, `thm:orth_falling_rule_eigen`.

The orthogonal Gram matrix `N ^ loops` on pair partitions; the all-ones and
determinant-vector absorption identities (even-rising and plain falling
eigenvalues — polynomial identities in the parameter, hence valid over any
commutative ring); the matrix-level commuting Penrose partner; and the
two-line conditional sum rules mirroring `Weingarten.BelowThreshold`,
including the exact vanishing of the signed determinant sums when the falling
factorial vanishes, the kernel witness, and Gram singularity below threshold.

Provenance: the orthogonal Weingarten calculus follows the Collins–Śniady
convention (arXiv:math-ph/0402073); the odd-Jucys–Murphy route is Zinn-Justin
arXiv:0907.2719 with Matsumoto arXiv:1001.2345. The blueprint carries the full
citation record.
-/

namespace Weingarten

open Pairing

variable {k : Type*} [CommRing k] {n : ℕ}

/-- The orthogonal Gram matrix at parameter `N`: entries `N ^ loops`.
Blueprint: `def:orth_gram`. -/
def orthGram (k : Type*) [CommRing k] (n : ℕ) (N : k) :
    Matrix (Pairing n) (Pairing n) k :=
  fun p q => N ^ p.loops q

/-- Even-rising factorial `N (N+2) ⋯ (N+2n-2)`. Blueprint: `def:even_rising`. -/
def evenRising (k : Type*) [CommRing k] (n : ℕ) (N : k) : k :=
  ∏ j ∈ Finset.range n, (N + 2 * (j : k))

/-- Falling factorial `N (N-1) ⋯ (N-n+1)`. Blueprint: `def:falling_fact`. -/
def fallingFact (k : Type*) [CommRing k] (n : ℕ) (N : k) : k :=
  ∏ j ∈ Finset.range n, (N - (j : k))

/-- The orthogonal Gram is symmetric: `loops` is symmetric since `q*p` is a conjugate of
`p*q` by the involution `p` (`cycleCount_conj`). -/
theorem orthGram_symm (N : k) (p q : Pairing n) :
    orthGram k n N p q = orthGram k n N q p := by
  show N ^ (p.loops q) = N ^ (q.loops p)
  have hcc : cycleCount (2 * n) (p.1 * q.1) = cycleCount (2 * n) (q.1 * p.1) := by
    have hp : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_right p.2.1
    have key : q.1 * p.1 = p.1 * (p.1 * q.1) * p.1⁻¹ := by
      rw [hp, ← mul_assoc, p.2.1, one_mul]
    rw [key, cycleCount_conj]
  show N ^ (cycleCount (2 * n) (p.1 * q.1) / 2) = N ^ (cycleCount (2 * n) (q.1 * p.1) / 2)
  rw [hcc]

/-- Symmetry as a `vecMul`/`mulVec` identity. -/
theorem orthGram_vecMul_eq (N : k) (v : Pairing n → k) :
    Matrix.vecMul v (orthGram k n N) = (orthGram k n N).mulVec v := by
  funext p
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun q _ => by rw [orthGram_symm N q p]; ring)

section OnesAbsorption

open Equiv Equiv.Perm

/-- The cycle type of a pairing is `n` copies of `2`: a fixed-point-free involution has
all cycles of length `2`, the support is everything, so there are exactly `n` cycles. -/
theorem pairing_cycleType (p : Pairing n) : p.1.cycleType = Multiset.replicate n 2 := by
  have hall : ∀ x ∈ p.1.cycleType, x = 2 := by
    intro x hx
    have hd : x ∣ orderOf p.1 := dvd_of_mem_cycleType hx
    have ho : orderOf p.1 ∣ 2 := by apply orderOf_dvd_of_pow_eq_one; rw [pow_two]; exact p.2.1
    have hx2 : 2 ≤ x := two_le_of_mem_cycleType hx
    have := Nat.le_of_dvd (by norm_num) (hd.trans ho)
    omega
  have hsupp : p.1.support = Finset.univ := by ext x; simp [Equiv.Perm.mem_support, p.2.2 x]
  have hsum : p.1.cycleType.sum = 2 * n := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, Fintype.card_fin]
  have hrep := Multiset.eq_replicate_card.mpr hall
  have hcard : Multiset.card p.1.cycleType = n := by
    have hh : p.1.cycleType.sum = 2 * Multiset.card p.1.cycleType := by
      conv_lhs => rw [hrep]
      rw [Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
    omega
  rw [hrep, hcard]

/-- Any two pairings are conjugate (they share the cycle type `n × 2`). -/
theorem pairing_isConj (p q : Pairing n) : IsConj p.1 q.1 :=
  (Equiv.Perm.isConj_iff_cycleType_eq).mpr (by rw [pairing_cycleType, pairing_cycleType])

/-- Conjugating a pairing by a permutation of `Fin (2n)` is again a pairing. -/
def conjP (g : Perm (Fin (2 * n))) (q : Pairing n) : Pairing n :=
  ⟨g * q.1 * g⁻¹, by
    refine ⟨?_, ?_⟩
    · have h : (g * q.1 * g⁻¹) * (g * q.1 * g⁻¹) = g * (q.1 * q.1) * g⁻¹ := by group
      rw [h, q.2.1]; group
    · intro x
      simp only [Perm.mul_apply, ne_eq]; intro h
      apply q.2.2 (g⁻¹ x)
      calc q.1 (g⁻¹ x) = g⁻¹ (g (q.1 (g⁻¹ x))) := (Equiv.symm_apply_apply g _).symm
        _ = g⁻¹ x := by rw [show g (q.1 (g⁻¹ x)) = x from h]⟩

@[simp] theorem conjP_val (g : Perm (Fin (2 * n))) (q : Pairing n) :
    (conjP g q).1 = g * q.1 * g⁻¹ := rfl

theorem conjP_conjP (g h : Perm (Fin (2 * n))) (q : Pairing n) :
    conjP g (conjP h q) = conjP (g * h) q := by
  apply Subtype.ext; simp only [conjP_val, mul_inv_rev]; group

theorem conjP_one (q : Pairing n) : conjP 1 q = q := by
  apply Subtype.ext; simp [conjP_val]

/-- Conjugation by `g` as a self-equivalence of the pairing set. -/
def conjPEquiv (g : Perm (Fin (2 * n))) : Pairing n ≃ Pairing n where
  toFun := conjP g
  invFun := conjP g⁻¹
  left_inv q := by rw [conjP_conjP, inv_mul_cancel, conjP_one]
  right_inv q := by rw [conjP_conjP, mul_inv_cancel, conjP_one]

/-- Loop counts are invariant under simultaneous conjugation of both pairings: the product
`(gpg⁻¹)(gqg⁻¹) = g(pq)g⁻¹` is a conjugate of `pq`, and `cycleCount` is a class function. -/
theorem loops_conjP (g : Perm (Fin (2 * n))) (p q : Pairing n) :
    (conjP g p).loops (conjP g q) = p.loops q := by
  show cycleCount (2 * n) ((conjP g p).1 * (conjP g q).1) / 2
    = cycleCount (2 * n) (p.1 * q.1) / 2
  congr 1
  have hprod : (conjP g p).1 * (conjP g q).1 = g * (p.1 * q.1) * g⁻¹ := by
    simp only [conjP_val]; group
  rw [hprod, cycleCount_conj]

/-- The orthogonal-Gram row sum is the same for every row: relabelling by a conjugating
permutation `c` with `c p c⁻¹ = p'` (which exists since all pairings are conjugate)
reindexes the sum over `q` and preserves every `loops` value. -/
theorem rowSum_const (N : k) (p p' : Pairing n) :
    ∑ q : Pairing n, N ^ (p.loops q) = ∑ q : Pairing n, N ^ (p'.loops q) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (pairing_isConj p p')
  have hpp' : conjP c p = p' := Subtype.ext (by simpa using hc)
  rw [← Equiv.sum_comp (conjPEquiv c) (fun q => N ^ (p'.loops q))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  show N ^ (p.loops q) = N ^ (p'.loops (conjP c q))
  rw [← hpp', loops_conjP]

/-- The canonical reference pairing in dimension `n`: `qPair 1`, which pairs `a ↔ n + a`. -/
def refPairing (n : ℕ) : Pairing n := qPair 1

/-- The common row sum `∑_q N ^ loops(p, q)`, evaluated at the reference pairing. By
`rowSum_const` this is the row sum for *every* `p`. -/
def rowSum (k : Type*) [CommRing k] (n : ℕ) (N : k) : k :=
  ∑ q : Pairing n, N ^ ((refPairing n).loops q)

/-- The row sum equals `rowSum` for every row. -/
theorem rowSum_eq (N : k) (p : Pairing n) :
    ∑ q : Pairing n, N ^ (p.loops q) = rowSum k n N :=
  rowSum_const N p (refPairing n)

instance : Subsingleton (Pairing 0) := by
  constructor; intro a b; apply Subtype.ext; ext x; exact absurd x.isLt (by omega)

/-- Base case of the recursion: there is a unique pairing of `0` points, with `0` loops. -/
theorem rowSum_zero (N : k) : rowSum k 0 N = 1 := by
  rw [rowSum]
  rw [Finset.sum_eq_single (refPairing 0)]
  · have hcc : cycleCount (2 * 0) ((refPairing 0).1 * (refPairing 0).1) = 0 :=
      Nat.le_zero.mp (by simpa using cycleCount_le 0 ((refPairing 0).1 * (refPairing 0).1))
    have hl : (refPairing 0).loops (refPairing 0) = 0 := by rw [Pairing.loops, hcc]
    rw [hl, pow_zero]
  · intro b _ hb; exact absurd (Subsingleton.elim b (refPairing 0)) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/- **The recursion step** (`thm:orth_ones_absorb`): conditioning on the partner in `q` of the
distinguished chord of the reference pairing — exactly one choice closes a loop (factor `N`),
the other `2n` choices splice two chords (loop count unchanged) — gives
`rowSum (n+1) = (N + 2n) · rowSum n`. Proved below in sub-namespace `RSS` via the partner-fiber
bijection `Pairing (m+1) ≃ Pairing m ⊕ (Fin (2m) × Pairing m)` (`biEquiv`), with the orbit-count
merge lemma `gcount_swap_mul`, the close/splice extensions `closeP`/`spliceP`, and their loop
laws `loops_closeP` (+1 loop) / `loops_spliceP` (loop-preserving). -/
open Pairing Equiv Equiv.Perm

namespace RSS

variable {m : ℕ}

/-! ### Generic orbit count `gcount` and the merge lemma

The generic orbit count and the ~85-line merge argument live upstream in
`Weingarten.CycleCount` (`Weingarten.gcount`, `Weingarten.gcount_swap_mul`), proved
exactly once. The declarations below re-export them under their original `RSS` names
(statements unchanged) for the partner-fiber recursion here and for the symplectic
consumers in `Weingarten.SymplecticGram`. -/

/-- Orbit count of a permutation of any fintype (fixed points + cycles).
Re-export of the upstream `Weingarten.gcount`. -/
def gcount {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℕ :=
  Weingarten.gcount σ

theorem gcount_eq {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    gcount σ = (Fintype.card α - σ.cycleType.sum) + σ.cycleType.card :=
  Weingarten.gcount_eq σ

theorem cycleCount_eq_gcount (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    cycleCount N σ = gcount σ :=
  Weingarten.cycleCount_eq_gcount N σ

theorem gcount_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : α ≃ β) (σ : Equiv.Perm α) : gcount (E.permCongr σ) = gcount σ := by
  rw [gcount_eq, gcount_eq, cycleType_permCongr, Fintype.card_congr E]

/-- Merge lemma: left-multiplying by a transposition through a fixed point lowers the
orbit count by exactly one. Re-export of the upstream `Weingarten.gcount_swap_mul`. -/
theorem gcount_swap_mul {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (a b : α) (ha : σ a = a) (hab : a ≠ b) :
    gcount (Equiv.swap a b * σ) + 1 = gcount σ :=
  Weingarten.gcount_swap_mul σ a b ha hab

/-! ### The sum model `Fin 2 ⊕ Fin (2m)` and the close / splice involutions -/

private def Em (m : ℕ) : Fin (2*(m+1)) ≃ Fin 2 ⊕ Fin (2*m) :=
  (finCongr (by ring)).trans finSumFinEquiv.symm

private def closeFun (m : ℕ) (r : Equiv.Perm (Fin (2*m))) : Equiv.Perm (Fin 2 ⊕ Fin (2*m)) :=
  Equiv.Perm.sumCongr (Equiv.swap 0 1) r
@[simp] private theorem closeFun_inl (m : ℕ) (r : Equiv.Perm (Fin (2*m))) (y : Fin 2) :
    closeFun m r (Sum.inl y) = Sum.inl (Equiv.swap 0 1 y) := rfl
@[simp] private theorem closeFun_inr (m : ℕ) (r : Equiv.Perm (Fin (2*m))) (c : Fin (2*m)) :
    closeFun m r (Sum.inr c) = Sum.inr (r c) := rfl
private theorem closeFun_invol (m : ℕ) (r : Equiv.Perm (Fin (2*m))) (hr : r*r=1) :
    closeFun m r * closeFun m r = 1 := by
  unfold closeFun; rw [Equiv.Perm.sumCongr_mul, Equiv.swap_mul_self, hr, Equiv.Perm.sumCongr_one]
private theorem closeFun_fpf (m : ℕ) (r : Equiv.Perm (Fin (2*m))) (hfpf : ∀ x, r x ≠ x)
    (x : Fin 2 ⊕ Fin (2*m)) : closeFun m r x ≠ x := by
  cases x with
  | inl y => rw [closeFun_inl]; intro h
             have : Equiv.swap (0:Fin 2) 1 y = y := Sum.inl_injective h
             revert this; fin_cases y <;> decide
  | inr c => rw [closeFun_inr]; intro h; exact hfpf c (Sum.inr_injective h)

private def spliceFun (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m))) :
    Fin 2 ⊕ Fin (2*m) → Fin 2 ⊕ Fin (2*m)
  | Sum.inl x => if x = 0 then Sum.inr a else Sum.inr (r a)
  | Sum.inr c => if c = a then Sum.inl 0 else if c = r a then Sum.inl 1 else Sum.inr (r c)
@[simp] private theorem spliceFun_inl0 (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m))) :
    spliceFun m a r (Sum.inl 0) = Sum.inr a := by
  show (if (0:Fin 2) = 0 then Sum.inr a else Sum.inr (r a)) = Sum.inr a
  rw [if_pos rfl]
@[simp] private theorem spliceFun_inl1 (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m))) :
    spliceFun m a r (Sum.inl 1) = Sum.inr (r a) := by
  show (if (1:Fin 2) = 0 then Sum.inr a else Sum.inr (r a)) = Sum.inr (r a)
  rw [if_neg (by decide)]
private theorem spliceFun_inr (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m))) (c : Fin (2*m)) :
    spliceFun m a r (Sum.inr c) =
      if c = a then Sum.inl 0 else if c = r a then Sum.inl 1 else Sum.inr (r c) := rfl
private theorem spliceFun_invol (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r * r = 1) (hfpf : ∀ x, r x ≠ x) : Function.Involutive (spliceFun m a r) := by
  have hra : ∀ x, r (r x) = x := by
    intro x; have : (r*r) x = x := by rw [hr]; rfl
    rwa [Equiv.Perm.mul_apply] at this
  have hane : a ≠ r a := fun h => hfpf a h.symm
  have hrane : r a ≠ a := hfpf a
  intro x
  cases x with
  | inl y =>
    by_cases hy : y = 0
    · subst hy; rw [spliceFun_inl0, spliceFun_inr, if_pos rfl]
    · have hy1 : y = 1 := by omega
      subst hy1; rw [spliceFun_inl1, spliceFun_inr, if_neg hrane, if_pos rfl]
  | inr c =>
    rw [spliceFun_inr]
    by_cases h1 : c = a
    · rw [if_pos h1, spliceFun_inl0, h1]
    · by_cases h2 : c = r a
      · rw [if_neg h1, if_pos h2, spliceFun_inl1, h2]
      · rw [if_neg h1, if_neg h2, spliceFun_inr]
        have hrc_ne_a : r c ≠ a := by intro h; apply h2; rw [← hra c, h]
        have hrc_ne_ra : r c ≠ r a := by intro h; exact h1 (r.injective h)
        rw [if_neg hrc_ne_a, if_neg hrc_ne_ra, hra]
private noncomputable def spliceP' (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) : Equiv.Perm (Fin 2 ⊕ Fin (2*m)) :=
  (spliceFun_invol m a r hr hfpf).toPerm
private theorem spliceP'_apply (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) (x) :
    spliceP' m a r hr hfpf x = spliceFun m a r x := rfl
private theorem spliceP'_invol (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) : spliceP' m a r hr hfpf * spliceP' m a r hr hfpf = 1 := by
  ext x; show spliceFun m a r (spliceFun m a r x) = x; exact spliceFun_invol m a r hr hfpf x
private theorem spliceP'_fpf (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) (x) : spliceP' m a r hr hfpf x ≠ x := by
  rw [spliceP'_apply]
  have hane : a ≠ r a := fun h => hfpf a h.symm
  cases x with
  | inl y =>
    by_cases hy : y = 0
    · subst hy; rw [spliceFun_inl0]; exact fun h => Sum.inl_ne_inr h.symm
    · have hy1 : y = 1 := by omega
      subst hy1; rw [spliceFun_inl1]; exact fun h => Sum.inl_ne_inr h.symm
  | inr c =>
    rw [spliceFun_inr]
    by_cases h1 : c = a
    · rw [if_pos h1]; exact fun h => Sum.inl_ne_inr h
    · by_cases h2 : c = r a
      · rw [if_neg h1, if_pos h2]; exact fun h => Sum.inl_ne_inr h
      · rw [if_neg h1, if_neg h2]; intro h; exact hfpf c (Sum.inr_injective h)

/-! ### Swap evaluators and the splice decomposition -/

private theorem swap_il_ir_il (i j : Fin 2) (w : Fin (2*m)) :
    Equiv.swap (Sum.inl i) (Sum.inr w) (Sum.inl j : Fin 2 ⊕ Fin (2*m)) =
      if j = i then Sum.inr w else Sum.inl j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl, Equiv.swap_apply_left]
  · rw [if_neg h, Equiv.swap_apply_of_ne_of_ne (fun hh => h (Sum.inl_injective hh)) Sum.inl_ne_inr]
private theorem swap_il_ir_ir (i : Fin 2) (w c : Fin (2*m)) :
    Equiv.swap (Sum.inl i) (Sum.inr w) (Sum.inr c : Fin 2 ⊕ Fin (2*m)) =
      if c = w then Sum.inl i else Sum.inr c := by
  by_cases h : c = w
  · subst h; rw [if_pos rfl, Equiv.swap_apply_right]
  · rw [if_neg h, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun hh => h (Sum.inr_injective hh))]

private theorem splice_decomp (m : ℕ) (a : Fin (2*m)) (s r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) :
    closeFun m s * spliceP' m a r hr hfpf
      = Equiv.swap (Sum.inl 0) (Sum.inr (s a)) *
        (Equiv.swap (Sum.inl 1) (Sum.inr (s (r a))) * (closeFun m s * closeFun m r)) := by
  have hra : ∀ x, r (r x) = x := by
    intro x; have : (r*r) x = x := by rw [hr]; rfl
    rwa [Equiv.Perm.mul_apply] at this
  have hane : a ≠ r a := fun h => hfpf a h.symm
  have hsane : s a ≠ s (r a) := fun h => hane (s.injective h)
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    spliceP'_apply]
  cases x with
  | inl y =>
    by_cases hy : y = 0
    · subst hy
      rw [spliceFun_inl0, closeFun_inr, closeFun_inl, Equiv.swap_apply_left, closeFun_inl,
        Equiv.swap_apply_right, swap_il_ir_il, if_neg (by decide), swap_il_ir_il, if_pos rfl]
    · have hy1 : y = 1 := by omega
      subst hy1
      rw [spliceFun_inl1, closeFun_inr, closeFun_inl, Equiv.swap_apply_right, closeFun_inl,
        Equiv.swap_apply_left, swap_il_ir_il, if_pos rfl, swap_il_ir_ir,
        if_neg (fun h => hsane h.symm)]
  | inr c =>
    rw [spliceFun_inr]
    by_cases h1 : c = a
    · subst h1
      rw [if_pos rfl, closeFun_inl, Equiv.swap_apply_left, closeFun_inr, closeFun_inr,
        swap_il_ir_ir, if_pos rfl, swap_il_ir_il, if_neg (by decide)]
    · by_cases h2 : c = r a
      · subst h2
        rw [if_neg (fun h => hane h.symm), if_pos rfl, closeFun_inl, Equiv.swap_apply_right,
          closeFun_inr, closeFun_inr, hra, swap_il_ir_ir, if_neg hsane, swap_il_ir_ir, if_pos rfl]
      · rw [if_neg h1, if_neg h2, closeFun_inr, closeFun_inr, closeFun_inr]
        have hsrc_ne_v : s (r c) ≠ s (r a) := by
          intro h; exact h1 (r.injective (s.injective h))
        have hsrc_ne_u : s (r c) ≠ s a := by
          intro h; apply h2; rw [← hra c, s.injective h]
        rw [swap_il_ir_ir, if_neg hsrc_ne_v, swap_il_ir_ir, if_neg hsrc_ne_u]

/-! ### gcount of the products -/

private theorem closeFun_mul (m : ℕ) (s r : Equiv.Perm (Fin (2*m))) :
    closeFun m s * closeFun m r = Equiv.Perm.sumCongr 1 (s * r) := by
  unfold closeFun; rw [Equiv.Perm.sumCongr_mul, Equiv.swap_mul_self]
private theorem closeMul_fix0 (m : ℕ) (s r : Equiv.Perm (Fin (2*m))) :
    (closeFun m s * closeFun m r) (Sum.inl 0) = Sum.inl 0 := by rw [closeFun_mul]; rfl
private theorem closeMul_fix1 (m : ℕ) (s r : Equiv.Perm (Fin (2*m))) :
    (closeFun m s * closeFun m r) (Sum.inl 1) = Sum.inl 1 := by rw [closeFun_mul]; rfl
private theorem gcount_closeMul (m : ℕ) (s r : Equiv.Perm (Fin (2*m))) :
    gcount (closeFun m s * closeFun m r) = gcount (s * r) + 2 := by
  rw [closeFun_mul, gcount_eq, gcount_eq]
  rw [show Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 2)) (s*r)
        = Equiv.sumCongr (1:Equiv.Perm (Fin 2)) (s*r) from rfl, cycleType_sumCongr,
    Equiv.Perm.cycleType_one]
  have hsum : (s*r).cycleType.sum ≤ Fintype.card (Fin (2*m)) := Equiv.Perm.sum_cycleType_le _
  rw [Fintype.card_fin] at hsum
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  simp only [zero_add]
  omega
private theorem gcount_spliceMul (m : ℕ) (a : Fin (2*m)) (s r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) :
    gcount (closeFun m s * spliceP' m a r hr hfpf) = gcount (s * r) := by
  rw [splice_decomp]
  have hl01 : (Sum.inl 0 : Fin 2 ⊕ Fin (2*m)) ≠ Sum.inl 1 := fun h =>
    absurd (Sum.inl_injective h) (by decide)
  set Mc : Equiv.Perm (Fin 2 ⊕ Fin (2*m)) := closeFun m s * closeFun m r with hMc
  set N : Equiv.Perm (Fin 2 ⊕ Fin (2*m)) := Equiv.swap (Sum.inl 1) (Sum.inr (s (r a))) * Mc with hN
  have hfix1 : Mc (Sum.inl 1) = Sum.inl 1 := closeMul_fix1 m s r
  have hstep1 := gcount_swap_mul Mc (Sum.inl 1) (Sum.inr (s (r a))) hfix1 Sum.inl_ne_inr
  rw [← hN] at hstep1
  have hfix0 : N (Sum.inl 0) = Sum.inl 0 := by
    rw [hN, Equiv.Perm.mul_apply, hMc, closeMul_fix0 m s r,
      Equiv.swap_apply_of_ne_of_ne hl01 Sum.inl_ne_inr]
  have hstep0 := gcount_swap_mul N (Sum.inl 0) (Sum.inr (s a)) hfix0 Sum.inl_ne_inr
  have hMcval : gcount Mc = gcount (s*r) + 2 := gcount_closeMul m s r
  have hgoal : Equiv.swap (Sum.inl 0) (Sum.inr (s a)) *
      (Equiv.swap (Sum.inl 1) (Sum.inr (s (r a))) * (closeFun m s * closeFun m r))
      = Equiv.swap (Sum.inl 0) (Sum.inr (s a)) * N := by rw [hN, hMc]
  rw [hgoal]
  omega

/-! ### Transport to `Pairing (m+1)` and the loop laws -/

private def mkP (m : ℕ) (s : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : s * s = 1) (hfpf : ∀ x, s x ≠ x) : Pairing (m+1) :=
  ⟨(Em m).symm.permCongr s, by
    rw [← Equiv.permCongr_mul, hinv]; ext x; simp [Equiv.permCongr_apply], by
    intro x
    rw [Equiv.permCongr_apply]
    intro h
    apply hfpf ((Em m).symm.symm x)
    apply (Em m).symm.injective
    rw [Equiv.apply_symm_apply]; exact h⟩
@[simp] private theorem mkP_val (m : ℕ) (s : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : s * s = 1) (hfpf : ∀ x, s x ≠ x) :
    (mkP m s hinv hfpf).1 = (Em m).symm.permCongr s := rfl

private theorem mkP_loops (m : ℕ) (s t : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hs : s*s=1) (hsf : ∀ x, s x ≠ x) (ht : t*t=1) (htf : ∀ x, t x ≠ x) :
    (mkP m s hs hsf).loops (mkP m t ht htf) = gcount (s * t) / 2 := by
  unfold Pairing.loops
  rw [mkP_val, mkP_val, ← Equiv.permCongr_mul, cycleCount_eq_gcount, gcount_permCongr]

/-- The close pairing on `Fin (2(m+1))`. -/
private noncomputable def closeP (m : ℕ) (r : Pairing m) : Pairing (m+1) :=
  mkP m (closeFun m r.1) (closeFun_invol m r.1 r.2.1) (closeFun_fpf m r.1 r.2.2)
/-- The splice pairing on `Fin (2(m+1))`. -/
private noncomputable def spliceP (m : ℕ) (a : Fin (2*m)) (r : Pairing m) : Pairing (m+1) :=
  mkP m (spliceP' m a r.1 r.2.1 r.2.2) (spliceP'_invol m a r.1 r.2.1 r.2.2)
    (spliceP'_fpf m a r.1 r.2.1 r.2.2)

private theorem loops_closeP (m : ℕ) (s r : Pairing m) :
    (closeP m s).loops (closeP m r) = s.loops r + 1 := by
  unfold closeP
  rw [mkP_loops, gcount_closeMul, ← cycleCount_eq_gcount]
  show (cycleCount (2*m) (s.1 * r.1) + 2) / 2 = _
  show _ = cycleCount (2*m) (s.1 * r.1) / 2 + 1
  omega
private theorem loops_spliceP (m : ℕ) (a : Fin (2*m)) (s r : Pairing m) :
    (closeP m s).loops (spliceP m a r) = s.loops r := by
  unfold closeP spliceP
  rw [mkP_loops, gcount_spliceMul, ← cycleCount_eq_gcount]
  rfl

/-! ### The deletion map and reconstruction -/

private def otherFin2 (y : Fin 2) : Fin 2 := if y = 0 then 1 else 0
private theorem otherFin2_ne (y : Fin 2) : otherFin2 y ≠ y := by fin_cases y <;> decide
private theorem otherFin2_other (y : Fin 2) : otherFin2 (otherFin2 y) = y := by fin_cases y <;> decide
private def followInl (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m))) (c : Fin (2*m)) (y : Fin 2) : Fin (2*m) :=
  (q (Sum.inl (otherFin2 y))).elim (fun _ => c) (fun d => d)
private def delFun {m : ℕ} (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m))) (c : Fin (2*m)) : Fin (2*m) :=
  (q (Sum.inr c)).elim (followInl q c) (fun d => d)
private theorem delFun_eq_of_inr (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m))) (c d : Fin (2*m))
    (h : q (Sum.inr c) = Sum.inr d) : delFun q c = d := by unfold delFun; rw [h]; rfl
private theorem delFun_eq_of_inl (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m))) (c : Fin (2*m)) (y : Fin 2)
    (d : Fin (2*m)) (h : q (Sum.inr c) = Sum.inl y) (h2 : q (Sum.inl (otherFin2 y)) = Sum.inr d) :
    delFun q c = d := by unfold delFun followInl; rw [h]; simp only [Sum.elim_inl]; rw [h2]; rfl

private theorem inl_other_is_inr (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (c : Fin (2*m)) (y : Fin 2)
    (h : q (Sum.inr c) = Sum.inl y) : ∃ d, q (Sum.inl (otherFin2 y)) = Sum.inr d := by
  have hqy : q (Sum.inl y) = Sum.inr c := by have := hinv (Sum.inr c); rw [h] at this; exact this
  cases hcase : q (Sum.inl (otherFin2 y)) with
  | inr d => exact ⟨d, rfl⟩
  | inl z =>
    exfalso
    have hqz : q (Sum.inl z) = Sum.inl (otherFin2 y) := by
      have := hinv (Sum.inl (otherFin2 y)); rw [hcase] at this; exact this
    by_cases hzy : z = y
    · subst hzy; rw [hqy] at hqz; exact Sum.inr_ne_inl hqz
    · have hzo : z = otherFin2 y := by fin_cases y <;> fin_cases z <;> simp_all [otherFin2]
      subst hzo; exact hfpf (Sum.inl (otherFin2 y)) hcase

private theorem delFun_fpf (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (c : Fin (2*m)) : delFun q c ≠ c := by
  cases hc : q (Sum.inr c) with
  | inr d =>
    rw [delFun_eq_of_inr q c d hc]
    intro h; rw [h] at hc; exact hfpf (Sum.inr c) hc
  | inl y =>
    obtain ⟨d, hd⟩ := inl_other_is_inr q hinv hfpf c y hc
    rw [delFun_eq_of_inl q c y d hc hd]
    intro h; rw [h] at hd
    have hqy : q (Sum.inl y) = Sum.inr c := by have := hinv (Sum.inr c); rw [hc] at this; exact this
    have heq : Sum.inl (otherFin2 y) = (Sum.inl y : Fin 2 ⊕ Fin (2*m)) := by
      have h1 : q (Sum.inl (otherFin2 y)) = q (Sum.inl y) := by rw [hd, hqy]
      exact q.injective h1
    exact otherFin2_ne y (Sum.inl_injective heq)

private theorem delFun_invol (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (c : Fin (2*m)) :
    delFun q (delFun q c) = c := by
  cases hc : q (Sum.inr c) with
  | inr d =>
    rw [delFun_eq_of_inr q c d hc]
    have hqd : q (Sum.inr d) = Sum.inr c := by have := hinv (Sum.inr c); rw [hc] at this; exact this
    rw [delFun_eq_of_inr q d c hqd]
  | inl y =>
    obtain ⟨d, hd⟩ := inl_other_is_inr q hinv hfpf c y hc
    rw [delFun_eq_of_inl q c y d hc hd]
    have hqd : q (Sum.inr d) = Sum.inl (otherFin2 y) := by
      have := hinv (Sum.inl (otherFin2 y)); rw [hd] at this; exact this
    have hqy : q (Sum.inl y) = Sum.inr c := by have := hinv (Sum.inr c); rw [hc] at this; exact this
    rw [delFun_eq_of_inl q d (otherFin2 y) c hqd]
    rw [otherFin2_other]; exact hqy

private noncomputable def delPerm (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) : Equiv.Perm (Fin (2*m)) :=
  Function.Involutive.toPerm (delFun q) (fun c => delFun_invol q hinv hfpf c)
@[simp] private theorem delPerm_apply (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (c : Fin (2*m)) :
    delPerm q hinv hfpf c = delFun q c :=
  Function.Involutive.coe_toPerm (fun c => delFun_invol q hinv hfpf c) ▸ rfl
private noncomputable def delPair (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) : Pairing m :=
  ⟨delPerm q hinv hfpf, by
      have hI : Function.Involutive (delFun q) := fun c => delFun_invol q hinv hfpf c
      show delPerm q hinv hfpf * delPerm q hinv hfpf = 1
      ext c
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, delPerm, hI.coe_toPerm]
      exact congrArg Fin.val (hI c),
   fun c => by rw [delPerm_apply]; exact delFun_fpf q hinv hfpf c⟩
@[simp] private theorem delPair_val (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (c : Fin (2*m)) :
    (delPair q hinv hfpf).1 c = delFun q c := delPerm_apply q hinv hfpf c

private theorem delFun_close (m : ℕ) (r : Equiv.Perm (Fin (2*m))) :
    delFun (closeFun m r) = r := by
  funext c; exact delFun_eq_of_inr (closeFun m r) c (r c) (closeFun_inr m r c)
private theorem delFun_splice (m : ℕ) (a : Fin (2*m)) (r : Equiv.Perm (Fin (2*m)))
    (hr : r*r=1) (hfpf : ∀ x, r x ≠ x) :
    delFun (spliceP' m a r hr hfpf) = r := by
  have hra : ∀ x, r (r x) = x := by
    intro x; have : (r*r) x = x := by rw [hr]; rfl
    rwa [Equiv.Perm.mul_apply] at this
  have hane : a ≠ r a := fun h => hfpf a h.symm
  funext c
  by_cases h1 : c = a
  · rw [h1]
    refine delFun_eq_of_inl (spliceP' m a r hr hfpf) a 0 (r a) ?_ ?_
    · rw [spliceP'_apply, spliceFun_inr, if_pos rfl]
    · rw [show otherFin2 (0:Fin 2) = 1 from rfl, spliceP'_apply, spliceFun_inl1]
  · by_cases h2 : c = r a
    · rw [h2, hra]
      refine delFun_eq_of_inl (spliceP' m a r hr hfpf) (r a) 1 a ?_ ?_
      · rw [spliceP'_apply, spliceFun_inr, if_neg (fun h => hane h.symm), if_pos rfl]
      · rw [show otherFin2 (1:Fin 2) = 0 from rfl, spliceP'_apply, spliceFun_inl0]
    · refine delFun_eq_of_inr (spliceP' m a r hr hfpf) c (r c) ?_
      rw [spliceP'_apply, spliceFun_inr, if_neg h1, if_neg h2]

/-! ### Reconstruction -/

private theorem close_inr_is_inr (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (h0 : q (Sum.inl 0) = Sum.inl 1) (c : Fin (2*m)) :
    ∃ d, q (Sum.inr c) = Sum.inr d := by
  have h1 : q (Sum.inl 1) = Sum.inl 0 := by have := hinv (Sum.inl 0); rw [h0] at this; exact this
  cases hc : q (Sum.inr c) with
  | inr d => exact ⟨d, rfl⟩
  | inl y =>
    exfalso
    have hqy : q (Sum.inl y) = Sum.inr c := by have := hinv (Sum.inr c); rw [hc] at this; exact this
    by_cases hy : y = 0
    · subst hy; rw [h0] at hqy; exact Sum.inl_ne_inr hqy
    · have : y = 1 := by omega
      subst this; rw [h1] at hqy; exact Sum.inl_ne_inr hqy

private theorem recon_close (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (h0 : q (Sum.inl 0) = Sum.inl 1) :
    q = closeFun m (delPerm q hinv hfpf) := by
  have h1 : q (Sum.inl 1) = Sum.inl 0 := by have := hinv (Sum.inl 0); rw [h0] at this; exact this
  ext x
  cases x with
  | inl y =>
    by_cases hy : y = 0
    · subst hy; rw [h0, closeFun_inl]; norm_num
    · have : y = 1 := by omega
      subst this; rw [h1, closeFun_inl]; norm_num
  | inr c =>
    obtain ⟨d, hd⟩ := close_inr_is_inr q hinv h0 c
    rw [hd, closeFun_inr, delPerm_apply, delFun_eq_of_inr q c d hd]

private theorem recon_splice (q : Equiv.Perm (Fin 2 ⊕ Fin (2*m)))
    (hinv : ∀ x, q (q x) = x) (hfpf : ∀ x, q x ≠ x) (a : Fin (2*m))
    (h0 : q (Sum.inl 0) = Sum.inr a) :
    q = spliceP' m a (delPerm q hinv hfpf) (by
        ext c; rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, delPerm_apply, delPerm_apply]
        exact congrArg Fin.val (delFun_invol q hinv hfpf c))
      (fun c => by rw [delPerm_apply]; exact delFun_fpf q hinv hfpf c) := by
  set rr := delPerm q hinv hfpf with hrr
  have hrval : ∀ c, rr c = delFun q c := fun c => by rw [hrr, delPerm_apply]
  have hqa : q (Sum.inr a) = Sum.inl 0 := by have := hinv (Sum.inl 0); rw [h0] at this; exact this
  obtain ⟨b, hb⟩ : ∃ b, q (Sum.inl 1) = Sum.inr b := by
    cases hc : q (Sum.inl 1) with
    | inr b => exact ⟨b, rfl⟩
    | inl y =>
      exfalso
      have hq1 : q (Sum.inl y) = Sum.inl 1 := by have := hinv (Sum.inl 1); rw [hc] at this; exact this
      by_cases hy : y = 0
      · subst hy; rw [h0] at hq1; exact Sum.inr_ne_inl hq1
      · have : y = 1 := by omega
        subst this; exact hfpf (Sum.inl 1) hc
  have hqb : q (Sum.inr b) = Sum.inl 1 := by have := hinv (Sum.inl 1); rw [hb] at this; exact this
  have hra : rr a = b := by
    rw [hrval, delFun_eq_of_inl q a 0 b hqa (by rw [show otherFin2 (0:Fin 2)=1 from rfl]; exact hb)]
  ext x
  cases x with
  | inl y =>
    by_cases hy : y = 0
    · subst hy; rw [h0, spliceP'_apply, spliceFun_inl0]
    · have : y = 1 := by omega
      subst this; rw [hb, spliceP'_apply, spliceFun_inl1, hra]
  | inr c =>
    rw [spliceP'_apply, spliceFun_inr]
    by_cases h1 : c = a
    · subst h1; rw [if_pos rfl, hqa]
    · by_cases h2 : c = b
      · rw [if_neg h1, if_pos (h2.trans hra.symm), h2, hqb]
      · rw [if_neg h1, if_neg (fun h => h2 (h.trans hra))]
        obtain ⟨d, hd⟩ : ∃ d, q (Sum.inr c) = Sum.inr d := by
          cases hcd : q (Sum.inr c) with
          | inr d => exact ⟨d, rfl⟩
          | inl y =>
            exfalso
            have hqy : q (Sum.inl y) = Sum.inr c := by
              have := hinv (Sum.inr c); rw [hcd] at this; exact this
            by_cases hy : y = 0
            · subst hy; rw [h0] at hqy; exact h1 (Sum.inr_injective hqy.symm)
            · have : y = 1 := by omega
              subst this; rw [hb] at hqy; exact h2 (Sum.inr_injective hqy.symm)
        rw [hd]
        congr 1
        rw [show (delPerm q hinv hfpf) c = delFun q c from hrval c, delFun_eq_of_inr q c d hd]

/-! ### The deletion bijection -/

/-- The sum-model image of a pairing. -/
private def qhat (q : Pairing (m+1)) : Equiv.Perm (Fin 2 ⊕ Fin (2*m)) := (Em m).permCongr q.1
private theorem qhat_invol (q : Pairing (m+1)) (x) : qhat q (qhat q x) = x := by
  show (qhat q * qhat q) x = x
  unfold qhat
  rw [← Equiv.permCongr_mul, q.2.1]; simp [Equiv.permCongr_apply]
private theorem qhat_fpf (q : Pairing (m+1)) (x) : qhat q x ≠ x := by
  unfold qhat
  rw [Equiv.permCongr_apply]
  intro h
  apply q.2.2 ((Em m).symm x)
  apply (Em m).injective
  rw [Equiv.apply_symm_apply]; exact h
private theorem qhat_mkP (s : Equiv.Perm (Fin 2 ⊕ Fin (2*m))) (hinv) (hfpf) :
    qhat (mkP m s hinv hfpf) = s := by
  unfold qhat
  rw [mkP_val]
  ext x; simp [Equiv.permCongr_apply]

private abbrev IdxT (m : ℕ) : Type := Pairing m ⊕ (Fin (2*m) × Pairing m)

private noncomputable def biFun (m : ℕ) : IdxT m → Pairing (m+1)
  | Sum.inl r => closeP m r
  | Sum.inr (a, r) => spliceP m a r

private noncomputable def biInv (m : ℕ) (q : Pairing (m+1)) : IdxT m :=
  match qhat q (Sum.inl 0) with
  | Sum.inl _ => Sum.inl (delPair (qhat q) (qhat_invol q) (qhat_fpf q))
  | Sum.inr a => Sum.inr (a, delPair (qhat q) (qhat_invol q) (qhat_fpf q))

private theorem delPair_closeP (r : Pairing m) :
    delPair (qhat (closeP m r)) (qhat_invol _) (qhat_fpf _) = r := by
  apply Subtype.ext
  apply Equiv.ext; intro c
  rw [delPair_val]
  have : qhat (closeP m r) = closeFun m r.1 := by unfold closeP; rw [qhat_mkP]
  rw [this, delFun_close]
private theorem delPair_spliceP (a : Fin (2*m)) (r : Pairing m) :
    delPair (qhat (spliceP m a r)) (qhat_invol _) (qhat_fpf _) = r := by
  apply Subtype.ext
  apply Equiv.ext; intro c
  rw [delPair_val]
  have : qhat (spliceP m a r) = spliceP' m a r.1 r.2.1 r.2.2 := by unfold spliceP; rw [qhat_mkP]
  rw [this, delFun_splice]

private theorem qhat_closeP_zero (r : Pairing m) : qhat (closeP m r) (Sum.inl 0) = Sum.inl 1 := by
  unfold closeP; rw [qhat_mkP, closeFun_inl]; norm_num
private theorem qhat_spliceP_zero (a : Fin (2*m)) (r : Pairing m) :
    qhat (spliceP m a r) (Sum.inl 0) = Sum.inr a := by
  unfold spliceP; rw [qhat_mkP, spliceP'_apply, spliceFun_inl0]

private theorem bi_left_inv (m : ℕ) (x : IdxT m) : biInv m (biFun m x) = x := by
  cases x with
  | inl r =>
    show biInv m (closeP m r) = Sum.inl r
    unfold biInv
    rw [qhat_closeP_zero r]
    rw [delPair_closeP r]
  | inr ar =>
    obtain ⟨a, r⟩ := ar
    show biInv m (spliceP m a r) = Sum.inr (a, r)
    unfold biInv
    rw [qhat_spliceP_zero a r]
    rw [delPair_spliceP a r]

private theorem bi_right_inv (m : ℕ) (q : Pairing (m+1)) : biFun m (biInv m q) = q := by
  unfold biInv
  cases hc : qhat q (Sum.inl 0) with
  | inl y =>
    have hy : y = 1 := by
      by_contra hne
      have : y = 0 := by omega
      subst this
      exact qhat_fpf q (Sum.inl 0) hc
    subst hy
    show biFun m (Sum.inl (delPair (qhat q) (qhat_invol q) (qhat_fpf q))) = q
    show closeP m (delPair (qhat q) (qhat_invol q) (qhat_fpf q)) = q
    apply Subtype.ext
    unfold closeP
    rw [mkP_val]
    have hrec := recon_close (qhat q) (qhat_invol q) (qhat_fpf q) hc
    have : (delPair (qhat q) (qhat_invol q) (qhat_fpf q)).1 = delPerm (qhat q) (qhat_invol q) (qhat_fpf q) := rfl
    rw [this, ← hrec]
    unfold qhat
    ext z; simp [Equiv.permCongr_apply]
  | inr a =>
    show biFun m (Sum.inr (a, delPair (qhat q) (qhat_invol q) (qhat_fpf q))) = q
    show spliceP m a (delPair (qhat q) (qhat_invol q) (qhat_fpf q)) = q
    apply Subtype.ext
    unfold spliceP
    rw [mkP_val]
    have hrec := recon_splice (qhat q) (qhat_invol q) (qhat_fpf q) a hc
    have hsp : spliceP' m a (delPair (qhat q) (qhat_invol q) (qhat_fpf q)).1
          (delPair (qhat q) (qhat_invol q) (qhat_fpf q)).2.1
          (delPair (qhat q) (qhat_invol q) (qhat_fpf q)).2.2 = qhat q := by
      apply Equiv.ext; intro z
      rw [spliceP'_apply]
      conv_rhs => rw [hrec]
      rw [spliceP'_apply]
      rfl
    rw [hsp]
    unfold qhat
    ext z; simp [Equiv.permCongr_apply]

private noncomputable def biEquiv (m : ℕ) : IdxT m ≃ Pairing (m+1) where
  toFun := biFun m
  invFun := biInv m
  left_inv := bi_left_inv m
  right_inv := bi_right_inv m

/-! ### The recursion -/

private theorem rowSum_succ_proof (N : k) (m : ℕ) :
    rowSum k (m + 1) N = (N + 2 * (m : k)) * rowSum k m N := by
  set p : Pairing (m+1) := closeP m (refPairing m) with hp
  rw [← rowSum_eq N p]
  rw [← Equiv.sum_comp (biEquiv m) (fun q => N ^ (p.loops q))]
  rw [Fintype.sum_sum_type]
  have hclose : ∀ r : Pairing m, N ^ (p.loops (biEquiv m (Sum.inl r)))
      = N * N ^ ((refPairing m).loops r) := by
    intro r
    show N ^ (p.loops (closeP m r)) = _
    rw [hp, loops_closeP, pow_succ]; ring
  have hsplice : ∀ ar : Fin (2*m) × Pairing m,
      N ^ (p.loops (biEquiv m (Sum.inr ar))) = N ^ ((refPairing m).loops ar.2) := by
    intro ⟨a, r⟩
    show N ^ (p.loops (spliceP m a r)) = _
    rw [hp, loops_spliceP]
  simp only [biEquiv, Equiv.coe_fn_mk] at hclose hsplice ⊢
  rw [Finset.sum_congr rfl (fun r _ => hclose r)]
  rw [Finset.sum_congr rfl (fun ar _ => hsplice ar)]
  rw [← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  have hrowm : ∑ r : Pairing m, N ^ ((refPairing m).loops r) = rowSum k m N := rfl
  rw [hrowm]
  rw [show (∑ a : Fin (2*m), ∑ r : Pairing m, N ^ ((refPairing m).loops r))
        = ∑ a : Fin (2*m), rowSum k m N from by
      apply Finset.sum_congr rfl; intro a _; exact hrowm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end RSS

theorem rowSum_succ (N : k) (m : ℕ) :
    rowSum k (m + 1) N = (N + 2 * (m : k)) * rowSum k m N := RSS.rowSum_succ_proof N m

/-- Closed form of the row sum: the even-rising factorial, by the recursion. -/
theorem rowSum_eq_evenRising (N : k) (n : ℕ) : rowSum k n N = evenRising k n N := by
  induction n with
  | zero => rw [rowSum_zero, evenRising]; simp
  | succ m ih =>
    rw [rowSum_succ, ih, evenRising, evenRising, Finset.prod_range_succ]; ring

/-- All-ones absorption: row sums of the orthogonal Gram are the even-rising
factorial. Blueprint: `thm:orth_ones_absorb`. -/
theorem orthGram_mulVec_one (N : k) :
    (orthGram k n N).mulVec 1 = evenRising k n N • 1 := by
  funext p
  simp only [Matrix.mulVec, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  rw [dotProduct]
  simp only [orthGram, Pi.one_apply, mul_one]
  rw [rowSum_eq, rowSum_eq_evenRising]

end OnesAbsorption

section DetVecAbsorption

/-- The "left-half swap" on `Fin n ⊕ Fin n`. -/
abbrev leftSwap (a b : Fin n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.sumCongr (Equiv.swap a b) 1

@[simp] theorem leftSwap_inl (a b x : Fin n) :
    leftSwap a b (Sum.inl x) = Sum.inl (Equiv.swap a b x) := rfl
@[simp] theorem leftSwap_inr (a b y : Fin n) :
    leftSwap a b (Sum.inr y) = Sum.inr y := rfl

theorem leftSwap_sq (a b : Fin n) : leftSwap a b * leftSwap a b = 1 := by
  ext x; cases x with
  | inl x => simp [Equiv.Perm.one_apply]
  | inr y => simp [Equiv.Perm.one_apply]

theorem swapAcrossPerm_mul_swap (ρ : Equiv.Perm (Fin n)) (a b : Fin n) :
    swapAcrossPerm (ρ * Equiv.swap a b)
      = leftSwap a b * swapAcrossPerm ρ * leftSwap a b := by
  ext x
  cases x with
  | inl x =>
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, leftSwap_inl,
      swapAcrossPerm_inl, swapAcrossPerm_inl, leftSwap_inr, Equiv.Perm.mul_apply]
  | inr y =>
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, leftSwap_inr,
      swapAcrossPerm_inr, swapAcrossPerm_inr, leftSwap_inl, mul_inv_rev,
      Equiv.Perm.mul_apply, Equiv.swap_inv]

/-- The pairing `p` transported to `Fin n ⊕ Fin n` via `pairEquiv` (an involution). -/
def transp (p : Pairing n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  (pairEquiv n).permCongr p.1

theorem transp_apply (p : Pairing n) (x : Fin n ⊕ Fin n) :
    transp p x = (pairEquiv n) (p.1 ((pairEquiv n).symm x)) := by
  simp [transp, Equiv.permCongr_apply]

theorem transp_qPair (ρ : Equiv.Perm (Fin n)) :
    transp (qPair ρ) = swapAcrossPerm ρ := by
  ext x
  rw [transp_apply, qPair_apply]
  simp

theorem transp_involutive (p : Pairing n) (x : Fin n ⊕ Fin n) :
    transp p (transp p x) = x := by
  rw [transp_apply, transp_apply, Equiv.symm_apply_apply, pairing_invol, Equiv.apply_symm_apply]

theorem leftSwap_comm (p : Pairing n) {a b : Fin n}
    (hab : a ≠ b) (hpa : transp p (Sum.inl a) = Sum.inl b) :
    leftSwap a b * transp p = transp p * leftSwap a b := by
  have hpb : transp p (Sum.inl b) = Sum.inl a := by
    have := transp_involutive p (Sum.inl a); rw [hpa] at this; exact this
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  cases x with
  | inl x =>
    by_cases hxa : x = a
    · subst hxa
      rw [leftSwap_inl, Equiv.swap_apply_left, hpa, hpb, leftSwap_inl, Equiv.swap_apply_right]
    · by_cases hxb : x = b
      · subst hxb
        rw [leftSwap_inl, Equiv.swap_apply_right, hpb, hpa, leftSwap_inl, Equiv.swap_apply_left]
      · rw [leftSwap_inl, Equiv.swap_apply_of_ne_of_ne hxa hxb]
        set y := transp p (Sum.inl x) with hy
        have hyne_a : y ≠ Sum.inl a := by
          intro h
          have : transp p y = transp p (Sum.inl a) := by rw [h]
          rw [hy, transp_involutive, hpa] at this
          exact hxb (Sum.inl_injective this)
        have hyne_b : y ≠ Sum.inl b := by
          intro h
          have : transp p y = transp p (Sum.inl b) := by rw [h]
          rw [hy, transp_involutive, hpb] at this
          exact hxa (Sum.inl_injective this)
        cases hyc : y with
        | inl z =>
          rw [leftSwap_inl, Equiv.swap_apply_of_ne_of_ne]
          · intro hza; exact hyne_a (by rw [hyc, hza])
          · intro hzb; exact hyne_b (by rw [hyc, hzb])
        | inr z => rw [leftSwap_inr]
  | inr y =>
    rw [leftSwap_inr]
    set z := transp p (Sum.inr y) with hz
    have hzne_a : z ≠ Sum.inl a := by
      intro h
      have : transp p z = transp p (Sum.inl a) := by rw [h]
      rw [hz, transp_involutive, hpa] at this
      exact Sum.inl_ne_inr this.symm
    have hzne_b : z ≠ Sum.inl b := by
      intro h
      have : transp p z = transp p (Sum.inl b) := by rw [h]
      rw [hz, transp_involutive, hpb] at this
      exact Sum.inl_ne_inr this.symm
    cases hzc : z with
    | inl w =>
      rw [leftSwap_inl, Equiv.swap_apply_of_ne_of_ne]
      · intro hwa; exact hzne_a (by rw [hzc, hwa])
      · intro hwb; exact hzne_b (by rw [hzc, hwb])
    | inr w => rw [leftSwap_inr]

/-- The transported left-swap as a permutation of `Fin (2n)`. -/
def Sperm (a b : Fin n) : Equiv.Perm (Fin (2 * n)) :=
  (pairEquiv n).symm.permCongr (leftSwap a b)

theorem Sperm_sq (a b : Fin n) : Sperm a b * Sperm a b = 1 := by
  unfold Sperm
  rw [← Equiv.permCongr_mul, leftSwap_sq]
  ext x; simp [Equiv.permCongr_apply]

theorem perm_eq_permCongr_transp (p : Pairing n) :
    p.1 = (pairEquiv n).symm.permCongr (transp p) := by
  ext x
  rw [transp]
  simp [Equiv.permCongr_apply]

theorem qPair_eq_permCongr (ρ : Equiv.Perm (Fin n)) :
    (qPair ρ).1 = (pairEquiv n).symm.permCongr (swapAcrossPerm ρ) := by
  rw [perm_eq_permCongr_transp (qPair ρ), transp_qPair]

theorem qPair_mul_swap_conj (ρ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (qPair (ρ * Equiv.swap a b)).1 = Sperm a b * (qPair ρ).1 * Sperm a b := by
  rw [qPair_eq_permCongr, swapAcrossPerm_mul_swap, qPair_eq_permCongr]
  unfold Sperm
  rw [← Equiv.permCongr_mul, ← Equiv.permCongr_mul]

theorem Sperm_comm (p : Pairing n) {a b : Fin n}
    (hab : a ≠ b) (hpa : transp p (Sum.inl a) = Sum.inl b) :
    Sperm a b * p.1 = p.1 * Sperm a b := by
  rw [perm_eq_permCongr_transp p]
  unfold Sperm
  rw [← Equiv.permCongr_mul, ← Equiv.permCongr_mul, leftSwap_comm p hab hpa]

/-- **Loop preservation.** Contracting the shared top-top chord `{a,b}` of `p` keeps the
loop count fixed under the involution `ρ ↦ ρ * swap a b`. -/
theorem loops_preserved (p : Pairing n) {a b : Fin n}
    (hab : a ≠ b) (hpa : transp p (Sum.inl a) = Sum.inl b) (ρ : Equiv.Perm (Fin n)) :
    p.loops (qPair (ρ * Equiv.swap a b)) = p.loops (qPair ρ) := by
  unfold Pairing.loops
  congr 1
  rw [qPair_mul_swap_conj]
  have hSinv : (Sperm a b)⁻¹ = Sperm a b :=
    inv_eq_of_mul_eq_one_right (Sperm_sq a b)
  have hcomm : p.1 * Sperm a b = Sperm a b * p.1 := (Sperm_comm p hab hpa).symm
  have hkey : p.1 * (Sperm a b * (qPair ρ).1 * Sperm a b)
      = Sperm a b * (p.1 * (qPair ρ).1) * (Sperm a b)⁻¹ := by
    rw [hSinv,
      show p.1 * (Sperm a b * (qPair ρ).1 * Sperm a b)
          = (p.1 * Sperm a b) * ((qPair ρ).1 * Sperm a b) by
        simp only [mul_assoc],
      hcomm,
      show Sperm a b * p.1 * ((qPair ρ).1 * Sperm a b)
          = Sperm a b * (p.1 * (qPair ρ).1) * Sperm a b by
        simp only [mul_assoc]]
  rw [hkey, cycleCount_conj]

/-- If `transp p` maps every `inl` to an `inr`, then `p` is permutation-like. -/
theorem perm_like_of_no_topchord (p : Pairing n)
    (h : ∀ a : Fin n, ∀ b : Fin n, transp p (Sum.inl a) ≠ Sum.inl b) :
    ∃ ρ : Equiv.Perm (Fin n), p = qPair ρ := by
  have hforward : ∀ a : Fin n, ∃ c : Fin n, transp p (Sum.inl a) = Sum.inr c := by
    intro a
    cases hc : transp p (Sum.inl a) with
    | inl b => exact absurd hc (h a b)
    | inr c => exact ⟨c, rfl⟩
  have hbackward : ∀ b : Fin n, ∃ d : Fin n, transp p (Sum.inr b) = Sum.inl d := by
    intro b
    cases hc : transp p (Sum.inr b) with
    | inl d => exact ⟨d, rfl⟩
    | inr c =>
      exfalso
      have hcb : transp p (Sum.inr c) = Sum.inr b := by
        have := transp_involutive p (Sum.inr b); rw [hc] at this; exact this
      let φ : Fin n → Fin n := fun a => (hforward a).choose
      have hφ : ∀ a, transp p (Sum.inl a) = Sum.inr (φ a) := fun a => (hforward a).choose_spec
      have hφinj : Function.Injective φ := by
        intro a a' haa
        have : transp p (Sum.inl a) = transp p (Sum.inl a') := by rw [hφ, hφ, haa]
        exact Sum.inl_injective ((transp p).injective this)
      have hφsurj : Function.Surjective φ := Finite.surjective_of_injective hφinj
      obtain ⟨a, ha⟩ := hφsurj c
      have : transp p (Sum.inr c) = Sum.inl a := by
        have hh := transp_involutive p (Sum.inl a); rw [hφ a, ha] at hh; exact hh
      rw [this] at hcb
      exact Sum.inl_ne_inr hcb
  let φ : Fin n → Fin n := fun a => (hforward a).choose
  have hφ : ∀ a, transp p (Sum.inl a) = Sum.inr (φ a) := fun a => (hforward a).choose_spec
  let ψ : Fin n → Fin n := fun b => (hbackward b).choose
  have hψ : ∀ b, transp p (Sum.inr b) = Sum.inl (ψ b) := fun b => (hbackward b).choose_spec
  have hψφ : ∀ a, ψ (φ a) = a := by
    intro a
    have h1 : transp p (Sum.inr (φ a)) = Sum.inl a := by
      have hh := transp_involutive p (Sum.inl a); rw [hφ a] at hh; exact hh
    rw [hψ (φ a)] at h1
    exact Sum.inl_injective h1
  have hφψ : ∀ b, φ (ψ b) = b := by
    intro b
    have h1 : transp p (Sum.inl (ψ b)) = Sum.inr b := by
      have hh := transp_involutive p (Sum.inr b); rw [hψ b] at hh; exact hh
    rw [hφ (ψ b)] at h1
    exact Sum.inr_injective h1
  let ρ : Equiv.Perm (Fin n) := ⟨φ, ψ, hψφ, hφψ⟩
  refine ⟨ρ, ?_⟩
  have htranspeq : transp p = swapAcrossPerm ρ := by
    ext x
    cases x with
    | inl a => rw [hφ a]; rfl
    | inr b =>
      rw [hψ b]
      show Sum.inl (ψ b) = Sum.inl (ρ⁻¹ b)
      rfl
  apply Subtype.ext
  rw [perm_eq_permCongr_transp p, htranspeq, ← transp_qPair, ← perm_eq_permCongr_transp]

/-- A non-permutation-like pairing has a top-top chord `{a,b}` (both in the lower half). -/
theorem exists_topchord (p : Pairing n) (h : ∀ τ : Equiv.Perm (Fin n), p ≠ qPair τ) :
    ∃ a b : Fin n, a ≠ b ∧ transp p (Sum.inl a) = Sum.inl b := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_exists, not_and] at hcon
  have hno : ∀ a b : Fin n, transp p (Sum.inl a) ≠ Sum.inl b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      intro heq
      have hta := transp_apply p (Sum.inl a)
      rw [heq] at hta
      have hfix : p.1 ((pairEquiv n).symm (Sum.inl a)) = (pairEquiv n).symm (Sum.inl a) := by
        apply (pairEquiv n).injective
        rw [Equiv.apply_symm_apply]
        exact hta.symm
      exact p.2.2 _ hfix
    · exact hcon a b hab
  obtain ⟨ρ, hρ⟩ := perm_like_of_no_topchord p hno
  exact h ρ hρ

/-- `detVec (qPair τ) = sgn τ`. -/
theorem detVec_qPair (τ : Equiv.Perm (Fin n)) :
    detVec k (qPair τ) = ((Equiv.Perm.sign τ : ℤ) : k) := by
  unfold detVec
  rw [Finset.sum_eq_single τ]
  · rw [if_pos rfl]
  · intro ρ _ hρ
    rw [if_neg]
    intro h
    exact hρ (qPair_injective h).symm
  · intro h; exact absurd (Finset.mem_univ τ) h

/-- `detVec p = 0` when `p` is not permutation-like. -/
theorem detVec_eq_zero (p : Pairing n) (h : ∀ τ : Equiv.Perm (Fin n), p ≠ qPair τ) :
    detVec k p = 0 := by
  unfold detVec
  apply Finset.sum_eq_zero
  intro ρ _
  rw [if_neg (h ρ)]

/-- The signed sum `∑ σ, sgn σ · N ^ c(σ)` is the falling factorial (via `sgnHom_gram`). -/
theorem sum_sgn_pow_cycleCount (N : k) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * N ^ cycleCount n σ
      = fallingFact k n N := by
  unfold fallingFact
  rw [← sgnHom_gram k n N, sgnHom_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (gram_apply k n N σ).symm

/-- STEP 1: the row entry collapses to a signed sum over permutations. -/
theorem mulVec_detVec_entry (N : k) (p : Pairing n) :
    ((orthGram k n N).mulVec (detVec k)) p
      = ∑ ρ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign ρ : ℤ) : k) * N ^ (p.loops (qPair ρ)) := by
  show ∑ q : Pairing n, (orthGram k n N) p q * detVec k q = _
  show ∑ q : Pairing n, N ^ (p.loops q) *
      (∑ ρ : Equiv.Perm (Fin n), if q = qPair ρ then ((Equiv.Perm.sign ρ : ℤ) : k) else 0) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.sum_eq_single (qPair ρ)]
  · rw [if_pos rfl]; ring
  · intro q _ hq
    rw [if_neg (fun h => hq h), mul_zero]
  · intro h; exact absurd (Finset.mem_univ (qPair ρ)) h

/-- STEP 2, permutation-like case: reindex by `Equiv.mulLeft τ` and apply `sgnHom_gram`. -/
theorem mulVec_detVec_perm_case (N : k) (τ : Equiv.Perm (Fin n)) :
    ((orthGram k n N).mulVec (detVec k)) (qPair τ)
      = (fallingFact k n N • detVec k) (qPair τ) := by
  rw [mulVec_detVec_entry]
  have hloop : ∀ ρ : Equiv.Perm (Fin n),
      (qPair τ).loops (qPair ρ) = cycleCount n (τ⁻¹ * ρ) := fun ρ => loops_qPair_qPair τ ρ
  simp_rw [hloop]
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)
        (fun ρ => ((Equiv.Perm.sign ρ : ℤ) : k) * N ^ cycleCount n (τ⁻¹ * ρ))]
  simp only [Equiv.coe_mulLeft]
  have hsimp : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign (τ * σ) : ℤ) : k) * N ^ cycleCount n (τ⁻¹ * (τ * σ))
        = ((Equiv.Perm.sign τ : ℤ) : k) *
            (((Equiv.Perm.sign σ : ℤ) : k) * N ^ cycleCount n σ) := by
    intro σ
    rw [← mul_assoc τ⁻¹ τ σ, inv_mul_cancel, one_mul, map_mul]
    push_cast
    ring
  simp_rw [hsimp]
  rw [← Finset.mul_sum, sum_sgn_pow_cycleCount]
  show _ = fallingFact k n N • detVec k (qPair τ)
  rw [detVec_qPair, smul_eq_mul]
  ring

/-- STEP 2, non-permutation case: a sign-reversing involution kills the signed sum. -/
theorem signed_loop_sum_eq_zero (N : k) (p : Pairing n)
    (h : ∀ τ : Equiv.Perm (Fin n), p ≠ qPair τ) :
    ∑ ρ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign ρ : ℤ) : k) * N ^ (p.loops (qPair ρ)) = 0 := by
  obtain ⟨a, b, hab, hpa⟩ := exists_topchord p h
  apply Finset.sum_involution (fun ρ _ => ρ * Equiv.swap a b)
  · intro ρ _
    rw [loops_preserved p hab hpa ρ]
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    push_cast
    ring
  · intro ρ _ _ heq
    have hone : Equiv.swap a b = 1 :=
      mul_left_cancel (a := ρ) (by rw [mul_one]; exact heq)
    rw [Equiv.swap_eq_one_iff] at hone
    exact hab hone
  · intro ρ _; exact Finset.mem_univ _
  · intro ρ _
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- Determinant-vector absorption: the signed permutation-supported vector is
an eigenvector with the plain falling factorial as eigenvalue.
Blueprint: `thm:orth_det_absorb`. -/
theorem orthGram_mulVec_detVec (N : k) :
    (orthGram k n N).mulVec (detVec k) = fallingFact k n N • detVec k := by
  funext p
  by_cases hp : ∃ τ : Equiv.Perm (Fin n), p = qPair τ
  · obtain ⟨τ, rfl⟩ := hp
    exact mulVec_detVec_perm_case N τ
  · rw [not_exists] at hp
    rw [mulVec_detVec_entry, signed_loop_sum_eq_zero N p hp]
    show 0 = (fallingFact k n N • detVec k) p
    rw [Pi.smul_apply, detVec_eq_zero p hp, smul_zero]

end DetVecAbsorption

/-- A commuting Penrose partner at matrix level: the two Penrose equations
plus explicit commutation (which the group-algebra setting of
`Weingarten.BelowThreshold` provides for free). Blueprint: `def:comm_penrose`. -/
structure IsCommPenrosePartner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G W : Matrix ι ι k) : Prop where
  gwg : G * W * G = G
  wgw : W * G * W = W
  comm : W * G = G * W

/-- Against an **invertible** `G`, a commuting Penrose partner is a genuine two-sided
inverse: `G * W = 1`. Shared derivation step of the four conditional sum rules
(`evenRising_smul_vecMul_one`, `fallingFact_smul_vecMul_detVec` here;
`evenFalling_smul_vecMul_epsVec`, `risingShift_smul_vecMul_epsDetVec` in
`Weingarten.SymplecticGram`). -/
theorem IsCommPenrosePartner.mul_eq_one_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G W : Matrix ι ι k} (h : IsCommPenrosePartner G W) (hu : IsUnit G) :
    G * W = 1 := by
  have hwg : W * G = 1 :=
    hu.mul_right_injective (by
      show G * (W * G) = G * 1
      rw [← mul_assoc, h.gwg, mul_one])
  exact mul_eq_one_comm.mp hwg

/-- **Generic per-eigenvalue Penrose rule** (division-free `λ`-smul form): against a
commuting Penrose partner, a left eigen-row of `G` whose eigenvalue is a unit
reproduces itself with one extra factor of `W` — no invertibility of `G` itself.
From `y G W G = y G` the eigen-row hypothesis gives `lam • (y W G) = lam • y`;
cancelling the unit `lam` and commuting `W G = G W` turns the leftover `G` back into
`lam`. This strengthens the four conditional sum rules to singular-Gram parameters:
only the single eigenvalue must be a unit. Blueprint: `lem:penrose_eigen`. -/
theorem IsCommPenrosePartner.smul_vecMul_eq_of_vecMul_eq_smul {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G W : Matrix ι ι k} (h : IsCommPenrosePartner G W) {lam : k}
    {y : ι → k} (hy : Matrix.vecMul y G = lam • y) (hlam : IsUnit lam) :
    lam • Matrix.vecMul y W = y := by
  have hwg : Matrix.vecMul y (W * G) = y := by
    refine hlam.smul_left_cancel.mp ?_
    calc lam • Matrix.vecMul y (W * G)
        = Matrix.vecMul (lam • y) (W * G) := (Matrix.smul_vecMul lam y (W * G)).symm
      _ = Matrix.vecMul (Matrix.vecMul y G) (W * G) := by rw [hy]
      _ = Matrix.vecMul y (G * (W * G)) := Matrix.vecMul_vecMul y G (W * G)
      _ = Matrix.vecMul y G := by rw [← mul_assoc, h.gwg]
      _ = lam • y := hy
  calc lam • Matrix.vecMul y W
      = Matrix.vecMul (lam • y) W := (Matrix.smul_vecMul lam y W).symm
    _ = Matrix.vecMul (Matrix.vecMul y G) W := by rw [hy]
    _ = Matrix.vecMul y (G * W) := Matrix.vecMul_vecMul y G W
    _ = Matrix.vecMul y (W * G) := by rw [h.comm]
    _ = y := hwg

/-- The two-line evaluation: against a commuting Penrose partner, the
determinant covector reproduces itself with one extra factor of `W`.
Blueprint: `lem:orth_two_line`. -/
theorem vecMul_detVec_two_line {N : k} {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W) :
    Matrix.vecMul (detVec k) W
      = fallingFact k n N • Matrix.vecMul (detVec k) (W * W) := by
  conv_lhs => rw [← h.wgw]
  rw [h.comm, mul_assoc, ← Matrix.vecMul_vecMul, orthGram_vecMul_eq, orthGram_mulVec_detVec,
    Matrix.smul_vecMul]

/-- Exact vanishing: when the falling factorial vanishes, every commuting
Penrose partner kills the determinant covector. Blueprint:
`thm:orth_det_vanish`. -/
theorem vecMul_detVec_eq_zero {N : k} {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W)
    (hN : fallingFact k n N = 0) :
    Matrix.vecMul (detVec k) W = 0 := by
  rw [vecMul_detVec_two_line h, hN, zero_smul]

/-- Kernel witness: when the falling factorial vanishes the determinant
vector lies in the kernel of the Gram. Blueprint: `thm:orth_ker_witness`. -/
theorem orthGram_mulVec_detVec_eq_zero {N : k} (hN : fallingFact k n N = 0) :
    (orthGram k n N).mulVec (detVec k) = 0 := by
  rw [orthGram_mulVec_detVec, hN, zero_smul]

/-- Gram singularity below threshold. Blueprint: `thm:orth_not_unit`. -/
theorem not_isUnit_orthGram {N : k} (hN : fallingFact k n N = 0)
    (hv : detVec k (n := n) ≠ 0) :
    ¬ IsUnit (orthGram k n N) := by
  intro hu
  apply hv
  obtain ⟨u, hu_eq⟩ := hu
  have hinv : (↑u⁻¹ : Matrix (Pairing n) (Pairing n) k) * orthGram k n N = 1 := by
    rw [← hu_eq]; exact u.inv_mul
  have : (↑u⁻¹ : Matrix (Pairing n) (Pairing n) k).mulVec
      ((orthGram k n N).mulVec (detVec k)) = detVec k := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [orthGram_mulVec_detVec_eq_zero hN, Matrix.mulVec_zero] at this
  exact this.symm

/-- The falling factorial vanishes at integer parameters below threshold: the
factor at `j = N` is zero — the orthogonal twin of `evenFalling_eq_zero`. -/
theorem fallingFact_eq_zero_of_lt {N : ℕ} (h : N < n) :
    fallingFact k n (N : k) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr h) (sub_self _)

/-- The determinant vector is nonzero: by `detVec_qPair` it takes the value `1`
on the identity-permutation pairing — the orthogonal twin of `epsVec_ne_zero`. -/
theorem detVec_ne_zero [Nontrivial k] : detVec (n := n) k ≠ 0 := by
  intro h
  have h1 : detVec k (qPair (1 : Equiv.Perm (Fin n))) = 0 := by rw [h]; rfl
  rw [detVec_qPair, map_one, Units.val_one, Int.cast_one] at h1
  exact one_ne_zero h1

/-- Unconditional Gram singularity at integer parameters below threshold: both
hypotheses of `not_isUnit_orthGram` are discharged from `N < n` alone
(`fallingFact_eq_zero_of_lt`, `detVec_ne_zero`), restoring parity with
`not_isUnit_sympGram`. Blueprint: `thm:orth_not_unit`. -/
theorem not_isUnit_orthGram_of_lt [Nontrivial k] {N : ℕ} (h : N < n) :
    ¬ IsUnit (orthGram k n (N : k)) :=
  not_isUnit_orthGram (fallingFact_eq_zero_of_lt h) detVec_ne_zero

/-- Conditional even-rising rule above threshold: row sums of any commuting
Penrose partner of an invertible Gram invert the even-rising factorial.
Blueprint: `thm:orth_rising_rule`. -/
theorem evenRising_smul_vecMul_one {N : k} {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W)
    (hu : IsUnit (orthGram k n N)) :
    evenRising k n N • Matrix.vecMul 1 W = 1 := by
  have hGW : orthGram k n N * W = 1 := h.mul_eq_one_of_isUnit hu
  rw [← Matrix.smul_vecMul, ← orthGram_mulVec_one, ← orthGram_vecMul_eq,
    Matrix.vecMul_vecMul, hGW, Matrix.vecMul_one]

/-- Conditional falling rule above threshold: signed determinant sums of any
commuting Penrose partner of an invertible Gram invert the falling factorial.
Blueprint: `thm:orth_falling_rule`. -/
theorem fallingFact_smul_vecMul_detVec {N : k}
    {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W)
    (hu : IsUnit (orthGram k n N)) :
    fallingFact k n N • Matrix.vecMul (detVec k) W = detVec k := by
  have hGW : orthGram k n N * W = 1 := h.mul_eq_one_of_isUnit hu
  rw [← Matrix.smul_vecMul, ← orthGram_mulVec_detVec, ← orthGram_vecMul_eq,
    Matrix.vecMul_vecMul, hGW, Matrix.vecMul_one]

/-- Per-eigenvalue even-rising rule: the row sums of any commuting Penrose partner
invert the even-rising factorial whenever that **single eigenvalue** is a unit — no
invertibility of the Gram itself, so the rule also covers the singular band (e.g.
`n = 2`, `N = 1`, where the falling factorial vanishes but `evenRising = 3` is a unit
over `ℚ`). Strengthens `evenRising_smul_vecMul_one`.
Blueprint: `thm:orth_rising_rule_eigen`. -/
theorem evenRising_smul_vecMul_one_of_partner {N : k}
    {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W)
    (hu : IsUnit (evenRising k n N)) :
    evenRising k n N • Matrix.vecMul 1 W = 1 :=
  h.smul_vecMul_eq_of_vecMul_eq_smul
    (by rw [orthGram_vecMul_eq, orthGram_mulVec_one]) hu

/-- Per-eigenvalue falling rule: the signed determinant sums of any commuting Penrose
partner invert the falling factorial whenever that single eigenvalue is a unit.
Strengthens `fallingFact_smul_vecMul_detVec`; complementary to the exact vanishing
`vecMul_detVec_eq_zero` when the falling factorial is zero.
Blueprint: `thm:orth_falling_rule_eigen`. -/
theorem fallingFact_smul_vecMul_detVec_of_partner {N : k}
    {W : Matrix (Pairing n) (Pairing n) k}
    (h : IsCommPenrosePartner (orthGram k n N) W)
    (hu : IsUnit (fallingFact k n N)) :
    fallingFact k n N • Matrix.vecMul (detVec k) W = detVec k :=
  h.smul_vecMul_eq_of_vecMul_eq_smul
    (by rw [orthGram_vecMul_eq, orthGram_mulVec_detVec]) hu

end Weingarten
