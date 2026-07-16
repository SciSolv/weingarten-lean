/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.OrthogonalGram

/-!
# The symplectic Gram: crossing-sign factorization and the role swap

Blueprint: `def:j_form`, `def:delta_contr`, `def:symp_gram_contr`,
`def:symp_gram_closed`, `lem:trace_j_pow`, `thm:crossing_sign`,
`cor:symp_conjugation`, `def:eps_det_vector`, `def:even_falling`,
`def:rising_shift`, `thm:symp_eps_ones_absorb`, `thm:symp_eps_det_absorb`,
`thm:symp_ker_witness`, `thm:symp_not_unit`, `thm:symp_vanish_below`,
`thm:symp_even_falling_rule`, `thm:symp_rising_shift_rule`,
`thm:symp_even_falling_rule_eigen`, `thm:symp_rising_shift_rule_eigen`.

The symplectic Gram of canonical `J`-contractions factorizes as
`ε(p) ε(q) (-1)^n (-2M)^loops` with `ε` the crossing parity
(`thm:crossing_sign` — the informal argument is recorded in the blueprint's
symplectic chapter; suites PS1–PS6). Conjugating the orthogonal absorption
identities — polynomial in the parameter, hence valid at `-2M` — yields the
ε-twisted absorptions with the roles swapped: the ε vector carries the
even-falling factorial `(2M)(2M-2)⋯(2M-2n+2)` (vanishing for `M < n`, the
kernel witness), and the ε-twisted determinant vector carries the shifted
rising factorial `(2M)(2M+1)⋯(2M+n-1)` (never vanishing for `M ≥ 1`).

Provenance: the PRIMARY reference for the ε-twisted symplectic Weingarten
calculus and the two-argument Gram is Matsumoto arXiv:1301.5401 (Thm 2.4 /
eq. (2.15)); Collins–Śniady arXiv:math-ph/0402073 §6 treats the symplectic
case via `d ↦ −d` in their convention; a recent independent treatment is
Coulter–Do arXiv:2506.04002. The blueprint carries the full citation record.
-/

namespace Weingarten

open Pairing

/-- The standard symplectic form on `Fin (2 * M)`, integer entries:
`J x y = 1` if `y = x + M`, `-1` if `x = y + M`, `0` otherwise.
Blueprint: `def:j_form`. -/
def Jform (M : ℕ) : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ :=
  fun x y =>
    if (y : ℕ) = (x : ℕ) + M then 1
    else if (x : ℕ) = (y : ℕ) + M then -1
    else 0

/-- The canonical `J`-contraction `Δ′` of a pairing along an index function:
the product of `J` entries over the canonical chords `(a, p a)` with
`a < p a`. Well-defined without any word choice. Blueprint: `def:delta_contr`. -/
def deltaContr (M : ℕ) {n : ℕ} (p : Pairing n)
    (i : Fin (2 * n) → Fin (2 * M)) : ℤ :=
  ∏ a ∈ Finset.univ.filter (fun a => a < p.1 a), Jform M (i a) (i (p.1 a))

/-- The symplectic Gram in contraction form. Blueprint: `def:symp_gram_contr`. -/
def sympGramContr (M n : ℕ) : Matrix (Pairing n) (Pairing n) ℤ :=
  fun p q => ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p i * deltaContr M q i

/-- The symplectic Gram in closed form: `ε(p) ε(q) (-1)^n (-2M)^loops`.
Blueprint: `def:symp_gram_closed`. -/
def sympGramClosed (k : Type*) [CommRing k] (M n : ℕ) :
    Matrix (Pairing n) (Pairing n) k :=
  fun p q => epsVec k p * epsVec k q * (-1) ^ n * (-(2 * (M : k))) ^ p.loops q

/-- `loops` is symmetric (conjugacy of `p*q` and `q*p` by the involution `p`). -/
theorem loops_symm {n : ℕ} (p q : Pairing n) : p.loops q = q.loops p := by
  show cycleCount (2 * n) (p.1 * q.1) / 2 = cycleCount (2 * n) (q.1 * p.1) / 2
  have hp : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_right p.2.1
  have key : q.1 * p.1 = p.1 * (p.1 * q.1) * p.1⁻¹ := by rw [hp, ← mul_assoc, p.2.1, one_mul]
  rw [key, cycleCount_conj]

/-- `ε` is a sign: its square is `1`. -/
theorem epsVec_sq {k : Type*} [CommRing k] {n : ℕ} (p : Pairing n) :
    epsVec k p * epsVec k p = 1 := by
  show ((epsSign p : ℤ) : k) * ((epsSign p : ℤ) : k) = 1
  rw [epsSign, ← Int.cast_mul, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The symplectic Gram is symmetric. -/
theorem sympGramClosed_symm {k : Type*} [CommRing k] {M n : ℕ} (p q : Pairing n) :
    sympGramClosed k M n p q = sympGramClosed k M n q p := by
  unfold sympGramClosed
  rw [loops_symm p q]; ring

/-- Symmetry as a `vecMul`/`mulVec` identity. -/
theorem sympGramClosed_vecMul_eq {k : Type*} [CommRing k] {M n : ℕ} (v : Pairing n → k) :
    Matrix.vecMul v (sympGramClosed k M n) = (sympGramClosed k M n).mulVec v := by
  funext p
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun q _ => by rw [sympGramClosed_symm q p]; ring)

/-- Matrix-level conjugation form: `Ĝ^Sp = D_ε · ((-1)^n • G^O(-2M)) · D_ε`. -/
theorem sympGramClosed_factor {k : Type*} [CommRing k] (M n : ℕ) :
    sympGramClosed k M n
      = Matrix.diagonal (epsVec k) * (((-1 : k) ^ n) • orthGram k n (-(2 * (M : k))))
        * Matrix.diagonal (epsVec k) := by
  ext p q
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  unfold sympGramClosed orthGram
  ring

/-- `D_ε · ε = 1`. -/
theorem diag_mulVec_epsVec {k : Type*} [CommRing k] {n : ℕ} :
    (Matrix.diagonal (epsVec k)).mulVec (epsVec (n := n) k) = 1 := by
  funext p; rw [Matrix.mulVec_diagonal]; exact epsVec_sq p

/-- `D_ε · 1 = ε`. -/
theorem diag_mulVec_one {k : Type*} [CommRing k] {n : ℕ} :
    (Matrix.diagonal (epsVec k)).mulVec (1 : Pairing n → k) = epsVec k := by
  funext p; rw [Matrix.mulVec_diagonal]; simp

/-- `J² = -1`: the standard symplectic form squares to minus the identity. For each row
`x`, exactly one column has `J x · ≠ 0` — the half-swap partner (`x+M` if `x<M`, else
`x-M`) — and chasing the two factors gives `-δ`. -/
theorem Jform_sq (M : ℕ) :
    Jform M ^ 2 = (-1 : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ) := by
  ext x z
  have hrhs : (-1 : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ) x z
      = if x = z then -1 else 0 := by
    rw [Matrix.neg_apply, Matrix.one_apply]; split <;> simp
  rw [hrhs, pow_two, Matrix.mul_apply]
  have hx2 : (x : ℕ) < 2 * M := x.isLt
  rcases lt_or_ge (x : ℕ) M with hx | hx
  · have hb : (x : ℕ) + M < 2 * M := by omega
    have hv : ((⟨(x : ℕ) + M, hb⟩ : Fin (2 * M)) : ℕ) = (x : ℕ) + M := rfl
    rw [Finset.sum_eq_single (⟨(x : ℕ) + M, hb⟩ : Fin (2 * M))]
    · have h1 : Jform M x ⟨(x : ℕ) + M, hb⟩ = 1 := by
        unfold Jform; rw [if_pos (by omega)]
      have h2 : Jform M ⟨(x : ℕ) + M, hb⟩ z = if x = z then -1 else 0 := by
        unfold Jform
        by_cases hz : x = z
        · subst hz; rw [if_neg (by omega), if_pos (by omega), if_pos rfl]
        · have hzv : (z : ℕ) ≠ (x : ℕ) := fun h => hz (Fin.ext h.symm)
          rw [if_neg (by omega), if_neg (by omega), if_neg hz]
      rw [h1, one_mul, h2]
    · intro y _ hy
      have hzero : Jform M x y = 0 := by
        unfold Jform
        rw [if_neg (fun hc => hy (Fin.ext hc)), if_neg (by omega)]
      rw [hzero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hb : (x : ℕ) - M < 2 * M := by omega
    have hv : ((⟨(x : ℕ) - M, hb⟩ : Fin (2 * M)) : ℕ) = (x : ℕ) - M := rfl
    rw [Finset.sum_eq_single (⟨(x : ℕ) - M, hb⟩ : Fin (2 * M))]
    · have h1 : Jform M x ⟨(x : ℕ) - M, hb⟩ = -1 := by
        unfold Jform; rw [if_neg (by omega), if_pos (by omega)]
      have h2 : Jform M ⟨(x : ℕ) - M, hb⟩ z = if x = z then 1 else 0 := by
        unfold Jform
        by_cases hz : x = z
        · subst hz; rw [if_pos (by omega), if_pos rfl]
        · have hzv : (z : ℕ) ≠ (x : ℕ) := fun h => hz (Fin.ext h.symm)
          rw [if_neg (by omega), if_neg (by omega), if_neg hz]
      rw [h1, h2, mul_ite, mul_one, mul_zero]
    · intro y _ hy
      have hzero : Jform M x y = 0 := by
        unfold Jform
        rw [if_neg (by omega), if_neg (fun hc => hy (Fin.ext (by omega)))]
      rw [hzero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- `J ^ 2 = -1` gives the loop trace `tr (J ^ (2m)) = (-1)^m · 2M`.
Blueprint: `lem:trace_j_pow`. -/
theorem trace_Jform_pow (M m : ℕ) :
    Matrix.trace ((Jform M) ^ (2 * m)) = (-1) ^ m * (2 * M : ℤ) := by
  have hpow : (Jform M ^ 2) ^ m
      = ((-1 : ℤ) ^ m) • (1 : Matrix (Fin (2 * M)) (Fin (2 * M)) ℤ) := by
    rw [Jform_sq]
    induction m with
    | zero => rw [pow_zero, pow_zero, one_smul]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ, mul_neg_one, mul_comm ((-1 : ℤ) ^ k) (-1), mul_smul,
        neg_one_smul]
  rw [pow_mul, hpow, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast; ring

/-- `J y x = -J x y` (antisymmetry of the symplectic form). -/
theorem Jform_antisymm (M : ℕ) (x y : Fin (2 * M)) : Jform M y x = - Jform M x y := by
  show (if (x : ℕ) = (y : ℕ) + M then (1 : ℤ) else if (y : ℕ) = (x : ℕ) + M then -1 else 0)
     = -(if (y : ℕ) = (x : ℕ) + M then (1 : ℤ) else if (x : ℕ) = (y : ℕ) + M then -1 else 0)
  by_cases h1 : (x : ℕ) = (y : ℕ) + M
  · rw [if_pos h1, if_neg (by omega), if_pos h1]; norm_num
  · by_cases h2 : (y : ℕ) = (x : ℕ) + M
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]; norm_num

/-- `Δ′_p` as a product of `J`-entries over the ordered left endpoints (the canonical
chords `(a_k, p a_k)`). -/
theorem deltaContr_eq_prod_leftEnd (M : ℕ) {n : ℕ} (p : Pairing n)
    (i : Fin (2 * n) → Fin (2 * M)) :
    deltaContr M p i
      = ∏ k : Fin n, Jform M (i (leftEndEmb p k)) (i (p.1 (leftEndEmb p k))) := by
  unfold deltaContr; symm
  apply Finset.prod_bij (fun k _ => leftEndEmb p k)
  · intro k _; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, leftEndEmb_lt p k⟩
  · intro k _ k' _ h; exact (leftEndEmb p).injective h
  · intro a ha; rw [Finset.mem_filter] at ha
    obtain ⟨k, hk⟩ := exists_leftEndEmb p ha.2; exact ⟨k, Finset.mem_univ _, hk⟩
  · intro k _; rfl

/-- The canonical-gauge contraction `Φ_p(i) = sgn(w_p) ∏ J` (Pfaffian normalization). -/
noncomputable def PhiCanon (M : ℕ) {n : ℕ} (p : Pairing n)
    (i : Fin (2 * n) → Fin (2 * M)) : ℤ :=
  ((Equiv.Perm.sign (canonicalWord p) : ℤ)) *
    ∏ k : Fin n, Jform M (i (leftEndEmb p k)) (i (p.1 (leftEndEmb p k)))

/-- Pfaffian-sign bridge (Lemma 1): `Δ′_p = ε(p) · Φ_p`, via `sign_canonicalWord`. -/
theorem deltaContr_eq_eps_PhiCanon (M : ℕ) {n : ℕ} (p : Pairing n)
    (i : Fin (2 * n) → Fin (2 * M)) :
    deltaContr M p i = epsVec ℤ p * PhiCanon M p i := by
  rw [PhiCanon, sign_canonicalWord]
  show deltaContr M p i = epsVec ℤ p * ((-1) ^ p.crossings * _)
  rw [show epsVec ℤ p = ((-1 : ℤ)) ^ p.crossings from rfl,
     ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact deltaContr_eq_prod_leftEnd M p i

/-! ### Transfer-matrix / closed-walk trace identity (Lemma 2, general form)

The single-loop contraction `∑_x ∏_a A (x a) (x (a+1))` over a cyclic index `x : Fin (m+1) → V`
equals `tr (A ^ (m+1))`. This is the analytic core of the loop trace (`lem:trace_j_pow`),
proved here in full generality (any square matrix over any commutative ring) by the standard
walk-counting induction. Specialized to `A = Jform M` and length `2m` it gives the per-loop
value `(-1)^m · 2M` via `trace_Jform_pow`. -/

section TransferMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

omit [Fintype V] [DecidableEq V] in
/-- Peel the first edge of a `cons`-built walk product. -/
theorem cons_prod_split (m : ℕ) (A : Matrix V V R) (v : V) (rest : Fin (m+1) → V) :
    (∏ a : Fin (m+1), A ((Fin.cons v rest : Fin (m+2)→V) a.castSucc)
        ((Fin.cons v rest : Fin (m+2)→V) a.succ))
      = A v (rest 0) * ∏ a : Fin m, A (rest a.castSucc) (rest a.succ) := by
  rw [Fin.prod_univ_succ]
  have h0 : A ((Fin.cons v rest : Fin (m+2)→V) (0:Fin (m+1)).castSucc)
      ((Fin.cons v rest : Fin (m+2)→V) (0:Fin (m+1)).succ) = A v (rest 0) := by
    simp [Fin.cons_zero]
  rw [h0]; congr 1

/-- Open-walk lemma: `(A ^ L) i k` is the sum over length-`L` walks from `i` to `k` of the
product of edge weights. -/
theorem matrix_pow_apply_eq_walk_sum (A : Matrix V V R) (L : ℕ) (i k : V) :
    (A ^ L) i k = ∑ w : Fin (L+1) → V,
        (if w 0 = i then (1:R) else 0) * (if w (Fin.last L) = k then 1 else 0)
          * ∏ a : Fin L, A (w a.castSucc) (w a.succ) := by
  induction L generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    rw [show (∑ w : Fin 1 → V,
          (if w 0 = i then (1:R) else 0) * (if w (Fin.last 0) = k then 1 else 0)
            * ∏ a : Fin 0, A (w a.castSucc) (w a.succ))
        = ∑ v : V, (if v = i then (1:R) else 0) * (if v = k then 1 else 0) * 1 from ?_]
    · simp only [mul_one]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]; by_cases h : i = k <;> simp [h]
      · intro v _ hv; simp [hv]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) V).symm]
      apply Finset.sum_congr rfl; intro v _
      simp only [Equiv.funUnique_symm_apply, Fin.last]
      rw [Finset.prod_eq_one (by intro a _; exact absurd a.isLt (by omega))]
      congr 1
  | succ m ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => V))]
    simp only [Fin.consEquiv_apply]
    rw [Fintype.sum_prod_type]
    have hstep : ∀ (v : V) (rest : Fin (m+1) → V),
        (if (Fin.cons v rest : Fin (m+2)→V) 0 = i then (1:R) else 0)
          * (if (Fin.cons v rest : Fin (m+2)→V) (Fin.last (m+1)) = k then 1 else 0)
          * ∏ a : Fin (m+1), A ((Fin.cons v rest : Fin (m+2)→V) a.castSucc)
              ((Fin.cons v rest : Fin (m+2)→V) a.succ)
        = (if v = i then (1:R) else 0) * ((if rest (Fin.last m) = k then 1 else 0)
          * (A v (rest 0) * ∏ a : Fin m, A (rest a.castSucc) (rest a.succ))) := by
      intro v rest
      rw [Fin.cons_zero, show (Fin.last (m+1)) = (Fin.last m).succ from rfl, Fin.cons_succ,
        cons_prod_split]
      ring
    simp_rw [hstep]
    rw [Finset.sum_eq_single i]
    rotate_left
    · intro v _ hv; rw [if_neg hv]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
    simp only [↓reduceIte, one_mul]
    rw [pow_succ', Matrix.mul_apply]
    have hih : ∀ j, (A^m) j k = ∑ w : Fin (m+1) → V,
        (if w 0 = j then (1:R) else 0) * (if w (Fin.last m) = k then 1 else 0)
          * ∏ a : Fin m, A (w a.castSucc) (w a.succ) := fun j => ih j
    simp_rw [hih, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro rest _
    rw [Finset.sum_eq_single (rest 0)]
    · rw [if_pos rfl, one_mul]; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
    · intro h; exact absurd (Finset.mem_univ (rest 0)) h

/-- The trace of a power is the sum over closed walks (open walks with matched endpoints). -/
theorem trace_pow_eq_closed_walk (A : Matrix V V R) (L : ℕ) :
    Matrix.trace (A ^ L)
      = ∑ w : Fin (L+1) → V, (if w (Fin.last L) = w 0 then (1:R) else 0)
          * ∏ a : Fin L, A (w a.castSucc) (w a.succ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [matrix_pow_apply_eq_walk_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.sum_eq_single (w 0)]
  · rw [if_pos rfl, one_mul]
  · intro v _ hv; rw [if_neg (Ne.symm hv)]; ring
  · intro h; exact absurd (Finset.mem_univ (w 0)) h

omit [Fintype V] [DecidableEq V] in
/-- The successor of `a : Fin (m+1)` in a `snoc`-closed walk is the cyclic successor. -/
theorem snoc_succ_cyclic (m : ℕ) (x : Fin (m+1) → V) (a : Fin (m+1)) :
    (Fin.snoc x (x 0) : Fin (m+2) → V) a.succ = x (a + 1) := by
  rcases eq_or_ne a (Fin.last m) with hlast | hlast
  · subst hlast
    rw [show (Fin.last m).succ = Fin.last (m+1) from rfl, Fin.snoc_last]
    congr 1; simp [Fin.last_add_one]
  · have hcast : a.succ = (a + 1).castSucc := by
      have h : a < Fin.last m := lt_of_le_of_ne (Fin.le_last a) hlast
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc, Fin.val_add_one_of_lt h]
    rw [hcast, Fin.snoc_castSucc]

omit [Fintype V] [DecidableEq V] in
/-- The closed-walk product over `snoc x (x 0)` is the cyclic product over `x`. -/
theorem snoc_walk_prod (A : Matrix V V R) (m : ℕ) (x : Fin (m+1) → V) :
    (∏ a : Fin (m+1), A ((Fin.snoc x (x 0) : Fin (m+2)→V) a.castSucc)
        ((Fin.snoc x (x 0) : Fin (m+2)→V) a.succ))
      = ∏ a : Fin (m+1), A (x a) (x (a+1)) := by
  apply Finset.prod_congr rfl; intro a _
  rw [Fin.snoc_castSucc, snoc_succ_cyclic]

/-- **Transfer-matrix / closed-walk trace identity** (`lem:trace_j_pow`, general form): for a
loop of length `L = m+1 ≥ 1`, the cyclic index contraction equals `tr (A ^ (m+1))`. -/
theorem trace_pow_eq_cyclic (A : Matrix V V R) (m : ℕ) :
    Matrix.trace (A ^ (m+1))
      = ∑ x : Fin (m+1) → V, ∏ a : Fin (m+1), A (x a) (x (a+1)) := by
  rw [trace_pow_eq_closed_walk]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ => V))]
  rw [Fintype.sum_prod_type]
  simp only [show ∀ (vlast : V) (x : Fin (m+1)→V),
      (Fin.snocEquiv (fun _ => V) (vlast, x)) = (Fin.snoc x vlast : Fin (m+2) → V)
        from fun _ _ => rfl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_eq_single (x 0)]
  · have hlast : (Fin.snoc x (x 0) : Fin (m+2)→V) (Fin.last (m+1)) = x 0 := by
      simp only [Fin.snoc_last]
    have hzero : (Fin.snoc x (x 0) : Fin (m+2)→V) 0 = x 0 := by
      rw [show (0 : Fin (m+2)) = (0 : Fin (m+1)).castSucc from rfl, Fin.snoc_castSucc]
    rw [hlast, hzero, if_pos rfl, one_mul, snoc_walk_prod]
  · intro vlast _ hv
    have hlast : (Fin.snoc x vlast : Fin (m+2)→V) (Fin.last (m+1)) = vlast := by
      simp only [Fin.snoc_last]
    have hzero : (Fin.snoc x vlast : Fin (m+2)→V) 0 = x 0 := by
      rw [show (0 : Fin (m+2)) = (0 : Fin (m+1)).castSucc from rfl, Fin.snoc_castSucc]
    rw [hlast, hzero, if_neg hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ (x 0)) h

end TransferMatrix

/-- **Per-loop value** (Lemma 2 for the symplectic form): the cyclic `J`-contraction around a
loop of `2m ≥ 2` vertices is `tr (Jform M ^ (2m)) = (-1)^m · 2M`. Combines the general
transfer-matrix identity `trace_pow_eq_cyclic` with `trace_Jform_pow`. -/
theorem loop_Jform_sum (M m : ℕ) :
    (∑ x : Fin (2*m + 1) → Fin (2 * M),
        ∏ a : Fin (2*m + 1), Jform M (x a) (x (a + 1)))
      = Matrix.trace (Jform M ^ (2*m + 1)) :=
  (trace_pow_eq_cyclic (Jform M) (2*m)).symm

/-- The cyclic `J`-contraction around a loop of even length `2m+2` is `(-1)^(m+1) · 2M`.
(Phrased with the loop length as `(2m+1)+1` to keep the `Fin` dimension fixed; `2m+2 = 2(m+1)`.) -/
theorem loop_Jform_sum_even (M m : ℕ) :
    (∑ x : Fin ((2*m+1) + 1) → Fin (2 * M),
        ∏ a : Fin ((2*m+1) + 1), Jform M (x a) (x (a + 1)))
      = (-1) ^ (m+1) * (2 * M : ℤ) := by
  rw [← trace_pow_eq_cyclic (Jform M) (2*m + 1),
    show (2*m + 1) + 1 = 2 * (m+1) from by ring, trace_Jform_pow]

/-! ### Orbit-factorization functional (general-purpose core for `PhiCanon_sum`)

The index-sum `∑_{i:α→V} ∏_a A (i a) (i (σ a))` is the analytic engine behind the loop
factorization: it factors multiplicatively over any `σ`-invariant partition of the index set
(`GLval_split`), is invariant under transport of the underlying type (`GLval_permCongr`), and
on the standard `+1` rotation of `Fin (m+1)` it is the closed walk trace `tr (A^(m+1))`
(`GLval_rot`, via the in-file `trace_pow_eq_cyclic`). Specialized to `A = Jform M` on the even
loops of `p ∪ q` this yields the per-loop value `(-1)^m·2M`. -/

section OrbitFactor

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

open Equiv Equiv.Perm

/-- The orbit-factorization functional `∑_{i:α→V} ∏_a A (i a) (i (σ a))`. -/
noncomputable def GLval {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix V V R) (σ : Equiv.Perm α) : R :=
  ∑ i : α → V, ∏ a : α, A (i a) (i (σ a))

omit [DecidableEq V] in
/-- Multiplicativity over a `σ`-invariant predicate split: the functional factors into the
contributions of `{p}` and `{¬p}` (each a union of `σ`-orbits). -/
theorem GLval_split {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix V V R) (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) :
    GLval A σ = GLval A (σ.subtypePerm hp)
      * GLval A (σ.subtypePerm (p := fun x => ¬ p x) (fun x => not_congr (hp x))) := by
  unfold GLval
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro g _
  apply Finset.sum_congr rfl; intro h _
  rw [← Fintype.prod_subtype_mul_prod_subtype p
       (fun a => A ((Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm (g, h) a)
                   ((Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm (g, h) (σ a)))]
  congr 1
  · apply Finset.prod_congr rfl; intro a _
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [dif_pos a.2, dif_pos ((hp a).mpr a.2)]; rfl
  · apply Finset.prod_congr rfl; intro a _
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
    rw [dif_neg a.2, dif_neg (fun hc => a.2 ((hp a).mp hc))]; rfl

omit [DecidableEq V] in
/-- Transport invariance: the functional only depends on the permutation up to relabelling. -/
theorem GLval_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix V V R) (e : α ≃ β) (σ : Equiv.Perm α) :
    GLval A (e.permCongr σ) = GLval A σ := by
  unfold GLval
  rw [← Equiv.sum_comp (Equiv.arrowCongr e (Equiv.refl V)).symm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl; intro a _
  simp only [Equiv.permCongr_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.symm_symm]

/-- On the standard `+1` rotation of `Fin (m+1)` the functional is the closed-walk trace. -/
theorem GLval_rot (A : Matrix V V R) (m : ℕ) :
    GLval A (Equiv.addRight (1 : Fin (m+1))) = Matrix.trace (A ^ (m+1)) := by
  unfold GLval
  rw [trace_pow_eq_cyclic]
  rfl

end OrbitFactor

/-- Abstract orbit/fiber factorization: the index sum splits as an independent choice on
each block. The engine for factoring the index sum over the loop partition. -/
theorem sum_prod_fiber_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ b, Fintype (α b)]
    [∀ b, DecidableEq (α b)] {W : Type*} [Fintype W] {R : Type*} [CommRing R]
    (g : ∀ b, (α b → W) → R) :
    (∑ f : (Σ b, α b) → W, ∏ b : ι, g b (fun a => f ⟨b, a⟩))
      = ∏ b : ι, ∑ h : α b → W, g b h := by
  rw [Finset.prod_univ_sum]
  rw [← Equiv.sum_comp (Equiv.piCurry (fun (b : ι) (_ : α b) => W)).symm
        (fun f => ∏ b : ι, g b (fun a => f ⟨b, a⟩))]
  refine Finset.sum_congr rfl (fun x _ => Finset.prod_congr rfl (fun b _ => rfl))

/-- **Per-vertex transfer collapse.** Summing a single shared index out of two `J`-factors
meeting at a vertex collapses to `(J²)(u,v) = -δ(u,v)`: `∑_w J u w · J w v = -[u=v]`. This is
the analytic merge step — `Jform_sq` (`J² = -1`) read through `Matrix.mul_apply`. It is the
local engine of the loop factorization: at every internal (summed-out) vertex of an
alternating loop the two incident chords fuse. -/
theorem Jform_vertex_collapse (M : ℕ) (u v : Fin (2 * M)) :
    (∑ w : Fin (2 * M), Jform M u w * Jform M w v) = (if u = v then (-1 : ℤ) else 0) := by
  rw [← Matrix.mul_apply, ← pow_two, Jform_sq, Matrix.neg_apply, Matrix.one_apply]
  split <;> simp

/-! ### Cycle-orbit enumeration and the single-cycle `GLval` value (toward `deltaContr_gram_closed`) -/

section CycleOrbit

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
variable {α : Type*} [Fintype α] [DecidableEq α]

open Equiv Equiv.Perm Function

omit [DecidableEq α] in
/-- For `x` moved by a cycle `σ`, the minimal period of `x` equals the order of `σ`. -/
theorem minimalPeriod_eq_orderOf_of_cycle (σ : Perm α) (hc : σ.IsCycle) (x : α)
    (hx : σ x ≠ x) :
    Function.minimalPeriod (⇑σ) x = orderOf σ := by
  have hper_mp : (σ ^ minimalPeriod (⇑σ) x) x = x := by
    have := isPeriodicPt_minimalPeriod (⇑σ) x
    rwa [IsPeriodicPt, IsFixedPt, Equiv.Perm.iterate_eq_pow] at this
  have hdvd1 : orderOf σ ∣ minimalPeriod (⇑σ) x := by
    rw [orderOf_dvd_iff_pow_eq_one]; exact hc.pow_eq_one_iff.mpr ⟨x, hx, hper_mp⟩
  have hdvd2 : minimalPeriod (⇑σ) x ∣ orderOf σ := by
    apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl
  exact Nat.dvd_antisymm hdvd2 hdvd1

/-- The minimal period of a point under `σ` equals the size of its `σ`-orbit. -/
theorem minimalPeriod_eq_cycleOf_card (σ : Perm α) (x : α) (hx : σ x ≠ x) :
    Function.minimalPeriod (⇑σ) x = (σ.cycleOf x).support.card := by
  have hccyc : (σ.cycleOf x).IsCycle := isCycle_cycleOf σ hx
  have hcx : (σ.cycleOf x) x ≠ x := by rw [cycleOf_apply_self]; exact hx
  have hsame : Function.minimalPeriod (⇑σ) x = Function.minimalPeriod (⇑(σ.cycleOf x)) x := by
    apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    constructor <;> intro h <;>
      · rw [IsPeriodicPt, IsFixedPt, iterate_eq_pow] at h ⊢
        rw [cycleOf_pow_apply_self] at *
        assumption
  rw [hsame, minimalPeriod_eq_orderOf_of_cycle _ hccyc x hcx, hccyc.orderOf]

theorem orbitMap_inj (σ : Perm α) (hc : σ.IsCycle) (hfull : σ.support = Finset.univ)
    (N : ℕ) (hcard : Fintype.card α = N + 1) (x0 : α) :
    Function.Injective (fun k : Fin (N+1) => (σ ^ (k : ℕ)) x0) := by
  have hx0 : σ x0 ≠ x0 := by rw [← Equiv.Perm.mem_support, hfull]; exact Finset.mem_univ x0
  have hmp : Function.minimalPeriod (⇑σ) x0 = N + 1 := by
    rw [minimalPeriod_eq_orderOf_of_cycle σ hc x0 hx0, hc.orderOf, hfull, Finset.card_univ, hcard]
  intro k1 k2 h
  simp only at h
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := ⇑σ) (x := x0)
  rw [hmp] at hinj
  apply Fin.ext
  exact hinj k1.isLt k2.isLt (by simp only [Equiv.Perm.iterate_eq_pow]; exact h)

/-- The orbit enumeration `k ↦ σ^k x0 : Fin (N+1) ≃ α` for a full-support `(N+1)`-cycle `σ`. -/
noncomputable def orbitEquiv (σ : Perm α) (hc : σ.IsCycle) (hfull : σ.support = Finset.univ)
    (N : ℕ) (hcard : Fintype.card α = N + 1) (x0 : α) : Fin (N+1) ≃ α :=
  Equiv.ofBijective (fun k : Fin (N+1) => (σ ^ (k : ℕ)) x0)
    (by rw [Fintype.bijective_iff_injective_and_card]
        exact ⟨orbitMap_inj σ hc hfull N hcard x0, by rw [Fintype.card_fin, hcard]⟩)

theorem orbitEquiv_apply (σ : Perm α) (hc : σ.IsCycle) (hfull : σ.support = Finset.univ)
    (N : ℕ) (hcard : Fintype.card α = N + 1) (x0 : α) (k : Fin (N+1)) :
    orbitEquiv σ hc hfull N hcard x0 k = (σ ^ (k:ℕ)) x0 := rfl

theorem orbitEquiv_rotation (σ : Perm α) (hc : σ.IsCycle) (hfull : σ.support = Finset.univ)
    (N : ℕ) (hcard : Fintype.card α = N + 1) (x0 : α) (k : Fin (N+1)) :
    σ (orbitEquiv σ hc hfull N hcard x0 k) = orbitEquiv σ hc hfull N hcard x0 (k + 1) := by
  rw [orbitEquiv_apply, orbitEquiv_apply]
  have hord : orderOf σ = N + 1 := by rw [hc.orderOf, hfull, Finset.card_univ, hcard]
  rw [← Equiv.Perm.mul_apply, ← pow_succ']
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp k.isLt) with hk | hk
  · have hkval : (k:ℕ) = N := hk
    have hklast : k = Fin.last N := Fin.ext (by rw [hkval]; rfl)
    have hk1 : ((k + 1 : Fin (N+1)) : ℕ) = 0 := by rw [hklast, Fin.last_add_one]; rfl
    rw [hk1, pow_zero, Equiv.Perm.one_apply]
    rw [hkval, show N + 1 = orderOf σ from hord.symm, pow_orderOf_eq_one, Equiv.Perm.one_apply]
  · rw [Fin.val_add_one_of_lt hk]

theorem orbitEquiv_permCongr (σ : Perm α) (hc : σ.IsCycle) (hfull : σ.support = Finset.univ)
    (N : ℕ) (hcard : Fintype.card α = N + 1) (x0 : α) :
    (orbitEquiv σ hc hfull N hcard x0).permCongr (Equiv.addRight 1) = σ := by
  ext y
  rw [Equiv.permCongr_apply]
  set e := orbitEquiv σ hc hfull N hcard x0
  show e (Equiv.addRight 1 (e.symm y)) = σ y
  rw [show Equiv.addRight (1:Fin (N+1)) (e.symm y) = e.symm y + 1 from rfl]
  rw [← orbitEquiv_rotation σ hc hfull N hcard x0 (e.symm y), Equiv.apply_symm_apply]

/-- **Single full-support cycle value**: for `σ` an `(N+1)`-cycle on `α` with full support,
`GLval A σ = trace (A ^ (N+1))`. -/
theorem GLval_fullCycle (A : Matrix V V R) (σ : Perm α) (hc : σ.IsCycle)
    (hfull : σ.support = Finset.univ) (N : ℕ) (hcard : Fintype.card α = N + 1) :
    GLval A σ = Matrix.trace (A ^ (N+1)) := by
  obtain ⟨x0, -, -⟩ := id hc
  rw [← orbitEquiv_permCongr σ hc hfull N hcard x0, GLval_permCongr, GLval_rot]

/-- On the support of a cycle factor `c` of `σ`, the permutation `σ` agrees with `c`. -/
theorem sigma_eq_c_on_support (σ c : Perm α) (hc : c ∈ σ.cycleFactorsFinset)
    (x : α) (hx : x ∈ c.support) : σ x = c x :=
  ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm

/-- The restriction of `σ` to a cycle factor's support has full support on the subtype. -/
theorem subtypePerm_support_full (σ c : Perm α) (hc : c ∈ σ.cycleFactorsFinset)
    (h : ∀ x, σ x ∈ c.support ↔ x ∈ c.support) :
    (σ.subtypePerm h).support = Finset.univ := by
  rw [Equiv.Perm.support_subtypePerm]
  ext ⟨x, hx⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rw [sigma_eq_c_on_support σ c hc x hx]
  exact (Equiv.Perm.mem_support.mp hx)

/-- The restriction of `σ` to a cycle factor's support is a single cycle on the subtype. -/
theorem subtypePerm_isCycle (σ c : Perm α) (hc : c ∈ σ.cycleFactorsFinset)
    (h : ∀ x, σ x ∈ c.support ↔ x ∈ c.support) :
    (σ.subtypePerm h).IsCycle := by
  have hccyc : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨x0, hx0, hx0all⟩ := hccyc
  have hx0mem : x0 ∈ c.support := Equiv.Perm.mem_support.mpr hx0
  refine ⟨⟨x0, hx0mem⟩, ?_, ?_⟩
  · rw [Equiv.Perm.subtypePerm_apply]
    simp only [ne_eq, Subtype.mk.injEq]
    rw [sigma_eq_c_on_support σ c hc x0 hx0mem]; exact hx0
  · rintro ⟨y, hy⟩ hyne
    rw [Equiv.Perm.subtypePerm_apply] at hyne
    simp only [ne_eq, Subtype.mk.injEq] at hyne
    have hysupp : y ∈ c.support := hy
    have hcy : c y ≠ y := by rw [← sigma_eq_c_on_support σ c hc y hysupp]; exact hyne
    have hsc : c.SameCycle x0 y := hx0all hcy
    obtain ⟨j, hj⟩ := hsc
    refine ⟨j, ?_⟩
    rw [Equiv.Perm.subtypePerm_zpow]
    apply Subtype.ext
    rw [Equiv.Perm.subtypePerm_apply]
    show (σ ^ j) x0 = y
    rw [← hj]
    have hcc : c = σ.cycleOf x0 := cycle_is_cycleOf hx0mem hc
    rw [hcc, cycleOf_zpow_apply_self]

end CycleOrbit

/-- Base case of the geometric index-sum identity: at `n = 0` there is a single index
function (the empty one), every canonical `J`-contraction is the empty product `1`, the
ε factors are `1`, and `loops = 0`. -/
theorem deltaContr_gram_closed_zero (M : ℕ) (p q : Pairing 0) :
    ∑ i : Fin (2 * 0) → Fin (2 * M), deltaContr M p i * deltaContr M q i
      = epsVec ℤ p * epsVec ℤ q * (-1) ^ (0 : ℕ) * (-(2 * (M : ℤ))) ^ p.loops q := by
  have hdelta : ∀ (r : Pairing 0) (i : Fin (2 * 0) → Fin (2 * M)), deltaContr M r i = 1 := by
    intro r i
    rw [deltaContr_eq_prod_leftEnd,
      Finset.prod_eq_one (by intro k _; exact absurd k.isLt (by omega))]
  have heps : ∀ r : Pairing 0, epsVec ℤ r = 1 := by
    intro r
    show ((epsSign r : ℤ)) = 1
    rw [epsSign, Pairing.crossings,
      Finset.filter_eq_empty_iff.mpr (by rintro ⟨a, _⟩ _; exact absurd a.isLt (by omega))]
    simp
  have hl : p.loops q = 0 := by
    unfold Pairing.loops
    have hcc : cycleCount (2 * 0) (p.1 * q.1) = 0 :=
      Nat.le_zero.mp (by simpa using cycleCount_le 0 (p.1 * q.1))
    rw [hcc]
  simp_rw [hdelta, heps, hl]
  simp

/-- The orbit count of a single pairing is `n`: a fixed-point-free involution on `Fin (2n)`
has `n` two-cycles and no fixed points. -/
theorem cycleCount_pairing {n : ℕ} (p : Pairing n) : cycleCount (2 * n) p.1 = n := by
  rw [cycleCount_eq, pairing_cycleType]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  omega

/-- The sign of a pairing is `(-1)^n` (it is a product of `n` transpositions). -/
theorem sign_pairing {n : ℕ} (p : Pairing n) :
    (Equiv.Perm.sign p.1 : ℤ) = (-1) ^ n := by
  rw [sign_eq_neg_one_pow, cycleCount_pairing]; congr 1; omega

/-- The full cycle count of `p.1 * q.1` is even: the product of two pairings is conjugate to
its own inverse (via the involution `p`), so its sign is `1`, forcing `2n - cycleCount` — and
hence `cycleCount` — to be even. This is why `loops = cycleCount / 2` loses no information. -/
theorem cycleCount_pq_even {n : ℕ} (p q : Pairing n) :
    Even (cycleCount (2 * n) (p.1 * q.1)) := by
  have hsign : (Equiv.Perm.sign (p.1 * q.1) : ℤ) = 1 := by
    rw [map_mul, Units.val_mul, sign_pairing p, sign_pairing q, ← pow_add, ← two_mul,
      pow_mul]; norm_num
  rw [sign_eq_neg_one_pow] at hsign
  have hle : cycleCount (2 * n) (p.1 * q.1) ≤ 2 * n := cycleCount_le (2 * n) _
  have heven : Even (2 * n - cycleCount (2 * n) (p.1 * q.1)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsign; norm_num at hsign
  obtain ⟨t, ht⟩ := heven
  exact ⟨n - t, by omega⟩

/-- `2 · loops(p, q) = cycleCount(p.1 * q.1)` (the halving is exact, `cycleCount_pq_even`). -/
theorem loops_two_mul {n : ℕ} (p q : Pairing n) :
    2 * p.loops q = cycleCount (2 * n) (p.1 * q.1) := by
  unfold Pairing.loops
  obtain ⟨t, ht⟩ := cycleCount_pq_even p q
  omega

/-- The closed form splits as `sign · magnitude`, with `magnitude = (-1)^n (2M)^loops` the
product of the per-loop traces and `sign = ε(p) ε(q) (-1)^loops` the crossing-sign factor. -/
theorem sympClosed_split (M : ℕ) {n : ℕ} (p q : Pairing n) :
    epsVec ℤ p * epsVec ℤ q * (-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q
      = (epsVec ℤ p * epsVec ℤ q * (-1) ^ p.loops q)
        * ((-1) ^ n * (2 * (M : ℤ)) ^ p.loops q) := by
  rw [show (-(2 * (M : ℤ))) = (-1) * (2 * M) by ring, mul_pow, ← mul_assoc]; ring

/-! ### Merge-induction infrastructure for `deltaContr_gram_closed` -/

/-- Symmetric per-vertex collapse `∑_w J(w,u) J(w,v) = [u=v]` (dual of `Jform_vertex_collapse`). -/
theorem Jform_vertex_collapse' (M : ℕ) (u v : Fin (2 * M)) :
    (∑ w : Fin (2 * M), Jform M w u * Jform M w v) = (if u = v then (1 : ℤ) else 0) := by
  have h : ∀ w, Jform M w u * Jform M w v = -(Jform M u w * Jform M w v) := by
    intro w; rw [Jform_antisymm M u w, Jform_antisymm M v w]; ring
  simp_rw [h, Finset.sum_neg_distrib, Jform_vertex_collapse]
  split <;> simp

/-- Extract the unique `i 0`-dependent factor of `deltaContr` (the chord `(0, p 0)`). -/
theorem deltaContr_extract_zero (M n : ℕ) (p : Pairing (n+1)) (i : Fin (2*(n+1)) → Fin (2*M)) :
    deltaContr M p i
      = Jform M (i 0) (i (p.1 0))
        * ∏ a ∈ (Finset.univ.filter (fun a => a < p.1 a)).erase 0,
            Jform M (i a) (i (p.1 a)) := by
  unfold deltaContr
  have h0mem : (0 : Fin (2*(n+1))) ∈ Finset.univ.filter (fun a => a < p.1 a) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Fin.pos_of_ne_zero (p.2.2 0)⟩
  rw [← Finset.prod_erase_mul _ _ h0mem]
  ring

theorem erased_indices_ne_zero (n : ℕ) (p : Pairing (n+1)) {a : Fin (2*(n+1))}
    (ha : a ∈ (Finset.univ.filter (fun a => a < p.1 a)).erase 0) :
    a ≠ 0 ∧ p.1 a ≠ 0 := by
  rw [Finset.mem_erase, Finset.mem_filter] at ha
  obtain ⟨hane, _, halt⟩ := ha
  refine ⟨hane, ?_⟩
  intro hpa0
  rw [hpa0] at halt
  exact absurd halt (Fin.not_lt_zero a)

/-- The erased product (the part of `deltaContr` not involving vertex `0`). -/
def EP (M n : ℕ) (p : Pairing (n+1)) (i : Fin (2*(n+1)) → Fin (2*M)) : ℤ :=
  ∏ a ∈ (Finset.univ.filter (fun a => a < p.1 a)).erase 0,
      Jform M (i a) (i (p.1 a))

theorem EP_update_zero (M n : ℕ) (p : Pairing (n+1)) (i : Fin (2*(n+1)) → Fin (2*M))
    (x : Fin (2*M)) : EP M n p (Function.update i 0 x) = EP M n p i := by
  unfold EP
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨hane, hpane⟩ := erased_indices_ne_zero n p ha
  rw [Function.update_of_ne hane, Function.update_of_ne hpane]

/-- **Merge step (analytic core).** Summing the value at vertex `0` collapses the two J-factors
meeting at `0` to `[i(p 0) = i(q 0)]`, leaving the erased products. -/
theorem deltaContr_gram_collapse_update (M n : ℕ) (p q : Pairing (n+1))
    (i : Fin (2*(n+1)) → Fin (2*M)) :
    (∑ x : Fin (2*M),
        deltaContr M p (Function.update i 0 x) * deltaContr M q (Function.update i 0 x))
      = (if i (p.1 0) = i (q.1 0) then EP M n p i * EP M n q i else 0) := by
  have hb : p.1 0 ≠ 0 := p.2.2 0
  have hc : q.1 0 ≠ 0 := q.2.2 0
  have hrw : ∀ x : Fin (2*M),
      deltaContr M p (Function.update i 0 x) * deltaContr M q (Function.update i 0 x)
        = (Jform M x (i (p.1 0)) * Jform M x (i (q.1 0))) * (EP M n p i * EP M n q i) := by
    intro x
    rw [deltaContr_extract_zero M n p, deltaContr_extract_zero M n q]
    rw [Function.update_self, Function.update_of_ne hb, Function.update_of_ne hc]
    show _ = _
    rw [show (∏ a ∈ (Finset.univ.filter (fun a => a < p.1 a)).erase 0,
              Jform M (Function.update i 0 x a) (Function.update i 0 x (p.1 a)))
            = EP M n p i from EP_update_zero M n p i x]
    rw [show (∏ a ∈ (Finset.univ.filter (fun a => a < q.1 a)).erase 0,
              Jform M (Function.update i 0 x a) (Function.update i 0 x (q.1 a)))
            = EP M n q i from EP_update_zero M n q i x]
    ring
  simp_rw [hrw, ← Finset.sum_mul, Jform_vertex_collapse']
  split <;> simp

/-- Reconstruct a full index function from its values on the nonzero vertices, using the value
at `p 0` as the (irrelevant) dummy value at vertex `0`. -/
noncomputable def reLift (M n : ℕ) (p : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) : Fin (2*(n+1)) → Fin (2*M) :=
  (Equiv.funSplitAt 0 (Fin (2*M))).symm (rest ⟨p.1 0, p.2.2 0⟩, rest)

theorem reLift_ne (M n : ℕ) (p : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) {a : Fin (2*(n+1))} (ha : a ≠ 0) :
    reLift M n p rest a = rest ⟨a, ha⟩ := by
  unfold reLift
  simp [Equiv.funSplitAt, Equiv.piSplitAt, ha]

theorem reLift_zero (M n : ℕ) (p : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    reLift M n p rest 0 = rest ⟨p.1 0, p.2.2 0⟩ := by
  unfold reLift
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem funSplitAt_symm_eq_update (M n : ℕ) (p : Pairing (n+1))
    (w : Fin (2*M)) (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    (Equiv.funSplitAt 0 (Fin (2*M))).symm (w, rest)
      = Function.update (reLift M n p rest) 0 w := by
  funext a
  by_cases ha : a = 0
  · subst ha; rw [Function.update_self]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [Function.update_of_ne ha, reLift_ne M n p rest ha]
    simp [Equiv.funSplitAt, Equiv.piSplitAt, ha]

/-- The `(n+1)`-index sum after summing out vertex `0` (fully analytic, sorry-free). -/
theorem deltaContr_gram_after_collapse (M n : ℕ) (p q : Pairing (n+1)) :
    (∑ i : Fin (2*(n+1)) → Fin (2*M), deltaContr M p i * deltaContr M q i)
      = ∑ rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M),
          (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
            then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest)
            else 0) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt (0 : Fin (2*(n+1))) (Fin (2*M))).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  simp_rw [funSplitAt_symm_eq_update M n p]
  rw [deltaContr_gram_collapse_update M n p q (reLift M n p rest)]
  rw [reLift_ne M n p rest (p.2.2 0), reLift_ne M n p rest (q.2.2 0)]

/-! ### Order-preserving survivor reduction + merge-sign p-side (foundation for the residuals).
Provides `sEquiv` (order-iso `Fin (2n) ≃ survivors {≠0,≠b}`), `pPrimeO` (reduced pairing),
`crossings_split` (`p.crossings = (pPrimeO p).crossings + straddle p`), and the p-side merge sign
`epsSign_pPrimeO`/`epsSign_mul_pPrimeO`. -/
section MergeSignFoundation
open Equiv Equiv.Perm Finset

-- ## Order-preserving survivor equivalence (deletes {0,b}, b≠0), order-iso form.

/-- The survivor finset `{x : x ≠ 0 ∧ x ≠ b}` as `({0,b})ᶜ`. -/
theorem surv_compl (b : Fin (2*(n+1))) (hb : b ≠ 0) :
    (({0, b} : Finset (Fin (2*(n+1))))ᶜ).card = 2*n := by
  rw [Finset.card_compl, Finset.card_pair (Ne.symm hb), Fintype.card_fin]; omega

/-- Order-iso `Fin (2n) ≃o survivors`. -/
noncomputable def survOIso (b : Fin (2*(n+1))) (hb : b ≠ 0) :
    Fin (2*n) ≃o {x : Fin (2*(n+1)) // x ∈ (({0, b} : Finset (Fin (2*(n+1))))ᶜ)} :=
  (({0, b} : Finset (Fin (2*(n+1))))ᶜ).orderIsoOfFin (surv_compl b hb)

/-- Survivor membership rewrite. -/
theorem mem_surv_iff (b x : Fin (2*(n+1))) :
    x ∈ (({0, b} : Finset (Fin (2*(n+1))))ᶜ) ↔ (x ≠ 0 ∧ x ≠ b) := by
  simp [Finset.mem_compl, Finset.mem_singleton]

/-- The survivor equiv as `Fin (2n) ≃ {x ≠ 0 ∧ x ≠ b}` (order-preserving on values). -/
noncomputable def sEquiv (b : Fin (2*(n+1))) (hb : b ≠ 0) :
    Fin (2*n) ≃ {x : Fin (2*(n+1)) // x ≠ 0 ∧ x ≠ b} :=
  (survOIso b hb).toEquiv.trans (Equiv.subtypeEquivRight (mem_surv_iff b))

theorem sEquiv_strictMono (b : Fin (2*(n+1))) (hb : b ≠ 0) {i j : Fin (2*n)} (h : i < j) :
    ((sEquiv b hb i : Fin (2*(n+1)))) < ((sEquiv b hb j : Fin (2*(n+1)))) := by
  unfold sEquiv
  simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe, OrderIso.coe_toEquiv]
  exact (survOIso b hb).strictMono h

theorem sEquiv_lt_iff (b : Fin (2*(n+1))) (hb : b ≠ 0) {i j : Fin (2*n)} :
    ((sEquiv b hb i : Fin (2*(n+1)))) < ((sEquiv b hb j : Fin (2*(n+1)))) ↔ i < j := by
  constructor
  · intro h; by_contra hc; rw [not_lt] at hc
    rcases hc.lt_or_eq with h2 | h2
    · exact absurd (sEquiv_strictMono b hb h2) (not_lt.mpr h.le)
    · rw [h2] at h; exact absurd h (lt_irrefl _)
  · exact sEquiv_strictMono b hb

theorem sEquiv_mem (b : Fin (2*(n+1))) (hb : b ≠ 0) (i : Fin (2*n)) :
    (sEquiv b hb i : Fin (2*(n+1))) ≠ 0 ∧ (sEquiv b hb i : Fin (2*(n+1))) ≠ b :=
  (sEquiv b hb i).2

-- ## The reduced pairing p' via the order-preserving survivor equiv

/-- `p` maps survivors `{≠0, ≠b}` (b=p.1 0) to survivors. -/
theorem p_surv (p : Pairing (n+1)) (x) :
    (p.1 x ≠ 0 ∧ p.1 x ≠ p.1 0) ↔ (x ≠ 0 ∧ x ≠ p.1 0) := by
  have hinj := p.1.injective
  have hkey : ∀ y, p.1 y = 0 ↔ y = p.1 0 := by
    intro y; constructor
    · intro h; have h2 : p.1 (p.1 y) = p.1 0 := by rw [h]
      rw [pairing_invol p y] at h2; exact h2
    · intro h; rw [h, pairing_invol p 0]
  refine ⟨fun ⟨h1,h2⟩ => ⟨fun hx => h2 (by rw [hx]), fun hx => h1 ((hkey x).mpr hx)⟩,
    fun ⟨h1,h2⟩ => ⟨fun h => h2 ((hkey x).mp h), fun h => h1 (hinj h)⟩⟩

/-- Reduced pairing built through the ORDER-PRESERVING survivor equiv `sEquiv`. -/
noncomputable def pPrimeO (p : Pairing (n+1)) : Pairing n :=
  ⟨(sEquiv (p.1 0) (p.2.2 0)).symm.permCongr (p.1.subtypePerm (p_surv p)), by
    rw [← Equiv.permCongr_mul,
      (by ext x
          simp only [Equiv.Perm.subtypePerm_mul, Equiv.Perm.subtypePerm_apply,
            Equiv.Perm.one_apply]
          exact congrArg Fin.val (pairing_invol p x.1)
        : p.1.subtypePerm (p_surv p) * p.1.subtypePerm (p_surv p) = 1)]
    ext x; simp [Equiv.permCongr_apply], by
    intro x; rw [Ne, Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply]
    simp only [Equiv.symm_symm]
    rw [Equiv.Perm.subtypePerm_apply]
    exact fun h => p.2.2 _ (Subtype.ext_iff.mp h)⟩

/-- The defining apply relation: `sEquiv (p'.1 i) = p.1 (sEquiv i)` (on values). -/
theorem pPrimeO_apply (p : Pairing (n+1)) (i : Fin (2*n)) :
    (sEquiv (p.1 0) (p.2.2 0) ((pPrimeO p).1 i) : Fin (2*(n+1)))
      = p.1 (sEquiv (p.1 0) (p.2.2 0) i) := by
  have : (pPrimeO p).1 i
      = (sEquiv (p.1 0) (p.2.2 0)).symm.permCongr (p.1.subtypePerm (p_surv p)) i := rfl
  rw [this, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

-- ## The crossings split: cr(p) = cr(p') + S_p

/-- The straddle count: number of vertices `c` with `0 < c < b` and `b < p.1 c`,
i.e. the number of `p`-chords straddling the deleted chord `(0, b)` (`b = p.1 0`). -/
def straddle (p : Pairing (n+1)) : ℕ :=
  (Finset.univ.filter (fun c : Fin (2*(n+1)) =>
    0 < c ∧ c < p.1 0 ∧ p.1 0 < p.1 c)).card

/-- `p.1 b = 0` where `b = p.1 0`. -/
theorem p_b_eq_zero (p : Pairing (n+1)) : p.1 (p.1 0) = 0 := pairing_invol p 0

/-- Every survivor `x` is `sEquiv` of some `i`. -/
theorem sEquiv_surj (p : Pairing (n+1)) {x : Fin (2*(n+1))} (hx : x ≠ 0 ∧ x ≠ p.1 0) :
    ∃ i, (sEquiv (p.1 0) (p.2.2 0) i : Fin (2*(n+1))) = x := by
  refine ⟨(sEquiv (p.1 0) (p.2.2 0)).symm ⟨x, hx⟩, ?_⟩
  rw [Equiv.apply_symm_apply]

set_option maxHeartbeats 1200000 in
/-- **Chord-deletion crossing split.** `p.crossings = (pPrimeO p).crossings + straddle p`.
The genuine combinatorial core of the merge sign: deleting the global-minimum chord `(0,b)`
removes exactly the crossings it participates in (the straddlers), and the surviving
crossings biject order-preservingly with those of the reduced pairing. -/
theorem crossings_split (p : Pairing (n+1)) :
    p.crossings = (pPrimeO p).crossings + straddle p := by
  set b := p.1 0 with hb
  set e := sEquiv b (p.2.2 0) with he
  -- The crossing-pair filter for p over Fin(2(n+1))^2.
  set Fp := (Finset.univ : Finset (Fin (2*(n+1)) × Fin (2*(n+1)))).filter
      (fun ac => ac.1 < p.1 ac.1 ∧ ac.2 < p.1 ac.2 ∧
        ac.1 < ac.2 ∧ ac.2 < p.1 ac.1 ∧ p.1 ac.1 < p.1 ac.2) with hFp
  -- Part B: those involving the (0,b) chord, i.e. ac.1 = 0.
  set FB := Fp.filter (fun ac => ac.1 = 0) with hFB
  set FA := Fp.filter (fun ac => ¬ ac.1 = 0) with hFA
  have hsplit : Fp.card = FA.card + FB.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Fp) (p := fun ac => ac.1 = 0)
    have hFBc : FB.card = (Fp.filter (fun ac => ac.1 = 0)).card := rfl
    have hFAc : FA.card = (Fp.filter (fun ac => ¬ ac.1 = 0)).card := rfl
    rw [hFAc, hFBc]; omega
  have hpcr : p.crossings = Fp.card := rfl
  -- b = p.1 0 is a RIGHT endpoint: p.1 b = 0 < b.
  have hb_right : p.1 b < b := by
    rw [hb, p_b_eq_zero]; exact Fin.pos_of_ne_zero (p.2.2 0)
  -- left endpoints are survivors (≠ 0 and ≠ b)
  have hleft_surv : ∀ x : Fin (2*(n+1)), x < p.1 x → x ≠ 0 → (x ≠ 0 ∧ x ≠ b) := by
    intro x hxl hx0
    exact ⟨hx0, fun h => by rw [h] at hxl; exact absurd hxl (not_lt.mpr hb_right.le)⟩
  -- e⁻¹ helper: e applied to e.symm of a survivor returns the survivor value
  have he_symm_val : ∀ (x : Fin (2*(n+1))) (hx : x ≠ 0 ∧ x ≠ b),
      (e (e.symm ⟨x, hx⟩) : Fin (2*(n+1))) = x := by
    intro x hx; rw [Equiv.apply_symm_apply]
  have hA : FA.card = (pPrimeO p).crossings := by
    rw [Pairing.crossings]
    symm
    apply Finset.card_bij (fun ij _ => ((e ij.1 : Fin (2*(n+1))), (e ij.2 : Fin (2*(n+1)))))
    · -- maps p'-crossings into FA
      rintro ⟨i, j⟩ hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      obtain ⟨hipi, hjpj, hij_lt, hjpi, hpipj⟩ := hij
      -- transport via e (order-preserving) and pPrimeO_apply
      have hei : (e ((pPrimeO p).1 i) : Fin (2*(n+1))) = p.1 (e i) := pPrimeO_apply p i
      have hej : (e ((pPrimeO p).1 j) : Fin (2*(n+1))) = p.1 (e j) := pPrimeO_apply p j
      simp only [hFA, hFp, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [← hei]; exact sEquiv_strictMono b (p.2.2 0) hipi
      · rw [← hej]; exact sEquiv_strictMono b (p.2.2 0) hjpj
      · exact sEquiv_strictMono b (p.2.2 0) hij_lt
      · rw [← hei]; exact sEquiv_strictMono b (p.2.2 0) hjpi
      · rw [← hei, ← hej]; exact sEquiv_strictMono b (p.2.2 0) hpipj
      · exact (e i).2.1
    · -- injective
      rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      have h1 : i = i' := e.injective (Subtype.ext heq.1)
      have h2 : j = j' := e.injective (Subtype.ext heq.2)
      exact Prod.ext h1 h2
    · -- surjective
      rintro ⟨a, c⟩ hac
      simp only [hFA, hFp, Finset.mem_filter, Finset.mem_univ, true_and] at hac
      obtain ⟨⟨hapa, hcpc, hac_lt, hcpa, hpapc⟩, ha0⟩ := hac
      -- a, c survivors
      have hasurv : a ≠ 0 ∧ a ≠ b := hleft_surv a hapa ha0
      have hc0 : c ≠ 0 := by
        intro h; rw [h] at hac_lt; exact Fin.not_lt_zero a hac_lt
      have hcsurv : c ≠ 0 ∧ c ≠ b := hleft_surv c hcpc hc0
      refine ⟨(e.symm ⟨a, hasurv⟩, e.symm ⟨c, hcsurv⟩), ?_, ?_⟩
      · -- in p'-crossings filter
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hea : (e (e.symm ⟨a, hasurv⟩) : Fin (2*(n+1))) = a := he_symm_val a hasurv
        have hec : (e (e.symm ⟨c, hcsurv⟩) : Fin (2*(n+1))) = c := he_symm_val c hcsurv
        have hpa : (e ((pPrimeO p).1 (e.symm ⟨a, hasurv⟩)) : Fin (2*(n+1))) = p.1 a := by
          rw [pPrimeO_apply, hea]
        have hpc : (e ((pPrimeO p).1 (e.symm ⟨c, hcsurv⟩)) : Fin (2*(n+1))) = p.1 c := by
          rw [pPrimeO_apply, hec]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [← sEquiv_lt_iff b (p.2.2 0), hea, hpa]; exact hapa
        · rw [← sEquiv_lt_iff b (p.2.2 0), hec, hpc]; exact hcpc
        · rw [← sEquiv_lt_iff b (p.2.2 0), hea, hec]; exact hac_lt
        · rw [← sEquiv_lt_iff b (p.2.2 0), hec, hpa]; exact hcpa
        · rw [← sEquiv_lt_iff b (p.2.2 0), hpa, hpc]; exact hpapc
      · -- the pair maps back to (a,c)
        simp only [Prod.mk.injEq]
        exact ⟨he_symm_val a hasurv, he_symm_val c hcsurv⟩
  have hB : FB.card = straddle p := by
    rw [straddle]
    apply Finset.card_bij (fun ac _ => ac.2)
    · -- maps into straddle filter
      rintro ⟨a, c⟩ hac
      simp only [hFB, hFp, Finset.mem_filter, Finset.mem_univ, true_and] at hac
      obtain ⟨⟨_, _, _, hcb, hbpc⟩, ha0⟩ := hac
      subst ha0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa using ‹(0 : Fin (2*(n+1))) < c›, hcb, hbpc⟩
    · -- injective
      rintro ⟨a, c⟩ hac ⟨a', c'⟩ hac' h
      simp only [hFB, Finset.mem_filter] at hac hac'
      simp only at h
      exact Prod.ext (by rw [hac.2, hac'.2]) h
    · -- surjective
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      obtain ⟨hc0, hcb, hbpc⟩ := hc
      refine ⟨(0, c), ?_, rfl⟩
      rw [hFB, Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [hFp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, lt_trans hcb hbpc, hc0, hcb, hbpc⟩
      exact Fin.pos_of_ne_zero (p.2.2 0)
  rw [hpcr, hsplit, hA, hB]

/-- **p-side crossing-parity sign lemma** (the named merge sign deliverable).
`ε(p) = (-1)^{straddle p} · ε(p')`, where `p'` deletes the global-minimum chord `(0, b)`
(`b = p.1 0`) and `straddle p` counts the chords crossing it. Direct corollary of
`crossings_split`. -/
theorem epsSign_pPrimeO (p : Pairing (n+1)) :
    (epsSign p : ℤ) = (-1) ^ (straddle p) * (epsSign (pPrimeO p) : ℤ) := by
  show ((-1 : ℤ)) ^ p.crossings = (-1) ^ (straddle p) * (-1) ^ (pPrimeO p).crossings
  rw [crossings_split p, pow_add, mul_comm]

/-- Equivalently, `ε(p) · ε(p') = (-1)^{straddle p}` (the parity correction is local). -/
theorem epsSign_mul_pPrimeO (p : Pairing (n+1)) :
    (epsSign p : ℤ) * (epsSign (pPrimeO p) : ℤ) = (-1) ^ (straddle p) := by
  rw [epsSign_pPrimeO p, mul_assoc]
  show (-1 : ℤ) ^ (straddle p) * ((-1) ^ (pPrimeO p).crossings * (-1) ^ (pPrimeO p).crossings) = _
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

end MergeSignFoundation

/-! ### Strategy-C infrastructure for `gram_recursion` (the merge / two-loop reduction) -/

/-- In the erased product `EP M n p i`, the value of `i` at the vertex `p.1 0` is irrelevant:
the only `p`-chord through `p.1 0` is the chord `(0, p.1 0)`, precisely the one erased from `EP`. -/
theorem EP_indep_of_partner (M n : ℕ) (p : Pairing (n+1)) (i : Fin (2*(n+1)) → Fin (2*M))
    (x : Fin (2*M)) :
    EP M n p (Function.update i (p.1 0) x) = EP M n p i := by
  unfold EP
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨hane, hpane⟩ := erased_indices_ne_zero n p ha
  rw [Finset.mem_erase, Finset.mem_filter] at ha
  obtain ⟨ha0, _, halt⟩ := ha
  have hpp0 : p.1 (p.1 0) = 0 := by
    have h2 : (p.1 * p.1) 0 = 0 := by rw [p.2.1]; rfl
    rwa [Equiv.Perm.mul_apply] at h2
  have hab : a ≠ p.1 0 := by intro h; rw [h, hpp0] at halt; exact absurd halt (Fin.not_lt_zero _)
  have hpab : p.1 a ≠ p.1 0 := fun h => ha0 (p.1.injective h)
  rw [Function.update_of_ne hab, Function.update_of_ne hpab]

/-- `EP_p ∘ reLift` does not depend on the value of `rest` at the vertex `b = p.1 0`: updating
`rest` at `⟨b⟩` changes `reLift rest` only at vertices `b` and `0`, neither read by `EP_p`. -/
theorem EP_reLift_indep_b (M n : ℕ) (p : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) (x : Fin (2*M)) :
    EP M n p (reLift M n p (Function.update rest ⟨p.1 0, p.2.2 0⟩ x))
      = EP M n p (reLift M n p rest) := by
  unfold EP
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨hane, hpane⟩ := erased_indices_ne_zero n p ha
  rw [Finset.mem_erase, Finset.mem_filter] at ha
  obtain ⟨ha0, _, halt⟩ := ha
  have hpp0 : p.1 (p.1 0) = 0 := by
    have h2 : (p.1 * p.1) 0 = 0 := by rw [p.2.1]; rfl
    rwa [Equiv.Perm.mul_apply] at h2
  have hab : a ≠ p.1 0 := by intro h; rw [h, hpp0] at halt; exact absurd halt (Fin.not_lt_zero _)
  have hpab : p.1 a ≠ p.1 0 := fun h => ha0 (p.1.injective h)
  rw [reLift_ne M n p _ hane, reLift_ne M n p _ hpane,
      reLift_ne M n p _ hane, reLift_ne M n p _ hpane]
  congr 1
  · rw [Function.update_of_ne (fun h => hab (congrArg Subtype.val h))]
  · rw [Function.update_of_ne (fun h => hpab (congrArg Subtype.val h))]

/-- `EP_q ∘ (reLift via p)` does not depend on the value of `rest` at the vertex `c = q.1 0`:
`EP_q` reads neither vertex `0` nor `q.1 0` (the latter's only `q`-chord `(0, q.1 0)` is erased). -/
theorem EP_q_reLift_indep (M n : ℕ) (p q : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) (x : Fin (2*M)) :
    EP M n q (reLift M n p (Function.update rest ⟨q.1 0, q.2.2 0⟩ x))
      = EP M n q (reLift M n p rest) := by
  unfold EP
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨hane, hqane⟩ := erased_indices_ne_zero n q ha
  rw [Finset.mem_erase, Finset.mem_filter] at ha
  obtain ⟨ha0, _, halt⟩ := ha
  have hqq0 : q.1 (q.1 0) = 0 := by
    have h2 : (q.1 * q.1) 0 = 0 := by rw [q.2.1]; rfl
    rwa [Equiv.Perm.mul_apply] at h2
  have hab : a ≠ q.1 0 := by intro h; rw [h, hqq0] at halt; exact absurd halt (Fin.not_lt_zero _)
  have hqab : q.1 a ≠ q.1 0 := fun h => ha0 (q.1.injective h)
  rw [reLift_ne M n p _ hane, reLift_ne M n p _ hqane,
      reLift_ne M n p _ hane, reLift_ne M n p _ hqane]
  congr 1
  · rw [Function.update_of_ne (fun h => hab (congrArg Subtype.val h))]
  · rw [Function.update_of_ne (fun h => hqab (congrArg Subtype.val h))]

/-- Generic free-coordinate factorization: a functional `F` on `S → W` independent of the value at
a fixed `a` sums to `card W` copies of the sum over functions on `{s ≠ a}` (re-lifted with any
basepoint `w₀`). -/
theorem sum_indep_factor {S : Type*} [Fintype S] [DecidableEq S]
    {W : Type*} [Fintype W] [DecidableEq W]
    (a : S) (w₀ : W) {R : Type*} [AddCommMonoid R] (F : (S → W) → R)
    (hindep : ∀ (f : S → W) (x : W), F (Function.update f a x) = F f) :
    (∑ f : S → W, F f)
      = (Fintype.card W) • (∑ g : {s : S // s ≠ a} → W,
          F ((Equiv.funSplitAt a W).symm (w₀, g))) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt a W).symm F, Fintype.sum_prod_type]
  have key : ∀ (w : W) (g : {s // s ≠ a} → W),
      F ((Equiv.funSplitAt a W).symm (w, g)) = F ((Equiv.funSplitAt a W).symm (w₀, g)) := by
    intro w g
    have h1 : (Equiv.funSplitAt a W).symm (w, g)
        = Function.update ((Equiv.funSplitAt a W).symm (w₀, g)) a w := by
      funext s
      by_cases hs : s = a
      · subst hs; rw [Function.update_self]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
      · rw [Function.update_of_ne hs]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hs]
    rw [h1, hindep]
  simp_rw [key]
  rw [Finset.sum_const, Finset.card_univ]

/-- In the two-loop case `p.1 0 = q.1 0`, the indicator `[rest b = rest c]` is identically true. -/
theorem gram_if_collapse_eq (M n : ℕ) (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
        then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest) else 0)
      = EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest) := by
  rw [show (⟨p.1 0, p.2.2 0⟩ : {j : Fin (2*(n+1)) // j ≠ 0}) = ⟨q.1 0, q.2.2 0⟩ from
        Subtype.ext hbc, if_pos rfl]

/-- The combined two-loop summand is independent of the value of `rest` at the merged vertex `⟨b⟩`. -/
theorem two_loop_summand_indep (M n : ℕ) (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) (x : Fin (2*M)) :
    EP M n p (reLift M n p (Function.update rest ⟨p.1 0, p.2.2 0⟩ x))
        * EP M n q (reLift M n p (Function.update rest ⟨p.1 0, p.2.2 0⟩ x))
      = EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest) := by
  rw [EP_reLift_indep_b M n p rest x]
  congr 1
  rw [show (⟨p.1 0, p.2.2 0⟩ : {j : Fin (2*(n+1)) // j ≠ 0}) = ⟨q.1 0, q.2.2 0⟩ from Subtype.ext hbc]
  rw [EP_q_reLift_indep M n p q rest x]

/-- **Two-loop `2*M`-extraction**: in the case `p.1 0 = q.1 0`, the index sum equals `2*M` times the
`Fin (2*n)`-reindexed contraction sum (the merged vertex `b` is free over `Fin (2*M)`). Fully proved. -/
theorem two_loop_branch (M n : ℕ) (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0)
    (w₀ : Fin (2*M)) :
    (∑ rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M),
        (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
          then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest) else 0))
      = (2*M) • (∑ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
          EP M n p (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g)))
            * EP M n q (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g)))) := by
  simp_rw [gram_if_collapse_eq M n p q hbc]
  rw [sum_indep_factor ⟨p.1 0, p.2.2 0⟩ w₀
        (fun rest => EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest))
        (two_loop_summand_indep M n p q hbc)]
  rw [Fintype.card_fin]

/-- At level `n+1`, the loop count is positive: `cycleCount (p*q)` is even (`cycleCount_pq_even`)
and at least `1` (the permutation acts on `2(n+1) ≥ 2` points), hence at least `2`. -/
theorem loops_pos {n : ℕ} (p q : Pairing (n+1)) : 0 < p.loops q := by
  have heven := cycleCount_pq_even p q
  have h2 : 2 * p.loops q = cycleCount (2*(n+1)) (p.1 * q.1) := loops_two_mul p q
  have hge1 : 1 ≤ cycleCount (2*(n+1)) (p.1 * q.1) := by
    rw [cycleCount]
    by_contra hlt
    push Not at hlt
    have hfix : (Finset.univ.filter fun x => (p.1*q.1) x = x).card = 0 := by omega
    have hct : (p.1*q.1).cycleType.card = 0 := by omega
    have hone : (p.1 * q.1) = 1 := by
      rw [← Equiv.Perm.cycleType_eq_zero]; exact Multiset.card_eq_zero.mp hct
    have hall : (Finset.univ.filter fun x => (p.1*q.1) x = x) = Finset.univ :=
      Finset.filter_true_of_mem (fun x _ => by rw [hone]; rfl)
    rw [hall, Finset.card_univ, Fintype.card_fin] at hfix
    omega
  omega

/-! ### Two-loop residual: the EP→deltaContr bridge, loops `+1`, and sign-parity. -/
section TwoLoopResidual
open Equiv Equiv.Perm Finset

/-- The index transport: a `rest`-function on nonzero vertices, pulled back to `Fin (2n)`
through the order-preserving survivor equiv `sEquiv b` (`b = p.1 0`). -/
noncomputable def idxOf (p : Pairing (n+1)) (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    Fin (2*n) → Fin (2*M) :=
  fun i => rest ⟨sEquiv (p.1 0) (p.2.2 0) i, (sEquiv_mem (p.1 0) (p.2.2 0) i).1⟩

/-- **EP→deltaContr bridge.** The erased product `EP_p (reLift p rest)` equals the reduced
contraction `deltaContr (pPrimeO p)` of the transported index. Sign-free because `sEquiv` is
order-preserving (the chord filter `a < p.1 a` matches `i < p'.1 i` exactly). -/
theorem EP_eq_deltaContr (M n : ℕ) (p : Pairing (n+1))
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    EP M n p (reLift M n p rest) = deltaContr M (pPrimeO p) (idxOf (M := M) p rest) := by
  set b := p.1 0 with hb
  set e := sEquiv b (p.2.2 0) with he
  unfold EP deltaContr
  symm
  apply Finset.prod_bij (fun i (_ : i ∈ Finset.univ.filter (fun i => i < (pPrimeO p).1 i)) =>
    (e i : Fin (2*(n+1))))
  · -- maps p'-left-ends into (erased) p-left-ends
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨_, hilt⟩ := hi
    have hei : (e ((pPrimeO p).1 i) : Fin (2*(n+1))) = p.1 (e i) := pPrimeO_apply p i
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨(e i).2.1, Finset.mem_univ _, ?_⟩
    rw [← hei]; exact sEquiv_strictMono b (p.2.2 0) hilt
  · -- injective
    intro i _ i' _ heq
    exact e.injective (Subtype.ext heq)
  · -- surjective
    intro a ha
    rw [Finset.mem_erase, Finset.mem_filter] at ha
    obtain ⟨ha0, _, halt⟩ := ha
    -- a is a survivor: a ≠ 0 (ha0) and a ≠ b (a is a LEFT end, b is a RIGHT end)
    have hb_right : p.1 b < b := by
      rw [hb, p_b_eq_zero]; exact Fin.pos_of_ne_zero (p.2.2 0)
    have hab : a ≠ b := fun h => by
      rw [h] at halt; exact absurd halt (not_lt.mpr hb_right.le)
    obtain ⟨i, hi⟩ := sEquiv_surj p ⟨ha0, hab⟩
    refine ⟨i, ?_, hi⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← sEquiv_lt_iff b (p.2.2 0)]
    have hei : (e ((pPrimeO p).1 i) : Fin (2*(n+1))) = p.1 (e i) := pPrimeO_apply p i
    rw [show (e i : Fin (2*(n+1))) = a from hi] at hei ⊢
    rw [hei]; exact halt
  · -- the J-values match
    intro i hi
    rw [Finset.mem_filter] at hi
    have hei : (e ((pPrimeO p).1 i) : Fin (2*(n+1))) = p.1 (e i) := pPrimeO_apply p i
    have hane : (e i : Fin (2*(n+1))) ≠ 0 := (e i).2.1
    have hpane : p.1 (e i : Fin (2*(n+1))) ≠ 0 := by
      rw [← hei]; exact (e ((pPrimeO p).1 i)).2.1
    rw [reLift_ne M n p rest hane, reLift_ne M n p rest hpane]
    unfold idxOf
    have h2 : (⟨p.1 (e i), hpane⟩ : {j : Fin (2*(n+1)) // j ≠ 0})
        = ⟨(e ((pPrimeO p).1 i) : Fin (2*(n+1))), (e ((pPrimeO p).1 i)).2.1⟩ := by
      rw [Subtype.ext_iff]; exact hei.symm
    rw [h2]

/-- **EP→deltaContr bridge for `q`** in the two-loop case `q.1 0 = p.1 0`: `EP_q (reLift p rest)`
equals `deltaContr (pPrimeO q)` of the index transported through `q`'s survivor equiv. Since
`q.1 0 = b = p.1 0`, the two survivor equivs agree and `reLift p` reads the right values.
(`_hbc` is deliberately unused in the formal proof — the bijection reads only `q`'s survivor
equiv — and is kept to record the two-loop-case hypothesis under which the bridge is invoked.) -/
theorem EP_q_eq_deltaContr (M n : ℕ) (p q : Pairing (n+1)) (_hbc : p.1 0 = q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    EP M n q (reLift M n p rest) = deltaContr M (pPrimeO q) (idxOf (M := M) q rest) := by
  set b := q.1 0 with hb
  set e := sEquiv b (q.2.2 0) with he
  unfold EP deltaContr
  symm
  apply Finset.prod_bij (fun i (_ : i ∈ Finset.univ.filter (fun i => i < (pPrimeO q).1 i)) =>
    (e i : Fin (2*(n+1))))
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨_, hilt⟩ := hi
    have hei : (e ((pPrimeO q).1 i) : Fin (2*(n+1))) = q.1 (e i) := pPrimeO_apply q i
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨(e i).2.1, Finset.mem_univ _, ?_⟩
    rw [← hei]; exact sEquiv_strictMono b (q.2.2 0) hilt
  · intro i _ i' _ heq
    exact e.injective (Subtype.ext heq)
  · intro a ha
    rw [Finset.mem_erase, Finset.mem_filter] at ha
    obtain ⟨ha0, _, halt⟩ := ha
    have hb_right : q.1 b < b := by
      rw [hb, p_b_eq_zero]; exact Fin.pos_of_ne_zero (q.2.2 0)
    have hab : a ≠ b := fun h => by
      rw [h] at halt; exact absurd halt (not_lt.mpr hb_right.le)
    obtain ⟨i, hi⟩ := sEquiv_surj q ⟨ha0, hab⟩
    refine ⟨i, ?_, hi⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← sEquiv_lt_iff b (q.2.2 0)]
    have hei : (e ((pPrimeO q).1 i) : Fin (2*(n+1))) = q.1 (e i) := pPrimeO_apply q i
    rw [show (e i : Fin (2*(n+1))) = a from hi] at hei ⊢
    rw [hei]; exact halt
  · intro i hi
    rw [Finset.mem_filter] at hi
    have hei : (e ((pPrimeO q).1 i) : Fin (2*(n+1))) = q.1 (e i) := pPrimeO_apply q i
    have hane : (e i : Fin (2*(n+1))) ≠ 0 := (e i).2.1
    have hpane : q.1 (e i : Fin (2*(n+1))) ≠ 0 := by
      rw [← hei]; exact (e ((pPrimeO q).1 i)).2.1
    rw [reLift_ne M n p rest hane, reLift_ne M n p rest hpane]
    unfold idxOf
    have h2 : (⟨q.1 (e i), hpane⟩ : {j : Fin (2*(n+1)) // j ≠ 0})
        = ⟨(e ((pPrimeO q).1 i) : Fin (2*(n+1))), (e ((pPrimeO q).1 i)).2.1⟩ := by
      rw [Subtype.ext_iff]; exact hei.symm
    rw [h2]

/-- A fixed-point-free involution on a finset (in a linear order) has even cardinality:
it pairs each `x` with `g x` across `{x < g x}` ↔ `{g x < x}`. -/
theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset α) (g : α → α) (hg_inv : ∀ x ∈ s, g (g x) = x) (hg_mem : ∀ x ∈ s, g x ∈ s)
    (hg_ne : ∀ x ∈ s, g x ≠ x) : Even s.card := by
  classical
  set A := s.filter (fun x => x < g x) with hA
  set B := s.filter (fun x => g x < x) with hB
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hA, Finset.mem_filter] at hxA
    rw [hB, Finset.mem_filter] at hxB
    exact absurd hxA.2 (not_lt.mpr hxB.2.le)
  have hunion : A ∪ B = s := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    · intro x hx
      rcases lt_trichotomy x (g x) with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h⟩)
      · exact absurd h.symm (hg_ne x hx)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hcardAB : A.card = B.card := by
    apply Finset.card_bij (fun x _ => g x)
    · intro x hx
      rw [hA, Finset.mem_filter] at hx
      rw [hB, Finset.mem_filter]
      exact ⟨hg_mem x hx.1, by rw [hg_inv x hx.1]; exact hx.2⟩
    · intro x hx y hy h
      rw [hA, Finset.mem_filter] at hx hy
      have := congrArg g h
      rwa [hg_inv x hx.1, hg_inv y hy.1] at this
    · intro y hy
      rw [hB, Finset.mem_filter] at hy
      refine ⟨g y, ?_, hg_inv y hy.1⟩
      rw [hA, Finset.mem_filter]
      exact ⟨hg_mem y hy.1, by rw [hg_inv y hy.1]; exact hy.2⟩
  have hs : s.card = A.card + B.card := by
    rw [← hunion, Finset.card_union_of_disjoint hAB_disj]
  rw [hs, ← hcardAB]; exact ⟨A.card, by ring⟩

/-- **Straddle parity.** `(-1)^(straddle p) = (-1)^|{c : 0<c<b}|` where `b = p.1 0`.
The lower interval `Lo = {0<c<b}` splits into straddlers (= straddle p) and within-`Lo`
`p`-chords (even, via the fpf involution `c ↦ p.1 c`), so `straddle p ≡ |Lo| (mod 2)`. -/
theorem straddle_parity_eq (p : Pairing (n+1)) :
    (-1 : ℤ) ^ (straddle p)
      = (-1) ^ (Finset.univ.filter (fun c : Fin (2*(n+1)) => 0 < c ∧ c < p.1 0)).card := by
  set b := p.1 0 with hb
  set Lo := Finset.univ.filter (fun c : Fin (2*(n+1)) => 0 < c ∧ c < b) with hLo
  set St := Finset.univ.filter (fun c : Fin (2*(n+1)) => 0 < c ∧ c < b ∧ b < p.1 c) with hSt
  set LoW := Lo.filter (fun c => p.1 c < b) with hLoW
  -- p.1 c ≠ 0 and ≠ b for c ∈ Lo
  have hb0 : b ≠ 0 := p.2.2 0
  have hpb0 : p.1 b = 0 := p_b_eq_zero p
  have hc_ne : ∀ c ∈ Lo, p.1 c ≠ 0 ∧ p.1 c ≠ b := by
    intro c hc
    rw [hLo, Finset.mem_filter] at hc
    obtain ⟨_, hc0, hcb⟩ := hc
    constructor
    · intro h
      -- p.1 c = 0 ⟹ c = p.1 0 = b, contra c < b
      have : c = b := by
        have h2 : p.1 (p.1 c) = p.1 0 := by rw [h]
        rwa [pairing_invol p c, ← hb] at h2
      rw [this] at hcb; exact absurd hcb (lt_irrefl b)
    · intro h
      -- p.1 c = b ⟹ c = p.1 b = 0, contra 0 < c
      have : c = 0 := by
        have h2 : p.1 (p.1 c) = p.1 b := by rw [h]
        rwa [pairing_invol p c, hpb0] at h2
      rw [this] at hc0; exact absurd hc0 (lt_irrefl _)
  -- Lo = St ∪ LoW disjointly
  have hLo_split : Lo.card = St.card + LoW.card := by
    have hdisj : Disjoint St LoW := by
      rw [Finset.disjoint_left]
      intro c hcSt hcLoW
      rw [hSt, Finset.mem_filter] at hcSt
      rw [hLoW, Finset.mem_filter] at hcLoW
      exact absurd hcSt.2.2.2 (not_lt.mpr hcLoW.2.le)
    have hunion : St ∪ LoW = Lo := by
      apply Finset.Subset.antisymm
      · intro c hc
        rcases Finset.mem_union.mp hc with h | h
        · rw [hSt, Finset.mem_filter] at h
          rw [hLo, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h.2.1, h.2.2.1⟩
        · exact (Finset.mem_filter.mp h).1
      · intro c hc
        have hne := hc_ne c hc
        rw [hLo, Finset.mem_filter] at hc
        obtain ⟨_, hc0, hcb⟩ := hc
        rcases lt_trichotomy (p.1 c) b with h | h | h
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨by rw [hLo, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc0, hcb⟩, h⟩)
        · exact absurd h hne.2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hc0, hcb, h⟩)
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  -- LoW even
  have hLoW_even : Even LoW.card := by
    apply even_card_of_fpf_involution LoW (fun c => p.1 c)
    · intro c _; exact pairing_invol p c
    · intro c hc
      rw [hLoW, Finset.mem_filter] at hc
      obtain ⟨hcLo, hcW⟩ := hc
      have hne := hc_ne c hcLo
      rw [hLo, Finset.mem_filter] at hcLo
      rw [hLoW, Finset.mem_filter, hLo, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, hcW⟩, ?_⟩
      · exact Fin.pos_of_ne_zero hne.1
      · rw [pairing_invol p c]; exact hcLo.2.2
    · intro c _; exact (p.2.2 c)
  -- straddle p = St.card
  have hStr : straddle p = St.card := by rw [straddle, hSt, hb]
  -- conclude parity
  obtain ⟨m, hm⟩ := hLoW_even
  rw [hStr]
  rw [show Lo.card = St.card + LoW.card from hLo_split, hm]
  rw [pow_add, pow_add]
  have : ((-1 : ℤ))^m * (-1)^m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [this, mul_one]

/-- **Two-loop sign.** In the case `p.1 0 = q.1 0`, `ε(p)·ε(q) = ε(p')·ε(q')` where
`p' = pPrimeO p`, `q' = pPrimeO q`. Both straddle counts have the same parity (= |{0<c<b}|,
same `b`), so the two `(-1)^straddle` corrections cancel. -/
theorem two_loop_sign (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0) :
    epsVec ℤ p * epsVec ℤ q = epsVec ℤ (pPrimeO p) * epsVec ℤ (pPrimeO q) := by
  -- ε(p)ε(p') = (-1)^straddle p, ε(q)ε(q') = (-1)^straddle q
  have hp : (epsSign p : ℤ) * (epsSign (pPrimeO p) : ℤ) = (-1) ^ (straddle p) :=
    epsSign_mul_pPrimeO p
  have hq : (epsSign q : ℤ) * (epsSign (pPrimeO q) : ℤ) = (-1) ^ (straddle q) :=
    epsSign_mul_pPrimeO q
  -- the two straddle signs are equal (same b)
  have hstr : (-1 : ℤ) ^ (straddle p) = (-1) ^ (straddle q) := by
    rw [straddle_parity_eq p, straddle_parity_eq q, hbc]
  -- assemble: ε(p)ε(q) and ε(p')ε(q') differ by (-1)^straddle p · (-1)^straddle q = 1
  show (epsSign p : ℤ) * (epsSign q : ℤ) = (epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ)
  have key : ((epsSign p : ℤ) * (epsSign q : ℤ)) * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))
      = (-1) ^ (straddle p) * (-1) ^ (straddle q) := by
    rw [← hp, ← hq]; ring
  rw [hstr, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow] at key
  -- key : (εp εq)(εp' εq') = 1, and (εp' εq')² = 1, so εp εq = εp' εq'
  have hsqp' : (epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO p) : ℤ) = 1 := by
    show ((-1:ℤ)) ^ _ * (-1) ^ _ = 1
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hsqq' : (epsSign (pPrimeO q) : ℤ) * (epsSign (pPrimeO q) : ℤ) = 1 := by
    show ((-1:ℤ)) ^ _ * (-1) ^ _ = 1
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hsq' : ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))
      * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ)) = 1 := by
    rw [show ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))
          * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))
        = (epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO p) : ℤ)
          * ((epsSign (pPrimeO q) : ℤ) * (epsSign (pPrimeO q) : ℤ)) from by ring]
    rw [hsqp', hsqq', one_mul]
  calc (epsSign p : ℤ) * (epsSign q : ℤ)
      = ((epsSign p : ℤ) * (epsSign q : ℤ))
          * (((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))
             * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ))) := by rw [hsq', mul_one]
    _ = (((epsSign p : ℤ) * (epsSign q : ℤ))
          * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ)))
          * ((epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ)) := by ring
    _ = (epsSign (pPrimeO p) : ℤ) * (epsSign (pPrimeO q) : ℤ) := by rw [key, one_mul]

/-- `sEquiv` value is independent of the (irrelevant) `≠0` proof: equal base `b` gives equal value. -/
theorem sEquiv_val_eq {b b' : Fin (2*(n+1))} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : b = b')
    (i : Fin (2*n)) :
    (sEquiv b hb i : Fin (2*(n+1))) = (sEquiv b' hb' i : Fin (2*(n+1))) := by
  subst h; rfl

/-- **Generic cycle-type bridge:** if `σ` fixes every non-`q` element (and maps `q` to `q`),
its cycle type equals that of its restriction `σ.subtypePerm`. -/
theorem cycleType_subtypePerm_of_fixes_compl {N : ℕ} (σ : Equiv.Perm (Fin N))
    (P : Fin N → Prop) [DecidablePred P] (hmem : ∀ x, P (σ x) ↔ P x)
    (hfix : ∀ x, ¬ P x → σ x = x) :
    σ.cycleType = (σ.subtypePerm hmem).cycleType := by
  have hext : σ = (σ.subtypePerm hmem).extendDomain (Equiv.refl (Subtype P)) := by
    ext x
    by_cases hx : P x
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ hx]
      simp only [Equiv.refl_symm, Equiv.refl_apply, Equiv.Perm.subtypePerm_apply, Equiv.refl_apply]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hx, hfix x hx]
  conv_lhs => rw [hext]
  rw [Equiv.Perm.cycleType_extendDomain (Equiv.refl (Subtype P))]

/-- The two-loop reduced product, transported through `sEquiv`, equals `(p*q)` restricted to
survivors. The key pointwise identity behind `loops_two_loop`. -/
theorem reduced_prod_apply (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0) (i : Fin (2*n)) :
    (sEquiv (p.1 0) (p.2.2 0) (((pPrimeO p).1 * (pPrimeO q).1) i) : Fin (2*(n+1)))
      = (p.1 * q.1) (sEquiv (p.1 0) (p.2.2 0) i) := by
  show (sEquiv (p.1 0) (p.2.2 0) ((pPrimeO p).1 ((pPrimeO q).1 i)) : Fin (2*(n+1)))
      = p.1 (q.1 (sEquiv (p.1 0) (p.2.2 0) i))
  rw [pPrimeO_apply p ((pPrimeO q).1 i)]
  congr 1
  -- sEquiv (p.1 0) ((pPrimeO q).1 i) = q.1 (sEquiv (p.1 0) i)
  rw [sEquiv_val_eq (p.2.2 0) (q.2.2 0) hbc ((pPrimeO q).1 i)]
  rw [pPrimeO_apply q i]
  rw [sEquiv_val_eq (q.2.2 0) (p.2.2 0) hbc.symm i]

/-- **Two-loop loop count.** In the case `p.1 0 = q.1 0`, the joint loop count drops by exactly
one when the common chord `(0, b)` is deleted: `p.loops q = (pPrimeO p).loops (pPrimeO q) + 1`.
The deleted chord forms an isolated 2-loop (`p*q` fixes `0` and `b`), so two fixed points are
removed (`2·cycleCount` drops by 2). -/
theorem loops_two_loop (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0) :
    p.loops q = (pPrimeO p).loops (pPrimeO q) + 1 := by
  set b := p.1 0 with hb
  set σ := p.1 * q.1 with hσ
  set P : Fin (2*(n+1)) → Prop := fun x => x ≠ 0 ∧ x ≠ b with hP
  -- σ fixes 0 and b
  have hσ0 : σ 0 = 0 := by
    show p.1 (q.1 0) = 0
    rw [← hbc, hb]; exact pairing_invol p 0
  have hqb : q.1 b = 0 := by
    rw [hbc]; exact pairing_invol q 0
  have hσb : σ b = b := by
    show p.1 (q.1 b) = b
    rw [hqb]
  -- P-membership: σ preserves survivors
  have hmem : ∀ x, P (σ x) ↔ P x := by
    intro x
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨fun hx => ?_, fun hx => ?_⟩
      · rw [hx, hσ0] at h1; exact h1 rfl
      · rw [hx, hσb] at h2; exact h2 rfl
    · intro ⟨h1, h2⟩
      refine ⟨fun hx => ?_, fun hx => ?_⟩
      · have : x = 0 := σ.injective (by rw [hx, hσ0])
        exact h1 this
      · have : x = b := σ.injective (by rw [hx, hσb])
        exact h2 this
  -- σ fixes non-survivors
  have hfix : ∀ x, ¬ P x → σ x = x := by
    intro x hx
    have hcases : x = 0 ∨ x = b := by
      by_contra h
      push Not at h
      exact hx ⟨h.1, h.2⟩
    rcases hcases with h | h
    · rw [h]; exact hσ0
    · rw [h]; exact hσb
  -- cycleType σ = cycleType (subtypePerm)
  have hct1 : σ.cycleType = (σ.subtypePerm hmem).cycleType :=
    cycleType_subtypePerm_of_fixes_compl σ P hmem hfix
  -- reduced product = permCongr of subtypePerm via sEquiv
  have hredprod : (pPrimeO p).1 * (pPrimeO q).1
      = (sEquiv b (p.2.2 0)).symm.permCongr (σ.subtypePerm hmem) := by
    apply Equiv.ext
    intro i
    rw [Equiv.permCongr_apply, Equiv.symm_symm]
    -- goal: (p'*q') i = (sEquiv b).symm ((subtypePerm) (sEquiv b i))
    apply (sEquiv b (p.2.2 0)).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [Equiv.Perm.subtypePerm_apply]
    show (sEquiv b (p.2.2 0) (((pPrimeO p).1 * (pPrimeO q).1) i) : Fin (2*(n+1)))
        = σ (sEquiv b (p.2.2 0) i)
    exact reduced_prod_apply p q hbc i
  have hct2 : ((pPrimeO p).1 * (pPrimeO q).1).cycleType = (σ.subtypePerm hmem).cycleType := by
    rw [hredprod, cycleType_permCongr]
  have hcteq : σ.cycleType = ((pPrimeO p).1 * (pPrimeO q).1).cycleType := by
    rw [hct1, hct2]
  -- cycleCount relation: same cycleType, dims differ by 2
  -- support sum ≤ 2n (survivors), so cycleCount difference is exactly 2
  have hsumle : σ.cycleType.sum ≤ 2 * n := by
    -- support ⊆ survivors = (univ.erase 0).erase b, card 2n
    have hsupp : σ.support ⊆ (Finset.univ.erase 0).erase b := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, Finset.mem_univ _⟩
      · intro hxb; rw [hxb] at hx; exact hx hσb
      · intro hx0; rw [hx0] at hx; exact hx hσ0
    have hcard : ((Finset.univ.erase 0).erase b).card = 2 * n := by
      have hbmem : b ∈ (Finset.univ.erase (0 : Fin (2*(n+1)))) :=
        Finset.mem_erase.mpr ⟨p.2.2 0, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem hbmem,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    calc σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
      _ ≤ ((Finset.univ.erase 0).erase b).card := Finset.card_le_card hsupp
      _ = 2 * n := hcard
  -- now compute via cycleCount_eq
  have hcc_big : cycleCount (2*(n+1)) σ
      = (2*(n+1) - σ.cycleType.sum) + σ.cycleType.card := cycleCount_eq _ σ
  have hcc_small : cycleCount (2*n) ((pPrimeO p).1 * (pPrimeO q).1)
      = (2*n - ((pPrimeO p).1 * (pPrimeO q).1).cycleType.sum)
        + ((pPrimeO p).1 * (pPrimeO q).1).cycleType.card := cycleCount_eq _ _
  rw [← hcteq] at hcc_small
  have hccrel : cycleCount (2*(n+1)) σ = cycleCount (2*n) ((pPrimeO p).1 * (pPrimeO q).1) + 2 := by
    rw [hcc_big, hcc_small]; omega
  -- convert to loops
  have h1 : 2 * p.loops q = cycleCount (2*(n+1)) (p.1 * q.1) := loops_two_mul p q
  have h2 : 2 * (pPrimeO p).loops (pPrimeO q)
      = cycleCount (2*n) ((pPrimeO p).1 * (pPrimeO q).1) := loops_two_mul _ _
  rw [← hσ] at h1
  omega

/-- In the two-loop case the two transported indices agree (`q.1 0 = p.1 0`). -/
theorem idxOf_q_eq_p (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    idxOf (M := M) q rest = idxOf (M := M) p rest := by
  funext i
  unfold idxOf
  congr 1
  apply Subtype.ext
  exact sEquiv_val_eq (q.2.2 0) (p.2.2 0) hbc.symm i

/-- The double-subtype survivor equiv `Fin (2n) ≃ {s : {j ≠ 0} // s ≠ ⟨b⟩}` (`b = p.1 0`). -/
noncomputable def dblE (p : Pairing (n+1)) :
    Fin (2*n) ≃ {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} :=
  (sEquiv (p.1 0) (p.2.2 0)).trans
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (congrArg Subtype.val h)⟩
      invFun := fun s => ⟨s.1.1, ⟨s.1.2, fun h => s.2 (Subtype.ext h)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The transported index `idxOf p restg` equals `g ∘ dblE p`. -/
theorem idxOf_funSplit_eq (p : Pairing (n+1)) (w₀ : Fin (2*M))
    (g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M)) :
    idxOf (M := M) p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g))
      = fun i => g (dblE p i) := by
  funext i
  unfold idxOf
  set svr : {j : Fin (2*(n+1)) // j ≠ 0} :=
    ⟨(sEquiv (p.1 0) (p.2.2 0) i : Fin (2*(n+1))), (sEquiv_mem (p.1 0) (p.2.2 0) i).1⟩ with hsvr
  have hne : svr ≠ ⟨p.1 0, p.2.2 0⟩ :=
    fun h => (sEquiv_mem (p.1 0) (p.2.2 0) i).2 (congrArg Subtype.val h)
  show (Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g) svr
      = g (⟨svr, hne⟩ : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩})
  simp [Equiv.funSplitAt, Equiv.piSplitAt, hne]

end TwoLoopResidual

/-- **Two-loop residual** (case `p 0 = q 0`): after extracting the free `2*M` factor at the merged
vertex (`two_loop_branch`), the `Fin (2*n)`-reindexed contraction sum, scaled by `2*M`, hits the
closed form at level `n+1`. The reduced pair `(p',q')` deletes `{0, b}` (an isolated `2`-loop of
`p ∪ q`), so `p.loops q = p'.loops q' + 1` and the sign is unchanged. Numerically verified
(`n ≤ 3`, `M ≤ 2`). The genuine combinatorial core of the two-loop case. -/
theorem two_loop_residual (M : ℕ) {n : ℕ}
    (IH : ∀ (p' q' : Pairing n),
      ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p' i * deltaContr M q' i
        = epsVec ℤ p' * epsVec ℤ q' * (-1) ^ n * (-(2 * (M : ℤ))) ^ p'.loops q')
    (p q : Pairing (n+1)) (hbc : p.1 0 = q.1 0) (w₀ : Fin (2*M)) :
    (2*M) • (∑ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
        EP M n p (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g)))
          * EP M n q (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g))))
      = epsVec ℤ p * epsVec ℤ q * (-1) ^ (n+1) * (-(2 * (M : ℤ))) ^ p.loops q := by
  -- Step 1: rewrite each summand via the bridges into a reduced contraction product of g∘dblE
  have hsummand : ∀ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
      EP M n p (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g)))
        * EP M n q (reLift M n p ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm (w₀, g)))
      = deltaContr M (pPrimeO p) (fun i => g (dblE p i))
        * deltaContr M (pPrimeO q) (fun i => g (dblE p i)) := by
    intro g
    rw [EP_eq_deltaContr M n p _, EP_q_eq_deltaContr M n p q hbc _,
        idxOf_q_eq_p p q hbc, idxOf_funSplit_eq p w₀ g]
  simp_rw [hsummand]
  -- Step 2: reindex ∑_g F(g ∘ dblE) = ∑_idx F(idx)
  rw [show (∑ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
        deltaContr M (pPrimeO p) (fun i => g (dblE p i))
          * deltaContr M (pPrimeO q) (fun i => g (dblE p i)))
      = ∑ idx : Fin (2*n) → Fin (2*M),
          deltaContr M (pPrimeO p) idx * deltaContr M (pPrimeO q) idx from by
    rw [← Equiv.sum_comp (Equiv.arrowCongr (dblE p).symm (Equiv.refl (Fin (2*M))))
        (fun idx => deltaContr M (pPrimeO p) idx * deltaContr M (pPrimeO q) idx)]
    apply Finset.sum_congr rfl
    intro g _
    have hg : (fun i => g (dblE p i))
        = (Equiv.arrowCongr (dblE p).symm (Equiv.refl (Fin (2*M)))) g := by
      funext i
      show g (dblE p i) = _
      rw [Equiv.arrowCongr_apply]
      simp
    rw [hg]]
  -- Step 3: apply IH and assemble
  rw [IH (pPrimeO p) (pPrimeO q), loops_two_loop p q hbc, two_loop_sign p q hbc]
  rw [pow_succ, nsmul_eq_mul]
  push_cast
  ring

/-! ### Merge-residual infrastructure (qStar rewiring, EP bridge, loops invariance, sign). -/
section MergeResidual
open Equiv Equiv.Perm Finset
variable {n : ℕ}

/-! ## qStar block -/
def qStarFun (p q : Pairing (n+1)) : Fin (2*(n+1)) → Fin (2*(n+1)) := fun v =>
  if v = 0 then p.1 0
  else if v = p.1 0 then 0
  else if v = q.1 0 then q.1 (p.1 0)
  else if v = q.1 (p.1 0) then q.1 0
  else q.1 v

theorem qStar_facts (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    p.1 0 ≠ 0 ∧ q.1 0 ≠ 0 ∧ q.1 (p.1 0) ≠ 0 ∧ q.1 (p.1 0) ≠ p.1 0 ∧
    q.1 0 ≠ p.1 0 ∧ q.1 (p.1 0) ≠ q.1 0 := by
  refine ⟨p.2.2 0, q.2.2 0, ?_, q.2.2 _, fun h => hbc h.symm, ?_⟩
  · intro h
    have h2 : q.1 (q.1 (p.1 0)) = q.1 0 := by rw [h]
    rw [pairing_invol] at h2; exact hbc h2
  · intro h
    have : p.1 0 = (0 : Fin (2*(n+1))) := q.1.injective h
    exact (p.2.2 0) this

theorem qStarFun_invol (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    Function.Involutive (qStarFun p q) := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  have hqd : q.1 (q.1 (p.1 0)) = p.1 0 := pairing_invol q (p.1 0)
  have hqc : q.1 (q.1 0) = 0 := pairing_invol q 0
  have E0 : ∀ v, q.1 v = 0 ↔ v = q.1 0 := fun v => by
    constructor
    · intro h; have := pairing_invol q v; rw [h] at this; exact this.symm
    · intro h; rw [h, hqc]
  have Eb : ∀ v, q.1 v = p.1 0 ↔ v = q.1 (p.1 0) := fun v => by
    constructor
    · intro h; have := pairing_invol q v; rw [h] at this; exact this.symm
    · intro h; rw [h, hqd]
  have Ec : ∀ v, q.1 v = q.1 0 ↔ v = 0 := fun v => ⟨fun h => q.1.injective h, fun h => by rw [h]⟩
  have Ed : ∀ v, q.1 v = q.1 (p.1 0) ↔ v = p.1 0 := fun v => ⟨fun h => q.1.injective h, fun h => by rw [h]⟩
  intro v
  show qStarFun p q (qStarFun p q v) = v
  unfold qStarFun
  by_cases h1 : v = 0
  · subst h1; rw [if_pos rfl, if_neg hb0, if_pos rfl]
  · by_cases h2 : v = p.1 0
    · subst h2; rw [if_neg hb0, if_pos rfl, if_pos rfl]
    · by_cases h3 : v = q.1 0
      · subst h3
        rw [if_neg hc0, if_neg hcb, if_pos rfl, if_neg hd0, if_neg hdb, if_neg hdc, if_pos rfl]
      · by_cases h4 : v = q.1 (p.1 0)
        · subst h4
          rw [if_neg hd0, if_neg hdb, if_neg hdc, if_pos rfl, if_neg hc0, if_neg hcb, if_pos rfl]
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          have e0 : q.1 v ≠ 0 := fun h => h3 ((E0 v).mp h)
          have eb : q.1 v ≠ p.1 0 := fun h => h4 ((Eb v).mp h)
          have ec : q.1 v ≠ q.1 0 := fun h => h1 ((Ec v).mp h)
          have ed : q.1 v ≠ q.1 (p.1 0) := fun h => h2 ((Ed v).mp h)
          rw [if_neg e0, if_neg eb, if_neg ec, if_neg ed, pairing_invol]

theorem qStarFun_ff (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    ∀ v, qStarFun p q v ≠ v := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  intro v
  unfold qStarFun
  by_cases h1 : v = 0
  · subst h1; rw [if_pos rfl]; exact hb0
  · by_cases h2 : v = p.1 0
    · subst h2; rw [if_neg hb0, if_pos rfl]; exact fun h => hb0 h.symm
    · by_cases h3 : v = q.1 0
      · subst h3; rw [if_neg hc0, if_neg hcb, if_pos rfl]; exact hdc
      · by_cases h4 : v = q.1 (p.1 0)
        · subst h4; rw [if_neg hd0, if_neg hdb, if_neg hdc, if_pos rfl]; exact fun h => hdc h.symm
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; exact q.2.2 v

noncomputable def qStar (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) : Pairing (n+1) :=
  ⟨(qStarFun_invol p q hbc).toPerm, by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Function.Involutive.coe_toPerm]
    exact congrArg _ (qStarFun_invol p q hbc x), by
    intro x
    simp only [Function.Involutive.coe_toPerm, ne_eq]
    exact qStarFun_ff p q hbc x⟩

theorem qStar_apply (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) (v) :
    (qStar p q hbc).1 v = qStarFun p q v := rfl

theorem qStar_zero (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (qStar p q hbc).1 0 = p.1 0 := by
  rw [qStar_apply]; unfold qStarFun; rw [if_pos rfl]

theorem reLift_qStar_eq {M : ℕ} (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    reLift M n (qStar p q hbc) rest = reLift M n p rest := by
  funext a
  by_cases ha : a = 0
  · subst ha
    rw [reLift_zero, reLift_zero]
    exact congrArg rest (Subtype.ext (qStar_zero p q hbc))
  · rw [reLift_ne _ _ _ _ ha, reLift_ne _ _ _ _ ha]

/-! ## sum_indicator_merge -/
theorem sum_indicator_merge {S : Type*} [Fintype S] [DecidableEq S]
    {W : Type*} [Fintype W] [DecidableEq W]
    (a a' : S) (ha' : a' ≠ a) {R : Type*} [AddCommMonoid R] (F : (S → W) → R)
    (hindep : ∀ (f : S → W) (x : W), F (Function.update f a x) = F f) :
    (∑ f : S → W, (if f a = f a' then F f else 0))
      = (∑ g : {s : S // s ≠ a} → W,
          F ((Equiv.funSplitAt a W).symm (g ⟨a', ha'⟩, g))) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt a W).symm (fun f => (if f a = f a' then F f else 0)),
      Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have hval_a : ∀ w : W, (Equiv.funSplitAt a W).symm (w, g) a = w := by
    intro w; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hval_a' : ∀ w : W, (Equiv.funSplitAt a W).symm (w, g) a' = g ⟨a', ha'⟩ := by
    intro w; simp [Equiv.funSplitAt, Equiv.piSplitAt, ha']
  have hFconst : ∀ w : W,
      F ((Equiv.funSplitAt a W).symm (w, g)) = F ((Equiv.funSplitAt a W).symm (g ⟨a', ha'⟩, g)) := by
    intro w
    have h1 : (Equiv.funSplitAt a W).symm (w, g)
        = Function.update ((Equiv.funSplitAt a W).symm (g ⟨a', ha'⟩, g)) a w := by
      funext s
      by_cases hs : s = a
      · subst hs; rw [Function.update_self]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
      · rw [Function.update_of_ne hs]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hs]
    rw [h1, hindep]
  simp_rw [hval_a, hval_a', hFconst]
  rw [Finset.sum_ite_eq' Finset.univ (g ⟨a', ha'⟩) (fun _ => F ((Equiv.funSplitAt a W).symm (g ⟨a', ha'⟩, g)))]
  rw [if_pos (Finset.mem_univ _)]

/-! ## EP_prod_all, flipQ, EP_q_eq_flip_EP_qStar -/
theorem EP_prod_all (M : ℕ) (r : Pairing (n+1)) (i : Fin (2*(n+1)) → Fin (2*M)) :
    EP M n r i = ∏ a : Fin (2*(n+1)),
        (if a ≠ 0 ∧ a < r.1 a then Jform M (i a) (i (r.1 a)) else 1) := by
  unfold EP
  rw [← Finset.prod_filter]
  apply Finset.prod_congr _ (fun a _ => rfl)
  ext a
  rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨h1, _, h2⟩; exact ⟨Finset.mem_univ _, h1, h2⟩
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, Finset.mem_univ _, h2⟩

noncomputable def flipQ (p q : Pairing (n+1)) : ℤ :=
  if (p.1 0 < q.1 (p.1 0) ↔ q.1 0 < q.1 (p.1 0)) then 1 else -1

set_option maxHeartbeats 1000000 in
theorem EP_q_eq_flip_EP_qStar (M : ℕ) (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (i : Fin (2*(n+1)) → Fin (2*M)) (hibc : i (p.1 0) = i (q.1 0)) :
    EP M n q i = flipQ p q * EP M n (qStar p q hbc) i := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  set b := p.1 0 with hbdef
  set c := q.1 0 with hcdef
  set d := q.1 (p.1 0) with hddef
  set S := ({0, b, c, d} : Finset (Fin (2*(n+1)))) with hS
  rw [EP_prod_all M q i, EP_prod_all M (qStar p q hbc) i]
  set gQ : Fin (2*(n+1)) → ℤ :=
    fun a => if a ≠ 0 ∧ a < q.1 a then Jform M (i a) (i (q.1 a)) else 1 with hgQ
  set gQs : Fin (2*(n+1)) → ℤ :=
    fun a => if a ≠ 0 ∧ a < (qStar p q hbc).1 a then Jform M (i a) (i ((qStar p q hbc).1 a)) else 1 with hgQs
  have hqs_off : ∀ a, a ∉ S → (qStar p q hbc).1 a = q.1 a := by
    intro a ha
    rw [hS] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    obtain ⟨ha0, hab, hac, had⟩ := ha
    rw [qStar_apply]; unfold qStarFun
    rw [if_neg ha0, if_neg (by rw [← hbdef]; exact hab), if_neg (by rw [← hcdef]; exact hac),
        if_neg (by rw [← hddef]; exact had)]
  have hoff : ∀ a, a ∉ S → gQ a = gQs a := by
    intro a ha
    simp only [hgQ, hgQs]
    rw [hqs_off a ha]
  rw [← Finset.prod_mul_prod_compl S gQ, ← Finset.prod_mul_prod_compl S gQs]
  have hcompl : (∏ a ∈ Sᶜ, gQ a) = (∏ a ∈ Sᶜ, gQs a) := by
    apply Finset.prod_congr rfl
    intro a ha; rw [Finset.mem_compl] at ha; exact hoff a ha
  rw [hcompl]
  suffices hsp : (∏ a ∈ S, gQ a) = flipQ p q * (∏ a ∈ S, gQs a) by rw [hsp]; ring
  have hexp : ∀ (g : Fin (2*(n+1)) → ℤ), (∏ a ∈ S, g a) = g 0 * g b * g c * g d := by
    intro g
    rw [hS, show ({0, b, c, d} : Finset (Fin (2*(n+1)))) = insert 0 (insert b (insert c {d})) from rfl]
    rw [Finset.prod_insert (by simp [Ne.symm hb0, Ne.symm hc0, Ne.symm hd0]),
        Finset.prod_insert (by simp [hbc, Ne.symm hdb]),
        Finset.prod_insert (by simp [Ne.symm hdc]),
        Finset.prod_singleton]
    ring
  rw [hexp gQ, hexp gQs]
  have hgQ0 : gQ 0 = 1 := by simp only [hgQ]; rw [if_neg]; rintro ⟨h0, _⟩; exact h0 rfl
  have hgQb : gQ b = (if b < d then Jform M (i b) (i d) else 1) := by
    simp only [hgQ]
    have hh : q.1 b = d := by rw [hbdef, hddef]
    rw [hh]
    by_cases h : b < d
    · rw [if_pos ⟨hb0, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h]
  have hgQc : gQ c = 1 := by
    simp only [hgQ]
    have hh : q.1 c = 0 := by rw [hcdef]; exact pairing_invol q 0
    rw [if_neg]; rintro ⟨_, hlt⟩; rw [hh] at hlt; exact absurd hlt (Fin.not_lt_zero c)
  have hgQd : gQ d = (if d < b then Jform M (i d) (i b) else 1) := by
    simp only [hgQ]
    have hh : q.1 d = b := by rw [hddef, hbdef]; exact pairing_invol q (p.1 0)
    rw [hh]
    by_cases h : d < b
    · rw [if_pos ⟨hd0, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h]
  have hgQs0 : gQs 0 = 1 := by simp only [hgQs]; rw [if_neg]; rintro ⟨h0, _⟩; exact h0 rfl
  have hgQsb : gQs b = 1 := by
    simp only [hgQs]
    have hh : (qStar p q hbc).1 b = 0 := by
      rw [qStar_apply]; unfold qStarFun; rw [if_neg hb0, if_pos hbdef.symm]
    rw [if_neg]; rintro ⟨_, hlt⟩; rw [hh] at hlt; exact absurd hlt (Fin.not_lt_zero b)
  have hgQsc : gQs c = (if c < d then Jform M (i c) (i d) else 1) := by
    simp only [hgQs]
    have hh : (qStar p q hbc).1 c = d := by
      rw [qStar_apply]; unfold qStarFun
      rw [if_neg hc0, if_neg (by rw [hcdef]; exact hcb), if_pos hcdef.symm, hddef]
    rw [hh]
    by_cases h : c < d
    · rw [if_pos ⟨hc0, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h]
  have hgQsd : gQs d = (if d < c then Jform M (i d) (i c) else 1) := by
    simp only [hgQs]
    have hh : (qStar p q hbc).1 d = c := by
      rw [qStar_apply]; unfold qStarFun
      rw [if_neg hd0, if_neg (by rw [hddef]; exact hdb), if_neg (by rw [hddef]; exact hdc),
          if_pos hddef.symm, hcdef]
    rw [hh]
    by_cases h : d < c
    · rw [if_pos ⟨hd0, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h]
  rw [hgQ0, hgQb, hgQc, hgQd, hgQs0, hgQsb, hgQsc, hgQsd]
  have hbd_ne : b ≠ d := Ne.symm hdb
  have hcd_ne : c ≠ d := Ne.symm hdc
  have hcomb_q : (if b < d then Jform M (i b) (i d) else (1:ℤ))
      * (if d < b then Jform M (i d) (i b) else (1:ℤ))
      = if b < d then Jform M (i b) (i d) else Jform M (i d) (i b) := by
    rcases lt_or_gt_of_ne hbd_ne with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_pos h, mul_one]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (not_lt.mpr h.le), one_mul]
  have hcomb_qs : (if c < d then Jform M (i c) (i d) else (1:ℤ))
      * (if d < c then Jform M (i d) (i c) else (1:ℤ))
      = if c < d then Jform M (i c) (i d) else Jform M (i d) (i c) := by
    rcases lt_or_gt_of_ne hcd_ne with h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), if_pos h, mul_one]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, if_neg (not_lt.mpr h.le), one_mul]
  have hibc' : i b = i c := by rw [hbdef, hcdef]; exact hibc
  have hflip : (if b < d then Jform M (i b) (i d) else Jform M (i d) (i b))
      = flipQ p q * (if c < d then Jform M (i c) (i d) else Jform M (i d) (i c)) := by
    rw [flipQ]
    show (if b < d then Jform M (i b) (i d) else Jform M (i d) (i b))
      = (if (b < d ↔ c < d) then (1:ℤ) else -1)
        * (if c < d then Jform M (i c) (i d) else Jform M (i d) (i c))
    rw [hibc']
    by_cases hb' : b < d <;> by_cases hc' : c < d
    · rw [if_pos hb', if_pos hc', if_pos (by tauto), one_mul]
    · rw [if_pos hb', if_neg hc', if_neg (by tauto)]
      rw [Jform_antisymm M (i d) (i c)]; ring
    · rw [if_neg hb', if_pos hc', if_neg (by tauto)]
      rw [Jform_antisymm M (i d) (i c)]; ring
    · rw [if_neg hb', if_neg hc', if_pos (by tauto), one_mul]
  rw [show (1 : ℤ) * (if b < d then Jform M (i b) (i d) else 1) * 1
          * (if d < b then Jform M (i d) (i b) else 1)
        = (if b < d then Jform M (i b) (i d) else 1) * (if d < b then Jform M (i d) (i b) else 1) from by ring]
  rw [show (flipQ p q) * (1 * 1 * (if c < d then Jform M (i c) (i d) else 1)
          * (if d < c then Jform M (i d) (i c) else 1))
        = (flipQ p q) * ((if c < d then Jform M (i c) (i d) else 1)
          * (if d < c then Jform M (i d) (i c) else 1)) from by ring]
  rw [hcomb_q, hcomb_qs, hflip]


/-! ## Loops invariance for the merge -/
theorem pqStar_fix_zero (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (p.1 * (qStar p q hbc).1) 0 = 0 := by
  rw [Equiv.Perm.mul_apply, qStar_zero]; exact pairing_invol p 0

theorem pqStar_fix_b (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (p.1 * (qStar p q hbc).1) (p.1 0) = p.1 0 := by
  rw [Equiv.Perm.mul_apply]
  have hqsb : (qStar p q hbc).1 (p.1 0) = 0 := by
    rw [qStar_apply]; unfold qStarFun
    rw [if_neg (p.2.2 0), if_pos rfl]
  rw [hqsb]

-- q*.1 = swap(c)(b) * swap(0)(d) * q.1   (perm-level)
theorem qStar_eq_swaps (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (qStar p q hbc).1
      = Equiv.swap (q.1 0) (p.1 0) * Equiv.swap (0 : Fin (2*(n+1))) (q.1 (p.1 0)) * q.1 := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  have hqd : q.1 (q.1 (p.1 0)) = p.1 0 := pairing_invol q (p.1 0)
  have hqc : q.1 (q.1 0) = 0 := pairing_invol q 0
  have hinj := q.1.injective
  ext v
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [qStar_apply]; unfold qStarFun
  by_cases h1 : v = 0
  · subst h1
    rw [if_pos rfl]
    -- RHS: swap(c)(b)(swap(0)(d)(q 0)); q0=c; inner: c≠0,c≠d → c; outer swap(c)(b)(c)=b
    rw [Equiv.swap_apply_of_ne_of_ne hc0 (Ne.symm hdc), Equiv.swap_apply_left]
  · by_cases h2 : v = p.1 0
    · subst h2
      rw [if_neg hb0, if_pos rfl]
      -- RHS: q(p0)=d; inner swap(0)(d)(d)=0; outer swap(c)(b)(0)=0 (0≠c,0≠b)
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hc0) (Ne.symm hb0)]
    · by_cases h3 : v = q.1 0
      · subst h3
        rw [if_neg hc0, if_neg hcb, if_pos rfl]
        -- RHS: q(q0)=0; inner swap(0)(d)(0)=d; outer swap(c)(b)(d)=d (d≠c,d≠b)
        rw [hqc, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hdc hdb]
      · by_cases h4 : v = q.1 (p.1 0)
        · subst h4
          rw [if_neg hd0, if_neg hdb, if_neg hdc, if_pos rfl]
          -- RHS: q(d)=q(q(p0))=p0=b; inner swap(0)(d)(b)=b (b≠0,b≠d); outer swap(c)(b)(b)=c
          rw [hqd, Equiv.swap_apply_of_ne_of_ne hb0 (Ne.symm hdb), Equiv.swap_apply_right]
        · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          have e0 : q.1 v ≠ 0 := fun h => h3 (by have := pairing_invol q v; rw [h] at this; exact this.symm)
          have eb : q.1 v ≠ p.1 0 := fun h => h4 (by have := pairing_invol q v; rw [h] at this; exact this.symm)
          have ec : q.1 v ≠ q.1 0 := fun h => h1 (hinj h)
          have ed : q.1 v ≠ q.1 (p.1 0) := fun h => h2 (hinj h)
          rw [Equiv.swap_apply_of_ne_of_ne e0 ed, Equiv.swap_apply_of_ne_of_ne ec eb]

-- swap decomposition of p*q from p*q*
theorem pq_swap_decomp (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    p.1 * q.1 = Equiv.swap (p.1 0) (p.1 (q.1 (p.1 0))) * Equiv.swap (p.1 (q.1 0)) 0
        * (p.1 * (qStar p q hbc).1) := by
  -- from qStar_eq_swaps: q* = sc * sd * q with sc=swap(c)(b), sd=swap(0)(d); invert: q = sd*sc*q*
  have hsc : (Equiv.swap (q.1 0) (p.1 0)) * (Equiv.swap (q.1 0) (p.1 0)) = 1 := Equiv.swap_mul_self _ _
  have hsd : (Equiv.swap (0:Fin (2*(n+1))) (q.1 (p.1 0))) * (Equiv.swap (0:Fin (2*(n+1))) (q.1 (p.1 0))) = 1 :=
    Equiv.swap_mul_self _ _
  have hqeq : q.1 = Equiv.swap (0:Fin (2*(n+1))) (q.1 (p.1 0)) * Equiv.swap (q.1 0) (p.1 0)
      * (qStar p q hbc).1 := by
    rw [qStar_eq_swaps p q hbc]
    -- sd*sc*(sc*sd*q) = q
    set sc := Equiv.swap (q.1 0) (p.1 0)
    set sd := Equiv.swap (0:Fin (2*(n+1))) (q.1 (p.1 0))
    calc q.1 = (sd * sd) * q.1 := by rw [hsd, one_mul]
      _ = sd * ((sc * sc) * (sd * q.1)) := by rw [hsc, one_mul]; group
      _ = sd * sc * (sc * sd * q.1) := by group
  conv_lhs => rw [hqeq]
  rw [← mul_assoc, ← mul_assoc]
  -- p.1 * swap(0)(d) = swap(p0)(pd)*p.1 ; then *swap(c)(b) = swap(p0)(pd)*swap(pc)(pb)*p.1
  rw [mul_swap_eq_swap_mul p.1 (0:Fin (2*(n+1))) (q.1 (p.1 0))]
  rw [mul_assoc (Equiv.swap (p.1 0) (p.1 (q.1 (p.1 0)))) p.1 (Equiv.swap (q.1 0) (p.1 0))]
  rw [mul_swap_eq_swap_mul p.1 (q.1 0) (p.1 0)]
  -- p.1 (p.1 0) = 0
  rw [show p.1 (p.1 0) = 0 from pairing_invol p 0]
  simp only [mul_assoc]

/-! ## cycleCount +2 and loops invariance for the merge. -/

theorem cycleCount_pqStar (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    cycleCount (2*(n+1)) (p.1 * (qStar p q hbc).1)
      = cycleCount (2*(n+1)) (p.1 * q.1) + 2 := by
  set σ := p.1 * (qStar p q hbc).1 with hσ
  -- abbreviations (NOT set, to keep pd = p.1 (q.1 (p.1 0)) literal)
  -- fixed points
  have hfix0 : σ 0 = 0 := pqStar_fix_zero p q hbc
  have hfixb : σ (p.1 0) = p.1 0 := pqStar_fix_b p q hbc
  have hb0 : p.1 0 ≠ 0 := p.2.2 0
  -- distinctness: 0 ≠ p.1 (q.1 0)
  have h0pc : (0 : Fin (2*(n+1))) ≠ p.1 (q.1 0) := by
    intro h
    have hq0 : q.1 0 = p.1 0 := by
      apply p.1.injective
      rw [pairing_invol p 0, ← h]
    exact hbc hq0.symm
  -- distinctness: p.1 0 ≠ p.1 (q.1 (p.1 0))
  have hbpd : p.1 0 ≠ p.1 (q.1 (p.1 0)) := by
    intro h
    have hd0 : q.1 (p.1 0) = (0 : Fin (2*(n+1))) := by
      apply p.1.injective
      exact h.symm
    have hcontra : p.1 0 = q.1 0 := by
      have h3 := pairing_invol q (p.1 0)
      rw [hd0] at h3
      exact h3.symm
    exact hbc hcontra
  -- swap symmetry
  have hsw1 : Equiv.swap (p.1 (q.1 0)) (0 : Fin (2*(n+1)))
      = Equiv.swap (0 : Fin (2*(n+1))) (p.1 (q.1 0)) := Equiv.swap_comm _ _
  -- step 1
  have hstep1 := RSS.gcount_swap_mul σ (0 : Fin (2*(n+1))) (p.1 (q.1 0)) hfix0 h0pc
  -- the inner perm fixes p.1 0
  have hbpc : p.1 0 ≠ p.1 (q.1 0) := by
    intro h
    have : (0 : Fin (2*(n+1))) = q.1 0 := p.1.injective h
    exact (q.2.2 0) this.symm
  have hfixb_inner : (Equiv.swap (0 : Fin (2*(n+1))) (p.1 (q.1 0)) * σ) (p.1 0) = p.1 0 := by
    rw [Equiv.Perm.mul_apply, hfixb, Equiv.swap_apply_of_ne_of_ne hb0 hbpc]
  -- step 2
  have hstep2 := RSS.gcount_swap_mul (Equiv.swap (0 : Fin (2*(n+1))) (p.1 (q.1 0)) * σ)
    (p.1 0) (p.1 (q.1 (p.1 0))) hfixb_inner hbpd
  -- decomp
  have hdecomp : p.1 * q.1
      = Equiv.swap (p.1 0) (p.1 (q.1 (p.1 0))) * (Equiv.swap (0:Fin (2*(n+1))) (p.1 (q.1 0)) * σ) := by
    rw [pq_swap_decomp p q hbc, ← hσ, hsw1, mul_assoc]
  rw [RSS.cycleCount_eq_gcount, RSS.cycleCount_eq_gcount, hdecomp]
  omega

theorem loops_pqStar (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    p.loops (qStar p q hbc) = p.loops q + 1 := by
  have h1 : 2 * p.loops (qStar p q hbc) = cycleCount (2*(n+1)) (p.1 * (qStar p q hbc).1) :=
    loops_two_mul p (qStar p q hbc)
  have h2 : 2 * p.loops q = cycleCount (2*(n+1)) (p.1 * q.1) := loops_two_mul p q
  have h3 := cycleCount_pqStar p q hbc
  omega

/-! ### Bridge: equal mod-2 ⇒ equal (-1)^ -/
theorem negpow_of_zmod (a b : ℕ) (h : ((a : ℕ) : ZMod 2) = ((b : ℕ) : ZMod 2)) :
    (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := by rw [Nat.even_iff] at *; omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd b := by rw [Nat.odd_iff] at *; omega
    rw [ha.neg_one_pow, hb.neg_one_pow]

/-! ### crInd, memI, crossings_zmod -/
def crInd (r : Pairing (n+1)) (ac : Fin (2*(n+1)) × Fin (2*(n+1))) : ZMod 2 :=
  if ac.1 < r.1 ac.1 ∧ ac.2 < r.1 ac.2 ∧ ac.1 < ac.2 ∧ ac.2 < r.1 ac.1 ∧ r.1 ac.1 < r.1 ac.2
  then 1 else 0

def memI (x x' v : Fin (2*(n+1))) : ZMod 2 := if x < v ∧ v < x' then 1 else 0

theorem crossings_zmod (r : Pairing (n+1)) :
    ((r.crossings : ℕ) : ZMod 2) = ∑ ac : Fin (2*(n+1)) × Fin (2*(n+1)), crInd r ac := by
  show ((((Finset.univ : Finset (Fin (2*(n+1)) × Fin (2*(n+1)))).filter fun ac =>
      ac.1 < r.1 ac.1 ∧ ac.2 < r.1 ac.2 ∧
      ac.1 < ac.2 ∧ ac.2 < r.1 ac.1 ∧ r.1 ac.1 < r.1 ac.2).card : ℕ) : ZMod 2)
      = ∑ ac : Fin (2*(n+1)) × Fin (2*(n+1)), crInd r ac
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ac _
  simp only [crInd]
  split <;> simp

theorem qStar_off (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) (v)
    (h0 : v ≠ 0) (hb : v ≠ p.1 0) (hc : v ≠ q.1 0) (hd : v ≠ q.1 (p.1 0)) :
    (qStar p q hbc).1 v = q.1 v := by
  rw [qStar_apply]; unfold qStarFun; rw [if_neg h0, if_neg hb, if_neg hc, if_neg hd]

theorem crInd_eq_off_V (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (ac : Fin (2*(n+1)) × Fin (2*(n+1)))
    (h1 : ac.1 ≠ 0 ∧ ac.1 ≠ p.1 0 ∧ ac.1 ≠ q.1 0 ∧ ac.1 ≠ q.1 (p.1 0))
    (h2 : ac.2 ≠ 0 ∧ ac.2 ≠ p.1 0 ∧ ac.2 ≠ q.1 0 ∧ ac.2 ≠ q.1 (p.1 0)) :
    crInd (qStar p q hbc) ac = crInd q ac := by
  simp only [crInd]
  rw [qStar_off p q hbc ac.1 h1.1 h1.2.1 h1.2.2.1 h1.2.2.2,
      qStar_off p q hbc ac.2 h2.1 h2.2.1 h2.2.2.1 h2.2.2.2]

/-! ### order_id, gChord -/
theorem order_idN (x x' α β : ℕ) (hxx' : x < x') (hαβ : α < β)
    (hxa : x ≠ α) (hxb : x ≠ β) (hxa' : x' ≠ α) (hxb' : x' ≠ β) :
    (if x < α ∧ α < x' ∧ x' < β then (1:ZMod 2) else 0)
      + (if α < x ∧ x < β ∧ β < x' then 1 else 0)
      = (if x < α ∧ α < x' then 1 else 0) + (if x < β ∧ β < x' then 1 else 0) := by
  by_cases h1 : x < α ∧ α < x'
  · obtain ⟨h1a, h1b⟩ := h1
    by_cases h2 : x < β ∧ β < x'
    · obtain ⟨h2a, h2b⟩ := h2
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1a,h1b⟩, if_pos ⟨h2a,h2b⟩]
      decide
    · have hnb : ¬ (x < β ∧ β < x') := h2
      rw [not_and_or] at h2
      have hxlb : x < β := by omega
      have hx'β2 : x' < β := by
        rcases h2 with h2 | h2
        · exact absurd hxlb h2
        · omega
      have n2 : ¬ (α < x ∧ x < β ∧ β < x') := by omega
      rw [if_pos ⟨h1a, h1b, hx'β2⟩, if_neg n2, if_pos ⟨h1a,h1b⟩, if_neg hnb]
  · by_cases h2 : x < β ∧ β < x'
    · obtain ⟨h2a, h2b⟩ := h2
      have hax : α < x := by by_contra hc; exact h1 ⟨by omega, by omega⟩
      have n1 : ¬ (x < α ∧ α < x' ∧ x' < β) := by omega
      have n3 : ¬ (x < α ∧ α < x') := fun hc => h1 hc
      rw [if_neg n1, if_pos ⟨hax, h2a, h2b⟩, if_neg n3, if_pos ⟨h2a,h2b⟩]
    · have n1 : ¬ (x < α ∧ α < x' ∧ x' < β) := fun hc => h1 ⟨hc.1, hc.2.1⟩
      have n2 : ¬ (α < x ∧ x < β ∧ β < x') := fun hc => h2 ⟨hc.2.1, hc.2.2⟩
      rw [if_neg n1, if_neg n2, if_neg h1, if_neg h2]

theorem order_id (x x' α β : Fin (2*(n+1))) (hxx' : x < x') (hαβ : α < β)
    (hxa : x ≠ α) (hxb : x ≠ β) (hxa' : x' ≠ α) (hxb' : x' ≠ β) :
    (if x < α ∧ α < x' ∧ x' < β then (1:ZMod 2) else 0)
      + (if α < x ∧ x < β ∧ β < x' then 1 else 0)
      = (if x < α ∧ α < x' then 1 else 0) + (if x < β ∧ β < x' then 1 else 0) := by
  simp only [Fin.lt_def]
  refine order_idN x.val x'.val α.val β.val hxx' hαβ ?_ ?_ ?_ ?_
  · exact fun h => hxa (Fin.val_injective h)
  · exact fun h => hxb (Fin.val_injective h)
  · exact fun h => hxa' (Fin.val_injective h)
  · exact fun h => hxb' (Fin.val_injective h)

theorem gChord (r : Pairing (n+1)) (x α β : Fin (2*(n+1)))
    (hxl : x < r.1 x) (hrβ : r.1 α = β)
    (hxα : x ≠ α) (hxβ : x ≠ β) (hx'α : r.1 x ≠ α) (hx'β : r.1 x ≠ β) :
    crInd r (x, α) + crInd r (α, x) + crInd r (x, β) + crInd r (β, x)
      = memI x (r.1 x) α + memI x (r.1 x) β := by
  have hαβ : α ≠ β := by intro h; rw [h] at hrβ; exact (r.2.2 β) hrβ
  have hrα : r.1 β = α := by rw [← hrβ, pairing_invol]
  have e1 : crInd r (x, α) = if x < r.1 x ∧ α < β ∧ x < α ∧ α < r.1 x ∧ r.1 x < β then (1:ZMod 2) else 0 := by
    simp only [crInd, hrβ]
  have e2 : crInd r (α, x) = if α < β ∧ x < r.1 x ∧ α < x ∧ x < r.1 α ∧ r.1 α < r.1 x then (1:ZMod 2) else 0 := by
    simp only [crInd, hrβ]
  have e3 : crInd r (x, β) = if x < r.1 x ∧ β < α ∧ x < β ∧ β < r.1 x ∧ r.1 x < α then (1:ZMod 2) else 0 := by
    simp only [crInd, hrα]
  have e4 : crInd r (β, x) = if β < α ∧ x < r.1 x ∧ β < x ∧ x < r.1 β ∧ r.1 β < r.1 x then (1:ZMod 2) else 0 := by
    simp only [crInd, hrα]
  rw [hrβ] at e2; rw [hrα] at e4
  simp only [memI]
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have z3 : crInd r (x, β) = 0 := by rw [e3]; exact if_neg (by rintro ⟨_,h,_⟩; exact absurd h (not_lt.mpr (le_of_lt hlt)))
    have z4 : crInd r (β, x) = 0 := by rw [e4]; exact if_neg (by rintro ⟨h,_⟩; exact absurd h (not_lt.mpr (le_of_lt hlt)))
    have c1 : crInd r (x, α) = if x < α ∧ α < r.1 x ∧ r.1 x < β then (1:ZMod 2) else 0 := by
      rw [e1]; congr 1; simp only [eq_iff_iff]
      exact ⟨fun ⟨_,_,a,b,c⟩ => ⟨a,b,c⟩, fun ⟨a,b,c⟩ => ⟨hxl, hlt, a, b, c⟩⟩
    have c2 : crInd r (α, x) = if α < x ∧ x < β ∧ β < r.1 x then (1:ZMod 2) else 0 := by
      rw [e2]; congr 1; simp only [eq_iff_iff]
      exact ⟨fun ⟨_,_,a,b,c⟩ => ⟨a,b,c⟩, fun ⟨a,b,c⟩ => ⟨hlt, hxl, a, b, c⟩⟩
    rw [c1, c2, z3, z4, add_zero, add_zero]
    exact order_id x (r.1 x) α β hxl hlt hxα hxβ hx'α hx'β
  · exact absurd heq hαβ
  · have z1 : crInd r (x, α) = 0 := by rw [e1]; exact if_neg (by rintro ⟨_,h,_⟩; exact absurd h (not_lt.mpr (le_of_lt hgt)))
    have z2 : crInd r (α, x) = 0 := by rw [e2]; exact if_neg (by rintro ⟨h,_⟩; exact absurd h (not_lt.mpr (le_of_lt hgt)))
    have c3 : crInd r (x, β) = if x < β ∧ β < r.1 x ∧ r.1 x < α then (1:ZMod 2) else 0 := by
      rw [e3]; congr 1; simp only [eq_iff_iff]
      exact ⟨fun ⟨_,_,a,b,c⟩ => ⟨a,b,c⟩, fun ⟨a,b,c⟩ => ⟨hxl, hgt, a, b, c⟩⟩
    have c4 : crInd r (β, x) = if β < x ∧ x < α ∧ α < r.1 x then (1:ZMod 2) else 0 := by
      rw [e4]; congr 1; simp only [eq_iff_iff]
      exact ⟨fun ⟨_,_,a,b,c⟩ => ⟨a,b,c⟩, fun ⟨a,b,c⟩ => ⟨hgt, hxl, a, b, c⟩⟩
    rw [c3, c4, z1, z2, zero_add, zero_add]
    rw [add_comm (if x < α ∧ α < r.1 x then (1:ZMod 2) else 0)
                 (if x < β ∧ β < r.1 x then (1:ZMod 2) else 0)]
    exact order_id x (r.1 x) β α hxl hgt hxβ hxα hx'β hx'α

/-! ### partner facts -/
theorem qStar_b (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) : (qStar p q hbc).1 (p.1 0) = 0 := by
  obtain ⟨hb0, _, _, _, _, _⟩ := qStar_facts p q hbc
  rw [qStar_apply]; unfold qStarFun; rw [if_neg hb0, if_pos rfl]

theorem qStar_c (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) : (qStar p q hbc).1 (q.1 0) = q.1 (p.1 0) := by
  obtain ⟨_, hc0, _, _, hcb, _⟩ := qStar_facts p q hbc
  rw [qStar_apply]; unfold qStarFun; rw [if_neg hc0, if_neg hcb, if_pos rfl]

theorem qStar_d (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (qStar p q hbc).1 (q.1 (p.1 0)) = q.1 0 := by
  obtain ⟨_, _, hd0, hdb, _, hdc⟩ := qStar_facts p q hbc
  rw [qStar_apply]; unfold qStarFun; rw [if_neg hd0, if_neg hdb, if_neg hdc, if_pos rfl]

theorem qx_ne0 (q : Pairing (n+1)) (x) (hc : x ≠ q.1 0) : q.1 x ≠ 0 := by
  intro h; apply hc; have := pairing_invol q x; rw [h] at this; exact this.symm

theorem qx_neb (p q : Pairing (n+1)) (x) (hd : x ≠ q.1 (p.1 0)) : q.1 x ≠ p.1 0 := by
  intro h; apply hd; have := pairing_invol q x; rw [h] at this; exact this.symm

theorem qx_nec (q : Pairing (n+1)) (x) (h0 : x ≠ 0) : q.1 x ≠ q.1 0 := fun h => h0 (q.1.injective h)

theorem qx_ned (p q : Pairing (n+1)) (x) (hb : x ≠ p.1 0) : q.1 x ≠ q.1 (p.1 0) := fun h => hb (q.1.injective h)

/-! ### Δ_x = 0 : the external-special cancellation per external chord -/

/-- The combined indicator difference for one ordered pair. -/
noncomputable def Dind (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (ac : Fin (2*(n+1)) × Fin (2*(n+1))) : ZMod 2 :=
  crInd (qStar p q hbc) ac + crInd q ac

/-- For an external `x` (∉ V) that is a left-endpoint chord (`x < q.1 x`), the total interaction
of `x`'s chord with the four special vertices cancels mod 2: q's V-matching {0,c},{b,d} and
qStar's V-matching {0,b},{c,d} cross `x`'s chord the same number of times mod 2. -/
theorem Delta_left (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) (x : Fin (2*(n+1)))
    (h0 : x ≠ 0) (hb : x ≠ p.1 0) (hc : x ≠ q.1 0) (hd : x ≠ q.1 (p.1 0))
    (hxl : x < q.1 x) :
    (Dind p q hbc (x, 0) + Dind p q hbc (0, x)
      + (Dind p q hbc (x, p.1 0) + Dind p q hbc (p.1 0, x))
      + (Dind p q hbc (x, q.1 0) + Dind p q hbc (q.1 0, x))
      + (Dind p q hbc (x, q.1 (p.1 0)) + Dind p q hbc (q.1 (p.1 0), x))) = 0 := by
  set b := p.1 0 with hbdef
  set c := q.1 0 with hcdef
  set d := q.1 (p.1 0) with hddef
  -- external chord facts
  have hqx : q.1 x ≠ 0 := qx_ne0 q x hc
  have hqxb : q.1 x ≠ b := qx_neb p q x hd
  have hqxc : q.1 x ≠ c := qx_nec q x h0
  have hqxd : q.1 x ≠ d := qx_ned p q x hb
  have hsx : (qStar p q hbc).1 x = q.1 x := qStar_off p q hbc x h0 hb hc hd
  have hsxl : x < (qStar p q hbc).1 x := by rw [hsx]; exact hxl
  -- gChord for qStar's two chords {0,b},{c,d}
  have hsZero : (qStar p q hbc).1 0 = b := qStar_zero p q hbc
  have hsC : (qStar p q hbc).1 c = d := qStar_c p q hbc
  have gqs1 := gChord (qStar p q hbc) x 0 b hsxl hsZero
      h0 hb (by rw [hsx]; exact hqx) (by rw [hsx]; exact hqxb)
  have gqs2 := gChord (qStar p q hbc) x c d hsxl hsC
      hc hd (by rw [hsx]; exact hqxc) (by rw [hsx]; exact hqxd)
  -- gChord for q's two chords {0,c},{b,d}
  have hqC : q.1 0 = c := hcdef.symm
  have hqB : q.1 b = d := by rw [hbdef, hddef]
  have gq1 := gChord q x 0 c hxl hqC h0 hc hqx hqxc
  have gq2 := gChord q x b d hxl hqB hb hd hqxb hqxd
  -- unfold Dind and regroup
  simp only [Dind]
  -- memI under qStar uses interval (x, qStar.1 x) = (x, q.1 x); rewrite to match q's
  rw [hsx] at gqs1 gqs2
  -- Regroup the 16 crInd terms into 4 gChord blocks.
  trans ((crInd (qStar p q hbc) (x,0) + crInd (qStar p q hbc) (0,x)
            + crInd (qStar p q hbc) (x,b) + crInd (qStar p q hbc) (b,x))
        + (crInd (qStar p q hbc) (x,c) + crInd (qStar p q hbc) (c,x)
            + crInd (qStar p q hbc) (x,d) + crInd (qStar p q hbc) (d,x))
        + ((crInd q (x,0) + crInd q (0,x) + crInd q (x,c) + crInd q (c,x))
        + (crInd q (x,b) + crInd q (b,x) + crInd q (x,d) + crInd q (d,x))))
  · ring
  · rw [gqs1, gqs2, gq1, gq2]
    have hdup : ∀ a b c d : ZMod 2,
        (a + b + (c + d)) + ((a + c) + (b + d)) = 0 := by decide
    exact hdup _ _ _ _

/-- crInd vanishes whenever the second coordinate is a right-endpoint of `x`'s would-be chord:
if `¬(x < r.1 x)` then `crInd r (x, w) = 0` and `crInd r (w, x) = 0`. -/
theorem crInd_x_zero (r : Pairing (n+1)) (x w : Fin (2*(n+1))) (hx : ¬ (x < r.1 x)) :
    crInd r (x, w) = 0 ∧ crInd r (w, x) = 0 := by
  constructor
  · simp only [crInd]; exact if_neg (fun h => hx h.1)
  · simp only [crInd]; exact if_neg (fun h => hx h.2.1)

/-- For an external `x` (∉ V) that is NOT a left-endpoint (`¬(x < q.1 x)`), Δ_x is trivially 0. -/
theorem Delta_right (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) (x : Fin (2*(n+1)))
    (h0 : x ≠ 0) (hb : x ≠ p.1 0) (hc : x ≠ q.1 0) (hd : x ≠ q.1 (p.1 0))
    (hxr : ¬ (x < q.1 x)) :
    (Dind p q hbc (x, 0) + Dind p q hbc (0, x)
      + (Dind p q hbc (x, p.1 0) + Dind p q hbc (p.1 0, x))
      + (Dind p q hbc (x, q.1 0) + Dind p q hbc (q.1 0, x))
      + (Dind p q hbc (x, q.1 (p.1 0)) + Dind p q hbc (q.1 (p.1 0), x))) = 0 := by
  have hsx : (qStar p q hbc).1 x = q.1 x := qStar_off p q hbc x h0 hb hc hd
  have hxrs : ¬ (x < (qStar p q hbc).1 x) := by rw [hsx]; exact hxr
  simp only [Dind]
  rw [(crInd_x_zero (qStar p q hbc) x 0 hxrs).1, (crInd_x_zero (qStar p q hbc) x 0 hxrs).2,
      (crInd_x_zero (qStar p q hbc) x (p.1 0) hxrs).1, (crInd_x_zero (qStar p q hbc) x (p.1 0) hxrs).2,
      (crInd_x_zero (qStar p q hbc) x (q.1 0) hxrs).1, (crInd_x_zero (qStar p q hbc) x (q.1 0) hxrs).2,
      (crInd_x_zero (qStar p q hbc) x (q.1 (p.1 0)) hxrs).1, (crInd_x_zero (qStar p q hbc) x (q.1 (p.1 0)) hxrs).2,
      (crInd_x_zero q x 0 hxr).1, (crInd_x_zero q x 0 hxr).2,
      (crInd_x_zero q x (p.1 0) hxr).1, (crInd_x_zero q x (p.1 0) hxr).2,
      (crInd_x_zero q x (q.1 0) hxr).1, (crInd_x_zero q x (q.1 0) hxr).2,
      (crInd_x_zero q x (q.1 (p.1 0)) hxr).1, (crInd_x_zero q x (q.1 (p.1 0)) hxr).2]
  ring

/-- Δ_x = 0 for every external `x`. -/
theorem Delta_ext (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) (x : Fin (2*(n+1)))
    (h0 : x ≠ 0) (hb : x ≠ p.1 0) (hc : x ≠ q.1 0) (hd : x ≠ q.1 (p.1 0)) :
    (Dind p q hbc (x, 0) + Dind p q hbc (0, x)
      + (Dind p q hbc (x, p.1 0) + Dind p q hbc (p.1 0, x))
      + (Dind p q hbc (x, q.1 0) + Dind p q hbc (q.1 0, x))
      + (Dind p q hbc (x, q.1 (p.1 0)) + Dind p q hbc (q.1 (p.1 0), x))) = 0 := by
  by_cases hxl : x < q.1 x
  · exact Delta_left p q hbc x h0 hb hc hd hxl
  · exact Delta_right p q hbc x h0 hb hc hd hxl

/-! ### V Finset and its distinctness -/
section Vblock
variable (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)

/-- The four special vertices. -/
noncomputable def Vset : Finset (Fin (2*(n+1))) := {0, p.1 0, q.1 0, q.1 (p.1 0)}

theorem mem_Vset {v} : v ∈ Vset p q ↔ v = 0 ∨ v = p.1 0 ∨ v = q.1 0 ∨ v = q.1 (p.1 0) := by
  simp [Vset]

/-- Expansion of a sum over `Vset` into its four distinct terms. -/
theorem sum_Vset {M : Type*} [AddCommMonoid M] (hbc : p.1 0 ≠ q.1 0) (f : Fin (2*(n+1)) → M) :
    ∑ w ∈ Vset p q, f w = f 0 + f (p.1 0) + f (q.1 0) + f (q.1 (p.1 0)) := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  have d1 : (0 : Fin (2*(n+1))) ∉ ({p.1 0, q.1 0, q.1 (p.1 0)} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not; exact ⟨hb0.symm, hc0.symm, hd0.symm⟩
  have d2 : p.1 0 ∉ ({q.1 0, q.1 (p.1 0)} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not; exact ⟨hcb.symm, hdb.symm⟩
  have d3 : q.1 0 ∉ ({q.1 (p.1 0)} : Finset _) := by
    simp only [Finset.mem_singleton]; exact hdc.symm
  rw [Vset, Finset.sum_insert d1, Finset.sum_insert d2, Finset.sum_insert d3,
      Finset.sum_singleton]
  abel

/-- `Dind` vanishes when both coordinates are off `V`. -/
theorem Dind_off (x w : Fin (2*(n+1)))
    (hx : x ∉ Vset p q) (hw : w ∉ Vset p q) : Dind p q hbc (x, w) = 0 := by
  rw [mem_Vset] at hx hw
  push Not at hx hw
  simp only [Dind]
  rw [crInd_eq_off_V p q hbc (x, w) ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩
        ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2⟩]
  exact CharTwo.add_self_eq_zero _

/-- For `u ∉ V`, the inner sum over `w ∉ V` vanishes. -/
theorem inner_off_zero (u : Fin (2*(n+1))) (hu : u ∉ Vset p q) :
    ∑ w ∈ (Vset p q)ᶜ, Dind p q hbc (u, w) = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  rw [Finset.mem_compl] at hw
  exact Dind_off p q hbc u w hu hw

/-- The total `crInd`-difference sum reduces to the V×V block. -/
theorem total_eq_Vblock :
    ∑ ac : Fin (2*(n+1)) × Fin (2*(n+1)), Dind p q hbc ac
      = ∑ u ∈ Vset p q, ∑ w ∈ Vset p q, Dind p q hbc (u, w) := by
  rw [Fintype.sum_prod_type]
  -- split outer sum over V vs Vᶜ
  rw [← Finset.sum_add_sum_compl (Vset p q) (fun u => ∑ w, Dind p q hbc (u, w))]
  -- inner sums: split over V vs Vᶜ
  have hin : ∀ u, ∑ w, Dind p q hbc (u, w)
      = (∑ w ∈ Vset p q, Dind p q hbc (u, w)) + ∑ w ∈ (Vset p q)ᶜ, Dind p q hbc (u, w) := by
    intro u; rw [Finset.sum_add_sum_compl]
  simp_rw [hin]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the u∉V, w∉V block is 0
  rw [Finset.sum_congr rfl (fun u hu => inner_off_zero p q hbc u (Finset.mem_compl.mp hu)),
      Finset.sum_const_zero, add_zero]
  -- remaining: (∑_{u∈V}∑_{w∈V}) + (∑_{u∈V}∑_{w∉V} + ∑_{u∉V}∑_{w∈V})
  -- show the external-special part is 0
  have hext : (∑ u ∈ Vset p q, ∑ w ∈ (Vset p q)ᶜ, Dind p q hbc (u, w))
            + (∑ u ∈ (Vset p q)ᶜ, ∑ w ∈ Vset p q, Dind p q hbc (u, w)) = 0 := by
    rw [Finset.sum_comm]
    -- now: ∑_{x∉V} ∑_{u∈V} D(u,x)  +  ∑_{x∉V} ∑_{w∈V} D(x,w)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_compl, mem_Vset] at hx
    push Not at hx
    obtain ⟨h0, hb, hc, hd⟩ := hx
    rw [sum_Vset p q hbc (fun u => Dind p q hbc (u, x)),
        sum_Vset p q hbc (fun w => Dind p q hbc (x, w))]
    -- = (D(0,x)+D(b,x)+D(c,x)+D(d,x)) + (D(x,0)+D(x,b)+D(x,c)+D(x,d))
    have hΔ := Delta_ext p q hbc x h0 hb hc hd
    rw [show (Dind p q hbc (0, x) + Dind p q hbc (p.1 0, x) + Dind p q hbc (q.1 0, x)
              + Dind p q hbc (q.1 (p.1 0), x))
          + (Dind p q hbc (x, 0) + Dind p q hbc (x, p.1 0) + Dind p q hbc (x, q.1 0)
              + Dind p q hbc (x, q.1 (p.1 0)))
        = (Dind p q hbc (x, 0) + Dind p q hbc (0, x)
            + (Dind p q hbc (x, p.1 0) + Dind p q hbc (p.1 0, x))
            + (Dind p q hbc (x, q.1 0) + Dind p q hbc (q.1 0, x))
            + (Dind p q hbc (x, q.1 (p.1 0)) + Dind p q hbc (q.1 (p.1 0), x))) from by ring]
    exact hΔ
  -- rearrange:  A + B + C  with B + C = 0 (where A = Vblock, B = V×Vᶜ, C = Vᶜ×V)
  rw [show (∑ u ∈ Vset p q, ∑ w ∈ Vset p q, Dind p q hbc (u, w))
          + (∑ u ∈ Vset p q, ∑ w ∈ (Vset p q)ᶜ, Dind p q hbc (u, w))
          + (∑ u ∈ (Vset p q)ᶜ, ∑ w ∈ Vset p q, Dind p q hbc (u, w))
        = (∑ u ∈ Vset p q, ∑ w ∈ Vset p q, Dind p q hbc (u, w))
          + ((∑ u ∈ Vset p q, ∑ w ∈ (Vset p q)ᶜ, Dind p q hbc (u, w))
            + (∑ u ∈ (Vset p q)ᶜ, ∑ w ∈ Vset p q, Dind p q hbc (u, w))) from by ring,
      hext, add_zero]

/-- The exponent `e` with `flipQ p q = (-1)^e`. -/
noncomputable def flipExp (p q : Pairing (n+1)) : ZMod 2 :=
  if (p.1 0 < q.1 (p.1 0) ↔ q.1 0 < q.1 (p.1 0)) then 0 else 1

/-- The V-block residue as a pure nat-order identity (the 16-pair crossing count of both
V-matchings, in `ZMod 2`). -/
theorem vnat (B C D : ℕ) (nb0 : 0 < B) (nc0 : 0 < C) (nd0 : 0 < D)
    (nbc : B ≠ C) (nbd : B ≠ D) (ncd : C ≠ D) :
    ((if 0 < B ∧ 0 < B ∧ 0 < 0 ∧ 0 < B ∧ B < B then (1:ZMod 2) else 0) + if 0 < C ∧ 0 < C ∧ 0 < 0 ∧ 0 < C ∧ C < C then 1 else 0) +
                ((if 0 < B ∧ B < 0 ∧ 0 < B ∧ B < B ∧ B < 0 then 1 else 0) +
                  if 0 < C ∧ B < D ∧ 0 < B ∧ B < C ∧ C < D then 1 else 0) +
              ((if 0 < B ∧ C < D ∧ 0 < C ∧ C < B ∧ B < D then 1 else 0) +
                if 0 < C ∧ C < 0 ∧ 0 < C ∧ C < C ∧ C < 0 then 1 else 0) +
            ((if 0 < B ∧ D < C ∧ 0 < D ∧ D < B ∧ B < C then 1 else 0) +
              if 0 < C ∧ D < B ∧ 0 < D ∧ D < C ∧ C < B then 1 else 0) +
          (((if B < 0 ∧ 0 < B ∧ B < 0 ∧ 0 < 0 ∧ 0 < B then 1 else 0) +
                  if B < D ∧ 0 < C ∧ B < 0 ∧ 0 < D ∧ D < C then 1 else 0) +
                ((if B < 0 ∧ B < 0 ∧ B < B ∧ B < 0 ∧ 0 < 0 then 1 else 0) +
                  if B < D ∧ B < D ∧ B < B ∧ B < D ∧ D < D then 1 else 0) +
              ((if B < 0 ∧ C < D ∧ B < C ∧ C < 0 ∧ 0 < D then 1 else 0) +
                if B < D ∧ C < 0 ∧ B < C ∧ C < D ∧ D < 0 then 1 else 0) +
            ((if B < 0 ∧ D < C ∧ B < D ∧ D < 0 ∧ 0 < C then 1 else 0) +
              if B < D ∧ D < B ∧ B < D ∧ D < D ∧ D < B then 1 else 0)) +
        (((if C < D ∧ 0 < B ∧ C < 0 ∧ 0 < D ∧ D < B then 1 else 0) +
                if C < 0 ∧ 0 < C ∧ C < 0 ∧ 0 < 0 ∧ 0 < C then 1 else 0) +
              ((if C < D ∧ B < 0 ∧ C < B ∧ B < D ∧ D < 0 then 1 else 0) +
                if C < 0 ∧ B < D ∧ C < B ∧ B < 0 ∧ 0 < D then 1 else 0) +
            ((if C < D ∧ C < D ∧ C < C ∧ C < D ∧ D < D then 1 else 0) +
              if C < 0 ∧ C < 0 ∧ C < C ∧ C < 0 ∧ 0 < 0 then 1 else 0) +
          ((if C < D ∧ D < C ∧ C < D ∧ D < D ∧ D < C then 1 else 0) +
            if C < 0 ∧ D < B ∧ C < D ∧ D < 0 ∧ 0 < B then 1 else 0)) +
      (((if D < C ∧ 0 < B ∧ D < 0 ∧ 0 < C ∧ C < B then 1 else 0) +
              if D < B ∧ 0 < C ∧ D < 0 ∧ 0 < B ∧ B < C then 1 else 0) +
            ((if D < C ∧ B < 0 ∧ D < B ∧ B < C ∧ C < 0 then 1 else 0) +
              if D < B ∧ B < D ∧ D < B ∧ B < B ∧ B < D then 1 else 0) +
          ((if D < C ∧ C < D ∧ D < C ∧ C < C ∧ C < D then 1 else 0) +
            if D < B ∧ C < 0 ∧ D < C ∧ C < B ∧ B < 0 then 1 else 0) +
        ((if D < C ∧ D < C ∧ D < D ∧ D < C ∧ C < C then 1 else 0) +
          if D < B ∧ D < B ∧ D < D ∧ D < B ∧ B < B then 1 else 0)) =
    1 + if B < D ↔ C < D then 0 else 1 := by
  rcases lt_trichotomy B C with hBC | hBC | hBC <;>
  rcases lt_trichotomy B D with hBD | hBD | hBD <;>
  rcases lt_trichotomy C D with hCD | hCD | hCD <;>
  first
    | (exfalso; omega)
    | ((repeat first
        | rw [if_pos (show _ by omega)]
        | rw [if_neg (show _ by omega)]); decide)

/-- crInd on a pair of V-vertices, with all images substituted, in terms of the order of 0,b,c,d. -/
theorem Vblock_residue (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    ∑ u ∈ Vset p q, ∑ w ∈ Vset p q, Dind p q hbc (u, w) = 1 + flipExp p q := by
  obtain ⟨hb0, hc0, hd0, hdb, hcb, hdc⟩ := qStar_facts p q hbc
  -- images (stated with literal p.1 0, q.1 0, q.1 (p.1 0))
  have qs0 : (qStar p q hbc).1 0 = p.1 0 := qStar_zero p q hbc
  have qsb : (qStar p q hbc).1 (p.1 0) = 0 := qStar_b p q hbc
  have qsc : (qStar p q hbc).1 (q.1 0) = q.1 (p.1 0) := qStar_c p q hbc
  have qsd : (qStar p q hbc).1 (q.1 (p.1 0)) = q.1 0 := qStar_d p q hbc
  have qc : q.1 (q.1 0) = 0 := pairing_invol q 0
  have qd : q.1 (q.1 (p.1 0)) = p.1 0 := pairing_invol q (p.1 0)
  rw [sum_Vset p q hbc, sum_Vset p q hbc (fun w => Dind p q hbc (0, w)),
      sum_Vset p q hbc (fun w => Dind p q hbc (p.1 0, w)),
      sum_Vset p q hbc (fun w => Dind p q hbc (q.1 0, w)),
      sum_Vset p q hbc (fun w => Dind p q hbc (q.1 (p.1 0), w))]
  simp only [Dind, crInd, qs0, qsb, qsc, qsd, qc, qd, flipExp]
  simp only [Fin.lt_def, Fin.val_zero]
  -- distinctness in ℕ
  have nb0 : (0:ℕ) < (p.1 0).val := Fin.pos_iff_ne_zero.mpr hb0
  have nc0 : (0:ℕ) < (q.1 0).val := Fin.pos_iff_ne_zero.mpr hc0
  have nd0 : (0:ℕ) < (q.1 (p.1 0)).val := Fin.pos_iff_ne_zero.mpr hd0
  have nbc : (p.1 0).val ≠ (q.1 0).val := fun h => hcb (Fin.val_injective h).symm
  have nbd : (p.1 0).val ≠ (q.1 (p.1 0)).val := fun h => hdb (Fin.val_injective h).symm
  have ncd : (q.1 0).val ≠ (q.1 (p.1 0)).val := fun h => hdc (Fin.val_injective h).symm
  exact vnat _ _ _ nb0 nc0 nd0 nbc nbd ncd

/-! ### Final assembly -/

/-- The natural-number flip exponent. -/
noncomputable def flipExpN (p q : Pairing (n+1)) : ℕ :=
  if (p.1 0 < q.1 (p.1 0) ↔ q.1 0 < q.1 (p.1 0)) then 0 else 1

theorem flipExp_cast (p q : Pairing (n+1)) :
    flipExp p q = ((flipExpN p q : ℕ) : ZMod 2) := by
  simp only [flipExp, flipExpN]; split <;> simp

theorem flipQ_eq_pow (p q : Pairing (n+1)) : flipQ p q = (-1 : ℤ) ^ (flipExpN p q) := by
  simp only [flipQ, flipExpN]; split <;> simp

/-- The core ZMod 2 crossing identity. -/
theorem cross_zmod_id (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    (((qStar p q hbc).crossings : ℕ) : ZMod 2)
      = (((q.crossings : ℕ) : ZMod 2)) + 1 + flipExp p q := by
  have hsum : (((qStar p q hbc).crossings : ℕ) : ZMod 2)
            + ((q.crossings : ℕ) : ZMod 2) = 1 + flipExp p q := by
    rw [crossings_zmod, crossings_zmod, ← Finset.sum_add_distrib]
    have : ∀ ac, crInd (qStar p q hbc) ac + crInd q ac = Dind p q hbc ac := fun ac => rfl
    simp_rw [this]
    rw [total_eq_Vblock, Vblock_residue]
  -- in ZMod 2, A + B = X ⟹ A = X + B  (B + B = 0)
  set A := (((qStar p q hbc).crossings : ℕ) : ZMod 2) with hA
  set Bq := ((q.crossings : ℕ) : ZMod 2) with hBq
  rw [add_assoc, ← hsum,
      show Bq + (A + Bq) = A + (Bq + Bq) from by ring,
      CharTwo.add_self_eq_zero, add_zero]

end Vblock

/-- **Local merge-sign crossing lemma** (the single remaining leaf of the whole development).
`ε(qStar) = -flipQ · ε(q)`, equivalently `qStar.crossings ≡ q.crossings + 1 + flipExp (mod 2)`
where `flipExp = 0` iff `(b < q.1 b ↔ c < q.1 b)` (`b = p.1 0`, `c = q.1 0`). The pairings `q`
and `qStar` share every chord except the two special chords on `V = {0, b, c, q.1 b}`:
`q` has `{0,c}, {b, q.1 b}` while `qStar` has `{0,b}, {c, q.1 b}` (the two distinct perfect
matchings of `V`). Crossing-count difference (in `ZMod 2`, via `crossings_zmod`/`crInd`):
external–external chord pairs are identical (`crInd` agrees off `V`); external–special crossings
cancel mod 2 (each external chord crosses an even number more of `qStar`'s specials than `q`'s,
the `n_I`-parity argument: both matchings of `V` give crossing-parity `= |V ∩ interval| mod 2`);
the residue is the special–special crossing `[{0,b}×{c,q.1 b}] − [{0,c}×{b,q.1 b}]`, a finite
case-check on the order of `{0,b,c,q.1 b}` that equals `1 + flipExp`.

This is a `sign_canonicalWord`-class crossing-parity inversion count — the genuinely
research-hard residue. Numerically verified: `decide` over `Pairing 2` confirms
`crCount(qStar) + crCount(q) + 1 + flipExp ≡ 0 (mod 2)` for every admissible pair (see
`scratch/_mr_sign_check.lean`). EVERYTHING else in the merge case (`EP_q_eq_flip_EP_qStar`,
`loops_pqStar`, `merge_sign`'s reduction via `two_loop_sign p (qStar)`, and the full
`merge_residual` assembly) is proved and axiom-clean and depends only on this leaf. -/
theorem qStar_sign (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    epsVec ℤ (qStar p q hbc) = - flipQ p q * epsVec ℤ q := by
  show ((-1 : ℤ)) ^ (qStar p q hbc).crossings = - flipQ p q * ((-1 : ℤ)) ^ q.crossings
  rw [flipQ_eq_pow]
  rw [show -((-1:ℤ)^(flipExpN p q)) * (-1)^q.crossings
        = (-1)^(1 + flipExpN p q + q.crossings) from by
        rw [pow_add, pow_add, pow_one]; ring]
  apply negpow_of_zmod
  push_cast
  rw [cross_zmod_id p q hbc, flipExp_cast]
  ring

/-- `flipQ` squares to one. -/
theorem flipQ_sq (p q : Pairing (n+1)) : flipQ p q * flipQ p q = 1 := by
  rw [flipQ]; split <;> ring

/-- The merge-sign identity: `flipQ · ε(p') · ε(q'') = - εp · εq`, where `p' = pPrimeO p`,
`q'' = pPrimeO (qStar p q hbc)`. Combines `two_loop_sign p (qStar)` (valid since
`p.1 0 = qStar.1 0`) with the local crossing lemma `qStar_sign`. -/
theorem merge_sign (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0) :
    flipQ p q * (epsVec ℤ (pPrimeO p) * epsVec ℤ (pPrimeO (qStar p q hbc)))
      = - (epsVec ℤ p * epsVec ℤ q) := by
  have hbc' : p.1 0 = (qStar p q hbc).1 0 := (qStar_zero p q hbc).symm
  have htl := two_loop_sign p (qStar p q hbc) hbc'
  rw [← htl, qStar_sign p q hbc]
  have hsq : flipQ p q * flipQ p q = 1 := flipQ_sq p q
  rw [show flipQ p q * (epsVec ℤ p * (-flipQ p q * epsVec ℤ q))
        = -((flipQ p q * flipQ p q) * (epsVec ℤ p * epsVec ℤ q)) from by ring, hsq, one_mul]

/-- The merged functional summed over the nonzero-vertex index in the merge case:
`flipQ · (EP_p(reLift p rest) · EP_qStar(reLift p rest))`. Marked `irreducible` so it stays
fully opaque during the reindexing unifications (otherwise the elaborator whnf-loops). -/
@[irreducible] noncomputable def mergeF (M : ℕ) {n : ℕ} (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) : ℤ :=
  flipQ p q * (EP M n p (reLift M n p rest) * EP M n (qStar p q hbc) (reLift M n p rest))

theorem mergeF_apply (M : ℕ) {n : ℕ} (p q : Pairing (n+1)) (hbc : p.1 0 ≠ q.1 0)
    (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :
    mergeF M p q hbc rest
      = flipQ p q * (EP M n p (reLift M n p rest) * EP M n (qStar p q hbc) (reLift M n p rest)) := by
  rw [mergeF]

end MergeResidual

set_option maxHeartbeats 800000 in
/-- **Merge residual** (case `p 0 ≠ q 0`): the indicator `[rest b = rest c]` merges the distinct
vertices `b = p 0`, `c = q 0`; the `Fin (2*n)`-reindexed contraction sum over the reduced pair
`(p',q')` (SAME loop count, `p.loops q = p'.loops q'`) hits the closed form at level `n+1`. The
crossing-sign factor `-ε(p)ε(q)ε(p')ε(q') = +1` after cancellation (`sign_canonicalWord`-class
inversion count). Numerically verified (`n ≤ 3`, `M ≤ 2`). The genuine combinatorial core of the
merge case. -/
theorem merge_residual (M : ℕ) {n : ℕ}
    (IH : ∀ (p' q' : Pairing n),
      ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p' i * deltaContr M q' i
        = epsVec ℤ p' * epsVec ℤ q' * (-1) ^ n * (-(2 * (M : ℤ))) ^ p'.loops q')
    (p q : Pairing (n+1)) (hbc : ¬ p.1 0 = q.1 0) :
    (∑ rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M),
        (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
          then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest)
          else 0))
      = epsVec ℤ p * epsVec ℤ q * (-1) ^ (n+1) * (-(2 * (M : ℤ))) ^ p.loops q := by
  rcases isEmpty_or_nonempty (Fin (2*M)) with hE | hN
  · have hz : (2*(M:ℤ)) = 0 := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · simp [h0]
      · exact absurd (⟨⟨0, by omega⟩⟩ : Nonempty (Fin (2*M))) (not_nonempty_iff.mpr hE)
    have hempty : IsEmpty ({j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :=
      ⟨fun f => hE.false (f ⟨p.1 0, p.2.2 0⟩)⟩
    rw [Finset.sum_of_isEmpty]
    have hloop : 0 < p.loops q := loops_pos p q
    rw [show (-(2 * (M:ℤ))) = 0 from by rw [hz]; ring, zero_pow (by omega : p.loops q ≠ 0)]
    ring
  obtain ⟨w₀⟩ := hN
  have hcne : (⟨q.1 0, q.2.2 0⟩ : {j : Fin (2*(n+1)) // j ≠ 0}) ≠ ⟨p.1 0, p.2.2 0⟩ := by
    intro h; exact hbc (Subtype.ext_iff.mp h).symm
  have hbc' : p.1 0 = (qStar p q hbc).1 0 := (qStar_zero p q hbc).symm
  -- Step 1: rewrite summand to the indicator over `mergeF`.
  have hsummand : ∀ rest, (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
        then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest) else 0)
      = (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩ then mergeF M p q hbc rest else 0) := by
    intro rest
    by_cases hcond : rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
    · rw [if_pos hcond, if_pos hcond, mergeF_apply]
      have hcondi : reLift M n p rest (p.1 0) = reLift M n p rest (q.1 0) := by
        rw [reLift_ne M n p rest (p.2.2 0), reLift_ne M n p rest (q.2.2 0)]; exact hcond
      rw [EP_q_eq_flip_EP_qStar M p q hbc (reLift M n p rest) hcondi]; ring
    · rw [if_neg hcond, if_neg hcond]
  simp_rw [hsummand]
  -- Step 2: `mergeF` is independent of `rest` at ⟨p.1 0⟩.
  have hFindep : ∀ (rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) (x : Fin (2*M)),
      mergeF M p q hbc (Function.update rest ⟨p.1 0, p.2.2 0⟩ x) = mergeF M p q hbc rest := by
    intro rest x
    rw [mergeF_apply, mergeF_apply]
    congr 2
    · exact EP_reLift_indep_b M n p rest x
    · have key := EP_q_reLift_indep M n p (qStar p q hbc) rest x
      have helt : (⟨(qStar p q hbc).1 0, (qStar p q hbc).2.2 0⟩ : {j : Fin (2*(n+1)) // j ≠ 0})
          = ⟨p.1 0, p.2.2 0⟩ := Subtype.ext (qStar_zero p q hbc)
      rw [helt] at key
      exact key
  -- Step 3: reindex via sum_indicator_merge (a = ⟨p.1 0⟩, a' = ⟨q.1 0⟩).
  refine Eq.trans (sum_indicator_merge ⟨p.1 0, p.2.2 0⟩ ⟨q.1 0, q.2.2 0⟩ hcne
    (mergeF M p q hbc) hFindep) ?_
  -- Step 4: bridge each summand to `flipQ · deltaContr p' (g∘dblE) · deltaContr q'' (g∘dblE)`.
  have hsumm2 : ∀ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
      mergeF M p q hbc ((Equiv.funSplitAt ⟨p.1 0, p.2.2 0⟩ (Fin (2*M))).symm
            (g (⟨⟨q.1 0, q.2.2 0⟩, hcne⟩ : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩}), g))
        = flipQ p q * (deltaContr M (pPrimeO p) (fun i => g (dblE p i))
            * deltaContr M (pPrimeO (qStar p q hbc)) (fun i => g (dblE p i))) := by
    intro g
    rw [mergeF_apply]
    set rr : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M) :=
      (Equiv.funSplitAt (⟨p.1 0, p.2.2 0⟩ : {j : Fin (2*(n+1)) // j ≠ 0}) (Fin (2*M))).symm
        (g (⟨⟨q.1 0, q.2.2 0⟩, hcne⟩ : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩}), g)
      with hrr
    have hidxp : idxOf (M := M) p rr = fun i => g (dblE p i) := by
      rw [hrr]; exact idxOf_funSplit_eq p (g (⟨⟨q.1 0, q.2.2 0⟩, hcne⟩ : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩})) g
    have hidxq : idxOf (M := M) (qStar p q hbc) rr = fun i => g (dblE p i) := by
      rw [idxOf_q_eq_p p (qStar p q hbc) hbc' rr, hidxp]
    rw [show EP M n p (reLift M n p rr) = deltaContr M (pPrimeO p) (idxOf (M := M) p rr) from
          EP_eq_deltaContr M n p rr]
    rw [show EP M n (qStar p q hbc) (reLift M n p rr)
          = deltaContr M (pPrimeO (qStar p q hbc)) (idxOf (M := M) (qStar p q hbc) rr) from
        EP_q_eq_deltaContr M n p (qStar p q hbc) hbc' rr]
    rw [hidxp, hidxq]
  rw [Finset.sum_congr rfl (fun g (_ : g ∈ (Finset.univ :
        Finset ({s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M)))) =>
      hsumm2 g)]
  -- Step 5: pull flipQ out, reindex ∑_g (...∘ dblE p) = ∑_idx (...).
  rw [← Finset.mul_sum]
  rw [show (∑ g : {s : {j : Fin (2*(n+1)) // j ≠ 0} // s ≠ ⟨p.1 0, p.2.2 0⟩} → Fin (2*M),
        deltaContr M (pPrimeO p) (fun i => g (dblE p i))
          * deltaContr M (pPrimeO (qStar p q hbc)) (fun i => g (dblE p i)))
      = ∑ idx : Fin (2*n) → Fin (2*M),
          deltaContr M (pPrimeO p) idx * deltaContr M (pPrimeO (qStar p q hbc)) idx from by
    rw [← Equiv.sum_comp (Equiv.arrowCongr (dblE p).symm (Equiv.refl (Fin (2*M))))
        (fun idx => deltaContr M (pPrimeO p) idx * deltaContr M (pPrimeO (qStar p q hbc)) idx)]
    apply Finset.sum_congr rfl
    intro g _
    have hg : (fun i => g (dblE p i))
        = (Equiv.arrowCongr (dblE p).symm (Equiv.refl (Fin (2*M)))) g := by
      funext i; show g (dblE p i) = _; rw [Equiv.arrowCongr_apply]; simp
    rw [hg]]
  -- Step 6: apply IH for (pPrimeO p, pPrimeO qStar), then loops-invariance + merge-sign.
  rw [IH (pPrimeO p) (pPrimeO (qStar p q hbc))]
  -- loops invariance: (pPrimeO p).loops (pPrimeO qStar) = p.loops q
  have hloops : (pPrimeO p).loops (pPrimeO (qStar p q hbc)) = p.loops q := by
    have h1 := loops_two_loop p (qStar p q hbc) hbc'
    have h2 := loops_pqStar p q hbc
    omega
  rw [hloops]
  -- sign: flipQ · (ε(p') · ε(q'')) = -(εp · εq)
  rw [show flipQ p q * (epsVec ℤ (pPrimeO p) * epsVec ℤ (pPrimeO (qStar p q hbc)) * (-1) ^ n
          * (-(2 * (M : ℤ))) ^ p.loops q)
        = (flipQ p q * (epsVec ℤ (pPrimeO p) * epsVec ℤ (pPrimeO (qStar p q hbc))))
          * ((-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q) from by ring]
  rw [merge_sign p q hbc]
  rw [pow_succ]
  ring



theorem gram_recursion (M : ℕ) {n : ℕ}
    (IH : ∀ (p' q' : Pairing n),
      ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p' i * deltaContr M q' i
        = epsVec ℤ p' * epsVec ℤ q' * (-1) ^ n * (-(2 * (M : ℤ))) ^ p'.loops q')
    (p q : Pairing (n+1)) :
    (∑ rest : {j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M),
        (if rest ⟨p.1 0, p.2.2 0⟩ = rest ⟨q.1 0, q.2.2 0⟩
          then EP M n p (reLift M n p rest) * EP M n q (reLift M n p rest)
          else 0))
      = epsVec ℤ p * epsVec ℤ q * (-1) ^ (n+1) * (-(2 * (M : ℤ))) ^ p.loops q := by
  by_cases hbc : p.1 0 = q.1 0
  · rcases isEmpty_or_nonempty (Fin (2*M)) with hE | hN
    · have hz : (2*(M:ℤ)) = 0 := by
        rcases Nat.eq_zero_or_pos M with h0 | hpos
        · simp [h0]
        · exact absurd (⟨⟨0, by omega⟩⟩ : Nonempty (Fin (2*M))) (not_nonempty_iff.mpr hE)
      have hempty : IsEmpty ({j : Fin (2*(n+1)) // j ≠ 0} → Fin (2*M)) :=
        ⟨fun f => hE.false (f ⟨p.1 0, p.2.2 0⟩)⟩
      rw [Finset.sum_of_isEmpty]
      have hloop : 0 < p.loops q := loops_pos p q
      rw [show (-(2 * (M:ℤ))) = 0 from by rw [hz]; ring, zero_pow (by omega : p.loops q ≠ 0)]
      ring
    · obtain ⟨w₀⟩ := hN
      rw [two_loop_branch M n p q hbc w₀]
      exact two_loop_residual M IH p q hbc w₀
  · exact merge_residual M IH p q hbc

/-- **The geometric loop core** (the single remaining symplectic leaf, gauge-free form):
the index sum of the canonical `J`-contractions `Δ′_p Δ′_q` factors over the joint loops
of `p ∪ q`, each `2m`-loop contributing `tr(J^{2m}) = (-1)^m·2M` (`loop_Jform_sum_even`)
with the per-loop cyclic-shift orientation sign assembling to the closed form.
Blueprint: `thm:crossing_sign` core; the informal argument (Lemmas 2–3 + Assembly)
is recorded in the blueprint's symplectic chapter. Base case `n = 0` is
`deltaContr_gram_closed_zero`. -/
theorem deltaContr_gram_closed (M : ℕ) {n : ℕ} (p q : Pairing n) :
    ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p i * deltaContr M q i
      = epsVec ℤ p * epsVec ℤ q * (-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q := by
  induction n with
  | zero => exact deltaContr_gram_closed_zero M p q
  | succ k ih =>
    rw [deltaContr_gram_after_collapse M k p q]
    exact gram_recursion M ih p q

/-- **The loop core**: the gauge-invariant index sum factors over the joint loops of
`p ∪ q`, each `2m`-loop contributing `tr(J^{2m}) = (-1)^m·2M` (`trace_Jform_pow`) after
one cyclic shift (sign `(-1)` per loop). Reduced here to the gauge-free geometric core
`deltaContr_gram_closed` via the Pfaffian-sign bridge: writing
`Φ_p = ε(p) Δ′_p` (`deltaContr_eq_prod_leftEnd`, `sign_canonicalWord`), pulling the two
constant ε factors out of the sum, and cancelling them against the ε factors of the
closed form (`epsVec_sq`). Blueprint: `thm:crossing_sign` core; the informal
argument (Lemmas 2–3) is recorded in the blueprint's symplectic chapter. -/
theorem PhiCanon_sum (M : ℕ) {n : ℕ} (p q : Pairing n) :
    ∑ i : Fin (2 * n) → Fin (2 * M), PhiCanon M p i * PhiCanon M q i
      = (-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q := by
  have hsign : ∀ (r : Pairing n) (i : Fin (2 * n) → Fin (2 * M)),
      PhiCanon M r i = epsVec ℤ r * deltaContr M r i := by
    intro r i
    rw [PhiCanon, deltaContr_eq_prod_leftEnd, sign_canonicalWord]; rfl
  simp_rw [hsign]
  rw [show (∑ i : Fin (2 * n) → Fin (2 * M),
        epsVec ℤ p * deltaContr M p i * (epsVec ℤ q * deltaContr M q i))
      = epsVec ℤ p * epsVec ℤ q
        * ∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p i * deltaContr M q i from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
  rw [deltaContr_gram_closed]
  rw [show epsVec ℤ p * epsVec ℤ q
        * (epsVec ℤ p * epsVec ℤ q * (-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q)
      = (epsVec ℤ p * epsVec ℤ p) * (epsVec ℤ q * epsVec ℤ q)
        * ((-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q) from by ring]
  rw [epsVec_sq, epsVec_sq, one_mul, one_mul]

/-- Crossing-sign factorization: the contraction Gram equals the closed form. Reduced, via the
Pfaffian-sign bridge, to the loop core `PhiCanon_sum`. Blueprint: `thm:crossing_sign`. -/
theorem sympGramContr_eq_closed (M n : ℕ) :
    sympGramContr M n = sympGramClosed ℤ M n := by
  ext p q
  show (∑ i : Fin (2 * n) → Fin (2 * M), deltaContr M p i * deltaContr M q i)
       = epsVec ℤ p * epsVec ℤ q * (-1) ^ n * (-(2 * (M : ℤ))) ^ p.loops q
  have hfac : ∀ i, deltaContr M p i * deltaContr M q i
        = epsVec ℤ p * epsVec ℤ q * (PhiCanon M p i * PhiCanon M q i) := by
    intro i; rw [deltaContr_eq_eps_PhiCanon, deltaContr_eq_eps_PhiCanon]; ring
  simp_rw [hfac]; rw [← Finset.mul_sum, PhiCanon_sum]; ring

/-- Conjugation form, entrywise: the closed symplectic Gram is the signed
conjugation of the orthogonal Gram at parameter `-2M`.
Blueprint: `cor:symp_conjugation`. -/
theorem sympGramClosed_eq_conj (k : Type*) [CommRing k] (M n : ℕ)
    (p q : Pairing n) :
    sympGramClosed k M n p q
      = epsVec k p * ((-1) ^ n * orthGram k n (-(2 * (M : k))) p q) * epsVec k q := by
  unfold sympGramClosed orthGram
  ring

/-- The ε-twisted determinant vector. Blueprint: `def:eps_det_vector`. -/
def epsDetVec (k : Type*) [CommRing k] {n : ℕ} : Pairing n → k := fun p =>
  epsVec k p * detVec k p

/-- `D_ε · (ε ⊙ det) = det`. -/
theorem diag_mulVec_epsDetVec {k : Type*} [CommRing k] {n : ℕ} :
    (Matrix.diagonal (epsVec k)).mulVec (epsDetVec (n := n) k) = detVec k := by
  funext p; rw [Matrix.mulVec_diagonal]
  show epsVec k p * (epsVec k p * detVec k p) = detVec k p
  rw [← mul_assoc, epsVec_sq, one_mul]

/-- `D_ε · det = ε ⊙ det`. -/
theorem diag_mulVec_detVec {k : Type*} [CommRing k] {n : ℕ} :
    (Matrix.diagonal (epsVec k)).mulVec (detVec (n := n) k) = epsDetVec k := by
  funext p; rw [Matrix.mulVec_diagonal]; rfl

/-- Even-falling factorial `(2M)(2M-2)⋯(2M-2n+2)`. Blueprint:
`def:even_falling`. -/
def evenFalling (k : Type*) [CommRing k] (M n : ℕ) : k :=
  ∏ j ∈ Finset.range n, (2 * (M : k) - 2 * (j : k))

/-- `evenRising(-2M) = (-1)^n · evenFalling`. -/
theorem evenRising_neg {k : Type*} [CommRing k] (M n : ℕ) :
    evenRising k n (-(2 * (M : k))) = (-1) ^ n * evenFalling k M n := by
  have hc : (-1 : k) ^ n = ∏ _j ∈ Finset.range n, (-1 : k) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [evenRising, evenFalling, hc, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => by ring)

/-- The even-falling factorial vanishes below threshold. -/
theorem evenFalling_eq_zero {k : Type*} [CommRing k] {M n : ℕ} (h : M < n) :
    evenFalling k M n = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr h) (by ring)

/-- Shifted rising factorial `(2M)(2M+1)⋯(2M+n-1)`. Blueprint:
`def:rising_shift`. -/
def risingShift (k : Type*) [CommRing k] (M n : ℕ) : k :=
  ∏ j ∈ Finset.range n, (2 * (M : k) + (j : k))

/-- `fallingFact(-2M) = (-1)^n · risingShift`. -/
theorem fallingFact_neg {k : Type*} [CommRing k] (M n : ℕ) :
    fallingFact k n (-(2 * (M : k))) = (-1) ^ n * risingShift k M n := by
  have hc : (-1 : k) ^ n = ∏ _j ∈ Finset.range n, (-1 : k) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [fallingFact, risingShift, hc, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => by ring)

/-- ε-twisted ones absorption: the ε vector carries the even-falling
factorial. Blueprint: `thm:symp_eps_ones_absorb`. -/
theorem sympGram_mulVec_epsVec (k : Type*) [CommRing k] (M n : ℕ) :
    (sympGramClosed k M n).mulVec (epsVec k)
      = evenFalling k M n • epsVec k := by
  have hsc : (-1 : k) ^ n * evenRising k n (-(2 * M)) = evenFalling k M n := by
    rw [evenRising_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [sympGramClosed_factor, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diag_mulVec_epsVec,
    Matrix.smul_mulVec, orthGram_mulVec_one, Matrix.mulVec_smul, Matrix.mulVec_smul,
    diag_mulVec_one]
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, hsc]

/-- ε-twisted determinant absorption: the ε-twisted determinant vector
carries the shifted rising factorial. Blueprint: `thm:symp_eps_det_absorb`. -/
theorem sympGram_mulVec_epsDetVec (k : Type*) [CommRing k] (M n : ℕ) :
    (sympGramClosed k M n).mulVec (epsDetVec k)
      = risingShift k M n • epsDetVec k := by
  have hsc : (-1 : k) ^ n * fallingFact k n (-(2 * M)) = risingShift k M n := by
    rw [fallingFact_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [sympGramClosed_factor, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diag_mulVec_epsDetVec,
    Matrix.smul_mulVec, orthGram_mulVec_detVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
    diag_mulVec_detVec]
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, hsc]

/-- Kernel witness below threshold: for `M < n` the ε vector lies in the
kernel of the symplectic Gram. Blueprint: `thm:symp_ker_witness`. -/
theorem sympGram_mulVec_epsVec_eq_zero (k : Type*) [CommRing k] {M n : ℕ}
    (h : M < n) :
    (sympGramClosed k M n).mulVec (epsVec k) = 0 := by
  rw [sympGram_mulVec_epsVec, evenFalling_eq_zero h, zero_smul]

/-- The ε vector is nowhere zero (it is `±1`-valued). -/
theorem epsVec_apply_ne_zero {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (p : Pairing n) : epsVec k p ≠ 0 := by
  show ((epsSign p : ℤ) : k) ≠ 0
  rw [epsSign]
  push_cast
  exact ((isUnit_one.neg).pow _).ne_zero

/-- Hence the ε vector is not the zero vector. -/
theorem epsVec_ne_zero {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ} :
    epsVec (n := n) k ≠ 0 :=
  fun h => epsVec_apply_ne_zero (qPair 1) (by rw [h]; rfl)

/-- Gram singularity below threshold. Blueprint: `thm:symp_not_unit`. -/
theorem not_isUnit_sympGram (k : Type*) [CommRing k] [Nontrivial k]
    {M n : ℕ} (h : M < n) :
    ¬ IsUnit (sympGramClosed k M n) := by
  intro hu
  apply epsVec_ne_zero (k := k) (n := n)
  obtain ⟨u, hu_eq⟩ := hu
  have hinv : (↑u⁻¹ : Matrix (Pairing n) (Pairing n) k) * sympGramClosed k M n = 1 := by
    rw [← hu_eq]; exact u.inv_mul
  have hkey : (↑u⁻¹ : Matrix (Pairing n) (Pairing n) k).mulVec
      ((sympGramClosed k M n).mulVec (epsVec k)) = epsVec k := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [sympGram_mulVec_epsVec_eq_zero k h, Matrix.mulVec_zero] at hkey
  exact hkey.symm

/-- Exact vanishing below threshold: for `M < n` every commuting Penrose
partner kills the ε covector. Blueprint: `thm:symp_vanish_below`. -/
theorem vecMul_epsVec_eq_zero {k : Type*} [CommRing k] {M n : ℕ}
    {W : Matrix (Pairing n) (Pairing n) k}
    (hW : IsCommPenrosePartner (sympGramClosed k M n) W) (h : M < n) :
    Matrix.vecMul (epsVec k) W = 0 := by
  have htwo : Matrix.vecMul (epsVec k) W
      = evenFalling k M n • Matrix.vecMul (epsVec k) (W * W) := by
    conv_lhs => rw [← hW.wgw]
    rw [hW.comm, mul_assoc, ← Matrix.vecMul_vecMul, sympGramClosed_vecMul_eq,
      sympGram_mulVec_epsVec, Matrix.smul_vecMul]
  rw [htwo, evenFalling_eq_zero h, zero_smul]

/-- Conditional even-falling rule above threshold. Blueprint:
`thm:symp_even_falling_rule`. -/
theorem evenFalling_smul_vecMul_epsVec {k : Type*} [CommRing k] {M n : ℕ}
    {W : Matrix (Pairing n) (Pairing n) k}
    (hW : IsCommPenrosePartner (sympGramClosed k M n) W)
    (hu : IsUnit (sympGramClosed k M n)) :
    evenFalling k M n • Matrix.vecMul (epsVec k) W = epsVec k := by
  have hGW : sympGramClosed k M n * W = 1 := hW.mul_eq_one_of_isUnit hu
  rw [← Matrix.smul_vecMul, ← sympGram_mulVec_epsVec, ← sympGramClosed_vecMul_eq,
    Matrix.vecMul_vecMul, hGW, Matrix.vecMul_one]

/-- Conditional shifted-rising rule: the ε-twisted determinant sums invert
the never-vanishing shifted rising factorial — the role swap relative to the
orthogonal series. Blueprint: `thm:symp_rising_shift_rule`. -/
theorem risingShift_smul_vecMul_epsDetVec {k : Type*} [CommRing k] {M n : ℕ}
    {W : Matrix (Pairing n) (Pairing n) k}
    (hW : IsCommPenrosePartner (sympGramClosed k M n) W)
    (hu : IsUnit (sympGramClosed k M n)) :
    risingShift k M n • Matrix.vecMul (epsDetVec k) W = epsDetVec k := by
  have hGW : sympGramClosed k M n * W = 1 := hW.mul_eq_one_of_isUnit hu
  rw [← Matrix.smul_vecMul, ← sympGram_mulVec_epsDetVec, ← sympGramClosed_vecMul_eq,
    Matrix.vecMul_vecMul, hGW, Matrix.vecMul_one]

/-- Per-eigenvalue even-falling rule: the ε-twisted row sums of any commuting Penrose
partner invert the even-falling factorial whenever that **single eigenvalue** is a
unit — no invertibility of the symplectic Gram itself. Strengthens
`evenFalling_smul_vecMul_epsVec`; complementary to the exact vanishing
`vecMul_epsVec_eq_zero` below threshold.
Blueprint: `thm:symp_even_falling_rule_eigen`. -/
theorem evenFalling_smul_vecMul_epsVec_of_partner {k : Type*} [CommRing k] {M n : ℕ}
    {W : Matrix (Pairing n) (Pairing n) k}
    (hW : IsCommPenrosePartner (sympGramClosed k M n) W)
    (hu : IsUnit (evenFalling k M n)) :
    evenFalling k M n • Matrix.vecMul (epsVec k) W = epsVec k :=
  hW.smul_vecMul_eq_of_vecMul_eq_smul
    (by rw [sympGramClosed_vecMul_eq, sympGram_mulVec_epsVec]) hu

/-- Per-eigenvalue shifted-rising rule: the ε-twisted determinant sums of any
commuting Penrose partner invert the shifted rising factorial whenever that single
eigenvalue is a unit — since `risingShift` never vanishes for `M ≥ 1`, this covers
the whole singular band `M < n`, where the Gram-level hypothesis of
`risingShift_smul_vecMul_epsDetVec` is unavailable.
Blueprint: `thm:symp_rising_shift_rule_eigen`. -/
theorem risingShift_smul_vecMul_epsDetVec_of_partner {k : Type*} [CommRing k] {M n : ℕ}
    {W : Matrix (Pairing n) (Pairing n) k}
    (hW : IsCommPenrosePartner (sympGramClosed k M n) W)
    (hu : IsUnit (risingShift k M n)) :
    risingShift k M n • Matrix.vecMul (epsDetVec k) W = epsDetVec k :=
  hW.smul_vecMul_eq_of_vecMul_eq_smul
    (by rw [sympGramClosed_vecMul_eq, sympGram_mulVec_epsDetVec]) hu

end Weingarten
