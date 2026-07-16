/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.MatrixEntryIntegrals

/-!
# The `n = 2` matrix-entry integrals

The four canonical fourth moments of Haar-distributed `U ∈ U(N)` (`N ≥ 2`), proved
from the abstract `HaarExpectation` interface — linearity, normalization, and
bi-invariance only, no characters:

* `E |U_{ii}|⁴ = 2/(N(N+1))`;
* `E |U_{ii}|²|U_{ij}|² = 1/(N(N+1))` (same row, distinct columns);
* `E |U_{ii}|²|U_{jj}|² = 1/(N²−1)` (the parallel pattern);
* `E U_{ii}U_{jj}·conj(U_{ij}U_{ji}) = −1/(N(N²−1))` (the crossed pattern).

All statements are at **general** distinct indices `i ≠ j` — the derivation only uses
distinctness, so the equalization burden is absorbed once here rather than re-paid by
every consumer.

## Method (character-free; the Weingarten `n = 2` system)

Bi-invariance under the *monomial* unitaries (permutations, diagonal phases) plus row
and column unitarity yield three linear equations among the four moments — an
**underdetermined** system. The closing fourth equation `A = 2B` comes from
right-invariance under the π/4 plane rotation `planeUnitary` (the one genuinely
non-monomial unitary), with the charge-unbalanced cross terms killed by
`phaseUnitary _ _ Complex.I` (charges here are at most 2, so `i² = −1 ≠ 1` suffices).
Solving the system gives the values above.

## Provenance (PDF-verified citations)

The values are the `n = 2` unitary Weingarten moments: Collins–Śniady,
arXiv:math-ph/0402073, Cor. 2.4 / eq. (11), with the worked example
`∫ |U₁₁|⁴ = 2/(d(d+1))` on p. 6 (the source PDF misprints the integrand exponent;
the displayed integrand and value are the fourth moment); Collins–Matsumoto,
arXiv:1701.04493, Example 2.3
(`Wg([1,2], d) = 1/(d²−1)`, `Wg([2,1], d) = −1/(d(d²−1))`). They match the machine-
checked `wg_two_one` / `wg_two_swap` of `Weingarten.Haar.WeingartenValues`
(documentation-level tie: the moment values are `Wg`-weighted pattern counts).
-/

namespace Weingarten.Haar

open Matrix

variable {N : ℕ}

namespace HaarExpectation

/-! ### Pointwise unitarity sums, as identities in `C(U(N), ℂ)` -/

/-- Row unitarity: `∑_c |U_{ic}|² = 1` as an observable identity. -/
private theorem rowUnit_obs (i : Fin N) :
    (∑ c, entryObs N i c * star (entryObs N i c))
      = (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) := by
  ext U
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    entryObs_apply, ContinuousMap.one_apply]
  have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  calc ∑ c, U.1 i c * star (U.1 i c)
      = (U.1 * star U.1) i i := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun c _ => by rw [Matrix.star_apply]
    _ = (1 : Matrix (Fin N) (Fin N) ℂ) i i := by rw [hU]
    _ = 1 := Matrix.one_apply_eq i

/-- Row orthogonality: `∑_c U_{ic}·conj(U_{kc}) = 0` for `i ≠ k`, as an observable
identity. -/
private theorem rowOrtho_obs {i k : Fin N} (hik : i ≠ k) :
    (∑ c, entryObs N i c * star (entryObs N k c))
      = (0 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) := by
  ext U
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    entryObs_apply, ContinuousMap.zero_apply]
  have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  calc ∑ c, U.1 i c * star (U.1 k c)
      = (U.1 * star U.1) i k := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun c _ => by rw [Matrix.star_apply]
    _ = (1 : Matrix (Fin N) (Fin N) ℂ) i k := by rw [hU]
    _ = 0 := Matrix.one_apply_ne hik

/-- Column unitarity: `∑_r |U_{rj}|² = 1` as an observable identity (from
`star U * U = 1`). -/
private theorem colUnit_obs (j : Fin N) :
    (∑ r, entryObs N r j * star (entryObs N r j))
      = (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) := by
  ext U
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    entryObs_apply, ContinuousMap.one_apply]
  have hU : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  calc ∑ r, U.1 r j * star (U.1 r j)
      = (star U.1 * U.1) j j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun r _ => by
          rw [Matrix.star_apply, mul_comm]
    _ = (1 : Matrix (Fin N) (Fin N) ℂ) j j := by rw [hU]
    _ = 1 := Matrix.one_apply_eq j

/-- Two distinct indices force `2 ≤ N`. -/
private theorem two_le_of_ne {i j : Fin N} (hij : i ≠ j) : 2 ≤ N := by
  have h1 := i.isLt
  have h2 := j.isLt
  have h3 : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  omega

end HaarExpectation

/-! ### The squared-modulus observable -/

/-- The squared-modulus entry observable `U ↦ |U_{ab}|²`, as an element of
`C(U(N), ℂ)`. -/
noncomputable def absSqObs (N : ℕ) (a b : Fin N) : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  entryObs N a b * star (entryObs N a b)

@[simp] theorem absSqObs_apply (a b : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    absSqObs N a b U = U.1 a b * star (U.1 a b) := rfl

namespace HaarExpectation

/-! ### Equalization: same-pattern moments are equal (permutation bi-invariance) -/

/-- Column equalization at a fixed anchor `|U_{ii}|²`: for any row `a`, the moment
`E (|U_{ac}|²·|U_{ii}|²)` does not depend on the column `c` as long as `c ≠ i`
(exchange the columns `j ↔ c` by a right permutation fixing column `i`). -/
private theorem eqz_swap_col (E : HaarExpectation N) (a : Fin N) {i j c : Fin N}
    (hji : j ≠ i) (hci : c ≠ i) :
    E (absSqObs N a c * absSqObs N i i) = E (absSqObs N a j * absSqObs N i i) := by
  have hswap : (absSqObs N a j * absSqObs N i i).comp
      (ContinuousMap.mulRight (permUnitary N (Equiv.swap j c)))
      = absSqObs N a c * absSqObs N i i := by
    ext U
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
      ContinuousMap.mul_apply, absSqObs_apply]
    rw [mul_permUnitary_apply, mul_permUnitary_apply, Equiv.symm_swap,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hci)]
  rw [← hswap, E.map_right_mul]

/-- Row equalization at a fixed anchor `|U_{ii}|²`: the moment
`E (|U_{ri}|²·|U_{ii}|²)` does not depend on the row `r` as long as `r ≠ i`. -/
private theorem eqz_swap_row (E : HaarExpectation N) {i j r : Fin N}
    (hji : j ≠ i) (hri : r ≠ i) :
    E (absSqObs N r i * absSqObs N i i) = E (absSqObs N j i * absSqObs N i i) := by
  have hswap : (absSqObs N j i * absSqObs N i i).comp
      (ContinuousMap.mulLeft (permUnitary N (Equiv.swap j r)))
      = absSqObs N r i * absSqObs N i i := by
    ext U
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
      ContinuousMap.mul_apply, absSqObs_apply]
    rw [permUnitary_mul_apply, permUnitary_mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hri)]
  rw [← hswap, E.map_left_mul]

/-! ### The three unitarity contractions (the linear system, minus its closure) -/

/-- Contraction (1): `A + (N−1)·B = 1/N`, from row-`i` unitarity against the anchor
`|U_{ii}|²`. -/
private theorem eq_one (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N i i * absSqObs N i i)
      + ((N : ℂ) - 1) * E (absSqObs N i j * absSqObs N i i) = (N : ℂ)⁻¹ := by
  have hN := HaarExpectation.two_le_of_ne hij
  have hanchor : E (absSqObs N i i) = (N : ℂ)⁻¹ := integral_normSq_entry E i i
  have hsum : E (absSqObs N i i) = ∑ c, E (absSqObs N i c * absSqObs N i i) := by
    conv_lhs => rw [show absSqObs N i i = 1 * absSqObs N i i from (one_mul _).symm,
      ← rowUnit_obs i, Finset.sum_mul]
    exact E.map_sum _ _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have htail : ∀ c ∈ Finset.univ.erase i,
      E (absSqObs N i c * absSqObs N i i) = E (absSqObs N i j * absSqObs N i i) :=
    fun c hc => eqz_swap_col E i (Ne.symm hij) (Finset.ne_of_mem_erase hc)
  rw [Finset.sum_congr rfl htail, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hsum
  rw [← hanchor, hsum]

/-- Contraction (1′): `A + (N−1)·B′ = 1/N`, from column-`i` unitarity — the column
mirror of (1); together they give `B = B′` with no transpose invariance. -/
private theorem eq_one' (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N i i * absSqObs N i i)
      + ((N : ℂ) - 1) * E (absSqObs N j i * absSqObs N i i) = (N : ℂ)⁻¹ := by
  have hN := HaarExpectation.two_le_of_ne hij
  have hanchor : E (absSqObs N i i) = (N : ℂ)⁻¹ := integral_normSq_entry E i i
  have hsum : E (absSqObs N i i) = ∑ r, E (absSqObs N r i * absSqObs N i i) := by
    conv_lhs => rw [show absSqObs N i i = 1 * absSqObs N i i from (one_mul _).symm,
      ← colUnit_obs i, Finset.sum_mul]
    exact E.map_sum _ _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have htail : ∀ r ∈ Finset.univ.erase i,
      E (absSqObs N r i * absSqObs N i i) = E (absSqObs N j i * absSqObs N i i) :=
    fun r hr => eqz_swap_row E (Ne.symm hij) (Finset.ne_of_mem_erase hr)
  rw [Finset.sum_congr rfl htail, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hsum
  rw [← hanchor, hsum]

/-- Contraction (2): `B′ + (N−1)·C = 1/N`, from row-`j` unitarity against the anchor
`|U_{ii}|²`. -/
private theorem eq_two (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N j i * absSqObs N i i)
      + ((N : ℂ) - 1) * E (absSqObs N j j * absSqObs N i i) = (N : ℂ)⁻¹ := by
  have hN := HaarExpectation.two_le_of_ne hij
  have hanchor : E (absSqObs N i i) = (N : ℂ)⁻¹ := integral_normSq_entry E i i
  have hsum : E (absSqObs N i i) = ∑ c, E (absSqObs N j c * absSqObs N i i) := by
    conv_lhs => rw [show absSqObs N i i = 1 * absSqObs N i i from (one_mul _).symm,
      ← rowUnit_obs j, Finset.sum_mul]
    exact E.map_sum _ _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have htail : ∀ c ∈ Finset.univ.erase i,
      E (absSqObs N j c * absSqObs N i i) = E (absSqObs N j j * absSqObs N i i) :=
    fun c hc => eqz_swap_col E j (Ne.symm hij) (Finset.ne_of_mem_erase hc)
  rw [Finset.sum_congr rfl htail, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hsum
  rw [← hanchor, hsum]

/-- The column pair `(|U_{ij}|², |U_{jj}|²)` has the same moment as the column pair
`(|U_{ji}|², |U_{ii}|²)` (exchange the two columns). `_hij` is deliberately unused:
the column exchange needs no distinctness; the hypothesis keeps the equalization
helpers' signatures uniform at the call sites. -/
private theorem eqz_colpair (E : HaarExpectation N) {i j : Fin N} (_hij : i ≠ j) :
    E (absSqObs N i j * absSqObs N j j) = E (absSqObs N j i * absSqObs N i i) := by
  have hswap : (absSqObs N j i * absSqObs N i i).comp
      (ContinuousMap.mulRight (permUnitary N (Equiv.swap i j)))
      = absSqObs N i j * absSqObs N j j := by
    ext U
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
      ContinuousMap.mul_apply, absSqObs_apply]
    rw [mul_permUnitary_apply, mul_permUnitary_apply, Equiv.symm_swap,
      Equiv.swap_apply_left]
    ring
  rw [← hswap, E.map_right_mul]

/-- Crossed-term equalization: the `c`-th term of contraction (3) equals the canonical
crossed moment, for every `c ≠ j` (exchange columns `i ↔ c` by a right permutation
fixing column `j`). -/
private theorem eqz_crossed (E : HaarExpectation N) {i j c : Fin N} (hij : i ≠ j)
    (hcj : c ≠ j) :
    E (entryObs N i c * star (entryObs N j c)
        * (entryObs N j j * star (entryObs N i j)))
      = E (entryObs N i i * entryObs N j j
        * star (entryObs N i j) * star (entryObs N j i)) := by
  have hswap : (entryObs N i i * entryObs N j j
        * star (entryObs N i j) * star (entryObs N j i)).comp
      (ContinuousMap.mulRight (permUnitary N (Equiv.swap i c)))
      = entryObs N i c * star (entryObs N j c)
        * (entryObs N j j * star (entryObs N i j)) := by
    ext U
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, entryObs_apply]
    rw [mul_permUnitary_apply, mul_permUnitary_apply, mul_permUnitary_apply,
      mul_permUnitary_apply, Equiv.symm_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hcj)]
    ring
  rw [← hswap, E.map_right_mul]

/-- Contraction (3): `B′ + (N−1)·D = 0`, from the row orthogonality
`∑_c U_{ic}·conj(U_{jc}) = 0` against `U_{jj}·conj(U_{ij})`. -/
private theorem eq_three (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N j i * absSqObs N i i)
      + ((N : ℂ) - 1) * E (entryObs N i i * entryObs N j j
          * star (entryObs N i j) * star (entryObs N j i)) = 0 := by
  have hN := HaarExpectation.two_le_of_ne hij
  set G : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
    entryObs N j j * star (entryObs N i j) with hG
  have hzero : (0 : ℂ)
      = ∑ c, E (entryObs N i c * star (entryObs N j c) * G) := by
    have hobs : (0 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
        = ∑ c, entryObs N i c * star (entryObs N j c) * G := by
      rw [← Finset.sum_mul, rowOrtho_obs hij, zero_mul]
    calc (0 : ℂ) = E 0 := (map_zero E.toFun).symm
      _ = E (∑ c, entryObs N i c * star (entryObs N j c) * G) := by rw [← hobs]
      _ = ∑ c, E (entryObs N i c * star (entryObs N j c) * G) := E.map_sum _ _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hzero
  have hhead : E (entryObs N i j * star (entryObs N j j) * G)
      = E (absSqObs N j i * absSqObs N i i) := by
    have h1 : entryObs N i j * star (entryObs N j j) * G
        = absSqObs N i j * absSqObs N j j := by
      rw [hG]; ext U
      simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, entryObs_apply,
        absSqObs_apply]
      ring
    rw [h1, eqz_colpair E hij]
  have htail : ∀ c ∈ Finset.univ.erase j,
      E (entryObs N i c * star (entryObs N j c) * G)
        = E (entryObs N i i * entryObs N j j
            * star (entryObs N i j) * star (entryObs N j i)) := by
    intro c hc
    rw [hG]
    exact eqz_crossed E hij (Finset.ne_of_mem_erase hc)
  rw [hhead, Finset.sum_congr rfl htail, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] at hzero
  exact hzero.symm

/-! ### The rotation closure `A = 2B`

The one genuinely non-monomial step: right-invariance under the π/4 plane rotation.
The composed observable `|(U·R)_{ii}|⁴` expands into nine terms; the six with unbalanced
column-`i` phase charge die by translation with `phaseUnitary _ i Complex.I` (charges
are at most 2 here, so powers of `i` never hit `1`), and the three survivors give
`A = s⁴·(2A + 4B)` with `s⁴ = 1/4`.

Provenance: the method belongs to the elementary-invariance genre of low-order `U(N)`
integrals (cf. S. Samuel, J. Math. Phys. 21 (1980) 2695 — `U(N)` integrals by elementary
invariance at low order); this exact closing-equation presentation is unlocated in print
(no novelty inferred). -/

/-- A Haar expectation preserves subtraction. -/
private theorem map_sub' (E : HaarExpectation N)
    (f g : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (f - g) = E f - E g :=
  E.toFun.map_sub f g

/-- `Complex.I` lies on the unit circle. -/
theorem I_mul_star_I : Complex.I * star Complex.I = 1 := by
  rw [Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg]

private theorem hw_I : (Complex.I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem hw_sI : (star Complex.I : ℂ) ≠ 1 := by
  rw [Complex.star_def, Complex.conj_I]
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem hw_sII : (star Complex.I * star Complex.I : ℂ) ≠ 1 := by
  rw [Complex.star_def, Complex.conj_I, neg_mul_neg, Complex.I_mul_I]
  norm_num

/-- The rotation closure: `E |U_{ii}|⁴ = 2·E (|U_{ij}|²|U_{ii}|²)`. -/
private theorem eq_rot (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N i i * absSqObs N i i)
      = 2 * E (absSqObs N i j * absSqObs N i i) := by
  classical
  set e : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := entryObs N i i with he
  set f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := entryObs N i j with hf
  set T1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := absSqObs N i i * absSqObs N i i
    with hT1
  set T2 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := absSqObs N i j * absSqObs N i j
    with hT2
  set T5 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := absSqObs N i i * absSqObs N i j
    with hT5
  set T3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := e * e * star f * star f with hT3
  set T4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := star e * star e * f * f with hT4
  set T6 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := e * e * star e * star f with hT6
  set T7 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := e * star e * star e * f with hT7
  set T8 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := e * f * star f * star f with hT8
  set T9 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) := star e * f * f * star f with hT9
  set P : Matrix.unitaryGroup (Fin N) ℂ := phaseUnitary N i Complex.I I_mul_star_I
    with hP
  have hkill : ∀ (T : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) (w : ℂ), w ≠ 1 →
      T.comp (ContinuousMap.mulRight P) = w • T → E T = 0 :=
    fun T w hw h => E.integral_eq_zero_of_charge_right hw h
  have hPe : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
      (U * P).1 i i = U.1 i i * Complex.I := by
    intro U; rw [hP, mul_phaseUnitary_apply, if_pos rfl]
  have hPf : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
      (U * P).1 i j = U.1 i j := by
    intro U; rw [hP, mul_phaseUnitary_apply, if_neg (Ne.symm hij), mul_one]
  have hK3 : E T3 = 0 := by
    refine hkill T3 (Complex.I * Complex.I) (by rw [Complex.I_mul_I]; norm_num) ?_
    ext U
    simp only [hT3, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
      entryObs_apply, smul_eq_mul, hPe U, hPf U]
    ring
  have hK4 : E T4 = 0 := by
    refine hkill T4 (star Complex.I * star Complex.I) hw_sII ?_
    · ext U
      simp only [hT4, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
        entryObs_apply, smul_eq_mul, hPe U, hPf U, star_mul']
      ring
  have hK6 : E T6 = 0 := by
    refine hkill T6 (Complex.I * Complex.I * star Complex.I) ?_ ?_
    · rw [Complex.I_mul_I, Complex.star_def, Complex.conj_I, neg_mul_neg, one_mul]
      exact hw_I
    · ext U
      simp only [hT6, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
        entryObs_apply, smul_eq_mul, hPe U, hPf U, star_mul']
      ring
  have hK7 : E T7 = 0 := by
    refine hkill T7 (Complex.I * star Complex.I * star Complex.I) ?_ ?_
    · rw [I_mul_star_I, one_mul]
      exact hw_sI
    · ext U
      simp only [hT7, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
        entryObs_apply, smul_eq_mul, hPe U, hPf U, star_mul']
      ring
  have hK8 : E T8 = 0 := by
    refine hkill T8 Complex.I hw_I ?_
    · ext U
      simp only [hT8, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
        entryObs_apply, smul_eq_mul, hPe U, hPf U]
      ring
  have hK9 : E T9 = 0 := by
    refine hkill T9 (star Complex.I) hw_sI ?_
    · ext U
      simp only [hT9, he, hf, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
        entryObs_apply, smul_eq_mul, hPe U, hPf U, star_mul']
      ring
  have hexp : T1.comp (ContinuousMap.mulRight (planeUnitary N i j hij))
      = invSqrtTwo ^ 4 • (T1 + T2 + T3 + T4 + (4 : ℂ) • T5
          - (2 : ℂ) • T6 - (2 : ℂ) • T7 - (2 : ℂ) • T8 - (2 : ℂ) • T9) := by
    ext U
    simp only [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, he, hf,
      ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
      ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.sub_apply, absSqObs_apply,
      entryObs_apply, smul_eq_mul]
    rw [mul_planeUnitary_fst hij U i]
    simp only [star_sub, star_mul', invSqrtTwo_star]
    ring
  have hT2A : E T2 = E T1 := by
    have hswap : T1.comp
        (ContinuousMap.mulRight (permUnitary N (Equiv.swap i j)))
        = T2 := by
      ext U
      simp only [hT1, hT2, ContinuousMap.comp_apply, ContinuousMap.coe_mulRight,
        ContinuousMap.mul_apply, absSqObs_apply]
      rw [mul_permUnitary_apply, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [← hswap, E.map_right_mul]
  have hT5B : E T5 = E (absSqObs N i j * absSqObs N i i) := by
    have : T5 = absSqObs N i j * absSqObs N i i := mul_comm _ _
    rw [this]
  have hs4 : invSqrtTwo ^ 4 = (4 : ℂ)⁻¹ := by
    have h2 := invSqrtTwo_mul_self
    calc invSqrtTwo ^ 4
        = (invSqrtTwo * invSqrtTwo) * (invSqrtTwo * invSqrtTwo) := by ring
      _ = (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by rw [h2]
      _ = (4 : ℂ)⁻¹ := by norm_num
  have hA : E T1 = invSqrtTwo ^ 4 * (E T1 + E T2 + E T3 + E T4 + 4 * E T5
      - 2 * E T6 - 2 * E T7 - 2 * E T8 - 2 * E T9) := by
    calc E T1
        = E (T1.comp (ContinuousMap.mulRight (planeUnitary N i j hij))) :=
          (E.map_right_mul _ _).symm
      _ = E (invSqrtTwo ^ 4 • (T1 + T2 + T3 + T4 + (4 : ℂ) • T5
            - (2 : ℂ) • T6 - (2 : ℂ) • T7 - (2 : ℂ) • T8 - (2 : ℂ) • T9)) := by
          rw [hexp]
      _ = invSqrtTwo ^ 4 * (E T1 + E T2 + E T3 + E T4 + 4 * E T5
            - 2 * E T6 - 2 * E T7 - 2 * E T8 - 2 * E T9) := by
          rw [E.map_smul]
          congr 1
          simp only [map_sub' E, HaarExpectation.map_add, HaarExpectation.map_smul]
  rw [hK3, hK4, hK6, hK7, hK8, hK9, hT2A, hs4] at hA
  rw [← hT5B]
  linear_combination (2 : ℂ) * hA

/-! ### Solving the system: the four public values -/

/-- Nonzero denominators for `2 ≤ N`, over ℂ. -/
private theorem denomsC (hN : 2 ≤ N) :
    (N : ℂ) ≠ 0 ∧ (N : ℂ) - 1 ≠ 0 ∧ (N : ℂ) + 1 ≠ 0 ∧ (N : ℂ) ^ 2 - 1 ≠ 0 := by
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm : (N : ℂ) - 1 ≠ 0 := by
    intro h
    have h1 : (N : ℂ) = 1 := by linear_combination h
    have h2 : N = 1 := Nat.cast_eq_one.mp h1
    omega
  have hp : (N : ℂ) + 1 ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
    have h2 : N + 1 = 0 := Nat.cast_eq_zero.mp h1
    omega
  refine ⟨h0, hm, hp, ?_⟩
  have hfac : (N : ℂ) ^ 2 - 1 = ((N : ℂ) - 1) * ((N : ℂ) + 1) := by ring
  rw [hfac]
  exact mul_ne_zero hm hp

/-- **The same-row fourth moment**: `E (|U_{ij}|²·|U_{ii}|²) = 1/(N(N+1))` for `i ≠ j`.

This is the `n = 2` Weingarten moment of the same-row pattern (Collins–Śniady,
arXiv:math-ph/0402073, Cor. 2.4/eq. (11); value cross-checked against the p. 6 worked
example and Collins–Matsumoto, arXiv:1701.04493, Ex. 2.3 — both PDF-verified). -/
theorem integral_absSq_mul_absSq_row (E : HaarExpectation N) {i j : Fin N}
    (hij : i ≠ j) :
    E (absSqObs N i j * absSqObs N i i) = ((N : ℂ) * ((N : ℂ) + 1))⁻¹ := by
  obtain ⟨h0, hm, hp, hq⟩ := denomsC (HaarExpectation.two_le_of_ne hij)
  have hkey : ((N : ℂ) + 1) * E (absSqObs N i j * absSqObs N i i) = (N : ℂ)⁻¹ := by
    linear_combination (eq_one E hij) - (eq_rot E hij)
  have hval : E (absSqObs N i j * absSqObs N i i) = (N : ℂ)⁻¹ / ((N : ℂ) + 1) := by
    rw [eq_div_iff hp]
    linear_combination hkey
  rw [hval]
  field_simp

/-- **The single-entry fourth moment**: `E |U_{ii}|⁴ = 2/(N(N+1))`
(Collins–Śniady, arXiv:math-ph/0402073, p. 6 worked example: `∫|U₁₁|⁴ = 2/(d(d+1))`,
PDF-verified). -/
theorem integral_absSq_sq (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (absSqObs N i i * absSqObs N i i) = 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹ := by
  rw [eq_rot E hij, integral_absSq_mul_absSq_row E hij]

/-- **The same-column fourth moment** equals the same-row one:
`E (|U_{ji}|²·|U_{ii}|²) = 1/(N(N+1))` — no transpose invariance needed; the column
contraction supplies it. -/
theorem integral_absSq_mul_absSq_col (E : HaarExpectation N) {i j : Fin N}
    (hij : i ≠ j) :
    E (absSqObs N j i * absSqObs N i i) = ((N : ℂ) * ((N : ℂ) + 1))⁻¹ := by
  obtain ⟨h0, hm, hp, hq⟩ := denomsC (HaarExpectation.two_le_of_ne hij)
  have hBB : E (absSqObs N j i * absSqObs N i i)
      = E (absSqObs N i j * absSqObs N i i) := by
    have h0' : ((N : ℂ) - 1) * (E (absSqObs N j i * absSqObs N i i)
        - E (absSqObs N i j * absSqObs N i i)) = 0 := by
      linear_combination (eq_one' E hij) - (eq_one E hij)
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h hm
    · exact sub_eq_zero.mp h
  rw [hBB, integral_absSq_mul_absSq_row E hij]

/-- **The parallel fourth moment**: `E (|U_{jj}|²·|U_{ii}|²) = 1/(N²−1)` for `i ≠ j`
(the `Wg(id)` diagonal of the `n = 2` Weingarten formula; Collins–Matsumoto,
arXiv:1701.04493, Ex. 2.3, PDF-verified; matches
`Weingarten.Haar.wg_two_one`). -/
theorem integral_absSq_mul_absSq_diag (E : HaarExpectation N) {i j : Fin N}
    (hij : i ≠ j) :
    E (absSqObs N j j * absSqObs N i i) = ((N : ℂ) ^ 2 - 1)⁻¹ := by
  obtain ⟨h0, hm, hp, hq⟩ := denomsC (HaarExpectation.two_le_of_ne hij)
  have hkey : ((N : ℂ) - 1) * E (absSqObs N j j * absSqObs N i i)
      = (N : ℂ)⁻¹ - ((N : ℂ) * ((N : ℂ) + 1))⁻¹ := by
    linear_combination (eq_two E hij) - (integral_absSq_mul_absSq_col E hij)
  have hval : E (absSqObs N j j * absSqObs N i i)
      = ((N : ℂ)⁻¹ - ((N : ℂ) * ((N : ℂ) + 1))⁻¹) / ((N : ℂ) - 1) := by
    rw [eq_div_iff hm]
    linear_combination hkey
  rw [hval]
  field_simp
  ring

/-- **The crossed fourth moment**: `E (U_{ii}U_{jj}·conj(U_{ij}U_{ji})) = −1/(N(N²−1))`
for `i ≠ j` (the `Wg(swap)` off-diagonal of the `n = 2` Weingarten formula;
Collins–Matsumoto, arXiv:1701.04493, Ex. 2.3, PDF-verified; matches
`Weingarten.Haar.wg_two_swap`). -/
theorem integral_entry_crossed (E : HaarExpectation N) {i j : Fin N} (hij : i ≠ j) :
    E (entryObs N i i * entryObs N j j * star (entryObs N i j) * star (entryObs N j i))
      = -((N : ℂ) * ((N : ℂ) ^ 2 - 1))⁻¹ := by
  obtain ⟨h0, hm, hp, hq⟩ := denomsC (HaarExpectation.two_le_of_ne hij)
  have hkey : ((N : ℂ) - 1) * E (entryObs N i i * entryObs N j j
        * star (entryObs N i j) * star (entryObs N j i))
      = -((N : ℂ) * ((N : ℂ) + 1))⁻¹ := by
    linear_combination (eq_three E hij) - (integral_absSq_mul_absSq_col E hij)
  have hval : E (entryObs N i i * entryObs N j j
        * star (entryObs N i j) * star (entryObs N j i))
      = -((N : ℂ) * ((N : ℂ) + 1))⁻¹ / ((N : ℂ) - 1) := by
    rw [eq_div_iff hm]
    linear_combination hkey
  rw [hval]
  field_simp
  ring

/-! ### Stage 2: the fourth moment of the trace

The diagonal 4-term `U_{aa}U_{bb}·conj(U_{cc}U_{dd})` transforms under the diagonal
phase at `r` with a weight that is a **universal** product of `if`-factors
(`diag_term_phase` — one hypothesis-free covariance lemma replaces every case-by-case
kill argument). Classification by pair matching (`diag_term_value`) then evaluates
every term from the Stage-1 values.

Literature (PDF-verified): the sharp `N ≥ 2` anchor is
**Diaconis–Evans, Trans. AMS 353 (2001), Thm 2.1(a)** (condition
`n ≥ max(Σ j·a_j, Σ j·b_j)`); the original Diaconis–Shahshahani 1994 Thm 2 carries a
condition that Diaconis–Evans explicitly label *incorrect* — it is cited for priority
only. The exact value at every `N` is Rains, Electron. J. Combin. 5 (1998) #R12,
Thm 1.1: `E|Tr U|^{2n} = #{σ ∈ S_n : LIS(σ) ≤ N}` — giving `2` for `N ≥ 2` and `1` at
`N = 1`. The pattern-sum display is Drouffe–Zuber, Phys. Rep. 102 (1983), (A.22)–(A.26):
`F₂(I,I) = 2!(C_{[1²]}N² + C_{[2]}N) = 2`. -/

/-- **Universal phase covariance of the diagonal 4-term** (no hypotheses): left
translation by the diagonal phase at `r` rescales `U_{aa}U_{bb}·conj(U_{cc}U_{dd})` by
the indicated product of `if`-factors. -/
private theorem diag_term_phase (a b c d r : Fin N) :
    (entryObs N a a * entryObs N b b
        * star (entryObs N c c) * star (entryObs N d d)).comp
      (ContinuousMap.mulLeft (phaseUnitary N r Complex.I I_mul_star_I))
    = ((if a = r then Complex.I else 1) * (if b = r then Complex.I else 1)
        * (if c = r then star Complex.I else 1) * (if d = r then star Complex.I else 1))
      • (entryObs N a a * entryObs N b b
        * star (entryObs N c c) * star (entryObs N d d)) := by
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
    entryObs_apply, smul_eq_mul]
  rw [phaseUnitary_mul_apply, phaseUnitary_mul_apply, phaseUnitary_mul_apply,
    phaseUnitary_mul_apply]
  simp only [star_mul', apply_ite (star : ℂ → ℂ), star_one]
  ring

/-- The parametric kill: whenever the universal phase weight at some `r` is a scalar
`w ≠ 1`, the diagonal 4-term has vanishing expectation. -/
private theorem diag_term_kill (E : HaarExpectation N) (r : Fin N) {a b c d : Fin N}
    (w : ℂ) (hw : w ≠ 1)
    (hwa : (if a = r then Complex.I else 1) * (if b = r then Complex.I else 1)
        * (if c = r then star Complex.I else 1) * (if d = r then star Complex.I else 1)
        = w) :
    E (entryObs N a a * entryObs N b b
        * star (entryObs N c c) * star (entryObs N d d)) = 0 := by
  refine E.integral_eq_zero_of_charge
    (g := phaseUnitary N r Complex.I I_mul_star_I) hw ?_
  rw [← hwa]
  exact diag_term_phase a b c d r

/-- **Classification of the diagonal 4-term moments**: the value is the single-entry
fourth moment `A` when all four indices coincide, the parallel value `C` when the two
pairs match as sets with `a ≠ b`, and `0` otherwise (pair-multiset mismatch — killed by
the universal phase weight). -/
private theorem diag_term_value (E : HaarExpectation N) (hN : 2 ≤ N)
    (a b c d : Fin N) :
    E (entryObs N a a * entryObs N b b
        * star (entryObs N c c) * star (entryObs N d d))
      = if a = b then
          (if c = a ∧ d = a then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹ else 0)
        else if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then ((N : ℂ) ^ 2 - 1)⁻¹ else 0 := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  by_cases hab : a = b
  · rw [hab, if_pos rfl]
    by_cases hcb : c = b
    · rw [hcb]
      by_cases hdb : d = b
      · rw [hdb, if_pos ⟨rfl, rfl⟩]
        have hobs : entryObs N b b * entryObs N b b
            * star (entryObs N b b) * star (entryObs N b b)
            = absSqObs N b b * absSqObs N b b := by
          ext U
          simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply,
            entryObs_apply, absSqObs_apply]
          ring
        rw [hobs]
        obtain ⟨j, hj⟩ := exists_ne b
        exact integral_absSq_sq E (Ne.symm hj)
      · rw [if_neg (fun h => hdb h.2)]
        exact diag_term_kill E d (star Complex.I) hw_sI (by simp [Ne.symm hdb])
    · rw [if_neg (fun h => hcb h.1)]
      by_cases hdc : d = c
      · rw [hdc]
        exact diag_term_kill E c (star Complex.I * star Complex.I) hw_sII
          (by simp [Ne.symm hcb])
      · exact diag_term_kill E c (star Complex.I) hw_sI
          (by simp [Ne.symm hcb, hdc])
  · rw [if_neg hab]
    by_cases h1 : c = a ∧ d = b
    · obtain ⟨hca, hdb⟩ := h1
      rw [if_pos (Or.inl ⟨hca, hdb⟩), hca, hdb]
      have hobs : entryObs N a a * entryObs N b b
          * star (entryObs N a a) * star (entryObs N b b)
          = absSqObs N b b * absSqObs N a a := by
        ext U
        simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply,
          entryObs_apply, absSqObs_apply]
        ring
      rw [hobs]
      exact integral_absSq_mul_absSq_diag E hab
    · by_cases h2 : c = b ∧ d = a
      · obtain ⟨hcb, hda⟩ := h2
        rw [if_pos (Or.inr ⟨hcb, hda⟩), hcb, hda]
        have hobs : entryObs N a a * entryObs N b b
            * star (entryObs N b b) * star (entryObs N a a)
            = absSqObs N b b * absSqObs N a a := by
          ext U
          simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply,
            entryObs_apply, absSqObs_apply]
          ring
        rw [hobs]
        exact integral_absSq_mul_absSq_diag E hab
      · rw [if_neg (fun h => h.elim h1 h2)]
        by_cases hca : c = a
        · rw [hca]
          have hdb : d ≠ b := fun h => h1 ⟨hca, h⟩
          by_cases hda : d = a
          · rw [hda]
            exact diag_term_kill E b Complex.I hw_I (by simp [hab])
          · exact diag_term_kill E d (star Complex.I) hw_sI
              (by simp [Ne.symm hda, Ne.symm hdb])
        · by_cases hcb : c = b
          · rw [hcb]
            have hda : d ≠ a := fun h => h2 ⟨hcb, h⟩
            by_cases hdb : d = b
            · rw [hdb]
              exact diag_term_kill E a Complex.I hw_I (by simp [Ne.symm hab])
            · exact diag_term_kill E d (star Complex.I) hw_sI
                (by simp [Ne.symm hda, Ne.symm hdb])
          · by_cases hdc : d = c
            · rw [hdc]
              exact diag_term_kill E c (star Complex.I * star Complex.I) hw_sII
                (by simp [Ne.symm hca, Ne.symm hcb])
            · exact diag_term_kill E c (star Complex.I) hw_sI
                (by simp [Ne.symm hca, Ne.symm hcb, hdc])

/-! ### The trace charge kills (β-expansion feed) -/

/-- `E (Tr U)² = 0`: the observable carries charge `2` under the central phase, so the
Collins–Śniady eq. (12) argument (PDF-verified) kills it. -/
theorem integral_trace_sq (E : HaarExpectation N) :
    E (traceObs N * traceObs N) = 0 := by
  refine E.integral_eq_zero_of_charge (g := scalarUnitary N Complex.I I_mul_star_I)
    (w := Complex.I * Complex.I) (by rw [Complex.I_mul_I]; norm_num) ?_
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, traceObs_apply, smul_eq_mul]
  rw [scalarUnitary_mul_val, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `E (conj Tr U)² = 0`: charge `−2`. -/
theorem integral_star_trace_sq (E : HaarExpectation N) :
    E (star (traceObs N) * star (traceObs N)) = 0 := by
  refine E.integral_eq_zero_of_charge (g := scalarUnitary N Complex.I I_mul_star_I)
    (w := star Complex.I * star Complex.I) hw_sII ?_
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.smul_apply,
    traceObs_apply, smul_eq_mul]
  rw [scalarUnitary_mul_val, Matrix.trace_smul, smul_eq_mul, star_mul']
  ring

/-- `E (conj Tr U) = 0`: the conjugate-trace mean vanishes (sign trick at `−1`). -/
theorem integral_star_trace (E : HaarExpectation N) :
    E (star (traceObs N)) = 0 := by
  refine E.integral_eq_zero_of_neg_comp
    (g := scalarUnitary N (-1) (by rw [star_neg, star_one]; ring)) ?_
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.star_apply, ContinuousMap.neg_apply, traceObs_apply]
  rw [scalarUnitary_mul_val, Matrix.trace_smul]
  simp

/-! ### The fourth moment of the trace -/

/-- **`E |Tr U|⁴ = 2` for `N ≥ 2`.**

Expanding the trace over diagonal entries, the only surviving 4-tuples are the
all-equal ones (`N` terms of the single-entry value `A = 2/(N(N+1))`) and the matched
distinct pairs (`2N(N−1)` terms of the parallel value `C = 1/(N²−1)`), giving
`2/(N+1) + 2N/(N+1) = 2`.

Literature (PDF-verified): the sharp range is Diaconis–Evans, Trans. AMS 353
(2001), Thm 2.1(a) at `a = b = (2)` (`n ≥ 2`); the exact value at every `N` is Rains,
Electron. J. Combin. 5 (1998) #R12, Thm 1.1 (`#{σ ∈ S₂ : LIS(σ) ≤ N}`); the
Weingarten pattern sum is Drouffe–Zuber, Phys. Rep. 102 (1983), (A.22)–(A.26)
(`F₂(I,I) = 2`). At `N = 1` the value is `1`, which is why `2 ≤ N` is required. -/
theorem integral_absTrace_pow_four (E : HaarExpectation N) (hN : 2 ≤ N) :
    E (traceObs N * star (traceObs N) * (traceObs N * star (traceObs N))) = 2 := by
  obtain ⟨h0, hm, hp, hq⟩ := denomsC hN
  -- (1) expand into the diagonal quadruple sum
  have hexp : traceObs N * star (traceObs N) * (traceObs N * star (traceObs N))
      = ∑ a, ∑ b, ∑ c, ∑ d, entryObs N a a * entryObs N b b
          * star (entryObs N c c) * star (entryObs N d d) := by
    ext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply,
      ContinuousMap.sum_apply, traceObs_apply, entryObs_apply]
    have ht : (U.1).trace = ∑ a, U.1 a a := rfl
    rw [ht, star_sum]
    calc (∑ a, U.1 a a) * (∑ c, star (U.1 c c))
          * ((∑ b, U.1 b b) * (∑ d, star (U.1 d d)))
        = (∑ a, ∑ c, U.1 a a * star (U.1 c c))
          * (∑ b, ∑ d, U.1 b b * star (U.1 d d)) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
      _ = ∑ a, ∑ b, (∑ c, U.1 a a * star (U.1 c c))
          * (∑ d, U.1 b b * star (U.1 d d)) := by
          rw [Finset.sum_mul_sum]
      _ = ∑ a, ∑ b, ∑ c, ∑ d, U.1 a a * U.1 b b
          * star (U.1 c c) * star (U.1 d d) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
            ring
  rw [hexp]
  -- (2) push `E` through the quadruple sum
  rw [E.map_sum]
  rw [Finset.sum_congr rfl fun a _ => E.map_sum _ _]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => E.map_sum _ _]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => E.map_sum _ _]
  -- (3) evaluate every term by the classification
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      diag_term_value E hN a b c d]
  -- (4) collapse the inner double sums
  have hinner : ∀ a b : Fin N,
      (∑ c : Fin N, ∑ d : Fin N,
        if a = b then
          (if c = a ∧ d = a then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹ else 0)
        else if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then ((N : ℂ) ^ 2 - 1)⁻¹ else 0)
      = if a = b then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹
        else 2 * ((N : ℂ) ^ 2 - 1)⁻¹ := by
    intro a b
    by_cases hab : a = b
    · simp only [if_pos hab, ite_and]
      have hc : ∀ c : Fin N,
          (∑ d : Fin N, if c = a then
            (if d = a then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹ else 0) else 0)
          = if c = a then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹ else 0 := by
        intro c
        by_cases hc' : c = a
        · simp [hc', Finset.sum_ite_eq']
        · simp [hc']
      rw [Finset.sum_congr rfl fun c _ => hc c]
      simp [Finset.sum_ite_eq']
    · simp only [if_neg hab]
      have hsplit : ∀ c d : Fin N,
          (if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then ((N : ℂ) ^ 2 - 1)⁻¹ else 0)
          = (if c = a ∧ d = b then ((N : ℂ) ^ 2 - 1)⁻¹ else 0)
            + (if c = b ∧ d = a then ((N : ℂ) ^ 2 - 1)⁻¹ else 0) := by
        intro c d
        by_cases h1 : c = a ∧ d = b
        · simp [h1, hab]
        · by_cases h2 : c = b ∧ d = a
          · simp [h2, hab, Ne.symm hab]
          · simp [h1, h2]
      simp only [hsplit, Finset.sum_add_distrib, ite_and]
      have h₁ : ∀ c : Fin N,
          (∑ d : Fin N, if c = a then
            (if d = b then ((N : ℂ) ^ 2 - 1)⁻¹ else 0) else 0)
          = if c = a then ((N : ℂ) ^ 2 - 1)⁻¹ else 0 := by
        intro c
        by_cases hc' : c = a
        · simp [hc', Finset.sum_ite_eq']
        · simp [hc']
      have h₂ : ∀ c : Fin N,
          (∑ d : Fin N, if c = b then
            (if d = a then ((N : ℂ) ^ 2 - 1)⁻¹ else 0) else 0)
          = if c = b then ((N : ℂ) ^ 2 - 1)⁻¹ else 0 := by
        intro c
        by_cases hc' : c = b
        · simp [hc', Finset.sum_ite_eq']
        · simp [hc']
      rw [Finset.sum_congr rfl fun c _ => h₁ c,
        Finset.sum_congr rfl fun c _ => h₂ c]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hinner a b]
  -- (5) the outer count: `N` diagonal terms and `N(N−1)` off-diagonal ones
  have houter : ∀ a : Fin N,
      (∑ b : Fin N, if a = b then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹
        else 2 * ((N : ℂ) ^ 2 - 1)⁻¹)
      = 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹
        + ((N : ℂ) - 1) * (2 * ((N : ℂ) ^ 2 - 1)⁻¹) := by
    intro a
    have hpt : ∀ b : Fin N,
        (if a = b then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹
          else 2 * ((N : ℂ) ^ 2 - 1)⁻¹)
        = 2 * ((N : ℂ) ^ 2 - 1)⁻¹
          + (if b = a then 2 * ((N : ℂ) * ((N : ℂ) + 1))⁻¹
              - 2 * ((N : ℂ) ^ 2 - 1)⁻¹ else 0) := by
      intro b
      by_cases h : a = b
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl fun b _ => hpt b, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [Finset.sum_congr rfl fun a _ => houter a, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  -- (6) the final arithmetic: `N·A + N(N−1)·C·2 = 2`
  field_simp
  ring

end HaarExpectation

end Weingarten.Haar
