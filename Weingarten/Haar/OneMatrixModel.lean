/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.EntryIntegralsTwo

/-!
# One-matrix-model strong-coupling coefficients

The β-expansion of the one-matrix-model trace observable
`⟨Tr U⟩_β = E[T e^{βR}]/E[e^{βR}]` (Chatterjee's β convention, `T = Tr U`,
`R = Re Tr U`) is governed by finitely many **trace-word moments**
`E (T^a · conj(T)^b)`, all proved here through total degree 5 in one unified
statement (`integral_trace_pow_mul_star_pow`):

* unbalanced words (`a ≠ b`) vanish — the charge argument, executed with the
  primitive eighth root `ζ = (1+i)/√2` (the naive `z = i` kill fails at charge 4
  since `i⁴ = 1`, and charge-4 words genuinely occur, e.g. `E T⁴`);
* balanced words take the complex-Gaussian values `E|T|⁰ = 1`, `E|T|² = 1`,
  `E|T|⁴ = 2` (`N ≥ 2`).

The headline (`one_matrix_model_coeffs`): through order `β⁴`,
`⟨Tr U⟩_β = β/2` on the nose — `w₁ = 1/2`, `w₂ = w₃ = w₄ = 0` for `N ≥ 2`.

## Provenance (PDF-verified, archived)

The balanced values are the exact finite-`N` Gaussian moment match of
**Diaconis–Evans**, Trans. AMS 353 (2001), Thm 2.1(a) (condition
`n ≥ max(Σ j·a_j, Σ j·b_j)`; the Diaconis–Shahshahani 1994 condition is labelled
*incorrect* there). The conceptual frame is **mock-Gaussianity**: by Soshnikov
(Ann. Probab. 28 (2000) 1353–1370, Lemma 1/eq. (2.9)), as sharpened by
Hughes–Rudnick (J. Phys. A 36 (2003) 2919, arXiv:math/0206289, Thm 7 and Remark),
the cumulants of order `3..2N` of any mode-`±1` linear statistic of Haar-`U(N)`
vanish **exactly at finite `N`** — the strong-coupling coefficient vanishing proved
below is precisely this phenomenon. The exact value of every balanced moment at
every `N` is Rains (Electron. J. Combin. 5 (1998) #R12, Thm 1.1):
`E|Tr U|^{2n} = #{σ ∈ Sₙ : LIS(σ) ≤ N}`.
-/

namespace Weingarten.Haar

open Matrix

variable {N : ℕ}

/-! ### The primitive eighth root of unity

`ζ = (1+i)/√2`, built from `invSqrtTwo` — no transcendental functions. Its powers
`ζ, i, iζ, −1, −ζ, −i` are all `≠ 1` (imaginary part nonzero, except `ζ⁴ = −1` which
needs the real part), so translation by the scalar unitary `ζ·1` kills every
unbalanced trace word of charge `1..6`. -/

/-- The primitive eighth root of unity `ζ = (1+i)/√2`. -/
noncomputable def zeta : ℂ := invSqrtTwo * (1 + Complex.I)

private theorem invSqrtTwo_im : invSqrtTwo.im = 0 := by
  rw [invSqrtTwo, ← Complex.ofReal_inv]
  exact Complex.ofReal_im _

private theorem invSqrtTwo_re : invSqrtTwo.re = (Real.sqrt 2)⁻¹ := by
  rw [invSqrtTwo, ← Complex.ofReal_inv]
  exact Complex.ofReal_re _

private theorem sqrtTwo_inv_ne : (Real.sqrt 2)⁻¹ ≠ 0 :=
  inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- `ζ` lies on the unit circle. -/
theorem zeta_mul_star_zeta : zeta * star zeta = 1 := by
  have h2 := invSqrtTwo_mul_self
  have hI := Complex.I_mul_I
  simp only [zeta, star_mul', Complex.star_def, map_add, map_one, Complex.conj_I,
    invSqrtTwo_star]
  linear_combination (2 : ℂ) * h2 - invSqrtTwo * invSqrtTwo * hI

/-- `ζ² = i`. -/
theorem zeta_sq : zeta ^ 2 = Complex.I := by
  have h2 := invSqrtTwo_mul_self
  have hI := Complex.I_mul_I
  simp only [zeta]
  linear_combination (2 * Complex.I : ℂ) * h2 + invSqrtTwo * invSqrtTwo * hI

/-- The imaginary part of `ζ`. -/
private theorem zeta_im : zeta.im = (Real.sqrt 2)⁻¹ := by
  rw [zeta, Complex.mul_im, invSqrtTwo_im, invSqrtTwo_re]
  simp

private theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [zeta_im, Complex.one_im] at this
  exact sqrtTwo_inv_ne this

private theorem zeta_pow_two_ne_one : zeta ^ 2 ≠ 1 := by
  rw [zeta_sq]
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem zeta_re : zeta.re = (Real.sqrt 2)⁻¹ := by
  rw [zeta, Complex.mul_re, invSqrtTwo_im, invSqrtTwo_re]
  simp

private theorem zeta_pow_three_ne_one : zeta ^ 3 ≠ 1 := by
  have h3 : zeta ^ 3 = Complex.I * zeta := by
    calc zeta ^ 3 = zeta ^ 2 * zeta := by ring
      _ = Complex.I * zeta := by rw [zeta_sq]
  rw [h3]
  intro h
  have him := congrArg Complex.im h
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_im, zero_mul, one_mul,
    zero_add, zeta_re] at him
  exact sqrtTwo_inv_ne him

private theorem zeta_pow_four_ne_one : zeta ^ 4 ≠ 1 := by
  have h4 : zeta ^ 4 = -1 := by
    calc zeta ^ 4 = (zeta ^ 2) ^ 2 := by ring
      _ = Complex.I ^ 2 := by rw [zeta_sq]
      _ = -1 := Complex.I_sq
  rw [h4]
  norm_num

private theorem zeta_pow_five_ne_one : zeta ^ 5 ≠ 1 := by
  have h5 : zeta ^ 5 = -zeta := by
    calc zeta ^ 5 = (zeta ^ 2) ^ 2 * zeta := by ring
      _ = Complex.I ^ 2 * zeta := by rw [zeta_sq]
      _ = -zeta := by rw [Complex.I_sq]; ring
  rw [h5]
  intro h
  have := congrArg Complex.im h
  rw [Complex.neg_im, zeta_im, Complex.one_im, neg_eq_zero] at this
  exact sqrtTwo_inv_ne this

private theorem zeta_pow_six_ne_one : zeta ^ 6 ≠ 1 := by
  have h6 : zeta ^ 6 = -Complex.I := by
    calc zeta ^ 6 = (zeta ^ 2) ^ 3 := by ring
      _ = Complex.I ^ 3 := by rw [zeta_sq]
      _ = -Complex.I := by
          calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
            _ = -Complex.I := by rw [Complex.I_sq]; ring
  rw [h6]
  intro h
  have := congrArg Complex.im h
  simp at this

/-- `ζ^m ≠ 1` for `1 ≤ m ≤ 6` — the charge weights this phase consumes. -/
private theorem zeta_pow_ne_one {m : ℕ} (h1 : 1 ≤ m) (h6 : m ≤ 6) :
    zeta ^ m ≠ 1 := by
  interval_cases m
  · simpa using zeta_ne_one
  · exact zeta_pow_two_ne_one
  · exact zeta_pow_three_ne_one
  · exact zeta_pow_four_ne_one
  · exact zeta_pow_five_ne_one
  · exact zeta_pow_six_ne_one

/-- The ζ-weight of an unbalanced word is never `1` (total degree ≤ 6): the weight
collapses to `ζ^{a−b}` (or its star), a nontrivial power of a primitive eighth root. -/
private theorem zeta_weight_ne_one {a b : ℕ} (hab : a ≠ b) (hle : a + b ≤ 6) :
    zeta ^ a * (star zeta) ^ b ≠ 1 := by
  rcases Nat.lt_or_ge a b with h | h
  · have hred : zeta ^ a * (star zeta) ^ b = star (zeta ^ (b - a)) := by
      calc zeta ^ a * (star zeta) ^ b
          = zeta ^ a * ((star zeta) ^ a * (star zeta) ^ (b - a)) := by
            rw [← pow_add, Nat.add_sub_cancel' h.le]
        _ = (zeta * star zeta) ^ a * (star zeta) ^ (b - a) := by
            rw [mul_pow]; ring
        _ = star (zeta ^ (b - a)) := by
            rw [zeta_mul_star_zeta, one_pow, one_mul, star_pow]
    rw [hred]
    intro hcon
    have hpow : zeta ^ (b - a) = 1 := by
      have := congrArg star hcon
      simpa using this
    exact zeta_pow_ne_one (by omega) (by omega) hpow
  · have hlt : b < a := lt_of_le_of_ne h (Ne.symm hab)
    have hred : zeta ^ a * (star zeta) ^ b = zeta ^ (a - b) := by
      calc zeta ^ a * (star zeta) ^ b
          = zeta ^ (a - b) * (zeta ^ b * (star zeta) ^ b) := by
            rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le]
        _ = zeta ^ (a - b) := by
            rw [← mul_pow, zeta_mul_star_zeta, one_pow, mul_one]
    rw [hred]
    exact zeta_pow_ne_one (by omega) (by omega)

namespace HaarExpectation

/-- **The general trace-word charge kill**: translation by the scalar unitary `z·1`
rescales `T^a·conj(T)^b` by `z^a·(star z)^b`; whenever that weight is `≠ 1`, the
expectation vanishes (the Collins–Śniady eq. (12) phase argument, PDF-verified, in
its general word form). -/
theorem integral_trace_word_eq_zero (E : HaarExpectation N) {a b : ℕ} (z : ℂ)
    (hz : z * star z = 1) (hne : z ^ a * (star z) ^ b ≠ 1) :
    E ((traceObs N) ^ a * (star (traceObs N)) ^ b) = 0 := by
  refine E.integral_eq_zero_of_charge (g := scalarUnitary N z hz) hne ?_
  ext U
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft,
    ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.star_apply,
    ContinuousMap.smul_apply, traceObs_apply, smul_eq_mul]
  rw [scalarUnitary_mul_val, Matrix.trace_smul, smul_eq_mul, star_mul']
  rw [mul_pow, mul_pow]
  ring

/-- **The trace-word moments through total degree 5**: unbalanced words vanish
(ζ-charge kill), balanced words take the complex-Gaussian values `1, 1, 2`
(Diaconis–Evans, Trans. AMS 353 (2001), Thm 2.1(a), sharp at `N ≥ 2`; the exact
values at every `N` are Rains's LIS counts, EJC 5 (1998) #R12, Thm 1.1). This single
lemma is the complete moment input of the strong-coupling coefficient bookkeeping. -/
theorem integral_trace_pow_mul_star_pow (E : HaarExpectation N) (hN : 2 ≤ N)
    {a b : ℕ} (hle : a + b ≤ 5) :
    E ((traceObs N) ^ a * (star (traceObs N)) ^ b)
      = if a = b then (if a = 0 then 1 else if a = 1 then 1 else 2) else 0 := by
  by_cases hab : a = b
  · rw [if_pos hab]
    subst hab
    have ha2 : a ≤ 2 := by omega
    haveI : NeZero N := ⟨by omega⟩
    interval_cases a
    · rw [if_pos rfl, pow_zero, one_mul]
      exact E.map_one
    · rw [if_neg one_ne_zero, if_pos rfl, pow_one, pow_one]
      exact integral_trace_mul_star_trace E
    · rw [if_neg two_ne_zero, if_neg (by norm_num), show (traceObs N) ^ 2
        * (star (traceObs N)) ^ 2 = traceObs N * star (traceObs N)
        * (traceObs N * star (traceObs N)) from by ring]
      exact integral_absTrace_pow_four E hN
  · rw [if_neg hab]
    exact E.integral_trace_word_eq_zero zeta zeta_mul_star_zeta
      (zeta_weight_ne_one hab (by omega))

end HaarExpectation

open HaarExpectation

/-! ### The moment sequences of the one-matrix-model expansion

`⟨Tr U⟩_β = M(β)/Z(β)` with `M(β) = Σ m_k β^k/k!`, `Z(β) = Σ z_k β^k/k!` —
exponential generating functions of the moments below. Everything is finite,
algebraic, and analysis-free: the coefficients `w_k` of the formal quotient are
scalar identities in the `m`/`z` values. Conceptually `w_k = κ(T, R^{⊗k})/k!` (joint
cumulants), and the vanishing theorems below are the **exact finite-`N`
mock-Gaussianity** of `Tr U` (Soshnikov; Hughes–Rudnick) — see the module
docstring. -/

/-- The real-part-of-trace observable `R = (T + T̄)/2`. -/
noncomputable def reTraceObs (N : ℕ) : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  (2⁻¹ : ℂ) • (traceObs N + star (traceObs N))

/-- Numerator moments `m_k = E (T·R^k)`. -/
noncomputable def mMoment (E : HaarExpectation N) (k : ℕ) : ℂ :=
  E (traceObs N * (reTraceObs N) ^ k)

/-- Denominator moments `z_k = E (R^k)`. -/
noncomputable def zMoment (E : HaarExpectation N) (k : ℕ) : ℂ :=
  E ((reTraceObs N) ^ k)

variable (E : HaarExpectation N)

theorem zMoment_zero : zMoment E 0 = 1 := by
  rw [zMoment, pow_zero]; exact E.map_one

theorem mMoment_zero (hN : 2 ≤ N) : mMoment E 0 = 0 := by
  rw [mMoment, pow_zero, mul_one,
    show traceObs N = (traceObs N) ^ 1 * (star (traceObs N)) ^ 0 from by ring,
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem zMoment_one (hN : 2 ≤ N) : zMoment E 1 = 0 := by
  rw [zMoment, pow_one, reTraceObs, E.map_smul,
    show traceObs N + star (traceObs N)
      = (traceObs N) ^ 1 * (star (traceObs N)) ^ 0
        + (traceObs N) ^ 0 * (star (traceObs N)) ^ 1 from by ring,
    E.map_add, integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem mMoment_one (hN : 2 ≤ N) : mMoment E 1 = 2⁻¹ := by
  rw [mMoment, pow_one, reTraceObs, mul_smul_comm, E.map_smul,
    show traceObs N * (traceObs N + star (traceObs N))
      = (traceObs N) ^ 2 * (star (traceObs N)) ^ 0
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 1 from by ring,
    E.map_add, integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

/-- `E` against small numeral multiples — thin wrappers over the public
`HaarExpectation.map_natCast_mul` (numeral bridged by `Nat.cast_ofNat`). -/
private theorem map_two_mul (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (2 * f) = 2 * E f := by
  have h := E.map_natCast_mul 2 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_three_mul (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (3 * f) = 3 * E f := by
  have h := E.map_natCast_mul 3 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_four_mul (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (4 * f) = 4 * E f := by
  have h := E.map_natCast_mul 4 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

private theorem map_six_mul (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (6 * f) = 6 * E f := by
  have h := E.map_natCast_mul 6 f
  rwa [Nat.cast_ofNat, Nat.cast_ofNat] at h

theorem zMoment_two (hN : 2 ≤ N) : zMoment E 2 = 2⁻¹ := by
  rw [zMoment, reTraceObs, smul_pow, E.map_smul,
    show (traceObs N + star (traceObs N)) ^ 2
      = (traceObs N) ^ 2 * (star (traceObs N)) ^ 0
        + (2 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 1)
        + (traceObs N) ^ 0 * (star (traceObs N)) ^ 2 from by ring,
    E.map_add, E.map_add, map_two_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem mMoment_two (hN : 2 ≤ N) : mMoment E 2 = 0 := by
  rw [mMoment, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
    show traceObs N * (traceObs N + star (traceObs N)) ^ 2
      = (traceObs N) ^ 3 * (star (traceObs N)) ^ 0
        + (2 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 1)
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 2 from by ring,
    E.map_add, E.map_add, map_two_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem zMoment_three (hN : 2 ≤ N) : zMoment E 3 = 0 := by
  rw [zMoment, reTraceObs, smul_pow, E.map_smul,
    show (traceObs N + star (traceObs N)) ^ 3
      = (traceObs N) ^ 3 * (star (traceObs N)) ^ 0
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 1)
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 2)
        + (traceObs N) ^ 0 * (star (traceObs N)) ^ 3 from by ring,
    E.map_add, E.map_add, E.map_add, map_three_mul E, map_three_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem mMoment_three (hN : 2 ≤ N) : mMoment E 3 = 3 / 4 := by
  rw [mMoment, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
    show traceObs N * (traceObs N + star (traceObs N)) ^ 3
      = (traceObs N) ^ 4 * (star (traceObs N)) ^ 0
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 3 * (star (traceObs N)) ^ 1)
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 2)
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 3 from by ring,
    E.map_add, E.map_add, E.map_add, map_three_mul E, map_three_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem zMoment_four (hN : 2 ≤ N) : zMoment E 4 = 3 / 4 := by
  rw [zMoment, reTraceObs, smul_pow, E.map_smul,
    show (traceObs N + star (traceObs N)) ^ 4
      = (traceObs N) ^ 4 * (star (traceObs N)) ^ 0
        + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 3 * (star (traceObs N)) ^ 1)
        + (6 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 2)
        + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 1 * (star (traceObs N)) ^ 3)
        + (traceObs N) ^ 0 * (star (traceObs N)) ^ 4 from by ring,
    E.map_add, E.map_add, E.map_add, E.map_add, map_four_mul E, map_six_mul E,
    map_four_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem mMoment_four (hN : 2 ≤ N) : mMoment E 4 = 0 := by
  rw [mMoment, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
    show traceObs N * (traceObs N + star (traceObs N)) ^ 4
      = (traceObs N) ^ 5 * (star (traceObs N)) ^ 0
        + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 4 * (star (traceObs N)) ^ 1)
        + (6 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 3 * (star (traceObs N)) ^ 2)
        + (4 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 3)
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 4 from by ring,
    E.map_add, E.map_add, E.map_add, E.map_add, map_four_mul E, map_six_mul E,
    map_four_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

/-! ### The strong-coupling coefficients

`W(β) = M(β)/Z(β) = Σ w_k β^k` by truncated division of the exponential generating
functions (`z₀ = 1` makes `Z` a formal unit):
`w_k = m_k/k! − Σ_{j<k} w_j·z_{k−j}/(k−j)!`, unfolded explicitly through order 4. -/

/-- `w₀ = m₀`. -/
noncomputable def w0 : ℂ := mMoment E 0

/-- `w₁ = m₁ − w₀·z₁`. -/
noncomputable def w1 : ℂ := mMoment E 1 - w0 E * zMoment E 1

/-- `w₂ = m₂/2! − w₀·z₂/2! − w₁·z₁`. -/
noncomputable def w2 : ℂ :=
  mMoment E 2 / 2 - w0 E * zMoment E 2 / 2 - w1 E * zMoment E 1

/-- `w₃ = m₃/3! − w₀·z₃/3! − w₁·z₂/2! − w₂·z₁`. -/
noncomputable def w3 : ℂ :=
  mMoment E 3 / 6 - w0 E * zMoment E 3 / 6 - w1 E * zMoment E 2 / 2
    - w2 E * zMoment E 1

/-- `w₄ = m₄/4! − w₀·z₄/4! − w₁·z₃/3! − w₂·z₂/2! − w₃·z₁`. -/
noncomputable def w4 : ℂ :=
  mMoment E 4 / 24 - w0 E * zMoment E 4 / 24 - w1 E * zMoment E 3 / 6
    - w2 E * zMoment E 2 / 2 - w3 E * zMoment E 1

/-- **The leading strong-coupling coefficient: `w₁ = 1/2`** — in Chatterjee units,
`⟨Tr U⟩_β = β/2 + O(β⁵)`. Cross-checked at source against the Gross–Witten
strong-coupling solution (primary sources: D. J. Gross, E. Witten, Phys. Rev. D 21
(1980) 446; S. R. Wadia, Phys. Lett. B 93 (1980) 403) as displayed in Drouffe–Zuber,
Phys. Rep. 102 (1983),
(A.33)–(A.34) (`⟨Re Tr U_p⟩ = β/2` exactly at `N = ∞`), and at `N = 2` against the
Bessel–Toeplitz determinant `Z₂ = I₀² − I₁²` (Wadia, arXiv:1212.2906, eqs. (46)/(48);
the printed machine expansion in his eq. (49) matches through `β⁸`). -/
theorem w1_eq (hN : 2 ≤ N) : w1 E = 2⁻¹ := by
  rw [w1, w0, mMoment_one E hN, mMoment_zero E hN, zMoment_one E hN]
  ring

/-- **Vanishing at order 2**: `w₂ = 0`. -/
theorem w2_eq (hN : 2 ≤ N) : w2 E = 0 := by
  rw [w2, w1, w0, mMoment_two E hN, mMoment_one E hN, mMoment_zero E hN,
    zMoment_two E hN, zMoment_one E hN]
  ring

/-- **Vanishing at order 3**: `w₃ = 0` for `N ≥ 2` — the first genuinely
Weingarten-flavoured cancellation: `m₃/3! = (3/4)/6 = 1/8` against
`w₁·z₂/2! = (1/2)·(1/2)/2 = 1/8`. At `N = 1` this coefficient is `−1/16`
(`I₁/I₀ = β/2 − β³/16 + …`), which is why `2 ≤ N` is essential. This vanishing is the
order-4 exact mock-Gaussian cumulant vanishing of Soshnikov/Hughes–Rudnick. -/
theorem w3_eq (hN : 2 ≤ N) : w3 E = 0 := by
  rw [w3, w2, w1, w0, mMoment_three E hN, mMoment_two E hN, mMoment_one E hN,
    mMoment_zero E hN, zMoment_three E hN, zMoment_two E hN, zMoment_one E hN]
  ring

/-- **Vanishing at order 4**: `w₄ = 0` (charge parity: every order-5 trace word is
unbalanced). -/
theorem w4_eq (hN : 2 ≤ N) : w4 E = 0 := by
  rw [w4, w3, w2, w1, w0, mMoment_four E hN, mMoment_three E hN, mMoment_two E hN,
    mMoment_one E hN, mMoment_zero E hN, zMoment_four E hN, zMoment_three E hN,
    zMoment_two E hN, zMoment_one E hN]
  ring

/-- **The headline**: through order `β⁴`, the one-matrix-model trace observable
is `⟨Tr U⟩_β = β/2` on the nose — `w₁ = 1/2` and `w₂ = w₃ = w₄ = 0` for `N ≥ 2`.

*The vanishing is the theorem*: the trace of a Haar unitary is **mock-Gaussian**
(Hughes–Rudnick, arXiv:math/0206289, Thm 7, after Soshnikov, Ann. Probab. 28 (2000),
Lemma 1) — its cumulants of order `3..2N` vanish exactly at finite `N`, and the
Gaussian model gives `E[Z e^{βRe Z}]/E[e^{βRe Z}] = β/2` exactly. Deviations start at
`β^{2N+1}`: the next coefficient is `w₅ = (E|Tr U|⁶ − 6)/384`, which is `−1/384` at
`N = 2` (Rains: `E|Tr U|⁶ = #{σ ∈ S₃ : LIS ≤ 2} = 5`) and `0` for `N ≥ 3` — verified
against the `U(2)` Bessel determinant `Z₂ = I₀² − I₁²` and Wadia's printed expansion
(arXiv:1212.2906, eq. (49)). -/
theorem one_matrix_model_coeffs (hN : 2 ≤ N) :
    w1 E = 2⁻¹ ∧ w2 E = 0 ∧ w3 E = 0 ∧ w4 E = 0 :=
  ⟨w1_eq E hN, w2_eq E hN, w3_eq E hN, w4_eq E hN⟩

/-! ### The companion observable `⟨|Tr U|²⟩_β`

The companion trace observable with a **nonvanishing** low-order coefficient: with numerator
moments `n_k = E (|T|²·R^k)`, the truncated division gives
`⟨|Tr U|²⟩_β = 1 + β²/4 + O(β⁴)` for `N ≥ 2`. Representation-theoretically
`|Tr U|² = 1 + χ_adj(U)` (fund ⊗ fund* = 1 ⊕ adjoint), and the `β²/4` agrees at
leading order with the adjoint-character coefficient display of Drouffe–Zuber,
Phys. Rep. 102 (1983), (A.35); the β-series itself is not displayed in the verified
sources — it is derived here. Consistency: at `N = 1` the coefficient is `0`
(`|Tr U|² ≡ 1` on `U(1)`), so `2 ≤ N` is again essential. -/

/-- Companion numerator moments `n_k = E (|T|²·R^k)`. -/
noncomputable def nMoment (E : HaarExpectation N) (k : ℕ) : ℂ :=
  E (traceObs N * star (traceObs N) * (reTraceObs N) ^ k)

theorem nMoment_zero (hN : 2 ≤ N) : nMoment E 0 = 1 := by
  rw [nMoment, pow_zero, mul_one,
    show traceObs N * star (traceObs N)
      = (traceObs N) ^ 1 * (star (traceObs N)) ^ 1 from by ring,
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem nMoment_one (hN : 2 ≤ N) : nMoment E 1 = 0 := by
  rw [nMoment, pow_one, reTraceObs, mul_smul_comm, E.map_smul,
    show traceObs N * star (traceObs N) * (traceObs N + star (traceObs N))
      = (traceObs N) ^ 2 * (star (traceObs N)) ^ 1
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 2 from by ring,
    E.map_add, integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem nMoment_two (hN : 2 ≤ N) : nMoment E 2 = 1 := by
  rw [nMoment, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
    show traceObs N * star (traceObs N) * (traceObs N + star (traceObs N)) ^ 2
      = (traceObs N) ^ 3 * (star (traceObs N)) ^ 1
        + (2 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 2)
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 3 from by ring,
    E.map_add, E.map_add, map_two_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

theorem nMoment_three (hN : 2 ≤ N) : nMoment E 3 = 0 := by
  rw [nMoment, reTraceObs, smul_pow, mul_smul_comm, E.map_smul,
    show traceObs N * star (traceObs N) * (traceObs N + star (traceObs N)) ^ 3
      = (traceObs N) ^ 4 * (star (traceObs N)) ^ 1
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 3 * (star (traceObs N)) ^ 2)
        + (3 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ))
          * ((traceObs N) ^ 2 * (star (traceObs N)) ^ 3)
        + (traceObs N) ^ 1 * (star (traceObs N)) ^ 4 from by ring,
    E.map_add, E.map_add, E.map_add, map_three_mul E, map_three_mul E,
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega),
    integral_trace_pow_mul_star_pow E hN (by omega)]
  norm_num

/-- `c₀ = n₀`. -/
noncomputable def c0 : ℂ := nMoment E 0

/-- `c₁ = n₁ − c₀·z₁`. -/
noncomputable def c1 : ℂ := nMoment E 1 - c0 E * zMoment E 1

/-- `c₂ = n₂/2! − c₀·z₂/2! − c₁·z₁`. -/
noncomputable def c2 : ℂ :=
  nMoment E 2 / 2 - c0 E * zMoment E 2 / 2 - c1 E * zMoment E 1

/-- `c₃ = n₃/3! − c₀·z₃/3! − c₁·z₂/2! − c₂·z₁`. -/
noncomputable def c3 : ℂ :=
  nMoment E 3 / 6 - c0 E * zMoment E 3 / 6 - c1 E * zMoment E 2 / 2
    - c2 E * zMoment E 1

theorem c0_eq (hN : 2 ≤ N) : c0 E = 1 := by
  rw [c0, nMoment_zero E hN]

theorem c1_eq (hN : 2 ≤ N) : c1 E = 0 := by
  rw [c1, c0, nMoment_one E hN, nMoment_zero E hN, zMoment_one E hN]
  ring

/-- **The nonvanishing companion coefficient: `c₂ = 1/4`** —
`⟨|Tr U|²⟩_β = 1 + β²/4 + O(β⁴)` for `N ≥ 2`
(`n₂/2! − c₀·z₂/2! = 1/2 − 1/4`). At `N = 1` this coefficient is `0`
(`|Tr U|² ≡ 1` on `U(1)`). -/
theorem c2_eq (hN : 2 ≤ N) : c2 E = 4⁻¹ := by
  rw [c2, c1, c0, nMoment_two E hN, nMoment_one E hN, nMoment_zero E hN,
    zMoment_two E hN, zMoment_one E hN]
  ring

theorem c3_eq (hN : 2 ≤ N) : c3 E = 0 := by
  rw [c3, c2, c1, c0, nMoment_three E hN, nMoment_two E hN, nMoment_one E hN,
    nMoment_zero E hN, zMoment_three E hN, zMoment_two E hN, zMoment_one E hN]
  ring

/-- **The companion headline**: `⟨|Tr U|²⟩_β = 1 + β²/4 + O(β⁴)` for `N ≥ 2` —
the strong-coupling coefficients of the squared trace observable
(`c₀ = 1, c₁ = 0, c₂ = 1/4, c₃ = 0`), the first nonvanishing correction of the
phase. -/
theorem one_matrix_model_sq_coeffs (hN : 2 ≤ N) :
    c0 E = 1 ∧ c1 E = 0 ∧ c2 E = 4⁻¹ ∧ c3 E = 0 :=
  ⟨c0_eq E hN, c1_eq E hN, c2_eq E hN, c3_eq E hN⟩

end Weingarten.Haar
