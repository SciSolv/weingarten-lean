/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.StarReal
import Weingarten.Haar.TraceEntryMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The honest one-matrix kernel weight: real scalars and their positivity

The scalar layer of the **untruncated** single-matrix Boltzmann weight
`e^{β Re Tr U}`. This module lives here as the kernel-weight layer consumed by the
tilted-measure file (`ProductHaar`: `gibbsPair`/`chainGibbs`); it supplies `reTrace`,
the weight `expObs`, and the two transfer scalars below. In the lattice development
in which this layer originated, this was the one-link factor of the transfer kernel
`K(U,V) = e^{β Re Tr(U⁻¹V)}` (Lüscher, Comm. Math. Phys. 54 (1977) 283, Eq. (21);
Creutz, Phys. Rev. D 15 (1977) 1128, p. 1131). Its diagonalization on characters is Drouffe–Zuber, Phys. Rep. 102 (1983),
Eqs. (3.17)/(3.28); at `N = 2` the scalars below are built from the Bessel entries
of the Wadia determinant (arXiv:1212.2906; eqs. (46)/(48) anchor the `honestZ`
side). β is in Chatterjee units
(arXiv:1803.01950, eq. (3.2)).

**Real-first design (recorded design decision).** The two transfer scalars are defined as
*real* Bochner integrals against the genuine Haar probability measure `haarUnitary N`:

* `honestZ N β = ∫ exp (β · Re Tr U) dU` — the vacuum eigenvalue `λ₀(β)`, untruncated;
* `honestLamF N β = N⁻¹ ∫ (Re Tr U) · exp (β · Re Tr U) dU` — the fundamental
  eigenvalue `λ_F(β)`.

All positivity statements are therefore independent of any complex-reality bridge.

**The elementary positivity suite (design ruling: sinh symmetrization).**
Left translation by the *central* unitary `−1 ∈ U(N)` flips `Re Tr U ↦ −Re Tr U`
while preserving Haar, so `honestZ` is a `cosh`-integral and `honestLamF` is a
`sinh`-integral (`honestZ_eq_cosh`, `honestLamF_eq_sinh`). Consequences, with **no
series expansion, no differentiation under the integral, and no character-positivity
theory**: `honestZ_pos`, `honestZ_ge_one`, `honestLamF_nonneg` (β ≥ 0),
`honestLamF_pos` (1 ≤ N, β > 0), and the strict gap inequality
`honestLamF_lt_honestZ` (1 ≤ N, **all** β) from the pointwise bound
`cosh x − t·sinh x ≥ e^{−|x|}` for `|t| ≤ 1`.

**PB-1: the conjugation pushforward.** `conjEquiv N` is entrywise complex
conjugation `U ↦ conj U` as a `ContinuousMulEquiv` of `U(N)` (conjugation is a ring
homomorphism of ℂ, so it is multiplicative entrywise); `haarUnitary_map_conjEquiv`
identifies the pushforward of Haar with Haar by the uniqueness of Haar probability
measures. The reality bridge `traceExp_isReal` (the ℂ-valued Haar integral of
`Tr U · e^{β Re Tr U}` is star-fixed) combines this with the star-reality of the
honest expectation (`haarExpectation_isStarReal`); the cast identities
`haarExpectation_expObs` / `haarExpectation_traceObs_mul_expObs` hand the ℂ-valued
data directly to the real scalars (in the development in which this layer originated
these fed an eigen-equation module, which is not ported here).

**Scope honesty.** Everything here is about the *scalars* of the kernel weight; the
eigen-equation and gap layers of the development in which this layer originated are
NOT ported. No completeness of characters is claimed.
-/

namespace Weingarten.Haar

open MeasureTheory MeasureTheory.Measure Matrix

variable {N : ℕ}

/-! ### The real trace observable `Re Tr U` -/

/-- The real part of the trace, `reTrace U = Re Tr U`, as a real-valued function on
`U(N)` — the real-first counterpart of the ℂ-valued observable `reTraceObs N`. -/
def reTrace (U : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  ((U : Matrix (Fin N) (Fin N) ℂ)).trace.re

/-- `reTrace` is continuous. -/
theorem continuous_reTrace : Continuous (reTrace (N := N)) :=
  Complex.continuous_re.comp (continuous_subtype_val.matrix_trace)

/-- The coercion bridge to the frozen ℂ-valued observable:
`(reTrace U : ℂ) = reTraceObs N U`. -/
theorem ofReal_reTrace (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ((reTrace U : ℝ) : ℂ) = reTraceObs N U := by
  show ((((U : Matrix (Fin N) (Fin N) ℂ)).trace.re : ℝ) : ℂ) = _
  simp only [reTraceObs, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.star_apply, traceObs_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring

/-- `reTrace` is a class function: conjugation `U ↦ g·U·g⁻¹` fixes it. Reuses the
frozen `reTraceObs_comp_conj` through the coercion bridge. -/
theorem reTrace_conjMap (g U : Matrix.unitaryGroup (Fin N) ℂ) :
    reTrace (conjMap N g U) = reTrace U := by
  have h := congrArg (fun F : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) => F U)
    (reTraceObs_comp_conj (N := N) g)
  simp only [ContinuousMap.comp_apply] at h
  have h2 : ((reTrace (conjMap N g U) : ℝ) : ℂ) = ((reTrace U : ℝ) : ℂ) := by
    rw [ofReal_reTrace, ofReal_reTrace, h]
  exact_mod_cast h2

/-- `reTrace 1 = N`. -/
theorem reTrace_one (N : ℕ) : reTrace (1 : Matrix.unitaryGroup (Fin N) ℂ) = N := by
  show (((1 : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).trace.re = N
  rw [Matrix.UnitaryGroup.one_val, Matrix.trace_one]
  simp

/-- **The uniform trace bound** `|Re Tr U| ≤ N`: every entry of a unitary matrix has
norm at most `1` (`entry_norm_bound_of_unitary`), so the trace has norm at most `N`. -/
theorem abs_reTrace_le (U : Matrix.unitaryGroup (Fin N) ℂ) : |reTrace U| ≤ (N : ℝ) := by
  have htr : ((U : Matrix (Fin N) (Fin N) ℂ)).trace
      = ∑ i, (U : Matrix (Fin N) (Fin N) ℂ) i i := rfl
  calc |reTrace U| ≤ ‖((U : Matrix (Fin N) (Fin N) ℂ)).trace‖ :=
        Complex.abs_re_le_norm _
    _ = ‖∑ i, (U : Matrix (Fin N) (Fin N) ℂ) i i‖ := by rw [htr]
    _ ≤ ∑ i, ‖(U : Matrix (Fin N) (Fin N) ℂ) i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary U.2 i i
    _ = N := by simp

/-! ### The central `−1` and the sign flip -/

/-- The central unitary `−1 ∈ U(N)` — the scalar unitary at `z = −1`. Left
translation by it implements `U ↦ −U`, the symmetrization move of the positivity
suite. -/
noncomputable def negOne (N : ℕ) : Matrix.unitaryGroup (Fin N) ℂ :=
  scalarUnitary N (-1) (by rw [star_neg, star_one]; ring)

/-- Multiplication by `negOne N` rescales the matrix by `−1`. -/
theorem negOne_mul_val (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ((negOne N * U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = (-1 : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ) :=
  scalarUnitary_mul_val (-1) _ U

/-- **The sign flip**: `reTrace (−U) = −reTrace U`. -/
theorem reTrace_negOne_mul (U : Matrix.unitaryGroup (Fin N) ℂ) :
    reTrace (negOne N * U) = -reTrace U := by
  show (((negOne N * U : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)).trace.re = _
  rw [negOne_mul_val, Matrix.trace_smul]
  simp [reTrace]

/-! ### Integrability of the continuous real integrands -/

/-- Every continuous real function on the compact group `U(N)` is integrable for the
Haar probability measure — the real-valued sibling of `integrable_continuousMap`. -/
theorem integrable_continuous_real {f : Matrix.unitaryGroup (Fin N) ℂ → ℝ}
    (hf : Continuous f) : Integrable f (haarUnitary N) :=
  hf.integrable_of_hasCompactSupport ((isClosed_tsupport _).isCompact)

private theorem integrable_exp_reTrace (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      Real.exp (β * reTrace U)) (haarUnitary N) :=
  integrable_continuous_real
    (Real.continuous_exp.comp (continuous_const.mul continuous_reTrace))

private theorem integrable_exp_neg_reTrace (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      Real.exp (-(β * reTrace U))) (haarUnitary N) :=
  integrable_continuous_real
    (Real.continuous_exp.comp (continuous_const.mul continuous_reTrace).neg)

private theorem integrable_reTrace_mul_exp (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      reTrace U * Real.exp (β * reTrace U)) (haarUnitary N) :=
  integrable_continuous_real (continuous_reTrace.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_reTrace)))

private theorem integrable_reTrace_mul_exp_neg (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      reTrace U * Real.exp (-(β * reTrace U))) (haarUnitary N) :=
  integrable_continuous_real (continuous_reTrace.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_reTrace).neg))

private theorem integrable_reTrace_mul_sinh (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      reTrace U * Real.sinh (β * reTrace U)) (haarUnitary N) :=
  integrable_continuous_real (continuous_reTrace.mul
    (Real.continuous_sinh.comp (continuous_const.mul continuous_reTrace)))

private theorem integrable_cosh_reTrace (N : ℕ) (β : ℝ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      Real.cosh (β * reTrace U)) (haarUnitary N) :=
  integrable_continuous_real
    (Real.continuous_cosh.comp (continuous_const.mul continuous_reTrace))

/-! ### The exponential observable -/

/-- The **untruncated one-link Boltzmann weight** `expObs N β : U ↦ e^{β Re Tr U}` as
a ℂ-valued continuous observable — the conjugation-invariant weight fed to the hypothesis-parametric key lemma
`integral_entry_mul_conjInv`. Pointwise it is the coercion of a positive real. -/
noncomputable def expObs (N : ℕ) (β : ℝ) : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ⟨fun U => ((Real.exp (β * reTrace U) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_reTrace))⟩

@[simp] theorem expObs_apply (β : ℝ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    expObs N β U = ((Real.exp (β * reTrace U) : ℝ) : ℂ) := rfl

/-- `expObs` in complex-exponential form: `expObs N β U = exp (β · reTraceObs N U)`. -/
theorem expObs_eq_cexp (β : ℝ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    expObs N β U = Complex.exp ((β : ℂ) * reTraceObs N U) := by
  rw [expObs_apply, ← ofReal_reTrace, ← Complex.ofReal_mul, Complex.ofReal_exp]

/-- `expObs` is star-fixed: it is pointwise (positive) real. -/
theorem expObs_star_eq (N : ℕ) (β : ℝ) : star (expObs N β) = expObs N β := by
  ext U
  simp only [ContinuousMap.star_apply, expObs_apply, Complex.star_def,
    Complex.conj_ofReal]

/-- **Conjugation invariance of the weight**: `expObs ∘ conj_g = expObs` for every
unitary `g` — exactly the hypothesis shape consumed by
`integral_entry_mul_conjInv`. -/
theorem expObs_conjInvariant (N : ℕ) (β : ℝ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (expObs N β).comp (conjMap N g) = expObs N β := by
  ext U
  simp only [ContinuousMap.comp_apply, expObs_apply, reTrace_conjMap]

/-! ### The vacuum scalar `honestZ` -/

/-- **The honest vacuum eigenvalue** `Z(β) = ∫ e^{β Re Tr U} dU` — the untruncated
partition function of the single link (DZ (3.17) at the trivial character), as a real
Bochner integral against the genuine Haar probability measure. -/
noncomputable def honestZ (N : ℕ) (β : ℝ) : ℝ :=
  ∫ U, Real.exp (β * reTrace U) ∂haarUnitary N

/-- **Strict positivity of the vacuum scalar**, for every `N` and every `β`:
the integrand is a positive exponential and Haar is a (nonzero) probability
measure (`integral_exp_pos`). -/
theorem honestZ_pos (N : ℕ) (β : ℝ) : 0 < honestZ N β := by
  unfold honestZ
  exact integral_exp_pos (integrable_exp_reTrace N β)

/-- The Haar integral of `reTrace` vanishes — the real face of the fact
`E (Tr U) = 0` (`integral_trace`), transported through `integral_ofReal` and the
star-reality of the honest expectation. -/
theorem integral_reTrace_eq_zero (N : ℕ) :
    (∫ U, reTrace U ∂haarUnitary N) = 0 := by
  have hobs : (∫ U, ((reTrace U : ℝ) : ℂ) ∂haarUnitary N)
      = haarExpectation N (reTraceObs N) := by
    show _ = ∫ U, reTraceObs N U ∂haarUnitary N
    have h : (fun U : Matrix.unitaryGroup (Fin N) ℂ => ((reTrace U : ℝ) : ℂ))
        = fun U => reTraceObs N U := funext fun U => ofReal_reTrace U
    rw [h]
  have hzero : haarExpectation N (reTraceObs N) = 0 := by
    have h1 : haarExpectation N (star (traceObs N)) = 0 := by
      rw [haarExpectation_isStarReal N (traceObs N),
        (haarExpectation N).integral_trace, star_zero]
    rw [reTraceObs, HaarExpectation.map_smul, HaarExpectation.map_add, h1,
      (haarExpectation N).integral_trace]
    simp
  have hcast : ((∫ U, reTrace U ∂haarUnitary N : ℝ) : ℂ) = 0 := by
    have h3 : ((∫ U, reTrace U ∂haarUnitary N : ℝ) : ℂ)
        = ∫ U, ((reTrace U : ℝ) : ℂ) ∂haarUnitary N := integral_ofReal.symm
    rw [h3, hobs, hzero]
  exact_mod_cast hcast

/-- **`Z(β) ≥ 1` for all β**: integrate the elementary bound `x + 1 ≤ eˣ`
(`Real.add_one_le_exp`) and kill the linear term with `∫ reTrace = 0`. -/
theorem honestZ_ge_one (N : ℕ) (β : ℝ) : 1 ≤ honestZ N β := by
  have hf1 : Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ => β * reTrace U)
      (haarUnitary N) :=
    integrable_continuous_real (continuous_const.mul continuous_reTrace)
  have hcalc : (∫ U, (β * reTrace U + 1) ∂haarUnitary N) = 1 := by
    rw [integral_add hf1 (integrable_const 1),
      integral_const_mul, integral_reTrace_eq_zero, integral_const, probReal_univ]
    simp
  calc (1 : ℝ) = ∫ U, (β * reTrace U + 1) ∂haarUnitary N := hcalc.symm
    _ ≤ honestZ N β :=
        integral_mono
          (integrable_continuous_real
            ((continuous_const.mul continuous_reTrace).add continuous_const))
          (integrable_exp_reTrace N β)
          fun U => Real.add_one_le_exp (β * reTrace U)

/-- **The cosh form of the vacuum scalar**: translating by the central `−1` flips the
sign of `reTrace` while preserving Haar, so `Z(β) = ∫ cosh (β Re Tr U) dU`. -/
theorem honestZ_eq_cosh (N : ℕ) (β : ℝ) :
    honestZ N β = ∫ U, Real.cosh (β * reTrace U) ∂haarUnitary N := by
  have h0 : (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      Real.exp (β * reTrace (negOne N * U)))
      = fun U => Real.exp (-(β * reTrace U)) :=
    funext fun U => by rw [reTrace_negOne_mul, mul_neg]
  have hflip : (∫ U, Real.exp (-(β * reTrace U)) ∂haarUnitary N) = honestZ N β := by
    calc (∫ U, Real.exp (-(β * reTrace U)) ∂haarUnitary N)
        = ∫ U, Real.exp (β * reTrace (negOne N * U)) ∂haarUnitary N := by rw [h0]
      _ = honestZ N β :=
          integral_mul_left_eq_self (μ := haarUnitary N)
            (fun U => Real.exp (β * reTrace U)) (negOne N)
  calc honestZ N β = (honestZ N β + honestZ N β) / 2 := by ring
    _ = (honestZ N β + ∫ U, Real.exp (-(β * reTrace U)) ∂haarUnitary N) / 2 := by
        rw [hflip]
    _ = (∫ U, (Real.exp (β * reTrace U) + Real.exp (-(β * reTrace U)))
          ∂haarUnitary N) / 2 := by
        rw [integral_add (integrable_exp_reTrace N β) (integrable_exp_neg_reTrace N β)]
        rfl
    _ = ∫ U, Real.cosh (β * reTrace U) ∂haarUnitary N := by
        rw [div_eq_inv_mul, ← integral_const_mul]
        have h : (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
            (2 : ℝ)⁻¹ * (Real.exp (β * reTrace U) + Real.exp (-(β * reTrace U))))
            = fun U => Real.cosh (β * reTrace U) :=
          funext fun U => by rw [Real.cosh_eq]; ring
        rw [h]

/-! ### The fundamental scalar `honestLamF` and the sinh positivity suite -/

/-- **The honest fundamental eigenvalue**
`λ_F(β) = N⁻¹ ∫ (Re Tr U) e^{β Re Tr U} dU` — the untruncated fundamental-character
coefficient of the one-link kernel (DZ (3.17)/(3.28); the `N⁻¹` is the `n = 1`
Weingarten normalization of the entry column). `λ` is not a valid identifier at this
pin, whence `LamF`. -/
noncomputable def honestLamF (N : ℕ) (β : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N

/-- **The sinh symmetrization** (recorded design ruling): under
translation by the central `−1` the integrand `r·e^{βr}` maps to `(−r)·e^{−βr}`, so
its Haar integral equals `∫ r·sinh(βr)`. No differentiation under the integral, no
log-convexity, no series. -/
theorem honestLamF_eq_sinh (N : ℕ) (β : ℝ) :
    honestLamF N β
      = (N : ℝ)⁻¹ * ∫ U, reTrace U * Real.sinh (β * reTrace U) ∂haarUnitary N := by
  have h0 : (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      reTrace (negOne N * U) * Real.exp (β * reTrace (negOne N * U)))
      = fun U => (-reTrace U) * Real.exp (-(β * reTrace U)) :=
    funext fun U => by rw [reTrace_negOne_mul, mul_neg]
  have hflip : (∫ U, (-reTrace U) * Real.exp (-(β * reTrace U)) ∂haarUnitary N)
      = ∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N := by
    calc (∫ U, (-reTrace U) * Real.exp (-(β * reTrace U)) ∂haarUnitary N)
        = ∫ U, reTrace (negOne N * U) * Real.exp (β * reTrace (negOne N * U))
            ∂haarUnitary N := by rw [h0]
      _ = ∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N :=
          integral_mul_left_eq_self (μ := haarUnitary N)
            (fun U => reTrace U * Real.exp (β * reTrace U)) (negOne N)
  have hneg : (∫ U, reTrace U * Real.exp (-(β * reTrace U)) ∂haarUnitary N)
      = -∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N := by
    have h1 : (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
        reTrace U * Real.exp (-(β * reTrace U)))
        = fun U => -((-reTrace U) * Real.exp (-(β * reTrace U))) :=
      funext fun U => by ring
    rw [h1, integral_neg, hflip]
  have h2 : (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      reTrace U * Real.sinh (β * reTrace U))
      = fun U => (2 : ℝ)⁻¹ * (reTrace U * Real.exp (β * reTrace U)
          - reTrace U * Real.exp (-(β * reTrace U))) :=
    funext fun U => by rw [Real.sinh_eq]; ring
  unfold honestLamF
  rw [h2, integral_const_mul,
    integral_sub (integrable_reTrace_mul_exp N β) (integrable_reTrace_mul_exp_neg N β),
    hneg]
  ring

/-- Pointwise nonnegativity of the sinh integrand for `β ≥ 0`: `r` and `sinh (βr)`
share their sign. -/
private theorem reTrace_mul_sinh_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    0 ≤ reTrace U * Real.sinh (β * reTrace U) := by
  rcases le_or_gt 0 (reTrace U) with h | h
  · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr (mul_nonneg hβ h))
  · have key : reTrace U * Real.sinh (β * reTrace U)
        = (-reTrace U) * Real.sinh (β * -reTrace U) := by
      rw [mul_neg, Real.sinh_neg]; ring
    rw [key]
    exact mul_nonneg (neg_nonneg.mpr h.le)
      (Real.sinh_nonneg_iff.mpr (mul_nonneg hβ (neg_nonneg.mpr h.le)))

/-- **`λ_F(β) ≥ 0` for `β ≥ 0`** — from the sinh form, pointwise. -/
theorem honestLamF_nonneg (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ honestLamF N β := by
  rw [honestLamF_eq_sinh]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (integral_nonneg fun U => reTrace_mul_sinh_nonneg hβ U)

/-- **`λ_F(β) > 0` for `1 ≤ N`, `β > 0`**: the sinh integrand is continuous,
nonnegative, and strictly positive at `U = 1` (where `reTrace = N`), and the Haar
measure is open-positive (`integral_pos_of_integrable_nonneg_nonzero`). -/
theorem honestLamF_pos (N : ℕ) {β : ℝ} (hN : 1 ≤ N) (hβ : 0 < β) :
    0 < honestLamF N β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [honestLamF_eq_sinh]
  refine mul_pos (inv_pos.mpr hN0) ?_
  refine integral_pos_of_integrable_nonneg_nonzero
    (x := (1 : Matrix.unitaryGroup (Fin N) ℂ))
    (continuous_reTrace.mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_reTrace)))
    (integrable_reTrace_mul_sinh N β)
    (fun U => reTrace_mul_sinh_nonneg hβ.le U) ?_
  rw [reTrace_one]
  exact (mul_pos hN0 (Real.sinh_pos_iff.mpr (mul_pos hβ hN0))).ne'

/-- **The strict scalar gap `λ_F(β) < Z(β)`, for `1 ≤ N` and ALL β** (the
headline inequality of this file). Elementary pointwise mechanism: with `x = β·Re Tr U` and
`t = Re Tr U / N ∈ [−1, 1]`,

`t·sinh x ≤ |sinh x| = sinh |x|` and `cosh x = cosh |x|`, so
`cosh x − t·sinh x ≥ e^{−|x|} ≥ e^{−|β|N} > 0`,

and integrating against the probability measure separates the cosh form of `Z` from
the sinh form of `λ_F` by the explicit constant `e^{−|β|N}`. No series. -/
theorem honestLamF_lt_honestZ (N : ℕ) (β : ℝ) (hN : 1 ≤ N) :
    honestLamF N β < honestZ N β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  set c := Real.exp (-(|β| * N)) with hc
  have hpt : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
      (N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U)) + c
        ≤ Real.cosh (β * reTrace U) := by
    intro U
    have habs : |β * reTrace U| ≤ |β| * N := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_reTrace_le U) (abs_nonneg β)
    have h1 : (N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U))
        ≤ Real.sinh |β * reTrace U| := by
      calc (N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U))
          ≤ |(N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U))| := le_abs_self _
        _ = (N : ℝ)⁻¹ * (|reTrace U| * |Real.sinh (β * reTrace U)|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN0.le)]
        _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * |Real.sinh (β * reTrace U)|) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hN0.le)
            exact mul_le_mul_of_nonneg_right (abs_reTrace_le U) (abs_nonneg _)
        _ = |Real.sinh (β * reTrace U)| := by
            rw [← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]
        _ = Real.sinh |β * reTrace U| := Real.abs_sinh _
    have h2 : c ≤ Real.exp (-|β * reTrace U|) :=
      Real.exp_le_exp.mpr (neg_le_neg habs)
    have h3 : Real.sinh |β * reTrace U| + Real.exp (-|β * reTrace U|)
        = Real.cosh (β * reTrace U) := by
      rw [← Real.cosh_abs (β * reTrace U), ← Real.cosh_sub_sinh]
      ring
    linarith
  have hintL : Integrable (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      (N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U)) + c) (haarUnitary N) :=
    ((integrable_reTrace_mul_sinh N β).const_mul _).add (integrable_const c)
  have hmono := integral_mono hintL (integrable_cosh_reTrace N β) hpt
  have hL : (∫ U, ((N : ℝ)⁻¹ * (reTrace U * Real.sinh (β * reTrace U)) + c)
      ∂haarUnitary N) = honestLamF N β + c := by
    rw [integral_add ((integrable_reTrace_mul_sinh N β).const_mul _)
        (integrable_const c),
      integral_const_mul, integral_const, probReal_univ, one_smul,
      ← honestLamF_eq_sinh]
  rw [hL, ← honestZ_eq_cosh] at hmono
  have hcpos : 0 < c := Real.exp_pos _
  linarith

/-! ### PB-1: the conjugation pushforward `conjEquiv` -/

/-- **Entrywise complex conjugation as a continuous multiplicative equivalence of
`U(N)`** (PB-1). Entrywise conjugation is multiplicative on matrices because
conjugation is a ring homomorphism of the *commutative* ring ℂ, it preserves
unitarity (`Matrix.UnitaryGroup.map_star`), and it is an involutive homeomorphism in
the entrywise topology. -/
noncomputable def conjEquiv (N : ℕ) :
    Matrix.unitaryGroup (Fin N) ℂ ≃ₜ* Matrix.unitaryGroup (Fin N) ℂ where
  toFun U := Matrix.UnitaryGroup.map_star U
  invFun U := Matrix.UnitaryGroup.map_star U
  left_inv U := Subtype.ext (by
    ext i j
    simp [Matrix.UnitaryGroup.map_star, Matrix.map_apply])
  right_inv U := Subtype.ext (by
    ext i j
    simp [Matrix.UnitaryGroup.map_star, Matrix.map_apply])
  map_mul' U V := Subtype.ext (by
    ext i j
    simp [Matrix.UnitaryGroup.map_star, Matrix.map_apply, Matrix.mul_apply,
      Submonoid.coe_mul])
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.matrix_map continuous_star) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.matrix_map continuous_star) _

@[simp] theorem conjEquiv_val (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ((conjEquiv N U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = ((U : Matrix (Fin N) (Fin N) ℂ)).map star := rfl

/-- **PB-1: the pushforward of Haar under entrywise conjugation is Haar.** The image
measure is a Haar measure (`ContinuousMulEquiv.isHaarMeasure_map`) and a probability
measure, hence equals `haarUnitary N` by the uniqueness of Haar probability measures
(`isHaarMeasure_eq_of_isProbabilityMeasure`) — the same uniqueness pattern as the
unimodularity instance of `HaarConstruction`. -/
theorem haarUnitary_map_conjEquiv (N : ℕ) :
    (haarUnitary N).map (conjEquiv N) = haarUnitary N := by
  have h2 : IsProbabilityMeasure ((haarUnitary N).map (conjEquiv N)) :=
    isProbabilityMeasure_map ((conjEquiv N).continuous.measurable.aemeasurable)
  exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Change of variables under `conjEquiv` for ℂ-valued continuous observables. -/
theorem integral_comp_conjEquiv (N : ℕ) (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ U, f (conjEquiv N U) ∂haarUnitary N) = ∫ U, f U ∂haarUnitary N := by
  have hφ : AEMeasurable (⇑(conjEquiv N)) (haarUnitary N) :=
    (conjEquiv N).continuous.measurable.aemeasurable
  have hf : AEStronglyMeasurable (⇑f) ((haarUnitary N).map (⇑(conjEquiv N))) :=
    f.continuous.aestronglyMeasurable
  calc (∫ U, f (conjEquiv N U) ∂haarUnitary N)
      = ∫ U, f U ∂((haarUnitary N).map (⇑(conjEquiv N))) := (integral_map hφ hf).symm
    _ = ∫ U, f U ∂haarUnitary N := by rw [haarUnitary_map_conjEquiv]

/-- Change of variables under `conjEquiv` for ℝ-valued continuous integrands. -/
theorem integral_comp_conjEquiv_real (N : ℕ)
    {g : Matrix.unitaryGroup (Fin N) ℂ → ℝ} (hg : Continuous g) :
    (∫ U, g (conjEquiv N U) ∂haarUnitary N) = ∫ U, g U ∂haarUnitary N := by
  have hφ : AEMeasurable (⇑(conjEquiv N)) (haarUnitary N) :=
    (conjEquiv N).continuous.measurable.aemeasurable
  calc (∫ U, g (conjEquiv N U) ∂haarUnitary N)
      = ∫ U, g U ∂((haarUnitary N).map (⇑(conjEquiv N))) :=
        (integral_map hφ hg.aestronglyMeasurable).symm
    _ = ∫ U, g U ∂haarUnitary N := by rw [haarUnitary_map_conjEquiv]

/-- Entrywise conjugation conjugates the trace: `Tr (conj U) = conj (Tr U)`. -/
theorem trace_conjEquiv (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ((conjEquiv N U : Matrix.unitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ).trace
      = star (((U : Matrix (Fin N) (Fin N) ℂ)).trace) := by
  show (((U : Matrix (Fin N) (Fin N) ℂ)).map star).trace = _
  simp [Matrix.trace, Matrix.map_apply, Matrix.diag]

/-- Entrywise conjugation fixes `reTrace`: `Re Tr (conj U) = Re Tr U`. -/
theorem reTrace_conjEquiv (U : Matrix.unitaryGroup (Fin N) ℂ) :
    reTrace (conjEquiv N U) = reTrace U := by
  show ((conjEquiv N U : Matrix.unitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ).trace.re = _
  rw [trace_conjEquiv, Complex.star_def, Complex.conj_re]
  rfl

/-- Entrywise conjugation fixes the Boltzmann weight. -/
theorem expObs_conjEquiv (β : ℝ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    expObs N β (conjEquiv N U) = expObs N β U := by
  simp only [expObs_apply, reTrace_conjEquiv]

/-! ### The reality bridge -/

/-- **The conjugation kill**: against the star-fixed weight `expObs`, the starred
trace integrates to the same value as the trace — the `conjEquiv` change of
variables sends `conj (Tr U) · e^{β Re Tr U}` to `Tr U · e^{β Re Tr U}`. -/
theorem haarExpectation_star_traceObs_mul_expObs (N : ℕ) (β : ℝ) :
    haarExpectation N (star (traceObs N) * expObs N β)
      = haarExpectation N (traceObs N * expObs N β) := by
  show (∫ U, (star (traceObs N) * expObs N β) U ∂haarUnitary N)
      = ∫ U, (traceObs N * expObs N β) U ∂haarUnitary N
  rw [← integral_comp_conjEquiv N (star (traceObs N) * expObs N β)]
  have h : (fun U => (star (traceObs N) * expObs N β) (conjEquiv N U))
      = fun U => (traceObs N * expObs N β) U := by
    funext U
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, traceObs_apply,
      expObs_conjEquiv, trace_conjEquiv, star_star]
  rw [h]

/-- **The reality bridge (PB-1 payoff)**: the ℂ-valued Haar integral of
`Tr U · e^{β Re Tr U}` is star-fixed, i.e. real. Star-reality of the honest
expectation moves the star onto the observable; `expObs` is star-fixed; the
conjugation kill finishes. In the development in which this layer originated this
packaged reality content for downstream
consumers; this leaf is kept as the interface-level star-fixedness certificate
(the PB-1 chain feeding the cast identities below IS load-bearing). -/
theorem traceExp_isReal (N : ℕ) (β : ℝ) :
    star (haarExpectation N (traceObs N * expObs N β))
      = haarExpectation N (traceObs N * expObs N β) := by
  rw [← haarExpectation_isStarReal N (traceObs N * expObs N β), star_mul',
    expObs_star_eq, haarExpectation_star_traceObs_mul_expObs]

/-- The ℂ-valued expectation of the weight is the cast of the real vacuum scalar:
`E (expObs) = (honestZ : ℂ)`. -/
theorem haarExpectation_expObs (N : ℕ) (β : ℝ) :
    haarExpectation N (expObs N β) = ((honestZ N β : ℝ) : ℂ) := by
  show (∫ U, expObs N β U ∂haarUnitary N) = _
  simp only [expObs_apply]
  exact integral_ofReal

/-- **The fundamental-column cast identity**: the ℂ-valued Haar integral of
`Tr U · e^{β Re Tr U}` equals the cast of the *real* integral
`∫ (Re Tr U) e^{β Re Tr U} dU` — the exact real/complex hand-off for eigen-equation
consumers (in the development in which this layer originated; not ported here). -/
theorem haarExpectation_traceObs_mul_expObs (N : ℕ) (β : ℝ) :
    haarExpectation N (traceObs N * expObs N β)
      = ((∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N : ℝ) : ℂ) := by
  have hobs : reTraceObs N * expObs N β
      = (2⁻¹ : ℂ) • (traceObs N * expObs N β + star (traceObs N) * expObs N β) := by
    rw [reTraceObs, smul_mul_assoc, add_mul]
  have h1 : haarExpectation N (reTraceObs N * expObs N β)
      = haarExpectation N (traceObs N * expObs N β) := by
    rw [hobs, HaarExpectation.map_smul, HaarExpectation.map_add,
      haarExpectation_star_traceObs_mul_expObs]
    ring
  have h2 : haarExpectation N (reTraceObs N * expObs N β)
      = ((∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N : ℝ) : ℂ) := by
    show (∫ U, (reTraceObs N * expObs N β) U ∂haarUnitary N) = _
    have h : (fun U => (reTraceObs N * expObs N β) U)
        = fun U : Matrix.unitaryGroup (Fin N) ℂ =>
            ((reTrace U * Real.exp (β * reTrace U) : ℝ) : ℂ) := by
      funext U
      simp only [ContinuousMap.mul_apply, expObs_apply, ← ofReal_reTrace,
        ← Complex.ofReal_mul]
    rw [h]
    exact integral_ofReal
  rw [← h1, h2]

/-- The fundamental-column identity in `honestLamF` form (`1 ≤ N`):
`E (Tr U · e^{β Re Tr U}) = N · λ_F(β)` as complex numbers. -/
theorem haarExpectation_traceObs_mul_expObs_eq_lamF (N : ℕ) (β : ℝ) (hN : 1 ≤ N) :
    haarExpectation N (traceObs N * expObs N β)
      = (((N : ℝ) * honestLamF N β : ℝ) : ℂ) := by
  have hN0 : ((N : ℝ)) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have h : (N : ℝ) * honestLamF N β
      = ∫ U, reTrace U * Real.exp (β * reTrace U) ∂haarUnitary N := by
    unfold honestLamF
    rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  rw [haarExpectation_traceObs_mul_expObs, h]

end Weingarten.Haar
