/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West

Ported 2026-07-12; namespace/name surgery only, proofs byte-identical; this copy is authoritative going forward.
-/
import Weingarten.Haar.HaarConstruction
import Weingarten.Haar.SecondCountableShim
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The pair Haar expectation on `U(N) × U(N)` (PH-1–PH-3)

The two-copy analogue of `Weingarten.Haar.HaarExpectation`: an abstract
interface `PairHaarExpectation N E` for a normalized linear functional on continuous
pair observables `C(U(N) × U(N), ℂ)` that is invariant under translation in **each
slot separately** (left and right), covariant under the slot swap, and whose two
marginals are a designated one-variable Haar expectation `E` — together with the
honest witness `pairHaarExpectation N`, integration against the product measure
`(haarUnitary N).prod (haarUnitary N)`.

**Marginal target as an explicit structure parameter** (recorded design decision of
the development in which this layer originated). The marginal fields could quantify existentially over a
one-variable expectation; instead the target `E : HaarExpectation N` is a structure
*parameter*, so the witness statement `pairHaarExpectation N : PairHaarExpectation N
(haarExpectation N)` is self-documenting: the slot marginals of product Haar are
*the* honest Haar expectation, not merely *some* expectation.

**Per-slot translation encoding.** `U(N) × U(N)` is itself a compact topological
group (all instances fire by `inferInstance`, given the `SecondCountableShim`), and
translation in the first slot is translation by `(g, 1)` in the product group:
`(g, 1) * (U, V) = (g * U, V)`. The invariance fields therefore reuse the frozen
one-variable vocabulary `ContinuousMap.mulLeft`/`mulRight` verbatim, now at the
product group; the reading aids `mulLeft_pair_fst_apply` … `mulRight_pair_snd_apply`
record the per-slot content pointwise.

## The witness (PH-1)

* `pairHaar N := (haarUnitary N).prod (haarUnitary N)`, a probability measure
  (`Measure/Prod.lean:322`) that is left- and right-invariant for the product group
  (`Measure.prod.instIsMulLeftInvariant`/`…RightInvariant`,
  `Group/Measure.lean:130/:140`) — declared as instances on the `pairHaar` name.
* Integrability of continuous pair observables is
  `Continuous.integrable_of_hasCompactSupport`
  (`Function/LocallyIntegrable.lean:622`); the `OpensMeasurableSpace` demand on the
  product is discharged by the `SecondCountableShim`.
* The marginal identities are the verified pushforward route:
  `measurePreserving_fst`/`_snd` (`Measure/Prod.lean:258/:266`) + `integral_map` +
  `aestronglyMeasurable`; the swap is `Measure.prod_swap` (`Measure/Prod.lean:676`).

## Scope

The interface and witness (PH-1), plus: PH-2 is the
factorization theorem `pairE_prod_factorizes` — a **theorem of the witness** via
the hypothesis-free `integral_prod_mul` (recorded decision:
no interface field needed) — with the polynomial extension
`pairE_polynomial_factorizes` by linearity; PH-3 is the multiplication-composite
expectation `PairHaarExpectation.compMul : HaarExpectation N`, built from the
PH-1 structure fields only (**zero Fubini**), with the witness-level agreement
`pairHaarExpectation_compMul_eq`. `Mathlib.MeasureTheory.Integral.Prod` is
imported explicitly for the PH-2/witness-corollary Fubini layer. (PH-1..PH-5 are
this layer's law numbering, used across `PairHaar` and `ProductHaar`: PH-1 the pair
witness, PH-2 factorization, PH-3 `compMul`, PH-4 the product measure, PH-5 the
triangular substitution — with PH-6 the honest tilted measures.)
-/

namespace Weingarten.Haar

open MeasureTheory MeasureTheory.Measure

/-- An abstract **pair Haar expectation** on `U(N) × U(N)` against a designated
one-variable Haar expectation `E`: a ℂ-linear functional on the continuous pair
observables `C(U(N) × U(N), ℂ)` that is

* **normalized** (`toFun 1 = 1`),
* **invariant under left and right translation in each slot separately** — stated as
  product-group translation by `(g, 1)` (first slot) and `(1, g)` (second slot),
* **covariant under the slot swap** `(U, V) ↦ (V, U)`, and
* **marginalized by `E`**: on observables of one slot only, it agrees with `E`.

The marginal target `E` is an explicit structure parameter rather than an
existential — a recorded design decision: it makes the witness
statement (`PairHaarExpectation N (haarExpectation N)`) self-documenting. -/
structure PairHaarExpectation (N : ℕ) (E : HaarExpectation N) where
  /-- The underlying ℂ-linear expectation functional on continuous pair
  observables. -/
  toFun : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ) →ₗ[ℂ] ℂ
  /-- The expectation of the constant observable `1` is `1`. -/
  normalized : toFun 1 = 1
  /-- Invariance under left translation `(U, V) ↦ (g * U, V)` in the first slot. -/
  left_invariant_fst : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulLeft
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = toFun f
  /-- Invariance under left translation `(U, V) ↦ (U, g * V)` in the second slot. -/
  left_invariant_snd : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulLeft
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = toFun f
  /-- Invariance under right translation `(U, V) ↦ (U * g, V)` in the first slot. -/
  right_invariant_fst : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulRight
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = toFun f
  /-- Invariance under right translation `(U, V) ↦ (U, V * g)` in the second slot. -/
  right_invariant_snd : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulRight
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = toFun f
  /-- Covariance under the slot swap `(U, V) ↦ (V, U)`. -/
  swap_invariant : ∀
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp ContinuousMap.prodSwap) = toFun f
  /-- The first-slot marginal is the designated one-variable expectation `E`. -/
  marginal_fst : ∀ (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp ContinuousMap.fst) = E f
  /-- The second-slot marginal is the designated one-variable expectation `E`. -/
  marginal_snd : ∀ (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp ContinuousMap.snd) = E f

/-! ### Reading aids: the per-slot content of the product-group translations -/

/-- First-slot left translation, pointwise: `(g, 1) * (U, V) = (g * U, V)`. -/
theorem mulLeft_pair_fst_apply {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :
    (ContinuousMap.mulLeft
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) p
      = (g * p.1, p.2) := by
  simp [Prod.ext_iff]

/-- Second-slot left translation, pointwise: `(1, g) * (U, V) = (U, g * V)`. -/
theorem mulLeft_pair_snd_apply {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :
    (ContinuousMap.mulLeft
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) p
      = (p.1, g * p.2) := by
  simp [Prod.ext_iff]

/-- First-slot right translation, pointwise: `(U, V) * (g, 1) = (U * g, V)`. -/
theorem mulRight_pair_fst_apply {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :
    (ContinuousMap.mulRight
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) p
      = (p.1 * g, p.2) := by
  simp [Prod.ext_iff]

/-- Second-slot right translation, pointwise: `(U, V) * (1, g) = (U, V * g)`. -/
theorem mulRight_pair_snd_apply {N : ℕ} (g : Matrix.unitaryGroup (Fin N) ℂ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :
    (ContinuousMap.mulRight
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) p
      = (p.1, p.2 * g) := by
  simp [Prod.ext_iff]

namespace PairHaarExpectation

variable {N : ℕ} {E : HaarExpectation N}

noncomputable instance instFunLike :
    FunLike (PairHaarExpectation N E)
      C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ) ℂ where
  coe P := P.toFun
  coe_injective := fun P Q h => by
    obtain ⟨tP, nP, lfP, lsP, rfP, rsP, swP, mfP, msP⟩ := P
    obtain ⟨tQ, nQ, lfQ, lsQ, rfQ, rsQ, swQ, mfQ, msQ⟩ := Q
    obtain rfl : tP = tQ := DFunLike.coe_injective h
    rfl

/-- Applying the bundled `LinearMap` agrees with the `FunLike` coercion. -/
theorem toFun_apply (P : PairHaarExpectation N E)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P.toFun f = P f := rfl

/-- Normalization, restated through the coercion: `P 1 = 1`. -/
@[simp] theorem map_one (P : PairHaarExpectation N E) :
    P (1 : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) = 1 :=
  P.normalized

/-- First-slot left invariance, restated through the coercion. -/
theorem map_left_mul_fst (P : PairHaarExpectation N E)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp (ContinuousMap.mulLeft
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = P f :=
  P.left_invariant_fst g f

/-- Second-slot left invariance, restated through the coercion. -/
theorem map_left_mul_snd (P : PairHaarExpectation N E)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp (ContinuousMap.mulLeft
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = P f :=
  P.left_invariant_snd g f

/-- First-slot right invariance, restated through the coercion. -/
theorem map_right_mul_fst (P : PairHaarExpectation N E)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp (ContinuousMap.mulRight
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = P f :=
  P.right_invariant_fst g f

/-- Second-slot right invariance, restated through the coercion. -/
theorem map_right_mul_snd (P : PairHaarExpectation N E)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp (ContinuousMap.mulRight
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)))
      = P f :=
  P.right_invariant_snd g f

/-- Slot-swap covariance, restated through the coercion. -/
theorem map_swap (P : PairHaarExpectation N E)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp ContinuousMap.prodSwap) = P f :=
  P.swap_invariant f

/-- The first-slot marginal, restated through the coercion: `P (f ∘ fst) = E f`. -/
theorem map_marginal_fst (P : PairHaarExpectation N E)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp ContinuousMap.fst) = E f :=
  P.marginal_fst f

/-- The second-slot marginal, restated through the coercion: `P (f ∘ snd) = E f`. -/
theorem map_marginal_snd (P : PairHaarExpectation N E)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f.comp ContinuousMap.snd) = E f :=
  P.marginal_snd f

/-- A pair Haar expectation is additive. -/
protected theorem map_add (P : PairHaarExpectation N E)
    (f g : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (f + g) = P f + P g :=
  P.toFun.map_add f g

/-- Scalars pull out of a pair Haar expectation. -/
protected theorem map_smul (P : PairHaarExpectation N E) (c : ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (c • f) = c * P f :=
  P.toFun.map_smul c f

/-- The expectation of a constant pair observable is that constant. -/
@[simp] protected theorem map_const (P : PairHaarExpectation N E) (c : ℂ) :
    P (ContinuousMap.const
      (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) c) = c := by
  have h : ContinuousMap.const
      (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) c
      = c • (1 : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ))
      := by
    ext p; simp
  rw [h, P.map_smul, P.map_one, mul_one]

end PairHaarExpectation

/-! ### The pair Haar measure -/

/-- **The pair Haar measure on `U(N) × U(N)`**: the product of two copies of the Haar
probability measure `haarUnitary N`. -/
noncomputable def pairHaar (N : ℕ) :
    Measure (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :=
  (haarUnitary N).prod (haarUnitary N)

/-- `pairHaar N` is a probability measure (`Measure/Prod.lean:322`). -/
instance instIsProbabilityMeasurePairHaar (N : ℕ) :
    IsProbabilityMeasure (pairHaar N) :=
  inferInstanceAs (IsProbabilityMeasure ((haarUnitary N).prod (haarUnitary N)))

/-- `pairHaar N` is left-invariant for the product group `U(N) × U(N)` — in
particular under each per-slot left translation `(g, 1)`/`(1, g)`
(`Measure.prod.instIsMulLeftInvariant`, `Group/Measure.lean:130`). -/
instance instIsMulLeftInvariantPairHaar (N : ℕ) :
    IsMulLeftInvariant (pairHaar N) :=
  inferInstanceAs (IsMulLeftInvariant ((haarUnitary N).prod (haarUnitary N)))

/-- `pairHaar N` is right-invariant for the product group `U(N) × U(N)` — the two
factors are right-invariant by unimodularity of the compact group `U(N)`
(`Measure.prod.instIsMulRightInvariant`, `Group/Measure.lean:140`). -/
instance instIsMulRightInvariantPairHaar (N : ℕ) :
    IsMulRightInvariant (pairHaar N) :=
  inferInstanceAs (IsMulRightInvariant ((haarUnitary N).prod (haarUnitary N)))

/-- Every continuous pair observable is integrable for `pairHaar N`: the product
space is compact, so continuous functions have compact support, and the product
measure is finite. The `OpensMeasurableSpace` demand on the product is discharged by
the `SecondCountableShim`. -/
theorem integrable_continuousMap_pair (N : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    Integrable f (pairHaar N) :=
  f.continuous.integrable_of_hasCompactSupport ((isClosed_tsupport _).isCompact)

/-- The first-slot pushforward of `pairHaar N` is `haarUnitary N`
(`measurePreserving_fst`, `Measure/Prod.lean:258`). -/
theorem pairHaar_map_fst (N : ℕ) : (pairHaar N).map Prod.fst = haarUnitary N :=
  (measurePreserving_fst (μ := haarUnitary N) (ν := haarUnitary N)).map_eq

/-- The second-slot pushforward of `pairHaar N` is `haarUnitary N`
(`measurePreserving_snd`, `Measure/Prod.lean:266`). -/
theorem pairHaar_map_snd (N : ℕ) : (pairHaar N).map Prod.snd = haarUnitary N :=
  (measurePreserving_snd (μ := haarUnitary N) (ν := haarUnitary N)).map_eq

/-- `pairHaar N` is invariant under the slot swap (`Measure.prod_swap`,
`Measure/Prod.lean:676`, with both factors equal). -/
theorem pairHaar_map_swap (N : ℕ) : (pairHaar N).map Prod.swap = pairHaar N :=
  Measure.prod_swap

/-! ### The honest witness -/

/-- **The pair Haar expectation on `U(N) × U(N)`, for every `N`** (the PH-1
witness): integration of
continuous pair observables against the product measure `pairHaar N`. Its marginals
are the honest one-variable Haar expectation `haarExpectation N` — the marginal
parameter of the interface is discharged at the *designated* expectation, not an
existential one.

* linearity: `integral_add` (with `integrable_continuousMap_pair`) and
  `integral_smul`;
* normalization: `integral_const` on a probability measure;
* per-slot invariances: `integral_mul_left_eq_self`/`integral_mul_right_eq_self` at
  the product group elements `(g, 1)` and `(1, g)`, through the product invariance
  instances on `pairHaar`;
* slot swap: `Measure.prod_swap` + `integral_map`;
* marginals: `measurePreserving_fst`/`_snd` + `integral_map` (the verified
  pushforward route). -/
noncomputable def pairHaarExpectation (N : ℕ) :
    PairHaarExpectation N (haarExpectation N) where
  toFun :=
    { toFun := fun f => ∫ p, f p ∂pairHaar N
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap_pair N f)
          (integrable_continuousMap_pair N g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c fun p => f p }
  normalized := by
    show (∫ p, (1 : C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ,
        ℂ)) p ∂pairHaar N) = 1
    simp only [ContinuousMap.one_apply, integral_const, probReal_univ, one_smul]
  left_invariant_fst g f := by
    show (∫ p, (f.comp (ContinuousMap.mulLeft
        ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ))) p
        ∂pairHaar N) = ∫ p, f p ∂pairHaar N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft]
    exact integral_mul_left_eq_self (μ := pairHaar N) (fun p => f p)
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)
  left_invariant_snd g f := by
    show (∫ p, (f.comp (ContinuousMap.mulLeft
        ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ))) p
        ∂pairHaar N) = ∫ p, f p ∂pairHaar N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft]
    exact integral_mul_left_eq_self (μ := pairHaar N) (fun p => f p)
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)
  right_invariant_fst g f := by
    show (∫ p, (f.comp (ContinuousMap.mulRight
        ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ))) p
        ∂pairHaar N) = ∫ p, f p ∂pairHaar N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight]
    exact integral_mul_right_eq_self (μ := pairHaar N) (fun p => f p)
      ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)
  right_invariant_snd g f := by
    show (∫ p, (f.comp (ContinuousMap.mulRight
        ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ))) p
        ∂pairHaar N) = ∫ p, f p ∂pairHaar N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight]
    exact integral_mul_right_eq_self (μ := pairHaar N) (fun p => f p)
      ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)
  swap_invariant f := by
    show (∫ p, f (Prod.swap p) ∂pairHaar N) = ∫ p, f p ∂pairHaar N
    calc (∫ p, f (Prod.swap p) ∂pairHaar N)
        = ∫ q, f q ∂((pairHaar N).map Prod.swap) :=
          (integral_map measurable_swap.aemeasurable
            f.continuous.aestronglyMeasurable).symm
      _ = ∫ q, f q ∂pairHaar N := by rw [pairHaar_map_swap]
  marginal_fst f := by
    show (∫ p, f p.1 ∂pairHaar N) = ∫ U, f U ∂haarUnitary N
    calc (∫ p, f p.1 ∂pairHaar N)
        = ∫ U, f U ∂((pairHaar N).map Prod.fst) :=
          (integral_map measurable_fst.aemeasurable
            f.continuous.aestronglyMeasurable).symm
      _ = ∫ U, f U ∂haarUnitary N := by rw [pairHaar_map_fst]
  marginal_snd f := by
    show (∫ p, f p.2 ∂pairHaar N) = ∫ U, f U ∂haarUnitary N
    calc (∫ p, f p.2 ∂pairHaar N)
        = ∫ U, f U ∂((pairHaar N).map Prod.snd) :=
          (integral_map measurable_snd.aemeasurable
            f.continuous.aestronglyMeasurable).symm
      _ = ∫ U, f U ∂haarUnitary N := by rw [pairHaar_map_snd]

/-! ### Gates: the marginals of product Haar are the honest Haar expectation -/

/-- **First-slot marginal of the pair Haar expectation**: on observables of
the first slot only, the product-Haar integral is the honest one-variable Haar
expectation. -/
theorem pairHaarExpectation_marginal_fst (N : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    pairHaarExpectation N (f.comp ContinuousMap.fst) = haarExpectation N f :=
  (pairHaarExpectation N).marginal_fst f

/-- **Second-slot marginal of the pair Haar expectation**: on observables
of the second slot only, the product-Haar integral is the honest one-variable Haar
expectation. -/
theorem pairHaarExpectation_marginal_snd (N : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    pairHaarExpectation N (f.comp ContinuousMap.snd) = haarExpectation N f :=
  (pairHaarExpectation N).marginal_snd f

/-! ### Payoff probes -/

/-- The pair interface is inhabited for **all** `N`, at the designated marginal
`haarExpectation N`. -/
example (N : ℕ) : Nonempty (PairHaarExpectation N (haarExpectation N)) :=
  ⟨pairHaarExpectation N⟩

/-- The genuine product-Haar integral of the first-slot trace vanishes — the
one-variable moment, reached through the marginal gate. -/
example (N : ℕ) :
    pairHaarExpectation N ((traceObs N).comp ContinuousMap.fst) = 0 := by
  rw [pairHaarExpectation_marginal_fst]
  exact (haarExpectation N).integral_trace

/-! ## PH-2 factorization and PH-3 `compMul` -/

/-! ### PH-2: factorization on product observables — a theorem of the witness

**Recorded design decision:** "PH-2 factorization
`pairE_prod_factorizes` as THEOREM-OF-WITNESS (decision recorded:
`integral_prod_mul` is hypothesis-free at the pin, no interface field needed) +
polynomial factorization by linearity." Verified at the pin: `integral_prod_mul`
(`Mathlib/MeasureTheory/Integral/Prod.lean:579`) takes **no integrability
hypotheses** — its only demands are the `[SFinite]` section instances, discharged
by the probability instances on `haarUnitary N` — so the factorization identity
is stated against the honest witness `pairHaarExpectation N`, and **no**
`PairHaarExpectation` interface field is added. -/

/-- **PH-2 factorization (theorem of the witness)**: on product observables the
pair Haar expectation factorizes slot-by-slot,
`E₂((f ∘ fst) · (g ∘ snd)) = E f · E g` with `E = haarExpectation N`.

Stated against the witness `pairHaarExpectation N`, NOT as an interface field —
the recorded design decision: `integral_prod_mul` is
hypothesis-free at the pin (`Mathlib/MeasureTheory/Integral/Prod.lean:579`), so
the identity needs no side conditions and no new structure field. -/
theorem pairE_prod_factorizes (N : ℕ)
    (f g : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    pairHaarExpectation N
        ((f.comp ContinuousMap.fst) * (g.comp ContinuousMap.snd))
      = haarExpectation N f * haarExpectation N g := by
  show (∫ p, f p.1 * g p.2 ∂(haarUnitary N).prod (haarUnitary N))
      = (∫ U, f U ∂haarUnitary N) * ∫ V, g V ∂haarUnitary N
  exact integral_prod_mul (fun U => f U) (fun V => g V)

/-- A pair Haar expectation commutes with finite sums of pair observables
(the two-slot sibling of `HaarExpectation.map_sum`). -/
protected theorem PairHaarExpectation.map_sum {N : ℕ} {E : HaarExpectation N}
    (P : PairHaarExpectation N E) {ι : Type*} (s : Finset ι)
    (f : ι → C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P (∑ x ∈ s, f x) = ∑ x ∈ s, P (f x) := by
  exact map_sum P.toFun f s

/-- **Polynomial factorization by linearity** (the PH-2 extension; blueprint name
`pairE_polynomial_factorizes`): finite sums of product observables — the span in
which the two-slot polynomial observables live — factorize term-by-term under the
pair Haar expectation. Pure linearity on top of `pairE_prod_factorizes`; scalar
coefficients are absorbed into either slot by `HaarExpectation.map_smul`. -/
theorem pairE_polynomial_factorizes (N : ℕ) {ι : Type*} (s : Finset ι)
    (f g : ι → C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    pairHaarExpectation N
        (∑ i ∈ s, ((f i).comp ContinuousMap.fst) * ((g i).comp ContinuousMap.snd))
      = ∑ i ∈ s, haarExpectation N (f i) * haarExpectation N (g i) := by
  rw [PairHaarExpectation.map_sum]
  exact Finset.sum_congr rfl fun i _ => pairE_prod_factorizes N (f i) (g i)

/-! ### PH-3: the multiplication-composite expectation `compMul` -/

/-- The group multiplication `(U, V) ↦ U * V` on `U(N)`, as a continuous map.
(The pin has no `ContinuousMap.mul'`; built directly from `continuous_mul`.) -/
noncomputable def mulMap (N : ℕ) :
    C(Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ,
      Matrix.unitaryGroup (Fin N) ℂ) :=
  ⟨fun p => p.1 * p.2, continuous_mul⟩

@[simp] theorem mulMap_apply (N : ℕ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :
    mulMap N p = p.1 * p.2 := rfl

/-- **Left translation threads through multiplication**: first-slot left
translation by `(g, 1)` BEFORE multiplying is left translation by `g` AFTER
multiplying — pointwise `(g * U) * V = g * (U * V)`, i.e. associativity. This is
the whole content of `compMul`'s left invariance. -/
theorem comp_mulMap_mulLeft_fst (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (f.comp (ContinuousMap.mulLeft g)).comp (mulMap N)
      = (f.comp (mulMap N)).comp (ContinuousMap.mulLeft
          ((g, 1) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) := by
  ext p
  simp [ContinuousMap.coe_mulLeft, Prod.fst_mul, Prod.snd_mul, mul_assoc]

/-- **Right translation threads through multiplication**: second-slot right
translation by `(1, g)` BEFORE multiplying is right translation by `g` AFTER
multiplying — pointwise `U * (V * g) = (U * V) * g`. This is the whole content of
`compMul`'s right invariance. -/
theorem comp_mulMap_mulRight_snd (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (f.comp (ContinuousMap.mulRight g)).comp (mulMap N)
      = (f.comp (mulMap N)).comp (ContinuousMap.mulRight
          ((1, g) : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ)) := by
  ext p
  simp [ContinuousMap.coe_mulRight, Prod.fst_mul, Prod.snd_mul, mul_assoc]

namespace PairHaarExpectation

variable {N : ℕ} {E : HaarExpectation N}

/-- **PH-3: the multiplication-composite expectation.**
Precomposition with the group multiplication `mulMap N : U(N) × U(N) → U(N)`
turns any abstract pair Haar expectation into a one-variable Haar expectation,
`f ↦ E₂(f ∘ mul)`.

**Zero-Fubini discipline ("PH-1 fields only; zero Fubini"):** every
`HaarExpectation` field is discharged from the `PairHaarExpectation` structure
fields alone — linearity from `toFun` linearity, normalization from `normalized`
(`1 ∘ mul = 1`), left invariance from `left_invariant_fst` through associativity
`g * (U * V) = (g * U) * V` (`comp_mulMap_mulLeft_fst`), right invariance from
`right_invariant_snd` through `(U * V) * g = U * (V * g)`
(`comp_mulMap_mulRight_snd`). The concrete witness, the product measure, and the
Fubini layer are never consulted. -/
noncomputable def compMul (P : PairHaarExpectation N E) : HaarExpectation N where
  toFun :=
    { toFun := fun f => P (f.comp (mulMap N))
      map_add' := fun f g => by
        show P ((f + g).comp (mulMap N))
            = P (f.comp (mulMap N)) + P (g.comp (mulMap N))
        rw [ContinuousMap.add_comp]
        exact P.map_add _ _
      map_smul' := fun c f => by
        show P ((c • f).comp (mulMap N)) = c * P (f.comp (mulMap N))
        rw [ContinuousMap.smul_comp]
        exact P.map_smul c _ }
  normalized := by
    show P ((1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)).comp (mulMap N)) = 1
    rw [ContinuousMap.one_comp]
    exact P.map_one
  left_invariant g f := by
    show P ((f.comp (ContinuousMap.mulLeft g)).comp (mulMap N))
        = P (f.comp (mulMap N))
    rw [comp_mulMap_mulLeft_fst]
    exact P.map_left_mul_fst g (f.comp (mulMap N))
  right_invariant g f := by
    show P ((f.comp (ContinuousMap.mulRight g)).comp (mulMap N))
        = P (f.comp (mulMap N))
    rw [comp_mulMap_mulRight_snd]
    exact P.map_right_mul_snd g (f.comp (mulMap N))

/-- Unfolding lemma for `compMul`: `P.compMul f = P (f ∘ mul)`. -/
theorem compMul_apply (P : PairHaarExpectation N E)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    P.compMul f = P (f.comp (mulMap N)) := rfl

end PairHaarExpectation

/-! ### The witness corollary: `compMul` of the honest witness is the honest Haar
expectation

For the concrete witness the composite `f ↦ E₂(f ∘ mul)` is not merely *a*
one-variable Haar expectation — it agrees with `haarExpectation N` on every
observable. Witness-level, so Fubini is fair game (the zero-Fubini discipline
binds only the abstract `compMul` above): `integral_prod` iterates the pair
integral, and for each fixed first slot the inner integral kills the translation
by left invariance of `haarUnitary N`. -/

/-- **Witness-level agreement**: `compMul` of the honest pair
witness is the honest one-variable Haar expectation on every observable —
`∫∫ f(U·V) dV dU = ∫ f dU`. -/
theorem pairHaarExpectation_compMul_eq (N : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (pairHaarExpectation N).compMul f = haarExpectation N f := by
  have hInt : Integrable
      (fun p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ =>
        f (p.1 * p.2)) ((haarUnitary N).prod (haarUnitary N)) :=
    integrable_continuousMap_pair N (f.comp (mulMap N))
  have hinner : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
      (∫ V, f (U * V) ∂haarUnitary N) = ∫ V, f V ∂haarUnitary N := fun U =>
    integral_mul_left_eq_self (μ := haarUnitary N) (fun V => f V) U
  show (∫ p, f (p.1 * p.2) ∂(haarUnitary N).prod (haarUnitary N))
      = ∫ U, f U ∂haarUnitary N
  rw [integral_prod _ hInt]
  simp only [hinner]
  simp only [integral_const, probReal_univ, one_smul]

/-! ### Payoff probes (PH-2/PH-3) -/

/-- The abstract interface composes: every pair Haar expectation yields a
one-variable Haar expectation by multiplication — PH-3 inhabits the one-variable
interface with zero Fubini, for all `N`. -/
noncomputable example (N : ℕ) (P : PairHaarExpectation N (haarExpectation N)) :
    HaarExpectation N := P.compMul

/-- The genuine product-Haar integral of the multiplied trace vanishes — the
one-variable moment reached through `compMul`: `∫∫ Tr(U·V) dV dU = 0`. -/
example (N : ℕ) : (pairHaarExpectation N).compMul (traceObs N) = 0 := by
  rw [pairHaarExpectation_compMul_eq]
  exact (haarExpectation N).integral_trace

/-- Factorization payoff: the two-slot trace product factorizes and vanishes,
`E₂(Tr(U)·Tr(V)) = E(Tr)·E(Tr) = 0`. -/
example (N : ℕ) :
    pairHaarExpectation N
        (((traceObs N).comp ContinuousMap.fst)
          * ((traceObs N).comp ContinuousMap.snd)) = 0 := by
  rw [pairE_prod_factorizes, (haarExpectation N).integral_trace, mul_zero]

end Weingarten.Haar
