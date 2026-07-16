/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.HaarExpectation
import Weingarten.Haar.MatrixEntryIntegrals
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Construction of the Haar expectation on `U(N)`

This file inhabits the interface `Weingarten.Haar.HaarExpectation N` for **every** `N`, by
integrating continuous observables against Mathlib's Haar probability measure on the
compact group `Matrix.unitaryGroup (Fin N) ℂ`. Every theorem downstream that is
conditional on `(E : HaarExpectation N)` thereby becomes an unconditional statement
about genuine Haar integrals — see the closing `example`s.

## Contents

* `isCompact_unitaryGroup` / `instCompactSpaceUnitaryGroup`: `U(N)` is compact — it is
  a closed subset (`isClosed_unitary`) of the compact set of matrices whose entries all
  lie in the closed unit disc (`IsCompact.matrix` on `Metric.closedBall 0 1`, with the
  entry bound `entry_norm_bound_of_unitary`).
* `instMeasurableSpaceUnitaryGroup` / `instBorelSpaceUnitaryGroup`: the Borel σ-algebra.
  Mathlib has no `MeasurableSpace` instance on `Matrix` (nor, a fortiori, on its
  unitary subtype), so `borel _` with `BorelSpace _ := ⟨rfl⟩` creates no diamond.
* `haarUnitary`: the Haar probability measure `haarMeasure ⊤`, normalized on the
  positive compact `⊤ = univ` — the same pattern as `AddCircle.haarAddCircle`.
  It is a left-invariant Haar probability measure by construction.
* `instIsMulRightInvariantHaarUnitary`: **compact groups are unimodular.** The image of
  `haarUnitary N` under right translation is again a Haar probability measure
  (`isHaarMeasure_map_mul_right`, `Measure.isProbabilityMeasure_map`), so by the
  uniqueness of Haar probability measures
  (`Measure.isHaarMeasure_eq_of_isProbabilityMeasure`) it coincides with `haarUnitary N`.
* `integrable_continuousMap`: continuous observables are integrable — on a compact
  space every continuous function has compact support.
* `haarExpectation`: the Haar state `f ↦ ∫ U, f U ∂(haarUnitary N)`, packaged as a
  `HaarExpectation N`. Linearity is `integral_add`/`integral_smul`, normalization is
  `integral_const` on a probability measure, and the two invariances are
  `integral_mul_left_eq_self` / `integral_mul_right_eq_self`.

## Provenance

The existence of the bi-invariant Haar state on a compact group is classical
(Haar–von Neumann–Weil); the formulation as a normalized bi-invariant linear functional
on `C(G)` follows Banica–Collins, arXiv:math/0511253, Def. 4.1, as recorded in
`Weingarten.Haar.HaarExpectation`. The measure-theoretic input is Mathlib's
`MeasureTheory.Measure.haarMeasure` and the uniqueness theory of
`Mathlib.MeasureTheory.Measure.Haar.Unique`.
-/

namespace Weingarten.Haar

open MeasureTheory MeasureTheory.Measure

/-! ### Compactness of `U(N)` -/

/-- **`U(N)` is a compact subset of matrix space.** It is closed (`isClosed_unitary`,
since unitarity is the closed condition `star U * U = 1 ∧ U * star U = 1`) and contained
in the compact set of matrices all of whose entries lie in the closed unit disc
(`IsCompact.matrix` applied to `Metric.closedBall (0 : ℂ) 1`; the entry bound is
`entry_norm_bound_of_unitary`). -/
theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) :=
  ((isCompact_closedBall (0 : ℂ) 1).matrix).of_isClosed_subset isClosed_unitary
    fun _U hU => Set.mem_matrix.mpr fun i j =>
      mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hU i j)

/-- The unitary group `U(N)` is a compact topological space. -/
instance instCompactSpaceUnitaryGroup (N : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

/-! ### The Borel measurable structure

Mathlib provides no `MeasurableSpace` instance on `Matrix m n α` (matrix topology
instances exist in `Mathlib.Topology.Instances.Matrix`, but no measurable-space
counterpart), hence none on the unitary subtype either. Declaring the Borel σ-algebra
directly therefore creates no instance diamond. -/

/-- The Borel σ-algebra on `U(N)`. -/
noncomputable instance instMeasurableSpaceUnitaryGroup (N : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin N) ℂ) := borel _

/-- The σ-algebra on `U(N)` is Borel, definitionally. -/
instance instBorelSpaceUnitaryGroup (N : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin N) ℂ) := ⟨rfl⟩

/-! ### The Haar probability measure on `U(N)` -/

/-- **The Haar probability measure on `U(N)`**: Mathlib's `haarMeasure` normalized on
the positive compact `⊤` (the whole group — nonempty with nonempty interior, compact by
`instCompactSpaceUnitaryGroup`). Same pattern as `AddCircle.haarAddCircle`. -/
noncomputable def haarUnitary (N : ℕ) : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
  haarMeasure ⊤

/-- `haarUnitary N` is a Haar measure: left-invariant, finite on compacts, positive on
open sets. -/
instance instIsHaarMeasureHaarUnitary (N : ℕ) : IsHaarMeasure (haarUnitary N) :=
  isHaarMeasure_haarMeasure ⊤

/-- `haarUnitary N` is a probability measure: `haarMeasure ⊤` assigns mass `1` to the
normalizing compact `⊤`, whose carrier is the whole group. -/
instance instIsProbabilityMeasureHaarUnitary (N : ℕ) :
    IsProbabilityMeasure (haarUnitary N) :=
  ⟨haarMeasure_self⟩

/-- **Compact groups are unimodular**: `haarUnitary N` is also right-invariant. The
right-translate `(haarUnitary N).map (· * g)` is again a Haar measure
(`isHaarMeasure_map_mul_right`) and again a probability measure, so it equals
`haarUnitary N` by the uniqueness of Haar probability measures. -/
instance instIsMulRightInvariantHaarUnitary (N : ℕ) :
    IsMulRightInvariant (haarUnitary N) where
  map_mul_right_eq_self g := by
    have : IsProbabilityMeasure ((haarUnitary N).map (· * g)) :=
      isProbabilityMeasure_map (continuous_mul_const g).measurable.aemeasurable
    exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-! ### Integrability of continuous observables -/

/-- Every continuous observable is integrable for `haarUnitary N`: on a compact space a
continuous function automatically has compact support, and the Haar probability measure
is finite. -/
theorem integrable_continuousMap (N : ℕ) (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    Integrable f (haarUnitary N) :=
  f.continuous.integrable_of_hasCompactSupport ((isClosed_tsupport _).isCompact)

/-! ### The Haar expectation -/

/-- **The Haar expectation on `U(N)`**, for every `N`: integration of continuous
observables against the Haar probability measure `haarUnitary N`. This inhabits the
interface `HaarExpectation N`, turning every theorem conditional on a Haar expectation
into an unconditional statement about genuine Haar integrals.

* linearity: `integral_add` (with `integrable_continuousMap`) and `integral_smul`;
* normalization: `integral_const` plus `μ univ = 1`;
* left/right invariance: `integral_mul_left_eq_self` / `integral_mul_right_eq_self`,
  the latter through the unimodularity instance
  `instIsMulRightInvariantHaarUnitary`. -/
noncomputable def haarExpectation (N : ℕ) : HaarExpectation N where
  toFun :=
    { toFun := fun f => ∫ U, f U ∂haarUnitary N
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap N f) (integrable_continuousMap N g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c fun U => f U }
  normalized := by
    show (∫ U, (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) U ∂haarUnitary N) = 1
    simp only [ContinuousMap.one_apply, integral_const, probReal_univ, one_smul]
  left_invariant g f := by
    show (∫ U, (f.comp (ContinuousMap.mulLeft g)) U ∂haarUnitary N)
        = ∫ U, f U ∂haarUnitary N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulLeft]
    exact integral_mul_left_eq_self (μ := haarUnitary N) (fun U => f U) g
  right_invariant g f := by
    show (∫ U, (f.comp (ContinuousMap.mulRight g)) U ∂haarUnitary N)
        = ∫ U, f U ∂haarUnitary N
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mulRight]
    exact integral_mul_right_eq_self (μ := haarUnitary N) (fun U => f U) g

/-! ### The payoff: the interface is inhabited for every `N`

Each conditional bridge theorem of `Weingarten.Haar.MatrixEntryIntegrals`
now holds unconditionally for the genuine Haar integral. -/

/-- The interface `HaarExpectation N` is inhabited for **all** `N` — the inhabitation
question is closed by the honest Haar measure, not just the `N = 0` degenerate
witness. -/
example (N : ℕ) : Nonempty (HaarExpectation N) := ⟨haarExpectation N⟩

/-- The genuine Haar integral of the trace over `U(3)` vanishes. -/
example : haarExpectation 3 (traceObs 3) = 0 :=
  (haarExpectation 3).integral_trace

/-- The genuine Haar second moment of the trace over `U(3)` is `1`. -/
example : haarExpectation 3 (traceObs 3 * star (traceObs 3)) = 1 :=
  (haarExpectation 3).integral_trace_mul_star_trace

/-- The genuine Haar integral of `|U_{ij}|²` is `1/N`, for every `N` and every
entry. -/
example (N : ℕ) (i j : Fin N) :
    haarExpectation N (entryObs N i j * star (entryObs N i j)) = (N : ℂ)⁻¹ :=
  (haarExpectation N).integral_normSq_entry i j

/-- The trace-pairing contraction formula holds unconditionally under the genuine Haar
integral: `E (Tr(A U) · Tr(B U*)) = N⁻¹ · Tr(A B)`. -/
example (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    haarExpectation N (traceMulObs N A * traceMulStarObs N B)
      = (N : ℂ)⁻¹ * (A * B).trace :=
  (haarExpectation N).integral_trace_mul_trace_star A B

end Weingarten.Haar
