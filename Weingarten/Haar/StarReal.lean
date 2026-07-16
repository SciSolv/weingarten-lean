/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.HaarConstruction

/-!
# Star-reality of the honest Haar expectation

The interface `Weingarten.Haar.HaarExpectation` deliberately omits both positivity and
star-reality (see the design note in `HaarExpectation.lean`). This file records
star-reality as a standalone predicate `HaarExpectation.IsStarReal` and proves it for
the **constructed** Haar expectation — `∫ conj f = conj ∫ f` is a genuine fact about
the Bochner integral (`MeasureTheory.integral_conj`), not derivable from the bare
interface. Import-only extension of the interface.

Consumers instantiate starred moment identities at `haarExpectation N` in one line
instead of re-running mirrored expansions. -/

namespace Weingarten.Haar

open MeasureTheory

/-- A Haar expectation is **star-real** if it intertwines the pointwise star of
observables with complex conjugation of values: `E (star f) = conj (E f)`. True for
any expectation given by integration against a (real, positive) measure; deliberately
not an axiom of the interface. -/
def HaarExpectation.IsStarReal {N : ℕ} (E : HaarExpectation N) : Prop :=
  ∀ f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ), E (star f) = star (E f)

/-- **The honest Haar expectation is star-real**: `∫ conj f dU = conj ∫ f dU`
(`MeasureTheory.integral_conj`). -/
theorem haarExpectation_isStarReal (N : ℕ) : (haarExpectation N).IsStarReal := by
  intro f
  show (∫ U, (star f) U ∂haarUnitary N) = star (∫ U, f U ∂haarUnitary N)
  simp only [ContinuousMap.star_apply, Complex.star_def]
  exact integral_conj

end Weingarten.Haar
