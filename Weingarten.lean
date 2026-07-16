/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.JucysMurphy
import Weingarten.CycleCount
import Weingarten.Gram
import Weingarten.Homs
import Weingarten.BelowThreshold
import Weingarten.L1Norm
import Weingarten.WeingartenFunction
import Weingarten.SumRules
import Weingarten.Parity
import Weingarten.ClosedForm
import Weingarten.Cell23
import Weingarten.Pairings
import Weingarten.OrthogonalGram
import Weingarten.SymplecticGram
import Weingarten.Haar.HaarExpectation
import Weingarten.Haar.MatrixEntryIntegrals
import Weingarten.Haar.EntryIntegralsTwo
import Weingarten.Haar.HaarConstruction
import Weingarten.Haar.SecondCountableShim
import Weingarten.Haar.ConjugationInvariance
import Weingarten.Haar.StarReal
import Weingarten.Haar.PairHaar
import Weingarten.Haar.OneMatrixModel
import Weingarten.Haar.TraceEntryMoments
import Weingarten.Haar.HonestKernel
import Weingarten.Haar.ProductHaar
import Weingarten.Haar.WeingartenValues
import Weingarten.Haar.BridgeSummary

/-!
# Weingarten calculus in the stable range and below — root module

See `blueprint/` for the dependency-graphed plan.

The `Weingarten.Haar` modules provide the **U(N) Haar-integration bridge at the formalized degrees**:
the abstract Haar state on `C(U(N))` with its Mathlib-measure witness, the exact
`n = 1` entry integral, the `n = 2` fourth-moment system, trace-word moments
through total degree 5 with the β-expansion coefficients they determine, the
pair/product Haar layer with the honest tilted measures, and small-`n` values of
`Weingarten.wg` re-derived from the sum rules. The general-`n` Weingarten moment
formula is **not** formalized here.
-/
