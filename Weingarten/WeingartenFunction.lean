/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.L1Norm

/-!
# The Weingarten element and the Weingarten function

Proved and elaborated (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`).
Blueprint: `def:wgElement`, `def:wg`, `thm:gram_mul`.

In the stable range `n - 1 < N` (every integer `N ≥ n` qualifies) the Weingarten
element is the inverse of the Gram element, and `wg σ` is its `σ`-coefficient. All
downstream statements quantify over real `N` with this hypothesis — strictly more
general than the integer statements of the companion note, at no extra proof cost.

Precision note: `wg` is the stable-range *inverse*; in that range it coincides with
the Moore–Penrose pseudo-inverse of the general Collins–Śniady theory
(arXiv:math-ph/0402073, Prop. 2.5 / eq. (13)), but the general-`N` pseudo-inverse is a
different object, handled below threshold via the Penrose-pair characterization in
`Weingarten.BelowThreshold`. Downstream descriptions should not call `wg` "the
pseudo-inverse" without the range hypothesis.
-/

namespace Weingarten

/-- The Weingarten element `(gram ℝ n N)⁻¹`. Blueprint: `def:wgElement`. -/
noncomputable def wgElement (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) : SymAlg ℝ n :=
  ↑(isUnit_gram n N hN).unit⁻¹

/-- The Weingarten function: the `σ`-coefficient of the Weingarten element.
Blueprint: `def:wg`. -/
noncomputable def wg (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  wgElement n N hN σ

/-- Blueprint: `thm:gram_mul`. -/
theorem gram_mul_wgElement (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    gram ℝ n N * wgElement n N hN = 1 := by
  rw [wgElement]; exact (isUnit_gram n N hN).mul_val_inv

/-- Blueprint: `thm:gram_mul`. -/
theorem wgElement_mul_gram (n : ℕ) (N : ℝ) (hN : (n : ℝ) - 1 < N) :
    wgElement n N hN * gram ℝ n N = 1 := by
  rw [wgElement]; exact (isUnit_gram n N hN).val_inv_mul

end Weingarten
