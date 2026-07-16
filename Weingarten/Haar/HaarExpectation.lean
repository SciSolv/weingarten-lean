/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.Instances.Matrix

/-!
# The abstract Haar expectation on `U(N)`: a Haar state on `C(U(N))`

`Weingarten.Haar.HaarExpectation N` bundles a ℂ-linear functional `E` on **continuous**
observables `C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)` together with

* **normalization**: `E 1 = 1`, and
* **bi-invariance**: `E (f ∘ (g * ·)) = E f = E (f ∘ (· * g))` for every fixed
  unitary `g`, stated as composition with the continuous translation maps
  `ContinuousMap.mulLeft g` / `ContinuousMap.mulRight g`.

## Provenance (PDF-verified citations)

The functional formulation follows Banica–Collins, *Integration over compact quantum
groups*, arXiv:math/0511253, Def. 4.1 (PDF-verified): the Haar state is the bi-invariant
unital linear functional **on the function algebra `C(G)`** of the (quantum) group,
whose existence is Woronowicz's theorem. It matches the usage in Collins–Śniady,
*Integration with respect to the Haar measure on unitary, orthogonal and symplectic
group*, arXiv:math-ph/0402073, Prop. 2.2 (PDF-verified), whose proof consumes only the
left- and right-invariance of a probability measure — precisely the fields recorded
here.

## Why continuous functions (design decision, recorded for reviewers)

An earlier iteration of this interface took the linear functional on **all** functions
`Matrix.unitaryGroup (Fin N) ℂ → ℂ`. That version is **provably uninhabited** for every
`N ≥ 1`, so all theorems assuming it were vacuously true. The inconsistency proof: pick
`g` of infinite order (e.g. the scalar unitary `exp(2π√2·i)`, infinite order because
`√2` is irrational) and use choice to select an integer orbit-position observable
`ind : U(N) → ℤ` along the free ⟨g⟩-orbits; then `ind (g·U) = ind U + 1` pointwise, so
`U ↦ -ind U` exhibits the constant `1` as the coboundary `f - f ∘ (g * ·)`, which any
linear left-invariant functional annihilates — contradicting `E 1 = 1`. Restricting the
domain to `C(G)` — which is literally the Banica–Collins Def. 4.1 design — kills the
paradox: the choice-built orbit-position observable is not continuous (it cannot be —
otherwise the coboundary argument would contradict the existence of the genuine Haar
integral, which *is* linear, normalized and bi-invariant on `C(G)`); the transplanted
inconsistency proof fails to elaborate at exactly the step that feeds the coboundary
observable to the functional. `haarExpectationZero` below is the
degenerate-case inhabitation witness; the honest `U(N)` Haar measure discharges the
hypothesis for all `N` (`haarExpectation` in `HaarConstruction`).

The topological prerequisites are by instance resolution:
`Matrix.unitaryGroup n α` is an abbreviation for `unitary (Matrix n n α)`,
`Mathlib.Topology.Algebra.Star.Unitary` makes `unitary R` a topological group whenever
`R` is a topological star monoid, and `Mathlib.Topology.Instances.Matrix` provides the
(T2) topological star-ring structure on matrices over `ℂ`.

## Design notes

* **Positivity is deliberately omitted.** None of the first-tier bridge theorems in
  `Weingarten.Haar.MatrixEntryIntegrals` need it: the `n = 1` matrix-entry
  integrals, the trace integrals, and the shared-link contraction follow from linearity,
  normalization, and bi-invariance alone.
* The purpose of the abstraction is to prove the Haar–Weingarten bridge *conditionally*
  on such a functional. The measure-theoretic construction — integration against
  Mathlib's `haarMeasure` on the compact group `Matrix.unitaryGroup (Fin N) ℂ` —
  discharges the hypothesis in `HaarConstruction`; nothing in this tier depends on
  measure theory.
* The **charge lemma** `integral_eq_zero_of_charge` (with the scalar unitaries
  `scalarUnitary`) and the **sign-trick lemmas** `integral_eq_zero_of_neg_comp` /
  `integral_eq_zero_of_neg_comp_right` are the single citation point for the
  Collins–Śniady arXiv:math-ph/0402073 eq. (12) phase argument (PDF-verified).
-/

namespace Weingarten.Haar

/-- An abstract **Haar expectation** on the unitary group `U(N)`: a ℂ-linear functional
on the algebra of continuous observables `C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)` that is
normalized and invariant under left and right translation.

Every Haar state in the sense of Banica–Collins, arXiv:math/0511253, Def. 4.1
(PDF-verified) — a bi-invariant unital linear functional on the function algebra
`C(G)` — yields such a functional when specialized to the classical group `U(N)`;
the three fields are exactly the hypotheses consumed by the moment computations of
Collins–Śniady, arXiv:math-ph/0402073, Prop. 2.2 (PDF-verified). Positivity is
deliberately omitted, and the domain is `C(G, ℂ)` rather than all functions: the
all-functions variant is provably uninhabited — see the module docstring. -/
structure HaarExpectation (N : ℕ) where
  /-- The underlying ℂ-linear expectation functional on continuous observables. -/
  toFun : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) →ₗ[ℂ] ℂ
  /-- The expectation of the constant observable `1` is `1` (Haar is a probability). -/
  normalized : toFun 1 = 1
  /-- Invariance under left translation `U ↦ g * U` by any fixed unitary `g`. -/
  left_invariant : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulLeft g)) = toFun f
  /-- Invariance under right translation `U ↦ U * g` by any fixed unitary `g`. -/
  right_invariant : ∀ (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)),
    toFun (f.comp (ContinuousMap.mulRight g)) = toFun f

/-! ### Scalar unitaries

The central elements `z • 1` for `z` on the unit circle. Translation by them rescales
polynomial observables by a phase, which is what the charge lemma below consumes. -/

/-- The scalar matrix `z • 1` as an element of the unitary group, for `z` on the unit
circle (`z * star z = 1`). These are central, and left translation by them multiplies
each matrix entry by `z` — the "phase" elements of the Collins–Śniady
arXiv:math-ph/0402073 eq. (12) argument. -/
noncomputable def scalarUnitary (N : ℕ) (z : ℂ) (hz : z * star z = 1) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨z • (1 : Matrix (Fin N) (Fin N) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul,
      Matrix.mul_smul, one_mul, smul_smul, hz, one_smul]⟩

@[simp] theorem scalarUnitary_val (N : ℕ) (z : ℂ) (hz : z * star z = 1) :
    (scalarUnitary N z hz).1 = z • (1 : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- Left multiplication by `scalarUnitary N z hz` rescales the whole matrix by `z`. -/
theorem scalarUnitary_mul_val {N : ℕ} (z : ℂ) (hz : z * star z = 1)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (scalarUnitary N z hz * U).1 = z • U.1 := by
  rw [Matrix.UnitaryGroup.mul_val, scalarUnitary_val, Matrix.smul_mul, one_mul]

namespace HaarExpectation

variable {N : ℕ}

noncomputable instance instFunLike :
    FunLike (HaarExpectation N) C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) ℂ where
  coe E := E.toFun
  coe_injective := fun E F h => by
    obtain ⟨tE, nE, lE, rE⟩ := E
    obtain ⟨tF, nF, lF, rF⟩ := F
    obtain rfl : tE = tF := DFunLike.coe_injective h
    rfl

/-- Applying the bundled `LinearMap` agrees with the `FunLike` coercion. -/
theorem toFun_apply (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E.toFun f = E f := rfl

/-- Normalization, restated through the coercion: `E 1 = 1`. -/
@[simp] theorem map_one (E : HaarExpectation N) :
    E (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) = 1 :=
  E.normalized

/-- Left invariance, restated through the coercion. -/
theorem map_left_mul (E : HaarExpectation N) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (f.comp (ContinuousMap.mulLeft g)) = E f :=
  E.left_invariant g f

/-- Right invariance, restated through the coercion. -/
theorem map_right_mul (E : HaarExpectation N) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (f.comp (ContinuousMap.mulRight g)) = E f :=
  E.right_invariant g f

/-- A Haar expectation is additive. -/
protected theorem map_add (E : HaarExpectation N)
    (f g : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (f + g) = E f + E g :=
  E.toFun.map_add f g

/-- A Haar expectation preserves negation. -/
protected theorem map_neg (E : HaarExpectation N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (-f) = -(E f) :=
  E.toFun.map_neg f

/-- Scalars pull out of a Haar expectation. -/
protected theorem map_smul (E : HaarExpectation N) (c : ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) : E (c • f) = c * E f :=
  E.toFun.map_smul c f

/-- A Haar expectation commutes with finite sums of observables. -/
protected theorem map_sum (E : HaarExpectation N) {ι : Type*} (s : Finset ι)
    (f : ι → C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (∑ x ∈ s, f x) = ∑ x ∈ s, E (f x) := by
  exact map_sum E.toFun f s

/-- The expectation of a constant observable is that constant
(from `normalized` plus linearity). -/
@[simp] protected theorem map_const (E : HaarExpectation N) (c : ℂ) :
    E (ContinuousMap.const (Matrix.unitaryGroup (Fin N) ℂ) c) = c := by
  have h : ContinuousMap.const (Matrix.unitaryGroup (Fin N) ℂ) c
      = c • (1 : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) := by
    ext U; simp
  rw [h, E.map_smul, E.map_one, mul_one]

/-- **The linearity workhorse**: a Haar expectation commutes with finite weighted sums
of observables, `E (∑ x ∈ s, c x • f x) = ∑ x ∈ s, c x * E (f x)`. This is the single
move that pushes `E` through the polynomial expansions of trace observables (the 8-fold
sums at `n = 2` and the β-expansions). -/
protected theorem map_weighted_sum (E : HaarExpectation N) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (∑ x ∈ s, c x • f x) = ∑ x ∈ s, c x * E (f x) := by
  rw [E.map_sum]
  exact Finset.sum_congr rfl fun x _ => E.map_smul (c x) (f x)

/-! ### The charge lemma and the sign trick

These two lemmas are the entire invariance technology consumed downstream, and the
single citation point for the phase argument of Collins–Śniady, arXiv:math-ph/0402073,
eq. (12) (PDF-verified). -/

/-- **The charge lemma** (Collins–Śniady, arXiv:math-ph/0402073, eq. (12) phase
argument, PDF-verified): if left translation by some unitary `g` — e.g. a scalar
unitary `scalarUnitary N z hz` — merely rescales the observable by a factor `w ≠ 1`,
then its expectation vanishes. Proof: `E f = E (w • f) = w * E f`. -/
theorem integral_eq_zero_of_charge (E : HaarExpectation N)
    {g : Matrix.unitaryGroup (Fin N) ℂ} {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    {w : ℂ} (hw : w ≠ 1) (h : f.comp (ContinuousMap.mulLeft g) = w • f) : E f = 0 := by
  have h1 : E f = w * E f := by
    calc E f = E (f.comp (ContinuousMap.mulLeft g)) := (E.map_left_mul g f).symm
      _ = E (w • f) := by rw [h]
      _ = w * E f := E.map_smul w f
  have h2 : (w - 1) * E f = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hw
  · exact h3

/-- **The charge lemma, right-translation version**: if right translation by some
unitary `g` rescales the observable by a factor `w ≠ 1`, then its expectation
vanishes. -/
theorem integral_eq_zero_of_charge_right (E : HaarExpectation N)
    {g : Matrix.unitaryGroup (Fin N) ℂ} {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    {w : ℂ} (hw : w ≠ 1) (h : f.comp (ContinuousMap.mulRight g) = w • f) : E f = 0 := by
  have h1 : E f = w * E f := by
    calc E f = E (f.comp (ContinuousMap.mulRight g)) := (E.map_right_mul g f).symm
      _ = E (w • f) := by rw [h]
      _ = w * E f := E.map_smul w f
  have h2 : (w - 1) * E f = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hw
  · exact h3

/-- **The sign trick** (charge lemma at `w = −1`): if left translation by `g` negates
the observable, its expectation vanishes. -/
theorem integral_eq_zero_of_neg_comp (E : HaarExpectation N)
    {g : Matrix.unitaryGroup (Fin N) ℂ} {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    (h : f.comp (ContinuousMap.mulLeft g) = -f) : E f = 0 :=
  E.integral_eq_zero_of_charge (by norm_num : (-1 : ℂ) ≠ 1)
    (h.trans (neg_one_smul ℂ f).symm)

/-- **The sign trick, right-translation version**: if right translation by `g` negates
the observable, its expectation vanishes. -/
theorem integral_eq_zero_of_neg_comp_right (E : HaarExpectation N)
    {g : Matrix.unitaryGroup (Fin N) ℂ} {f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)}
    (h : f.comp (ContinuousMap.mulRight g) = -f) : E f = 0 :=
  E.integral_eq_zero_of_charge_right (by norm_num : (-1 : ℂ) ≠ 1)
    (h.trans (neg_one_smul ℂ f).symm)

end HaarExpectation

/-! ### Translation as a ⋆-algebra homomorphism

Precomposition with a (continuous) translation map is a ⋆-algebra homomorphism of the
observable algebra `C(U(N), ℂ)`. Bundling it gives `map_mul`/`map_star`/`map_sum` for
free, so translating a *polynomial* observable (products of entries and their stars —
the n = 2 moments, the β-expansions) reduces mechanically to translating its
entry factors. -/

/-- Left translation `f ↦ f ∘ (g * ·)`, as a ⋆-algebra homomorphism of observables. -/
noncomputable def translateLeft (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) →⋆ₐ[ℂ] C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ (ContinuousMap.mulLeft g)

/-- Right translation `f ↦ f ∘ (· * g)`, as a ⋆-algebra homomorphism of observables. -/
noncomputable def translateRight (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) →⋆ₐ[ℂ] C(Matrix.unitaryGroup (Fin N) ℂ, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ (ContinuousMap.mulRight g)

@[simp] theorem translateLeft_apply (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    translateLeft N g f = f.comp (ContinuousMap.mulLeft g) := rfl

@[simp] theorem translateRight_apply (N : ℕ) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    translateRight N g f = f.comp (ContinuousMap.mulRight g) := rfl

/-- Left invariance, phrased through the bundled translation homomorphism. -/
theorem HaarExpectation.map_translateLeft {N : ℕ} (E : HaarExpectation N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (translateLeft N g f) = E f :=
  E.map_left_mul g f

/-- Right invariance, phrased through the bundled translation homomorphism. -/
theorem HaarExpectation.map_translateRight {N : ℕ} (E : HaarExpectation N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E (translateRight N g f) = E f :=
  E.map_right_mul g f

/-! ### Numeral-robust linearity

`ring`-normalized expansions produce `OfNat` numeral multiples `(k : C(U(N),ℂ)) * f`
whose numerals do not unify with `Nat.cast`-stated lemmas (a documented
Nat-cast/OfNat incident). The bridge below states the scalar collapse once at the
`ContinuousMap` level; consumers reach numerals through `Nat.cast_ofNat`. -/

/-- A natural-number multiple of an observable is the scalar multiple:
`(n : C(U(N),ℂ)) * f = (n : ℂ) • f`. -/
theorem natCast_mul_eq_smul {N : ℕ} (n : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (n : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) * f = (n : ℂ) • f := by
  ext U
  simp

/-- **Numeral-robust linearity**: `E (n·f) = n·(E f)` for natural `n` — the public
form of the private `map_{two,three,four,six}_mul` addition-decomposition helpers
of the downstream value proofs. -/
theorem HaarExpectation.map_natCast_mul {N : ℕ} (E : HaarExpectation N) (n : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    E ((n : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) * f) = (n : ℂ) * E f := by
  rw [natCast_mul_eq_smul, E.map_smul]

/-! ### Inhabitation sanity witness -/

/-- **Inhabitation witness** for the interface at `N = 0`: `U(0)` is a one-point group
(the empty matrix), so evaluation at its unique point is a normalized bi-invariant
linear functional on `C(U(0), ℂ)`. This is the degenerate case of the Haar state; its
role here is purely structural — it certifies that `HaarExpectation` is not vacuous by
construction, unlike the all-functions predecessor interface (see the module
docstring). -/
noncomputable def haarExpectationZero : HaarExpectation 0 where
  toFun :=
    { toFun := fun f => f 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  normalized := rfl
  left_invariant g f := by
    have h : g * (1 : Matrix.unitaryGroup (Fin 0) ℂ) = 1 :=
      Matrix.UnitaryGroup.ext _ _ fun i => i.elim0
    exact congrArg f h
  right_invariant g f := by
    have h : (1 : Matrix.unitaryGroup (Fin 0) ℂ) * g = 1 :=
      Matrix.UnitaryGroup.ext _ _ fun i => i.elim0
    exact congrArg f h

/-- The interface is inhabited (at `N = 0`, by evaluation at the unique point). -/
noncomputable example : HaarExpectation 0 := haarExpectationZero

end Weingarten.Haar
