/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.HaarConstruction
import Weingarten.Haar.SecondCountableShim
import Weingarten.Haar.PairHaar
import Weingarten.Haar.HonestKernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# The product Haar measure on `U(N)^k` (PH-4, measure tier)

The `k`-copy analogue of `haarUnitary N`: the product measure
`productHaar N k := Measure.pi (fun _ : Fin k => haarUnitary N)` on the finite pi power
`Fin k → U(N)` — the measure that carries the honest tilted measures below
(`gibbsPair` / `chainGibbs`). Per-slot translation invariance, slot marginals, and the
`k = 0` / `k = 1` degenerate identifications are delivered against verified pin
locators. (PH-4..PH-6 continue the law numbering defined in `PairHaar`.)

## Measure-tier-first (recorded design decision)

ProductHaar is delivered **measure-tier-first**: an
interface-iterated PH-4 would require the partial integral to be **continuous in the outer
slot** — a continuity/boundedness axiom the `HaarExpectation` interface deliberately omits
(same refutation class as the all-functions incident recorded in `HaarExpectation`). Any future
Fubini-free peeling wish must FIRST pre-probe a `ContinuousMap.curry` +
bounded-integration route at the pin — the iterated interface is never rebuilt
unprobed.

## Contents

* `productHaar N k`: `Measure.pi` over the constant family `haarUnitary N`, with the
  probability instance (`Constructions/Pi.lean:312`), the open-positivity instance
  (`Pi.lean:609`; each factor is open-positive because `IsHaarMeasure` extends
  `IsOpenPosMeasure`), the product-group left/right translation invariance instances
  (`Pi.lean:567`/`:581` — the right one because compact groups are unimodular
  slotwise), and the Haar-measure instance (`Pi.lean:643`). The Borel/opens-measurable
  synthesis on pi powers of `U(N)` fires through the `SecondCountableShim`; the
  pi-power probes are committed **there**, and the slotwise `MeasurableMul` demand of
  the invariance instances is probed **here**.
* Per-slot invariance `productHaar_map_update_mulLeft` (+ `mulRight` sibling,
  constant-`g` version): updating slot `i` by the left translation `A i ↦ g * A i`
  preserves `productHaar N k`. Route: the update map **is** product-group translation
  by the constant tuple `Function.update 1 i g` (pointwise reading aids
  `update_mulLeft_eq_update_one_mul` / `update_mulRight_eq_mul_update_one`), so
  `map_mul_left_eq_self` / `map_mul_right_eq_self` (`Group/Measure.lean:49`/`:54`)
  close it through the product invariance instances.
* Eval marginals via `measurePreserving_eval` (`Pi.lean:406`): the pushforward of
  `productHaar N k` under evaluation at any slot is `haarUnitary N`
  (`productHaar_eval_marginal`), with the integral corollary
  `productHaar_integral_eval` — `∫ f (A i) ∂productHaar N k = haarExpectation N f`,
  the slot-marginal supply for downstream chain inductions.
* `k = 0` degenerate probes: the empty product is the Dirac mass at the unique empty
  configuration (`productHaar_zero_eq_dirac`, via `Measure.pi_of_empty`,
  `Pi.lean:342`), it is a probability measure (instance probe), and it integrates
  **every** observable — no measurability hypothesis — to its value at the unique
  point (`productHaar_zero_integral`, via `integral_unique`,
  `Integral/Bochner/Basic.lean:1209`).
* `k = 1` agreement via `measurePreserving_piUnique` (`Pi.lean:818`, verified at the
  pin): the evaluation equivalence `(Fin 1 → U(N)) ≃ᵐ U(N)` is measure-preserving
  between `productHaar N 1` and `haarUnitary N`
  (`productHaar_one_piUnique` / `productHaar_one_map_piUnique`).

## Scope

Measure-tier plumbing, plus the PH-5 triangular substitution and the PH-6 honest
tilted measures appended below: no invariant-span scope claims and no gap claims are
made in this file.
-/

namespace Weingarten.Haar

open MeasureTheory MeasureTheory.Measure

/-! ### The product Haar measure and its instances -/

/-- **The product Haar measure on `U(N)^k`** (PH-4, measure tier): the `Measure.pi`
product of `k` copies of the Haar probability measure `haarUnitary N`, on the finite
pi power `Fin k → U(N)`. Delivered measure-tier-first per the recorded design
decision (module docstring). -/
noncomputable def productHaar (N k : ℕ) :
    Measure (Fin k → Matrix.unitaryGroup (Fin N) ℂ) :=
  Measure.pi fun _ : Fin k => haarUnitary N

/-- `productHaar N k` is a probability measure (`pi.instIsProbabilityMeasure`,
`Constructions/Pi.lean:312`, from the slotwise probability instances). -/
instance instIsProbabilityMeasureProductHaar (N k : ℕ) :
    IsProbabilityMeasure (productHaar N k) :=
  inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun _ : Fin k => haarUnitary N))

/-- `productHaar N k` is positive on nonempty open sets (`pi.isOpenPosMeasure`,
`Constructions/Pi.lean:609`; each factor is open-positive because `IsHaarMeasure`
extends `IsOpenPosMeasure`, `Group/Measure.lean:776`). -/
instance instIsOpenPosMeasureProductHaar (N k : ℕ) :
    IsOpenPosMeasure (productHaar N k) :=
  inferInstanceAs
    (IsOpenPosMeasure (Measure.pi fun _ : Fin k => haarUnitary N))

/-- `productHaar N k` is left-invariant for the product group `U(N)^k`
(`pi.isMulLeftInvariant`, `Constructions/Pi.lean:567`; the slotwise `MeasurableMul`
demand fires from continuity of multiplication — probe below). -/
instance instIsMulLeftInvariantProductHaar (N k : ℕ) :
    IsMulLeftInvariant (productHaar N k) :=
  inferInstanceAs
    (IsMulLeftInvariant (Measure.pi fun _ : Fin k => haarUnitary N))

/-- `productHaar N k` is right-invariant for the product group `U(N)^k`
(`pi.isMulRightInvariant`, `Constructions/Pi.lean:581`; each slot is right-invariant
by unimodularity of the compact group `U(N)`,
`instIsMulRightInvariantHaarUnitary`). -/
instance instIsMulRightInvariantProductHaar (N k : ℕ) :
    IsMulRightInvariant (productHaar N k) :=
  inferInstanceAs
    (IsMulRightInvariant (Measure.pi fun _ : Fin k => haarUnitary N))

/-- `productHaar N k` is a Haar measure on the compact product group `U(N)^k`
(`pi.isHaarMeasure`, `Constructions/Pi.lean:643`). -/
instance instIsHaarMeasureProductHaar (N k : ℕ) :
    IsHaarMeasure (productHaar N k) :=
  inferInstanceAs (IsHaarMeasure (Measure.pi fun _ : Fin k => haarUnitary N))

/-- Probe: the slotwise `MeasurableMul` demand of the pi invariance instances fires
from continuity of multiplication (`ContinuousMul.measurableMul`,
`BorelSpace/Basic.lean:522`, through the `SeparatelyContinuousMul` bridge). The
pi-power Borel/opens-measurable probes are committed in the `SecondCountableShim`. -/
example (N : ℕ) : MeasurableMul (Matrix.unitaryGroup (Fin N) ℂ) := inferInstance

/-! ### Per-slot invariance (constant-`g` version)

Updating slot `i` by a fixed translation is not a new kind of symmetry: it **is**
translation by a constant tuple in the product group `U(N)^k`, namely by
`Function.update 1 i g` (identity in every slot except `i`). The two pointwise
reading aids record this, and the invariance instances above then close the gate. -/

/-- **Per-slot left update as a product-group translation, pointwise**: updating
slot `i` of `A` to `g * A i` is left multiplication of `A` by the constant tuple
`Function.update 1 i g`. -/
theorem update_mulLeft_eq_update_one_mul {N k : ℕ} (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ) (A : Fin k → Matrix.unitaryGroup (Fin N) ℂ) :
    Function.update A i (g * A i)
      = Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g * A := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- **Per-slot right update as a product-group translation, pointwise**: updating
slot `i` of `A` to `A i * g` is right multiplication of `A` by the constant tuple
`Function.update 1 i g`. -/
theorem update_mulRight_eq_mul_update_one {N k : ℕ} (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ) (A : Fin k → Matrix.unitaryGroup (Fin N) ℂ) :
    Function.update A i (A i * g)
      = A * Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [Function.update_of_ne hj]

/-- **Per-slot left invariance of product Haar** (constant-`g` version):
pushing `productHaar N k` forward by the map that updates slot `i` with left
multiplication by a fixed `g` gives back `productHaar N k`. The update map is the
product-group translation by `Function.update 1 i g`
(`update_mulLeft_eq_update_one_mul`), so left invariance of the product measure
(`map_mul_left_eq_self`, `Group/Measure.lean:49`) closes it. This is the
per-slot plumbing: changing one coordinate by a fixed left translation
leaves the product Haar measure invariant. -/
theorem productHaar_map_update_mulLeft (N k : ℕ) (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (productHaar N k).map (fun A => Function.update A i (g * A i))
      = productHaar N k := by
  have h : (fun A : Fin k → Matrix.unitaryGroup (Fin N) ℂ =>
        Function.update A i (g * A i))
      = (Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g * ·) :=
    funext fun A => update_mulLeft_eq_update_one_mul i g A
  rw [h]
  exact map_mul_left_eq_self (productHaar N k)
    (Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g)

/-- **Per-slot right invariance of product Haar** (the cheap `mulRight` sibling):
pushing `productHaar N k` forward by the map that updates slot `i` with right
multiplication by a fixed `g` gives back `productHaar N k` — compact groups are
unimodular slotwise, so the right sibling costs one line more than the left
(`update_mulRight_eq_mul_update_one` + `map_mul_right_eq_self`,
`Group/Measure.lean:54`). -/
theorem productHaar_map_update_mulRight (N k : ℕ) (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ) :
    (productHaar N k).map (fun A => Function.update A i (A i * g))
      = productHaar N k := by
  have h : (fun A : Fin k → Matrix.unitaryGroup (Fin N) ℂ =>
        Function.update A i (A i * g))
      = (· * Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g) :=
    funext fun A => update_mulRight_eq_mul_update_one i g A
  rw [h]
  exact map_mul_right_eq_self (productHaar N k)
    (Function.update (1 : Fin k → Matrix.unitaryGroup (Fin N) ℂ) i g)

/-! ### Eval marginals -/

/-- Evaluation at slot `i` is measure-preserving from `productHaar N k` to
`haarUnitary N` (`measurePreserving_eval`, `Constructions/Pi.lean:406`, from the
slotwise probability instances). -/
theorem measurePreserving_eval_productHaar (N k : ℕ) (i : Fin k) :
    MeasurePreserving (Function.eval i) (productHaar N k) (haarUnitary N) :=
  measurePreserving_eval (fun _ : Fin k => haarUnitary N) i

/-- **Eval marginal of product Haar**: the pushforward of
`productHaar N k` under evaluation at any slot `i` is the one-variable Haar
probability measure `haarUnitary N`. -/
theorem productHaar_eval_marginal (N k : ℕ) (i : Fin k) :
    (productHaar N k).map (Function.eval i) = haarUnitary N :=
  (measurePreserving_eval_productHaar N k i).map_eq

/-- **Integral form of the eval marginal**: on continuous observables of one slot
only, the product-Haar integral is the honest one-variable Haar expectation — the
slot-marginal supply for downstream chain inductions. Verified pushforward route:
`integral_map` + `measurable_pi_apply` + `Continuous.aestronglyMeasurable`. -/
theorem productHaar_integral_eval (N k : ℕ) (i : Fin k)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, f (A i) ∂productHaar N k) = haarExpectation N f := by
  show (∫ A, f (A i) ∂productHaar N k) = ∫ U, f U ∂haarUnitary N
  calc (∫ A, f (A i) ∂productHaar N k)
      = ∫ U, f U ∂((productHaar N k).map (Function.eval i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable
          f.continuous.aestronglyMeasurable).symm
    _ = ∫ U, f U ∂haarUnitary N := by rw [productHaar_eval_marginal]

/-! ### The `k = 0` degenerate probes

The empty product is the Dirac mass at the unique empty configuration: a
probability measure that integrates **every** observable — no measurability
hypothesis — to its value at the unique point. -/

/-- **`k = 0`: the empty product is a Dirac mass** at the unique (empty)
configuration (`Measure.pi_of_empty`, `Constructions/Pi.lean:342`). -/
theorem productHaar_zero_eq_dirac (N : ℕ) :
    productHaar N 0
      = Measure.dirac (default : Fin 0 → Matrix.unitaryGroup (Fin N) ℂ) :=
  Measure.pi_of_empty (fun _ : Fin 0 => haarUnitary N) default

/-- **`k = 0`: integration is evaluation at the unique point**, for *every*
observable — `integral_unique` (`Integral/Bochner/Basic.lean:1209`) plus the
probability instance; no measurability hypothesis on `f` is needed. -/
theorem productHaar_zero_integral (N : ℕ)
    (f : (Fin 0 → Matrix.unitaryGroup (Fin N) ℂ) → ℂ) :
    (∫ A, f A ∂productHaar N 0) = f default := by
  rw [integral_unique, probReal_univ, one_smul]
  -- the two `default`s arrive through different (propositionally equal) instance
  -- paths; the configuration space at `k = 0` is a subsingleton
  exact congrArg f (Subsingleton.elim _ _)

/-- Probe: the probability instance survives the `k = 0` degeneracy. -/
example (N : ℕ) : IsProbabilityMeasure (productHaar N 0) := inferInstance

/-! ### The `k = 1` agreement

`measurePreserving_piUnique` (`Constructions/Pi.lean:818`, verified at the pin): the
evaluation equivalence `(Fin 1 → U(N)) ≃ᵐ U(N)` identifies `productHaar N 1` with
`haarUnitary N` — the one-copy product theory *is* the one-variable theory. -/

/-- The forward map of the `k = 1` evaluation equivalence is evaluation at the
unique slot. -/
theorem piUnique_apply_default (N : ℕ)
    (A : Fin 1 → Matrix.unitaryGroup (Fin N) ℂ) :
    (MeasurableEquiv.piUnique fun _ : Fin 1 => Matrix.unitaryGroup (Fin N) ℂ) A
      = A default := rfl

/-- **`k = 1` agreement** (via `measurePreserving_piUnique`, `Pi.lean:818`): the
evaluation equivalence `(Fin 1 → U(N)) ≃ᵐ U(N)` is measure-preserving from
`productHaar N 1` to `haarUnitary N`. -/
theorem productHaar_one_piUnique (N : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piUnique fun _ : Fin 1 => Matrix.unitaryGroup (Fin N) ℂ)
      (productHaar N 1) (haarUnitary N) :=
  measurePreserving_piUnique fun _ : Fin 1 => haarUnitary N

/-- **`k = 1` agreement, map form**: the pushforward of `productHaar N 1` under the
evaluation equivalence is `haarUnitary N`. -/
theorem productHaar_one_map_piUnique (N : ℕ) :
    (productHaar N 1).map
      (MeasurableEquiv.piUnique fun _ : Fin 1 => Matrix.unitaryGroup (Fin N) ℂ)
      = haarUnitary N :=
  (productHaar_one_piUnique N).map_eq

/-- Probe: the inverse direction — the constant-tuple embedding `U(N) → (Fin 1 →
U(N))` pushes `haarUnitary N` to `productHaar N 1`. -/
example (N : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piUnique
        fun _ : Fin 1 => Matrix.unitaryGroup (Fin N) ℂ).symm
      (haarUnitary N) (productHaar N 1) :=
  (productHaar_one_piUnique N).symm _

/-! ### Payoff probes -/

/-- The genuine product-Haar integral of the trace at any single slot vanishes —
the one-variable moment reached through the eval marginal, at every `k` and
every slot. -/
example (N k : ℕ) (i : Fin k) :
    (∫ A, traceObs N (A i) ∂productHaar N k) = 0 :=
  (productHaar_integral_eval N k i (traceObs N)).trans
    (haarExpectation N).integral_trace

/-- The `k = 1` slot marginal agrees with the honest Haar expectation on every
observable — the degenerate consistency of the two routes. -/
example (N : ℕ) (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, f (A default) ∂productHaar N 1) = haarExpectation N f :=
  productHaar_integral_eval N 1 default f

/-! ## PH-5 (triangular substitution) and PH-6 (honest tilted measures)

Contents:

* **PH-5** `productE_update_mulLeft` / `productE_update_mulRight`: the
  interface/integral-level **triangular substitution** — updating one designated slot
  by a translation that depends only on the *other* slots leaves the product-Haar
  integral of every continuous observable unchanged — together with the constant-`g`
  integral forms (`…_const`), the `integral_map` + measure-lemma route the design
  instructed to probe first. In the development in which this layer originated,
  PH-5 fed the plaquette change of variables.
* **PH-6** `gibbsPair` / `chainGibbs`: the **honest (untruncated,
  normalized) tilted measures**, packaged via `Measure.tilted`
  (`Measure/Tilted.lean:42`), with `IsProbabilityMeasure` instances by
  `isProbabilityMeasure_tilted` (`:126`) and the `integral_tilted` transfer formula
  (`:230`) — the measures a chain correlator integrates against.

No gap claims and no invariant-span scope claims are made in this file, and no
lattice-gauge-theory claim is made in this repository; β is in Chatterjee units
(arXiv:1803.01950, eq. (3.2)), matching `HonestKernel`. -/

/-! ### PH-5, constant-`g` tier: the integral forms of the measure lemmas

The recorded design instruction is to
probe the change-of-variables route FIRST: with the measure-level
`productHaar_map_update_mulLeft` in hand, the constant-`g` integral invariance is
exactly `integral_map` + measurability of the update map. Both constant forms are
committed here as the probed route; the full function-`g` triangular substitution
follows below. -/

/-- **Constant-`g` integral form of per-slot left invariance**: updating slot `i` by a
fixed left translation leaves the product-Haar integral of every continuous observable
unchanged. Route (probed FIRST): `integral_map` +
continuity/measurability of the update map (`Continuous.update`,
`Topology/Constructions.lean:920`) + the measure-level lemma
`productHaar_map_update_mulLeft`. -/
theorem productE_update_mulLeft_const (N k : ℕ) (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (F : C(Fin k → Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, F (Function.update A i (g * A i)) ∂productHaar N k)
      = ∫ A, F A ∂productHaar N k := by
  have hT : Measurable (fun A : Fin k → Matrix.unitaryGroup (Fin N) ℂ =>
      Function.update A i (g * A i)) :=
    (continuous_id.update i (continuous_const.mul (continuous_apply i))).measurable
  calc (∫ A, F (Function.update A i (g * A i)) ∂productHaar N k)
      = ∫ B, F B ∂((productHaar N k).map
          (fun A => Function.update A i (g * A i))) :=
        (integral_map hT.aemeasurable F.continuous.aestronglyMeasurable).symm
    _ = ∫ A, F A ∂productHaar N k := by rw [productHaar_map_update_mulLeft]

/-- **Constant-`g` integral form of per-slot right invariance** — the `mulRight`
sibling of `productE_update_mulLeft_const`, through
`productHaar_map_update_mulRight`. -/
theorem productE_update_mulRight_const (N k : ℕ) (i : Fin k)
    (g : Matrix.unitaryGroup (Fin N) ℂ)
    (F : C(Fin k → Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, F (Function.update A i (A i * g)) ∂productHaar N k)
      = ∫ A, F A ∂productHaar N k := by
  have hT : Measurable (fun A : Fin k → Matrix.unitaryGroup (Fin N) ℂ =>
      Function.update A i (A i * g)) :=
    (continuous_id.update i ((continuous_apply i).mul continuous_const)).measurable
  calc (∫ A, F (Function.update A i (A i * g)) ∂productHaar N k)
      = ∫ B, F B ∂((productHaar N k).map
          (fun A => Function.update A i (A i * g))) :=
        (integral_map hT.aemeasurable F.continuous.aestronglyMeasurable).symm
    _ = ∫ A, F A ∂productHaar N k := by rw [productHaar_map_update_mulRight]

/-! ### PH-5: the triangular substitution -/

/-- **PH-5: the triangular substitution**: for a designated slot `i` and a
continuous `g` that depends only on the *other* slots (hypothesis `hgi`), updating
slot `i` by the configuration-dependent left translation `A i ↦ g A * A i` leaves the
product-Haar integral of every continuous observable unchanged.

**Pitfall (recorded design ruling, PH-5, quoted verbatim):** "invariance by a
*function of the other slots* is NOT an interface field and must not become one — it
is a theorem of the iterated construction. This is the single lemma that makes the S2
change of variables a finite induction."

In the measure-tier-first delivery (module docstring) the "iterated construction"
reading is realized measure-theoretically: split off slot `i` with the
measure-preserving `MeasurableEquiv.piFinSuccAbove` (`Constructions/Pi.lean:801`),
apply Fubini in the symmetric order (`integral_prod_symm`, `Integral/Prod.lean:516`),
and at each fixed value of the other slots the inner one-variable integral is
invariant under the *now-constant* translation (`integral_mul_left_eq_self`) because
`g` cannot see slot `i`; `Fin.update_insertNth` (`Data/Fin/Tuple/Basic.lean:1028`) is
the exact update/insert interchange. In the originating development this is the
lemma that made the plaquette change of variables a finite induction. -/
theorem productE_update_mulLeft (N k : ℕ) (i : Fin k)
    (g : (Fin k → Matrix.unitaryGroup (Fin N) ℂ) → Matrix.unitaryGroup (Fin N) ℂ)
    (hg : Continuous g)
    (hgi : ∀ (A : Fin k → Matrix.unitaryGroup (Fin N) ℂ)
      (x : Matrix.unitaryGroup (Fin N) ℂ), g (Function.update A i x) = g A)
    (F : C(Fin k → Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, F (Function.update A i (g A * A i)) ∂productHaar N k)
      = ∫ A, F A ∂productHaar N k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  -- the slot-`i` split: `piFinSuccAbove` is measure-preserving from `productHaar`
  -- to `haarUnitary ⊗ productHaar-on-the-rest`
  have hMP : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i)
      (productHaar N (n + 1))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => haarUnitary N) i
  -- transport of arbitrary integrals along the split (hypothesis-free:
  -- `integral_map_equiv`)
  have hkey : ∀ Φ : (Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) → ℂ,
      (∫ A, Φ A ∂productHaar N (n + 1))
        = ∫ p, Φ ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
            ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    intro Φ
    conv_lhs => rw [← (hMP.symm _).map_eq]
    exact integral_map_equiv _ Φ
  -- transport of integrability along the split
  have hFint : ∀ Φ : (Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) → ℂ,
      Integrable Φ (productHaar N (n + 1)) →
      Integrable (fun p => Φ ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p))
        ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    intro Φ hΦ
    exact (integrable_map_equiv _ Φ).mp (by rw [(hMP.symm _).map_eq]; exact hΦ)
  -- integrability of the two continuous integrands on the pi space
  have hΦ1 : Integrable (fun A : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ =>
      F (Function.update A i (g A * A i))) (productHaar N (n + 1)) :=
    (F.continuous.comp
        (continuous_id.update i (hg.mul (continuous_apply i)))).integrable_of_hasCompactSupport
      ((isClosed_tsupport _).isCompact)
  have hΦ2 : Integrable (fun A : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ => F A)
      (productHaar N (n + 1)) :=
    F.continuous.integrable_of_hasCompactSupport ((isClosed_tsupport _).isCompact)
  -- the slot-`i` reading of the two integrands: `e.symm (x, y) = i.insertNth x y`,
  -- the update/insert interchange, and independence of `g` from slot `i`
  have hleft : (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F (Function.update ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
          (g ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
            * ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i)))
      = fun p => F (i.insertNth (g (i.insertNth 1 p.2) * p.1) p.2) := by
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_apply_same]
    have hgy : g (i.insertNth p.1 p.2) = g (i.insertNth 1 p.2) := by
      rw [← Fin.update_insertNth (α := fun _ : Fin (n + 1) =>
        Matrix.unitaryGroup (Fin N) ℂ) i p.1 1 p.2, hgi]
    rw [hgy, Fin.update_insertNth]
  have hright : (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p))
      = fun p => F (i.insertNth p.1 p.2) := by
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
  -- integrability of the two integrands on the split product space
  have hint1 : Integrable (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F (i.insertNth (g (i.insertNth 1 p.2) * p.1) p.2))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    rw [← hleft]
    exact hFint _ hΦ1
  have hint2 : Integrable (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) => F (i.insertNth p.1 p.2))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    rw [← hright]
    exact hFint _ hΦ2
  -- split, Fubini (symmetric order), one-variable left invariance at fixed outer
  -- values, and reassemble
  calc (∫ A, F (Function.update A i (g A * A i)) ∂productHaar N (n + 1))
      = ∫ p, F (Function.update ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
          (g ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
            * ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i))
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
        hkey _
    _ = ∫ p, F (i.insertNth (g (i.insertNth 1 p.2) * p.1) p.2)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
        rw [hleft]
    _ = ∫ y, (∫ x, F (i.insertNth (g (i.insertNth 1 y) * x) y) ∂haarUnitary N)
          ∂(Measure.pi fun _ : Fin n => haarUnitary N) :=
        integral_prod_symm _ hint1
    _ = ∫ y, (∫ x, F (i.insertNth x y) ∂haarUnitary N)
          ∂(Measure.pi fun _ : Fin n => haarUnitary N) :=
        integral_congr_ae (ae_of_all _ fun y =>
          integral_mul_left_eq_self (μ := haarUnitary N)
            (fun x => F (i.insertNth x y)) (g (i.insertNth 1 y)))
    _ = ∫ p, F (i.insertNth p.1 p.2)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
        (integral_prod_symm _ hint2).symm
    _ = ∫ p, F ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
        rw [hright]
    _ = ∫ A, F A ∂productHaar N (n + 1) := (hkey _).symm

/-- **PH-5, the `mulRight` sibling**: updating slot `i` by the configuration-dependent
right translation `A i ↦ A i * g A`, with `g` depending only on the other slots,
leaves the product-Haar integral of every continuous observable unchanged. Same
mechanism as `productE_update_mulLeft` (whose docstring carries the blueprint's
verbatim pitfall note), with `integral_mul_right_eq_self` in the inner slot — compact
groups are unimodular slotwise. -/
theorem productE_update_mulRight (N k : ℕ) (i : Fin k)
    (g : (Fin k → Matrix.unitaryGroup (Fin N) ℂ) → Matrix.unitaryGroup (Fin N) ℂ)
    (hg : Continuous g)
    (hgi : ∀ (A : Fin k → Matrix.unitaryGroup (Fin N) ℂ)
      (x : Matrix.unitaryGroup (Fin N) ℂ), g (Function.update A i x) = g A)
    (F : C(Fin k → Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, F (Function.update A i (A i * g A)) ∂productHaar N k)
      = ∫ A, F A ∂productHaar N k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  have hMP : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i)
      (productHaar N (n + 1))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => haarUnitary N) i
  have hkey : ∀ Φ : (Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) → ℂ,
      (∫ A, Φ A ∂productHaar N (n + 1))
        = ∫ p, Φ ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
            ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    intro Φ
    conv_lhs => rw [← (hMP.symm _).map_eq]
    exact integral_map_equiv _ Φ
  have hFint : ∀ Φ : (Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) → ℂ,
      Integrable Φ (productHaar N (n + 1)) →
      Integrable (fun p => Φ ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p))
        ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    intro Φ hΦ
    exact (integrable_map_equiv _ Φ).mp (by rw [(hMP.symm _).map_eq]; exact hΦ)
  have hΦ1 : Integrable (fun A : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ =>
      F (Function.update A i (A i * g A))) (productHaar N (n + 1)) :=
    (F.continuous.comp
        (continuous_id.update i ((continuous_apply i).mul hg))).integrable_of_hasCompactSupport
      ((isClosed_tsupport _).isCompact)
  have hΦ2 : Integrable (fun A : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ => F A)
      (productHaar N (n + 1)) :=
    F.continuous.integrable_of_hasCompactSupport ((isClosed_tsupport _).isCompact)
  have hleft : (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F (Function.update ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
          (((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
            * g ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p))))
      = fun p => F (i.insertNth (p.1 * g (i.insertNth 1 p.2)) p.2) := by
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_apply_same]
    have hgy : g (i.insertNth p.1 p.2) = g (i.insertNth 1 p.2) := by
      rw [← Fin.update_insertNth (α := fun _ : Fin (n + 1) =>
        Matrix.unitaryGroup (Fin N) ℂ) i p.1 1 p.2, hgi]
    rw [hgy, Fin.update_insertNth]
  have hright : (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p))
      = fun p => F (i.insertNth p.1 p.2) := by
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
  have hint1 : Integrable (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) =>
        F (i.insertNth (p.1 * g (i.insertNth 1 p.2)) p.2))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    rw [← hleft]
    exact hFint _ hΦ1
  have hint2 : Integrable (fun p : Matrix.unitaryGroup (Fin N) ℂ ×
        (Fin n → Matrix.unitaryGroup (Fin N) ℂ) => F (i.insertNth p.1 p.2))
      ((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
    rw [← hright]
    exact hFint _ hΦ2
  calc (∫ A, F (Function.update A i (A i * g A)) ∂productHaar N (n + 1))
      = ∫ p, F (Function.update ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
          (((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p) i
            * g ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)))
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
        hkey _
    _ = ∫ p, F (i.insertNth (p.1 * g (i.insertNth 1 p.2)) p.2)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
        rw [hleft]
    _ = ∫ y, (∫ x, F (i.insertNth (x * g (i.insertNth 1 y)) y) ∂haarUnitary N)
          ∂(Measure.pi fun _ : Fin n => haarUnitary N) :=
        integral_prod_symm _ hint1
    _ = ∫ y, (∫ x, F (i.insertNth x y) ∂haarUnitary N)
          ∂(Measure.pi fun _ : Fin n => haarUnitary N) :=
        integral_congr_ae (ae_of_all _ fun y =>
          integral_mul_right_eq_self (μ := haarUnitary N)
            (fun x => F (i.insertNth x y)) (g (i.insertNth 1 y)))
    _ = ∫ p, F (i.insertNth p.1 p.2)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) :=
        (integral_prod_symm _ hint2).symm
    _ = ∫ p, F ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => Matrix.unitaryGroup (Fin N) ℂ) i).symm p)
          ∂((haarUnitary N).prod (Measure.pi fun _ : Fin n => haarUnitary N)) := by
        rw [hright]
    _ = ∫ A, F A ∂productHaar N (n + 1) := (hkey _).symm

/-- Consistency probe: the constant-`g` form is the degenerate instance of the
triangular substitution (constant functions depend on no slot at all). -/
example (N k : ℕ) (i : Fin k) (g : Matrix.unitaryGroup (Fin N) ℂ)
    (F : C(Fin k → Matrix.unitaryGroup (Fin N) ℂ, ℂ)) :
    (∫ A, F (Function.update A i (g * A i)) ∂productHaar N k)
      = ∫ A, F A ∂productHaar N k :=
  productE_update_mulLeft N k i (fun _ => g) continuous_const (fun _ _ => rfl) F

/-! ### PH-6: the honest tilted measures

The HONEST (untruncated, normalized) tilted-measure packaging via `Measure.tilted`
(`Measure/Tilted.lean:42`): `μ.tilted W` is `μ` reweighted by
`e^{W} / ∫ e^{W} dμ`, so the partition-function normalization is carried by the
definition and never needs a separate `Z ≠ 0` side condition. The weight is built
from the real-first `reTrace` of `HonestKernel` (β in Chatterjee units,
arXiv:1803.01950 eq. (3.2); the one-matrix kernel anchors — Lüscher Eq. (21), Creutz
p. 1131, DZ (3.17)/(3.28) — are recorded there). The integrability input of every probability instance is elementary:
the weight is continuous on a compact configuration space, hence its exponential is
integrable against the ambient probability measure. -/

/-- **PH-6: the honest two-site Gibbs (tilted) measure**: the pair Haar measure
`pairHaar N` tilted by the untruncated two-argument weight `β · Re Tr (U⁻¹ V)` — the
normalized packaging of the kernel weight `K(U, V) = e^{β Re Tr (U⁻¹ V)}` whose
scalar layer is `HonestKernel`. (The name `gibbsPair` is kept: it is an honest
description of the tilted measure.) -/
noncomputable def gibbsPair (N : ℕ) (β : ℝ) :
    Measure (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :=
  (pairHaar N).tilted (fun p => β * reTrace (p.1⁻¹ * p.2))

private theorem integrable_exp_pairWeight (N : ℕ) (β : ℝ) :
    Integrable (fun p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ
      => Real.exp (β * reTrace (p.1⁻¹ * p.2))) (pairHaar N) :=
  (Real.continuous_exp.comp (continuous_const.mul
      (continuous_reTrace.comp
        ((continuous_fst.inv).mul continuous_snd)))).integrable_of_hasCompactSupport
    ((isClosed_tsupport _).isCompact)

/-- `gibbsPair N β` is a probability measure (`isProbabilityMeasure_tilted`,
`Measure/Tilted.lean:126`): the weight is continuous on the compact `U(N) × U(N)`,
so its exponential is `pairHaar`-integrable. -/
instance instIsProbabilityMeasureGibbsPair (N : ℕ) (β : ℝ) :
    IsProbabilityMeasure (gibbsPair N β) :=
  isProbabilityMeasure_tilted (integrable_exp_pairWeight N β)

/-- **`β = 0` degeneracy probe**: the unweighted honest Gibbs pair measure is the
pair Haar measure (`tilted_const` at `c = 0`, using the probability instance). -/
theorem gibbsPair_beta_zero (N : ℕ) : gibbsPair N 0 = pairHaar N := by
  unfold gibbsPair
  rw [show (fun p : Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ =>
      (0 : ℝ) * reTrace (p.1⁻¹ * p.2)) = fun _ => (0 : ℝ) from
    funext fun _ => zero_mul _]
  exact tilted_const (pairHaar N) 0

/-- **PH-6: the honest open-chain Gibbs (tilted) measure**: the `(L+1)`-fold product
Haar measure tilted by the untruncated nearest-neighbour weight
`∑_{s < L} β · Re Tr ((A_s)⁻¹ A_{s+1})` — an open chain of `L + 1` copies of `U(N)`
with `L` kernel factors. (The name `chainGibbs` is kept: it is an honest description
of the tilted measure; no lattice-gauge-theory claim is made in this repository.)
β in Chatterjee units (arXiv:1803.01950, eq. (3.2)). -/
noncomputable def chainGibbs (N : ℕ) (β : ℝ) (L : ℕ) :
    Measure (Fin (L + 1) → Matrix.unitaryGroup (Fin N) ℂ) :=
  (productHaar N (L + 1)).tilted
    (fun A => ∑ s : Fin L, β * reTrace ((A s.castSucc)⁻¹ * A s.succ))

private theorem integrable_exp_chainWeight (N : ℕ) (β : ℝ) (L : ℕ) :
    Integrable (fun A : Fin (L + 1) → Matrix.unitaryGroup (Fin N) ℂ =>
      Real.exp (∑ s : Fin L, β * reTrace ((A s.castSucc)⁻¹ * A s.succ)))
      (productHaar N (L + 1)) :=
  (Real.continuous_exp.comp (continuous_finsetSum _ fun s _ =>
      continuous_const.mul (continuous_reTrace.comp
        (((continuous_apply s.castSucc).inv).mul
          (continuous_apply s.succ))))).integrable_of_hasCompactSupport
    ((isClosed_tsupport _).isCompact)

/-- `chainGibbs N β L` is a probability measure
(`isProbabilityMeasure_tilted`, `Measure/Tilted.lean:126`): the chain action is a
finite sum of continuous terms on the compact configuration space
`(Fin (L+1)) → U(N)`, so its exponential is `productHaar`-integrable
(`Continuous.integrable_of_hasCompactSupport`). -/
instance instIsProbabilityMeasureChainGibbs (N : ℕ) (β : ℝ) (L : ℕ) :
    IsProbabilityMeasure (chainGibbs N β L) :=
  isProbabilityMeasure_tilted (integrable_exp_chainWeight N β L)

/-- **The `integral_tilted` transfer formula for `chainGibbs`**: for
*every* observable `f`, the `chainGibbs` integral is the `productHaar` integral
reweighted by the normalized Boltzmann factor
`e^{W(A)} / ∫ e^{W} d(productHaar)` — exactly as `integral_tilted`
(`Measure/Tilted.lean:230`) gives it, with no integrability or measurability side
conditions. This is the bridge that trades `chainGibbs`
correlators for genuine multi-copy product-Haar integrals. -/
theorem chainGibbs_integral (N : ℕ) (β : ℝ) (L : ℕ)
    (f : (Fin (L + 1) → Matrix.unitaryGroup (Fin N) ℂ) → ℂ) :
    (∫ A, f A ∂chainGibbs N β L)
      = ∫ A, (Real.exp (∑ s : Fin L, β * reTrace ((A s.castSucc)⁻¹ * A s.succ))
            / ∫ B, Real.exp (∑ s : Fin L, β * reTrace ((B s.castSucc)⁻¹ * B s.succ))
                ∂productHaar N (L + 1)) • f A ∂productHaar N (L + 1) := by
  unfold chainGibbs
  exact integral_tilted _ f

/-- **`β = 0` degeneracy probe**: the unweighted honest chain Gibbs measure is the
product Haar measure — the `L`-fold sum of zero weights tilts by a constant. -/
theorem chainGibbs_beta_zero (N L : ℕ) : chainGibbs N 0 L = productHaar N (L + 1) := by
  unfold chainGibbs
  rw [show (fun A : Fin (L + 1) → Matrix.unitaryGroup (Fin N) ℂ =>
      ∑ s : Fin L, (0 : ℝ) * reTrace ((A s.castSucc)⁻¹ * A s.succ))
      = fun _ => (0 : ℝ) from funext fun _ => by simp]
  exact tilted_const (productHaar N (L + 1)) 0

/-- Normalization payoff probe: the honest chain Gibbs measure integrates the
constant observable `1` to `1` — the probability instance in integral form. -/
example (N : ℕ) (β : ℝ) (L : ℕ) : (∫ _A, (1 : ℂ) ∂chainGibbs N β L) = 1 := by
  rw [integral_const, probReal_univ, one_smul]

end Weingarten.Haar
