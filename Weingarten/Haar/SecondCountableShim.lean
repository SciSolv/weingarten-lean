/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.Haar.HaarConstruction
import Mathlib.Topology.Bases

/-!
# Second-countability shim for `Matrix` and `U(N)`

The two verified instances closing a toolchain gap: at the pinned Mathlib
(`94fba23`) there is **no**
`SecondCountableTopology` instance for `Matrix (Fin N) (Fin N) ℂ` — the pi-type
instances do not see through the `Matrix` definition — and none for the unitary
subtype either: the `Set`-keyed subtype instance (`Topology/Bases.lean:875`) never
fires for the `Submonoid`-style coercion of `Matrix.unitaryGroup`.

* `instSecondCountableMatrix`: **defeq transport** from the pi type — `Matrix m n α`
  is by definition `m → n → α` and carries the pi topology definitionally, so the
  countable-product instance `(inferInstance : SecondCountableTopology
  ((Fin N) → (Fin N) → ℂ))` *is* the matrix instance.
* `instSecondCountableUnitaryGroup`: the subtype topology is the induced topology,
  so `secondCountableTopology_induced` (`Topology/Bases.lean:866`) applied to
  `Subtype.val` transports second-countability from matrix space.

## Why an own file

**Pin-advance visibility**: a later Mathlib may add these instances upstream; any
toolchain advance should re-check exactly this file for instance collisions, so the
shim stays visible in one place rather than buried in a consumer.

## Payoff

After these two instances, `OpensMeasurableSpace`/`BorelSpace` on binary products
and finite pi powers of `U(N)` all fire by `inferInstance`
(`Prod.opensMeasurableSpace`/`Prod.borelSpace` need `SecondCountableTopologyEither`;
`Pi.opensMeasurableSpace`/`Pi.borelSpace` need per-factor second-countability —
`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:407/:642/:357/:631`).
The closing `example` probes certify this in-tree.
-/

namespace Weingarten.Haar

/-- **Second-countability of matrix space**: `Matrix m n α` is
definitionally the pi type `m → n → α` with the pi topology, so the countable-product
instance transports by defeq. -/
instance instSecondCountableMatrix (N : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  (inferInstance : SecondCountableTopology ((Fin N) → (Fin N) → ℂ))

/-- **Second-countability of `U(N)`**: the subtype topology on
`Matrix.unitaryGroup (Fin N) ℂ` is the topology induced by `Subtype.val`, so
`secondCountableTopology_induced` (`Topology/Bases.lean:866`) applies. The `Set`-keyed
subtype instance at `Topology/Bases.lean:875` never fires for the `Submonoid`
coercion, whence the explicit instance. -/
instance instSecondCountableUnitaryGroup (N : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin N) ℂ) :=
  TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-! ### Probes (committed in-tree)

The product and pi-power Borel synthesis that the shim unlocks — each fires by bare
`inferInstance`. These are the exact instance demands of the `PairHaar` witness
(binary product) and the `ProductHaar`/`chainGibbs` tier (finite pi powers). -/

/-- Probe: the opens-measurable structure on the pair space `U(N) × U(N)` fires. -/
example (N : ℕ) :
    OpensMeasurableSpace
      (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

/-- Probe: the Borel-space structure on the pair space `U(N) × U(N)` fires. -/
example (N : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin N) ℂ × Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

/-- Probe: the opens-measurable structure on finite pi powers of `U(N)` fires. -/
example (N k : ℕ) :
    OpensMeasurableSpace (Fin k → Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

/-- Probe: the Borel-space structure on finite pi powers of `U(N)` fires. -/
example (N k : ℕ) : BorelSpace (Fin k → Matrix.unitaryGroup (Fin N) ℂ) :=
  inferInstance

end Weingarten.Haar
