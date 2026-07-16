/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten

/-!
# Axiom audit — permanent verification tool (not part of the library build)

Like the `scripts/*.py` suites, this file proves nothing new — the Lean
development is the proof. What it adds is a one-command audit of the stated
axiom profile: it walks every constant in the environment whose name root is
`Weingarten` (the root module imports the whole development, including the
`Weingarten.Haar` layer) and collects, via `Lean.collectAxioms`, the full set
of axioms each one depends on. The audit **fails with a nonzero exit code** if
any axiom outside the allowed trio

  `propext`, `Classical.choice`, `Quot.sound`

appears. This soundly catches `sorryAx` (a `sorry` anywhere in a proof) and
`Lean.ofReduceBool` / `Lean.ofReduceNat` (`native_decide`) in the same pass,
alongside any other stray axiom.

Run from the repository root, after `lake build`:

  lake env lean scripts/AxiomsAudit.lean

CI runs this step after the build; see `.github/workflows/blueprint.yml`.
-/

open Lean

/-- The only axioms a `Weingarten` constant is allowed to depend on. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Audit every `Weingarten`-rooted constant; `throwError` (nonzero exit) on
any disallowed axiom, otherwise print the count, the elapsed time, and an
explicit `PASS` line. -/
def runAxiomsAudit : CoreM Unit := do
  let t0 ← IO.monoMsNow
  let env ← getEnv
  let names : Array Name := env.constants.toList.foldl (init := #[]) fun acc (n, _) =>
    if n.getRoot == `Weingarten then acc.push n else acc
  let mut offenders : Array (Name × Name) := #[]
  for n in names do
    for ax in (← collectAxioms n) do
      unless allowedAxioms.contains ax do
        offenders := offenders.push (n, ax)
  let t1 ← IO.monoMsNow
  unless offenders.isEmpty do
    for (n, ax) in offenders do
      IO.println s!"AxiomsAudit: FAIL -- {n} depends on disallowed axiom {ax}"
    throwError "AxiomsAudit: FAIL -- {offenders.size} disallowed axiom dependencies \
      across {names.size} Weingarten constants"
  IO.println s!"AxiomsAudit: PASS -- {names.size} Weingarten constants audited in \
    {t1 - t0} ms; every axiom dependency lies in the allowed trio \
    \{propext, Classical.choice, Quot.sound} (in particular: no sorryAx, \
    no Lean.ofReduceBool / Lean.ofReduceNat)."

#eval runAxiomsAudit
