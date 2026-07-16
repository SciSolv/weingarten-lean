#!/usr/bin/env python3
# Copyright (c) 2026 Daniel G. West. Apache-2.0 (see LICENSE). Authors: Daniel G. West
"""Master runner for the exact-arithmetic cross-check suites.

These scripts do NOT prove anything -- the Lean development is the proof, and is
sorry-free and axiom-clean. What they add is an INDEPENDENT check: each formalized
computational theorem is re-computed from scratch in exact rational arithmetic
(stdlib only -- fractions.Fraction, itertools; no floats/numpy/sympy) and compared
against a second, genuinely independent computation, exhaustively over all cases
up to a size bound.

  python scripts/verify_all.py

The four verify_<package>.py suites print one `PASS <theorem>` line per formalized
theorem (see scripts/VERIFICATION.md for the per-theorem ledger). The remaining
suites are the original convention- and proof-step cross-checks. This runner
executes them all under the current interpreter and exits 0 iff every suite
exits 0.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# Per-theorem suites first (their stdout IS the per-theorem ledger), then the
# original cross-check / exploration suites.
ORDER = [
    "verify_unitary.py",
    "verify_below.py",
    "verify_orthogonal.py",
    "verify_symplectic.py",
    "convention_checks.py",
    "absorption_proof_checks.py",
    "crossing_sign_proof_checks.py",
    "symplectic_adjudication.py",
    "pfaffian_reading_checks.py",
    "brauer_exploration.py",
]


def main():
    results = []
    for name in ORDER:
        path = os.path.join(HERE, name)
        print("=" * 72)
        print("RUN  " + name)
        print("-" * 72)
        if not os.path.exists(path):
            print("MISSING " + path)
            results.append((name, None))
            continue
        rc = subprocess.run([sys.executable, path], cwd=ROOT).returncode
        results.append((name, rc))
        print()

    print("=" * 72)
    print("SUMMARY")
    print("-" * 72)
    failed = []
    for name, rc in results:
        if rc == 0:
            tag = "PASS"
        elif rc is None:
            tag = "MISSING"
            failed.append(name)
        else:
            tag = "FAIL (exit %d)" % rc
            failed.append(name)
        print("  %-32s %s" % (name, tag))
    print("=" * 72)

    if failed:
        print("%d SUITE(S) FAILED: %s" % (len(failed), ", ".join(failed)))
        sys.exit(1)
    print("ALL %d CROSS-CHECK SUITES PASSED" % len(results))
    sys.exit(0)


if __name__ == "__main__":
    main()
