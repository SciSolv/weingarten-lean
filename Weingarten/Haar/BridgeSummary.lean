/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.SymplecticGram

/-!
# Bridge summary: the Haar layer's Weingarten vocabulary

The `Weingarten.Haar` modules were developed downstream of this repository's
Weingarten calculus and are now maintained here. This
file records how the bridge vocabulary used there maps onto the repository's own
declarations:

* the unitary Weingarten **Gram** element on `Sₙ` (matrix entries
  `N^{loops(σ⁻¹τ)}`, over any `CommRing`) is `Weingarten.gram`;
* the unitary **Weingarten function** is `Weingarten.wg` — the inverse of the Gram
  element in the stable range `N > n − 1`, where it coincides with the Moore–Penrose
  pseudo-inverse of the general Collins–Śniady theory; explicit small-`n`
  evaluations are in `Weingarten.Haar.WeingartenValues`, derived from the sum rules
  `Weingarten.sum_wg` / `Weingarten.sum_sgn_wg`;
* the orthogonal Weingarten Gram `N^{loops}` on pair partitions is
  `Weingarten.orthGram`;
* the symplectic Weingarten Gram `ε·ε·(−1)ⁿ·(−2M)^{loops}` is
  `Weingarten.sympGramClosed`, running on the symplectic *form* `Weingarten.Jform`
  (`J² = −1`) via the negative-dimension duality `O(−2M) ↔ Sp(2M)` — deliberately
  **group-free**: no compact `Sp(N) = USp(2N)` is built.

**Scope honesty (the claim ceiling).** The `Weingarten.Haar` modules provide the
U(N) Haar-integration bridge **at the formalized degrees only**: the exact `n = 1`
entry integral, the `n = 2` fourth-moment system, and trace-word moments through
total degree 5. The general-`n` integral ↔ Gram moment identity (the Collins–Śniady
master formula) is **not** formalized in this repository, and no declaration claims
or names it.
-/

namespace Weingarten.Haar

/-- Live cross-layer sanity check (kept from the original bridge file): a
Weingarten-calculus theorem about an object the Haar vocabulary refers to
(`sympGramClosed_symm`, symmetry of the symplectic Gram) is in scope here —
confirming the dependency is genuinely load-bearing, not merely declared. -/
example {k : Type*} [CommRing k] (M n : ℕ) (p q : Weingarten.Pairing n) :
    Weingarten.sympGramClosed k M n p q = Weingarten.sympGramClosed k M n q p :=
  Weingarten.sympGramClosed_symm p q

end Weingarten.Haar
