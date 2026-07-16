/-
Copyright (c) 2026 Daniel G. West. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel G. West
-/
import Weingarten.CycleCount
import Weingarten.BelowThreshold

/-!
# The below-threshold cell `(N, n) = (2, 3)`, certified over `ℚ`

Fully elaborated and `sorry`-free (`#print axioms` of every theorem below gives only
`propext`, `Classical.choice`, `Quot.sound` — kernel-only, **no** `native_decide`).
Blueprint: `def:gram23`, `def:w23`, `lem:penrose_unique`, `thm:cell23`, `def:wcell`,
`thm:penrose_alg`, `cor:cell_rules`, `prop:avg_sign`, `prop:sign_flip`,
`cor:gram_two_singular`, `cor:cell_unique`.

Below threshold the Gram matrix is singular and the Weingarten data is its Moore–Penrose
pseudoinverse. Rather than building pseudoinverse theory, this file certifies the single
cell used by the companion note as a finite exact computation: the explicit `6 × 6`
rational matrices satisfy the four Penrose equations (check C6), and the transpose-form
Penrose solution is unique, so `17/144, 1/144, -7/144` are *the* `(2,3)` Weingarten
values. Row sums recover the all-`N` rising value `1/24`, and signed row sums vanish — the
exact below-threshold collapse of the falling rule.

**Proof route for `penrose` and `row_sums`.** `decide` over `ℚ` is infeasible (kernel
reduction stalls on `Rat` gcd-normalization). Instead the data is integer-valued up to a
global `1/144`: `G = 2 ^ cycleCount` is `ℤ`-valued and `W = (1/144) • W₀` with
`W₀ ∈ {17, 1, -7}`, so the Penrose equations become the `ℤ`-matrix identities
`G·W₀·G = 144·G` etc., which kernel `decide` *does* reduce (no `Rat`). Casting back through
`Int.castRingHom ℚ` recovers the rational statements. `row_sums`/`avg_sign` likewise reduce
to integer sums. No `native_decide` anywhere, so the trusted base is unchanged.

**Algebra-level certificate.** `penrose_alg` transports the matrix certificate along the
injective left-regular representation `Φ = toMatrixAlgEquiv ∘ Algebra.lmul`, using that
`cycleCount` and `wval` are inverse-symmetric class functions (`cycleCount_mul_inv_comm`,
`wval_mul_inv_comm`).
-/

namespace Weingarten.Cell23

open Equiv (Perm)
open scoped Matrix

/-! ### The cell data

(`cycleCount`'s inversion/conjugation invariance — `cycleCount_inv`, `cycleCount_conj`,
`cycleCount_mul_inv_comm` — now lives upstream in `CycleCount.lean`.) -/

/-- Gram matrix `G (σ, τ) = 2 ^ cycleCount (σ⁻¹ * τ)` on `S₃`, over `ℚ`.
Blueprint: `def:gram23`. -/
def G : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℚ :=
  Matrix.of fun σ τ => (2 : ℚ) ^ cycleCount 3 (σ⁻¹ * τ)

/-- The candidate `(2,3)` Weingarten values: `17/144` at the identity, `1/144` on the
three transpositions (positive, where the stable range would force negative — the sign
flip), `-7/144` on the two 3-cycles. -/
def wval (σ : Perm (Fin 3)) : ℚ :=
  if σ = 1 then 17 / 144 else if Equiv.Perm.sign σ = -1 then 1 / 144 else -7 / 144

/-- Candidate Weingarten matrix `W (σ, τ) = wval (σ⁻¹ * τ)`. Blueprint: `def:w23`. -/
def W : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℚ :=
  Matrix.of fun σ τ => wval (σ⁻¹ * τ)

/-! ### Integer model

`G` and `144 • W` are integer matrices; over `ℤ` the Penrose equations have no `Rat`
normalization, so kernel `decide` reduces them. -/

/-- Integer Gram matrix `2 ^ cycleCount`. -/
def Gz : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℤ :=
  Matrix.of fun σ τ => (2 : ℤ) ^ cycleCount 3 (σ⁻¹ * τ)
/-- Integer Weingarten weights `144 • wval`. -/
def wz (σ : Perm (Fin 3)) : ℤ := if σ = 1 then 17 else if Equiv.Perm.sign σ = -1 then 1 else -7
/-- Integer Weingarten matrix `144 • W`. -/
def Wz : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℤ :=
  Matrix.of fun σ τ => wz (σ⁻¹ * τ)

theorem GzWzGz : Gz * Wz * Gz = (144 : ℤ) • Gz := by decide
theorem WzGzWz : Wz * Gz * Wz = (144 : ℤ) • Wz := by decide
theorem GWsymm : (Gz * Wz)ᵀ = Gz * Wz := by decide
theorem WGsymm : (Wz * Gz)ᵀ = Wz * Gz := by decide

theorem hG : G = (Int.castRingHom ℚ).mapMatrix Gz := by
  ext σ τ
  simp only [G, Gz, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    Int.coe_castRingHom]
  push_cast; ring
theorem hW : W = (1 / 144 : ℚ) • (Int.castRingHom ℚ).mapMatrix Wz := by
  ext σ τ
  simp only [W, Wz, wval, wz, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom]
  split_ifs <;> push_cast <;> ring
theorem GWG_Q : (Int.castRingHom ℚ).mapMatrix Gz * (Int.castRingHom ℚ).mapMatrix Wz
    * (Int.castRingHom ℚ).mapMatrix Gz = (144 : ℚ) • (Int.castRingHom ℚ).mapMatrix Gz := by
  rw [← map_mul, ← map_mul, GzWzGz]; ext σ τ
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Int.coe_castRingHom]
  push_cast; ring
theorem WGW_Q : (Int.castRingHom ℚ).mapMatrix Wz * (Int.castRingHom ℚ).mapMatrix Gz
    * (Int.castRingHom ℚ).mapMatrix Wz = (144 : ℚ) • (Int.castRingHom ℚ).mapMatrix Wz := by
  rw [← map_mul, ← map_mul, WzGzWz]; ext σ τ
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Int.coe_castRingHom]
  push_cast; ring
theorem hGW : G * W = (1 / 144 : ℚ) • (Int.castRingHom ℚ).mapMatrix (Gz * Wz) := by
  rw [hG, hW, Matrix.mul_smul, ← map_mul]
theorem hWG : W * G = (1 / 144 : ℚ) • (Int.castRingHom ℚ).mapMatrix (Wz * Gz) := by
  rw [hG, hW, Matrix.smul_mul, ← map_mul]

/-! ### Penrose uniqueness and the certified cell -/

/-- Transpose-form Moore–Penrose uniqueness over `ℚ` (standard six-line algebra, valid
over any commutative ring). Blueprint: `lem:penrose_unique`. -/
theorem penrose_unique {ι : Type*} [Fintype ι] (A X Y : Matrix ι ι ℚ)
    (hX : A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A)
    (hY : A * Y * A = A ∧ Y * A * Y = Y ∧ (A * Y)ᵀ = A * Y ∧ (Y * A)ᵀ = Y * A) :
    X = Y := by
  obtain ⟨hX1, hX2, hX3, hX4⟩ := hX
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hAB : A * X = A * Y := by
    calc A * X = (A * X)ᵀ := hX3.symm
      _ = Xᵀ * Aᵀ := Matrix.transpose_mul A X
      _ = Xᵀ * (A * Y * A)ᵀ := by rw [hY1]
      _ = Xᵀ * (Aᵀ * (A * Y)ᵀ) := by rw [Matrix.transpose_mul (A * Y) A]
      _ = Xᵀ * (Aᵀ * (A * Y)) := by rw [hY3]
      _ = Xᵀ * Aᵀ * (A * Y) := by rw [← mul_assoc]
      _ = (A * X)ᵀ * (A * Y) := by rw [← Matrix.transpose_mul]
      _ = A * X * (A * Y) := by rw [hX3]
      _ = A * X * A * Y := by rw [← mul_assoc]
      _ = A * Y := by rw [hX1]
  have hXA : X * A = Y * A := by
    calc X * A = (X * A)ᵀ := hX4.symm
      _ = Aᵀ * Xᵀ := Matrix.transpose_mul X A
      _ = (A * Y * A)ᵀ * Xᵀ := by rw [hY1]
      _ = ((Y * A)ᵀ * Aᵀ) * Xᵀ := by
            rw [show A * Y * A = A * (Y * A) from mul_assoc A Y A, Matrix.transpose_mul A (Y * A)]
      _ = ((Y * A) * Aᵀ) * Xᵀ := by rw [hY4]
      _ = (Y * A) * (Aᵀ * Xᵀ) := by rw [mul_assoc]
      _ = (Y * A) * (X * A)ᵀ := by rw [← Matrix.transpose_mul]
      _ = (Y * A) * (X * A) := by rw [hX4]
      _ = Y * (A * (X * A)) := by rw [mul_assoc]
      _ = Y * (A * X * A) := by rw [← mul_assoc A X A]
      _ = Y * A := by rw [hX1]
  calc X = X * A * X := hX2.symm
    _ = X * (A * X) := by rw [mul_assoc]
    _ = X * (A * Y) := by rw [hAB]
    _ = X * A * Y := by rw [← mul_assoc]
    _ = Y * A * Y := by rw [hXA]
    _ = Y := hY2

/-- Bridge to the full Moore–Penrose property: against a symmetric matrix `A`, a
symmetric partner `X` satisfying the two product identities and commuting with
`A` satisfies all four Penrose equations — the transpose conditions come for
free from symmetry plus commutation. -/
theorem penrose_of_symm_comm {ι : Type*} [Fintype ι] (A X : Matrix ι ι ℚ)
    (h1 : A * X * A = A) (h2 : X * A * X = X)
    (hA : Aᵀ = A) (hX : Xᵀ = X) (hc : X * A = A * X) :
    A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A := by
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hX, hA, hc]
  · rw [Matrix.transpose_mul, hA, hX, ← hc]

/-- Canonicity of symmetric commuting two-equation partners: any two of them
agree (via `penrose_of_symm_comm` and the four-equation `penrose_unique`), so
the two Penrose equations plus symmetry and commutation pin the partner down
uniquely — in particular it is *the* Moore–Penrose pseudo-inverse. -/
theorem penrose_unique_of_symm_comm {ι : Type*} [Fintype ι] (A X Y : Matrix ι ι ℚ)
    (hA : Aᵀ = A)
    (hX1 : A * X * A = A) (hX2 : X * A * X = X) (hXs : Xᵀ = X) (hXc : X * A = A * X)
    (hY1 : A * Y * A = A) (hY2 : Y * A * Y = Y) (hYs : Yᵀ = Y) (hYc : Y * A = A * Y) :
    X = Y :=
  penrose_unique A X Y (penrose_of_symm_comm A X hX1 hX2 hA hXs hXc)
    (penrose_of_symm_comm A Y hY1 hY2 hA hYs hYc)

/-- The four Penrose equations for `(G, W)` — finite exact computation (check C6), via the
integer model and kernel `decide` over `ℤ`. Blueprint: `thm:cell23`. -/
theorem penrose : G * W * G = G ∧ W * G * W = W ∧ (G * W)ᵀ = G * W ∧ (W * G)ᵀ = W * G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hG, hW]; simp only [Matrix.smul_mul, Matrix.mul_smul]; rw [GWG_Q, smul_smul]; norm_num
  · rw [hG, hW]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [WGW_Q, smul_smul]; norm_num
  · rw [hGW, Matrix.transpose_smul]; congr 1
    rw [show ((Int.castRingHom ℚ).mapMatrix (Gz * Wz))ᵀ
          = (Int.castRingHom ℚ).mapMatrix ((Gz * Wz)ᵀ) from rfl, GWsymm]
  · rw [hWG, Matrix.transpose_smul]; congr 1
    rw [show ((Int.castRingHom ℚ).mapMatrix (Wz * Gz))ᵀ
          = (Int.castRingHom ℚ).mapMatrix ((Wz * Gz)ᵀ) from rfl, WGsymm]

/-! ### Integer sums for the row-sum and average-sign rules -/

theorem sum_wz : ∑ σ : Perm (Fin 3), wz σ = 6 := by decide
theorem sum_sgn_wz : ∑ σ : Perm (Fin 3), (Equiv.Perm.sign σ : ℤ) * wz σ = 0 := by decide
theorem sum_abs_wz : ∑ σ : Perm (Fin 3), |wz σ| = 34 := by decide
theorem hwv (σ : Perm (Fin 3)) : wval σ = (1 / 144) * ((wz σ : ℤ) : ℚ) := by
  simp only [wval, wz]; split_ifs <;> push_cast <;> ring
theorem sum_wval : ∑ σ : Perm (Fin 3), wval σ = 1 / 24 := by
  have h : ∑ σ : Perm (Fin 3), wval σ = (1 / 144) * ∑ σ : Perm (Fin 3), ((wz σ : ℤ) : ℚ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => hwv σ)
  rw [h, ← Int.cast_sum, sum_wz]; norm_num
theorem sum_sgn_wval : ∑ σ : Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℚ) * wval σ = 0 := by
  have h : ∑ σ : Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℚ) * wval σ
      = (1 / 144) * ∑ σ : Perm (Fin 3), (((Equiv.Perm.sign σ : ℤ) * wz σ : ℤ) : ℚ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [hwv σ]; push_cast; ring
  rw [h, ← Int.cast_sum, sum_sgn_wz]; norm_num
theorem sum_abs_wval : ∑ σ : Perm (Fin 3), |wval σ| = 34 / 144 := by
  have h : ∑ σ : Perm (Fin 3), |wval σ| = (1 / 144) * ∑ σ : Perm (Fin 3), ((|wz σ| : ℤ) : ℚ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [hwv σ, abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 144)]
    push_cast; ring
  rw [h, ← Int.cast_sum, sum_abs_wz]; norm_num

/-- Row sums `1/24` (rising value at `N = 2`) and signed row sums `0` (below-threshold
collapse of the falling rule), by reindexing each row to the full weight sum.
Blueprint: `thm:cell23` (check C6). -/
theorem row_sums :
    (∀ σ, ∑ τ, W σ τ = 1 / 24) ∧
      (∀ σ, ∑ τ, ((Equiv.Perm.sign τ : ℤ) : ℚ) * W σ τ = 0) := by
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · have h1 : ∑ τ, W σ τ = ∑ ρ : Perm (Fin 3), wval ρ := by
      simp only [W, Matrix.of_apply]
      exact Equiv.sum_comp (Equiv.mulLeft σ⁻¹) wval
    rw [h1, sum_wval]
  · have h2 : ∑ τ, ((Equiv.Perm.sign τ : ℤ) : ℚ) * W σ τ
        = ((Equiv.Perm.sign σ : ℤ) : ℚ)
            * ∑ ρ : Perm (Fin 3), ((Equiv.Perm.sign ρ : ℤ) : ℚ) * wval ρ := by
      simp only [W, Matrix.of_apply]
      rw [← Equiv.sum_comp (Equiv.mulLeft σ)
            (fun τ => ((Equiv.Perm.sign τ : ℤ) : ℚ) * wval (σ⁻¹ * τ)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [inv_mul_cancel_left, map_mul, Units.val_mul]
      push_cast; ring
    rw [h2, sum_sgn_wval, mul_zero]

/-! ### Algebra-level upgrades -/

/-- The candidate Weingarten data as a group-algebra element over `ℚ`.
Blueprint: `def:wcell`. -/
noncomputable def Wcell : SymAlg ℚ 3 :=
  ∑ σ : Perm (Fin 3), wval σ • MonoidAlgebra.of ℚ (Perm (Fin 3)) σ

/-- `wval` depends only on the identity-test and the sign, both inversion/conjugation
invariant; hence `wval` is a class function with the inverse-symmetry of `G`. -/
theorem wval_congr (x y : Perm (Fin 3)) (hsign : Equiv.Perm.sign x = Equiv.Perm.sign y)
    (hone : x = 1 ↔ y = 1) : wval x = wval y := by
  unfold wval
  by_cases h : x = 1
  · rw [if_pos h, if_pos (hone.mp h)]
  · rw [if_neg h, if_neg (fun hy => h (hone.mpr hy)), hsign]
theorem wval_mul_inv_comm (a b : Perm (Fin 3)) : wval (a * b⁻¹) = wval (a⁻¹ * b) := by
  apply wval_congr
  · rw [map_mul, map_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_inv]
  · rw [mul_inv_eq_one, inv_mul_eq_one]

/-- Left-regular representation as an injective `ℚ`-algebra hom
`SymAlg ℚ 3 → Matrix _ _ ℚ`, with entry `Φ x i j = x (i * j⁻¹)`. -/
private noncomputable def Phi :
    SymAlg ℚ 3 →ₐ[ℚ] Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℚ :=
  (LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne).toAlgHom.comp (Algebra.lmul ℚ (SymAlg ℚ 3))

private theorem Phi_apply (x : SymAlg ℚ 3) (i j : Perm (Fin 3)) :
    Phi x i j = x (i * j⁻¹) := by
  have h1 : Phi x i j = (x * MonoidAlgebra.single j (1 : ℚ)) i := by
    rw [Phi, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, LinearMap.toMatrixAlgEquiv_apply,
      Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.coe_basisSingleOne]
    rfl
  rw [h1, MonoidAlgebra.mul_single_apply, mul_one]

/-- The regular-representation matrix of `gram ℚ 3 2` is `G` (using `cycleCount`'s
inverse-symmetry). -/
private theorem hPhiG : Phi (gram ℚ 3 2) = G := by
  ext i j
  rw [gram, map_sum, Matrix.sum_apply, G, Matrix.of_apply, ← cycleCount_mul_inv_comm 3 i j]
  rw [Finset.sum_eq_single_of_mem (i * j⁻¹) (Finset.mem_univ _)
    (fun σ _ hσ => by
      rw [map_smul, Matrix.smul_apply, Phi_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_apply, if_neg hσ, smul_eq_mul, mul_zero])]
  rw [map_smul, Matrix.smul_apply, Phi_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_apply, if_pos rfl, smul_eq_mul, mul_one]

/-- The regular-representation matrix of `Wcell` is `W` (using `wval`'s inverse-symmetry). -/
private theorem hPhiW : Phi Wcell = W := by
  ext i j
  rw [Wcell, map_sum, Matrix.sum_apply, W, Matrix.of_apply, ← wval_mul_inv_comm i j]
  rw [Finset.sum_eq_single_of_mem (i * j⁻¹) (Finset.mem_univ _)
    (fun σ _ hσ => by
      rw [map_smul, Matrix.smul_apply, Phi_apply, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_apply, if_neg hσ, smul_eq_mul, mul_zero])]
  rw [map_smul, Matrix.smul_apply, Phi_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_apply, if_pos rfl, smul_eq_mul, mul_one]

/-- **Algebra-level Penrose certificate.** Transport the matrix certificate `penrose`
along the injective left-regular embedding `Φ = toMatrixAlgEquiv ∘ Algebra.lmul`
(`hPhiG`, `hPhiW` identify `Φ(gram) = G`, `Φ(Wcell) = W`, since `N ^ cycleCount` and
`wval` are inverse-symmetric class functions). Blueprint: `thm:penrose_alg`. -/
theorem penrose_alg : IsPenrosePair (gram ℚ 3 2) Wcell := by
  have hinj : Function.Injective Phi :=
    (LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne).injective.comp Algebra.lmul_injective
  refine ⟨hinj ?_, hinj ?_⟩
  · rw [map_mul, map_mul, hPhiG, hPhiW]; exact penrose.1
  · rw [map_mul, map_mul, hPhiG, hPhiW]; exact penrose.2.1

/-- Uniqueness characterization: any transpose-form Penrose solution for `G` equals `W` —
the certified values are *the* `(2,3)` Weingarten data. Blueprint: `cor:cell_unique`. -/
theorem pseudoinverse_unique (X : Matrix (Perm (Fin 3)) (Perm (Fin 3)) ℚ)
    (hX : G * X * G = G ∧ X * G * X = X ∧ (G * X)ᵀ = G * X ∧ (X * G)ᵀ = X * G) :
    X = W :=
  penrose_unique G X W hX penrose

/-! ### Coherence of the augmentation and sign characters on `Wcell` -/

theorem aug_of (σ : Perm (Fin 3)) :
    aug ℚ 3 (MonoidAlgebra.of ℚ (Perm (Fin 3)) σ) = 1 := by
  rw [aug, MonoidAlgebra.lift_of, MonoidHom.one_apply]
theorem aug_Wcell : aug ℚ 3 Wcell = ∑ σ : Perm (Fin 3), wval σ := by
  rw [Wcell, map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_smul, aug_of, smul_eq_mul, mul_one]
theorem sgnHom_Wcell :
    sgnHom ℚ 3 Wcell = ∑ σ : Perm (Fin 3), ((Equiv.Perm.sign σ : ℤ) : ℚ) * wval σ := by
  rw [Wcell, map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_smul, sgnHom_of, smul_eq_mul, mul_comm]

/-- Coherence: the cell's sum rules through the augmentation and sign characters of the
group-algebra certificate. The sign rule is the genuine below-threshold value (the falling
factorial vanishes, so the conditional falling rule degenerates to `0`).
Blueprint: `cor:cell_rules` (check B4). -/
theorem row_sums_of_penrose :
    aug ℚ 3 Wcell = 1 / 24 ∧ sgnHom ℚ 3 Wcell = 0 :=
  ⟨by rw [aug_Wcell, sum_wval], by rw [sgnHom_Wcell, sum_sgn_wval]⟩

/-- The certified below-threshold average-sign anchor `3/17`.
Blueprint: `prop:avg_sign` (check B4). -/
theorem avg_sign :
    (∑ σ : Perm (Fin 3), wval σ) / (∑ σ : Perm (Fin 3), |wval σ|) = 3 / 17 := by
  rw [sum_wval, sum_abs_wval]; norm_num

/-- Concrete sign-flip witness: a transposition with *positive* Weingarten value.
Blueprint: `prop:sign_flip`. -/
theorem sign_flip :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 ∧ 0 < wval (Equiv.swap 0 1) := by
  have hs : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := Equiv.Perm.sign_swap (by decide)
  refine ⟨hs, ?_⟩
  rw [wval, if_neg (by decide), if_pos hs]; norm_num

/-- The Gram element at `(N, n) = (2, 3)` is not a unit (instance of
`Weingarten.not_isUnit_gram`; numerically `det G = 0`, check B3b).
Blueprint: `cor:gram_two_singular`. -/
theorem gram_two_not_isUnit : ¬ IsUnit (gram ℚ 3 (2 : ℚ)) := by
  have h := not_isUnit_gram (n := 3) (N := 2) (by norm_num) (by norm_num)
  simpa using h

end Weingarten.Cell23
