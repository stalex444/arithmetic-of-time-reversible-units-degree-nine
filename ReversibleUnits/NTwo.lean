module
public import Mathlib
public import ReversibleUnits.HadamardInverse

@[expose] public section
/-!
# The `n = 2` contrast: reversible units of a quartic field of signature `(2, 1)`

For a number field `K` with two real places `w₁, w₂` and one complex place `σ` (labellings
`e₁ : {real places} ≃ Fin 2`, `e₂ : {complex places} ≃ Fin 1`; the shape of `ℚ(Q)`), the
`2 × 2` place symbol of `x ∈ K` is

  `X(x) = [[x_{w₁}, conj σ(x)], [σ(x), x_{w₂}]]`

(`quarticSymbol`; it is the matrix `minkowskiToHerm e₁ e₂ (mixedEmbedding K x)` of
`HermitianExclusion/UnitSchur.lean`, by `minkowskiToHerm_apply` there — carried here directly so
that this file is Mathlib-only).

Ported from `HermitianExclusion` (UnitSchur.lean `section Quartic`, CPTick.lean
`section OneDirection`; kernel there): `placeMatrix_posSemidef_iff` (Sylvester's `2 × 2`
criterion), `prod_places_two` (product formula), `posMap_iff_norm_le_one`, `one_direction_xor`,
`unit_one_direction_xor`.

New in this file:
* `unit_both_cp_iff`: for a unit `u`, both Schur multipliers `T_u` and `T_{u⁻¹}` are completely
  positive iff `u` is totally positive and `‖σ(u)‖ = 1`.
* `unit_both_cp_iff_rankOne`: the same condition is "`X(u)` is rank one" — the `n = 2` instance of
  `isCPSchur_and_isCPSchur_hadamardInv_iff`, since `X(u⁻¹)` is the Hadamard inverse of `X(u)`.

So for `n = 2` a reversible unit needs `‖σ(u)‖ = 1` (a Salem-type condition); the degree-nine
compositum construction is the `n = 3` contrast. No concrete field is treated here (the `ℚ(Q)`
instance follows from statement 17 of PALOMAR-2026-10-21-000012 with `unit_one_direction_xor`; not
proved here).
-/

namespace ReversibleUnits

open Matrix ComplexConjugate NumberField NumberField.InfinitePlace
open scoped ComplexOrder

/-! ### The `2 × 2` place matrix -/

/-- The place matrix `[[a, conj z], [z, b]]`. -/
def placeMatrix (a b : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), conj z; z, (b : ℂ)]

theorem placeMatrix_isHermitian (a b : ℝ) (z : ℂ) : (placeMatrix a b z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [placeMatrix, conjTranspose_apply]

/-- The Hadamard inverse of a place matrix is the place matrix of the inverses. -/
theorem hadamardInv_placeMatrix (a b : ℝ) (z : ℂ) :
    (Matrix.of fun i j => (placeMatrix a b z i j)⁻¹) = placeMatrix a⁻¹ b⁻¹ z⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [placeMatrix]

/-- Sylvester's criterion for the `2 × 2` place matrix `[[a, conj z], [z, b]]`:
positive semidefinite iff `0 ≤ a`, `0 ≤ b`, `|z|² ≤ ab`. (Ported from UnitSchur.lean.) -/
theorem placeMatrix_posSemidef_iff (a b : ℝ) (z : ℂ) :
    (placeMatrix a b z).PosSemidef ↔ 0 ≤ a ∧ 0 ≤ b ∧ ‖z‖ ^ 2 ≤ a * b := by
  constructor
  · intro h
    have ha := re_diag_nonneg_of_posSemidef h 0
    have hb := re_diag_nonneg_of_posSemidef h 1
    have hz := norm_sq_le_mul_re_diag_of_posSemidef h 1 0
    simp [placeMatrix] at ha hb hz
    rw [mul_comm] at hz
    exact ⟨ha, hb, hz⟩
  · rintro ⟨ha, hb, hz⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg (placeMatrix_isHermitian a b z) fun v => ?_
    have hform : star v ⬝ᵥ (placeMatrix a b z *ᵥ v) =
        conj (v 0) * ((a : ℂ) * v 0 + conj z * v 1) + conj (v 1) * (z * v 0 + (b : ℂ) * v 1) := by
      simp [dotProduct, mulVec, Fin.sum_univ_two, placeMatrix]
    rw [hform, Complex.nonneg_iff]
    have him : (conj (v 0) * ((a : ℂ) * v 0 + conj z * v 1) +
        conj (v 1) * (z * v 0 + (b : ℂ) * v 1)).im = 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hre : (conj (v 0) * ((a : ℂ) * v 0 + conj z * v 1) +
        conj (v 1) * (z * v 0 + (b : ℂ) * v 1)).re =
        a * ‖v 0‖ ^ 2 + b * ‖v 1‖ ^ 2 + 2 * (conj (v 0) * conj z * v 1).re := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    refine ⟨?_, him.symm⟩
    rw [hre]
    have hcross : -(‖v 0‖ * ‖z‖ * ‖v 1‖) ≤ (conj (v 0) * conj z * v 1).re := by
      have := Complex.abs_re_le_norm (conj (v 0) * conj z * v 1)
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj] at this
      exact (abs_le.mp this).1
    have hP := norm_nonneg (v 0)
    have hR := norm_nonneg (v 1)
    have hr := norm_nonneg z
    have hamgm : 2 * (‖z‖ * ‖v 0‖ * ‖v 1‖) ≤ a * ‖v 0‖ ^ 2 + b * ‖v 1‖ ^ 2 := by
      rcases ha.lt_or_eq with ha' | ha'
      · have key : a * (a * ‖v 0‖ ^ 2 + b * ‖v 1‖ ^ 2 - 2 * (‖z‖ * ‖v 0‖ * ‖v 1‖)) =
            (a * ‖v 0‖ - ‖z‖ * ‖v 1‖) ^ 2 + (a * b - ‖z‖ ^ 2) * ‖v 1‖ ^ 2 := by ring
        have hkey : 0 ≤ a * (a * ‖v 0‖ ^ 2 + b * ‖v 1‖ ^ 2 - 2 * (‖z‖ * ‖v 0‖ * ‖v 1‖)) := by
          rw [key]
          exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg _))
        have := nonneg_of_mul_nonneg_right hkey ha'
        linarith
      · subst ha'
        have hz0 : ‖z‖ = 0 := by nlinarith
        rw [hz0]
        nlinarith
    nlinarith

/-! ### The generic one-direction theorem (ported from CPTick.lean) -/

/-- For a totally positive triple of norm one, the symbol is positive iff `‖z‖ ≤ 1`. -/
theorem posMap_iff_norm_le_one {a b : ℝ} {z : ℂ} (ha : 0 < a) (hb : 0 < b)
    (hn : a * b * ‖z‖ ^ 2 = 1) :
    IsPositiveMap (schurMul (placeMatrix a b z)) ↔ ‖z‖ ≤ 1 := by
  rw [isPositiveMap_schurMul_iff, placeMatrix_posSemidef_iff]
  have hab : 0 < a * b := mul_pos ha hb
  have hr := norm_nonneg z
  constructor
  · rintro ⟨-, -, h⟩
    have h4 : ‖z‖ ^ 2 * ‖z‖ ^ 2 ≤ 1 := by
      calc ‖z‖ ^ 2 * ‖z‖ ^ 2 ≤ a * b * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ = 1 := hn
    nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1)]
  · intro h
    refine ⟨ha.le, hb.le, ?_⟩
    have hr2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith

/-- **The exactly-one clause (generic).** For `0 < a`, `0 < b`, `ab‖z‖² = 1` and `‖z‖ ≠ 1`,
exactly one of the symbols `(a, b, z)` and `(a⁻¹, b⁻¹, z⁻¹)` is positive. -/
theorem one_direction_xor {a b : ℝ} {z : ℂ} (ha : 0 < a) (hb : 0 < b)
    (hn : a * b * ‖z‖ ^ 2 = 1) (hz1 : ‖z‖ ≠ 1) :
    Xor (IsPositiveMap (schurMul (placeMatrix a b z)))
      (IsPositiveMap (schurMul (placeMatrix a⁻¹ b⁻¹ z⁻¹))) := by
  have hz0 : 0 < ‖z‖ := by
    rcases (norm_nonneg z).lt_or_eq with h | h
    · exact h
    · rw [← h] at hn; norm_num at hn
  have hn' : a⁻¹ * b⁻¹ * ‖z⁻¹‖ ^ 2 = 1 := by
    rw [norm_inv, inv_pow, ← mul_inv, ← mul_inv, hn, inv_one]
  rw [posMap_iff_norm_le_one ha hb hn,
    posMap_iff_norm_le_one (inv_pos.mpr ha) (inv_pos.mpr hb) hn', norm_inv, inv_le_one₀ hz0]
  rcases lt_or_gt_of_ne hz1 with h | h
  · exact Or.inl ⟨h.le, not_le.mpr h⟩
  · exact Or.inr ⟨h.le, not_le.mpr h⟩

/-- **Both directions (generic).** For `0 < a`, `0 < b`, `ab‖z‖² = 1`: both symbols `(a, b, z)`
and `(a⁻¹, b⁻¹, z⁻¹)` are positive iff `‖z‖ = 1`. -/
theorem both_posMap_iff_norm_eq_one {a b : ℝ} {z : ℂ} (ha : 0 < a) (hb : 0 < b)
    (hn : a * b * ‖z‖ ^ 2 = 1) :
    IsPositiveMap (schurMul (placeMatrix a b z)) ∧
        IsPositiveMap (schurMul (placeMatrix a⁻¹ b⁻¹ z⁻¹)) ↔ ‖z‖ = 1 := by
  have hz0 : 0 < ‖z‖ := by
    rcases (norm_nonneg z).lt_or_eq with h | h
    · exact h
    · rw [← h] at hn; norm_num at hn
  have hn' : a⁻¹ * b⁻¹ * ‖z⁻¹‖ ^ 2 = 1 := by
    rw [norm_inv, inv_pow, ← mul_inv, ← mul_inv, hn, inv_one]
  rw [posMap_iff_norm_le_one ha hb hn,
    posMap_iff_norm_le_one (inv_pos.mpr ha) (inv_pos.mpr hb) hn', norm_inv, inv_le_one₀ hz0]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-! ### Units of a field of signature `(2, 1)` -/

section Units

variable {K : Type*} [Field K] [NumberField K]
  (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
  (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1)

/-- The `2 × 2` place symbol `X(x) = [[x_{w₁}, conj σ(x)], [σ(x), x_{w₂}]]` (equal to UnitSchur's
`minkowskiToHerm e₁ e₂ (mixedEmbedding K x)`). -/
noncomputable def quarticSymbol (x : K) : Matrix (Fin 2) (Fin 2) ℂ :=
  placeMatrix (embedding_of_isReal (e₁.symm 0).2 x) (embedding_of_isReal (e₁.symm 1).2 x)
    (embedding (e₂.symm 0).1 x)

omit [NumberField K] in
/-- The symbol of `x⁻¹` is the Hadamard inverse of the symbol of `x`. -/
theorem quarticSymbol_inv (x : K) :
    quarticSymbol e₁ e₂ x⁻¹ = Matrix.of fun i j => (quarticSymbol e₁ e₂ x i j)⁻¹ := by
  rw [quarticSymbol, quarticSymbol, hadamardInv_placeMatrix, map_inv₀, map_inv₀, map_inv₀]

/-- The product formula for the shape `(2, 1)`: `|x|_{w₁} |x|_{w₂} |x|_σ² = |N(x)|`.
(Ported from UnitSchur.lean.) -/
theorem prod_places_two (x : K) :
    ‖embedding_of_isReal (e₁.symm 0).2 x‖ * ‖embedding_of_isReal (e₁.symm 1).2 x‖ *
      ‖embedding (e₂.symm 0).1 x‖ ^ 2 = |Algebra.norm ℚ x| := by
  classical
  have h := prod_eq_abs_norm x
  rw [prod_eq_prod_mul_prod, ← Equiv.prod_comp e₁.symm, ← Equiv.prod_comp e₂.symm,
    Fin.prod_univ_two, Fin.prod_univ_one] at h
  simp only [mult_isReal, mult_isComplex, pow_one] at h
  rw [← h, norm_embedding_of_isReal, norm_embedding_of_isReal, norm_embedding_eq]

/-- **The exactly-one clause for units** (ported from CPTick.lean). For a totally positive unit
`u` with `‖σ(u)‖ ≠ 1`, exactly one of `T_u`, `T_{u⁻¹}` is completely positive. -/
theorem unit_one_direction_xor (u : (𝓞 K)ˣ)
    (h₁ : 0 < embedding_of_isReal (e₁.symm 0).2 (u : K))
    (h₂ : 0 < embedding_of_isReal (e₁.symm 1).2 (u : K))
    (hS : ‖embedding (e₂.symm 0).1 (u : K)‖ ≠ 1) :
    Xor (IsCPSchur (quarticSymbol e₁ e₂ (u : K))) (IsCPSchur (quarticSymbol e₁ e₂ (u : K)⁻¹)) := by
  rw [isCPSchur_iff_isPositiveMap, isCPSchur_iff_isPositiveMap, quarticSymbol, quarticSymbol,
    map_inv₀, map_inv₀, map_inv₀]
  have hprod := prod_places_two e₁ e₂ (u : K)
  rw [Units.norm, Rat.cast_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h₁,
    abs_of_pos h₂] at hprod
  exact one_direction_xor h₁ h₂ hprod hS

/-- **Statement 10, the `n = 2` contrast.** For a unit `u` of a number field of signature `(2, 1)`, both
Schur multipliers `T_u` and `T_{u⁻¹}` on `2 × 2` matrices are completely positive iff `u` is
positive at both real places and `‖σ(u)‖ = 1`. -/
theorem unit_both_cp_iff (u : (𝓞 K)ˣ) :
    IsCPSchur (quarticSymbol e₁ e₂ (u : K)) ∧ IsCPSchur (quarticSymbol e₁ e₂ (u : K)⁻¹) ↔
      0 < embedding_of_isReal (e₁.symm 0).2 (u : K) ∧
        0 < embedding_of_isReal (e₁.symm 1).2 (u : K) ∧
          ‖embedding (e₂.symm 0).1 (u : K)‖ = 1 := by
  set a := embedding_of_isReal (e₁.symm 0).2 (u : K) with ha
  set b := embedding_of_isReal (e₁.symm 1).2 (u : K) with hb
  set z := embedding (e₂.symm 0).1 (u : K) with hz
  have hprod : ‖a‖ * ‖b‖ * ‖z‖ ^ 2 = 1 := by
    rw [ha, hb, hz, prod_places_two, Units.norm, Rat.cast_one]
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, norm_zero, zero_mul, zero_mul] at hprod; exact zero_ne_one hprod
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0, norm_zero, mul_zero, zero_mul] at hprod; exact zero_ne_one hprod
  have hsym : quarticSymbol e₁ e₂ (u : K)⁻¹ = placeMatrix a⁻¹ b⁻¹ z⁻¹ := by
    rw [quarticSymbol, map_inv₀, map_inv₀, map_inv₀]
  rw [hsym, quarticSymbol, ← ha, ← hb, ← hz, isCPSchur_iff_isPositiveMap,
    isCPSchur_iff_isPositiveMap]
  constructor
  · intro h
    have h1 := (isPositiveMap_schurMul_iff.mp h.1)
    rw [placeMatrix_posSemidef_iff] at h1
    have ha1 : 0 < a := lt_of_le_of_ne h1.1 (Ne.symm ha0)
    have hb1 : 0 < b := lt_of_le_of_ne h1.2.1 (Ne.symm hb0)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha1, abs_of_pos hb1] at hprod
    exact ⟨ha1, hb1, (both_posMap_iff_norm_eq_one ha1 hb1 hprod).mp h⟩
  · rintro ⟨ha1, hb1, h⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha1, abs_of_pos hb1] at hprod
    exact (both_posMap_iff_norm_eq_one ha1 hb1 hprod).mpr h

omit [NumberField K] in
/-- **Statement 10, rank-one form.** For a unit `u` of a number field of signature `(2, 1)`, both `T_u` and
`T_{u⁻¹}` are completely positive iff the place symbol `X(u)` is rank one, `X(u) = w w*` — the
`n = 2` instance of `isCPSchur_and_isCPSchur_hadamardInv_iff`. -/
theorem unit_both_cp_iff_rankOne (u : (𝓞 K)ˣ) :
    IsCPSchur (quarticSymbol e₁ e₂ (u : K)) ∧ IsCPSchur (quarticSymbol e₁ e₂ (u : K)⁻¹) ↔
      ∃ w : Fin 2 → ℂ, quarticSymbol e₁ e₂ (u : K) = vecMulVec w (star w) := by
  have hu : (u : K) ≠ 0 := NumberField.Units.coe_ne_zero u
  have h0 : ∀ i j, quarticSymbol e₁ e₂ (u : K) i j ≠ 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [quarticSymbol, placeMatrix, hu]
  rw [quarticSymbol_inv]
  exact isCPSchur_and_isCPSchur_hadamardInv_iff h0

end Units

end ReversibleUnits
