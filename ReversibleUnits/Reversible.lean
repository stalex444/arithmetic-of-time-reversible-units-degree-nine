module
public import Mathlib
public import ReversibleUnits.HadamardInverse
public import ReversibleUnits.Compositum

@[expose] public section
/-!
# Reversible units of a degree-nine compositum

Assembly of `ReversibleUnits.Compositum` (the field part) and `ReversibleUnits.HadamardInverse`
(the Schur-multiplier part). For `K` of degree `9` with a totally real cubic subfield `L` and a
cubic subfield `M` with one real place, and the slot bijection `slotEquiv`, the **symbol** of
`x : K` is the `3 × 3` matrix `X(x) = (slotEquiv (i, j) x)`.

* `symbol_mul`: `X(x y) = X(x) ⊙ X(y)` (Hadamard product), and `symbol_inv`: `X(x⁻¹)` is the
  Hadamard inverse of `X(x)`.
* `reversible_iff`: for a unit `u`, both Schur multipliers `T_{X(u)}` and `T_{X(u⁻¹)}` are
  completely positive iff `u ∈ H`, i.e. `N_{K/L} u = N_{K/M} u = 1`.
* `exists_reversible`: there is a unit `u` of infinite order such that `T_{X(uⁿ)}` and
  `T_{X(u⁻ⁿ)}` are completely positive for every `n : ℤ`.
-/

open Module NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace NumberField.Units
  ComplexConjugate Matrix

namespace ReversibleUnits

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
  (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
  (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ) (hμ₁ : ¬IsReal μ₁)

/-- The symbol `X(x) = (slotEquiv (i, j) x)` of `x : K`. -/
noncomputable def symbol (x : K) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j) x

theorem symbol_apply (x : K) (i j : Fin 3) :
    symbol hL hM hK hMr lab μ₁ hμ₁ x i j = slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j) x := rfl

/-- The symbol is multiplicative for the Hadamard product. -/
theorem symbol_mul (x y : K) :
    symbol hL hM hK hMr lab μ₁ hμ₁ (x * y) =
      symbol hL hM hK hMr lab μ₁ hμ₁ x ⊙ symbol hL hM hK hMr lab μ₁ hμ₁ y := by
  ext i j
  simp only [symbol_apply, map_mul, hadamard_apply]

/-- The symbol of `x⁻¹` is the Hadamard inverse of the symbol of `x`. -/
theorem symbol_inv (x : K) :
    symbol hL hM hK hMr lab μ₁ hμ₁ x⁻¹ =
      Matrix.of fun i j => (symbol hL hM hK hMr lab μ₁ hμ₁ x i j)⁻¹ := by
  ext i j
  simp only [symbol_apply, map_inv₀, of_apply]

/-- **Reversible units.** For a unit `u`, both Schur multipliers `T_{X(u)}` and `T_{X(u⁻¹)}` are
completely positive iff `N_{K/L} u = 1` and `N_{K/M} u = 1`. -/
theorem reversible_iff (u : (𝓞 K)ˣ) :
    IsCPSchur (symbol hL hM hK hMr lab μ₁ hμ₁ (u : K)) ∧
        IsCPSchur (symbol hL hM hK hMr lab μ₁ hμ₁ ((u⁻¹ : (𝓞 K)ˣ) : K)) ↔
      u ∈ relNormKernel L M := by
  rw [coe_units_inv_eq, symbol_inv,
    isCPSchur_and_isCPSchur_hadamardInv_iff'
      (X := symbol hL hM hK hMr lab μ₁ hμ₁ (u : K)) (fun i j => by
        rw [symbol_apply]; exact (map_ne_zero _).mpr (coe_ne_zero u)),
    mem_relNormKernel, rankOne_iff hL hM hK hMr lab μ₁ hμ₁]
  rfl

/-- **Existence of reversible units.** There is a unit `u` of infinite order such that, for
every `n : ℤ`, both Schur multipliers `T_{X(uⁿ)}` and `T_{X(u⁻ⁿ)}` are completely positive. -/
theorem exists_reversible :
    ∃ u : (𝓞 K)ˣ, u ∉ torsion K ∧ ∀ n : ℤ,
      IsCPSchur (symbol hL hM hK hMr lab μ₁ hμ₁ ((u ^ n : (𝓞 K)ˣ) : K)) ∧
        IsCPSchur (symbol hL hM hK hMr lab μ₁ hμ₁ (((u ^ n)⁻¹ : (𝓞 K)ˣ) : K)) := by
  obtain ⟨u, hu, hu1⟩ := exists_mem_relNormKernel_ne_one hL hM hK hMr
  refine ⟨u, fun ht => hu1 ?_, fun n => ?_⟩
  · have h : u ∈ relNormKernel L M ⊓ torsion K := ⟨hu, ht⟩
    rw [relNormKernel_inf_torsion hL hK] at h
    exact h
  · exact (reversible_iff hL hM hK hMr lab μ₁ hμ₁ (u ^ n)).mpr (Subgroup.zpow_mem _ hu n)

end ReversibleUnits
