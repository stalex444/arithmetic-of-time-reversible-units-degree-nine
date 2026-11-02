module
public import Mathlib
public import Challenge
public import ReversibleUnits

@[expose] public section
/-!
# Audit of the entry's definitions

The compared statements in `Challenge.lean` use Mathlib's vocabulary (pinned revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`) and four definitions added by the entry:
`DegreeNine.IsPositiveMap`, `DegreeNine.schurAmp`, `DegreeNine.IsCPSchur` and
`DegreeNine.IsSlotAssignment`. This file is not part of the compared set. It imports
`Challenge` (for exactly those four definitions; no theorem of `Challenge` is used, and every
theorem below depends only on `propext`, `Quot.sound`, `Classical.choice`) and the proof library
`ReversibleUnits`. It records, as kernel-checked theorems, the facts about the four definitions
that the informal account relies on:

* `isPositiveMap_iff`, `schurAmp_apply`, `isCPSchur_iff` — the definitions unfold as stated: a
  positive map preserves positive semidefiniteness; the `k`-th ampliation multiplies the block
  entry at `((a, i), (b, j))` by `S i j`; `IsCPSchur S` is "every ampliation is positive".
* `isCPSchur_iff_posSemidef` — Paulsen's theorem (2002, Thm 3.7): over a finite index type,
  `IsCPSchur S ↔ S.PosSemidef`. So the complete positivity in statements 2 and 8–10 is the
  positive semidefiniteness of the symbol.
* `isCPSchur_iff_isPositiveMap_hadamard` — the ampliation form agrees with the plain positivity
  of `X ↦ S ⊙ X` (for Schur multipliers, positive ⟺ completely positive).
* `isCPSchur_allOnes`, `not_isCPSchur_neg_one` — non-vacuity: the all-ones symbol is completely
  positive, the `1 × 1` symbol `-1` is not.
* `eq_vecMulVec_star_iff` — `X = vecMulVec w (star w)` means `X i j = w i * conj (w j)` (the
  rank-one form of statements 1, 2, 5, 6).
* `exists_lab_and_not_isReal` — the data of statements 4–9 exist: for `M` cubic with one real
  place there is a non-real embedding `μ₁`, and every cubic `L` has a labelling
  `Fin 3 ≃ (L →+* ℂ)`.
* `exists_isSlotAssignment`, `isSlotAssignment_unique`, `bijective_of_isSlotAssignment` — for
  every labelling and every non-real `μ₁`, a slot assignment exists, any two coincide, and a slot
  assignment is a bijection `Fin 3 × Fin 3 → (K →+* ℂ)` (so the hypothesis `he` of statements 5–9
  fixes `e` and is satisfiable).
* `isReal_diag_of_isSlotAssignment`, `conjugate_of_isSlotAssignment`,
  `symbol_isHermitian` — the diagonal slots are real embeddings, slot `(j, i)` is the conjugate of
  slot `(i, j)`, and hence the symbol `Matrix.of fun i j => e (i, j) x` is Hermitian.
* `symbol_mul`, `symbol_inv`, `symbol_units_inv` — the symbol is multiplicative for the Hadamard
  product, the symbol of `x⁻¹` is the entrywise (Hadamard) inverse of the symbol of `x`, and the
  coercion of the unit `u⁻¹` is `(u : K)⁻¹` (the form used in statements 8, 9).
* `symbol_ne_zero` — the symbol of `x ≠ 0` has no zero entry (the hypothesis `h0` of statements
  1, 2 holds for symbols).
* `quarticSymbol_isHermitian`, `quarticSymbol_inv` — the `2 × 2` matrix of statement 10 is
  Hermitian, and the second matrix there is the Hadamard inverse of the first.
* `mem_relNormSet_iff` — the set in statement 7 is the set of units with
  `N_{K/L} u = N_{K/M} u = 1` (the library's `relNormKernel`), a subgroup.
-/

open Matrix ComplexConjugate NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
  NumberField.Units Module
open scoped ComplexOrder

namespace DefinitionAudit

/-! ### Positive maps, ampliations, complete positivity -/

section Schur

variable {ι : Type*}

/-- `IsPositiveMap Φ` unfolds as stated. -/
theorem isPositiveMap_iff (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    DegreeNine.IsPositiveMap Φ ↔ ∀ X : Matrix ι ι ℂ, X.PosSemidef → (Φ X).PosSemidef := Iff.rfl

/-- The `k`-th ampliation multiplies the block entry at `((a, i), (b, j))` by `S i j`. -/
theorem schurAmp_apply (k : ℕ) (S : Matrix ι ι ℂ) (X : Matrix (Fin k × ι) (Fin k × ι) ℂ)
    (a b : Fin k) (i j : ι) :
    DegreeNine.schurAmp k S X (a, i) (b, j) = S i j * X (a, i) (b, j) := rfl

/-- `IsCPSchur S` unfolds as stated. -/
theorem isCPSchur_iff (S : Matrix ι ι ℂ) :
    DegreeNine.IsCPSchur S ↔ ∀ k : ℕ, DegreeNine.IsPositiveMap (DegreeNine.schurAmp k S) :=
  Iff.rfl

/-- `DegreeNine.IsCPSchur` is the library's `ReversibleUnits.IsCPSchur` (same body). -/
theorem isCPSchur_iff_library (S : Matrix ι ι ℂ) :
    DegreeNine.IsCPSchur S ↔ ReversibleUnits.IsCPSchur S := Iff.rfl

variable [Fintype ι]

/-- **Paulsen 2002, Thm 3.7.** The Schur multiplier `T_S` is completely positive iff `S` is
positive semidefinite. -/
theorem isCPSchur_iff_posSemidef (S : Matrix ι ι ℂ) :
    DegreeNine.IsCPSchur S ↔ S.PosSemidef :=
  ReversibleUnits.isCPSchur_iff_posSemidef

/-- For Schur multipliers, complete positivity (ampliation form) is plain positivity of
`X ↦ S ⊙ X`. -/
theorem isCPSchur_iff_isPositiveMap_hadamard (S : Matrix ι ι ℂ) :
    DegreeNine.IsCPSchur S ↔ DegreeNine.IsPositiveMap (fun X : Matrix ι ι ℂ => S ⊙ X) :=
  ReversibleUnits.isCPSchur_iff_isPositiveMap

/-- Non-vacuity: the all-ones symbol is completely positive. -/
theorem isCPSchur_allOnes : DegreeNine.IsCPSchur (Matrix.of fun _ _ : ι => (1 : ℂ)) :=
  (isCPSchur_iff_posSemidef _).mpr (ReversibleUnits.posSemidef_allOnes ι)

/-- Non-vacuity: the `1 × 1` symbol `-1` is not completely positive. -/
theorem not_isCPSchur_neg_one : ¬DegreeNine.IsCPSchur (Matrix.of fun _ _ : Fin 1 => (-1 : ℂ)) := by
  rw [isCPSchur_iff_posSemidef]
  intro h
  have h0 := ReversibleUnits.re_diag_nonneg_of_posSemidef h 0
  norm_num at h0

omit [Fintype ι] in
/-- The rank-one form: `X = w w*` entrywise. -/
theorem eq_vecMulVec_star_iff (X : Matrix ι ι ℂ) (w : ι → ℂ) :
    X = vecMulVec w (star w) ↔ ∀ i j, X i j = w i * conj (w j) :=
  ReversibleUnits.eq_vecMulVec_star_iff

end Schur

/-! ### Slot assignments -/

section Slot

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

/-- The data of statements 4–9 exist: a labelling of the embeddings of a cubic `L` and a non-real
embedding of a cubic `M` with one real place. -/
theorem exists_lab_and_not_isReal (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hMr : nrRealPlaces M = 1) :
    Nonempty (Fin 3 ≃ (L →+* ℂ)) ∧ ∃ μ₁ : M →+* ℂ, ¬ComplexEmbedding.IsReal μ₁ :=
  ⟨⟨(Fintype.equivFinOfCardEq (by rw [Embeddings.card, hL])).symm⟩,
    ReversibleUnits.exists_not_isReal hM hMr⟩

/-- A number field with exactly one real place has exactly one real embedding. -/
theorem eq_of_isReal_of_isReal {F : Type*} [Field F] [NumberField F]
    (hF : nrRealPlaces F = 1) {φ ψ : F →+* ℂ} (hφ : ComplexEmbedding.IsReal φ)
    (hψ : ComplexEmbedding.IsReal ψ) : φ = ψ := by
  classical
  have h := card_real_embeddings (K := F)
  rw [hF] at h
  exact congrArg Subtype.val
    (Fintype.card_le_one_iff.mp (le_of_eq h) (⟨φ, hφ⟩ : {φ : F →+* ℂ // IsReal φ}) ⟨ψ, hψ⟩)

/-- Any two slot assignments coincide (`K = L ⊔ M`, and `M` has one real embedding). -/
theorem isSlotAssignment_unique (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1)
    (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ) {f g : Fin 3 × Fin 3 → (K →+* ℂ)}
    (hf : DegreeNine.IsSlotAssignment lab μ₁ f) (hg : DegreeNine.IsSlotAssignment lab μ₁ g) :
    f = g := by
  funext p
  obtain ⟨i, j⟩ := p
  apply ReversibleUnits.restrictPair_injective (ReversibleUnits.sup_eq_top_of_hyp hL hM hK hMr)
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf i j
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg i j
  refine Prod.ext (by simp only [ReversibleUnits.restrictPair_fst, hf1, hg1]) ?_
  simp only [ReversibleUnits.restrictPair_snd]
  have htri : ∀ i j : Fin 3, i = j ∨ j = i + 1 ∨ i = j + 1 := by decide
  rcases htri i j with h | h | h
  · exact eq_of_isReal_of_isReal hMr (hf2 h) (hg2 h)
  · rw [hf3 h, hg3 h]
  · rw [hf4 h, hg4 h]

variable (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
  (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
  (hμ₁ : ¬ComplexEmbedding.IsReal μ₁)

/-- The library's slot bijection is a slot assignment. -/
theorem isSlotAssignment_slotEquiv :
    DegreeNine.IsSlotAssignment lab μ₁ (ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁) := by
  intro i j
  simp only [ReversibleUnits.slotEquiv_apply, ReversibleUnits.pairEmb_comp_left,
    ReversibleUnits.pairEmb_comp_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · congr 1
    fin_cases i <;> fin_cases j <;> rfl
  · rintro rfl
    have h : (ReversibleUnits.slotTable (i, i)).2 = 0 := by fin_cases i <;> rfl
    rw [h]
    exact ReversibleUnits.isReal_realEmb hMr
  · rintro rfl
    have h : (ReversibleUnits.slotTable (i, i + 1)).2 = 1 := by fin_cases i <;> rfl
    rw [h]
    rfl
  · rintro rfl
    have h : (ReversibleUnits.slotTable (j + 1, j)).2 = 2 := by fin_cases j <;> rfl
    rw [h]
    rfl

include hL hM hK hMr hμ₁ in
/-- Slot assignments exist. -/
theorem exists_isSlotAssignment :
    ∃ e : Fin 3 × Fin 3 → (K →+* ℂ), DegreeNine.IsSlotAssignment lab μ₁ e :=
  ⟨_, isSlotAssignment_slotEquiv hL hM hK hMr lab μ₁ hμ₁⟩

variable {lab μ₁} in
theorem eq_slotEquiv_of_isSlotAssignment {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : DegreeNine.IsSlotAssignment lab μ₁ e) :
    e = ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁ :=
  isSlotAssignment_unique hL hM hK hMr lab μ₁ he
    (isSlotAssignment_slotEquiv hL hM hK hMr lab μ₁ hμ₁)

include hL hM hK hMr hμ₁ in
variable {lab μ₁} in
/-- A slot assignment is a bijection onto the nine embeddings of `K`. -/
theorem bijective_of_isSlotAssignment {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : DegreeNine.IsSlotAssignment lab μ₁ e) : Function.Bijective e := by
  rw [eq_slotEquiv_of_isSlotAssignment hL hM hK hMr hμ₁ he]
  exact (ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁).bijective

include hL hM hK hMr hμ₁ in
variable {lab μ₁} in
/-- The diagonal slots of a slot assignment are real embeddings of `K`. -/
theorem isReal_diag_of_isSlotAssignment {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : DegreeNine.IsSlotAssignment lab μ₁ e) (i : Fin 3) : ComplexEmbedding.IsReal (e (i, i)) := by
  rw [eq_slotEquiv_of_isSlotAssignment hL hM hK hMr hμ₁ he]
  exact ReversibleUnits.slotEquiv_diag_isReal hL hM hK hMr lab μ₁ hμ₁ i

include hL hM hK hMr hμ₁ in
variable {lab μ₁} in
/-- Slot `(j, i)` of a slot assignment is the complex conjugate of slot `(i, j)`. -/
theorem conjugate_of_isSlotAssignment {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : DegreeNine.IsSlotAssignment lab μ₁ e) (i j : Fin 3) :
    e (j, i) = conjugate (e (i, j)) := by
  rw [eq_slotEquiv_of_isSlotAssignment hL hM hK hMr hμ₁ he]
  exact ReversibleUnits.slotEquiv_swap hL hM hK hMr lab μ₁ hμ₁ i j

include hL hM hK hMr hμ₁ in
variable {lab μ₁} in
/-- The symbol of `x` for a slot assignment is Hermitian. -/
theorem symbol_isHermitian {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : DegreeNine.IsSlotAssignment lab μ₁ e) (x : K) :
    (Matrix.of fun i j => e (i, j) x).IsHermitian := by
  ext i j
  rw [conjTranspose_apply, of_apply, of_apply, conjugate_of_isSlotAssignment hL hM hK hMr hμ₁ he,
    ComplexEmbedding.conjugate_coe_eq, Complex.star_def, Complex.conj_conj]

end Slot

/-! ### The symbol: Hadamard product, Hadamard inverse, nonzero entries -/

section Symbol

variable {K : Type*} [Field K] (e : Fin 3 × Fin 3 → (K →+* ℂ))

/-- The symbol is multiplicative for the Hadamard product (any family of embeddings). -/
theorem symbol_mul (x y : K) :
    (Matrix.of fun i j => e (i, j) (x * y)) =
      (Matrix.of fun i j => e (i, j) x) ⊙ (Matrix.of fun i j => e (i, j) y) := by
  ext i j
  simp only [of_apply, map_mul, hadamard_apply]

/-- The symbol of `x⁻¹` is the Hadamard inverse of the symbol of `x`. -/
theorem symbol_inv (x : K) :
    (Matrix.of fun i j => e (i, j) x⁻¹) = Matrix.of fun i j => ((Matrix.of fun i j => e (i, j) x)
      i j)⁻¹ := by
  ext i j
  simp only [of_apply, map_inv₀]

/-- The symbol of a nonzero element has no zero entry. -/
theorem symbol_ne_zero {x : K} (hx : x ≠ 0) (i j : Fin 3) :
    (Matrix.of fun i j => e (i, j) x) i j ≠ 0 := by
  rw [of_apply]
  exact (map_ne_zero _).mpr hx

/-- The coercion of the inverse unit is the inverse of the coercion. -/
theorem symbol_units_inv [NumberField K] (u : (𝓞 K)ˣ) : ((u⁻¹ : (𝓞 K)ˣ) : K) = (u : K)⁻¹ :=
  ReversibleUnits.coe_units_inv_eq u

end Symbol

/-! ### The `2 × 2` symbol of statement 10 -/

section Quartic

variable {K : Type*} [Field K]
  (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
  (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1)

/-- The matrix of statement 10 is Hermitian. -/
theorem quarticSymbol_isHermitian (x : K) :
    (!![((embedding_of_isReal (e₁.symm 0).2 x : ℝ) : ℂ), conj (embedding (e₂.symm 0).1 x);
      embedding (e₂.symm 0).1 x, ((embedding_of_isReal (e₁.symm 1).2 x : ℝ) : ℂ)]).IsHermitian :=
  ReversibleUnits.placeMatrix_isHermitian _ _ _

/-- The second matrix of statement 10 is the Hadamard inverse of the first. -/
theorem quarticSymbol_inv (x : K) :
    !![((embedding_of_isReal (e₁.symm 0).2 x⁻¹ : ℝ) : ℂ), conj (embedding (e₂.symm 0).1 x⁻¹);
      embedding (e₂.symm 0).1 x⁻¹, ((embedding_of_isReal (e₁.symm 1).2 x⁻¹ : ℝ) : ℂ)] =
    Matrix.of fun i j =>
      (!![((embedding_of_isReal (e₁.symm 0).2 x : ℝ) : ℂ), conj (embedding (e₂.symm 0).1 x);
        embedding (e₂.symm 0).1 x, ((embedding_of_isReal (e₁.symm 1).2 x : ℝ) : ℂ)] i j)⁻¹ :=
  ReversibleUnits.quarticSymbol_inv e₁ e₂ x

end Quartic

/-! ### The set of statement 7 -/

section RelNorm

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

/-- The set of statement 7 is the library's subgroup `relNormKernel L M` of units with
`N_{K/L} u = N_{K/M} u = 1`, read through `Additive`. -/
theorem mem_relNormSet_iff (x : Additive (𝓞 K)ˣ) :
    x ∈ {x : Additive (𝓞 K)ˣ | Algebra.norm L ((x.toMul : (𝓞 K)ˣ) : K) = 1 ∧
      Algebra.norm M ((x.toMul : (𝓞 K)ˣ) : K) = 1} ↔
      x.toMul ∈ ReversibleUnits.relNormKernel L M :=
  ReversibleUnits.mem_relNormKernel.symm

end RelNorm

end DefinitionAudit
