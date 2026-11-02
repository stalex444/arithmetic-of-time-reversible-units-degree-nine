module
public import Mathlib
public import ReversibleUnits

@[expose] public section
/-!
# Reversible units of a degree-nine field: proofs of the compared statements

Each of the ten statements of `Challenge.lean` is proved here, with the identical statement, by
transfer from the proof library `ReversibleUnits` (`HadamardInverse`, `NTwo`, `Compositum`,
`Reversible`). The four definitions of `Challenge.lean` are repeated verbatim.

* Statements 1, 2: `ReversibleUnits.posSemidef_hadamardInv_iff`,
  `ReversibleUnits.isCPSchur_and_isCPSchur_hadamardInv_iff` (`DegreeNine.IsCPSchur` and
  `ReversibleUnits.IsCPSchur` have the same body, so the transfer is definitional).
* Statement 3: `ReversibleUnits.sup_eq_top_of_hyp`, `ReversibleUnits.linearDisjoint_of_hyp`,
  `ReversibleUnits.places_compositum`.
* Statement 4: the library's `slotEquiv` is a slot assignment (`isSlotAssignment_slotEquiv`
  below), and any two slot assignments agree (`slotAssignment_unique` below: an embedding of `K` is
  determined by its restrictions to `L` and `M`, and `M` has exactly one real embedding).
* Statements 5–9: rewrite the given slot assignment to `slotEquiv` by uniqueness, then
  `ReversibleUnits.rankOne_iff_norm_eq_ratCast`, `ReversibleUnits.rankOne_iff`,
  `ReversibleUnits.relNormKernel_inf_torsion`,
  `ReversibleUnits.finrank_span_logEmbedding_relNormKernel`, `ReversibleUnits.reversible_iff`,
  `ReversibleUnits.exists_reversible`.
* Statement 10: `ReversibleUnits.unit_both_cp_iff` (`quarticSymbol` unfolds to the `!![…]` place
  matrix of the statement).
-/

open Matrix ComplexConjugate NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
  NumberField.Units Module
open scoped ComplexOrder

namespace DegreeNine

/-- A map on matrices is **positive** if it sends positive semidefinite matrices to positive
semidefinite matrices. -/
def IsPositiveMap {ι : Type*} (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop :=
  ∀ X : Matrix ι ι ℂ, X.PosSemidef → (Φ X).PosSemidef

/-- The `k`-th ampliation `id_k ⊗ T_S` of the Schur multiplier `T_S : X ↦ S ⊙ X`, on block
matrices indexed by `Fin k × ι`. -/
def schurAmp {ι : Type*} (k : ℕ) (S : Matrix ι ι ℂ) (X : Matrix (Fin k × ι) (Fin k × ι) ℂ) :
    Matrix (Fin k × ι) (Fin k × ι) ℂ :=
  (S.submatrix Prod.snd Prod.snd) ⊙ X

/-- **Complete positivity of the Schur multiplier** `T_S`: every ampliation is a positive map. -/
def IsCPSchur {ι : Type*} (S : Matrix ι ι ℂ) : Prop := ∀ k : ℕ, IsPositiveMap (schurAmp k S)

/-- **Slot assignment.** `e (i, j)` restricts to `lab (-(i + j))` on `L`; on `M` it restricts to a
real embedding when `i = j`, to `μ₁` when `j = i + 1`, and to `conjugate μ₁` when `i = j + 1`. -/
def IsSlotAssignment {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ) (e : Fin 3 × Fin 3 → (K →+* ℂ)) : Prop :=
  ∀ i j : Fin 3, (e (i, j)).comp (algebraMap L K) = lab (-(i + j)) ∧
    (i = j → ComplexEmbedding.IsReal ((e (i, j)).comp (algebraMap M K))) ∧
    (j = i + 1 → (e (i, j)).comp (algebraMap M K) = μ₁) ∧
    (i = j + 1 → (e (i, j)).comp (algebraMap M K) = conjugate μ₁)

/-! ### Bridges -/

/-- `DegreeNine.IsCPSchur` is `ReversibleUnits.IsCPSchur` (same body). -/
private theorem isCPSchur_iff {ι : Type*} (S : Matrix ι ι ℂ) :
    IsCPSchur S ↔ ReversibleUnits.IsCPSchur S := Iff.rfl

/-- A number field with exactly one real place has exactly one real embedding. -/
private theorem eq_of_isReal_of_isReal {F : Type*} [Field F] [NumberField F]
    (hF : nrRealPlaces F = 1) {φ ψ : F →+* ℂ} (hφ : ComplexEmbedding.IsReal φ)
    (hψ : ComplexEmbedding.IsReal ψ) : φ = ψ := by
  classical
  have h := card_real_embeddings (K := F)
  rw [hF] at h
  exact congrArg Subtype.val
    (Fintype.card_le_one_iff.mp (le_of_eq h) (⟨φ, hφ⟩ : {φ : F →+* ℂ // IsReal φ}) ⟨ψ, hψ⟩)

/-- Any two slot assignments are equal. -/
private theorem slotAssignment_unique {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K} (h₂ : L ⊔ M = ⊤) (hMr : nrRealPlaces M = 1)
    (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ) {f g : Fin 3 × Fin 3 → (K →+* ℂ)}
    (hf : IsSlotAssignment lab μ₁ f) (hg : IsSlotAssignment lab μ₁ g) : f = g := by
  funext p
  obtain ⟨i, j⟩ := p
  apply ReversibleUnits.restrictPair_injective h₂
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf i j
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg i j
  refine Prod.ext (by simp only [ReversibleUnits.restrictPair_fst, hf1, hg1]) ?_
  simp only [ReversibleUnits.restrictPair_snd]
  have htri : ∀ i j : Fin 3, i = j ∨ j = i + 1 ∨ i = j + 1 := by decide
  rcases htri i j with h | h | h
  · exact eq_of_isReal_of_isReal hMr (hf2 h) (hg2 h)
  · rw [hf3 h, hg3 h]
  · rw [hf4 h, hg4 h]

/-- The library's slot bijection `slotEquiv` is a slot assignment. -/
private theorem isSlotAssignment_slotEquiv {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) :
    IsSlotAssignment lab μ₁ (ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁) := by
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

/-- A slot assignment is the library's `slotEquiv`. -/
private theorem eq_slotEquiv {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) {e : Fin 3 × Fin 3 → (K →+* ℂ)}
    (he : IsSlotAssignment lab μ₁ e) :
    e = ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁ :=
  slotAssignment_unique (ReversibleUnits.sup_eq_top_of_hyp hL hM hK hMr) hMr lab μ₁ he
    (isSlotAssignment_slotEquiv hL hM hK hMr lab μ₁ hμ₁)

/-! ### The ten compared statements -/

/-- **1.** Hadamard inverse and rank one. -/
theorem hadamardInv_posSemidef_iff {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (h0 : ∀ i j, X i j ≠ 0) :
    (Matrix.of fun i j => (X i j)⁻¹).PosSemidef ↔ ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  exact ReversibleUnits.posSemidef_hadamardInv_iff hX h0

/-- **2.** Both Schur multipliers completely positive iff rank one. -/
theorem cp_both_iff_rankOne {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ} (h0 : ∀ i j, X i j ≠ 0) :
    IsCPSchur X ∧ IsCPSchur (Matrix.of fun i j => (X i j)⁻¹) ↔
      ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  rw [isCPSchur_iff, isCPSchur_iff]
  exact ReversibleUnits.isCPSchur_and_isCPSchur_hadamardInv_iff h0

/-- **3.** The setting: `K = LM`, linearly disjoint, with `3` real and `3` complex places. -/
theorem compositum_setting {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) :
    L ⊔ M = ⊤ ∧ L.LinearDisjoint M ∧ nrRealPlaces K = 3 ∧ nrComplexPlaces K = 3 := by
  have h₂ := ReversibleUnits.sup_eq_top_of_hyp hL hM hK hMr
  have h₁ := ReversibleUnits.linearDisjoint_of_hyp hL hM hK hMr
  obtain ⟨hr, hc⟩ := ReversibleUnits.places_compositum h₁ h₂
  have hLr : nrRealPlaces L = 3 := by rw [← IsTotallyReal.finrank L, hL]
  rw [hLr, hMr] at hr hc
  rw [hL, hM] at hc
  exact ⟨h₂, h₁, hr, by omega⟩

/-- **4.** The slot assignment exists, is a Hermitian bijection, and is unique. -/
theorem slot_assignment_exists_unique {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) :
    ∃ e : Fin 3 × Fin 3 ≃ (K →+* ℂ), IsSlotAssignment lab μ₁ e ∧
      (∀ i, ComplexEmbedding.IsReal (e (i, i))) ∧ (∀ i j, e (j, i) = conjugate (e (i, j))) ∧
      ∀ f : Fin 3 × Fin 3 → (K →+* ℂ), IsSlotAssignment lab μ₁ f → f = e := by
  exact ⟨ReversibleUnits.slotEquiv hL hM hK hMr lab μ₁ hμ₁,
    isSlotAssignment_slotEquiv hL hM hK hMr lab μ₁ hμ₁,
    ReversibleUnits.slotEquiv_diag_isReal hL hM hK hMr lab μ₁ hμ₁,
    ReversibleUnits.slotEquiv_swap hL hM hK hMr lab μ₁ hμ₁,
    fun _ hf => eq_slotEquiv hL hM hK hMr lab μ₁ hμ₁ hf⟩

/-- **5.** Rank-one symbols of nonzero elements: equal positive rational relative norms. -/
theorem rankOne_iff_relNorm_eq_ratCast {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) (x : K) (hx : x ≠ 0) :
    (∃ w : Fin 3 → ℂ, ∀ i j, e (i, j) x = w i * conj (w j)) ↔
      ∃ c : ℚ, 0 < c ∧ Algebra.norm L x = algebraMap ℚ L c ∧
        Algebra.norm M x = algebraMap ℚ M c := by
  obtain rfl := eq_slotEquiv hL hM hK hMr lab μ₁ hμ₁ he
  exact ReversibleUnits.rankOne_iff_norm_eq_ratCast hL hM hK hMr lab μ₁ hμ₁ x hx

/-- **6.** Rank-one symbols of units: trivial relative norms to `L` and to `M`. -/
theorem unit_rankOne_iff {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) (u : (𝓞 K)ˣ) :
    (Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1) ↔
      ∃ w : Fin 3 → ℂ, ∀ i j, e (i, j) (u : K) = w i * conj (w j) := by
  obtain rfl := eq_slotEquiv hL hM hK hMr lab μ₁ hμ₁ he
  exact ReversibleUnits.rankOne_iff hL hM hK hMr lab μ₁ hμ₁ u

/-- **7.** The units with trivial relative norms are torsion-free of rank two. -/
theorem relNormKernel_torsionFree_rank_two {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) :
    (∀ u : (𝓞 K)ˣ, Algebra.norm L (u : K) = 1 → Algebra.norm M (u : K) = 1 →
        u ∈ torsion K → u = 1) ∧
      finrank ℤ (Submodule.span ℤ ((logEmbedding K) ''
        {x : Additive (𝓞 K)ˣ | Algebra.norm L ((x.toMul : (𝓞 K)ˣ) : K) = 1 ∧
          Algebra.norm M ((x.toMul : (𝓞 K)ˣ) : K) = 1})) = 2 := by
  refine ⟨fun u h1 h2 ht => ?_, ?_⟩
  · have h : u ∈ ReversibleUnits.relNormKernel L M ⊓ torsion K :=
      ⟨ReversibleUnits.mem_relNormKernel.mpr ⟨h1, h2⟩, ht⟩
    rw [ReversibleUnits.relNormKernel_inf_torsion hL hK, Subgroup.mem_bot] at h
    exact h
  · have hset : {x : Additive (𝓞 K)ˣ | Algebra.norm L ((x.toMul : (𝓞 K)ˣ) : K) = 1 ∧
        Algebra.norm M ((x.toMul : (𝓞 K)ˣ) : K) = 1} =
        {x : Additive (𝓞 K)ˣ | x.toMul ∈ ReversibleUnits.relNormKernel L M} := by
      ext x
      exact ReversibleUnits.mem_relNormKernel.symm
    rw [hset]
    exact ReversibleUnits.finrank_span_logEmbedding_relNormKernel hL hM hK hMr

/-- **8.** Both-way complete positivity characterizes the units with trivial relative norms. -/
theorem reversible_iff {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) (u : (𝓞 K)ˣ) :
    IsCPSchur (Matrix.of fun i j => e (i, j) (u : K)) ∧
        IsCPSchur (Matrix.of fun i j => e (i, j) ((u⁻¹ : (𝓞 K)ˣ) : K)) ↔
      Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1 := by
  obtain rfl := eq_slotEquiv hL hM hK hMr lab μ₁ hμ₁ he
  rw [isCPSchur_iff, isCPSchur_iff, ← ReversibleUnits.mem_relNormKernel]
  exact ReversibleUnits.reversible_iff hL hM hK hMr lab μ₁ hμ₁ u

/-- **9.** A unit of infinite order all of whose powers run both ways. -/
theorem exists_reversible {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) :
    ∃ u : (𝓞 K)ˣ, u ∉ torsion K ∧ ∀ n : ℤ,
      IsCPSchur (Matrix.of fun i j => e (i, j) ((u ^ n : (𝓞 K)ˣ) : K)) ∧
        IsCPSchur (Matrix.of fun i j => e (i, j) (((u ^ n)⁻¹ : (𝓞 K)ˣ) : K)) := by
  obtain rfl := eq_slotEquiv hL hM hK hMr lab μ₁ hμ₁ he
  obtain ⟨u, hu, hn⟩ := ReversibleUnits.exists_reversible hL hM hK hMr lab μ₁ hμ₁
  exact ⟨u, hu, fun n => ⟨(isCPSchur_iff _).mpr (hn n).1, (isCPSchur_iff _).mpr (hn n).2⟩⟩

/-- **10.** The degree-four contrast: both ways iff positive at the real places and on the unit
circle at the complex place. -/
theorem quartic_reversible_iff {K : Type*} [Field K] [NumberField K]
    (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (u : (𝓞 K)ˣ) :
    IsCPSchur !![((embedding_of_isReal (e₁.symm 0).2 (u : K) : ℝ) : ℂ),
        conj (embedding (e₂.symm 0).1 (u : K));
        embedding (e₂.symm 0).1 (u : K), ((embedding_of_isReal (e₁.symm 1).2 (u : K) : ℝ) : ℂ)] ∧
      IsCPSchur !![((embedding_of_isReal (e₁.symm 0).2 (u : K)⁻¹ : ℝ) : ℂ),
        conj (embedding (e₂.symm 0).1 (u : K)⁻¹);
        embedding (e₂.symm 0).1 (u : K)⁻¹, ((embedding_of_isReal (e₁.symm 1).2 (u : K)⁻¹ : ℝ) : ℂ)] ↔
      0 < embedding_of_isReal (e₁.symm 0).2 (u : K) ∧
        0 < embedding_of_isReal (e₁.symm 1).2 (u : K) ∧
          ‖embedding (e₂.symm 0).1 (u : K)‖ = 1 := by
  exact ReversibleUnits.unit_both_cp_iff e₁ e₂ u

end DegreeNine
