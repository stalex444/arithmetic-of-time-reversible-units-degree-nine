module
public import Mathlib

@[expose] public section
/-!
# Reversible units of a degree-nine field: the rank-one Hermitian locus and both-way complete positivity

Let `K` be a number field of degree `9` containing a totally real cubic subfield `L` and a cubic
subfield `M` with exactly one real place. Then `K = LM` has three real and three complex places,
and its nine embeddings into `ℂ` are the pairs `(λ, μ)` of an embedding of `L` and one of `M`. A
**slot assignment** places them in a `3 × 3` array: given a labelling `lab` of the three (real)
embeddings of `L` and a non-real embedding `μ₁` of `M`, the slot `(i, j)` holds the embedding that
restricts to `lab (-(i + j))` on `L` and, on `M`, to the real embedding when `i = j`, to `μ₁` when
`j = i + 1` and to its conjugate `μ̄₁` when `i = j + 1` (indices in `ZMod 3`). The **symbol** of
`x ∈ K` is the `3 × 3` matrix of its nine conjugates in these slots; it is Hermitian, and the symbol
of `x⁻¹` is its entrywise (Hadamard) inverse. For a matrix `S`, the Schur multiplier `T_S : X ↦ S ⊙ X`
is completely positive (`IsCPSchur S`, ampliation form) iff `S` is positive semidefinite (Paulsen
2002, Thm 3.7; proved in the library as `ReversibleUnits.isCPSchur_iff_posSemidef`). The entry
compares exactly these ten statements.

Supporting lemmas (any size):

1. `hadamardInv_posSemidef_iff` — for every finite index type, a positive semidefinite complex
   matrix `X` with no zero entry has positive semidefinite Hadamard inverse `(X i j)⁻¹` iff
   `X = w w*` for some vector `w` (rank one).
2. `cp_both_iff_rankOne` — for every complex matrix `X` with no zero entry (positive
   semidefiniteness not assumed), the Schur multipliers of `X` and of its Hadamard inverse are both
   completely positive iff `X = w w*`.

The degree-nine theorem:

3. `compositum_setting` — for `K`, `L`, `M` as above (degree hypotheses `9`, `3`, `3`): `L ⊔ M = K`,
   `L` and `M` are linearly disjoint, and `K` has `3` real and `3` complex places.
4. `slot_assignment_exists_unique` — for every labelling `lab` and every non-real `μ₁`, there is a
   slot assignment, it is a bijection `Fin 3 × Fin 3 ≃ (K →+* ℂ)` with real diagonal slots and slot
   `(j, i)` the complex conjugate of slot `(i, j)`, and every function satisfying the slot
   conditions equals it.
5. `rankOne_iff_relNorm_eq_ratCast` — for every slot assignment `e` and every `x ≠ 0` in `K`: the
   symbol of `x` is rank one (`e (i, j) x = w i * conj (w j)`) iff the relative norms
   `N_{K/L}(x)` and `N_{K/M}(x)` are equal to one positive rational number.
6. `unit_rankOne_iff` — for every slot assignment `e` and every unit `u`: the symbol of `u` is rank
   one iff `N_{K/L}(u) = 1` and `N_{K/M}(u) = 1`.
7. `relNormKernel_torsionFree_rank_two` — the units `H` with `N_{K/L}(u) = N_{K/M}(u) = 1` contain
   no torsion other than `1`, and their image under the logarithmic embedding spans a `ℤ`-module of
   rank `2` (hence `H ≅ ℤ²`, since the logarithmic embedding is injective on `H` with image in the
   unit lattice).
8. `reversible_iff` — for every slot assignment and every unit `u`: the Schur multipliers of the
   symbols of `u` and of `u⁻¹` are both completely positive iff `u ∈ H`.
9. `exists_reversible` — for every slot assignment there is a unit `u` of infinite order such that,
   for every `n : ℤ`, the Schur multipliers of the symbols of `uⁿ` and `u⁻ⁿ` are both completely
   positive.

The degree-four contrast:

10. `quartic_reversible_iff` — the degree-four contrast: for a number field with two real places and
    one complex place, and its `2 × 2` place symbol (the two real conjugates on the diagonal, the
    complex conjugate `σ(u)` off it), the Schur multipliers of the symbols of a unit `u` and of `u⁻¹`
    are both completely positive iff `u` is positive at both real places and `‖σ(u)‖ = 1`.

Statements 4–6, 8 and 9 hold for every labelling and every non-real `μ₁`. The vocabulary is
Mathlib's (`Matrix.PosSemidef`, `vecMulVec`, `Algebra.norm`, `IntermediateField.LinearDisjoint`,
`NumberField.InfinitePlace`, `NumberField.ComplexEmbedding`, `NumberField.Units.torsion`,
`NumberField.Units.logEmbedding`; Mathlib's `CompletelyPositiveMap` is not used, see the
fidelity note in `formalization.yaml`); the four definitions below (`IsPositiveMap`, `schurAmp`,
`IsCPSchur`, `IsSlotAssignment`) are the only ones the entry adds, and `Solution.lean` repeats them
verbatim. Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with
the identical statement.

Application, cited and not a claim of the entry: in a physical reading in which a unit acts by
multiplication on a Hermitian place register and an admissible step must be completely positive,
statement 10 says that in degree four a step `u ≠ 1` runs both ways only through a conjugate on the
unit circle (Salem type); in a field such as `ℚ(Q)`, `Q⁴ = Q + 1`, the only such elements are `±1`
(not proved in this entry; it follows from statement 17 of the registered entry
PALOMAR-2026-10-21-000012, since `ℚ(Q) ⊆ ℚ(ρ, Q)`). Statements 6–9 say that in degree nine, in the
shape `(3, 3)`, a rank-two group of units runs both ways. The steps are completely positive, not
trace-non-increasing.
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

/-- **1.** Hadamard inverse and rank one. -/
theorem hadamardInv_posSemidef_iff {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (h0 : ∀ i j, X i j ≠ 0) :
    (Matrix.of fun i j => (X i j)⁻¹).PosSemidef ↔ ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  sorry

/-- **2.** Both Schur multipliers completely positive iff rank one. -/
theorem cp_both_iff_rankOne {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ} (h0 : ∀ i j, X i j ≠ 0) :
    IsCPSchur X ∧ IsCPSchur (Matrix.of fun i j => (X i j)⁻¹) ↔
      ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  sorry

/-- **3.** The setting: `K = LM`, linearly disjoint, with `3` real and `3` complex places. -/
theorem compositum_setting {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) :
    L ⊔ M = ⊤ ∧ L.LinearDisjoint M ∧ nrRealPlaces K = 3 ∧ nrComplexPlaces K = 3 := by
  sorry

/-- **4.** The slot assignment exists, is a Hermitian bijection, and is unique. -/
theorem slot_assignment_exists_unique {K : Type*} [Field K] [NumberField K]
    {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) :
    ∃ e : Fin 3 × Fin 3 ≃ (K →+* ℂ), IsSlotAssignment lab μ₁ e ∧
      (∀ i, ComplexEmbedding.IsReal (e (i, i))) ∧ (∀ i j, e (j, i) = conjugate (e (i, j))) ∧
      ∀ f : Fin 3 × Fin 3 → (K →+* ℂ), IsSlotAssignment lab μ₁ f → f = e := by
  sorry

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
  sorry

/-- **6.** Rank-one symbols of units: trivial relative norms to both cubic subfields. -/
theorem unit_rankOne_iff {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) (u : (𝓞 K)ˣ) :
    (Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1) ↔
      ∃ w : Fin 3 → ℂ, ∀ i j, e (i, j) (u : K) = w i * conj (w j) := by
  sorry

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
  sorry

/-- **8.** Both-way complete positivity characterizes the units with trivial relative norms. -/
theorem reversible_iff {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) (u : (𝓞 K)ˣ) :
    IsCPSchur (Matrix.of fun i j => e (i, j) (u : K)) ∧
        IsCPSchur (Matrix.of fun i j => e (i, j) ((u⁻¹ : (𝓞 K)ˣ) : K)) ↔
      Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1 := by
  sorry

/-- **9.** A unit of infinite order all of whose powers run both ways. -/
theorem exists_reversible {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}
    (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
    (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ)
    (hμ₁ : ¬ComplexEmbedding.IsReal μ₁) (e : Fin 3 × Fin 3 → (K →+* ℂ))
    (he : IsSlotAssignment lab μ₁ e) :
    ∃ u : (𝓞 K)ˣ, u ∉ torsion K ∧ ∀ n : ℤ,
      IsCPSchur (Matrix.of fun i j => e (i, j) ((u ^ n : (𝓞 K)ˣ) : K)) ∧
        IsCPSchur (Matrix.of fun i j => e (i, j) (((u ^ n)⁻¹ : (𝓞 K)ˣ) : K)) := by
  sorry

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
  sorry

end DegreeNine
