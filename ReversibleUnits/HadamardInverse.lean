module
public import Mathlib

@[expose] public section
/-!
# Schur multipliers and the Hadamard inverse of a positive semidefinite matrix

Supporting linear algebra for the degree-nine reversible units.

* `section Schur` is ported verbatim (namespace changed) from
  `HermitianExclusion/UnitSchur.lean` (`section Schur`; unpublished, reproduced here in full, so
  nothing depends on it): the Schur multiplier `T_S(X) = S ⊙ X`,
  its complete positivity in ampliation form (`IsCPSchur`) and Paulsen's theorem
  (Completely bounded maps and operator algebras, Cambridge 2002, Thm 3.7):
  completely positive ⟺ symbol positive semidefinite (`isCPSchur_iff_posSemidef`).
  The (⇐) direction is Schur's product theorem (`Matrix.PosSemidef.hadamard`).
* `section HadamardInverse`: for a positive semidefinite `X` with every entry nonzero, the
  Hadamard (entrywise) inverse `X^{∘-1}` is positive semidefinite iff `X = w w*` has rank one
  (`posSemidef_hadamardInv_iff`); hence both Schur multipliers `T_X`, `T_{X^{∘-1}}` are completely
  positive iff `X` is rank one (`isCPSchur_and_isCPSchur_hadamardInv_iff`). The argument: the
  `2 × 2` minors give `|x_{i₀ i}|² = x_{i₀ i₀} x_ii`; then `v = −x_{i₀ i} e_{i₀} + x_{i₀ i₀} e_i` is
  isotropic for `X`, hence in its kernel, which gives `X = w w*`.
  Adjacent literature: Reams (1999), Lim (2020); no novelty is claimed for this lemma.
-/

namespace ReversibleUnits

open Matrix ComplexConjugate
open scoped ComplexOrder

/-! ### Schur multipliers: positive ⟺ completely positive ⟺ symbol positive semidefinite -/

section Schur

variable {ι : Type*}

/-- The Schur multiplier with symbol `S`: `T_S(X) = S ⊙ X`. -/
def schurMul (S X : Matrix ι ι ℂ) : Matrix ι ι ℂ := S ⊙ X

@[simp] theorem schurMul_apply (S X : Matrix ι ι ℂ) (i j : ι) : schurMul S X i j = S i j * X i j :=
  rfl

/-- A map on matrices is **positive** if it sends positive semidefinite matrices to positive
semidefinite matrices. `IsPositiveMap (schurMul S)` is complete positivity of the Schur
multiplier `T_S` in symbol form (Paulsen 2002, Thm 3.7). -/
def IsPositiveMap (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop :=
  ∀ X : Matrix ι ι ℂ, X.PosSemidef → (Φ X).PosSemidef

/-- A map on matrices is **trace-non-increasing** if `tr Φ(X) ≤ tr X` on positive semidefinite
`X` (both traces are real there). -/
def IsTraceNonIncreasing [Fintype ι] (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop :=
  ∀ X : Matrix ι ι ℂ, X.PosSemidef → (trace (Φ X)).re ≤ (trace X).re

/-- The `k`-th ampliation `id_k ⊗ T_S` of the Schur multiplier, on block matrices indexed by
`Fin k × ι`: every block is Schur-multiplied by `S`, i.e. it is the Schur multiplier with symbol
`S ⊗ J_k = S.submatrix Prod.snd Prod.snd`. -/
def schurAmp (k : ℕ) (S : Matrix ι ι ℂ) (X : Matrix (Fin k × ι) (Fin k × ι) ℂ) :
    Matrix (Fin k × ι) (Fin k × ι) ℂ :=
  (S.submatrix Prod.snd Prod.snd) ⊙ X

/-- **Complete positivity of a Schur multiplier** (textbook ampliation form, specialised to Schur
multipliers): every ampliation `id_k ⊗ T_S` is a positive map. -/
def IsCPSchur (S : Matrix ι ι ℂ) : Prop := ∀ k : ℕ, IsPositiveMap (schurAmp k S)

/-- The all-ones matrix `J` is positive semidefinite (`J = 𝟙 𝟙*`). -/
theorem posSemidef_allOnes (ι : Type*) [Fintype ι] :
    (Matrix.of fun _ _ : ι => (1 : ℂ)).PosSemidef := by
  have h := posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℂ))
  convert h using 1
  ext i j
  simp [vecMulVec_apply]

theorem hadamard_allOnes (S : Matrix ι ι ℂ) : S ⊙ (Matrix.of fun _ _ => (1 : ℂ)) = S := by
  ext i j
  simp [hadamard_apply]

variable [Fintype ι]

/-- The easy direction of Paulsen's theorem: a positive Schur multiplier has a positive
semidefinite symbol, because `S = T_S(J)`. -/
theorem posSemidef_of_isPositiveMap_schurMul {S : Matrix ι ι ℂ}
    (h : IsPositiveMap (schurMul S)) : S.PosSemidef := by
  have := h _ (posSemidef_allOnes ι)
  rwa [schurMul, hadamard_allOnes] at this

/-- **Schur multipliers: positive ⟺ symbol positive semidefinite.** (⇐) is Schur's product
theorem (1911; `Matrix.PosSemidef.hadamard`), (⇒) is `S = T_S(J)`. Paulsen 2002, Thm 3.7. -/
theorem isPositiveMap_schurMul_iff {S : Matrix ι ι ℂ} :
    IsPositiveMap (schurMul S) ↔ S.PosSemidef :=
  ⟨posSemidef_of_isPositiveMap_schurMul, fun hS _ hX => hS.hadamard hX⟩

/-- **Schur multipliers: completely positive (ampliation form) ⟺ symbol positive semidefinite**
(Paulsen 2002, Thm 3.7, over a finite index type). -/
theorem isCPSchur_iff_posSemidef {S : Matrix ι ι ℂ} : IsCPSchur S ↔ S.PosSemidef := by
  constructor
  · intro h
    have h1 := h 1 _ (posSemidef_allOnes (Fin 1 × ι))
    unfold schurAmp at h1
    rw [hadamard_allOnes] at h1
    have h2 := h1.submatrix (fun i : ι => ((0 : Fin 1), i))
    convert h2 using 1
    ext i j
    rfl
  · intro hS k X hX
    exact (hS.submatrix _).hadamard hX

/-- For Schur multipliers, positivity already implies complete positivity. -/
theorem isCPSchur_iff_isPositiveMap {S : Matrix ι ι ℂ} :
    IsCPSchur S ↔ IsPositiveMap (schurMul S) := by
  rw [isCPSchur_iff_posSemidef, isPositiveMap_schurMul_iff]

/-! #### Trace-non-increasing ⟹ diagonal symbol entries `≤ 1` -/

theorem trace_schurMul_diagonal [DecidableEq ι] (S : Matrix ι ι ℂ) (d : ι → ℂ) :
    trace (schurMul S (diagonal d)) = ∑ i, S i i * d i := by
  simp [schurMul, trace, hadamard_apply]

/-- `T_S` trace-non-increasing ⟹ `Re s_ii ≤ 1` (test on the rank-one projector `E_ii`). -/
theorem re_diag_le_one_of_isTraceNonIncreasing [DecidableEq ι] {S : Matrix ι ι ℂ}
    (h : IsTraceNonIncreasing (schurMul S)) (i : ι) : (S i i).re ≤ 1 := by
  have hX : (diagonal (Pi.single i (1 : ℂ))).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
  have := h _ hX
  rw [trace_schurMul_diagonal, trace_diagonal] at this
  simpa [Pi.single_apply] using this

/-! #### Positive semidefinite ⟹ `0 ≤ s_ii` and `|s_ij|² ≤ s_ii s_jj` -/

omit [Fintype ι] in
theorem re_diag_nonneg_of_posSemidef {S : Matrix ι ι ℂ} (hS : S.PosSemidef) (i : ι) :
    0 ≤ (S i i).re :=
  (Complex.nonneg_iff.mp hS.diag_nonneg).1

omit [Fintype ι] in
theorem im_diag_eq_zero_of_posSemidef {S : Matrix ι ι ℂ} (hS : S.PosSemidef) (i : ι) :
    (S i i).im = 0 :=
  (Complex.nonneg_iff.mp hS.diag_nonneg).2.symm

omit [Fintype ι] in
/-- The `2 × 2` principal-minor inequality `|s_ij|² ≤ s_ii s_jj` of a positive semidefinite
matrix (from `Matrix.PosSemidef.det_nonneg` on the principal submatrix `![i, j]`). -/
theorem norm_sq_le_mul_re_diag_of_posSemidef {S : Matrix ι ι ℂ} (hS : S.PosSemidef) (i j : ι) :
    ‖S i j‖ ^ 2 ≤ (S i i).re * (S j j).re := by
  have hdet := (hS.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at hdet
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hji : S j i = conj (S i j) := by
    have := hS.isHermitian.apply j i
    rw [Complex.star_def] at this
    exact this.symm
  rw [hji, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hdet
  have h1 := (Complex.nonneg_iff.mp hdet).1
  have hi := im_diag_eq_zero_of_posSemidef hS i
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, hi, zero_mul, sub_zero] at h1
  linarith

end Schur

/-! ### The Hadamard inverse: positive semidefinite ⟺ rank one -/

section HadamardInverse

variable {ι : Type*}

/-- `X = w w*` entrywise. -/
theorem eq_vecMulVec_star_iff {X : Matrix ι ι ℂ} {w : ι → ℂ} :
    X = vecMulVec w (star w) ↔ ∀ i j, X i j = w i * conj (w j) := by
  constructor
  · rintro rfl i j
    simp [vecMulVec_apply]
  · intro h
    ext i j
    simp [vecMulVec_apply, h i j]

/-- A diagonal entry of a positive semidefinite matrix is real. -/
theorem diag_eq_ofReal_re_of_posSemidef {S : Matrix ι ι ℂ} (hS : S.PosSemidef) (i : ι) :
    S i i = ((S i i).re : ℂ) :=
  Complex.ext (by simp) (by simp [im_diag_eq_zero_of_posSemidef hS i])

/-- A nonzero diagonal entry of a positive semidefinite matrix has positive real part. -/
theorem re_diag_pos_of_posSemidef {S : Matrix ι ι ℂ} (hS : S.PosSemidef) {i : ι}
    (hi : S i i ≠ 0) : 0 < (S i i).re := by
  rcases (re_diag_nonneg_of_posSemidef hS i).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hi
    rw [diag_eq_ofReal_re_of_posSemidef hS i, ← h]
    simp

/-- (⇐) of `posSemidef_hadamardInv_iff`, with no hypothesis on the entries: the Hadamard inverse
of `w w*` is `w⁻¹ (w⁻¹)*`, which is positive semidefinite. -/
theorem posSemidef_hadamardInv_vecMulVec [Fintype ι] (w : ι → ℂ) :
    (Matrix.of fun i j => (vecMulVec w (star w) i j)⁻¹).PosSemidef := by
  convert posSemidef_vecMulVec_self_star (fun i => (w i)⁻¹) using 1
  ext i j
  simp only [of_apply, vecMulVec_apply, Pi.star_apply, mul_inv, star_inv₀]

/-- The `2 × 2` minors of `X` and of its Hadamard inverse together force equality in the
principal-minor inequality: `|x_ij|² = x_ii x_jj`. -/
theorem norm_sq_eq_mul_re_diag_of_hadamardInv [Fintype ι] {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (h0 : ∀ i j, X i j ≠ 0)
    (hY : (Matrix.of fun i j => (X i j)⁻¹).PosSemidef) (i j : ι) :
    ‖X i j‖ ^ 2 = (X i i).re * (X j j).re := by
  have h1 := norm_sq_le_mul_re_diag_of_posSemidef hX i j
  have h2 := norm_sq_le_mul_re_diag_of_posSemidef hY i j
  simp only [of_apply] at h2
  rw [diag_eq_ofReal_re_of_posSemidef hX i, diag_eq_ofReal_re_of_posSemidef hX j, norm_inv,
    ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re] at h2
  have hi := re_diag_pos_of_posSemidef hX (h0 i i)
  have hj := re_diag_pos_of_posSemidef hX (h0 j j)
  have hn : 0 < ‖X i j‖ := norm_pos_iff.mpr (h0 i j)
  rw [inv_pow, ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)] at h2
  exact le_antisymm h1 h2

/-- (⇒) of `posSemidef_hadamardInv_iff`. With `|x_{i₀ i}|² = x_{i₀ i₀} x_ii`, the vector
`v = -x_{i₀ i} e_{i₀} + x_{i₀ i₀} e_i` is isotropic for `X`, hence in its kernel; the kernel
equations are the column relations `x_ji x_{i₀ i₀} = x_{j i₀} x_{i₀ i}`, i.e.
`X = w w*` with `w_j = x_{j i₀} / √x_{i₀ i₀}`. -/
theorem exists_eq_vecMulVec_of_posSemidef_hadamardInv [Fintype ι] {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (h0 : ∀ i j, X i j ≠ 0)
    (hY : (Matrix.of fun i j => (X i j)⁻¹).PosSemidef) :
    ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, by ext i; exact isEmptyElim i⟩
  set D : ℝ := (X i₀ i₀).re with hD
  have hDpos : 0 < D := re_diag_pos_of_posSemidef hX (h0 i₀ i₀)
  have hX0 : X i₀ i₀ = (D : ℂ) := diag_eq_ofReal_re_of_posSemidef hX i₀
  have hherm : ∀ i j, X j i = conj (X i j) := fun i j => by
    have := hX.isHermitian.apply j i
    rw [Complex.star_def] at this
    exact this.symm
  have hcol : ∀ i j, X j i * (D : ℂ) = X j i₀ * X i₀ i := by
    intro i j
    set v : ι → ℂ := Pi.single i₀ (-X i₀ i) + Pi.single i (D : ℂ) with hv
    have hXv : ∀ k, (X *ᵥ v) k = X k i₀ * (-X i₀ i) + X k i * D := by
      intro k
      simp [hv, mulVec_add]
      ring
    have hsv : ∀ y : ι → ℂ, star v ⬝ᵥ y = star (-X i₀ i) * y i₀ + star (D : ℂ) * y i := by
      intro y
      rw [hv, star_add, ← Pi.single_star, ← Pi.single_star, add_dotProduct, single_dotProduct,
        single_dotProduct]
    have hnorm : X i₀ i * conj (X i₀ i) = (D : ℂ) * ((X i i).re : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
        norm_sq_eq_mul_re_diag_of_hadamardInv hX h0 hY i₀ i]
      push_cast
      ring
    have e1 : (X *ᵥ v) i₀ = 0 := by
      rw [hXv, hX0]
      ring
    have e2 : (X *ᵥ v) i = 0 := by
      rw [hXv, hherm i₀ i, diag_eq_ofReal_re_of_posSemidef hX i]
      linear_combination (-1 : ℂ) * hnorm
    have hzero : star v ⬝ᵥ X *ᵥ v = 0 := by
      rw [hsv, e1, e2]
      ring
    have := congrFun ((hX.dotProduct_mulVec_zero_iff).mp hzero) j
    rw [hXv] at this
    simp only [Pi.zero_apply] at this
    linear_combination this
  have hs : ((Real.sqrt D : ℝ) : ℂ) * ((Real.sqrt D : ℝ) : ℂ) = (D : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hDpos.le]
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  refine ⟨fun j => X j i₀ / ((Real.sqrt D : ℝ) : ℂ), ?_⟩
  ext j i
  rw [vecMulVec_apply, Pi.star_apply, Complex.star_def, map_div₀, Complex.conj_ofReal,
    ← hherm i i₀, div_mul_div_comm, hs, eq_div_iff hD0]
  exact hcol i j

/-- **Statement 1.** For a positive semidefinite `X` with every entry nonzero, the Hadamard inverse
`X^{∘-1} = (x_ij⁻¹)` is positive semidefinite iff `X = w w*` has rank one. -/
theorem posSemidef_hadamardInv_iff [Fintype ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (h0 : ∀ i j, X i j ≠ 0) :
    (Matrix.of fun i j => (X i j)⁻¹).PosSemidef ↔ ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  constructor
  · exact exists_eq_vecMulVec_of_posSemidef_hadamardInv hX h0
  · rintro ⟨w, rfl⟩
    exact posSemidef_hadamardInv_vecMulVec w

/-- **Statement 2.** For `X` with every entry nonzero, both Schur multipliers `T_X` and `T_{X^{∘-1}}`
are completely positive iff `X = w w*` has rank one. -/
theorem isCPSchur_and_isCPSchur_hadamardInv_iff [Fintype ι] {X : Matrix ι ι ℂ}
    (h0 : ∀ i j, X i j ≠ 0) :
    IsCPSchur X ∧ IsCPSchur (Matrix.of fun i j => (X i j)⁻¹) ↔
      ∃ w : ι → ℂ, X = vecMulVec w (star w) := by
  rw [isCPSchur_iff_posSemidef, isCPSchur_iff_posSemidef]
  constructor
  · rintro ⟨hX, hY⟩
    exact exists_eq_vecMulVec_of_posSemidef_hadamardInv hX h0 hY
  · rintro ⟨w, rfl⟩
    exact ⟨posSemidef_vecMulVec_self_star w, posSemidef_hadamardInv_vecMulVec w⟩

/-- **Statement 2, entrywise form.** -/
theorem isCPSchur_and_isCPSchur_hadamardInv_iff' [Fintype ι] {X : Matrix ι ι ℂ}
    (h0 : ∀ i j, X i j ≠ 0) :
    IsCPSchur X ∧ IsCPSchur (Matrix.of fun i j => (X i j)⁻¹) ↔
      ∃ w : ι → ℂ, ∀ i j, X i j = w i * conj (w j) := by
  rw [isCPSchur_and_isCPSchur_hadamardInv_iff h0]
  simp only [eq_vecMulVec_star_iff]

end HadamardInverse

end ReversibleUnits
