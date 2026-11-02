module
public import Mathlib

@[expose] public section
/-!
# The degree-nine compositum of a totally real cubic and a cubic with one real place

Let `K` be a number field of degree `9` containing a totally real cubic subfield `L` and a cubic
subfield `M` with exactly one real place. Then `K` has signature `(3, 3)`; its nine complex
embeddings are the pairs `(λ, μ)` of embeddings of `L` and `M`.

* **Ported (registered) material, `section Ported`.** The embeddings of a linearly disjoint
  compositum are the pairs of embeddings of the factors (`embeddingsEquiv`), an embedding is real
  iff both restrictions are (`isReal_iff_restrictPair`), and the place count
  (`places_compositum`). Ported from `HermiteCompositum/Places.lean` of the Palomar entry
  PALOMAR-2026-10-21-000012 (commit `5aa870e98236ba240561b798265c629df8c2d031`); not re-proved,
  only the ambient field renamed from `L` to `K`.
* **(a0) The hypotheses force a linearly disjoint compositum.** `L ≠ M`, `L ⊔ M = ⊤`,
  `L.LinearDisjoint M` (`ne_of_hyp`, `sup_eq_top_of_hyp`, `linearDisjoint_of_hyp`).
* **(b) Relative norms as products over embeddings.** For `σ : L →+* ℂ`,
  `σ (N_{K/L} x) = ∏_{τ : M →+* ℂ} (σ, τ)(x)` (`map_norm_left`), and symmetrically for `M`
  (`map_norm_right`).
* **(c) The rank-one theorem.** An explicit bijection `slotEquiv : Fin 3 × Fin 3 ≃ (K →+* ℂ)`
  built from a labelling of the embeddings of `L` and a non-real embedding `μ₁` of `M`, with the
  diagonal slots real and the slot `(j, i)` the complex conjugate of the slot `(i, j)`. For every
  `x : K` with `N_{K/L} x = N_{K/M} x = 1`, the matrix of slot values is `w w*`
  (`rankOne_of_norms`); for a unit `u`, the converse holds (`rankOne_iff`); the existential form
  is `exists_slotEquiv_rankOne_iff`. For any `x ≠ 0`: the slot matrix is rank one iff
  `N_{K/L} x = N_{K/M} x ∈ ℚ_{>0}` (`rankOne_iff_norm_eq_ratCast`).
* **(d) The group `H`** of units with `N_{K/L} u = N_{K/M} u = 1` (`relNormKernel`): it is
  torsion-free (`relNormKernel_inf_torsion`), contains a unit `≠ 1`
  (`exists_mem_relNormKernel_ne_one`, via the projection `π(u) = (u⁹ N_{K/L}(u)⁻³ N_{K/M}(u)⁻³)²`
  and a Dirichlet unit large at one real place), and has `ℤ`-rank `2`
  (`finrank_relNormKernel`; in `logEmbedding` form `finrank_span_logEmbedding_relNormKernel`).
  The rank is computed by rank–nullity for `u ↦ (N_{K/L} u, N_{K/M} u)` into
  `(𝓞 L)ˣ × (𝓞 M)ˣ`, of `ℤ`-ranks `5` and `2 + 1`; the range has rank exactly `3` because
  `(l, m) ↦ l m` composed with the norm pair has torsion kernel.
-/

open Module NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace ComplexConjugate

open scoped TensorProduct

namespace ReversibleUnits

/-! ### Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum/Places.lean`) -/

section Ported

variable {K : Type*} [Field K] [NumberField K] {K₁ K₂ : IntermediateField ℚ K}

/-- If `K₁ ⊔ K₂ = ⊤` as intermediate fields of a number field, the same holds for the underlying
subalgebras. Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.toSubalgebra_sup_eq_top`). -/
theorem toSubalgebra_sup_eq_top (h₂ : K₁ ⊔ K₂ = ⊤) :
    K₁.toSubalgebra ⊔ K₂.toSubalgebra = ⊤ := by
  rw [← IntermediateField.sup_toSubalgebra_of_isAlgebraic_right, h₂,
    IntermediateField.top_toSubalgebra]

/-- The isomorphism `K₁ ⊗[ℚ] K₂ ≃ₐ[ℚ] K` of a linearly disjoint compositum.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.compositumAlgEquiv`). -/
noncomputable def compositumAlgEquiv (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    K₁ ⊗[ℚ] K₂ ≃ₐ[ℚ] K :=
  ((IntermediateField.linearDisjoint_iff'.1 h₁).mulMap.trans
    (Subalgebra.equivOfEq _ _ (toSubalgebra_sup_eq_top h₂))).trans Subalgebra.topEquiv

/-- Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.compositumAlgEquiv_tmul`). -/
@[simp]
theorem compositumAlgEquiv_tmul (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (a : K₁) (b : K₂) :
    compositumAlgEquiv h₁ h₂ (a ⊗ₜ[ℚ] b) = (a : K) * (b : K) := by
  simp only [compositumAlgEquiv, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply,
    Subalgebra.topEquiv_apply]
  exact Subalgebra.LinearDisjoint.val_mulMap_tmul _ _ _

/-- Restriction of an embedding `K →+* ℂ` to the pair of embeddings of `K₁` and `K₂`.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.restrictPair`). -/
def restrictPair (K₁ K₂ : IntermediateField ℚ K) (φ : K →+* ℂ) :
    (K₁ →+* ℂ) × (K₂ →+* ℂ) :=
  (φ.comp (algebraMap K₁ K), φ.comp (algebraMap K₂ K))

/-- Ported from PALOMAR-2026-10-21-000012. -/
@[simp] theorem restrictPair_fst (φ : K →+* ℂ) :
    (restrictPair K₁ K₂ φ).1 = φ.comp (algebraMap K₁ K) := rfl

/-- Ported from PALOMAR-2026-10-21-000012. -/
@[simp] theorem restrictPair_snd (φ : K →+* ℂ) :
    (restrictPair K₁ K₂ φ).2 = φ.comp (algebraMap K₂ K) := rfl

/-- Two embeddings of `K` that agree on `K₁` and on `K₂` agree on `K₁ ⊔ K₂ = ⊤`.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.restrictPair_injective`). -/
theorem restrictPair_injective (h₂ : K₁ ⊔ K₂ = ⊤) :
    Function.Injective (restrictPair K₁ K₂) := by
  intro φ ψ h
  simp only [restrictPair, Prod.mk.injEq] at h
  have hle : K₁.toSubalgebra ⊔ K₂.toSubalgebra ≤
      AlgHom.equalizer φ.toRatAlgHom ψ.toRatAlgHom := by
    refine sup_le ?_ ?_
    · intro x hx
      exact RingHom.congr_fun h.1 ⟨x, hx⟩
    · intro x hx
      exact RingHom.congr_fun h.2 ⟨x, hx⟩
  rw [toSubalgebra_sup_eq_top h₂] at hle
  ext x
  exact hle (Algebra.mem_top (x := x))

/-- Every pair of embeddings of `K₁` and `K₂` extends to an embedding of `K`.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.restrictPair_surjective`). -/
theorem restrictPair_surjective (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    Function.Surjective (restrictPair K₁ K₂) := by
  rintro ⟨φ₁, φ₂⟩
  let e := compositumAlgEquiv h₁ h₂
  let Φ : K →ₐ[ℚ] ℂ :=
    (Algebra.TensorProduct.productMap φ₁.toRatAlgHom φ₂.toRatAlgHom).comp e.symm.toAlgHom
  refine ⟨Φ.toRingHom, ?_⟩
  simp only [restrictPair, Prod.mk.injEq]
  constructor
  · ext a
    have ha : e.symm (a : K) = a ⊗ₜ[ℚ] (1 : K₂) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    simp [Φ, ha]
  · ext b
    have hb : e.symm (b : K) = (1 : K₁) ⊗ₜ[ℚ] b := by
      rw [AlgEquiv.symm_apply_eq]
      simp [e]
    simp [Φ, hb]

/-- Embeddings of a linearly disjoint compositum are pairs of embeddings of the factors.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.embeddingsEquiv`). -/
noncomputable def embeddingsEquiv (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    (K →+* ℂ) ≃ (K₁ →+* ℂ) × (K₂ →+* ℂ) :=
  Equiv.ofBijective _ ⟨restrictPair_injective h₂, restrictPair_surjective h₁ h₂⟩

/-- Ported from PALOMAR-2026-10-21-000012. -/
@[simp] theorem embeddingsEquiv_apply (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (φ : K →+* ℂ) : embeddingsEquiv h₁ h₂ φ = restrictPair K₁ K₂ φ := rfl

/-- An embedding of the compositum is real iff both of its restrictions are real.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.isReal_iff_restrictPair`). -/
theorem isReal_iff_restrictPair (h₂ : K₁ ⊔ K₂ = ⊤) (φ : K →+* ℂ) :
    IsReal φ ↔ IsReal (restrictPair K₁ K₂ φ).1 ∧ IsReal (restrictPair K₁ K₂ φ).2 := by
  constructor
  · intro h
    exact ⟨h.comp _, h.comp _⟩
  · rintro ⟨h1, h2⟩
    rw [ComplexEmbedding.isReal_iff] at h1 h2 ⊢
    apply restrictPair_injective h₂
    simp only [restrictPair, Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨by rw [conjugate_comp]; exact h1, by rw [conjugate_comp]; exact h2⟩

open scoped Classical in
/-- Real embeddings of the compositum are pairs of real embeddings.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.card_real_embeddings_compositum`). -/
theorem card_real_embeddings_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    Fintype.card {φ : K →+* ℂ // IsReal φ} =
      Fintype.card {φ : K₁ →+* ℂ // IsReal φ} * Fintype.card {φ : K₂ →+* ℂ // IsReal φ} := by
  rw [← Fintype.card_prod]
  exact Fintype.card_congr
    (((embeddingsEquiv h₁ h₂).subtypeEquiv fun φ => isReal_iff_restrictPair h₂ φ).trans
      Equiv.subtypeProdEquivProd)

/-- The degree of a linearly disjoint compositum is the product of the degrees.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.finrank_compositum`). -/
theorem finrank_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    finrank ℚ K = finrank ℚ K₁ * finrank ℚ K₂ := by
  have := h₁.finrank_sup
  rwa [h₂, IntermediateField.finrank_top'] at this

/-- Real places of a linearly disjoint compositum.
Ported from PALOMAR-2026-10-21-000012 (`HermiteCompositum.nrRealPlaces_compositum`). -/
theorem nrRealPlaces_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces K = nrRealPlaces K₁ * nrRealPlaces K₂ := by
  classical
  rw [← card_real_embeddings, ← card_real_embeddings, ← card_real_embeddings]
  exact card_real_embeddings_compositum h₁ h₂

/-- `r₁(K₁) r₁(K₂) + 2 r₂(K) = [K₁:ℚ] [K₂:ℚ]`. Ported from PALOMAR-2026-10-21-000012
(`HermiteCompositum.nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum`). -/
theorem nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum
    (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces K₁ * nrRealPlaces K₂ + 2 * nrComplexPlaces K =
      finrank ℚ K₁ * finrank ℚ K₂ := by
  rw [← nrRealPlaces_compositum h₁ h₂, card_add_two_mul_card_eq_rank, finrank_compositum h₁ h₂]

/-- `2 r₂(K) = [K₁:ℚ] [K₂:ℚ] - r₁(K₁) r₁(K₂)`. Ported from PALOMAR-2026-10-21-000012
(`HermiteCompositum.two_mul_nrComplexPlaces_compositum`). -/
theorem two_mul_nrComplexPlaces_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    2 * nrComplexPlaces K = finrank ℚ K₁ * finrank ℚ K₂ - nrRealPlaces K₁ * nrRealPlaces K₂ := by
  have := nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum h₁ h₂
  omega

/-- **Places of a linearly disjoint compositum** (compared statement (3) of
PALOMAR-2026-10-21-000012, `HermiteCompositum.places_compositum`; ported, not re-proved). -/
theorem places_compositum (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) :
    nrRealPlaces K = nrRealPlaces K₁ * nrRealPlaces K₂ ∧
      2 * nrComplexPlaces K =
        finrank ℚ K₁ * finrank ℚ K₂ - nrRealPlaces K₁ * nrRealPlaces K₂ :=
  ⟨nrRealPlaces_compositum h₁ h₂, two_mul_nrComplexPlaces_compositum h₁ h₂⟩

end Ported

/-! ### Pairs of embeddings -/

section Pair

variable {K : Type*} [Field K] [NumberField K] {K₁ K₂ : IntermediateField ℚ K}

/-- The embedding of the compositum with restrictions `σ` and `τ`. -/
noncomputable def pairEmb (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) : K →+* ℂ :=
  (embeddingsEquiv h₁ h₂).symm (σ, τ)

theorem restrictPair_pairEmb (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) : restrictPair K₁ K₂ (pairEmb h₁ h₂ σ τ) = (σ, τ) :=
  (embeddingsEquiv h₁ h₂).apply_symm_apply (σ, τ)

theorem pairEmb_comp_left (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) : (pairEmb h₁ h₂ σ τ).comp (algebraMap K₁ K) = σ :=
  congrArg Prod.fst (restrictPair_pairEmb h₁ h₂ σ τ)

theorem pairEmb_comp_right (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) : (pairEmb h₁ h₂ σ τ).comp (algebraMap K₂ K) = τ :=
  congrArg Prod.snd (restrictPair_pairEmb h₁ h₂ σ τ)

theorem eq_pairEmb_iff (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) (φ : K →+* ℂ) :
    φ = pairEmb h₁ h₂ σ τ ↔ φ.comp (algebraMap K₁ K) = σ ∧ φ.comp (algebraMap K₂ K) = τ := by
  rw [pairEmb, Equiv.eq_symm_apply, embeddingsEquiv_apply, restrictPair, Prod.mk.injEq]

/-- The conjugate of the pair `(σ, τ)` is the pair of conjugates. -/
theorem conjugate_pairEmb (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) :
    conjugate (pairEmb h₁ h₂ σ τ) = pairEmb h₁ h₂ (conjugate σ) (conjugate τ) := by
  rw [eq_pairEmb_iff, conjugate_comp, conjugate_comp, pairEmb_comp_left, pairEmb_comp_right]
  exact ⟨rfl, rfl⟩

/-- The pair embedding does not depend on the order of the factors. -/
theorem pairEmb_swap (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) :
    pairEmb h₁.symm (sup_comm K₁ K₂ ▸ h₂) τ σ = pairEmb h₁ h₂ σ τ := by
  rw [eq_pairEmb_iff, pairEmb_comp_left, pairEmb_comp_right]
  exact ⟨rfl, rfl⟩

/-- The signed norm `N_{K/ℚ}` as the product over all complex embeddings. -/
theorem algebraMap_norm_eq_prod (x : K) :
    algebraMap ℚ ℂ (Algebra.norm ℚ x) = ∏ φ : K →+* ℂ, φ x := by
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])).symm

theorem pairEmb_algebraMap_left (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) (a : K₁) : pairEmb h₁ h₂ σ τ (algebraMap K₁ K a) = σ a :=
  RingHom.congr_fun (pairEmb_comp_left h₁ h₂ σ τ) a

theorem pairEmb_algebraMap_right (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (τ : K₂ →+* ℂ) (b : K₂) : pairEmb h₁ h₂ σ τ (algebraMap K₂ K b) = τ b :=
  RingHom.congr_fun (pairEmb_comp_right h₁ h₂ σ τ) b

theorem pairEmb_inj (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    {σ σ' : K₁ →+* ℂ} {τ τ' : K₂ →+* ℂ} (h : pairEmb h₁ h₂ σ τ = pairEmb h₁ h₂ σ' τ') :
    σ = σ' ∧ τ = τ' :=
  Prod.mk.inj ((embeddingsEquiv h₁ h₂).symm.injective h)

/-- **(b) The relative norm as a product over embeddings.** For `σ : K₁ →+* ℂ`,
`σ (N_{K/K₁} x) = ∏_{τ : K₂ →+* ℂ} (σ, τ)(x)`. No normality is needed. -/
theorem map_norm_left (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (σ : K₁ →+* ℂ) (x : K) :
    σ (Algebra.norm K₁ x) = ∏ τ : K₂ →+* ℂ, pairEmb h₁ h₂ σ τ x := by
  let _ : Algebra K₁ ℂ := σ.toAlgebra
  have h := Algebra.norm_eq_prod_embeddings K₁ ℂ x
  rw [RingHom.algebraMap_toAlgebra] at h
  rw [h]
  have key : ∀ φ : K →ₐ[K₁] ℂ,
      pairEmb h₁ h₂ σ ((φ : K →+* ℂ).comp (algebraMap K₂ K)) = (φ : K →+* ℂ) := by
    intro φ
    symm
    rw [eq_pairEmb_iff]
    refine ⟨?_, rfl⟩
    ext a
    exact φ.commutes a
  let e : (K →ₐ[K₁] ℂ) ≃ (K₂ →+* ℂ) :=
    { toFun := fun φ => (φ : K →+* ℂ).comp (algebraMap K₂ K)
      invFun := fun τ =>
        { pairEmb h₁ h₂ σ τ with
          commutes' := fun a => RingHom.congr_fun (pairEmb_comp_left h₁ h₂ σ τ) a }
      left_inv := fun φ => by
        apply AlgHom.coe_ringHom_injective
        exact key φ
      right_inv := fun τ => pairEmb_comp_right h₁ h₂ σ τ }
  exact Fintype.prod_equiv e _ _ (fun φ => by
    change φ x = pairEmb h₁ h₂ σ ((φ : K →+* ℂ).comp (algebraMap K₂ K)) x
    rw [key φ]
    rfl)

/-- **(b), the other factor.** For `τ : K₂ →+* ℂ`,
`τ (N_{K/K₂} x) = ∏_{σ : K₁ →+* ℂ} (σ, τ)(x)`. -/
theorem map_norm_right (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤)
    (τ : K₂ →+* ℂ) (x : K) :
    τ (Algebra.norm K₂ x) = ∏ σ : K₁ →+* ℂ, pairEmb h₁ h₂ σ τ x := by
  rw [map_norm_left h₁.symm (sup_comm K₁ K₂ ▸ h₂) τ x]
  exact Finset.prod_congr rfl fun σ _ => by rw [pairEmb_swap]

/-- **(b), restriction to the other factor.** For `b ∈ K₂`, `N_{K/K₁}(b) = N_{K₂/ℚ}(b)`. -/
theorem norm_algebraMap_right (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (b : K₂) :
    Algebra.norm K₁ (algebraMap K₂ K b) = algebraMap ℚ K₁ (Algebra.norm ℚ b) := by
  obtain ⟨σ⟩ := (inferInstance : Nonempty (K₁ →+* ℂ))
  apply σ.injective
  rw [map_norm_left h₁ h₂ σ]
  simp_rw [pairEmb_algebraMap_right]
  rw [← algebraMap_norm_eq_prod b]
  simp only [eq_ratCast, map_ratCast]

/-- The relative norm of the projection `x⁹ N_{K/K₁}(x)⁻³ N_{K/K₂}(x)⁻³` to `K₁`, when
`[K₂ : ℚ] = 3`: it is `N_{K/ℚ}(x)⁻³`. -/
theorem norm_proj_left (h₁ : K₁.LinearDisjoint K₂) (h₂ : K₁ ⊔ K₂ = ⊤) (h3 : finrank ℚ K₂ = 3)
    {x : K} (hx : x ≠ 0) :
    Algebra.norm K₁ (x ^ 9 * (algebraMap K₁ K (Algebra.norm K₁ x))⁻¹ ^ 3 *
      (algebraMap K₂ K (Algebra.norm K₂ x))⁻¹ ^ 3) =
      (algebraMap ℚ K₁ (Algebra.norm ℚ x))⁻¹ ^ 3 := by
  have hf : finrank K₁ K = 3 := (h₁.finrank_left_eq_finrank h₂).trans h3
  have hn : Algebra.norm K₁ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, Algebra.norm_inv, Algebra.norm_inv,
    Algebra.norm_algebraMap, hf, norm_algebraMap_right h₁ h₂, Algebra.norm_norm]
  have h9 : Algebra.norm K₁ x ^ 9 * ((Algebra.norm K₁ x ^ 3)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← pow_mul]
    exact mul_inv_cancel₀ (pow_ne_zero _ hn)
  rw [h9, one_mul]

end Pair

/-! ### (a0) The degree-nine hypotheses force a linearly disjoint compositum -/

section Hyp

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

/-- A totally real cubic and a cubic with one real place are different subfields. -/
theorem ne_of_hyp (hL : finrank ℚ L = 3) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) :
    L ≠ M := by
  rintro rfl
  have := IsTotallyReal.finrank L
  omega

/-- The compositum of the two cubics is all of `K`. -/
theorem sup_eq_top_of_hyp (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) : L ⊔ M = ⊤ := by
  have hd1 : finrank ℚ L ∣ finrank ℚ ↥(L ⊔ M) :=
    IntermediateField.finrank_dvd_of_le_right le_sup_left
  have hd2 : finrank ℚ ↥(L ⊔ M) ∣ finrank ℚ K := by
    have := IntermediateField.finrank_dvd_of_le_right (le_top : L ⊔ M ≤ ⊤)
    rwa [IntermediateField.finrank_top'] at this
  rw [hL] at hd1
  rw [hK] at hd2
  have hpos : 0 < finrank ℚ ↥(L ⊔ M) := Module.finrank_pos
  have h9 : finrank ℚ ↥(L ⊔ M) = 3 ∨ finrank ℚ ↥(L ⊔ M) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) hd2
    interval_cases h : finrank ℚ ↥(L ⊔ M) <;> simp_all
  rcases h9 with h3 | h9
  · exfalso
    have hLeq : L = L ⊔ M :=
      IntermediateField.eq_of_le_of_finrank_eq le_sup_left (by rw [hL, h3])
    have hMeq : M = L ⊔ M :=
      IntermediateField.eq_of_le_of_finrank_eq le_sup_right (by rw [hM, h3])
    exact ne_of_hyp hL hMr (hLeq.trans hMeq.symm)
  · apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [h9, IntermediateField.finrank_top', hK]

/-- The two cubics are linearly disjoint. -/
theorem linearDisjoint_of_hyp (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) : L.LinearDisjoint M := by
  apply IntermediateField.LinearDisjoint.of_finrank_sup
  rw [sup_eq_top_of_hyp hL hM hK hMr, IntermediateField.finrank_top', hK, hL, hM]

end Hyp

/-! ### (c) The rank-one theorem -/

section Core

/-- **The algebraic core of the rank-one theorem.** Given real `r₀ r₁ r₂` and complex
`c₀ c₁ c₂` with `r_k |c_k|² = 1` for `k = 0, 2`, `r₀ r₁ r₂ = 1` and `c₀ c₁ c₂ = 1`, the Hermitian matrix with
diagonal `r_k` and off-diagonal entries `(0,1) = c₂`, `(1,2) = c₀`, `(0,2) = c̄₁` is `w w*`, with
`w = (√r₀, c̄₂/√r₀, c̄₀ √r₀ / c₂)`. -/
theorem rankOne_aux {r0 r1 r2 : ℝ} {c0 c1 c2 : ℂ}
    (h0 : (r0 : ℂ) * c0 * conj c0 = 1) (h2 : (r2 : ℂ) * c2 * conj c2 = 1) (hr : (r0 : ℂ) * r1 * r2 = 1)
    (hc : c0 * c1 * c2 = 1) :
    ∃ w0 w1 w2 : ℂ,
      w0 * conj w0 = r0 ∧ w0 * conj w1 = c2 ∧ w0 * conj w2 = conj c1 ∧
      w1 * conj w0 = conj c2 ∧ w1 * conj w1 = r1 ∧ w1 * conj w2 = c0 ∧
      w2 * conj w0 = c1 ∧ w2 * conj w1 = conj c0 ∧ w2 * conj w2 = r2 := by
  have hreal : r0 * Complex.normSq c0 = 1 := by
    have : (r0 : ℂ) * (Complex.normSq c0 : ℂ) = 1 := by
      rw [← Complex.mul_conj, ← mul_assoc]; exact h0
    exact_mod_cast this
  have hpos : 0 < r0 := by nlinarith [Complex.normSq_nonneg c0]
  have hd : conj c0 * conj c1 * conj c2 = 1 := by
    have := congrArg conj hc
    simpa only [map_mul, map_one] using this
  set s : ℂ := ((Real.sqrt r0 : ℝ) : ℂ) with hs_def
  have hs : s * s = r0 := by
    rw [hs_def, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  have hs0 : s ≠ 0 := by
    rw [hs_def, Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.mpr hpos).ne'
  have hsc : conj s = s := Complex.conj_ofReal _
  have hc2 : c2 ≠ 0 := by rintro rfl; simp at h2
  have hd2 : conj c2 ≠ 0 := (map_ne_zero _).mpr hc2
  have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hci : c2 * c2⁻¹ = 1 := mul_inv_cancel₀ hc2
  have hdi : conj c2 * (conj c2)⁻¹ = 1 := mul_inv_cancel₀ hd2
  refine ⟨s, conj c2 * s⁻¹, conj c0 * s * c2⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [map_mul, map_inv₀, Complex.conj_conj, hsc]
  · exact hs
  · linear_combination c2 * hsi
  · linear_combination c0 * (conj c2)⁻¹ * hs +
      (conj c2)⁻¹ * (conj c1 * conj c2 * h0 - (r0 : ℂ) * c0 * hd) + conj c1 * hdi
  · linear_combination conj c2 * hsi
  · linear_combination s⁻¹ ^ 2 * (-(c2 * conj c2) * hr + (r0 : ℂ) * r1 * h2) +
      (r1 : ℂ) * (-(s⁻¹ ^ 2) * hs + (s * s⁻¹ + 1) * hsi)
  · linear_combination c0 * (s * s⁻¹ * hdi + hsi)
  · linear_combination conj c0 * c2⁻¹ * hs +
      c2⁻¹ * (c1 * c2 * h0 - (r0 : ℂ) * conj c0 * hc) + c1 * hci
  · linear_combination conj c0 * (c2 * c2⁻¹ * hsi + hci)
  · linear_combination c2⁻¹ * (conj c2)⁻¹ * c0 * conj c0 * hs +
      (r0 : ℂ) * c2⁻¹ * (conj c2)⁻¹ * (-(c0 * conj c0) * hr + (r1 : ℂ) * r2 * h0) +
      c2⁻¹ * (conj c2)⁻¹ * hr +
      (-(c2⁻¹ * (conj c2)⁻¹) * h2 + (r2 : ℂ) * (conj c2 * (conj c2)⁻¹ * hci + hdi))

/-- **The scaled core.** The same conclusion when the three products equal a common `c > 0`
instead of `1`. -/
theorem rankOne_aux_scaled {r0 r1 r2 c : ℝ} {c0 c1 c2 : ℂ} (hc : 0 < c)
    (h0 : (r0 : ℂ) * c0 * conj c0 = c) (h2 : (r2 : ℂ) * c2 * conj c2 = c)
    (hr : (r0 : ℂ) * r1 * r2 = c) (hcc : c0 * c1 * c2 = c) :
    ∃ w0 w1 w2 : ℂ,
      w0 * conj w0 = r0 ∧ w0 * conj w1 = c2 ∧ w0 * conj w2 = conj c1 ∧
      w1 * conj w0 = conj c2 ∧ w1 * conj w1 = r1 ∧ w1 * conj w2 = c0 ∧
      w2 * conj w0 = c1 ∧ w2 * conj w1 = conj c0 ∧ w2 * conj w2 = r2 := by
  set s : ℝ := c ^ ((3 : ℕ)⁻¹ : ℝ) with hs_def
  have hs3 : s ^ 3 = c := Real.rpow_inv_natCast_pow hc.le (by norm_num)
  have hs0 : 0 < s := Real.rpow_pos_of_pos hc _
  have hsC : (s : ℂ) ^ 3 = c := by exact_mod_cast hs3
  have hsC0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hsc : conj (s : ℂ) = s := Complex.conj_ofReal _
  obtain ⟨w0, w1, w2, e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ :=
    rankOne_aux (r0 := r0 / s) (r1 := r1 / s) (r2 := r2 / s)
      (c0 := c0 / s) (c1 := c1 / s) (c2 := c2 / s)
      (by push_cast; rw [map_div₀, hsc]; field_simp; linear_combination h0 - hsC)
      (by push_cast; rw [map_div₀, hsc]; field_simp; linear_combination h2 - hsC)
      (by push_cast; field_simp; linear_combination hr - hsC)
      (by field_simp; linear_combination hcc - hsC)
  set t : ℂ := ((Real.sqrt s : ℝ) : ℂ) with ht_def
  have htt : t * conj t = s := by
    rw [ht_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hs0.le]
  have key : ∀ a b v : ℂ, a * conj b = v / s → (t * a) * conj (t * b) = v := by
    intro a b v h
    rw [map_mul, show t * a * (conj t * conj b) = (t * conj t) * (a * conj b) by ring, htt, h]
    field_simp
  refine ⟨t * w0, t * w1, t * w2, key _ _ _ ?_, key _ _ _ e01, key _ _ _ ?_, key _ _ _ ?_,
    key _ _ _ ?_, key _ _ _ e12, key _ _ _ e20, key _ _ _ ?_, key _ _ _ ?_⟩
  · rw [e00]; push_cast; rfl
  · rw [e02, map_div₀, hsc]
  · rw [e10, map_div₀, hsc]
  · rw [e11]; push_cast; rfl
  · rw [e21, map_div₀, hsc]
  · rw [e22]; push_cast; rfl

end Core

section Main

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

/-- A number field with one real place has a real embedding. -/
theorem exists_isReal_of_nrRealPlaces_eq_one (hMr : nrRealPlaces M = 1) :
    ∃ φ : M →+* ℂ, IsReal φ := by
  classical
  have h := card_real_embeddings (K := M)
  rw [hMr] at h
  obtain ⟨φ⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_eq Nat.one_pos h.symm)
  exact ⟨φ.1, φ.2⟩

/-- The real embedding of `M` (unique, as `M` has exactly one real place). -/
noncomputable def realEmb (hMr : nrRealPlaces M = 1) : M →+* ℂ :=
  (exists_isReal_of_nrRealPlaces_eq_one hMr).choose

theorem isReal_realEmb (hMr : nrRealPlaces M = 1) : IsReal (realEmb hMr) :=
  (exists_isReal_of_nrRealPlaces_eq_one hMr).choose_spec

/-- The three embeddings of the cubic `M`: `μ_r` (real), `μ₁` (non-real) and `μ̄₁`. -/
noncomputable def mEnum (hM : finrank ℚ M = 3) {μr μ₁ : M →+* ℂ} (hr : IsReal μr)
    (h1 : ¬IsReal μ₁) : Fin 3 ≃ (M →+* ℂ) :=
  Equiv.ofBijective ![μr, μ₁, conjugate μ₁] <| by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
    · have h01 : μr ≠ μ₁ := fun h => h1 (h ▸ hr)
      have h02 : μr ≠ conjugate μ₁ := fun h => h1 (isReal_conjugate_iff.mp (h ▸ hr))
      have h12 : μ₁ ≠ conjugate μ₁ := fun h => h1 (isReal_iff.mpr h.symm)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · rw [Fintype.card_fin, Embeddings.card, hM]

/-- The slot table: the slot `(i, j)` is sent to the pair `(k, m)` meaning `(λ_k, μ_m)`, with
`μ_0 = μ_r`, `μ_1 = μ₁`, `μ_2 = μ̄₁`. Diagonal `(i, i) ↦ (λ_i, μ_r)`; `(0,1) ↦ (λ₂, μ₁)`,
`(1,2) ↦ (λ₀, μ₁)`, `(2,0) ↦ (λ₁, μ₁)`, and `(j, i)` gets the conjugate `μ̄₁`. -/
def slotTable : Fin 3 × Fin 3 ≃ Fin 3 × Fin 3 where
  toFun p := ![![(0, 0), (2, 1), (1, 2)], ![(2, 2), (1, 0), (0, 1)], ![(1, 1), (0, 2), (2, 0)]]
    p.1 p.2
  invFun q := ![![(0, 0), (1, 2), (2, 1)], ![(1, 1), (2, 0), (0, 2)], ![(2, 2), (0, 1), (1, 0)]]
    q.1 q.2
  left_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl
  right_inv q := by
    rcases q with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl

variable (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3) (hK : finrank ℚ K = 9) [IsTotallyReal L]
  (hMr : nrRealPlaces M = 1) (lab : Fin 3 ≃ (L →+* ℂ)) (μ₁ : M →+* ℂ) (hμ₁ : ¬IsReal μ₁)

/-- **The slot assignment** `Fin 3 × Fin 3 ≃ (K →+* ℂ)`: slot `(i, i)` is the real embedding
`(λ_i, μ_r)`; slots `(0,1)`, `(1,2)`, `(2,0)` are `(λ₂, μ₁)`, `(λ₀, μ₁)`, `(λ₁, μ₁)`; slot
`(j, i)` is the complex conjugate of slot `(i, j)`. Here `λ_k = lab k`. -/
noncomputable def slotEquiv : Fin 3 × Fin 3 ≃ (K →+* ℂ) :=
  slotTable.trans ((lab.prodCongr (mEnum hM (isReal_realEmb hMr) hμ₁)).trans
    (embeddingsEquiv (linearDisjoint_of_hyp hL hM hK hMr) (sup_eq_top_of_hyp hL hM hK hMr)).symm)

theorem slotEquiv_apply (p : Fin 3 × Fin 3) :
    slotEquiv hL hM hK hMr lab μ₁ hμ₁ p =
      pairEmb (linearDisjoint_of_hyp hL hM hK hMr) (sup_eq_top_of_hyp hL hM hK hMr)
        (lab (slotTable p).1) (mEnum hM (isReal_realEmb hMr) hμ₁ (slotTable p).2) := rfl

theorem conjugate_mEnum (k : Fin 3) :
    mEnum hM (isReal_realEmb hMr) hμ₁ (![0, 2, 1] k) =
      conjugate (mEnum hM (isReal_realEmb hMr) hμ₁ k) := by
  fin_cases k
  · exact (isReal_iff.mp (isReal_realEmb hMr)).symm
  · rfl
  · exact (star_star μ₁).symm

/-- The diagonal slots are real embeddings. -/
theorem slotEquiv_diag_isReal (i : Fin 3) : IsReal (slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, i)) := by
  have h : slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, i) =
      pairEmb (linearDisjoint_of_hyp hL hM hK hMr) (sup_eq_top_of_hyp hL hM hK hMr)
        (lab i) (realEmb hMr) := by
    fin_cases i <;> rfl
  rw [h, isReal_iff_restrictPair (sup_eq_top_of_hyp hL hM hK hMr), restrictPair_pairEmb]
  exact ⟨IsTotallyReal.complexEmbedding_isReal _, isReal_realEmb hMr⟩

/-- The slot `(j, i)` is the complex conjugate of the slot `(i, j)`. -/
theorem slotEquiv_swap (i j : Fin 3) :
    slotEquiv hL hM hK hMr lab μ₁ hμ₁ (j, i) =
      conjugate (slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j)) := by
  rw [slotEquiv_apply, slotEquiv_apply, conjugate_pairEmb,
    isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal (lab _))]
  have e1 : (slotTable (j, i)).1 = (slotTable (i, j)).1 := by
    fin_cases i <;> fin_cases j <;> rfl
  have e2 : (slotTable (j, i)).2 = ![0, 2, 1] (slotTable (i, j)).2 := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [e1, e2, conjugate_mEnum hM hMr μ₁ hμ₁]

include hM hμ₁ in
/-- A product over the embeddings of `M`, as `μ_r, μ₁, μ̄₁`. -/
theorem prod_embeddings_right (f : (M →+* ℂ) → ℂ) :
    ∏ τ, f τ = f (realEmb hMr) * f μ₁ * f (conjugate μ₁) := by
  rw [← (mEnum hM (isReal_realEmb hMr) hμ₁).prod_comp, Fin.prod_univ_three]
  rfl

omit [IsTotallyReal L] in
/-- A product over the embeddings of `L`, through the labelling. -/
theorem prod_embeddings_left (f : (L →+* ℂ) → ℂ) :
    ∏ σ, f σ = f (lab 0) * f (lab 1) * f (lab 2) := by
  rw [← lab.prod_comp, Fin.prod_univ_three]

/-- **(c) The rank-one theorem, forward direction (any `x : K`).** If `N_{K/L} x = 1` and
`N_{K/M} x = 1`, the matrix of slot values `(slotEquiv (i, j) x)` is `w w*`. -/
theorem rankOne_of_norms (x : K) (hxL : Algebra.norm L x = 1) (hxM : Algebra.norm M x = 1) :
    ∃ w : Fin 3 → ℂ, ∀ i j, slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j) x = w i * conj (w j) := by
  set h₁ := linearDisjoint_of_hyp hL hM hK hMr
  set h₂ := sup_eq_top_of_hyp hL hM hK hMr
  set c : Fin 3 → ℂ := fun k => pairEmb h₁ h₂ (lab k) μ₁ x with hc_def
  have hreal : ∀ k, IsReal (pairEmb h₁ h₂ (lab k) (realEmb hMr)) := fun k => by
    rw [isReal_iff_restrictPair h₂, restrictPair_pairEmb]
    exact ⟨IsTotallyReal.complexEmbedding_isReal _, isReal_realEmb hMr⟩
  set r : Fin 3 → ℝ := fun k => (pairEmb h₁ h₂ (lab k) (realEmb hMr) x).re with hr_def
  have hr : ∀ k, (r k : ℂ) = pairEmb h₁ h₂ (lab k) (realEmb hMr) x := fun k =>
    (hreal k).coe_embedding_apply x
  have hcc : ∀ k, pairEmb h₁ h₂ (lab k) (conjugate μ₁) x = conj (c k) := fun k => by
    rw [hc_def]
    simp only
    rw [← conjugate_coe_eq, conjugate_pairEmb,
      isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal (lab k))]
  have h1 : ∀ k, (r k : ℂ) * c k * conj (c k) = 1 := by
    intro k
    have := map_norm_left h₁ h₂ (lab k) x
    rw [hxL, map_one, prod_embeddings_right hM hMr μ₁ hμ₁] at this
    rw [hr, ← hcc]
    exact this.symm
  have h2 : (r 0 : ℂ) * r 1 * r 2 = 1 := by
    have := map_norm_right h₁ h₂ (realEmb hMr) x
    rw [hxM, map_one, prod_embeddings_left lab] at this
    rw [hr, hr, hr]
    exact this.symm
  have h3 : c 0 * c 1 * c 2 = 1 := by
    have := map_norm_right h₁ h₂ μ₁ x
    rw [hxM, map_one, prod_embeddings_left lab] at this
    exact this.symm
  obtain ⟨w0, w1, w2, e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ :=
    rankOne_aux (h1 0) (h1 2) h2 h3
  refine ⟨![w0, w1, w2], fun i j => ?_⟩
  fin_cases i <;> fin_cases j
  · exact (hr 0).symm.trans e00.symm
  · exact e01.symm
  · exact (hcc 1).trans e02.symm
  · exact (hcc 2).trans e10.symm
  · exact (hr 1).symm.trans e11.symm
  · exact e12.symm
  · exact e20.symm
  · exact (hcc 0).trans e21.symm
  · exact (hr 2).symm.trans e22.symm

/-- **(c) The rank-one theorem for units.** A unit `u` has trivial relative norms to both cubic
subfields iff its matrix of slot values is rank one, `w w*`. -/
theorem rankOne_iff (u : (𝓞 K)ˣ) :
    (Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1) ↔
      ∃ w : Fin 3 → ℂ, ∀ i j, slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j) (u : K) =
        w i * conj (w j) := by
  constructor
  · rintro ⟨hL1, hM1⟩
    exact rankOne_of_norms hL hM hK hMr lab μ₁ hμ₁ _ hL1 hM1
  rintro ⟨w, hw⟩
  set h₁ := linearDisjoint_of_hyp hL hM hK hMr
  set h₂ := sup_eq_top_of_hyp hL hM hK hMr
  set e := slotEquiv hL hM hK hMr lab μ₁ hμ₁
  -- the product `P = |w₀|² |w₁|² |w₂|²` equals `1`
  set p : ℝ := Complex.normSq (w 0) * Complex.normSq (w 1) * Complex.normSq (w 2) with hp_def
  have hpc : (p : ℂ) = w 0 * conj (w 0) * (w 1 * conj (w 1)) * (w 2 * conj (w 2)) := by
    rw [hp_def, Complex.mul_conj, Complex.mul_conj, Complex.mul_conj]
    push_cast; ring
  have hp0 : 0 ≤ p := by
    rw [hp_def]
    exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _)
  have hN : ((Algebra.norm ℚ (u : K) : ℚ) : ℂ) = (p : ℂ) ^ 3 := by
    have h := algebraMap_norm_eq_prod (u : K)
    rw [eq_ratCast] at h
    rw [h, ← e.prod_comp, Fintype.prod_prod_type]
    simp only [Fin.prod_univ_three, hw, hpc]
    ring
  have hNr : ((Algebra.norm ℚ (u : K) : ℚ) : ℝ) = p ^ 3 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast, hN]
    push_cast; ring
  have hP : p = 1 := by
    rcases abs_eq zero_le_one |>.mp (NumberField.Units.norm K u) with h | h
    · rw [h, Rat.cast_one] at hNr
      exact (pow_eq_one_iff_of_nonneg hp0 (by norm_num)).mp hNr.symm
    · rw [h] at hNr
      push_cast at hNr
      nlinarith [pow_nonneg hp0 3]
  have hPc : w 0 * conj (w 0) * (w 1 * conj (w 1)) * (w 2 * conj (w 2)) = 1 := by
    rw [← hpc, hP, Complex.ofReal_one]
  constructor
  · apply (lab 0).injective
    have h := map_norm_left h₁ h₂ (lab 0) (u : K)
    rw [prod_embeddings_right hM hMr μ₁ hμ₁] at h
    have h' : (lab 0) (Algebra.norm L (u : K)) = e (0, 0) u * e (1, 2) u * e (2, 1) u := h
    rw [h', hw, hw, hw, map_one]
    linear_combination hPc
  · apply (realEmb hMr).injective
    have h := map_norm_right h₁ h₂ (realEmb hMr) (u : K)
    rw [prod_embeddings_left lab] at h
    have h' : (realEmb hMr) (Algebra.norm M (u : K)) = e (0, 0) u * e (1, 1) u * e (2, 2) u := h
    rw [h', hw, hw, hw, map_one]
    linear_combination hPc

/-- The trace `Tr_{F/ℚ}` as the sum over all complex embeddings. -/
theorem algebraMap_trace_eq_sum {F : Type*} [Field F] [NumberField F] (y : F) :
    algebraMap ℚ ℂ (Algebra.trace ℚ F y) = ∑ σ : F →+* ℂ, σ y := by
  rw [trace_eq_sum_embeddings ℂ (x := y)]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])).symm

/-- An element of a number field all of whose complex embeddings take the same value `P` is the
rational number `Tr(y)/[F:ℚ]`, and `P` is its image. -/
theorem eq_ratCast_of_forall_embeddings {F : Type*} [Field F] [NumberField F] {n : ℕ}
    (hn : finrank ℚ F = n) (hn0 : n ≠ 0) (y : F) (P : ℂ) (hy : ∀ σ : F →+* ℂ, σ y = P) :
    y = algebraMap ℚ F (Algebra.trace ℚ F y / n) ∧ ((Algebra.trace ℚ F y / n : ℚ) : ℂ) = P := by
  have htr := algebraMap_trace_eq_sum y
  simp only [hy, Finset.sum_const, Finset.card_univ, Embeddings.card, hn, nsmul_eq_mul,
    eq_ratCast] at htr
  have hP : ((Algebra.trace ℚ F y / n : ℚ) : ℂ) = P := by
    rw [Rat.cast_div, htr, Rat.cast_natCast]
    field_simp
  refine ⟨?_, hP⟩
  obtain ⟨σ⟩ := (inferInstance : Nonempty (F →+* ℂ))
  apply σ.injective
  rw [hy, eq_ratCast, map_ratCast, hP]

/-- **(c), stretch: the rank-one condition for any nonzero `x`.** For `x ≠ 0`, the slot matrix of
`x` is rank one, `w w*`, iff `N_{K/L} x = N_{K/M} x = c` for a positive rational `c`. -/
theorem rankOne_iff_norm_eq_ratCast (x : K) (hx : x ≠ 0) :
    (∃ w : Fin 3 → ℂ, ∀ i j, slotEquiv hL hM hK hMr lab μ₁ hμ₁ (i, j) x = w i * conj (w j)) ↔
      ∃ c : ℚ, 0 < c ∧ Algebra.norm L x = algebraMap ℚ L c ∧
        Algebra.norm M x = algebraMap ℚ M c := by
  set h₁ := linearDisjoint_of_hyp hL hM hK hMr
  set h₂ := sup_eq_top_of_hyp hL hM hK hMr
  set e := slotEquiv hL hM hK hMr lab μ₁ hμ₁
  constructor
  · rintro ⟨w, hw⟩
    set p : ℝ := Complex.normSq (w 0) * Complex.normSq (w 1) * Complex.normSq (w 2) with hp_def
    have hpc : (p : ℂ) = w 0 * conj (w 0) * (w 1 * conj (w 1)) * (w 2 * conj (w 2)) := by
      rw [hp_def, Complex.mul_conj, Complex.mul_conj, Complex.mul_conj]
      push_cast; ring
    have hw0 : ∀ i, w i ≠ 0 := by
      intro i hi
      have := hw i i
      rw [hi, zero_mul] at this
      exact hx ((map_eq_zero _).mp this)
    have hp : 0 < p := by
      rw [hp_def]
      exact mul_pos (mul_pos (Complex.normSq_pos.mpr (hw0 0)) (Complex.normSq_pos.mpr (hw0 1)))
        (Complex.normSq_pos.mpr (hw0 2))
    -- all embeddings of `N_{K/L} x` equal `p`
    have hL' : ∀ σ : L →+* ℂ, σ (Algebra.norm L x) = p := by
      intro σ
      obtain ⟨k, rfl⟩ := lab.surjective σ
      rw [map_norm_left h₁ h₂, prod_embeddings_right hM hMr μ₁ hμ₁, hpc]
      fin_cases k
      · change e (0, 0) x * e (1, 2) x * e (2, 1) x = _
        rw [hw, hw, hw]; ring
      · change e (1, 1) x * e (2, 0) x * e (0, 2) x = _
        rw [hw, hw, hw]; ring
      · change e (2, 2) x * e (0, 1) x * e (1, 0) x = _
        rw [hw, hw, hw]; ring
    have hM' : ∀ τ : M →+* ℂ, τ (Algebra.norm M x) = p := by
      intro τ
      obtain ⟨m, rfl⟩ := (mEnum hM (isReal_realEmb hMr) hμ₁).surjective τ
      rw [map_norm_right h₁ h₂, prod_embeddings_left lab, hpc]
      fin_cases m
      · change e (0, 0) x * e (1, 1) x * e (2, 2) x = _
        rw [hw, hw, hw]
      · change e (1, 2) x * e (2, 0) x * e (0, 1) x = _
        rw [hw, hw, hw]; ring
      · change e (2, 1) x * e (0, 2) x * e (1, 0) x = _
        rw [hw, hw, hw]; ring
    obtain ⟨hyL, hcL⟩ := eq_ratCast_of_forall_embeddings hL (by norm_num) _ _ hL'
    obtain ⟨hyM, hcM⟩ := eq_ratCast_of_forall_embeddings hM (by norm_num) _ _ hM'
    have heq : (Algebra.trace ℚ M (Algebra.norm M x) / (3 : ℕ) : ℚ) =
        Algebra.trace ℚ L (Algebra.norm L x) / (3 : ℕ) := by
      exact_mod_cast hcM.trans hcL.symm
    refine ⟨Algebra.trace ℚ L (Algebra.norm L x) / (3 : ℕ), ?_, hyL, heq ▸ hyM⟩
    have : ((Algebra.trace ℚ L (Algebra.norm L x) / (3 : ℕ) : ℚ) : ℝ) = p := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_ratCast, hcL]
    exact_mod_cast this ▸ hp
  · rintro ⟨q, hq, hxL, hxM⟩
    set c : Fin 3 → ℂ := fun k => pairEmb h₁ h₂ (lab k) μ₁ x with hc_def
    have hreal : ∀ k, IsReal (pairEmb h₁ h₂ (lab k) (realEmb hMr)) := fun k => by
      rw [isReal_iff_restrictPair h₂, restrictPair_pairEmb]
      exact ⟨IsTotallyReal.complexEmbedding_isReal _, isReal_realEmb hMr⟩
    set r : Fin 3 → ℝ := fun k => (pairEmb h₁ h₂ (lab k) (realEmb hMr) x).re with hr_def
    have hr : ∀ k, (r k : ℂ) = pairEmb h₁ h₂ (lab k) (realEmb hMr) x := fun k =>
      (hreal k).coe_embedding_apply x
    have hcc : ∀ k, pairEmb h₁ h₂ (lab k) (conjugate μ₁) x = conj (c k) := fun k => by
      rw [hc_def]
      simp only
      rw [← conjugate_coe_eq, conjugate_pairEmb,
        isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal (lab k))]
    have hqC : ((q : ℝ) : ℂ) = (q : ℂ) := Complex.ofReal_ratCast q
    have h1 : ∀ k, (r k : ℂ) * c k * conj (c k) = ((q : ℝ) : ℂ) := by
      intro k
      have := map_norm_left h₁ h₂ (lab k) x
      rw [hxL, eq_ratCast, map_ratCast, prod_embeddings_right hM hMr μ₁ hμ₁] at this
      rw [hr, ← hcc, hqC]
      exact this.symm
    have h2 : (r 0 : ℂ) * r 1 * r 2 = ((q : ℝ) : ℂ) := by
      have := map_norm_right h₁ h₂ (realEmb hMr) x
      rw [hxM, eq_ratCast, map_ratCast, prod_embeddings_left lab] at this
      rw [hr, hr, hr, hqC]
      exact this.symm
    have h3 : c 0 * c 1 * c 2 = ((q : ℝ) : ℂ) := by
      have := map_norm_right h₁ h₂ μ₁ x
      rw [hxM, eq_ratCast, map_ratCast, prod_embeddings_left lab] at this
      rw [hqC]
      exact this.symm
    obtain ⟨w0, w1, w2, e00, e01, e02, e10, e11, e12, e20, e21, e22⟩ :=
      rankOne_aux_scaled (by exact_mod_cast hq) (h1 0) (h1 2) h2 h3
    refine ⟨![w0, w1, w2], fun i j => ?_⟩
    fin_cases i <;> fin_cases j
    · exact (hr 0).symm.trans e00.symm
    · exact e01.symm
    · exact (hcc 1).trans e02.symm
    · exact (hcc 2).trans e10.symm
    · exact (hr 1).symm.trans e11.symm
    · exact e12.symm
    · exact e20.symm
    · exact (hcc 0).trans e21.symm
    · exact (hr 2).symm.trans e22.symm

end Main

section Corollary

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

/-- A cubic field with one real place has a non-real embedding. -/
theorem exists_not_isReal (hM : finrank ℚ M = 3) (hMr : nrRealPlaces M = 1) :
    ∃ μ : M →+* ℂ, ¬IsReal μ := by
  classical
  have h1 := card_complex_embeddings (K := M)
  have h2 := card_add_two_mul_card_eq_rank M
  rw [hM, hMr] at h2
  have hc : nrComplexPlaces M = 1 := by omega
  rw [hc] at h1
  obtain ⟨φ⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_eq (by norm_num) h1.symm)
  exact ⟨φ.1, φ.2⟩

/-- **(c), existential form.** Some bijection `e : Fin 3 × Fin 3 ≃ (K →+* ℂ)` with real diagonal
and `e (j, i) = conj (e (i, j))` detects the units with trivial relative norms as exactly those
whose slot matrix is rank one. -/
theorem exists_slotEquiv_rankOne_iff (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) :
    ∃ e : Fin 3 × Fin 3 ≃ (K →+* ℂ), (∀ i, IsReal (e (i, i))) ∧
      (∀ i j, e (j, i) = conjugate (e (i, j))) ∧
      ∀ u : (𝓞 K)ˣ, (Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1) ↔
        ∃ w : Fin 3 → ℂ, ∀ i j, e (i, j) (u : K) = w i * conj (w j) := by
  obtain ⟨μ₁, hμ₁⟩ := exists_not_isReal hM hMr
  let lab : Fin 3 ≃ (L →+* ℂ) := (Fintype.equivFinOfCardEq (by rw [Embeddings.card, hL])).symm
  exact ⟨slotEquiv hL hM hK hMr lab μ₁ hμ₁, slotEquiv_diag_isReal hL hM hK hMr lab μ₁ hμ₁,
    slotEquiv_swap hL hM hK hMr lab μ₁ hμ₁, rankOne_iff hL hM hK hMr lab μ₁ hμ₁⟩

end Corollary

/-! ### (d) The group `H` of units with trivial relative norms -/

section Rank

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

open NumberField.Units

omit [NumberField K] in
theorem coe_units_inv_eq (u : (𝓞 K)ˣ) : ((u⁻¹ : (𝓞 K)ˣ) : K) = (u : K)⁻¹ :=
  map_units_inv (algebraMap (𝓞 K) K) u

theorem norm_mul_norm_units_inv (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ) :
    Algebra.norm F (u : K) * Algebra.norm F ((u⁻¹ : (𝓞 K)ˣ) : K) = 1 := by
  rw [← map_mul, ← coe_mul, mul_inv_cancel, coe_one, map_one]

variable (L M) in
/-- **The group `H`**: units of `𝓞 K` whose relative norms to `L` and to `M` are both `1`. -/
def relNormKernel : Subgroup (𝓞 K)ˣ where
  carrier := {u | Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    simp only [Set.mem_ofPred_eq, coe_mul, map_mul, ha1, ha2, hb1, hb2, mul_one, and_self]
  one_mem' := by simp only [Set.mem_ofPred_eq, coe_one, map_one, and_self]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have key : ∀ F : IntermediateField ℚ K, Algebra.norm F (a : K) = 1 →
        Algebra.norm F ((a⁻¹ : (𝓞 K)ˣ) : K) = 1 := by
      intro F hF
      have h := norm_mul_norm_units_inv F a
      rwa [hF, one_mul] at h
    exact ⟨key L ha1, key M ha2⟩

theorem mem_relNormKernel {u : (𝓞 K)ˣ} :
    u ∈ relNormKernel L M ↔ Algebra.norm L (u : K) = 1 ∧ Algebra.norm M (u : K) = 1 := Iff.rfl

/-- **`H` is torsion-free**: `H ⊓ torsion K = ⊥` (the degree `9` is odd, so the torsion is `±1`,
and `N_{K/L}(-1) = (-1)³ = -1`). -/
theorem relNormKernel_inf_torsion (hL : finrank ℚ L = 3) (hK : finrank ℚ K = 9) :
    relNormKernel L M ⊓ torsion K = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hH, ht⟩
  rw [Subgroup.mem_bot]
  rcases torsion_eq_one_or_neg_one_of_odd_finrank (by rw [hK]; decide) ⟨u, ht⟩ with h | h
  · exact h
  · exfalso
    have h' : u = -1 := h
    have hfin : finrank L K = 3 := by
      have := Module.finrank_mul_finrank ℚ L K
      rw [hL, hK] at this
      omega
    have h1 := hH.1
    rw [h', coe_neg_one, show (-1 : K) = algebraMap L K (-1) by simp, Algebra.norm_algebraMap,
      hfin] at h1
    norm_num at h1

/-- The relative norm `N_{K/F}(u)` of a unit, as a unit of `𝓞 K`. -/
noncomputable def normUnit (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ) : (𝓞 K)ˣ :=
  Units.mkOfMulEqOne
    (⟨algebraMap F K (Algebra.norm F (u : K)), (mem_integralClosure_iff ℤ K).mpr
      (Algebra.isIntegral_norm F (RingOfIntegers.isIntegral_coe (u : 𝓞 K))).algebraMap⟩ : 𝓞 K)
    (⟨algebraMap F K (Algebra.norm F ((u⁻¹ : (𝓞 K)ˣ) : K)), (mem_integralClosure_iff ℤ K).mpr
      (Algebra.isIntegral_norm F
        (RingOfIntegers.isIntegral_coe ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))).algebraMap⟩ : 𝓞 K)
    (RingOfIntegers.ext <| by
      have h : algebraMap F K (Algebra.norm F (u : K)) *
          algebraMap F K (Algebra.norm F ((u⁻¹ : (𝓞 K)ˣ) : K)) = 1 := by
        rw [← map_mul, norm_mul_norm_units_inv, map_one]
      exact h)

theorem coe_normUnit (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ) :
    (normUnit F u : K) = algebraMap F K (Algebra.norm F (u : K)) := rfl

variable (L M) in
/-- The projection `π(u) = (u⁹ N_{K/L}(u)⁻³ N_{K/M}(u)⁻³)²` of a unit into `H`. -/
noncomputable def proj (u : (𝓞 K)ˣ) : (𝓞 K)ˣ :=
  (u ^ 9 * (normUnit L u)⁻¹ ^ 3 * (normUnit M u)⁻¹ ^ 3) ^ 2

theorem coe_proj (u : (𝓞 K)ˣ) :
    (proj L M u : K) = ((u : K) ^ 9 * (algebraMap L K (Algebra.norm L (u : K)))⁻¹ ^ 3 *
      (algebraMap M K (Algebra.norm M (u : K)))⁻¹ ^ 3) ^ 2 := by
  simp only [proj, coe_pow, coe_mul, coe_units_inv_eq, coe_normUnit]

theorem sq_inv_pow_three_algebraMap {F : Type*} [Field F] [Algebra ℚ F] {q : ℚ} (hq : q ^ 2 = 1) :
    ((algebraMap ℚ F q)⁻¹ ^ 3) ^ 2 = 1 := by
  rw [← map_inv₀, ← map_pow, ← map_pow, show (q⁻¹ ^ 3) ^ 2 = ((q ^ 2) ^ 3)⁻¹ by ring, hq]
  simp

/-- `π(u) ∈ H` for every unit `u`. -/
theorem proj_mem (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) (u : (𝓞 K)ˣ) :
    proj L M u ∈ relNormKernel L M := by
  have h₁ := linearDisjoint_of_hyp hL hM hK hMr
  have h₂ := sup_eq_top_of_hyp hL hM hK hMr
  have hx : (u : K) ≠ 0 := coe_ne_zero u
  have hq : Algebra.norm ℚ (u : K) ^ 2 = 1 := by
    rcases abs_eq zero_le_one |>.mp (NumberField.Units.norm K u) with h | h <;> rw [h] <;> norm_num
  constructor
  · rw [coe_proj, map_pow, norm_proj_left h₁ h₂ hM hx]
    exact sq_inv_pow_three_algebraMap hq
  · rw [coe_proj, map_pow, mul_right_comm _ (_ ^ 3) (_ ^ 3),
      norm_proj_left h₁.symm (sup_comm L M ▸ h₂) hL hx]
    exact sq_inv_pow_three_algebraMap hq

/-- **(d), minimum: `H` is nontrivial.** There is a unit `u ≠ 1` with `N_{K/L} u = N_{K/M} u = 1`
(hence, `H` being torsion-free, of infinite order). It is `π(v)` for a Dirichlet unit `v` that
is large at one real place `(λ, μ_r)` and small at every other place. -/
theorem exists_mem_relNormKernel_ne_one (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) :
    ∃ u ∈ relNormKernel L M, u ≠ 1 := by
  classical
  have h₁ := linearDisjoint_of_hyp hL hM hK hMr
  have h₂ := sup_eq_top_of_hyp hL hM hK hMr
  obtain ⟨σ0⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have hφ0 : IsReal (pairEmb h₁ h₂ σ0 (realEmb hMr)) := by
    rw [isReal_iff_restrictPair h₂, restrictPair_pairEmb]
    exact ⟨IsTotallyReal.complexEmbedding_isReal _, isReal_realEmb hMr⟩
  obtain ⟨v, hv⟩ := dirichletUnitTheorem.exists_unit (K := K)
    (InfinitePlace.mk (pairEmb h₁ h₂ σ0 (realEmb hMr)))
  have hpos : ∀ φ : K →+* ℂ, 0 < ‖φ (v : K)‖ := fun φ =>
    norm_pos_iff.mpr ((map_ne_zero φ).mpr (coe_ne_zero v))
  have hsmall : ∀ φ : K →+* ℂ, φ ≠ pairEmb h₁ h₂ σ0 (realEmb hMr) → ‖φ (v : K)‖ < 1 := by
    intro φ hφ
    have hne : InfinitePlace.mk φ ≠ InfinitePlace.mk (pairEmb h₁ h₂ σ0 (realEmb hMr)) := by
      rw [Ne, InfinitePlace.mk_eq_iff]
      rintro (h | h)
      · exact hφ h
      · apply hφ
        calc φ = conjugate (conjugate φ) := (star_star φ).symm
          _ = conjugate (pairEmb h₁ h₂ σ0 (realEmb hMr)) := by rw [h]
          _ = pairEmb h₁ h₂ σ0 (realEmb hMr) := isReal_iff.mp hφ0
    have := hv _ hne
    rw [InfinitePlace.apply] at this
    exact (Real.log_neg_iff (hpos φ)).mp this
  -- the product formula `∏ ‖φ v‖ = |N v| = 1` and the big coordinate
  have hprod : ∏ φ : K →+* ℂ, ‖φ (v : K)‖ = 1 := by
    rw [← norm_prod, ← algebraMap_norm_eq_prod, eq_ratCast, Complex.norm_ratCast]
    exact_mod_cast NumberField.Units.norm K v
  set a := ‖pairEmb h₁ h₂ σ0 (realEmb hMr) (v : K)‖ with ha_def
  have hbig : 1 < a := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (pairEmb h₁ h₂ σ0 (realEmb hMr)))]
      at hprod
    have hcard : (Finset.univ.erase (pairEmb h₁ h₂ σ0 (realEmb hMr))).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Embeddings.card, hK]
      norm_num
    obtain ⟨ψ, hψ⟩ := hcard
    have hrest : ∏ φ ∈ Finset.univ.erase (pairEmb h₁ h₂ σ0 (realEmb hMr)), ‖φ (v : K)‖ < 1 := by
      rw [← Finset.mul_prod_erase _ _ hψ]
      have h1 : ‖ψ (v : K)‖ < 1 := hsmall ψ (Finset.ne_of_mem_erase hψ)
      have h2 : ∏ φ ∈ (Finset.univ.erase (pairEmb h₁ h₂ σ0 (realEmb hMr))).erase ψ,
          ‖φ (v : K)‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun φ hφ =>
          (hsmall φ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hφ))).le
      calc _ ≤ ‖ψ (v : K)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact h1
    have hrpos : 0 < ∏ φ ∈ Finset.univ.erase (pairEmb h₁ h₂ σ0 (realEmb hMr)), ‖φ (v : K)‖ :=
      Finset.prod_pos fun φ _ => hpos φ
    nlinarith
  -- the two relative norms are at most `a` at the place
  have hA : ‖σ0 (Algebra.norm L (v : K))‖ ≤ a := by
    rw [map_norm_left h₁ h₂ σ0, norm_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (realEmb hMr))]
    refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      fun τ hτ => (hsmall _ fun h => Finset.ne_of_mem_erase hτ (pairEmb_inj h₁ h₂ h).2).le)
  have hB : ‖(realEmb hMr) (Algebra.norm M (v : K))‖ ≤ a := by
    rw [map_norm_right h₁ h₂ (realEmb hMr), norm_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ0)]
    refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      fun σ hσ => (hsmall _ fun h => Finset.ne_of_mem_erase hσ (pairEmb_inj h₁ h₂ h).1).le)
  have hApos : 0 < ‖σ0 (Algebra.norm L (v : K))‖ :=
    norm_pos_iff.mpr ((map_ne_zero _).mpr (Algebra.norm_ne_zero_iff.mpr (coe_ne_zero v)))
  have hBpos : 0 < ‖(realEmb hMr) (Algebra.norm M (v : K))‖ :=
    norm_pos_iff.mpr ((map_ne_zero _).mpr (Algebra.norm_ne_zero_iff.mpr (coe_ne_zero v)))
  refine ⟨proj L M v, proj_mem hL hM hK hMr v, fun h1 => ?_⟩
  have hval := congrArg (fun z : (𝓞 K)ˣ => ‖pairEmb h₁ h₂ σ0 (realEmb hMr) (z : K)‖) h1
  simp only [coe_proj, coe_one, map_one, norm_one, map_pow, map_mul, map_inv₀,
    pairEmb_algebraMap_left, pairEmb_algebraMap_right, norm_pow, norm_mul, norm_inv] at hval
  rw [← ha_def] at hval
  set A := ‖σ0 (Algebra.norm L (v : K))‖
  set B := ‖(realEmb hMr) (Algebra.norm M (v : K))‖
  have hAB : A ^ 3 * B ^ 3 < a ^ 9 := by
    calc A ^ 3 * B ^ 3 ≤ a ^ 3 * a ^ 3 :=
          mul_le_mul (pow_le_pow_left₀ hApos.le hA 3) (pow_le_pow_left₀ hBpos.le hB 3)
            (by positivity) (by positivity)
      _ = a ^ 6 := by ring
      _ < a ^ 9 := pow_lt_pow_right₀ hbig (by norm_num)
  have hkey : 1 < a ^ 9 * A⁻¹ ^ 3 * B⁻¹ ^ 3 := by
    rw [inv_pow, inv_pow, mul_assoc, ← mul_inv, ← div_eq_mul_inv]
    exact (one_lt_div (by positivity)).mpr hAB
  have := one_lt_pow₀ hkey (two_ne_zero)
  rw [hval] at this
  exact lt_irrefl _ this

end Rank

/-! ### (d) The rank of `H` is `2` -/

section RankTwo

universe u

/-- ℤ-rank-nullity for a finitely generated abelian group. -/
theorem finrank_ker_add_finrank_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] (f : A →ₗ[ℤ] B) :
    finrank ℤ (LinearMap.ker f) + finrank ℤ (LinearMap.range f) = finrank ℤ A := by
  rw [← (LinearMap.quotKerEquivRange f).finrank_eq, add_comm]
  exact Submodule.finrank_quotient_add_finrank _

/-- A torsion abelian group has `ℤ`-rank `0`. -/
theorem finrank_eq_zero_of_torsion {A : Type*} [AddCommGroup A]
    (h : ∀ x : A, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0) : finrank ℤ A = 0 := by
  apply Module.finrank_eq_zero_of_rank_eq_zero
  rw [rank_eq_zero_iff]
  intro x
  obtain ⟨n, hn, hx⟩ := h x
  exact ⟨n, by exact_mod_cast hn, by rwa [natCast_zsmul]⟩

theorem finrank_prod_le {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module.Finite ℤ A]
    [Module.Finite ℤ B] : finrank ℤ (A × B) ≤ finrank ℤ A + finrank ℤ B := by
  have h := finrank_ker_add_finrank_range (LinearMap.snd ℤ A B)
  rw [LinearMap.ker_snd] at h
  have h1 : finrank ℤ (LinearMap.range (LinearMap.inl ℤ A B)) ≤ finrank ℤ A :=
    LinearMap.finrank_range_le _
  have h2 : finrank ℤ (LinearMap.range (LinearMap.snd ℤ A B)) ≤ finrank ℤ B :=
    Submodule.finrank_le _
  omega

theorem le_finrank_prod {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module.Finite ℤ A]
    [Module.Finite ℤ B] : finrank ℤ A + finrank ℤ B ≤ finrank ℤ (A × B) := by
  have h := rank_add_rank_le_rank_prod (R := ℤ) (M := A) (M₁ := B)
  unfold finrank
  rw [← Cardinal.toNat_add (Module.rank_lt_aleph0 ℤ A) (Module.rank_lt_aleph0 ℤ B)]
  exact Cardinal.toNat_le_toNat h (Module.rank_lt_aleph0 _ _)

variable {K : Type*} [Field K] [NumberField K] {L M : IntermediateField ℚ K}

open NumberField.Units

/-- The relative norm on units, `(𝓞 K)ˣ →* (𝓞 F)ˣ`. -/
noncomputable def normHom (F : IntermediateField ℚ K) : (𝓞 K)ˣ →* (𝓞 F)ˣ :=
  Units.map (RingOfIntegers.norm F)

theorem coe_normHom (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ) :
    ((normHom F u : (𝓞 F)ˣ) : F) = Algebra.norm F (u : K) := rfl

theorem normHom_eq_one_iff (F : IntermediateField ℚ K) (u : (𝓞 K)ˣ) :
    normHom F u = 1 ↔ Algebra.norm F (u : K) = 1 := by
  rw [← coe_normHom]
  exact (coe_injective F).eq_iff.symm.trans (by rw [coe_one])

variable (L M) in
/-- The pair of relative norms, as a `ℤ`-linear map of additive unit groups. Its kernel is `H`. -/
noncomputable def normPair : Additive (𝓞 K)ˣ →ₗ[ℤ] Additive (𝓞 L)ˣ × Additive (𝓞 M)ˣ :=
  ((normHom L).toAdditive.prod (normHom M).toAdditive).toIntLinearMap

theorem mem_ker_normPair {x : Additive (𝓞 K)ˣ} :
    x ∈ LinearMap.ker (normPair L M) ↔ x.toMul ∈ relNormKernel L M := by
  rw [LinearMap.mem_ker, mem_relNormKernel, ← normHom_eq_one_iff, ← normHom_eq_one_iff]
  simp only [normPair, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.prod_apply, Prod.mk_eq_zero,
    MonoidHom.toAdditive_apply_apply, ofMul_eq_zero]

/-- `H` and the kernel of `normPair` as `ℤ`-modules. -/
noncomputable def kerEquiv :
    Additive (relNormKernel L M) ≃ₗ[ℤ] LinearMap.ker (normPair L M) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun x => ⟨Additive.ofMul (x.toMul : (𝓞 K)ˣ), mem_ker_normPair.mpr x.toMul.2⟩
      invFun := fun y => Additive.ofMul ⟨y.1.toMul, mem_ker_normPair.mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- The inclusion of the units of a subfield, `(𝓞 F)ˣ →* (𝓞 K)ˣ`. -/
noncomputable def inclHom (F : IntermediateField ℚ K) : (𝓞 F)ˣ →* (𝓞 K)ˣ :=
  Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom

theorem coe_inclHom (F : IntermediateField ℚ K) (x : (𝓞 F)ˣ) :
    ((inclHom F x : (𝓞 K)ˣ) : K) = algebraMap F K (x : F) := rfl

variable (L M) in
/-- `(l, m) ↦ l m`, as a `ℤ`-linear map of additive unit groups. -/
noncomputable def inclPair : Additive (𝓞 L)ˣ × Additive (𝓞 M)ˣ →ₗ[ℤ] Additive (𝓞 K)ˣ :=
  ((inclHom L).toAdditive.coprod (inclHom M).toAdditive).toIntLinearMap

theorem rank_of_places {F : Type*} [Field F] [NumberField F] {r c : ℕ}
    (hr : nrRealPlaces F = r) (hc : nrComplexPlaces F = c) :
    finrank ℤ (Additive (𝓞 F)ˣ) = r + c - 1 := by
  rw [finrank_eq, Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces, hr, hc]

/-- A unit of a cubic field has `N(x)² = 1`. -/
theorem norm_sq_units {F : Type*} [Field F] [NumberField F] (x : (𝓞 F)ˣ) :
    Algebra.norm ℚ (x : F) ^ 2 = 1 := by
  rcases abs_eq zero_le_one |>.mp (NumberField.Units.norm F x) with h | h <;> rw [h] <;> norm_num

/-- **(d) The rank of `H`.** `H ≅ ℤ²`: its `ℤ`-rank is `2` (and it is torsion-free,
`relNormKernel_inf_torsion`). -/
theorem finrank_relNormKernel (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) :
    finrank ℤ (Additive (relNormKernel L M)) = 2 := by
  have h₁ := linearDisjoint_of_hyp hL hM hK hMr
  have h₂ := sup_eq_top_of_hyp hL hM hK hMr
  -- the three unit ranks
  have hLr : nrRealPlaces L = 3 := (IsTotallyReal.finrank L).symm.trans hL
  have hLc : nrComplexPlaces L = 0 := IsTotallyReal.nrComplexPlaces_eq_zero L
  have hMc : nrComplexPlaces M = 1 := by
    have := card_add_two_mul_card_eq_rank M
    omega
  have hKr : nrRealPlaces K = 3 := by
    rw [nrRealPlaces_compositum h₁ h₂, hLr, hMr]
  have hKc : nrComplexPlaces K = 3 := by
    have := nrRealPlaces_mul_add_two_mul_nrComplexPlaces_compositum h₁ h₂
    rw [hLr, hMr, hL, hM] at this
    omega
  have rK : finrank ℤ (Additive (𝓞 K)ˣ) = 5 := by rw [rank_of_places hKr hKc]
  have rL : finrank ℤ (Additive (𝓞 L)ˣ) = 2 := by rw [rank_of_places hLr hLc]
  have rM : finrank ℤ (Additive (𝓞 M)ˣ) = 1 := by rw [rank_of_places hMr hMc]
  have hnull := finrank_ker_add_finrank_range (normPair L M)
  rw [← (kerEquiv (L := L) (M := M)).finrank_eq, rK] at hnull
  -- upper bound on the range
  have hup : finrank ℤ (LinearMap.range (normPair L M)) ≤ 3 := by
    have := (Submodule.finrank_le (LinearMap.range (normPair L M))).trans
      (finrank_prod_le (A := Additive (𝓞 L)ˣ) (B := Additive (𝓞 M)ˣ))
    omega
  -- lower bound on the range: `normPair ∘ inclPair` has torsion kernel
  have hfL : finrank L K = 3 := by
    have := Module.finrank_mul_finrank ℚ L K
    rw [hL, hK] at this
    omega
  have hfM : finrank M K = 3 := by
    have := Module.finrank_mul_finrank ℚ M K
    rw [hM, hK] at this
    omega
  have htors : ∀ x ∈ LinearMap.ker ((normPair L M).comp (inclPair L M)), (6 : ℕ) • x = 0 := by
    rintro ⟨a, b⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hx' := (Prod.mk_eq_zero.mp hx)
    simp only [inclPair, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coprod_apply, map_add,
      MonoidHom.toAdditive_apply_apply] at hx'
    obtain ⟨hxa, hxb⟩ := hx'
    have ha := congrArg (fun z => ((Additive.toMul z : (𝓞 L)ˣ) : L)) hxa
    have hb := congrArg (fun z => ((Additive.toMul z : (𝓞 M)ˣ) : M)) hxb
    simp only [toMul_add, toMul_ofMul, toMul_zero, coe_mul, coe_one, coe_normHom,
      coe_inclHom] at ha hb
    rw [Algebra.norm_algebraMap, hfL, norm_algebraMap_right h₁ h₂] at ha
    rw [Algebra.norm_algebraMap, hfM, mul_comm,
      norm_algebraMap_right h₁.symm (sup_comm L M ▸ h₂)] at hb
    have ha6 : ((a.toMul : (𝓞 L)ˣ) : L) ^ 6 = 1 := by
      have hq := norm_sq_units b.toMul
      have h2 : (((a.toMul : (𝓞 L)ˣ) : L) ^ 3 *
          algebraMap ℚ L (Algebra.norm ℚ ((b.toMul : (𝓞 M)ˣ) : M))) ^ 2 = 1 := by
        rw [ha, one_pow]
      rw [mul_pow, ← map_pow (algebraMap ℚ L), hq, map_one, mul_one, ← pow_mul] at h2
      exact h2
    have hb6 : ((b.toMul : (𝓞 M)ˣ) : M) ^ 6 = 1 := by
      have hq := norm_sq_units a.toMul
      have h2 : (((b.toMul : (𝓞 M)ˣ) : M) ^ 3 *
          algebraMap ℚ M (Algebra.norm ℚ ((a.toMul : (𝓞 L)ˣ) : L))) ^ 2 = 1 := by
        rw [hb, one_pow]
      rw [mul_pow, ← map_pow (algebraMap ℚ M), hq, map_one, mul_one, ← pow_mul] at h2
      exact h2
    refine Prod.ext ?_ ?_
    · show (6 : ℕ) • a = 0
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      apply coe_injective L
      simp only [coe_pow, coe_one]
      exact ha6
    · show (6 : ℕ) • b = 0
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      apply coe_injective M
      simp only [coe_pow, coe_one]
      exact hb6
  have hker0 : finrank ℤ (LinearMap.ker ((normPair L M).comp (inclPair L M))) = 0 :=
    finrank_eq_zero_of_torsion fun x => ⟨6, by norm_num, Subtype.ext (htors x.1 x.2)⟩
  have hnull2 := finrank_ker_add_finrank_range ((normPair L M).comp (inclPair L M))
  rw [hker0, zero_add] at hnull2
  have hprod := le_finrank_prod (A := Additive (𝓞 L)ˣ) (B := Additive (𝓞 M)ˣ)
  rw [rL, rM] at hprod
  have hmono : finrank ℤ (LinearMap.range ((normPair L M).comp (inclPair L M))) ≤
      finrank ℤ (LinearMap.range (normPair L M)) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  omega

/-- **(d), in `logEmbedding` form.** The `ℤ`-span of the logarithmic embedding of `H` (Mathlib's
`NumberField.Units.logEmbedding`, the log vector with the place `w₀` dropped) has rank `2`. -/
theorem finrank_span_logEmbedding_relNormKernel (hL : finrank ℚ L = 3) (hM : finrank ℚ M = 3)
    (hK : finrank ℚ K = 9) [IsTotallyReal L] (hMr : nrRealPlaces M = 1) :
    finrank ℤ (Submodule.span ℤ
      ((logEmbedding K) '' {x : Additive (𝓞 K)ˣ | x.toMul ∈ relNormKernel L M})) = 2 := by
  have himg : (logEmbedding K) '' {x : Additive (𝓞 K)ˣ | x.toMul ∈ relNormKernel L M} =
      ((LinearMap.ker (normPair L M)).map (logEmbedding K).toIntLinearMap : Set _) := by
    rw [Submodule.map_coe]
    congr 1
    ext x
    exact mem_ker_normPair.symm
  rw [himg, Submodule.span_eq, ← LinearMap.range_domRestrict]
  have hinj : Function.Injective
      ((logEmbedding K).toIntLinearMap.domRestrict (LinearMap.ker (normPair L M))) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have ht : x.1.toMul ∈ torsion K :=
      (dirichletUnitTheorem.logEmbedding_eq_zero_iff (x := x.1.toMul)).mp hx
    have h1 : x.1.toMul ∈ relNormKernel L M ⊓ torsion K := ⟨mem_ker_normPair.mp x.2, ht⟩
    rw [relNormKernel_inf_torsion hL hK, Subgroup.mem_bot] at h1
    exact Subtype.ext (Additive.toMul.injective (h1.trans toMul_zero.symm))
  rw [← (LinearEquiv.ofInjective _ hinj).finrank_eq, ← (kerEquiv (L := L) (M := M)).finrank_eq]
  exact finrank_relNormKernel hL hM hK hMr

end RankTwo

end ReversibleUnits
