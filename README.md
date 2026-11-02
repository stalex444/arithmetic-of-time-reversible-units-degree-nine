# Reversible units of a degree-nine field

Kernel-checked, in Lean 4 + Mathlib: in every number field `K` of degree 9 that contains a totally
real cubic field `L` and a cubic field `M` with one real place, the units whose nine conjugates form
a rank-one Hermitian matrix `w w*` are exactly the units with trivial relative norm to both `L` and
`M`. They form a torsion-free group `H` of rank 2 (so `H ≅ ℤ²`; the isomorphism is not itself a
Lean term). Equivalently, `H` is exactly the set of units `u` for which the Schur multipliers of `u`
and of `u⁻¹` are both completely positive. In degree four, by contrast, a unit `u ≠ 1` runs both
ways only if its complex conjugate lies on the unit circle.

## The objects

`K = LM` has three real and three complex places, and its nine embeddings are the pairs `(λ, μ)`.
Fix a labelling `λ₀, λ₁, λ₂` of the (real) embeddings of `L`, the real embedding `μ_r` of `M`, and
a non-real embedding `μ₁`. The **slot assignment** puts `(λ_i, μ_r)` in the diagonal slot `(i, i)`,
`(λ_{−(i+j)}, μ₁)` in the slots `(0,1)`, `(1,2)`, `(2,0)`, and their complex conjugates in the
transposed slots (indices mod 3). The **symbol** of `x ∈ K` is the `3 × 3` matrix of its conjugates in
these slots. It is Hermitian and multiplicative under the entrywise (Hadamard) product, so the symbol
of `x⁻¹` is the entrywise inverse of the symbol of `x`. For a matrix `S`, the Schur multiplier
`X ↦ S ⊙ X` is completely positive exactly when `S` is positive semidefinite (Paulsen 2002,
Thm 3.7; proved in the library as `ReversibleUnits.isCPSchur_iff_posSemidef`).

## The compared statements (namespace `DegreeNine`)

| # | name | statement |
|---|------|-----------|
| 1 | `hadamardInv_posSemidef_iff` | supporting lemma: a PSD matrix with no zero entry has PSD entrywise inverse iff it is `w w*` (any size) |
| 2 | `cp_both_iff_rankOne` | supporting lemma: for any matrix with no zero entry (PSD not assumed), both Schur multipliers are completely positive iff it is `w w*` |
| 3 | `compositum_setting` | `L ⊔ M = K`, linearly disjoint, `K` has 3 real and 3 complex places |
| 4 | `slot_assignment_exists_unique` | the slot assignment exists, is a Hermitian bijection `Fin 3 × Fin 3 ≃ (K →+* ℂ)`, and is unique |
| 5 | `rankOne_iff_relNorm_eq_ratCast` | for `x ≠ 0`: symbol rank one iff `N_{K/L}(x) = N_{K/M}(x)` is one positive rational |
| 6 | `unit_rankOne_iff` | for a unit `u`: symbol rank one iff `N_{K/L}(u) = N_{K/M}(u) = 1` |
| 7 | `relNormKernel_torsionFree_rank_two` | these units are torsion-free and their logarithms span a lattice of rank 2 |
| 8 | `reversible_iff` | for a unit `u`: both Schur multipliers (of `u` and of `u⁻¹`) completely positive iff `u ∈ H` |
| 9 | `exists_reversible` | a unit of infinite order all of whose powers run both ways |
| 10 | `quartic_reversible_iff` | degree four, two real places and one complex: both ways iff positive at the real places and `‖σ(u)‖ = 1` |

Statements 4–6, 8 and 9 hold for every labelling and every non-real `μ₁`. Every compared theorem
depends on `propext`, `Classical.choice` and `Quot.sound` only.

## The proof in five lines

Let `r_k = (λ_k, μ_r)` and `c_k = (λ_k, μ₁)`. For `u` with both relative norms 1:
- `N_{K/L}(u) = 1` read at `λ_k` gives `u(r_k)|u(c_k)|² = 1`;
- `N_{K/M}(u) = 1` read at `μ_r` and at `μ₁` gives `u(r₀)u(r₁)u(r₂) = 1` and `u(c₀)u(c₁)u(c₂) = 1`.

Together these say the symbol is `w w*`, with `w₀ = √u(r₀)`, `w₁ = conj u(c₂)/w₀` and
`w₂ = conj u(c₀)·w₀/u(c₂)`. Conversely, if the symbol is `w w*` then
`N_{K/ℚ}(u) = (u(r₀)u(r₁)u(r₂))³ = ±1`, which forces the three equations back. The rank is 2 because
the logarithms of `H` lie in a plane (`ℓ(c_k) = −ℓ(r_k)/2`, `Σℓ(r_k) = 0`) and the pair of norm maps
`U_K → U_L × U_M` has image of rank `2 + 1`.

## Relation to the literature

In degree four the units that run both ways are `1` and the Salem units (statement 10). Statements
5–9 settle the degree-nine case for every such compositum, and determine the group exactly. No prior
statement of this was found in about twenty recorded searches; the nearest results, Dubickas 2014
(units whose complex conjugates have equal modulus) and Kerada 1995 (generalized Salem numbers, with
conjugates on the unit circle), concern different conjugate patterns.

## What is not claimed

- No concrete field is treated, and the satisfiability of the hypotheses is not kernel-checked: any
  totally real cubic `L` with `M = ℚ(∛2)` gives such a `K` (computed, not in the package).
- The converse is open: is every field of signature `(3, 3)` with a nontrivial rank-one unit such a
  compositum?
- Shapes `n ≥ 4` (degree `n²`, signature `(n, n(n−1)/2)`) are open.
- Statement 1 (any size) is not claimed as new; Reams 1999 (identified by title, not read) and
  Lim 2020 are adjacent.
- Statement 10's ingredients are classical; the form in which a unit's conjugate lies on the unit
  circle is the Salem case (Ghate–Hironaka 2001; Smyth 2015).
- The registered entry PALOMAR-2026-10-21-000012 supplies the compositum place bookkeeping
  (`restrictPair`, `embeddingsEquiv`, `places_compositum`), ported and cited, not re-proved.

## Application (cited, not a claim of the entry)

Read a unit as a step acting by multiplication on a Hermitian register of its places, and require
an admissible step to be completely positive. Then statement 10 says that in the degree-four shape a
step `u ≠ 1` can run both ways only through a conjugate on the unit circle. In a field such as
`ℚ(Q)`, `Q⁴ = Q + 1`, the only such elements are `±1` (not proved in this entry; it follows from
statement 17 of the registered entry PALOMAR-2026-10-21-000012, since `ℚ(Q) ⊆ ℚ(ρ, Q)`). So there
every totally positive unit `u ≠ 1` runs exactly one way (statement 10 with the library's
`unit_one_direction_xor`). Statements 6–9 say that in the degree-nine shape a rank-two group of units
runs both ways. The steps are completely positive, not trace-non-increasing. The cubic field `ℚ(ρ)`,
`ρ³ = ρ + 1`, can serve as the factor `M`.

## Building

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The
build record, axiom audit and statement-identity checks are in `BUILD.txt`.

## Files

- `Challenge.lean`: the ten statements, Mathlib-only, as `sorry` placeholders, with the four
  definitions the entry adds.
- `Solution.lean`: the same statements proved, by transfer from the library.
- `ReversibleUnits/HadamardInverse.lean`: statements 1–2, and the Schur-multiplier block (Paulsen's
  criterion).
- `ReversibleUnits/Compositum.lean`: statements 3–7; the place bookkeeping is ported from
  PALOMAR-2026-10-21-000012.
- `ReversibleUnits/Reversible.lean`: statements 8–9.
- `ReversibleUnits/NTwo.lean`: statement 10.
- `ReversibleUnits.lean`: the library root.
- `DefinitionAudit.lean`: kernel checks of the facts the definitions rely on.
- `comparator.json`, `formalization.yaml`, `BUILD.txt`: the comparator configuration, the registry
  metadata, and the build record.

License: MIT. Author: Stephanie Alexander.
