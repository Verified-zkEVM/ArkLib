/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.Matrix.Basic
import ArkLib.Data.Probability.Instances

/-!
## Main Results

- Lemma 4.1 [BCGM25] : Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `A` a matrix
with a left  pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `A`
is an MCA generator with the same error `ε_mca` as `G`.
- Corollary 4.2 [BCGM25] : Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `κ` a
subset of `ℓ`. Then the projected generator over `κ` is an MCA generator with the same error as `G`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

namespace LinearTransformations

open NNReal ENNReal unitInterval LinearCode CoreDefinitions Matrix
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type} [Fintype S]

/-- Let `G : S → 𝔽^ℓ` be a generator and let `A` be an `ℓ × ℓ'` matrix. Then `G' : S → 𝔽^ℓ'` is a
generator defined by `x ↦ G(x) · A`.
This is the generator `G'` inside Lemma 4.1 [BCGM25]. -/
def generatorByRightMul (G : Generator S ℓ F) (A : Matrix ℓ ℓ' F) : Generator S ℓ' F :=
    fun x ↦ Matrix.vecMul (G x) A

/-- Let `G : S → 𝔽^ℓ` be a generator and `κ` a subset of `ℓ`. Define a new generator
`G' : S → 𝔽^κ`, which we call a projected generator, by restricting the output of `G` to the indices
given by `κ`.
This is the generator `G'` inside Corollary 4.2 [BCGM25] -/
def projectedGenerator (G : Generator S ℓ F) (κ : Set ℓ) : Generator S κ F :=
    fun x ↦ Set.restrict κ (G x)

/-- Let `U : ℓ' → (ι → F)` be a family of `ℓ'` codewords over `𝔽^ι`. Obtain a family of `ℓ`
codewords by acting on `U` by left multiplication with an `ℓ × ℓ'` matrix `A`. -/
def matrixMulCodewords (A : Matrix ℓ ℓ' F) (U : ℓ' → (ι → F)) : ℓ → (ι → F) :=
  fun i k => ∑ j : ℓ', A i j * U j k

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `A` a matrix
with a left  pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `A`
is an MCA generator with the same error `ε_mca` as `G`.
Lemma 4.1 [BCGM25]. -/
lemma pseudoinverseGen [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → I)
  (LC : LinearCode ι F) (hGMCA : IsMCAGenerator G ε_mca LC)
  (A : Matrix ℓ ℓ' F) (hA : HasLeftPseudoInverse A) :
    IsMCAGenerator (generatorByRightMul G A) ε_mca LC := by
  intro U γ
  have isMCA_generatorByRightMul_of_isMCA (x : S) :
IsMCA (generatorByRightMul G A) LC x U γ → IsMCA G LC x (matrixMulCodewords A U) γ := by
    obtain ⟨B, hB⟩ := hA
    rintro ⟨T, hT_card, hT_proj, j, hj⟩
    refine ⟨T, hT_card, ?_, ?_⟩
    · convert hT_proj using 1
      ext i
      simp only [generatorByRightMul, Matrix.vecMul_vecMul]
      congr! 2
    · contrapose! hj
      convert LinearCode.projectedCode_linearCombination LC T (fun i => matrixMulCodewords A U i)
        (fun i => B j i) (fun i => hj i) using 1
      ext k
      simp [matrixMulCodewords, ← Matrix.mul_apply, ← Matrix.mul_assoc, hB]
  exact le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _ fun x h => isMCA_generatorByRightMul_of_isMCA x h)
    (hGMCA (matrixMulCodewords A U) γ)

open Classical in
/-- Extend a collection of words `U : κ → (ι → F)` to `ℓ → (ι → F)` by filling in the extra
positions with zeros. -/
noncomputable def zeroExtend (κ : Set ℓ) (U : κ → (ι → F)) : ℓ → (ι → F) :=
fun i => if h : i ∈ κ then U ⟨i, h⟩ else 0

/-- If the MCA condition `IsMCA` holds for a projected generator, then `IsMCA` holds for the
original generator `G` with the zero-extension defined above. -/
lemma isMCA_projectedGenerator_of_isMCA (LC : LinearCode ι F) [Nonempty S] (G : Generator S ℓ F)
    (κ : Set ℓ) [Fintype κ] (U : κ → (ι → F)) (γ : I) (x : S) :
    IsMCA (projectedGenerator G κ) LC x U γ → IsMCA G LC x (zeroExtend κ U) γ := by
  have vecMul_projectedGenerator :
    Matrix.vecMul (projectedGenerator G κ x) U = Matrix.vecMul (G x) (zeroExtend κ U) := by
    ext i
    simp only [Matrix.vecMul, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Set.toFinset κ))]
    · refine Finset.sum_bij (fun j _ => j) ?_ ?_ ?_ ?_ <;>
        simp [projectedGenerator, zeroExtend]
    · intro x _ hx; simp [zeroExtend]; aesop
  have zeroExtend_val (j : κ) : zeroExtend κ U j.val = U j := by
    simp [zeroExtend, j.property]
  rintro ⟨T, hT₁, hT₂, j, hT₃⟩
  exact ⟨T, hT₁,
    by convert hT₂ using 1; exact funext fun _ => by simp [vecMul_projectedGenerator],
    ⟨j, by rw [zeroExtend_val] ; assumption⟩⟩

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `κ` a
subset of `ℓ`. Then the projected generator over `κ` is an MCA generator with the same error as `G`.
Corollary 4.2 [BCGM25]. -/
lemma generatorSubset [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hGMCA : IsMCAGenerator G ε_mca LC) (κ : Set ℓ) [Fintype κ] :
  IsMCAGenerator (projectedGenerator G κ) ε_mca LC := by
  intro U γ
  exact le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _
          fun x h => isMCA_projectedGenerator_of_isMCA LC G κ U γ x h)
    (hGMCA (zeroExtend κ U) γ)

end LinearTransformations
