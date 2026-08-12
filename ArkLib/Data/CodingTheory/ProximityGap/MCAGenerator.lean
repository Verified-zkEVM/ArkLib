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
open Probability

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type} [Fintype S]

/-- Let `G : S → 𝔽^ℓ` be a generator and let `M` be an `ℓ × ℓ'` matrix. Then `G' : S → 𝔽^ℓ'` is a
generator defined by `x ↦ G(x) · M`.
This is the generator `G'` inside Lemma 4.1 [BCGM25]. -/
def generatorByRightMul (G : Generator S ℓ F) (M : Matrix ℓ ℓ' F) : Generator S ℓ' F :=
    fun x ↦ Matrix.vecMul (G x) M

/-- Let `G : S → 𝔽^ℓ` be a generator and `κ` a subset of `ℓ`. Define a new generator
`G' : S → 𝔽^κ`, which we call a projected generator, by restricting the output of `G` to the indices
given by `κ`.
This is the generator `G'` inside Corollary 4.2 [BCGM25] -/
def projectedGenerator (G : Generator S ℓ F) (κ : Set ℓ) : Generator S κ F :=
    fun x ↦ Set.restrict κ (G x)

/-- Let `U : ℓ' → (ι → A)` be a family of `ℓ'` words over `A^ι`. Obtain a family of `ℓ`
words by acting on `U` by left multiplication with an `ℓ × ℓ'` matrix `M` over `F`. -/
def matrixMulCodewords (M : Matrix ℓ ℓ' F) (U : ℓ' → (ι → A)) : ℓ → (ι → A) :=
  fun i k => ∑ j : ℓ', M i j • U j k

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `M` a matrix
with a left pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `M`
is an MCA generator with the same error `ε_mca` as `G`.
Lemma 4.1 [BCGM25]. -/
lemma pseudoinverseGen [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
  (MC : ModuleCode ι F A) (hGMCA : IsMCAGenerator G ε_mca MC)
  (M : Matrix ℓ ℓ' F) (hM : HasLeftPseudoInverse M) :
    IsMCAGenerator (generatorByRightMul G M) ε_mca MC := by
  intro U γ
  have isMCA_generatorByRightMul_of_isMCA (x : S) :
IsMCA (generatorByRightMul G M) MC x U γ → IsMCA G MC x (matrixMulCodewords M U) γ := by
    obtain ⟨B, hB⟩ := hM
    rintro ⟨T, hT_card, hT_proj, j, hj⟩
    refine ⟨T, hT_card, ?_, ?_⟩
    · convert hT_proj using 1
      ext i
      simp only [generatorByRightMul, matrixMulCodewords, Matrix.vecMul,
        dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · contrapose! hj
      simp only [LinearCode.mem_projectedCodeSubmod_iff] at hj ⊢
      convert LinearCode.projectedCode_linearCombination MC T (fun i => matrixMulCodewords M U i)
        (fun i => B j i) (fun i => hj i) using 1
      ext k
      simp only [projectedWord, Set.restrict_apply, matrixMulCodewords, Finset.smul_sum,
        smul_smul]
      rw [Finset.sum_comm]
      simp [← Finset.sum_smul, ← Matrix.mul_apply, hB, Matrix.one_apply]
  exact le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _ fun x h => isMCA_generatorByRightMul_of_isMCA x h)
    (hGMCA (matrixMulCodewords M U) γ)

open Classical in
/-- Extend a collection of words `U : κ → (ι → A)` to `ℓ → (ι → A)` by filling in the extra
positions with zeros. -/
noncomputable def zeroExtend (κ : Set ℓ) (U : κ → (ι → A)) : ℓ → (ι → A) :=
fun i => if h : i ∈ κ then U ⟨i, h⟩ else 0

/-- If the MCA condition `IsMCA` holds for a projected generator, then `IsMCA` holds for the
original generator `G` with the zero-extension defined above. -/
lemma isMCA_projectedGenerator_of_isMCA (MC : ModuleCode ι F A) [Nonempty S] (G : Generator S ℓ F)
    (κ : Set ℓ) [Fintype κ] (U : κ → (ι → A)) (γ : I) (x : S) :
    IsMCA (projectedGenerator G κ) MC x U γ → IsMCA G MC x (zeroExtend κ U) γ := by
  have smulSum_projectedGenerator (i : ι) :
    ∑ j, projectedGenerator G κ x j • U j i = ∑ j, G x j • zeroExtend κ U j i := by
    rw [← Finset.sum_subset (Finset.subset_univ (Set.toFinset κ))]
    · refine Finset.sum_bij (fun j _ => j) ?_ ?_ ?_ ?_ <;>
        simp [projectedGenerator, zeroExtend]
    · intro x _ hx; simp [zeroExtend]; aesop
  have zeroExtend_val (j : κ) : zeroExtend κ U j.val = U j := by
    simp [zeroExtend, j.property]
  rintro ⟨T, hT₁, hT₂, j, hT₃⟩
  exact ⟨T, hT₁,
    by convert hT₂ using 1; exact funext fun i => (smulSum_projectedGenerator i.val).symm,
    ⟨j, by rw [zeroExtend_val] ; assumption⟩⟩

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `κ` a
subset of `ℓ`. Then the projected generator over `κ` is an MCA generator with the same error as `G`.
Corollary 4.2 [BCGM25]. -/
lemma generatorSubset [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
  (MC : ModuleCode ι F A)
  (hGMCA : IsMCAGenerator G ε_mca MC) (κ : Set ℓ) [Fintype κ] :
  IsMCAGenerator (projectedGenerator G κ) ε_mca MC := by
  intro U γ
  exact le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _
          fun x h => isMCA_projectedGenerator_of_isMCA MC G κ U γ x h)
    (hGMCA (zeroExtend κ U) γ)

end LinearTransformations
