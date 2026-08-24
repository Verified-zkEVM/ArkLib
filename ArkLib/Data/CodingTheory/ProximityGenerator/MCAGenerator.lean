/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.Matrix.Basic
import ArkLib.Data.Probability.Instances

/-!
# Preserving mutual correlated agreement under linear maps on the output

Two ways of building a new generator from an old one leave the mutual correlated agreement error
no larger: post-composing the output with a matrix that has a left pseudoinverse, and restricting
the output to a subset of its coordinates.

Both are proved first at the error *value*, where no error function appears in the statement, and
then in `IsMCAGenerator` form. Both value forms are one application of the shared transport
skeleton `mcaError_le_of_forall_isMCA_imp`, whose hypothesis is an implication between bad events;
so the only mathematical content in this file is the two event implications
`isMCA_generatorByRightMul_of_isMCA` and `isMCA_projectedGenerator_of_isMCA`.

## Main statements

* `mcaError_le_of_forall_isMCA_imp` — the transport skeleton: an implication between bad events,
  at the same radius and over the same seed space, bounds one error by the other.
* `mcaError_generatorByRightMul_le`, `pseudoinverseGen` — right multiplication by a matrix with a
  left pseudoinverse.
* `mcaError_projectedGenerator_le`, `generatorSubset` — projection onto a subset of the output
  coordinates.

The correspondence to [BCGM25]'s numbered statements is in `docs/kb/audits/bcgm25-mca-generators.md`

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

namespace LinearTransformations

open NNReal unitInterval LinearCode CoreDefinitions Matrix
open scoped ProbabilityTheory
open Probability

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type} [Fintype S]

/-- **Value-level MCA transport.** If the MCA bad event for `G'` on a word family `U` implies the
bad event for `G` on some reindexed family `Φ U`, at the same radius and over the same seed space,
then `G'`'s MCA error value is bounded by `G`'s.

This is the transport skeleton behind every [BCGM25] generator-preservation lemma (4.1, 4.2, and
the tensor and reindexing arguments to come): the mathematical content of each is exactly the
event implication, and everything else is this lemma. Stating it once at the *value* keeps `ε_mca`
out of the statement of each transport lemma; the `IsMCAGenerator` forms follow by
`isMCAGenerator_iff_mcaError_le` and transitivity. -/
lemma mcaError_le_of_forall_isMCA_imp [Nonempty S] (G : Generator S ℓ F) (G' : Generator S ℓ' F)
    (MC : ModuleCode ι F A) (δ : ℝ) (Φ : (ℓ' → (ι → A)) → (ℓ → (ι → A)))
    (h : ∀ (U : ℓ' → (ι → A)) (x : S), IsMCA G' MC x U δ → IsMCA G MC x (Φ U) δ) :
    mcaError G' MC δ ≤ mcaError G MC δ := by
  unfold mcaError
  refine iSup_le fun U => le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _ (fun x hx => h U x hx)) ?_
  exact le_iSup (fun V => Pr_{let x ←$ᵖ S}[IsMCA G MC x V δ]) (Φ U)

/-- Let `G : S → 𝔽^ℓ` be a generator and let `M` be an `ℓ × ℓ'` matrix. Then `G' : S → 𝔽^ℓ'` is a
generator defined by `x ↦ G(x) · M`. This is the generator whose error is bounded by
`mcaError_generatorByRightMul_le`. -/
def generatorByRightMul (G : Generator S ℓ F) (M : Matrix ℓ ℓ' F) : Generator S ℓ' F :=
    fun x ↦ Matrix.vecMul (G x) M

/-- Let `G : S → 𝔽^ℓ` be a generator and `κ` a subset of `ℓ`. Define a new generator
`G' : S → 𝔽^κ`, which we call a projected generator, by restricting the output of `G` to the indices
given by `κ`.
This is the generator whose error is bounded by `mcaError_projectedGenerator_le`. -/
def projectedGenerator (G : Generator S ℓ F) (κ : Set ℓ) : Generator S κ F :=
    fun x ↦ Set.restrict κ (G x)

/-- Let `U : ℓ' → (ι → A)` be a family of `ℓ'` words over `A^ι`. Obtain a family of `ℓ`
words by acting on `U` by left multiplication with an `ℓ × ℓ'` matrix `M` over `F`. -/
def matrixMulCodewords (M : Matrix ℓ ℓ' F) (U : ℓ' → (ι → A)) : ℓ → (ι → A) :=
  fun i k => ∑ j : ℓ', M i j • U j k

/-- If the MCA condition `IsMCA` holds for `generatorByRightMul G M`, then it holds for the
original generator `G` with the word family transported by `M`.

This event implication is the whole mathematical content of the bound; the error statements below
follow from it by `mcaError_le_of_forall_isMCA_imp`. -/
lemma isMCA_generatorByRightMul_of_isMCA [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F)
    (MC : ModuleCode ι F A) (M : Matrix ℓ ℓ' F) (hM : HasLeftPseudoInverse M)
    (U : ℓ' → (ι → A)) (γ : ℝ) (x : S) :
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

/-- Right multiplication by a matrix with a left pseudoinverse does not increase the MCA error.
Stated at the error *value*, so no error function appears. -/
lemma mcaError_generatorByRightMul_le [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F)
    (MC : ModuleCode ι F A) (M : Matrix ℓ ℓ' F) (hM : HasLeftPseudoInverse M) (γ : ℝ) :
    mcaError (generatorByRightMul G M) MC γ ≤ mcaError G MC γ :=
  mcaError_le_of_forall_isMCA_imp G (generatorByRightMul G M) MC γ (matrixMulCodewords M)
    (fun U x h => isMCA_generatorByRightMul_of_isMCA G MC M hM U γ x h)

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `M` a matrix
with a left pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `M`
is an MCA generator with the same error `ε_mca` as `G`.
The `IsMCAGenerator` form of `mcaError_generatorByRightMul_le`. -/
lemma pseudoinverseGen [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
    (MC : ModuleCode ι F A) (hGMCA : IsMCAGenerator G ε_mca MC)
    (M : Matrix ℓ ℓ' F) (hM : HasLeftPseudoInverse M) :
    IsMCAGenerator (generatorByRightMul G M) ε_mca MC :=
  fun γ => le_trans (mcaError_generatorByRightMul_le G MC M hM γ) (hGMCA γ)

open Classical in
/-- Extend a collection of words `U : κ → (ι → A)` to `ℓ → (ι → A)` by filling in the extra
positions with zeros. -/
noncomputable def zeroExtend (κ : Set ℓ) (U : κ → (ι → A)) : ℓ → (ι → A) :=
fun i => if h : i ∈ κ then U ⟨i, h⟩ else 0

/-- If the MCA condition `IsMCA` holds for a projected generator, then `IsMCA` holds for the
original generator `G` with the zero-extension defined above. -/
lemma isMCA_projectedGenerator_of_isMCA (MC : ModuleCode ι F A) [Nonempty S] (G : Generator S ℓ F)
    (κ : Set ℓ) [Fintype κ] (U : κ → (ι → A)) (γ : ℝ) (x : S) :
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
    ⟨j, by
      rw [zeroExtend_val]
      assumption⟩⟩

/-- Projecting a generator onto a subset of its output coordinates does not increase the MCA
error. Stated at the error *value*, so no error function appears. -/
lemma mcaError_projectedGenerator_le [Nonempty S] (G : Generator S ℓ F) (MC : ModuleCode ι F A)
    (κ : Set ℓ) [Fintype κ] (γ : ℝ) :
    mcaError (projectedGenerator G κ) MC γ ≤ mcaError G MC γ :=
  mcaError_le_of_forall_isMCA_imp G (projectedGenerator G κ) MC γ (zeroExtend κ)
    (fun U x h => isMCA_projectedGenerator_of_isMCA MC G κ U γ x h)

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `κ` a subset of `ℓ`.
Then the projected generator over `κ` is an MCA generator with the same error as `G`.
The `IsMCAGenerator` form of `mcaError_projectedGenerator_le`. -/
lemma generatorSubset [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
    (MC : ModuleCode ι F A)
    (hGMCA : IsMCAGenerator G ε_mca MC) (κ : Set ℓ) [Fintype κ] :
    IsMCAGenerator (projectedGenerator G κ) ε_mca MC :=
  fun γ => le_trans (mcaError_projectedGenerator_le G MC κ γ) (hGMCA γ)

/-- Mutual correlated agreement is invariant under bijective relabellings of the seed space and of
the output coordinates of a generator. This lets us transport MCA statements along the canonical
equivalences (such as `Fin.consEquiv`) that arise when iterating tensor products of generators.

Not an instance of `mcaError_le_of_forall_isMCA_imp`: that skeleton keeps the seed space fixed,
whereas here the seed space is relabelled along `eS`, so the probabilities are compared by
`Finset.card_equiv` rather than by monotonicity of `Pr`. -/
lemma isMCAGenerator_reindex {S' : Type} [Fintype S'] [Nonempty S'] [Nonempty S]
    (MC : ModuleCode ι F A) (G : Generator S ℓ F) (ε_mca : I → ℝ≥0)
    (hGMCA : IsMCAGenerator G ε_mca MC) (eS : S' ≃ S) (eL : ℓ ≃ ℓ') :
    IsMCAGenerator (fun x' j' => G (eS x') (eL.symm j')) ε_mca MC := by
  classical
  intro γ
  refine iSup_le fun U => ?_
  have hvec : ∀ x' : S', (fun k => ∑ j', G (eS x') (eL.symm j') • U j' k)
      = fun k => ∑ j, G (eS x') j • U (eL j) k := by
    intro x'
    funext kk
    rw [← Equiv.sum_comp eL fun j' => G (eS x') (eL.symm j') • U j' kk]
    simp
  have hiff : ∀ x' : S',
      IsMCA (fun x' j' => G (eS x') (eL.symm j')) MC x' U (γ : ℝ)
        ↔ IsMCA G MC (eS x') (fun j => U (eL j)) (γ : ℝ) := by
    intro x'
    constructor
    · rintro ⟨T, hT, hmem, j', hj'⟩
      exact ⟨T, hT, by rw [← hvec x']; exact hmem, eL.symm j', by simpa using hj'⟩
    · rintro ⟨T, hT, hmem, j, hj⟩
      exact ⟨T, hT, by rw [hvec x']; exact hmem, eL j, hj⟩
  have hcard : (Finset.univ.filter fun x' : S' =>
        IsMCA G MC (eS x') (fun j => U (eL j)) (γ : ℝ)).card
      = (Finset.univ.filter fun x : S => IsMCA G MC x (fun j => U (eL j)) (γ : ℝ)).card :=
    Finset.card_equiv eS fun x' => by simp
  calc Pr_{let x' ←$ᵖ S'}[IsMCA (fun x' j' => G (eS x') (eL.symm j')) MC x' U (γ : ℝ)]
      = Pr_{let x' ←$ᵖ S'}[IsMCA G MC (eS x') (fun j => U (eL j)) (γ : ℝ)] := Pr_congr hiff
    _ = Pr_{let x ←$ᵖ S}[IsMCA G MC x (fun j => U (eL j)) (γ : ℝ)] := by
        rw [prob_uniform_eq_ofReal, prob_uniform_eq_ofReal, hcard, Fintype.card_congr eS]
    _ ≤ (ε_mca γ : ENNReal) := hGMCA.prob_le _ γ

/-- The MCA error function for MDS codes, as defined in Theorem 6.1 [BCGM25].

Valued in `ℝ≥0` to match `IsMCAGenerator`; the paper's expression is a real, and is clamped at `0`
by `Real.toNNReal`. The clamp is not lossy for the intended parameter range — the expression is a
bound on a probability, and is nonnegative wherever [BCGM25]'s hypotheses `0 < η < 1` and
`2 ≤ ℓ` hold. -/
noncomputable def ε_MCA_MDS [DecidableEq F] [DecidableEq A] [Nonempty ι] (MC : ModuleCode ι F A)
  (ℓ s : ℕ) (η : ℝ) : I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (MC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_ℓ : ℝ := 1 - (ρ_C + η) ^ (1 / ℓ : ℝ)
  fun γ =>
    Real.toNNReal <|
      if γ < (δ_C / (ℓ + 1) : ℝ) then
        letI m' : ℝ := max (n * γ) 1
        m' * ((ℓ - 1) / s : ℝ)
      else
        if γ ≤ 1 - (ρ_C + η) ^ (1 / (ℓ + 1) : ℝ) then
            (n * γ_ℓ / η) * ((ℓ - 1) / s) +
            max (2 * (ℓ - 1) /
                  (η * ((ρ_C + η) ^ (1 / ((ℓ + 1) : ℝ)) - (ρ_C + η) ^ (1 / ℓ : ℝ)) * s))
                (ℓ * (ℓ + 1) / (η * s) : ℝ)
        else
        1

/-- Theorem 6.1 (MCA for MDS generators) [BCGM25]. -/
theorem isMCAGenerator_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [Nonempty ι]
    (G : Generator S ℓ F)
    (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (hℓ : 2 ≤ Fintype.card ℓ)
    (LC : LinearCode ι F) :
  IsMCAGenerator G (ε_MCA_MDS LC (Fintype.card ℓ) (Fintype.card S) η) LC := by sorry

end LinearTransformations
