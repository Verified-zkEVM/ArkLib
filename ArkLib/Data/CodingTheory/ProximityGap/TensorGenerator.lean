/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.Probability.Instances

/-!
## Main Results

- Lemma 4.4 [BCGM25] (tight form): if `G` has MCA with error `ε_mca` for `MC` and `G'` has MCA
with error `ε'_mca` for the `ℓ`-fold interleaving `MC^⋈ℓ`, then the tensor generator `G ⊗ G'`
has MCA with error `ε_mca + ε'_mca` for `MC`.

### On the interleaved hypothesis

[BCGM25]'s printed Lemma 4.4 assumes `G` and `G'` have mutual correlated agreement for `C`, but
its proof bounds the second case (Equation (5)) by applying `G'`'s MCA to the `ℓ`-fold
interleaving `C^ℓ ⊆ (Σ^ℓ)^n`: the family fed to `G'` is the stack `w_j := (u_{(1,j)}, …,
u_{(ℓ,j)})`, whose entries are interleaved symbols. We therefore hypothesise `G'`'s MCA **at the
interleaving**, which is what the proof actually uses. The strengthening is invisible in the
paper's applications: for the MDS generators of Theorem 6.1 [BCGM25] the MCA error depends only
on the relative distance, and `δ(C^ℓ) = δ(C)`, so the interleaved hypothesis is discharged by
the same theorem.

Without the interleaved hypothesis one must pick, per outer seed `x'`, a row witnessing
non-membership; that row depends on `x'`, so the family fed to `G'`'s MCA is not fixed and a
union bound over the `ℓ` rows is forced — yielding the weak error `ε_mca + ℓ • ε'_mca` instead.
With the interleaving the family `w` depends only on `U`, and the `ℓ` factor disappears.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051
-/

namespace TensorMCA

open NNReal ENNReal unitInterval LinearCode CoreDefinitions Code
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S S' : Type} [Fintype S] [Fintype S'] [Nonempty S] [Nonempty S']

/-- **Lemma 4.4 [BCGM25], tight form.** If `G : S → F^ℓ` has mutual correlated agreement with
error `ε_mca` for `MC`, and `G' : S' → F^ℓ'` has mutual correlated agreement with error `ε'_mca`
for the `ℓ`-fold interleaving `MC^⋈ℓ`, then the tensor generator `G ⊗ G' : S × S' → F^(ℓ × ℓ')`
has mutual correlated agreement with error `ε_mca + ε'_mca` for `MC`.

The proof follows the paper: writing `W x' i := ∑ j, G' x' j • U (i, j)` for the `G'`-combined
rows, the tensor combination is the `G`-combination of `W x'`. Case-split on whether some
`W x' i` fails to project into the code on the witness set `T`:
* if so, the tensor event implies the MCA event of `G` at the family `W x'` (seed `x`);
* if not, it implies the MCA event of `G'` at the interleaved family `w j := (k, i) ↦ U (i, j) k`
  — crucially **independent of `x'`** — for the interleaving `MC^⋈ℓ` (seed `x'`).
A union bound then gives `ε_mca + ε'_mca`. -/
theorem tensor_isMCAGenerator (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
    (ε_mca ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG : IsMCAGenerator G ε_mca MC)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + ε'_mca) MC := by
  intro U δ
  classical
  -- the `G'`-combined rows, per outer seed `x'`
  set W : S' → ℓ → (ι → A) := fun x' i k => ∑ j, G' x' j • U (i, j) k with hW
  -- the `x'`-independent interleaved family
  set w : ℓ' → (ι → InterleavedSymbol A ℓ) := fun j k i => U (i, j) k with hw
  -- the tensor combination is the `G`-combination of the `W`-rows
  have hv : ∀ (x : S) (x' : S'),
      (fun k => ∑ p : ℓ × ℓ', TensorGenerator_Explicit G G' (x, x') p • U p k)
        = fun k => ∑ i, G x i • W x' i k := by
    intro x x'
    funext k
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [TensorGenerator_Explicit, mul_smul]
  -- rows of the `G'`-combination of `w` are the `W`-rows
  have hrow : ∀ (x' : S') (i : ℓ),
      InterleavedWord.getRowWord (fun k => ∑ j, G' x' j • w j k) i = W x' i := by
    intro x' i
    funext k
    simp [hw, hW, InterleavedWord.getRowWord, Finset.sum_apply]
  -- the case split: the tensor event implies one of the two MCA events
  have himp : ∀ p : S × S', IsMCA (TensorGenerator_Explicit G G') MC p U δ →
      IsMCA G MC p.1 (W p.2) δ ∨
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ := by
    rintro ⟨x, x'⟩ ⟨T, hT, hcomb, ⟨i₀, j₀⟩, hbad⟩
    rw [hv x x'] at hcomb
    by_cases hcase : ∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T
    · exact Or.inl ⟨T, hT, hcomb, hcase⟩
    · push Not at hcase
      refine Or.inr ⟨T, hT, ?_, j₀, fun hmem => hbad ?_⟩
      · rw [projectedCodeSubmod_moduleInterleavedCode_iff]
        intro i
        rw [hrow x' i]
        exact hcase i
      · have h := (projectedCodeSubmod_moduleInterleavedCode_iff
          F A ℓ ι MC (w j₀) T).mp hmem i₀
        have hwrow : InterleavedWord.getRowWord (w j₀) i₀ = U (i₀, j₀) := by
          funext k; simp [hw, InterleavedWord.getRowWord]
        rwa [hwrow] at h
  -- assemble: implication, union bound, and the two marginal bounds
  have hA : Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
      ≤ ENNReal.ofReal (ε_mca δ) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')
      (fun p => IsMCA G MC p.1 (W p.2) δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun x' => hG (W x') δ
  have hB : Pr_{let p ← $ᵖ (S × S')}[
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ]
      ≤ ENNReal.ofReal (ε'_mca δ) := by
    rw [prob_split_uniform_sampling_of_prod
      (fun p => IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun _ => hG' w δ
  calc Pr_{let p ← $ᵖ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ ∨
          IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
        + Pr_{let p ← $ᵖ (S × S')}[
            IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        Pr_or_le _ _ _
    _ ≤ ENNReal.ofReal (ε_mca δ) + ENNReal.ofReal (ε'_mca δ) := add_le_add hA hB
    _ = ENNReal.ofReal ((ε_mca + ε'_mca) δ) := by
        rw [← ENNReal.ofReal_add (ε_mca δ).coe_nonneg (ε'_mca δ).coe_nonneg]
        norm_num

end TensorMCA
