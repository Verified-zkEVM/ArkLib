/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.Matrix.Basic
import ArkLib.Data.Probability.Instances

/-!
## Main Results

- Lemma 4.1 [BCGM25] : Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `A` a matrix
with a left  pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `A`
is an MCA generator with the same error `ε_mca` as `G`.
- Corollary 4.2 [BCGM25] : Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca`, and `κ` a
subset of `ℓ`. Then the projected generator over `κ` is an MCA generator with the same error as `G`.
- `isMCAGenerator_reindex` : MCA is invariant under bijective relabellings of the seed space and
of the output coordinates of a generator.
- Lemma 4.4 [BCGM25] : the tensor product of two MCA generators is an MCA generator, with the
weaker error `ε_mca + |ℓ| • ε_mca'` (`tensor_of_MCA_is_MCA`, fully proved) and with the tight
error `ε_mca + ε_mca'` of the paper (`tensor_of_MCA_is_MCA_tight`, currently `sorry`ed pending a
generalisation of `IsMCAGenerator` to module alphabets).

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
with a left pseudoinverse. Then the generator `G'` obtained from `G` by right multiplication by `A`
is an MCA generator with the same error `ε_mca` as `G`.
Lemma 4.1 [BCGM25]. -/
lemma pseudoinverseGen [DecidableEq ℓ'] [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ)
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
      · rfl
      · ext k
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
lemma generatorSubset [Nonempty S] (G : Generator S ℓ F) (ε_mca : I → ℝ) (LC : LinearCode ι F)
(hGMCA : IsMCAGenerator G ε_mca LC) (κ : Set ℓ) [Fintype κ] :
  IsMCAGenerator (projectedGenerator G κ) ε_mca LC := by
  intro U γ
  exact le_trans (Pr_le_Pr_of_implies ($ᵖ S) _ _
          fun x h => isMCA_projectedGenerator_of_isMCA LC G κ U γ x h)
    (hGMCA (zeroExtend κ U) γ)

/-- Mutual correlated agreement is invariant under bijective relabellings of the seed space and of
the output coordinates of a generator. This lets us transport MCA statements along the canonical
equivalences (such as `Fin.consEquiv`) that arise when iterating tensor products of generators. -/
lemma isMCAGenerator_reindex {S' : Type} [Fintype S'] [Nonempty S'] [Nonempty S]
    (LC : LinearCode ι F) (G : Generator S ℓ F) (ε_mca : I → ℝ)
    (hGMCA : IsMCAGenerator G ε_mca LC) (eS : S' ≃ S) (eL : ℓ ≃ ℓ') :
    IsMCAGenerator (fun x' j' => G (eS x') (eL.symm j')) ε_mca LC := by
  classical
  intro U γ
  -- The reindexed combination is the original combination of the relabelled words `U ∘ eL`.
  have hvec : ∀ x' : S', Matrix.vecMul (fun j' => G (eS x') (eL.symm j')) U
      = Matrix.vecMul (G (eS x')) (fun j => U (eL j)) := by
    intro x'
    funext kk
    simp only [Matrix.vecMul, dotProduct]
    rw [← Equiv.sum_comp eL fun j' => G (eS x') (eL.symm j') * U j' kk]
    simp
  have hiff : ∀ x' : S',
      IsMCA (fun x' j' => G (eS x') (eL.symm j')) LC x' U γ
        ↔ IsMCA G LC (eS x') (fun j => U (eL j)) γ := by
    intro x'
    constructor
    · rintro ⟨T, hT, hmem, j', hj'⟩
      refine ⟨T, hT, ?_, eL.symm j', by simpa using hj'⟩
      rw [← hvec x']
      exact hmem
    · rintro ⟨T, hT, hmem, j, hj⟩
      refine ⟨T, hT, ?_, eL j, hj⟩
      rw [hvec x']
      exact hmem
  have hcard : (Finset.univ.filter fun x' : S' =>
        IsMCA G LC (eS x') (fun j => U (eL j)) γ).card
      = (Finset.univ.filter fun x : S => IsMCA G LC x (fun j => U (eL j)) γ).card :=
    Finset.card_equiv eS fun x' => by simp
  calc Pr_{let x' ←$ᵖ S'}[IsMCA (fun x' j' => G (eS x') (eL.symm j')) LC x' U γ]
      = Pr_{let x' ←$ᵖ S'}[IsMCA G LC (eS x') (fun j => U (eL j)) γ] := Pr_congr hiff
    _ = Pr_{let x ←$ᵖ S}[IsMCA G LC x (fun j => U (eL j)) γ] := by
        rw [prob_uniform_eq_ofReal, prob_uniform_eq_ofReal, hcard, Fintype.card_congr eS]
    _ ≤ ENNReal.ofReal (ε_mca γ) := hGMCA _ γ

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca` and `G' : S' → 𝔽^ℓ'` be an MCA
generator with error `ε_mca'`. Then the (explicit) tensor generator `G ⊗ G' : S × S' → 𝔽^(ℓ × ℓ')`
is an MCA generator.

This is Lemma 4.4 [BCGM25]. The paper obtains the tight error `ε_mca + ε_mca'` by applying the MCA
property of `G'` to the `ℓ`-fold interleaving of `LC` (an MCA statement over the larger alphabet
`𝔽^ℓ`). The ArkLib `IsMCAGenerator` predicate is currently fixed to the base alphabet `𝔽`, so here
we replace that interleaving step by a union bound over the `ℓ` rows, which yields the (weaker but
self-contained) error `ε_mca + (Fintype.card ℓ) • ε_mca'`. We assume the error functions are
nonnegative (as MCA errors always are); this is needed to combine the two `ENNReal.ofReal` bounds
additively. A tight version, matching the paper, is left for a future generalisation of
`IsMCAGenerator` to arbitrary module alphabets. -/
lemma tensor_of_MCA_is_MCA [Nonempty S] {S' : Type} [Fintype S'] [Nonempty S'] (LC : LinearCode ι F)
    (G : Generator S ℓ F) (ε_mca : I → ℝ) (hε_mca : ∀ γ, 0 ≤ ε_mca γ)
    (hGMCA : IsMCAGenerator G ε_mca LC)
    (G' : Generator S' ℓ' F) (ε_mca' : I → ℝ) (hε_mca' : ∀ γ, 0 ≤ ε_mca' γ)
    (hG'MCA : IsMCAGenerator G' ε_mca' LC) :
    IsMCAGenerator (TensorGenerator_Explicit G G')
      (ε_mca + (Fintype.card ℓ : ℝ) • ε_mca') LC := by
  intro U γ
  -- `W x' i` is the `G'`-combination of the `i`-th "row" `(U (i, ·))` of the word matrix.
  set W : S' → (ℓ → (ι → F)) := fun x' i => Matrix.vecMul (G' x') (fun j => U (i, j))
  -- Pointwise: an MCA violation of the tensor generator forces an MCA violation of `G` (on the
  -- `W`-rows) or of `G'` (on some individual row).
  have himp : ∀ p : S × S', IsMCA (TensorGenerator_Explicit G G') LC p U γ →
      IsMCA G LC p.1 (W p.2) γ ∨ ∃ i, IsMCA G' LC p.2 (fun j => U (i, j)) γ := by
    rintro ⟨x, x'⟩ ⟨T, hTcard, hTproj, ⟨i₀, j₀⟩, hij⟩
    rw [vecMul_tensorGenerator_explicit G G' U x x'] at hTproj
    by_cases hcase : ∃ i, projectedWord (W x' i) T ∉ projectedCode_submod LC T
    · exact Or.inl ⟨T, hTcard, hTproj, hcase⟩
    · simp only [not_exists, not_not] at hcase
      exact Or.inr ⟨i₀, T, hTcard, hcase i₀, j₀, hij⟩
  -- Rewrite the target error as the matching sum of `ENNReal.ofReal`s.
  have hEq : ENNReal.ofReal (ε_mca γ) + (Fintype.card ℓ : ℝ≥0∞) * ENNReal.ofReal (ε_mca' γ)
      = ENNReal.ofReal ((ε_mca + (Fintype.card ℓ : ℝ) • ε_mca') γ) := by
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_add (hε_mca γ) (mul_nonneg (by positivity) (hε_mca' γ)),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  -- `G`-term: reorder so `S'` is sampled first, then apply `hGMCA` for each `x'`.
  have hA : Pr_{ let p ←$ᵖ (S × S') }[ IsMCA G LC p.1 (W p.2) γ ]
      ≤ ENNReal.ofReal (ε_mca γ) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')]
    simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
    exact Pr_seq_le_of_forall_le ($ᵖ S) ($ᵖ S')
      (fun x x' => IsMCA G LC x (W x') γ) (fun x' => hGMCA (W x') γ)
  -- `G'`-term: the event is independent of `x ∈ S`; union bound over the `ℓ` rows.
  have hB : Pr_{ let p ←$ᵖ (S × S') }[ ∃ i, IsMCA G' LC p.2 (fun j => U (i, j)) γ ]
      ≤ (Fintype.card ℓ : ℝ≥0∞) * ENNReal.ofReal (ε_mca' γ) := by
    rw [prob_split_uniform_sampling_of_prod]
    refine Pr_seq_le_of_forall_le ($ᵖ S') ($ᵖ S)
      (fun x' _ => ∃ i, IsMCA G' LC x' (fun j => U (i, j)) γ) (fun _ => ?_)
    refine (Pr_exists_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun i _ => hG'MCA (fun j => U (i, j)) γ).trans ?_
    simp [Finset.card_univ, nsmul_eq_mul]
  -- Combine: the tensor MCA event implies one of the two, then union + additivity.
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ (S × S')) _ _ himp) ?_
  refine le_trans (Pr_or_le ($ᵖ (S × S')) _ _) ?_
  rw [← hEq]
  exact add_le_add hA hB

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca` and `G' : S' → 𝔽^ℓ'` be an MCA
generator with error `ε_mca'`. Then the (explicit) tensor generator `G ⊗ G' : S × S' → 𝔽^(ℓ × ℓ')`
is an MCA generator with error `ε_mca + ε_mca'`.

This is Lemma 4.4 [BCGM25] with the tight error bound. The paper's proof bounds the second term of
its case split (Equation 5 in [BCGM25]) by applying the MCA property of `G'` to the `ℓ`-fold
interleaving of `LC`, an MCA statement over the module alphabet `𝔽^ℓ`. The current
`IsMCAGenerator` is fixed to the base alphabet `𝔽`, so this step cannot yet be expressed and the
lemma is `sorry`ed, pending the planned generalisation of `IsMCAGenerator` to module alphabets.
See `tensor_of_MCA_is_MCA` above for a fully proved version with the weaker error
`ε_mca + |ℓ| • ε_mca'`. -/
lemma tensor_of_MCA_is_MCA_tight [Nonempty S] {S' : Type} [Fintype S'] [Nonempty S']
    (LC : LinearCode ι F)
    (G : Generator S ℓ F) (ε_mca : I → ℝ) (hGMCA : IsMCAGenerator G ε_mca LC)
    (G' : Generator S' ℓ' F) (ε_mca' : I → ℝ) (hG'MCA : IsMCAGenerator G' ε_mca' LC) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + ε_mca') LC := by
  sorry

noncomputable def ε_MCA_MDS [DecidableEq F] [Nonempty ι] (LC : LinearCode ι F) (ℓ s : ℕ) (η : ℝ) :
    I → ℝ :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (LC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_ℓ : ℝ := 1 - (ρ_C + η) ^ (1 / ℓ : ℝ)
  fun γ =>
      if γ < (δ_C / (ℓ + 1) : ℝ) then
      letI m' : ℝ := max (n * γ) 1
      m' * ((ℓ - 1) / s : ℝ)
    else
      if γ ≤ 1 - (ρ_C + η) ^ (1 / (ℓ + 1) : ℝ) then
          (n * γ_ℓ / η) * ((ℓ - 1) / s) +
          max (2 * (ℓ - 1) / (η * ((ρ_C + η) ^ (1 / (ℓ + 1) : ℝ) - (ρ_C + η) ^ (1 / ℓ : ℝ)) * s))
              (ℓ * (ℓ + 1) / (η * s) : ℝ)
      else
      1

/-- Theorem 6.1 (MCA for MDS generators) [BCGM25].

The paper requires that `C_G` has dimension `ℓ` (i.e. the generator has full column rank), which
is the hypothesis `hdim` below; it is what makes the matrix `Mat(G(x₁), …, G(x_ℓ))` invertible in
the counting arguments (Lemmas 5.2 and 6.2, via Lemma 3.6). It is stated as a separate hypothesis
here because `IsMDSGenerator` only asserts that `C_G` meets the Singleton bound, which does not by
itself force the dimension to be `ℓ`. If it later turns out to be derivable from the other
hypotheses, `hdim` can be removed. -/
theorem MDS_is_MCA {S : Type} [Nonempty S] [Fintype S] [DecidableEq F] [Nonempty ι]
  (G : Generator S ℓ F)
  (hG : IsMDSGenerator G)
  (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
  (η : ℝ) (hη : 0 < η ∧ η < 1) (hℓ : 2 ≤ Fintype.card ℓ)
  (LC : LinearCode ι F) :
  IsMCAGenerator G (ε_MCA_MDS LC (Fintype.card ℓ) (Fintype.card S) η) LC := by sorry

end LinearTransformations
