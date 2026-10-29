/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving
public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.Data.Probability.Instances

/-!
# Mutual correlated agreement for tensor generators

The tensor generator `G ⊗ G'` combines a family indexed by `ℓ × ℓ'` by applying `G'` across each
row and then `G` across the results. Its mutual correlated agreement error is bounded here in
three forms.

Writing `W x' i := ∑ j, G' x' j • U (i, j)` for the `G'`-combined rows, the tensor combination is
the `G`-combination of `W x'`. The bad event splits on whether some row `W x' i` fails to project
into the code on the witness set `T`. If some row fails, the event implies `G`'s at the family
`W x'`. If none does, it implies `G'`'s — but at which family depends on the hypothesis available:

* given MCA for the `ℓ`-fold interleaving, the family is the stack
  `w j := (k, i) ↦ U (i, j) k`, which does not depend on the outer seed, and the errors add;
* given MCA for the base code only, the row witnessing failure depends on the outer seed; a
  union bound over the `ℓ` rows pays the inner error `ℓ` times.

[BCGM25]'s printed Lemma 4.4 assumes the base code and claims the added error.
`LinearTransformations.isMCAGenerator_tensorGenerator_tight` proves it by choosing the families
differently: the family for `G` depends on the inner seed `x'` only, and the family for `G'` on
the outer seed `x` only, so neither union bound over rows nor an interleaved hypothesis is needed.
The correspondence is recorded in `docs/kb/audits/bcgm25-mca-generators.md`.

Note that the error bound is typed `I → ℝ≥0` rather than `I → I`, so an added or scaled error is
vacuous once it reaches `1`.

## Main statements

* `TensorMCA.isMCAGenerator_tensorGenerator` — given MCA for the base code, errors add with the
  inner one scaled by `Fintype.card ℓ`.
* `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` — given MCA for the
  `ℓ`-fold interleaving instead, the errors add unscaled.
* `TensorMCA.isMCAGenerator_of_moduleInterleavedCode` — MCA for the interleaving implies MCA for
  the base code at the same error, so the interleaved hypothesis is the stronger of the two.
* `LinearTransformations.isMCAGenerator_tensorGenerator_tight` — [BCGM25] Lemma 4.4 as printed:
  given MCA for the base code, the errors add unscaled.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

@[expose] public section

namespace TensorMCA

open NNReal ENNReal unitInterval LinearCode CoreDefinitions Code
open scoped ProbabilityTheory
open Probability

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S S' : Type} [Fintype S] [Fintype S'] [SampleableType S] [SampleableType S']

/-- If `G` has mutual correlated agreement with error `ε_mca` for `MC`, and `G'` has it with error
`ε'_mca` for the `ℓ`-fold interleaving of `MC`, then the tensor generator has it for `MC` with the
errors added.

Stated for `TensorGenerator_Explicit`, the componentwise form, which is the one that is a
`Generator`; `TensorGenerator` lands in the tensor product and the two agree under
`tensorProductPiFunEquiv`.

Writing `W x' i := ∑ j, G' x' j • U (i, j)`, the tensor combination is the `G`-combination of
`W x'`. Case-split on whether some `W x' i` fails to project into the code on the witness set `T`:
if so, the tensor event implies `G`'s event at the family `W x'`; if not, it implies `G'`'s event
at the interleaved family `w j := (k, i) ↦ U (i, j) k`, which is independent of `x'`. A union
bound over the two cases gives the sum. -/
theorem isMCAGenerator_tensorGenerator_of_moduleInterleavedCode
    (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
    (ε_mca ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG : IsMCAGenerator G ε_mca MC)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + ε'_mca) MC := by
  intro δ
  refine iSup_le fun U => ?_
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
    set_option backward.isDefEq.respectTransparency false in
      intro x' i
      funext k
      rw [InterleavedWord.getRowWord_apply]
      simp [hw, hW]
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
      · set_option backward.isDefEq.respectTransparency false in
          rw [projectedCodeSubmod_moduleInterleavedCode_iff]
        intro i
        rw [hrow x' i]
        exact hcase i
      · have h := (projectedCodeSubmod_moduleInterleavedCode_iff
          F A ℓ ι MC (w j₀) T).mp hmem i₀
        have hwrow : InterleavedWord.getRowWord (w j₀) i₀ = U (i₀, j₀) := by
          funext k
          change U (i₀, j₀) k = U (i₀, j₀) k
          rfl
        rwa [hwrow] at h
  -- assemble: implication, union bound, and the two marginal bounds
  have hA : Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
      ≤ (ε_mca δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _
      (fun x' => hG.prob_le (W x') δ)
  have hB : Pr{let p ← $ᵗ (S × S')}[
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ]
      ≤ (ε'_mca δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _
      (fun _ => hG'.prob_le w δ)
  calc Pr{let p ← $ᵗ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ ∨
          IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        prEvent_mono _ _ _ himp
    _ ≤ Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
        + Pr{let p ← $ᵗ (S × S')}[
            IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        prEvent_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal) + (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, ENNReal.coe_add]

omit [Fintype ℓ] in
/-- Mutual correlated agreement for the `ℓ`-fold interleaving implies it for the base code, at the
same error: stack a base family as an interleaved family with constant rows.

So the hypothesis of `isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` is the stronger of
the two. -/
theorem isMCAGenerator_of_moduleInterleavedCode [Nonempty ℓ] (G' : Generator S' ℓ' F)
    (ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator G' ε'_mca MC := by
  intro δ
  exact (mcaError_le_mcaError_moduleInterleavedCode G' MC (δ : ℝ)).trans (hG' δ)

/-- If `G` and `G'` both have mutual correlated agreement for `MC` itself, the tensor generator has
it for `MC` with the inner error scaled by `Fintype.card ℓ`.

The factor is forced by this route: without the interleaved hypothesis of
`isMCAGenerator_tensorGenerator_of_moduleInterleavedCode`, the row witnessing non-membership
depends on the outer seed `x'`,
so the family fed to `G'` is not fixed and a union bound over the `ℓ` rows is required. -/
theorem isMCAGenerator_tensorGenerator (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
    (ε_mca ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG : IsMCAGenerator G ε_mca MC)
    (hG' : IsMCAGenerator G' ε'_mca MC) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + Fintype.card ℓ • ε'_mca) MC := by
  intro δ
  refine iSup_le fun U => ?_
  classical
  set W : S' → ℓ → (ι → A) := fun x' i k => ∑ j, G' x' j • U (i, j) k with hW
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
  -- case split: either `G`'s event at the combined rows, or `G'`'s event at SOME row —
  -- the row index depends on the seed pair, whence the union bound below
  have himp : ∀ p : S × S', IsMCA (TensorGenerator_Explicit G G') MC p U δ →
      IsMCA G MC p.1 (W p.2) δ ∨ ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ := by
    rintro ⟨x, x'⟩ ⟨T, hT, hcomb, ⟨i₀, j₀⟩, hbad⟩
    rw [hv x x'] at hcomb
    by_cases hcase : ∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T
    · exact Or.inl ⟨T, hT, hcomb, hcase⟩
    · push Not at hcase
      exact Or.inr ⟨i₀, T, hT, hcase i₀, j₀, hbad⟩
  have hA : Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
      ≤ (ε_mca δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _
      (fun x' => hG.prob_le (W x') δ)
  have hB : Pr{let p ← $ᵗ (S × S')}[∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ]
      ≤ (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _ fun _ =>
      prEvent_exists_le_card_mul ($ᵗ S')
        (fun i x' => IsMCA G' MC x' (fun j => U (i, j)) δ)
        (fun i => hG'.prob_le (fun j => U (i, j)) δ)
  calc Pr{let p ← $ᵗ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ ∨
          ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ] :=
        prEvent_mono _ _ _ himp
    _ ≤ Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
        + Pr{let p ← $ᵗ (S × S')}[∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ] :=
        prEvent_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal)
        + (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + Fintype.card ℓ • ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, ENNReal.coe_add, ENNReal.coe_mul,
          ENNReal.coe_natCast]

end TensorMCA

namespace LinearTransformations

open NNReal unitInterval CoreDefinitions LinearCode
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S S' : Type} [Fintype S] [Fintype S'] [SampleableType S] [SampleableType S']

/-- Let `G : S → 𝔽^ℓ` be an MCA generator with error `ε_mca` and `G' : S' → 𝔽^ℓ'` be an MCA
generator with error `ε_mca'`. Then the (explicit) tensor generator `G ⊗ G' : S × S' → 𝔽^(ℓ × ℓ')`
is an MCA generator with error `ε_mca + ε_mca'`.

This is [BCGM25] Lemma 4.4 as printed. Write `W x' i := ∑ j, G' x' j • U (i, j)` for the
`G'`-combined rows and `V x j := ∑ i, G x i • U (i, j)` for the `G`-combined columns, so the
tensor combination at `(x, x')` is both `∑ i, G x i • W x' i` and `∑ j, G' x' j • V x j`. For each
inner seed `x'`, pick a family `Z x'` for `G`:

* if some witness set `T` of the required size has every row `W x' i` in the code on `T` but some
  entry `U (i₀, j₀)` outside it, let `Z x'` be the column `i ↦ U (i, j₀)`. At a bad `(x, x')`,
  either `G'` is bad for `V x` at `x'`, or every `V x j` is in the code on `T`, so `G` is bad for
  `Z x'` at `x` on `T`;
* otherwise let `Z x' := W x'`. At a bad `(x, x')` some row `W x' i` is outside the code on the
  tensor witness set, so `G` is bad for `Z x'` at `x`.

The bad event is therefore contained in `{G bad for Z x' at x} ∪ {G' bad for V x at x'}`. The
first family depends only on `x'` and the second only on `x`, so each marginal bound holds for
every value of the other seed, and a union bound gives `ε_mca + ε_mca'`. -/
lemma isMCAGenerator_tensorGenerator_tight (MC : ModuleCode ι F A)
    (G : Generator S ℓ F) (ε_mca : I → ℝ≥0) (hGMCA : IsMCAGenerator G ε_mca MC)
    (G' : Generator S' ℓ' F) (ε_mca' : I → ℝ≥0) (hG'MCA : IsMCAGenerator G' ε_mca' MC) :
    IsMCAGenerator (TensorGenerator_Explicit G G') (ε_mca + ε_mca') MC := by
  intro δ
  refine iSup_le fun U => ?_
  classical
  let W : S' → ℓ → ι → A := fun x' i k => ∑ j, G' x' j • U (i, j) k
  let V : S → ℓ' → ι → A := fun x j k => ∑ i, G x i • U (i, j) k
  have hv : ∀ (x : S) (x' : S'),
      (fun k => ∑ p : ℓ × ℓ', TensorGenerator_Explicit G G' (x, x') p • U p k) =
        fun k => ∑ i, G x i • W x' i k := by
    intro x x'
    funext k
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp [TensorGenerator_Explicit, mul_smul]
  have hv' : ∀ (x : S) (x' : S'),
      (fun k => ∑ p : ℓ × ℓ', TensorGenerator_Explicit G G' (x, x') p • U p k) =
        fun k => ∑ j, G' x' j • V x j k := by
    intro x x'
    funext k
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [TensorGenerator_Explicit, mul_smul]
      exact smul_comm _ _ _
  -- If all combined rows are good on some witness set, choose a bad column there.
  -- Otherwise use the combined rows themselves as the family for G.
  have hchoose : ∀ x' : S', ∃ Z : ℓ → ι → A, ∀ x : S,
      IsMCA (TensorGenerator_Explicit G G') MC (x, x') U δ →
        IsMCA G MC x Z δ ∨ IsMCA G' MC x' (V x) δ := by
    intro x'
    by_cases hb : ∃ T : Finset ι,
        (T.card : ℝ) ≥ Fintype.card ι * (1 - (δ : ℝ)) ∧
        (∀ i, projectedWord (W x' i) T ∈ projectedCodeSubmod MC T) ∧
        ∃ i j, projectedWord (U (i, j)) T ∉ projectedCodeSubmod MC T
    · obtain ⟨T, hT, hrows, i₀, j₀, hbad⟩ := hb
      refine ⟨fun i => U (i, j₀), fun x _ => ?_⟩
      by_cases hinner : IsMCA G' MC x' (V x) δ
      · exact Or.inr hinner
      · apply Or.inl
        refine ⟨T, hT, ?_, i₀, hbad⟩
        have hcomb : projectedWord (fun k => ∑ j, G' x' j • V x j k) T ∈
            projectedCodeSubmod MC T := by
          rw [← hv' x x', hv x x']
          apply (mem_projectedCodeSubmod_iff MC T _).mpr
          apply projectedCode_linearCombination MC T (W x') (G x)
          intro i
          exact (mem_projectedCodeSubmod_iff MC T _).mp (hrows i)
        by_contra hnot
        exact hinner ⟨T, hT, hcomb, j₀, hnot⟩
    · refine ⟨W x', ?_⟩
      rintro x ⟨T, hT, hcomb, ⟨i₀, j₀⟩, hbad⟩
      by_cases hrows : ∃ i, projectedWord (W x' i) T ∉ projectedCodeSubmod MC T
      · apply Or.inl
        rw [hv x x'] at hcomb
        exact ⟨T, hT, hcomb, hrows⟩
      · exfalso
        apply hb
        refine ⟨T, hT, ?_, i₀, j₀, hbad⟩
        intro i
        by_contra hi
        exact hrows ⟨i, hi⟩
  choose Z hZ using hchoose
  -- Z depends only on x', while V depends only on x, so each marginal MCA bound applies.
  have hA : Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (Z p.2) δ] ≤
      (ε_mca δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _
      (fun x' => hGMCA.prob_le (Z x') δ)
  have hB : Pr{let p ← $ᵗ (S × S')}[IsMCA G' MC p.2 (V p.1) δ] ≤
      (ε_mca' δ : ENNReal) :=
    SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _
      (fun x => hG'MCA.prob_le (V x) δ)
  calc Pr{let p ← $ᵗ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr{let p ← $ᵗ (S × S')}[
          IsMCA G MC p.1 (Z p.2) δ ∨ IsMCA G' MC p.2 (V p.1) δ] :=
        prEvent_mono _ _ _ (fun p => hZ p.2 p.1)
    _ ≤ Pr{let p ← $ᵗ (S × S')}[IsMCA G MC p.1 (Z p.2) δ] +
        Pr{let p ← $ᵗ (S × S')}[IsMCA G' MC p.2 (V p.1) δ] :=
        prEvent_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal) + (ε_mca' δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + ε_mca') δ : ENNReal) := by
      rw [Pi.add_apply, ENNReal.coe_add]

end LinearTransformations
