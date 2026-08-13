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

- `tensor_isMCAGenerator` — Lemma 4.4 [BCGM25] (tight form): if `G` has MCA with error `ε_mca`
for `MC` and `G'` has MCA with error `ε'_mca` for the `ℓ`-fold interleaving `MC^⋈ℓ`, then the
tensor generator `G ⊗ G'` has MCA with error `ε_mca + ε'_mca` for `MC`.
- `tensor_isMCAGenerator_of_base` — Lemma 4.4 [BCGM25] at its printed hypothesis (`G'` has MCA
for `MC` itself), at the weaker error `ε_mca + ℓ • ε'_mca`: a union bound over the `ℓ` rows is
forced by this proof strategy. (That the printed error is *unreachable* from the printed
hypothesis is not claimed and not known: no separation at equal error is exhibited anywhere,
here or in [BCGM25]. What is established is that the paper's own argument does not reach it.)

  **Where the missing factor actually lives.** The case-(b) event *is* the MCA event of `G'` for
  the interleaving `MC^⋈ℓ`, so the printed error would follow from the printed hypothesis as soon
  as `ε_mca(C^ℓ) ≤ ε_mca(C)` — that interleaving costs nothing. [BCGM25] Lemma 10.1 gives only
  `ε_mca(C^k) ≤ k · ε_mca(C)`, and [ABF26] states the improvement as **open** immediately after
  its Lemma 4.7 (`ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`): *"It is an open question whether this bound
  is tight or can be improved."* So the `ℓ` here is exactly that open factor, not an artefact of
  this formalisation — and a proof of Lemma 4.4 at the printed hypothesis and the printed error,
  by this route, would resolve a stated open problem.

  Note the error type is `I → ℝ≥0` rather than `I → I`, so this bound is vacuous once
  `|ℓ| · ε'_mca δ ≥ 1`; [BCGM25] types its MCA error `[0,1] → [0,1]`.
- `isMCAGenerator_of_moduleInterleavedCode` — MCA for the interleaving implies MCA for the base
code at the same error, so the tight form's hypothesis is a strengthening of the printed one.

### On the interleaved hypothesis

[BCGM25]'s printed Lemma 4.4 assumes `G` and `G'` have mutual correlated agreement for `C`, but
its proof bounds the second case (Equation (5)) by applying `G'`'s MCA to the `ℓ`-fold
interleaving `C^ℓ ⊆ (Σ^ℓ)^n`: the family fed to `G'` is the stack `w_j := (u_{(1,j)}, …,
u_{(ℓ,j)})`, whose entries are interleaved symbols. We therefore hypothesise `G'`'s MCA **at the
interleaving**, which is what the proof actually uses.

**Where that strengthening is free, and where it is not.** [BCGM25] invokes Lemma 4.4 in
exactly two places, and they behave differently.

* **Theorem 8.2** (MCA for polynomial generators). Here the base MCA comes from Theorem 6.1,
  which is stated for *every* `F`-linear code `C ⊆ Σ^n` with error depending on `C` only
  through `n` and `δ_C`. The interleaving `C^ℓ ⊆ (Σ^ℓ)^n` is `F`-linear with the same `n` and
  the same relative distance, so Theorem 6.1 discharges the interleaved hypothesis directly.
  The strengthening costs nothing.

  *Caveat.* The distance half of that argument — `δᵣ(MC^⋈κ) = δᵣ(MC)` — has **no in-tree
  witness**: it is deferred, not proved here. So "costs nothing" is currently a claim about
  [BCGM25]'s Theorem 6.1 read on paper, not a fact this file establishes. `F`-linearity of the
  interleaving *is* in-tree (`ModuleCode.moduleInterleavedCode`).
* **Theorem 9.2** (polynomial generators for Reed–Solomon, list-decoding regime). Here the base
  MCA comes from Lemma 9.3, which is stated **only** for `C := RS[F, D, k]` and whose proof is
  irreducibly Reed–Solomon-specific (it constructs the Guruswami–Sudan polynomial `Q(X, Y, Z)`
  of [BCIKS20, Theorem 5.1] and factors `disc*_Y(Q)`). The interleaving `RS^ℓ ⊆ (F^ℓ)^n` is not
  a Reed–Solomon code, so Lemma 9.3 says nothing about it and the interleaved hypothesis is
  **not** dischargeable *at error `ε'_mca`*. It is dischargeable at a worse error: [BCGM25]'s
  own Lemma 10.1 (plain MCA implies MCA for the `k`-interleaving at error `k · ε_mca`) supplies
  the interleaved hypothesis at `ℓ · ε'_mca`. So the loss here is a factor of `ℓ`, not an
  outright obstruction — which is exactly the error the weak form
  `tensor_isMCAGenerator_of_base` reaches directly, at `ε_mca + ℓ • ε'_mca`.

So the deviation is invisible at Theorem 8.2 and *material* at Theorem 9.2. Both forms are
proved here for that reason; neither subsumes the other in practice.

**A separate gap in the source, noticed while checking the above.** The proof of Theorem 9.2
writes "By Lemma 9.3, `G_d` has mutual correlated agreement for any linear code `C` with error
`ε_MCA,RS,d`" — but Lemma 9.3 is stated only for Reed–Solomon codes. The parallel sentence in
the proof of Theorem 8.2 ("for any `F`-linear code `C`") *is* justified, by Theorem 6.1; the
Theorem 9.2 one is not justified by the lemma it cites. Theorem 9.2's printed error therefore
does not follow from its printed proof, independently of anything in this file. Were Lemma 9.3
in fact alphabet-general, the interleaved hypothesis above would be dischargeable there too.

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
open Probability

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
      ≤ (ε_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')
      (fun p => IsMCA G MC p.1 (W p.2) δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun x' => hG.apply (W x') δ
  have hB : Pr_{let p ← $ᵖ (S × S')}[
        IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ]
      ≤ (ε'_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_prod
      (fun p => IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun _ => hG'.apply w δ
  calc Pr_{let p ← $ᵖ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ ∨
          IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
        + Pr_{let p ← $ᵖ (S × S')}[
            IsMCA G' (ModuleCode.moduleInterleavedCode F A ℓ ι MC) p.2 w δ] :=
        Pr_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal) + (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, ENNReal.coe_add]

omit [Fintype ℓ] in
/-- Mutual correlated agreement for the `ℓ`-fold interleaving implies mutual correlated
agreement for the base code, at the same error: stack a base family as an interleaved family
with constant rows. Together with `tensor_isMCAGenerator` this shows the interleaved
hypothesis is a strengthening of [BCGM25]'s printed "MCA for `C`" hypothesis. -/
theorem isMCAGenerator_of_moduleInterleavedCode [Nonempty ℓ] (G' : Generator S' ℓ' F)
    (ε'_mca : I → ℝ≥0) (MC : ModuleCode ι F A)
    (hG' : IsMCAGenerator G' ε'_mca (ModuleCode.moduleInterleavedCode F A ℓ ι MC)) :
    IsMCAGenerator G' ε'_mca MC := by
  intro δ
  refine iSup_le fun U => ?_
  refine le_trans (Pr_le_Pr_of_implies _ _ _ fun x' => ?_) (hG'.apply (fun j k _ => U j k) δ)
  rintro ⟨T, hT, hcomb, j₀, hbad⟩
  refine ⟨T, hT, ?_, j₀, fun hmem => hbad ?_⟩
  · rw [projectedCodeSubmod_moduleInterleavedCode_iff]
    intro i
    have : InterleavedWord.getRowWord (fun k => ∑ j, G' x' j • (fun k _ => U j k : ι → ℓ → A) k) i
        = fun k => ∑ j, G' x' j • U j k := by
      funext k
      simp [InterleavedWord.getRowWord, Finset.sum_apply]
    rw [this]
    exact hcomb
  · obtain ⟨i⟩ := ‹Nonempty ℓ›
    have h := (projectedCodeSubmod_moduleInterleavedCode_iff
      F A ℓ ι MC (fun k _ => U j₀ k) T).mp hmem i
    have hrow : InterleavedWord.getRowWord (fun k (_ : ℓ) => U j₀ k) i = U j₀ := by
      funext k; simp [InterleavedWord.getRowWord]
    rwa [hrow] at h

/-- **Lemma 4.4 [BCGM25] at its printed hypothesis.** If `G` and `G'` both have mutual
correlated agreement for `MC` itself (the hypothesis as printed in the paper), the tensor
generator has MCA for `MC` with error `ε_mca + ℓ • ε'_mca`.

The `ℓ` factor is forced: without the interleaved hypothesis, the row witnessing
non-membership depends on the outer seed `x'`, so the case-(b) family fed to `G'` is not
fixed and a union bound over the `ℓ` rows is required. The paper's printed error
`ε_mca + ε'_mca` is recovered by `tensor_isMCAGenerator` under the (strictly stronger, cf.
`isMCAGenerator_of_moduleInterleavedCode`) hypothesis that `G'` has MCA for the `ℓ`-fold
interleaving — which is what the paper's own proof of Lemma 4.4 uses. -/
theorem tensor_isMCAGenerator_of_base (G : Generator S ℓ F) (G' : Generator S' ℓ' F)
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
  have hA : Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
      ≤ (ε_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_equiv_prod (Equiv.prodComm S S')
      (fun p => IsMCA G MC p.1 (W p.2) δ)]
    exact Pr_seq_le_of_forall_le _ _ _ fun x' => hG.apply (W x') δ
  have hB : Pr_{let p ← $ᵖ (S × S')}[∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ]
      ≤ (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) := by
    rw [prob_split_uniform_sampling_of_prod
      (fun p => ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ)]
    refine Pr_seq_le_of_forall_le _ _ _ fun _ => le_trans (Pr_exists_le _ _) ?_
    have hsum : ∑ i : ℓ, Pr_{let x' ← $ᵖ S'}[IsMCA G' MC x' (fun j => U (i, j)) δ]
        ≤ ∑ _i : ℓ, (ε'_mca δ : ENNReal) := by
      exact Finset.sum_le_sum fun i _ => hG'.apply (fun j => U (i, j)) δ
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  calc Pr_{let p ← $ᵖ (S × S')}[IsMCA (TensorGenerator_Explicit G G') MC p U δ]
      ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ ∨
          ∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ] :=
        Pr_le_Pr_of_implies _ _ _ himp
    _ ≤ Pr_{let p ← $ᵖ (S × S')}[IsMCA G MC p.1 (W p.2) δ]
        + Pr_{let p ← $ᵖ (S × S')}[∃ i, IsMCA G' MC p.2 (fun j => U (i, j)) δ] :=
        Pr_or_le _ _ _
    _ ≤ (ε_mca δ : ENNReal)
        + (Fintype.card ℓ : ENNReal) * (ε'_mca δ : ENNReal) := add_le_add hA hB
    _ = ((ε_mca + Fintype.card ℓ • ε'_mca) δ : ENNReal) := by
        rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, ENNReal.coe_add, ENNReal.coe_mul,
          ENNReal.coe_natCast]

end TensorMCA
