/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import ArkLib.Data.Probability.Instances

/-!
# Mutual correlated agreement under row-wise interleaving

This file compares the MCA error of a module code `C` with the MCA error of its row-wise
interleaving `C ^⋈ κ`, for an arbitrary generator `G : Generator S ℓ F`. The row index `κ` is
finite for the forward transfer and equality, and only nonempty for the reverse transfer.
The radius `δ` is an arbitrary real number throughout.

* Interleaving does not increase the error when the seed space is no larger than the field,
  `|S| ≤ |F|`. This direction holds for every finite `κ`, including an empty one.
* Interleaving does not decrease the error when `κ` is nonempty. This direction holds for every
  generator.
* The two directions give equality when `κ` is nonempty and `|S| ≤ |F|`.

## Main statements

* `Code.projectedWord_rowCombination_mem`: every `F`-linear combination of the rows
  of a word that projects into `C ^⋈ κ` projects into `C`.
* `Code.exists_rowFunctional_forall_notMem`: given at most `|F|` interleaved projection
  failures, one row functional `l : κ → F` turns every one of them into a failure of a scalar row
  combination.
* `CoreDefinitions.isMCA_iff_isProjectionBad`: the MCA event at radius `δ` is the integer-threshold
  event `Code.IsProjectionBad` at threshold `⌈|ι| · (1 - δ)⌉₊`.
* `CoreDefinitions.exists_forall_isMCA_of_forall_isMCA_interleaved`: at most `|F|` seeds that are
  bad for one family over `C ^⋈ κ` are all bad for one family over `C`.
* `CoreDefinitions.mcaError_moduleInterleavedCode_le_of_card_le`: if `|S| ≤ |F|`, then
  `mcaError G (C^⋈κ) δ ≤ mcaError G C δ`.
* `CoreDefinitions.mcaError_le_mcaError_moduleInterleavedCode`: if `κ` is nonempty, then
  `mcaError G C δ ≤ mcaError G (C^⋈κ) δ`.
* `CoreDefinitions.mcaError_moduleInterleavedCode_eq_of_card_le`: the equality.

## Proof outline

Fix a family `U : ℓ → ι → κ → A` of interleaved words. Each seed `x` that is bad for `U` comes
with a set `T x` of coordinates on which the generated word projects into `C ^⋈ κ` but some `U j`
does not. The row functionals `l : κ → F` for which every row combination
`i ↦ ∑ r, l r • U j i r` projects into `C` on `T x` form a submodule
`goodRowFunctionals C U (T x)` of `κ → F`. This submodule is proper: some row of some `U j` fails
to project into `C` on `T x`, and the coordinate functional of that row is then not in it.

At most `|F|` proper submodules do not cover `κ → F`. For finite `F` this is
`Submodule.exists_forall_notMem_of_card_le`, and for infinite `F` it is Mathlib's
`Submodule.exists_forall_notMem_of_forall_ne_top`. Choose `l` outside the submodules of all bad
seeds and set `V j := i ↦ ∑ r, l r • U j i r`. For a bad seed `x`, the word generated from `V` is
the `l`-combination of the rows of the word generated from `U`, so it projects into `C` on `T x`.
Some `V j` does not project into `C` on `T x`, by the choice of `l`. Hence every seed that is bad
for `U` is bad for `V`. There are at most `|S|` bad seeds, so `|S| ≤ |F|` suffices.

The reverse inequality embeds a family `U` over `C` as the interleaved family whose rows are all
equal to `U`.

## References

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Corollary 4.5, the exact transfer when the seed space has at most as many
  elements as the field.
* ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d` proves this row-projection argument
  three times, as private declarations under `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/`:
  `interleaved_powerProjectionBad_card_le` in `PowerAgreement.lean` (univariate powers over a
  finite field), `interleaved_powerProjectionBadArbitrary_finset_card_le` in
  `PowerAgreementArbitrary.lean` (univariate powers over an arbitrary field), and
  `interleaved_lineProjectionBad_card_le` in
  `TensorFoldAgreement.lean` (the binary line fold). Their shared row-functional avoidance step
  is supplied by `Code.exists_rowFunctional_forall_notMem`. The integer-threshold transfer and
  the exact-agreement conclusions of the first two are in
  `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`; the seedwise transfer here is derived
  from `Code.exists_forall_isProjectionBad_of_interleaved` through `isMCA_iff_isProjectionBad`.

Not covered here: the field-size-weighted transfer bound of [Jo26] for seed spaces larger than the
field.
-/

@[expose] public section

namespace CoreDefinitions

open LinearCode Code Probability
open scoped ProbabilityTheory


section Transfer

variable {ι F A κ ℓ : Type} [Fintype ι] [Field F] [AddCommMonoid A] [Module F A] [Finite κ]
  [Fintype ℓ]

omit [Finite κ] in
/-- **The MCA event is an integer-threshold event.** The size condition `|T| ≥ |ι| · (1 - δ)` of
`IsMCA` holds exactly when `⌈|ι| · (1 - δ)⌉₊ ≤ |T|`, so `IsMCA G C x U δ` is
`Code.IsProjectionBad G C ⌈|ι| · (1 - δ)⌉₊ x U`. For `δ ≥ 1` the threshold is `0`. -/
theorem isMCA_iff_isProjectionBad {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
    (C : ModuleCode ι F A) (x : S) (U : ℓ → ι → A) (δ : ℝ) :
    IsMCA G C x U δ ↔ IsProjectionBad G C ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ x U := by
  simp only [IsMCA, IsProjectionBad, ge_iff_le, Nat.ceil_le]

/-- **Seedwise transfer from an interleaved code to its base code.** If every seed in a set `s`
of at most `|F|` seeds is bad for the family `U` over `C ^⋈ κ` at radius `δ`, then one family `V`
over `C` has every seed in `s` bad at the same radius `δ`.

This is `Code.exists_forall_isProjectionBad_of_interleaved` at the threshold
`⌈|ι| · (1 - δ)⌉₊`, through `isMCA_iff_isProjectionBad`. There `V j` is the row combination
`i ↦ ∑ r, l r • U j i r` for the row functional `l` of `exists_rowFunctional_forall_notMem`,
applied to the witness sets of the seeds in `s`. The bound `hs` is the hypothesis of that lemma;
it is automatic for infinite `F`. The generator and the radius are arbitrary: a seed keeps its
witness set `T`, so the size clause of `IsMCA` carries over unchanged at every real `δ`. For
empty `s`, any `V` works. -/
theorem exists_forall_isMCA_of_forall_isMCA_interleaved {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) (U : ℓ → ι → κ → A) (s : Finset S)
    (hs : (s.card : ℕ∞) ≤ ENat.card F) (hbad : ∀ x ∈ s, IsMCA G (C^⋈κ) x U δ) :
    ∃ V : ℓ → ι → A, ∀ x ∈ s, IsMCA G C x V δ := by
  simp only [isMCA_iff_isProjectionBad] at hbad ⊢
  exact exists_forall_isProjectionBad_of_interleaved G C _ U s hs hbad

/-- **Interleaving does not increase MCA error when `|S| ≤ |F|`.** For every generator
`G : Generator S ℓ F` whose seed space has at most as many elements as the field, every module
code `C`, every finite row index `κ` and every real radius `δ`,
`mcaError G (C^⋈κ) δ ≤ mcaError G C δ`.

This generalizes [Jo26] Corollary 4.5 (one direction) and `ProximityGap.mcaError_interleaved_le`,
which is the affine-line case.

For a family `U` over `C ^⋈ κ`, the set of bad seeds has at most `|S| ≤ |F|` elements, so
`exists_forall_isMCA_of_forall_isMCA_interleaved` gives a family `V` over `C` that is bad at every
one of them. The hypothesis `hS` is used only there, to bound the number of submodules that one
row functional must avoid. It holds for every generator whose seed type is `F` itself, and for
every generator with finitely many seeds when `F` is infinite. For larger seed spaces [Jo26]
proves a weaker, field-size-weighted bound, which is not formalized here.

Edge cases: an empty `κ` needs no separate argument; there `C ^⋈ κ` has no bad seeds and the left
side is `0`. Radii outside `[0, 1]` need no separate argument either, because `IsMCA` is defined at
every real radius. -/
theorem mcaError_moduleInterleavedCode_le_of_card_le {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) (hS : ENat.card S ≤ ENat.card F) :
    mcaError G (C^⋈κ) δ ≤ mcaError G C δ := by
  classical
  refine iSup_le fun U ↦ ?_
  let s := Finset.univ.filter fun x ↦ IsMCA G (C^⋈κ) x U δ
  have hs : (s.card : ℕ∞) ≤ ENat.card F :=
    calc (s.card : ℕ∞) ≤ Fintype.card S := Nat.cast_le.mpr (Finset.card_le_univ s)
      _ = ENat.card S := ENat.card_eq_coe_fintype_card.symm
      _ ≤ ENat.card F := hS
  obtain ⟨V, hV⟩ := exists_forall_isMCA_of_forall_isMCA_interleaved G C δ U s hs
    fun x hx ↦ (Finset.mem_filter.mp hx).2
  calc Pr_{let x ←$ᵖ S}[IsMCA G (C^⋈κ) x U δ]
      ≤ Pr_{let x ←$ᵖ S}[IsMCA G C x V δ] :=
        Pr_le_Pr_of_implies _ _ _ fun x hx ↦
          hV x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
    _ ≤ mcaError G C δ := le_iSup (fun V ↦ Pr_{let x ←$ᵖ S}[IsMCA G C x V δ]) V

omit [Finite κ] in
/-- **Interleaving does not decrease MCA error.** For every generator `G`, every module code `C`,
every nonempty row index `κ` and every real radius `δ`, `mcaError G C δ ≤ mcaError G (C^⋈κ) δ`.

A family `U` over `C` embeds as the interleaved family `j ↦ i ↦ (r ↦ U j i)`, whose rows all
equal `U j`. A seed that is bad for `U` with witness set `T` is bad for the embedded family with
the same `T`: the generated word has every row equal to the generated word of `U`, and a member
that fails to project into `C` has a row that fails to project, so the member fails to project into
`C ^⋈ κ`. The argument is pointwise in the family and the seed, so it needs no condition on the
generator, the seed space or the radius, and `κ` need not be finite.

The hypothesis `Nonempty κ` is necessary. For empty `κ`, every word projects into `C ^⋈ κ`, so
the right side is `0`, while the left side can be positive. -/
theorem mcaError_le_mcaError_moduleInterleavedCode [Nonempty κ] {S : Type} [Nonempty S]
    [Fintype S] (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError G C δ ≤ mcaError G (C^⋈κ) δ := by
  refine iSup_le fun U ↦ ?_
  refine le_trans (Pr_le_Pr_of_implies _ _ _ fun x hx ↦ ?_)
    (le_iSup (fun W : ℓ → ι → κ → A ↦ Pr_{let x ←$ᵖ S}[IsMCA G (C^⋈κ) x W δ])
      fun j i _ ↦ U j i)
  obtain ⟨T, hT, hcomb, j, hj⟩ := hx
  refine ⟨T, hT, ?_, j, fun hmem ↦ hj ?_⟩
  · refine (projectedCodeSubmod_moduleInterleavedCode_iff F A κ ι C _ T).mpr fun r ↦ ?_
    have hrow : InterleavedWord.getRowWord (fun i ↦ ∑ j, G x j • fun (_ : κ) ↦ U j i) r =
        fun i ↦ ∑ j, G x j • U j i := by
      funext i
      change (∑ j, G x j • (fun (_ : κ) ↦ U j i)) r = ∑ j, G x j • U j i
      simp
    rw [hrow]
    exact hcomb
  · obtain ⟨r⟩ := ‹Nonempty κ›
    exact (projectedCodeSubmod_moduleInterleavedCode_iff F A κ ι C _ T).mp hmem r

/-- **Interleaving preserves MCA error when `|S| ≤ |F|`.** For every generator
`G : Generator S ℓ F` whose seed space has at most as many elements as the field, every module
code `C`, every nonempty finite row index `κ` and every real radius `δ`,
`mcaError G (C^⋈κ) δ = mcaError G C δ`.

This is [Jo26] Corollary 4.5 for an arbitrary generator and module code. It combines
`mcaError_moduleInterleavedCode_le_of_card_le`, which needs `hS`, with
`mcaError_le_mcaError_moduleInterleavedCode`, which needs `Nonempty κ`. The affine-line case with
`κ = Fin t` is `ProximityGap.mcaError_interleaved_eq`. -/
theorem mcaError_moduleInterleavedCode_eq_of_card_le [Nonempty κ] {S : Type} [Nonempty S]
    [Fintype S] (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ)
    (hS : ENat.card S ≤ ENat.card F) :
    mcaError G (C^⋈κ) δ = mcaError G C δ :=
  le_antisymm (mcaError_moduleInterleavedCode_le_of_card_le G C δ hS)
    (mcaError_le_mcaError_moduleInterleavedCode G C δ)

end Transfer

end CoreDefinitions
