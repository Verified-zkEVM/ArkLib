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
arbitrary for the forward transfer, and nonempty for the reverse transfer and equality.
The radius `δ` is an arbitrary real number throughout.

* Interleaving does not increase the error when the seed space is no larger than the field,
  `|S| ≤ |F|`. This direction holds for every `κ`, including an empty one.
* Interleaving does not decrease the error when `κ` is nonempty. This direction holds for every
  generator.
* The two directions give equality when `κ` is nonempty and `|S| ≤ |F|`.
* For a finite field and a seed space of any size, interleaving increases the error by at most
  the factor `(q ^ s - 1) / (q ^ (s - 1) * (q - 1))`, where `q := |F|` and `s := |κ|`. This is the
  upper bound of [Jo26] Theorem 4.2; it follows the paper's Lemma 3.1 (in counting form) and
  Lemma 4.1.

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
* `CoreDefinitions.card_le_card_filter_isMCA_rowCombination`: over a finite field, a seed that is
  bad for an interleaved family stays bad over `C` for the row combinations of at least
  `q ^ (s - 1) * (q - 1)` nonzero row functionals.
* `CoreDefinitions.mcaError_moduleInterleavedCode_le_fieldWeighted`: for finite `F` and a seed
  space of any size, `mcaError G (C^⋈κ) δ ≤ (q ^ s - 1) / (q ^ (s - 1) * (q - 1)) * mcaError G C δ`.

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

For the forward transfer with arbitrary `κ`, first restrict to the finite image of one failing
row per bad seed; the row-functional argument above then runs over that finite row type.

Without a bound on `|S|`, a bad seed `x` still stays bad for the row combination of every
nonzero row functional outside `goodRowFunctionals C U (T x)`, and a proper submodule leaves at
least `q ^ (s - 1) * (q - 1)` of the `q ^ s - 1` nonzero functionals outside it
(`Submodule.le_card_filter_notMem_of_ne_top`). Double counting over the nonzero row functionals
(`Probability.natCast_mul_prob_le_sum_prob_of_le_card_filter`) gives the field-size-weighted
bound.

The seedwise transfer is derived from `Code.exists_forall_isProjectionBad_of_interleaved` through
`isMCA_iff_isProjectionBad`. The integer-threshold transfer and its exact-agreement consequences
are in `ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement`.

## References

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Lemma 3.1, Lemma 4.1, Theorem 4.2 and Corollary 4.5
-/

@[expose] public section

namespace CoreDefinitions

open LinearCode Code Probability
open scoped ProbabilityTheory


section Transfer

variable {ι F A κ ℓ : Type} [Fintype ι] [Field F] [AddCommMonoid A] [Module F A]
  [Fintype ℓ]

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
`⌈|ι| · (1 - δ)⌉₊`, through `isMCA_iff_isProjectionBad`. There `V j` is a row combination over
the finite image of one failing row per seed, using `exists_rowFunctional_forall_notMem`.
The bound `hs` is the hypothesis of that lemma;
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
code `C`, every row index `κ` and every real radius `δ`,
`mcaError G (C^⋈κ) δ ≤ mcaError G C δ`.

The affine-line case is `ProximityGap.mcaError_interleaved_le`.

For a family `U` over `C ^⋈ κ`, the set of bad seeds has at most `|S| ≤ |F|` elements, so
`exists_forall_isMCA_of_forall_isMCA_interleaved` gives a family `V` over `C` that is bad at every
one of them. The hypothesis `hS` is used only there, to bound the number of submodules that one
row functional must avoid. It holds for every generator whose seed type is `F` itself, and for
every generator with finitely many seeds when `F` is infinite.

Edge cases: an empty `κ` needs no separate argument; there `C ^⋈ κ` has no bad seeds and the left
side is `0`. Radii outside `[0, 1]` need no separate argument either, because `IsMCA` is defined at
every real radius. -/
theorem mcaError_moduleInterleavedCode_le_of_card_le {S : Type} [Nonempty S] [Fintype S]
    [SampleableType S] (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ)
    (hS : ENat.card S ≤ ENat.card F) :
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
  calc Pr{let x ← $ᵗ S}[IsMCA G (C^⋈κ) x U δ]
      ≤ Pr{let x ← $ᵗ S}[IsMCA G C x V δ] :=
        prEvent_mono _ _ _ fun x hx ↦
          hV x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
    _ ≤ mcaError G C δ := le_iSup (fun V ↦ Pr{let x ← $ᵗ S}[IsMCA G C x V δ]) V

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
    [Fintype S] [SampleableType S] (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError G C δ ≤ mcaError G (C^⋈κ) δ := by
  refine iSup_le fun U ↦ ?_
  refine le_trans (prEvent_mono _ _ _ fun x hx ↦ ?_)
    (le_iSup (fun W : ℓ → ι → κ → A ↦ Pr{let x ← $ᵗ S}[IsMCA G (C^⋈κ) x W δ])
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
code `C`, every nonempty row index `κ` and every real radius `δ`,
`mcaError G (C^⋈κ) δ = mcaError G C δ`.

The proof combines `mcaError_moduleInterleavedCode_le_of_card_le`, which needs `hS`, with
`mcaError_le_mcaError_moduleInterleavedCode`, which needs `Nonempty κ`. The affine-line case with
`κ = Fin t` is `ProximityGap.mcaError_interleaved_eq`. -/
theorem mcaError_moduleInterleavedCode_eq_of_card_le [Nonempty κ] {S : Type} [Nonempty S]
    [Fintype S] [SampleableType S] (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ)
    (hS : ENat.card S ≤ ENat.card F) :
    mcaError G (C^⋈κ) δ = mcaError G C δ :=
  le_antisymm (mcaError_moduleInterleavedCode_le_of_card_le G C δ hS)
    (mcaError_le_mcaError_moduleInterleavedCode G C δ)

end Transfer

section FieldWeighted

open Classical in
/-- **A bad interleaved seed stays bad under most row combinations.** Let `F` be a finite field
with `q := |F|` elements and `κ` a finite row index with `s := |κ|` elements. If `x` is bad for
the interleaved family `U` over `C ^⋈ κ`, it is bad over `C` for the row combination
`j ↦ i ↦ ∑ r, l r • U j i r` of at least `q ^ (s - 1) * (q - 1)` nonzero row functionals `l`.
The functionals for which it may fail form the proper submodule `goodRowFunctionals C U T` of the
witness set `T`. -/
lemma card_le_card_filter_isMCA_rowCombination
    {ι F A κ ℓ : Type} [Fintype ι] [Field F] [Fintype F]
    [AddCommMonoid A] [Module F A] [Fintype κ] [Fintype ℓ]
    {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ)
    (U : ℓ → ι → κ → A) (x : S) (hx : IsMCA G (C^⋈κ) x U δ) :
    Fintype.card F ^ (Fintype.card κ - 1) * (Fintype.card F - 1) ≤
      ((Finset.univ.erase (0 : κ → F)).filter fun l ↦
        IsMCA G C x (fun j i ↦ ∑ r, l r • U j i r) δ).card := by
  classical
  obtain ⟨T, hT, hcomb, j, hj⟩ := hx
  have hp : goodRowFunctionals C U T ≠ ⊤ := by
    intro htop
    exact hj ((goodRowFunctionals_eq_top_iff C U T).mp htop j)
  apply (Submodule.le_card_filter_notMem_of_ne_top _ hp).trans
  apply Finset.card_le_card
  intro l hl
  have hlp : l ∉ goodRowFunctionals C U T := (Finset.mem_filter.mp hl).2
  have hl0 : l ≠ 0 := fun h ↦ hlp (h ▸ (goodRowFunctionals C U T).zero_mem)
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hl0, Finset.mem_univ _⟩, T, hT, ?_, ?_⟩
  · have hmem := projectedWord_rowCombination_mem C _ T l hcomb
    rwa [rowCombination_sum_smul] at hmem
  · exact not_forall.mp fun h ↦ hlp ((mem_goodRowFunctionals_iff C U T l).mpr h)

/-- **Field-size-weighted interleaving bound.** For every generator `G : Generator S ℓ F` over a
finite field with `q := |F|` elements, every module code `C`, every finite row index `κ` with
`s := |κ|` and every real radius `δ`,
`mcaError G (C^⋈κ) δ ≤ (q ^ s - 1) / (q ^ (s - 1) * (q - 1)) * mcaError G C δ`.

The size of the seed space `S` is not bounded relative to `|F|`; the seed space is sampleable,
which provides finiteness and nonemptiness. Compare `mcaError_moduleInterleavedCode_le_of_card_le`,
which removes the factor when `|S| ≤ |F|`. For `s ≥ 1` the factor equals
`1 + 1/q + ⋯ + 1/q ^ (s - 1)`, which is less than `q / (q - 1)`. For `s = 0` the factor is `0`,
and so is the left-hand side: with no rows, no family is bad.

Average over the `q ^ s - 1` nonzero row functionals `l`: by
`card_le_card_filter_isMCA_rowCombination` each bad seed for `U` stays bad for the row
combination of at least `q ^ (s - 1) * (q - 1)` of them, so double counting gives
`q ^ (s - 1) (q - 1) · Pr[bad for U] ≤ (q ^ s - 1) · mcaError G C δ`. The reverse inequality
`mcaError G C δ ≤ mcaError G (C^⋈κ) δ` for nonempty `κ` is
`mcaError_le_mcaError_moduleInterleavedCode`. -/
theorem mcaError_moduleInterleavedCode_le_fieldWeighted
    {ι F A κ ℓ : Type} [Fintype ι] [Field F] [Fintype F] [AddCommMonoid A] [Module F A]
    [Fintype κ] [Fintype ℓ]
    {S : Type} [Fintype S] [SampleableType S]
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ) :
    mcaError G (C^⋈κ) δ ≤
      (((Fintype.card F : ENNReal) ^ Fintype.card κ - 1) /
        ((Fintype.card F : ENNReal) ^ (Fintype.card κ - 1) * ((Fintype.card F : ENNReal) - 1))) *
        mcaError G C δ := by
  classical
  let k : ℕ := Fintype.card F ^ (Fintype.card κ - 1) * (Fintype.card F - 1)
  let t : Finset (κ → F) := Finset.univ.erase 0
  have hkpos : 0 < k := Nat.mul_pos (pow_pos Fintype.card_pos _)
    (Nat.sub_pos_of_lt Fintype.one_lt_card)
  have hk0 : (k : ENNReal) ≠ 0 := by exact_mod_cast hkpos.ne'
  have htcard : (t.card : ENNReal) =
      (Fintype.card F : ENNReal) ^ Fintype.card κ - 1 := by
    simp [t, Finset.card_erase_of_mem, ENNReal.natCast_sub]
  have hkcast : (k : ENNReal) =
      (Fintype.card F : ENNReal) ^ (Fintype.card κ - 1) *
        ((Fintype.card F : ENNReal) - 1) := by
    simp [k, ENNReal.natCast_sub]
  refine iSup_le fun U ↦ ?_
  let V : (κ → F) → ℓ → ι → A := fun l j i ↦ ∑ r, l r • U j i r
  have hcount := Probability.natCast_mul_prob_le_sum_prob_of_le_card_filter t
    (fun x ↦ IsMCA G (C^⋈κ) x U δ) (fun l x ↦ IsMCA G C x (V l) δ) k
    (fun x hx ↦ card_le_card_filter_isMCA_rowCombination G C δ U x hx)
  have hsum : (k : ENNReal) * Pr{let x ← $ᵗ S}[IsMCA G (C^⋈κ) x U δ] ≤
      (t.card : ENNReal) * mcaError G C δ := by
    calc
      _ ≤ ∑ l ∈ t, Pr{let x ← $ᵗ S}[IsMCA G C x (V l) δ] := hcount
      _ ≤ ∑ _l ∈ t, mcaError G C δ := Finset.sum_le_sum fun l _ ↦
        le_iSup (fun W ↦ Pr{let x ← $ᵗ S}[IsMCA G C x W δ]) (V l)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    Pr{let x ← $ᵗ S}[IsMCA G (C^⋈κ) x U δ] ≤
        ((t.card : ENNReal) * mcaError G C δ) / (k : ENNReal) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl (by simp))).mpr
      simpa only [mul_comm] using hsum
    _ = ((t.card : ENNReal) / (k : ENNReal)) * mcaError G C δ := by
      simp only [div_eq_mul_inv, mul_comm, mul_left_comm]
    _ = _ := by rw [htcard, hkcast]

end FieldWeighted

end CoreDefinitions
