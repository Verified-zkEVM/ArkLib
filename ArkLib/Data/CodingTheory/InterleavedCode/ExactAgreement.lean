/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode.Projection

/-!
# Exact agreement and its transfer to interleaved codes

Fix a module code `C : ModuleCode ι F A`, a family of words `U : ℓ → ι → A`, and a batching map
`G : S → ℓ → F` that sends a seed `x` to the coefficients of the combined word
`i ↦ ∑ j, G x j • U j i`. A codeword `c` that agrees with the combined word on at least `a`
coordinates has *exact agreement* at `x` if it is the same combination of codewords `c' j`, and
the coordinates where `c` agrees with the combined word are exactly the coordinates where every
`c' j` agrees with `U j`. A seed is *projection-bad* if some set of at least `a` coordinates
carries a codeword agreeing with the combined word, while some `U j` has no codeword agreeing
with it on that set.

This file proves three things.

* Exact agreement for all candidates at a seed rules out projection-badness at that seed. If
  codewords of `C` are determined by their values on any `a` coordinates, the converse holds.
  Consequently a uniform exact-agreement guarantee with at most `e` exceptional seeds is
  equivalent to the projection-bad seeds numbering at most `e`.
* If every scalar family over `C` has at most `e` projection-bad seeds, then every family over
  the interleaved code `C ^⋈ κ` has at most `e` projection-bad seeds, for finite `κ`, provided
  the seed space has at most `|F|` elements or `e < |F|`. The count `e` is not multiplied by
  the number of rows.
* Combining the two: a uniform exact-agreement guarantee for every scalar family over `C`
  gives the same guarantee, with the same exceptional count, for every family over `C ^⋈ κ`.

Nothing here depends on the shape of `G`. Univariate power batching `z ↦ (1, z, …, z^ℓ)`
is the instance used by Reed–Solomon proximity arguments, and its exceptional counts come from
root counting in the scalar provider; the transfer itself does not use any degree bound. The
scalar guarantee is a hypothesis, so no list-decoding or proximity-gap result is imported.
One proof covers every field, every batching map, every module code, and every finite row type,
including an empty one. The Reed–Solomon specialization
`ReedSolomon.uniformExactInterleavedPowerAgreement_of_scalar` is in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.

## Main definitions

* `Code.IsProjectionBad G C a x U`: the seed `x` is projection-bad at threshold `a`.
* `Code.HasExactAgreement G C x U c`: the codeword `c` has exact agreement at `x`.
* `Code.UniformExactAgreement G C a e U`: one set of at most `e` seeds, chosen before the seed
  and the codeword, outside which every codeword with `a` agreements has exact agreement.
* `Code.DeterminedByAgreement C a`: two codewords that agree on `a` coordinates are equal.

## Main statements

* `Code.not_isProjectionBad_of_forall_hasExactAgreement` and
  `Code.hasExactAgreement_of_not_isProjectionBad`, combined in
  `Code.forall_hasExactAgreement_iff_not_isProjectionBad`.
* `Code.uniformExactAgreement_iff_encard_le`: under `DeterminedByAgreement`, the uniform
  guarantee with count `e` is `{x | IsProjectionBad G C a x U}.encard ≤ e`.
* `Code.exists_forall_isProjectionBad_of_interleaved`: at most `|F|` seeds that are bad for one
  interleaved family are all bad for one scalar family.
* `Code.encard_setOf_isProjectionBad_moduleInterleavedCode_le`: the counting transfer.
* `Code.uniformExactAgreement_moduleInterleavedCode`: the exact-agreement transfer.

## References

* [Jo, S., *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*][Jo26], Corollary 4.5
-/

@[expose] public section

namespace Code

open LinearCode

section Definitions

variable {ι F A ℓ S : Type*} [Semiring F] [AddCommMonoid A] [Module F A] [Fintype ℓ]

/-- **Projection-bad seed.** The seed `x` is projection-bad for the family `U` at threshold `a`
if some coordinate set `T` with at least `a` elements has the following two properties: the
combined word `i ↦ ∑ j, G x j • U j i` agrees on `T` with a codeword of `C`, and some `U j` agrees
on `T` with no codeword of `C`.

This is `CoreDefinitions.IsMCA` with the real size condition `|T| ≥ |ι| · (1 - δ)` replaced by
the integer condition `a ≤ |T|`, and without finiteness conditions on the seed type; the bridge
is `CoreDefinitions.isMCA_iff_isProjectionBad`. -/
def IsProjectionBad (G : S → ℓ → F) (C : ModuleCode ι F A) (a : ℕ) (x : S)
    (U : ℓ → ι → A) : Prop :=
  ∃ T : Finset ι, a ≤ T.card ∧
    projectedWord (fun i ↦ ∑ j, G x j • U j i) T ∈ projectedCodeSubmod C T ∧
    ∃ j, projectedWord (U j) T ∉ projectedCodeSubmod C T

/-- **Exact agreement of one codeword at one seed.** There are codewords `c' j ∈ C` such that
`c` is their combination `i ↦ ∑ j, G x j • c' j i`, and at every coordinate `i`, the codeword `c`
agrees with the combined word `i ↦ ∑ j, G x j • U j i` exactly when every `c' j` agrees with
`U j`.

The second condition is an equality of full agreement sets, not an inclusion of a chosen subset:
the witnesses create no agreement of `c` beyond their common agreement with the family. The
predicate does not require `c ∈ C`; it is used for codewords. -/
def HasExactAgreement (G : S → ℓ → F) (C : ModuleCode ι F A) (x : S) (U : ℓ → ι → A)
    (c : ι → A) : Prop :=
  ∃ c' : ℓ → ι → A, (∀ j, c' j ∈ C) ∧ (c = fun i ↦ ∑ j, G x j • c' j i) ∧
    ∀ i, c i = ∑ j, G x j • U j i ↔ ∀ j, c' j i = U j i

/-- **Uniform exact agreement.** One finite set `bad` of at most `e` seeds is chosen after the
family `U` and before the seed and the codeword. Every seed `x ∉ bad` and every codeword `c ∈ C`
that agrees with the combined word on some set of at least `a` coordinates has exact agreement
(`HasExactAgreement`).

Stating closeness as agreement on some set `T` with `a ≤ |T|` is equivalent to requiring at least
`a` agreements, and needs no decidable equality on `A` or finiteness of `ι`. -/
def UniformExactAgreement (G : S → ℓ → F) (C : ModuleCode ι F A) (a e : ℕ)
    (U : ℓ → ι → A) : Prop :=
  ∃ bad : Finset S, bad.card ≤ e ∧ ∀ x ∉ bad, ∀ c ∈ C, ∀ T : Finset ι, a ≤ T.card →
    (∀ i ∈ T, c i = ∑ j, G x j • U j i) → HasExactAgreement G C x U c

omit [Fintype ℓ] in
/-- **Codewords are determined by `a` agreements.** Two codewords of `C` that agree on some set
of at least `a` coordinates are equal. For a linear code of length `n` with `a ≤ n` this says
that the minimum distance exceeds `n - a`. The Reed–Solomon code of message length `k` satisfies
it whenever `k ≤ a` (`ReedSolomon.determinedByAgreement_code`). -/
def DeterminedByAgreement (C : ModuleCode ι F A) (a : ℕ) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, ∀ T : Finset ι, a ≤ T.card → (∀ i ∈ T, c i = c' i) → c = c'

omit [Fintype ℓ] in
/-- Determination by `a` agreements passes from a code to its row-wise interleaving, for any
row type: two interleaved codewords agreeing on `T` agree row by row on `T`. -/
theorem DeterminedByAgreement.moduleInterleavedCode {κ : Type*} {C : ModuleCode ι F A} {a : ℕ}
    (hC : DeterminedByAgreement C a) : DeterminedByAgreement (C^⋈κ) a := by
  intro c hc c' hc' T hT hcc'
  funext i r
  exact congrFun (hC (fun i ↦ c i r) (hc r) (fun i ↦ c' i r) (hc' r) T hT
    fun i hi ↦ congrFun (hcc' i hi) r) i

end Definitions

section Exactness

variable {ι F A ℓ S : Type*} [Semiring F] [AddCommMonoid A] [Module F A] [Fintype ℓ]
  {G : S → ℓ → F} {C : ModuleCode ι F A} {a : ℕ} {x : S} {U : ℓ → ι → A}

/-- **Exact agreement rules out projection-badness.** If at the seed `x` every codeword agreeing
with the combined word on at least `a` coordinates has exact agreement, then `x` is not
projection-bad.

Given a bad witness set `T`, a codeword `c` agrees with the combined word on `T`. Exact agreement
of `c` gives codewords `c' j` that agree with `U j` wherever `c` agrees with the combined word,
in particular on `T`, contradicting the failure of some `U j` on `T`. No hypothesis on `C` is
needed. -/
theorem not_isProjectionBad_of_forall_hasExactAgreement
    (h : ∀ c ∈ C, ∀ T : Finset ι, a ≤ T.card → (∀ i ∈ T, c i = ∑ j, G x j • U j i) →
      HasExactAgreement G C x U c) :
    ¬ IsProjectionBad G C a x U := by
  rintro ⟨T, hT, hmem, j, hj⟩
  obtain ⟨c, hc, hcT⟩ := (mem_projectedCodeSubmod_iff C T _).mp hmem
  have hagree : ∀ i ∈ T, c i = ∑ j, G x j • U j i := fun i hi ↦ (congrFun hcT ⟨i, hi⟩).symm
  obtain ⟨c', hc', -, hiff⟩ := h c hc T hT hagree
  exact hj <| (mem_projectedCodeSubmod_iff C T _).mpr
    ⟨c' j, hc' j, funext fun i ↦ ((hiff i).mp (hagree i i.2) j).symm⟩

/-- **Not projection-bad gives exact agreement.** Suppose codewords of `C` are determined by `a`
agreements and the seed `x` is not projection-bad. Then every codeword `c` agreeing with the
combined word on some set of at least `a` coordinates has exact agreement.

Let `T'` be the full set where `c` agrees with the combined word. Since `x` is not bad, every
`U j` agrees on `T'` with a codeword `c' j`. The combination `∑ j, G x j • c' j` is a codeword
that agrees with `c` on `T'`, so it equals `c` by `hC`. Both directions of the agreement-set
equality then follow coordinatewise.

`hC` is needed: for the full code `C = ⊤`, no seed is projection-bad, but if `G x = 0` then a
nonzero codeword is not a combination with coefficients `G x`. `ι` is finite so that the full
agreement set is a `Finset`. -/
theorem hasExactAgreement_of_not_isProjectionBad [Finite ι] (hC : DeterminedByAgreement C a)
    (hx : ¬ IsProjectionBad G C a x U) {c : ι → A} (hc : c ∈ C) {T : Finset ι}
    (hT : a ≤ T.card) (hcT : ∀ i ∈ T, c i = ∑ j, G x j • U j i) :
    HasExactAgreement G C x U c := by
  classical
  set w : ι → A := fun i ↦ ∑ j, G x j • U j i with hw
  have hfin : {i | c i = w i}.Finite := Set.toFinite _
  set T' := hfin.toFinset with hT'
  have hmemT' : ∀ i, i ∈ T' ↔ c i = w i := fun i ↦ by simp [T']
  have hTT' : T ⊆ T' := fun i hi ↦ (hmemT' i).mpr (hcT i hi)
  have hT'card : a ≤ T'.card := hT.trans (Finset.card_le_card hTT')
  have hwT' : projectedWord w T' ∈ projectedCodeSubmod C T' :=
    (mem_projectedCodeSubmod_iff C T' _).mpr
      ⟨c, hc, funext fun i ↦ ((hmemT' i).mp i.2).symm⟩
  have hU : ∀ j, projectedWord (U j) T' ∈ projectedCodeSubmod C T' := by
    by_contra hnot
    push Not at hnot
    exact hx ⟨T', hT'card, hwT', hnot⟩
  choose c' hc' hc'T using fun j ↦ (mem_projectedCodeSubmod_iff C T' _).mp (hU j)
  have hc'U : ∀ j, ∀ i ∈ T', c' j i = U j i := fun j i hi ↦ (congrFun (hc'T j) ⟨i, hi⟩).symm
  set d : ι → A := fun i ↦ ∑ j, G x j • c' j i with hd
  have hdC : d ∈ C := by
    have : d = ∑ j, G x j • c' j := by
      funext i
      simp [d]
    rw [this]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hc' j)
  have hcd : c = d := hC c hc d hdC T' hT'card fun i hi ↦ by
    rw [(hmemT' i).mp hi]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hc'U j i hi]
  refine ⟨c', hc', hcd, fun i ↦ ⟨fun hi j ↦ hc'U j i ((hmemT' i).mpr hi), fun hi ↦ ?_⟩⟩
  rw [hcd]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hi j]

/-- **Exact agreement at a seed is the absence of projection-badness**, for codes determined by
`a` agreements. The forward direction holds for every code
(`not_isProjectionBad_of_forall_hasExactAgreement`); the reverse direction uses `hC`
(`hasExactAgreement_of_not_isProjectionBad`). -/
theorem forall_hasExactAgreement_iff_not_isProjectionBad [Finite ι]
    (hC : DeterminedByAgreement C a) :
    (∀ c ∈ C, ∀ T : Finset ι, a ≤ T.card → (∀ i ∈ T, c i = ∑ j, G x j • U j i) →
      HasExactAgreement G C x U c) ↔ ¬ IsProjectionBad G C a x U :=
  ⟨not_isProjectionBad_of_forall_hasExactAgreement,
    fun hx _ hc _ hT hcT ↦ hasExactAgreement_of_not_isProjectionBad hC hx hc hT hcT⟩

variable {e : ℕ}

/-- **Uniform exact agreement bounds the projection-bad seeds.** A uniform exact-agreement
guarantee with at most `e` exceptional seeds leaves at most `e` projection-bad seeds: every
projection-bad seed lies in the exceptional set, by
`not_isProjectionBad_of_forall_hasExactAgreement`. No hypothesis on `C` is needed. -/
theorem encard_setOf_isProjectionBad_le_of_uniformExactAgreement
    (h : UniformExactAgreement G C a e U) :
    {x | IsProjectionBad G C a x U}.encard ≤ e := by
  obtain ⟨bad, hcard, hgood⟩ := h
  calc {x | IsProjectionBad G C a x U}.encard ≤ (bad : Set S).encard := by
        refine Set.encard_le_encard fun x hx ↦ ?_
        by_contra hxbad
        exact not_isProjectionBad_of_forall_hasExactAgreement (hgood x hxbad) hx
    _ = bad.card := Set.encard_coe_eq_coe_finsetCard bad
    _ ≤ e := by exact_mod_cast hcard

/-- **Few projection-bad seeds give uniform exact agreement.** If codewords of `C` are determined
by `a` agreements and at most `e` seeds are projection-bad, then the projection-bad seeds form
an exceptional set for `UniformExactAgreement`. -/
theorem uniformExactAgreement_of_encard_le [Finite ι] (hC : DeterminedByAgreement C a)
    (h : {x | IsProjectionBad G C a x U}.encard ≤ e) :
    UniformExactAgreement G C a e U := by
  have hfin := Set.finite_of_encard_le_coe h
  refine ⟨hfin.toFinset, ?_, fun x hx c hc T hT hcT ↦ ?_⟩
  · rw [hfin.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  · exact hasExactAgreement_of_not_isProjectionBad hC (by simpa using hx) hc hT hcT

/-- **Uniform exact agreement is a count of projection-bad seeds.** For a code determined by `a`
agreements, the uniform exact-agreement guarantee with count `e` holds exactly when at most `e`
seeds are projection-bad. -/
theorem uniformExactAgreement_iff_encard_le [Finite ι] (hC : DeterminedByAgreement C a) :
    UniformExactAgreement G C a e U ↔ {x | IsProjectionBad G C a x U}.encard ≤ e :=
  ⟨encard_setOf_isProjectionBad_le_of_uniformExactAgreement,
    uniformExactAgreement_of_encard_le hC⟩

end Exactness

section Transfer

variable {ι F A ℓ S κ : Type*} [Field F] [AddCommMonoid A] [Module F A] [Fintype ℓ] [Finite κ]
  (G : S → ℓ → F) (C : ModuleCode ι F A) (a : ℕ)

/-- **Seedwise transfer of projection-badness.** If every seed in a set `s` of at most `|F|`
seeds is projection-bad for a family `U` over `C ^⋈ κ`, then one family `V` over `C` has every
seed of `s` projection-bad, at the same threshold.

`V j` is the row combination `i ↦ ∑ r, l r • U j i r` for the row functional `l` of
`exists_rowFunctional_forall_notMem`, applied to the witness sets of the seeds in `s`. A seed
keeps its witness set, so the threshold is unchanged. The bound `hs` is automatic for infinite
`F`; for finite `F` it is sharp for the avoidance step (`|F| + 1` lines cover `F²`). -/
theorem exists_forall_isProjectionBad_of_interleaved (U : ℓ → ι → κ → A) (s : Finset S)
    (hs : (s.card : ℕ∞) ≤ ENat.card F) (hbad : ∀ x ∈ s, IsProjectionBad G (C^⋈κ) a x U) :
    ∃ V : ℓ → ι → A, ∀ x ∈ s, IsProjectionBad G C a x V := by
  let : Fintype κ := Fintype.ofFinite κ
  choose! T hT using hbad
  obtain ⟨l, hl⟩ := exists_rowFunctional_forall_notMem C U s T hs fun x hx ↦ (hT x hx).2.2
  refine ⟨fun j i ↦ ∑ r, l r • U j i r, fun x hx ↦ ⟨T x, (hT x hx).1, ?_, hl x hx⟩⟩
  have hcomb := projectedWord_rowCombination_mem C _ (T x) l (hT x hx).2.1
  have hfun : (fun i ↦ ∑ r, l r • (∑ j, G x j • U j i) r) =
      fun i ↦ ∑ j, G x j • ∑ r, l r • U j i r := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun r _ ↦ smul_comm _ _ _
  rw [hfun] at hcomb
  exact hcomb

/-- **Interleaving does not increase the number of projection-bad seeds.** Suppose every family
`V` over `C` has at most `e` projection-bad seeds. Then every family `U` over `C ^⋈ κ`, for finite
`κ`, has at most `e` projection-bad seeds, provided either the seed space has at most `|F|`
elements or `e < |F|`.

If more than `e` seeds were bad for `U`, choose `e + 1` of them. The hypothesis `hS` makes
`e + 1 ≤ |F|` in either case, so `exists_forall_isProjectionBad_of_interleaved` gives one scalar
family with all `e + 1` seeds bad, contradicting `hscalar`. The count `e` is not multiplied by
the number of rows. Over an infinite field `hS` always holds. For `S = F`, as for univariate
power batching, the first alternative holds. The second alternative covers larger seed spaces,
such as multivariate batching, whenever the scalar count is below the field size.

Edge cases: for empty `κ` every word projects into `C ^⋈ κ`, so no seed is bad and the bound is
immediate. -/
theorem encard_setOf_isProjectionBad_moduleInterleavedCode_le {e : ℕ}
    (hS : ENat.card S ≤ ENat.card F ∨ (e : ℕ∞) < ENat.card F)
    (hscalar : ∀ V : ℓ → ι → A, {x | IsProjectionBad G C a x V}.encard ≤ e)
    (U : ℓ → ι → κ → A) :
    {x | IsProjectionBad G (C^⋈κ) a x U}.encard ≤ e := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, htbad, htcard⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
  set s := htfin.toFinset
  have hscard : (s.card : ℕ∞) = e + 1 := by
    rw [← htfin.encard_eq_coe_toFinset_card, htcard]
  have hs : (s.card : ℕ∞) ≤ ENat.card F := by
    rcases hS with hS | hS
    · calc (s.card : ℕ∞) = t.encard := htfin.encard_eq_coe_toFinset_card.symm
        _ ≤ (Set.univ : Set S).encard := Set.encard_le_encard (Set.subset_univ t)
        _ = ENat.card S := Set.encard_univ S
        _ ≤ ENat.card F := hS
    · rw [hscard]
      exact Order.add_one_le_of_lt hS
  obtain ⟨V, hV⟩ := exists_forall_isProjectionBad_of_interleaved G C a U s hs
    fun x hx ↦ htbad (htfin.mem_toFinset.mp hx)
  have hle : t.encard ≤ {x | IsProjectionBad G C a x V}.encard :=
    Set.encard_le_encard fun x hx ↦ hV x (htfin.mem_toFinset.mpr hx)
  have hcontra := hle.trans (hscalar V)
  rw [htcard] at hcontra
  exact Nat.not_succ_le_self e (by exact_mod_cast hcontra)

/-- **Exact agreement transfers to interleaved codes with the same exceptional count.** Let the
codewords of `C` be determined by `a` agreements, and suppose every scalar family `V` over `C`
has a uniform exact-agreement guarantee with at most `e` exceptional seeds. Then every family
`U` over `C ^⋈ κ`, for finite `κ`, has the same guarantee with the same count `e`, provided the
seed space has at most `|F|` elements or `e < |F|`.

The scalar guarantee bounds the projection-bad seeds of every scalar family
(`encard_setOf_isProjectionBad_le_of_uniformExactAgreement`), the counting transfer bounds them
for `U` (`encard_setOf_isProjectionBad_moduleInterleavedCode_le`), and determination passes to
`C ^⋈ κ` (`DeterminedByAgreement.moduleInterleavedCode`), which converts the count back into
exact agreement (`uniformExactAgreement_of_encard_le`).

The hypothesis `hC` is used only in the last step; the count transfer does not need it. No
positive row count is needed. -/
theorem uniformExactAgreement_moduleInterleavedCode [Finite ι] {e : ℕ}
    (hS : ENat.card S ≤ ENat.card F ∨ (e : ℕ∞) < ENat.card F)
    (hC : DeterminedByAgreement C a)
    (hscalar : ∀ V : ℓ → ι → A, UniformExactAgreement G C a e V)
    (U : ℓ → ι → κ → A) :
    UniformExactAgreement G (C^⋈κ) a e U :=
  uniformExactAgreement_of_encard_le hC.moduleInterleavedCode
    (encard_setOf_isProjectionBad_moduleInterleavedCode_le G C a hS
      (fun V ↦ encard_setOf_isProjectionBad_le_of_uniformExactAgreement (hscalar V)) U)

end Transfer

end Code
