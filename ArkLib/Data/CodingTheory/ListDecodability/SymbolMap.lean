/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability

/-!
# List sizes under an injective change of alphabet

Let `e : A → B` be injective, and let codes `C ⊆ ι → A` and `D ⊆ ι → B` satisfy
`e ∘ c ∈ D` for every `c ∈ C`. Applying `e` symbol by symbol preserves the relative Hamming
distance between any two words (`Code.relHammingDist_comp`), so it maps the point list of `C`
around a word `f` injectively into the point list of `D` around `e ∘ f`. Hence the maximised list
size of `C` is at most that of `D`, at every radius.

The typical use is an interleaved code over `A = κ → F`, where `e` packs a column of `κ` field
elements into one element of a larger ring and `D` is a scalar code over that ring. The
interleaved Reed–Solomon instance is
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds`. When the symbol map is a
bijection carrying one code onto the other, the inequality becomes an equality; the instance for
a basis of a field extension is `CodingTheory.lambda_extensionCode_eq_lambda_interleaved`.

## Main statements

* `Code.encard_closeCodewordsRel_le_of_injective_comp`: the pointwise inequality of point lists.
* `Code.Lambda_le_of_injective_comp`: the inequality of maximised list sizes.

## References

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AgreementBounds.lean`: the proof of
`lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound` injects every finite subset of an
interleaved point list into a scalar point list over `RatFunc F`. That injection is stated here
for arbitrary alphabets, codes and injective symbol maps.
-/

@[expose] public section

namespace Code

variable {ι : Type*} [Fintype ι] {A B : Type*}

/-- **Point lists under an injective symbol map.** If `e` is injective and sends every codeword
of `C` into `D` coordinatewise, the point list of `C` around `f` has at most as many elements as
the point list of `D` around `e ∘ f`, at every radius.

Injectivity is needed twice: it makes `c ↦ e ∘ c` injective, and it makes `e` preserve the
relative distance. For a non-injective `e` both can fail; for instance a constant `e` collapses
the whole list of `C` to one word. -/
theorem encard_closeCodewordsRel_le_of_injective_comp {C : Set (ι → A)} {D : Set (ι → B)}
    {e : A → B} (he : Function.Injective e) (hCD : ∀ c ∈ C, e ∘ c ∈ D) (f : ι → A) (δ : ℝ) :
    (closeCodewordsRel C f δ).encard ≤ (closeCodewordsRel D (e ∘ f) δ).encard := by
  classical
  have hinj : Set.InjOn (fun c : ι → A ↦ e ∘ c) (closeCodewordsRel C f δ) :=
    fun c _ d _ hcd ↦ funext fun i ↦ he (congrFun hcd i)
  rw [← hinj.encard_image]
  refine Set.encard_mono ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_closeCodewordsRel_iff] at hc ⊢
  exact ⟨hCD c hc.1, by rw [relHammingDist_comp he]; exact hc.2⟩

/-- **Maximised list sizes under an injective symbol map.** If `e` is injective and sends every
codeword of `C` into `D` coordinatewise, then `Lambda C δ ≤ Lambda D δ` for every radius `δ`.
The hypotheses are those of `encard_closeCodewordsRel_le_of_injective_comp`. -/
theorem Lambda_le_of_injective_comp {C : Set (ι → A)} {D : Set (ι → B)} {e : A → B}
    (he : Function.Injective e) (hCD : ∀ c ∈ C, e ∘ c ∈ D) (δ : ℝ) :
    Lambda C δ ≤ Lambda D δ :=
  Lambda_le_iff_forall_encard_le.mpr fun f ↦
    (encard_closeCodewordsRel_le_of_injective_comp he hCD f δ).trans
      (encard_closeCodewordsRel_le_Lambda D δ (e ∘ f))

end Code
