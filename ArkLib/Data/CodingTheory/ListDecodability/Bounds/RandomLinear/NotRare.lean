/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.BerP
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.Pivot

/-!
# The bad distribution is not implicitly rare

For every `s × L` matrix `A` with independent rows,
`H_q(A (u + α · 1_L)) ≥ s (h + h/(L + δ'))` under `badLaw` once `L` is large, where `h = H_q(p)`.
[GLMRSW22], Section 4, proves this lemma for the proof of their Theorem 4.1. The proof reduces
`A` to pivot form and applies `CodingTheory.RandomLinearInternal.entQ_add_mul_ber_lower` block by
block.

## Main statements

* `CodingTheory.RandomLinearInternal.block_entropy_lower`: the block decomposition.
* `CodingTheory.RandomLinearInternal.entQ_badLaw_mulVec_lower`: the entropy lower bound.

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Probability

/-- Block decomposition: lower bound for coordinates `r ∈ T` mixed with the `α`-coordinates `αs`,
given the bound `hβ` of `CodingTheory.RandomLinearInternal.entQ_add_mul_ber_lower` for the product
weight `b`. -/
theorem block_entropy_lower {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F]
    [DecidableEq F] {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) (p : ℝ) (L : ℕ) (β₀ : ℝ)
    (b : I → F → ℝ) (hb : ∀ i, IsProb (b i))
    (hβ : BlockEntropyBound q p L β₀ b)
    (V αs : Finset I) (hd : Disjoint V αs) (hV : ∀ i ∈ V, b i = ber q p)
    (hα : ∀ a ∈ αs, BerAtLeast q p (b a))
    (W : I → I → F) (T : Finset I) (hT : T ⊆ V) (hcov : ∀ r ∈ T, ∃ a ∈ αs, W r a ≠ 0)
    (hTL : T.card ≤ L) :
    (T.card : ℝ) * β₀ ≤
      entQ q (prodLaw b) (fun ω (r : T) => ω r + ∑ a ∈ αs, W r a * ω a) := by
  classical
  have hμ : IsProb (prodLaw b) := isProb_prodLaw b hb
  have hq1 : 1 < q := by omega
  induction αs using Finset.induction_on generalizing T with
  | empty =>
    have hT0 : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
      obtain ⟨a, ha, _⟩ := hcov r hr
      simp at ha
    subst hT0
    rw [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact entQ_nonneg hμ hq1 _
  | insert a αs haαs ih =>
    have haV : a ∉ V := fun h => Finset.disjoint_left.1 hd h (Finset.mem_insert_self _ _)
    have hd' : Disjoint V αs := hd.mono_right (Finset.subset_insert _ _)
    have hα' : ∀ a ∈ αs, BerAtLeast q p (b a) :=
      fun a' h => hα a' (Finset.mem_insert_of_mem h)
    set J := T.filter (fun r => W r a ≠ 0) with hJ
    set T' := T.filter (fun r => ¬ W r a ≠ 0) with hT'
    have hcard : J.card + T'.card = T.card := Finset.card_filter_add_card_filter_not _
    have hJT : J ⊆ T := Finset.filter_subset _ _
    have hT'T : T' ⊆ T := Finset.filter_subset _ _
    have hcov' : ∀ r ∈ T', ∃ a' ∈ αs, W r a' ≠ 0 := by
      intro r hr
      obtain ⟨hrT, hr0⟩ := Finset.mem_filter.1 hr
      obtain ⟨a', ha', hW⟩ := hcov r hrT
      rcases Finset.mem_insert.1 ha' with h | h
      · exact absurd (h ▸ hW) hr0
      · exact ⟨a', h, hW⟩
    have ih' := ih hd' hα' T' (hT'T.trans hT) hcov' ((Finset.card_le_card hT'T).trans hTL)
    have hβJ := hβ J a (fun h => haV (hT (hJT h))) (fun i hi => hV i (hT (hJT hi)))
      (hα a (Finset.mem_insert_self _ _)) ((Finset.card_le_card hJT).trans hTL) (fun r => W r a)
      (fun i hi => (Finset.mem_filter.1 hi).2)
    let S : Finset I := V.filter (fun r => W r a = 0) ∪ αs
    let Z : (I → F) → (I → F) := fun ω i => if i ∈ S then ω i else 0
    let Vv : (I → F) → (J → F) := fun ω r => ω r + W r a * ω a
    let ψ : (I → F) → (J → F) := fun z r => ∑ a' ∈ αs, W r a' * z a'
    let φ : (I → F) → (T' → F) := fun z r => z r + ∑ a' ∈ αs, W r a' * z a'
    let Y₁ : (I → F) → (T' → F) := fun ω r => ω r + ∑ a' ∈ αs, W r a' * ω a'
    have hαS : ∀ a' ∈ αs, a' ∈ S := fun a' h => Finset.mem_union_right _ h
    have hY : ∀ ω, Y₁ ω = φ (Z ω) := by
      intro ω
      funext r
      have hr : (r : I) ∈ S := by
        obtain ⟨hrT, hr0⟩ := Finset.mem_filter.1 r.2
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hT hrT, not_not.1 hr0⟩)
      simp only [Y₁, φ, Z, hr, ite_true]
      exact congrArg _ (Finset.sum_congr rfl fun a' ha' => by simp [hαS a' ha'])
    have hdisj : Disjoint (insert a (J : Set I)) (S : Set I) := by
      rw [Set.disjoint_left]
      intro i hi hiS
      have hiS' := Finset.mem_coe.1 hiS
      rcases hi with rfl | hiJ
      · rcases Finset.mem_union.1 hiS' with h | h
        · exact haV (Finset.mem_filter.1 h).1
        · exact haαs h
      · obtain ⟨hiT, hiW⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hiJ)
        rcases Finset.mem_union.1 hiS' with h | h
        · exact hiW (Finset.mem_filter.1 h).2
        · exact Finset.disjoint_left.1 hd' (hT hiT) h
    have hind : entQ q (prodLaw b) (fun ω => (Vv ω, Z ω)) =
        entQ q (prodLaw b) Vv + entQ q (prodLaw b) Z := by
      refine entQ_pair_eq_add_of_disjoint q b hb (P := insert a (J : Set I)) (Q := S) ?_ ?_ hdisj
      · intro x y h
        funext r
        simp only [Vv]
        rw [h r (Set.mem_insert_of_mem _ r.2), h a (Set.mem_insert _ _)]
      · intro x y h
        funext i
        simp only [Z]
        split_ifs with hi
        · exact h i (Finset.mem_coe.2 hi)
        · rfl
    have hpeel := entQ_peel hμ hq1 Y₁ Vv Z φ ψ hY hind
    let f : (T → F) → (T' → F) × (J → F) := fun y =>
      (fun r => y ⟨r.1, hT'T r.2⟩, fun r => y ⟨r.1, hJT r.2⟩)
    let g : (T' → F) × (J → F) → (T → F) := fun x r =>
      if h : W r a ≠ 0 then x.2 ⟨r.1, Finset.mem_filter.2 ⟨r.2, h⟩⟩
      else x.1 ⟨r.1, Finset.mem_filter.2 ⟨r.2, h⟩⟩
    have hfg := entQ_eq_of_inverse hμ hq1
      (fun ω (r : T) => ω r + ∑ a' ∈ insert a αs, W r a' * ω a') f g (by
        intro ω
        funext r
        by_cases h : W r a ≠ 0 <;> simp [g, f, h])
    have hcomp : f ∘ (fun ω (r : T) => ω r + ∑ a' ∈ insert a αs, W r a' * ω a') =
        fun ω => (Y₁ ω, Vv ω + ψ (Z ω)) := by
      funext ω
      refine Prod.ext ?_ ?_
      · funext r
        have h0 : W r a = 0 := not_not.1 (Finset.mem_filter.1 r.2).2
        simp [f, Y₁, Finset.sum_insert haαs, h0]
      · funext r
        have hs : ∑ x ∈ αs, W r x * (if x ∈ S then ω x else 0) = ∑ x ∈ αs, W r x * ω x :=
          Finset.sum_congr rfl fun x hx => by simp [hαS x hx]
        simp only [f, Vv, ψ, Z, Pi.add_apply, Finset.sum_insert haαs, Function.comp]
        rw [hs]
        ring
    rw [hcomp] at hfg
    rw [← hcard, Nat.cast_add, add_mul, add_comm]
    rw [← hfg]
    linarith [hpeel, ih', hβJ]

/-- For every `δ' > 0` there is `L₀` such that for all `L ≥ L₀` and every `s × L` matrix `A`
with independent rows (`s ≥ 1`), `H_q(A (u + α · 1_L)) ≥ s (H_q(p) + H_q(p)/(L + δ'))`
under `badLaw q p L F`. -/
theorem entQ_badLaw_mulVec_lower (q : ℕ) (hq : 2 ≤ q) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 - 1 / q)
    (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F], Fintype.card F = q →
      ∀ s : ℕ, 1 ≤ s → ∀ A : Matrix (Fin s) (Fin L) F, LinearIndependent F A →
        (s : ℝ) * (qEntropy q p + qEntropy q p / ((L : ℝ) + δ')) ≤
          entQ q (badLaw q p L F) (fun ω => A.mulVec (badRow ω)) := by
  classical
  obtain ⟨L₀, hL₀⟩ := entQ_add_mul_ber_lower q hq p hp0 hp1 δ' hδ'
  refine ⟨L₀, fun L hL F _ _ _ hF s hs A hA => ?_⟩
  have hq1 : 1 < q := by omega
  have hp1' : p ≤ 1 - 1 / (q : ℝ) := hp1.le
  obtain ⟨S, B, hB, hBA⟩ := Matrix.exists_mul_eq_pivot A hA
  let b : Option (Fin L) → F → ℝ := fun o => ber q (o.elim (1 - 1 / (q : ℝ)) (fun _ => p))
  have hb : ∀ o, IsProb (b o) := by
    intro o
    have hinv : (0 : ℝ) ≤ 1 / q := by positivity
    cases o with
    | none => exact isProb_ber (t := 1 - 1 / (q : ℝ)) hq hF (hp0.le.trans hp1.le) (by linarith)
    | some j => exact isProb_ber (t := p) hq hF hp0.le (by linarith)
  have hμ : IsProb (badLaw q p L F) := isProb_prodLaw b hb
  have hβ := hL₀ L hL hF b hb
  let A' : Matrix (Fin s) (Fin L) F := B * A
  let e : Fin s → Option (Fin L) := fun r => some (S r)
  have he : Function.Injective e := fun r r' h => S.injective (Option.some_injective _ h)
  let V : Finset (Option (Fin L)) := Finset.univ.image e
  let Wf : Fin s → Option (Fin L) → F := fun r o => o.elim (∑ j, A' r j) (fun j => A' r j)
  let W : Option (Fin L) → Option (Fin L) → F := fun o o' =>
    if h : ∃ r, e r = o then Wf h.choose o' else 0
  have hW : ∀ r o', W (e r) o' = Wf r o' := by
    intro r o'
    have h : ∃ r', e r' = e r := ⟨r, rfl⟩
    simp only [W]
    split_ifs
    rw [he h.choose_spec]
  have hcardV : V.card = s := by rw [Finset.card_image_of_injective _ he]; simp
  have hsL : s ≤ L := by simpa using Fintype.card_le_of_embedding S
  have hid : ∀ (ω : Option (Fin L) → F) r,
      ω (e r) + ∑ a ∈ Vᶜ, Wf r a * ω a = A'.mulVec (badRow ω) r := by
    intro ω r
    have h1 : ∑ o, Wf r o * ω o = A'.mulVec (badRow ω) r := by
      rw [Fintype.sum_option]
      simp only [Wf, Option.elim, Matrix.mulVec, dotProduct, badRow, mul_add,
        Finset.sum_mul]
      rw [add_comm, ← Finset.sum_add_distrib]
    have h2 : ∑ o ∈ V, Wf r o * ω o = ω (e r) := by
      rw [Finset.sum_image (fun x _ y _ h => he h)]
      simp only [Wf, e, Option.elim, A', hBA, ite_mul, one_mul, zero_mul]
      simp
    rw [← h1, ← Finset.sum_add_sum_compl V, h2]
  have hcov : ∀ r ∈ V, ∃ a ∈ Vᶜ, W r a ≠ 0 := by
    intro o ho
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 ho
    by_contra hcon
    push Not at hcon
    have hnone : (none : Option (Fin L)) ∈ Vᶜ := by simp [V, e]
    have hc := hcon none hnone
    rw [hW] at hc
    have hj : ∀ j, A' r j = if j = S r then 1 else 0 := by
      intro j
      by_cases hj : ∃ r', S r' = j
      · obtain ⟨r', rfl⟩ := hj
        rw [show A' r (S r') = (B * A) r (S r') from rfl, hBA]
        by_cases h : r = r'
        · subst h; simp
        · simp [h, S.injective.ne (Ne.symm h)]
      · push Not at hj
        have hjc : (some j : Option (Fin L)) ∈ Vᶜ := by
          simp only [V, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists,
            e]
          exact fun r' h => hj r' (Option.some_injective _ h)
        have := hcon _ hjc
        rw [hW] at this
        simp only [Wf, Option.elim] at this
        rw [this]
        simp [show ¬ j = S r from fun h => hj r h.symm]
    simp only [Wf, Option.elim, hj, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    exact one_ne_zero hc
  have hE := block_entropy_lower hq hF p L
    (qEntropy q p + qEntropy q p / ((L : ℝ) + δ')) b hb hβ V Vᶜ disjoint_compl_right
    (by
      intro i hi
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hi
      rfl)
    (by
      intro a _
      cases a with
      | none => exact ⟨1 - 1 / (q : ℝ), hp1', le_rfl, rfl⟩
      | some j => exact ⟨p, le_rfl, hp1', rfl⟩)
    W V subset_rfl hcov (by rw [hcardV]; exact hsL)
  let Y : (Option (Fin L) → F) → (V → F) := fun ω r => ω r + ∑ a ∈ Vᶜ, W r a * ω a
  let f : (V → F) → (Fin s → F) := fun y r => y ⟨e r, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
  let g : (Fin s → F) → (V → F) := fun x v => if h : ∃ r, e r = (v : Option (Fin L)) then
    x h.choose else 0
  have hfg := entQ_eq_of_inverse hμ hq1 Y f g (by
    intro ω
    funext v
    obtain ⟨r, -, hr⟩ := Finset.mem_image.1 v.2
    have h : ∃ r', e r' = (v : Option (Fin L)) := ⟨r, hr⟩
    simp only [g, f]
    split_ifs
    congr 1
    exact Subtype.ext h.choose_spec)
  have hcomp : f ∘ Y = fun ω => A'.mulVec (badRow ω) := by
    funext ω r
    simp only [f, Y, Function.comp, hW]
    exact hid ω r
  rw [hcomp] at hfg
  have hX := entQ_eq_of_inverse hμ hq1 (fun ω => A.mulVec (badRow ω)) B.mulVec B⁻¹.mulVec (by
    intro ω
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec])
  have hcomp2 : B.mulVec ∘ (fun ω => A.mulVec (badRow ω)) = fun ω => A'.mulVec (badRow ω) := by
    funext ω
    simp [A', Matrix.mulVec_mulVec]
  rw [hcomp2] at hX
  rw [← hX, hfg, ← hcardV]
  exact hE

end CodingTheory.RandomLinearInternal
