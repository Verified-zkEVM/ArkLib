/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.ToMathlib.Combinatorics.SetFamily.GenericZeroPattern
public import ArkLib.ToMathlib.Finset.Basic
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
public import ArkLib.ToMathlib.MvPolynomial.Diagonal
public import ArkLib.ToMathlib.Polynomial.DegreeLT
public import ArkLib.ToMathlib.Polynomial.LinearIndependent
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomials with prescribed roots at independent indeterminates

Let `F` be a field and `a = (X j)_{j ∈ ι}` the indeterminates of `MvPolynomial ι F`. For a
multiset `v` on `ι` and `k > card v`, the polynomials `X ^ e * ∏_{j ∈ v} (X - C (X j))`,
`e < k - card v`, span the polynomials of degree `< k` that vanish at each `X j` to order
`count j v`. For a family `s : α → Multiset ι`, `Polynomial.vanishingFamily` collects these
polynomials for all `s i`.

We prove that this family is linearly independent over `MvPolynomial ι F` (equivalently over its
fraction field) whenever `s` is a generic multiplicity pattern of dimension `k` whose
multiplicities are at most one except at a single point. For sets of size `k - 1` this says that
the polynomials `∏_{j ∈ S ℓ} (X - C (X j))` attached to a generic zero pattern are linearly
independent; specialising the indeterminates gives distinct points `α j` in any infinite field and
`m` linearly independent polynomials of degree `< m` in which the `ℓ`-th one vanishes at
`α (S ℓ)`.

`Polynomial.linearIndependent_vanishingFamily` is [Lov18, Theorem 1.7] and
`Polynomial.linearIndependent_prod_X_sub_C_of_isGenericZeroPattern` is [Lov18, Conjecture 1.3];
`Polynomial.exists_embedding_linearIndependent_of_isGenericZeroPattern` specialises it to an
infinite field. Not proved here: [Lov18, Theorem 1.2] (finite fields
with `|F| ≥ n + k - 1`), [Lov18, Conjecture 1.5] (open in the source) and [Lov18, Corollary 1.8].
See `docs/kb/papers/Lov18.md`.

## Main definitions

* `Polynomial.vanishingFamily a k s`: the polynomials `X ^ e * ∏_{j ∈ s i} (X - C (a j))`,
  indexed by `i` and `e < k - card (s i)`.

## Main statements

* `Polynomial.linearIndependent_vanishingFamily`: linear independence over `MvPolynomial ι F`.
* `Polynomial.linearIndependent_vanishingFamily_fractionRing`: the same over the fraction field.
* `Polynomial.linearIndependent_prod_X_sub_C_of_isGenericZeroPattern`: the set version.
* `Polynomial.exists_embedding_linearIndependent_of_isGenericZeroPattern`: distinct points in an
  infinite field and `m` linearly independent polynomials of degree `< m` realising a generic zero
  pattern.

## References

* [Lovett, S., *MDS matrices over small fields: A proof of the GM-MDS conjecture*][Lov18]
-/

@[expose] public section

universe u

open Finset
open Multiset (IsGenericMultiplicityPattern CountLeOneExcept)

/-! ### The combinatorial steps of the induction -/

section CombinatorialSteps

variable {α ι : Type*} [DecidableEq ι] {k : ℕ} {s : α → Multiset ι}

/-- Multiplicities after merging the point `d` into the point `j`. -/
private theorem Multiset.count_map_update_id {d j : ι} (hjd : j ≠ d) (m : Multiset ι)
    (x : ι) :
    (m.map (Function.update id d j)).count x =
      (if x = d then 0 else m.count x) + (if x = j then m.count d else 0) := by
  have hmap : m.map (Function.update id d j) =
      Multiset.replicate (m.count d) j + m.filter (· ≠ d) := by
    conv_lhs => rw [← Multiset.filter_add_not (· = d) m]
    rw [Multiset.map_add, Multiset.filter_eq' m d, Multiset.map_replicate, Function.update_self]
    congr 1
    conv_rhs => rw [← Multiset.map_id' (m.filter (· ≠ d))]
    exact Multiset.map_congr rfl fun y hy => by
      simp [(Multiset.mem_filter.1 hy).2]
  rw [hmap, Multiset.count_add, Multiset.count_replicate, Multiset.count_filter]
  by_cases hxd : x = d
  · subst hxd
    simp [hjd, Ne.symm hjd]
  · by_cases hxj : x = j
    · subst hxj
      simp [hxd, add_comm]
    · simp [hxd, hxj, Ne.symm hxj]

namespace Multiset.IsGenericMultiplicityPattern

/-- Replacing a tight subfamily `I` by its infimum keeps a generic multiplicity pattern. -/
private theorem tight_merge (hs : IsGenericMultiplicityPattern k s) {d : ι}
    (hd : CountLeOneExcept d s) (I : Finset α) (hI : I.Nonempty)
    (htight : ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k) :
    IsGenericMultiplicityPattern k
        (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) ∧
      CountLeOneExcept d (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) := by
  classical
  obtain ⟨a, ha⟩ := id hI
  have hpos := Finset.single_le_sum (f := fun i => k - Multiset.card (s i))
    (fun i _ => Nat.zero_le _) ha
  have hka := hs.card_lt a
  refine ⟨⟨fun o => ?_, fun I' hI' => ?_⟩, fun o x hx => ?_⟩
  · cases o with
    | none => simp only [Option.elim]; omega
    | some i => exact hs.card_lt i
  · let J := I'.eraseNone
    let K := J.map (Function.Embedding.subtype fun i => i ∉ I)
    have hmemK : ∀ i, i ∈ K ↔ ∃ h : i ∉ I, some ⟨i, h⟩ ∈ I' := fun i => by
      simp [K, J]
    by_cases hn : none ∈ I'
    · have hdisj : Disjoint I K := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨h, -⟩ := (hmemK x).1 hx'
        exact h hx
      have hI'eq : I' = Finset.insertNone J := by
        rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hn]
      have hsum : ∑ o ∈ I', (k - Multiset.card (o.elim (I.inf' hI s) fun i => s i)) =
          ∑ i ∈ I ∪ K, (k - Multiset.card (s i)) := by
        rw [hI'eq, Finset.sum_insertNone, Finset.sum_union hdisj, Finset.sum_map]
        simp only [Option.elim, Function.Embedding.coe_subtype]
        omega
      have hcard : Multiset.card (I'.inf' hI' fun o => o.elim (I.inf' hI s) fun i => s i) ≤
          Multiset.card ((I ∪ K).inf' (hI.mono Finset.subset_union_left) s) := by
        refine Multiset.card_le_card (Finset.le_inf' _ _ fun i hi => ?_)
        rcases Finset.mem_union.1 hi with hi | hi
        · exact (Finset.inf'_le
            (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) hn).trans
            (Finset.inf'_le s hi)
        · obtain ⟨h, hsome⟩ := (hmemK i).1 hi
          exact Finset.inf'_le
            (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) hsome
      have := hs.sum_add_card_inf'_le (I ∪ K) (hI.mono Finset.subset_union_left)
      omega
    · have hI'eq : I' = J.map Function.Embedding.some := by
        rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hn]
      have hK : K.Nonempty := by
        obtain ⟨o, ho⟩ := hI'
        cases o with
        | none => exact absurd ho hn
        | some i => exact ⟨i.1, (hmemK i.1).2 ⟨i.2, ho⟩⟩
      have hsum : ∑ o ∈ I', (k - Multiset.card (o.elim (I.inf' hI s) fun i => s i)) =
          ∑ i ∈ K, (k - Multiset.card (s i)) := by
        rw [hI'eq, Finset.sum_map, Finset.sum_map]
        rfl
      have hcard : Multiset.card (I'.inf' hI' fun o => o.elim (I.inf' hI s) fun i => s i) ≤
          Multiset.card (K.inf' hK s) := by
        refine Multiset.card_le_card (Finset.le_inf' _ _ fun i hi => ?_)
        obtain ⟨h, hsome⟩ := (hmemK i).1 hi
        exact Finset.inf'_le
          (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) hsome
      have := hs.sum_add_card_inf'_le K hK
      omega
  · cases o with
    | none => exact (Multiset.count_le_of_le x (Finset.inf'_le s ha)).trans (hd a x hx)
    | some i => exact hd i x hx

/-- Merging the point `d` into a point `j` that `s i₀` avoids, when no proper subfamily with at
least two members is tight. -/
private theorem map_update [Fintype α] (hs : IsGenericMultiplicityPattern k s) {d : ι}
    (hd : CountLeOneExcept d s) {j : ι} (hjd : j ≠ d) {i₀ : α} (hdi₀ : d ∉ s i₀)
    (hji₀ : j ∉ s i₀)
    (hnt : ∀ (I : Finset α) (hI : I.Nonempty), 1 < #I → I ≠ univ →
      ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) ≠ k) :
    IsGenericMultiplicityPattern k (fun i => (s i).map (Function.update id d j)) ∧
      CountLeOneExcept j (fun i => (s i).map (Function.update id d j)) := by
  classical
  refine ⟨⟨fun i => by simpa using hs.card_lt i, fun I hI => ?_⟩, fun i x hx => ?_⟩
  · have hcount : ∀ i x, ((s i).map (Function.update id d j)).count x =
        (if x = d then 0 else (s i).count x) + (if x = j then (s i).count d else 0) :=
      fun i x => Multiset.count_map_update_id hjd (s i) x
    obtain ⟨a, ha⟩ := id hI
    have hpt : ∀ x, (I.inf' hI fun i => (s i).map (Function.update id d j)).count x ≤
        ((I.inf' hI s).map (Function.update id d j)).count x +
          (if x = j ∧ i₀ ∉ I then 1 else 0) := by
      intro x
      rw [Multiset.count_finset_inf', Multiset.count_map_update_id hjd,
        Multiset.count_finset_inf', Multiset.count_finset_inf']
      by_cases hxd : x = d
      · refine (Finset.inf'_le _ ha).trans ?_
        simp [hcount, hxd, hjd.symm]
      by_cases hxj : x = j
      · by_cases hi₀ : i₀ ∈ I
        · refine (Finset.inf'_le _ hi₀).trans ?_
          simp [hcount, hxj, Multiset.count_eq_zero.2 hji₀, Multiset.count_eq_zero.2 hdi₀]
        · obtain ⟨i₁, hi₁, heq⟩ := Finset.exists_mem_eq_inf' hI fun i => (s i).count d
          refine (Finset.inf'_le _ hi₁).trans ?_
          rw [hcount]
          simp only [hxj, hjd, ↓reduceIte, true_and, hi₀, not_false_eq_true]
          rw [heq]
          have := hd i₁ j hjd
          omega
      · simp only [hxd, hxj, false_and, ↓reduceIte, add_zero]
        exact le_of_eq (Finset.inf'_congr hI rfl fun i _ => by rw [hcount]; simp [hxd, hxj])
    have hle : (I.inf' hI fun i => (s i).map (Function.update id d j)) ≤
        (I.inf' hI s).map (Function.update id d j) + (if i₀ ∈ I then 0 else {j}) := by
      refine Multiset.le_iff_count.2 fun x => (hpt x).trans (le_of_eq ?_)
      rw [Multiset.count_add]
      congr 1
      by_cases hi₀ : i₀ ∈ I
      · simp [hi₀]
      · by_cases hxj : x = j <;> simp [hi₀, hxj]
    have key := Multiset.card_le_card hle
    rw [Multiset.card_add, Multiset.card_map] at key
    simp only [Multiset.card_map]
    have h := hs.sum_add_card_inf'_le I hI
    by_cases h1 : #I = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.sum_singleton, Finset.inf'_singleton, Multiset.card_map]
      have := hs.card_lt a
      omega
    by_cases hu : I = univ
    · have hi₀ : i₀ ∈ I := hu ▸ Finset.mem_univ _
      simp only [hi₀, ↓reduceIte, Multiset.card_zero, add_zero] at key
      omega
    · have := hnt I hI (by have := hI.card_pos; omega) hu
      split_ifs at key <;> simp at key <;> omega
  · rw [Multiset.count_map_update_id hjd]
    by_cases hxd : x = d
    · simp [hxd, hjd.symm]
    · simp only [hxd, hx, ↓reduceIte, add_zero]
      exact hd i x hxd

/-- Adding the point `d` to a multiset `s i₀` with at most `k - 2` elements. -/
private theorem update_cons [DecidableEq α] (hs : IsGenericMultiplicityPattern k s) {d : ι}
    (hd : CountLeOneExcept d s) {i₀ : α} (hlt : Multiset.card (s i₀) + 1 < k) :
    IsGenericMultiplicityPattern k (Function.update s i₀ (d ::ₘ s i₀)) ∧
      CountLeOneExcept d (Function.update s i₀ (d ::ₘ s i₀)) := by
  set t := Function.update s i₀ (d ::ₘ s i₀) with ht
  have hti₀ : t i₀ = d ::ₘ s i₀ := Function.update_self _ _ _
  have hti : ∀ i, i ≠ i₀ → t i = s i := fun i hi => Function.update_of_ne hi _ _
  have hle : ∀ i, t i ≤ d ::ₘ s i := fun i => by
    by_cases hi : i = i₀
    · rw [hi, hti₀]
    · rw [hti i hi]
      exact Multiset.le_cons_self _ _
  refine ⟨⟨fun i => ?_, fun I hI => ?_⟩, fun i x hx => ?_⟩
  · by_cases hi : i = i₀
    · rw [hi, hti₀, Multiset.card_cons]
      omega
    · rw [hti i hi]
      exact hs.card_lt i
  · have h := hs.sum_add_card_inf'_le I hI
    by_cases hI₀ : i₀ ∈ I
    · have he : ∑ i ∈ I.erase i₀, (k - Multiset.card (t i)) =
          ∑ i ∈ I.erase i₀, (k - Multiset.card (s i)) :=
        Finset.sum_congr rfl fun i hi => by rw [hti i (Finset.ne_of_mem_erase hi)]
      have hcomp := Finset.apply_inf'_eq_inf'_comp hI (f := s) (fun m => d ::ₘ m)
        fun a b => Multiset.cons_inter_distrib d a b
      have h1 : I.inf' hI t ≤ d ::ₘ I.inf' hI s := by
        rw [hcomp]
        exact Finset.le_inf' _ _ fun i hi => (Finset.inf'_le _ hi).trans (hle i)
      have hc := Multiset.card_le_card h1
      rw [Multiset.card_cons] at hc
      rw [← Finset.add_sum_erase I _ hI₀, he, hti₀, Multiset.card_cons]
      rw [← Finset.add_sum_erase I _ hI₀] at h
      omega
    · have hsum : ∑ i ∈ I, (k - Multiset.card (t i)) = ∑ i ∈ I, (k - Multiset.card (s i)) :=
        Finset.sum_congr rfl fun i hi => by rw [hti i (fun h => hI₀ (h ▸ hi))]
      have hinf : I.inf' hI t = I.inf' hI s :=
        Finset.inf'_congr hI rfl fun i hi => hti i (fun h => hI₀ (h ▸ hi))
      rw [hsum, hinf]
      exact h
  · by_cases hi : i = i₀
    · rw [hi, hti₀, Multiset.count_cons_of_ne hx]
      exact hd i₀ x hx
    · rw [hti i hi]
      exact hd i x hx

/-- If `s i₀` contains every point other than `d` that occurs in the family, then every other
multiset contains `d`. -/
private theorem mem_of_forall_not_mem (hs : IsGenericMultiplicityPattern k s) {d : ι}
    (hd : CountLeOneExcept d s) {i₀ : α}
    (hcov : ∀ j, j ≠ d → j ∉ s i₀ → ∀ i, j ∉ s i) :
    ∀ i, i ≠ i₀ → d ∈ s i := by
  intro i hi
  by_contra hdi
  refine hs.not_le hi (Multiset.le_iff_count.2 fun x => ?_)
  by_cases hxd : x = d
  · rw [hxd, Multiset.count_eq_zero.2 hdi]
    exact Nat.zero_le _
  by_cases hxi : x ∈ s i
  · have hx0 : x ∈ s i₀ := by
      by_contra h
      exact hcov x hxd h i hxi
    exact (hd i x hxd).trans (Multiset.one_le_count_iff_mem.2 hx0)
  · rw [Multiset.count_eq_zero.2 hxi]
    exact Nat.zero_le _

end Multiset.IsGenericMultiplicityPattern

end CombinatorialSteps

namespace Polynomial

variable {R : Type*} [CommRing R] {ι α β : Type*}

/-! ### The polynomial family -/

/-- For multisets `s i` on `ι` and points `a : ι → R`, the polynomials
`X ^ e * ∏_{j ∈ s i} (X - C (a j))` with `e < k - card (s i)`. -/
noncomputable def vanishingFamily (a : ι → R) (k : ℕ) (s : α → Multiset ι) :
    (Σ i : α, Fin (k - Multiset.card (s i))) → R[X] :=
  fun p => X ^ (p.2 : ℕ) * ((s p.1).map fun j => X - C (a j)).prod

/-- Reindexing between two families on the same index type whose blocks have equal sizes. -/
private def blockEquiv {k k' : ℕ} {s t : α → Multiset ι}
    (h : ∀ i, k - Multiset.card (s i) = k' - Multiset.card (t i)) :
    (Σ i, Fin (k - Multiset.card (s i))) ≃ Σ i, Fin (k' - Multiset.card (t i)) :=
  Equiv.sigmaCongrRight fun i => finCongr (h i)

@[simp] private theorem blockEquiv_fst {k k' : ℕ} {s t : α → Multiset ι}
    (h : ∀ i, k - Multiset.card (s i) = k' - Multiset.card (t i))
    (p : Σ i, Fin (k - Multiset.card (s i))) : (blockEquiv h p).1 = p.1 := rfl

@[simp] private theorem blockEquiv_snd_val {k k' : ℕ} {s t : α → Multiset ι}
    (h : ∀ i, k - Multiset.card (s i) = k' - Multiset.card (t i))
    (p : Σ i, Fin (k - Multiset.card (s i))) : ((blockEquiv h p).2 : ℕ) = p.2 := rfl

private theorem map_vanishingFamily {S : Type*} [CommRing S] (φ : R →+* S) (a : ι → R) (k : ℕ)
    (s : α → Multiset ι) (p : Σ i : α, Fin (k - Multiset.card (s i))) :
    (vanishingFamily a k s p).map φ = vanishingFamily (φ ∘ a) k s p := by
  simp [vanishingFamily, Polynomial.map_multiset_prod, Multiset.map_map]

private theorem linearIndependent_vanishingFamily_iff [IsDomain R] (a : ι → R) (k : ℕ)
    (s : α → Multiset ι) :
    LinearIndependent R (vanishingFamily a k s) ↔
      LinearIndependent (FractionRing R)
        (vanishingFamily (algebraMap R (FractionRing R) ∘ a) k s) := by
  rw [← linearIndependent_map_algebraMap_iff (K := FractionRing R)]
  simp only [map_vanishingFamily]

private theorem monic_vanishingProd (a : ι → R) (m : Multiset ι) :
    ((m.map fun j => X - C (a j)).prod).Monic :=
  monic_multiset_prod_of_monic _ _ fun j _ => monic_X_sub_C (a j)

private theorem natDegree_vanishingProd [Nontrivial R] (a : ι → R) (m : Multiset ι) :
    ((m.map fun j => X - C (a j)).prod).natDegree = Multiset.card m := by
  have : (m.map fun j => X - C (a j)) = (m.map a).map fun r => X - C r := by
    rw [Multiset.map_map]
    rfl
  rw [this, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

private theorem linearIndependent_X_pow_comp {γ : Type*} {f : γ → ℕ}
    (hf : Function.Injective f) : LinearIndependent R fun g => (X ^ f g : R[X]) := by
  have := (Polynomial.basisMonomials R).linearIndependent.comp _ hf
  simpa [Function.comp_def, Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial]
    using this

private theorem eval_vanishingProd_ne_zero [IsDomain R] {a : ι → R} (ha : Function.Injective a)
    {d : ι} {m : Multiset ι} (hd : d ∉ m) : ((m.map fun j => X - C (a j)).prod).eval (a d) ≠ 0 := by
  simp only [eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C]
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨j, hj, hj0⟩ := Multiset.mem_map.1 h0
  exact hd (ha (sub_eq_zero.1 hj0) ▸ hj)

private theorem sum_update_cons [Fintype α] [DecidableEq α] {k : ℕ} {s : α → Multiset ι}
    {d : ι} {i₀ : α} (hlt : Multiset.card (s i₀) < k) :
    ∑ i, (k - Multiset.card (Function.update s i₀ (d ::ₘ s i₀) i)) + 1 =
      ∑ i, (k - Multiset.card (s i)) := by
  have he : ∑ i ∈ univ.erase i₀, (k - Multiset.card (Function.update s i₀ (d ::ₘ s i₀) i)) =
      ∑ i ∈ univ.erase i₀, (k - Multiset.card (s i)) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase univ (fun i => k - Multiset.card (s i)) (Finset.mem_univ i₀), he,
    Function.update_self, Multiset.card_cons]
  omega

private theorem sum_compl_tight [Fintype α] [DecidableEq α] [DecidableEq ι] {k : ℕ}
    {s : α → Multiset ι} (I : Finset α) (hI : I.Nonempty)
    (htight : ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k) :
    (k - Multiset.card (I.inf' hI s)) + ∑ i : {i // i ∉ I}, (k - Multiset.card (s i)) =
      ∑ i, (k - Multiset.card (s i)) := by
  rw [← Finset.sum_compl_add_sum I,
    Finset.sum_subtype Iᶜ (fun x => Finset.mem_compl) (fun i => k - Multiset.card (s i))]
  omega

/-- A family with at most one multiset is linearly independent: its members have distinct
degrees. -/
private theorem linearIndependent_vanishingFamily_of_subsingleton [IsDomain R] [Subsingleton α]
    (a : ι → R) (k : ℕ) (s : α → Multiset ι) : LinearIndependent R (vanishingFamily a k s) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨i₀⟩⟩
  · exact linearIndependent_empty_type
  have hinj : Function.Injective fun p : (Σ i : α, Fin (k - Multiset.card (s i))) =>
      (p.2 : ℕ) := by
    rintro ⟨i, e⟩ ⟨i', e'⟩ h
    obtain rfl := Subsingleton.elim i i'
    exact Sigma.ext rfl (heq_of_eq (Fin.ext h))
  have hX := linearIndependent_X_pow_comp (R := R) hinj
  have hP := (monic_vanishingProd a (s i₀)).ne_zero
  have := hX.map' (LinearMap.mulRight R ((s i₀).map fun j => X - C (a j)).prod)
    (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hP))
  convert this using 1
  funext p
  simp [vanishingFamily, Subsingleton.elim p.1 i₀]

/-- For sets of size `m - 1`, the family in dimension `m` is the family of products
`∏_{j ∈ S ℓ} (X - C (a j))`. -/
private theorem linearIndependent_prod_of_vanishingFamily {m : ℕ} (a : ι → R)
    {S : Fin m → Finset ι} (hcard : ∀ ℓ, #(S ℓ) + 1 = m)
    (h : LinearIndependent R (vanishingFamily a m fun ℓ => (S ℓ).val)) :
    LinearIndependent R fun ℓ => ∏ j ∈ S ℓ, (X - C (a j)) := by
  let e : Fin m → Σ ℓ : Fin m, Fin (m - Multiset.card (S ℓ).val) :=
    fun ℓ => ⟨ℓ, ⟨0, by have := hcard ℓ; rw [Finset.card_val]; omega⟩⟩
  have he : Function.Injective e := fun ℓ ℓ' h => (Sigma.mk.inj h).1
  convert h.comp e he using 1
  funext ℓ
  simp only [Function.comp_apply, vanishingFamily, e, pow_zero, one_mul]
  rfl

section Steps

variable [IsDomain R] {k : ℕ} {s : α → Multiset ι}

/-- Common root: the family for `s` is `X - C (a j)` times the family for `s` with `j` removed,
in dimension `k - 1`. -/
private theorem linearIndependent_vanishingFamily_of_erase [DecidableEq ι] (a : ι → R) {j : ι}
    (hj : ∀ i, j ∈ s i)
    (h : LinearIndependent R (vanishingFamily a (k - 1) fun i => (s i).erase j)) :
    LinearIndependent R (vanishingFamily a k s) := by
  have hc : ∀ i, k - 1 - Multiset.card ((s i).erase j) = k - Multiset.card (s i) := fun i => by
    rw [Multiset.card_erase_of_mem (hj i), Nat.pred_eq_sub_one]
    have := Multiset.card_pos_iff_exists_mem.2 ⟨j, hj i⟩
    omega
  have hmul := h.map' (LinearMap.mulLeft R (X - C (a j)))
    (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (X_sub_C_ne_zero (a j))))
  refine (linearIndependent_equiv' (blockEquiv hc) ?_).1 hmul
  funext p
  simp only [Function.comp_apply, vanishingFamily, blockEquiv_fst, blockEquiv_snd_val,
    LinearMap.mulLeft_apply]
  rw [← Multiset.prod_map_erase (hj p.1)]
  ring

/-- Over a field: if `I` is tight, the family for `s` spans the same space as the family in which
the members of `I` are replaced by their infimum. -/
private theorem linearIndependent_vanishingFamily_of_tight_field {K : Type*} [Field K]
    [Finite α] [DecidableEq ι] (b : ι → K) (I : Finset α) (hI : I.Nonempty)
    (htight : ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k)
    (h₁ : LinearIndependent K
      (vanishingFamily b k fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i))
    (h₂ : LinearIndependent K (vanishingFamily b k fun i : I => s i)) :
    LinearIndependent K (vanishingFamily b k s) := by
  classical
  have := Fintype.ofFinite α
  let P : Multiset ι → K[X] := fun m => (m.map fun j => X - C (b j)).prod
  let v := I.inf' hI s
  let n := k - Multiset.card v
  let w : Fin n → K[X] := fun e => X ^ (e : ℕ) * P v
  have hw : LinearIndependent K w :=
    (linearIndependent_X_pow_comp (R := K) Fin.val_injective).map' (LinearMap.mulRight K (P v))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (monic_vanishingProd b v).ne_zero))
  have hmemW : ∀ H : K[X], H.natDegree < n → P v * H ∈ Submodule.span K (Set.range w) := by
    intro H hH
    rw [as_sum_range' H n hH, Finset.mul_sum, Finset.sum_range]
    refine Submodule.sum_mem _ fun e _ => ?_
    have he : P v * monomial (e : ℕ) (H.coeff e) = H.coeff e • w e := by
      simp only [w, ← C_mul_X_pow_eq_monomial, smul_eq_C_mul]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  have hF : Submodule.span K (Set.range (vanishingFamily b k fun i : I => s i)) ≤
      Submodule.span K (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, e⟩, rfl⟩
    have hvi : v ≤ s i := Finset.inf'_le s i.2
    have hsplit : P (s i) = P v * P (s i - v) := by
      conv_lhs => rw [← add_tsub_cancel_of_le hvi]
      simp [P, Multiset.map_add, Multiset.prod_add]
    have hdeg : (X ^ (e : ℕ) * P (s i - v)).natDegree < n := by
      change (X ^ (e : ℕ) * ((s i - v).map fun j => X - C (b j)).prod).natDegree < n
      rw [(monic_X_pow _).natDegree_mul (monic_vanishingProd b _), natDegree_X_pow,
        natDegree_vanishingProd, Multiset.card_sub hvi]
      have := e.isLt
      have := Multiset.card_le_card hvi
      omega
    have hval : X ^ (e : ℕ) * P (s i) = P v * (X ^ (e : ℕ) * P (s i - v)) := by
      rw [hsplit]
      ring
    change X ^ (e : ℕ) * P (s i) ∈ _
    rw [hval]
    exact hmemW _ hdeg
  have hcardF : Fintype.card (Σ i : I, Fin (k - Multiset.card (s i))) = n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Finset.sum_coe_sort I fun i => k - Multiset.card (s i)]
    simp only [n, v]
    omega
  have : FiniteDimensional K (Submodule.span K (Set.range w)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range w)
  have heqW : Submodule.span K (Set.range (vanishingFamily b k fun i : I => s i)) =
      Submodule.span K (Set.range w) :=
    Submodule.eq_of_le_of_finrank_eq hF (by
      rw [finrank_span_eq_card h₂, finrank_span_eq_card hw, hcardF, Fintype.card_fin])
  have hsub : Set.range (vanishingFamily b k fun i : I => s i) ⊆
      Set.range (vanishingFamily b k s) := by
    rintro _ ⟨⟨i, e⟩, rfl⟩
    exact ⟨⟨i.1, e⟩, rfl⟩
  refine linearIndependent_of_span_le_of_card_le h₁ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨⟨o, e⟩, rfl⟩
    cases o with
    | none =>
      have hmem : w e ∈ Submodule.span K (Set.range w) := Submodule.subset_span ⟨e, rfl⟩
      rw [← heqW] at hmem
      exact Submodule.span_mono hsub hmem
    | some i => exact Submodule.subset_span ⟨⟨i.1, e⟩, rfl⟩
  · have hc1 : Fintype.card (Σ i : α, Fin (k - Multiset.card (s i))) =
        ∑ i, (k - Multiset.card (s i)) := by simp
    have hc2 : Fintype.card (Σ o : Option {i // i ∉ I},
        Fin (k - Multiset.card (o.elim (I.inf' hI s) fun i => s i))) =
        (k - Multiset.card (I.inf' hI s)) + ∑ i : {i // i ∉ I}, (k - Multiset.card (s i)) := by
      simp [Fintype.sum_option]
    rw [hc1, hc2, sum_compl_tight I hI htight]

/-- Tight subfamily: if `I` is tight, the family for `s` spans the same space as the family in
which the members of `I` are replaced by their infimum. -/
private theorem linearIndependent_vanishingFamily_of_tight [Finite α] [DecidableEq ι]
    (a : ι → R) (I : Finset α) (hI : I.Nonempty)
    (htight : ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k)
    (h₁ : LinearIndependent R
      (vanishingFamily a k fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i))
    (h₂ : LinearIndependent R (vanishingFamily a k fun i : I => s i)) :
    LinearIndependent R (vanishingFamily a k s) := by
  rw [linearIndependent_vanishingFamily_iff] at h₁ h₂ ⊢
  exact linearIndependent_vanishingFamily_of_tight_field _ I hI htight h₁ h₂

/-- Over a field and for finitely many multisets: adding a root `d` to the one member `s i₀` that
avoids it. -/
private theorem linearIndependent_vanishingFamily_of_update_cons_field {K : Type*} [Field K]
    [Finite α] [DecidableEq α] {b : ι → K} (hb : Function.Injective b) {d : ι} {i₀ : α}
    (hdi₀ : d ∉ s i₀) (hmem : ∀ i, i ≠ i₀ → d ∈ s i) (hlt : Multiset.card (s i₀) + 1 < k)
    (h : LinearIndependent K (vanishingFamily b k (Function.update s i₀ (d ::ₘ s i₀)))) :
    LinearIndependent K (vanishingFamily b k s) := by
  have := Fintype.ofFinite α
  set t := Function.update s i₀ (d ::ₘ s i₀) with ht
  let P : Multiset ι → K[X] := fun m => (m.map fun j => X - C (b j)).prod
  have hti : ∀ i, d ∈ t i := fun i => by
    by_cases hi : i = i₀
    · rw [hi, ht, Function.update_self]
      exact Multiset.mem_cons_self _ _
    · rw [ht, Function.update_of_ne hi]
      exact hmem i hi
  have hdvd : ∀ p, X - C (b d) ∣ vanishingFamily b k t p := by
    rintro ⟨i, e⟩
    change X - C (b d) ∣ X ^ (e : ℕ) * ((t i).map fun j => X - C (b j)).prod
    exact dvd_mul_of_dvd_right (Multiset.dvd_prod (Multiset.mem_map.2 ⟨d, hti i, rfl⟩)) _
  have hP : (P (s i₀)).eval (b d) ≠ 0 := eval_vanishingProd_ne_zero hb hdi₀
  have h' := linearIndependent_option_of_dvd h hdvd hP
  refine linearIndependent_of_span_le_of_card_le h' ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    have h0 : 0 < k - Multiset.card (s i₀) := by omega
    cases o with
    | none =>
      refine Submodule.subset_span ⟨⟨i₀, ⟨0, h0⟩⟩, ?_⟩
      simp [vanishingFamily, P]
    | some p =>
      obtain ⟨i, e⟩ := p
      by_cases hi : i = i₀
      · subst hi
        have ht0 : t i = d ::ₘ s i := by simp [ht]
        have he1 := e.isLt
        have he2 : Multiset.card (t i) = Multiset.card (s i) + 1 := by
          rw [ht0, Multiset.card_cons]
        have hval : vanishingFamily b k t ⟨i, e⟩ =
            vanishingFamily b k s ⟨i, ⟨e + 1, by omega⟩⟩ -
              C (b d) * vanishingFamily b k s ⟨i, ⟨e, by omega⟩⟩ := by
          simp only [vanishingFamily]
          simp only [ht0, Multiset.map_cons, Multiset.prod_cons]
          ring
        simp only [Option.elim]
        rw [hval, ← smul_eq_C_mul]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      · have hti' : t i = s i := by rw [ht, Function.update_of_ne hi]
        have he1 := e.isLt
        have he2 : Multiset.card (t i) = Multiset.card (s i) := by rw [hti']
        refine Submodule.subset_span ⟨⟨i, ⟨e, by omega⟩⟩, ?_⟩
        simp only [Option.elim, vanishingFamily]
        simp only [hti']
  · simp only [Fintype.card_option, Fintype.card_sigma, Fintype.card_fin]
    have := sum_update_cons (d := d) (show Multiset.card (s i₀) < k by omega)
    rw [ht]
    omega

/-- Adding a root `d` to the one member `s i₀` that avoids it. -/
private theorem linearIndependent_vanishingFamily_of_update_cons [Finite α] [DecidableEq α]
    {a : ι → R} (ha : Function.Injective a) {d : ι} {i₀ : α} (hdi₀ : d ∉ s i₀)
    (hmem : ∀ i, i ≠ i₀ → d ∈ s i) (hlt : Multiset.card (s i₀) + 1 < k)
    (h : LinearIndependent R (vanishingFamily a k (Function.update s i₀ (d ::ₘ s i₀)))) :
    LinearIndependent R (vanishingFamily a k s) := by
  rw [linearIndependent_vanishingFamily_iff] at h ⊢
  exact linearIndependent_vanishingFamily_of_update_cons_field
    ((IsFractionRing.injective R (FractionRing R)).comp ha) hdi₀ hmem hlt h

/-- Removing the one member `s i₀` that avoids `d`, when it contributes a single polynomial. -/
private theorem linearIndependent_vanishingFamily_of_ne {a : ι → R} (ha : Function.Injective a)
    {d : ι} {i₀ : α} (hdi₀ : d ∉ s i₀) (hmem : ∀ i, i ≠ i₀ → d ∈ s i)
    (heq : Multiset.card (s i₀) + 1 = k)
    (h : LinearIndependent R (vanishingFamily a k fun i : {i // i ≠ i₀} => s i)) :
    LinearIndependent R (vanishingFamily a k s) := by
  classical
  have hdvd : ∀ p, X - C (a d) ∣ vanishingFamily a k (fun i : {i // i ≠ i₀} => s i) p := by
    rintro ⟨i, e⟩
    exact dvd_mul_of_dvd_right (Multiset.dvd_prod (Multiset.mem_map.2 ⟨d, hmem i i.2, rfl⟩)) _
  have h' := linearIndependent_option_of_dvd h hdvd (eval_vanishingProd_ne_zero ha hdi₀)
  let e : (Σ i : α, Fin (k - Multiset.card (s i))) →
      Option (Σ i : {i // i ≠ i₀}, Fin (k - Multiset.card (s i))) :=
    fun p => if hp : p.1 = i₀ then none else some ⟨⟨p.1, hp⟩, p.2⟩
  have h0 : ∀ y : Fin (k - Multiset.card (s i₀)), (y : ℕ) = 0 := fun y => by
    have := y.isLt
    omega
  have he : Function.Injective e := by
    rintro ⟨i, x⟩ ⟨i', x'⟩ hp
    by_cases hi : i = i₀ <;> by_cases hi' : i' = i₀
    · subst hi hi'
      exact Sigma.ext rfl (heq_of_eq (Fin.ext ((h0 x).trans (h0 x').symm)))
    · simp [e, hi, hi'] at hp
    · simp [e, hi, hi'] at hp
    · simp only [e, hi, hi', dite_false, Option.some.injEq, Sigma.mk.injEq,
        Subtype.mk.injEq] at hp
      obtain ⟨rfl, hxx'⟩ := hp
      exact Sigma.ext rfl hxx'
  convert h'.comp e he using 1
  funext ⟨i, x⟩
  by_cases hi : i = i₀
  · subst hi
    simp [e, vanishingFamily, h0 x]
  · simp [e, hi, vanishingFamily]

end Steps

/-! ### The size decreasing along the induction -/

section Size

variable [DecidableEq ι]

/-- The quantity that decreases along the induction: the number of points of `ι` that occur in
some `s i` or equal `d`, plus `k`, plus the number of multisets, plus the total number
`∑ i, (k - card (s i))` of polynomials. -/
private def multiplicityPatternSize [Fintype α] (k : ℕ) (s : α → Multiset ι) (d : ι) : ℕ :=
  #(insert d (univ.biUnion fun i => (s i).toFinset)) + k + Fintype.card α +
    ∑ i, (k - Multiset.card (s i))

/-- The points of a family `t` lie among `d` and the points of `s`. -/
private theorem card_insert_biUnion_le [Fintype α] [Fintype β] {s : α → Multiset ι}
    {t : β → Multiset ι} {d d' : ι} (hd' : d' = d ∨ ∃ i, d' ∈ s i)
    (h : ∀ b x, x ∈ t b → x = d ∨ ∃ i, x ∈ s i) :
    #(insert d' (univ.biUnion fun b => (t b).toFinset)) ≤
      #(insert d (univ.biUnion fun i => (s i).toFinset)) := by
  refine Finset.card_le_card (Finset.insert_subset_iff.2 ⟨?_, fun x hx => ?_⟩)
  · rcases hd' with rfl | ⟨i, hi⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Multiset.mem_toFinset.2 hi⟩)
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 hx
    rcases h b x (Multiset.mem_toFinset.1 hb) with rfl | ⟨i, hi⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
        Multiset.mem_toFinset.2 hi⟩)

variable [Fintype α] {k : ℕ} {s : α → Multiset ι} {d : ι}

/-- Removing a common point and lowering the dimension decreases the size. -/
private theorem multiplicityPatternSize_erase_lt [Nonempty α] {j : ι}
    (hk : ∀ i, Multiset.card (s i) < k) (hj : ∀ i, j ∈ s i) :
    multiplicityPatternSize (k - 1) (fun i => (s i).erase j) d <
      multiplicityPatternSize k s d := by
  unfold multiplicityPatternSize
  beta_reduce
  obtain ⟨i₀⟩ := ‹Nonempty α›
  have hU := card_insert_biUnion_le (s := s) (t := fun i => (s i).erase j) (d := d) (Or.inl rfl)
    fun b x hx => Or.inr ⟨b, Multiset.mem_of_mem_erase hx⟩
  have hsum : ∑ i, (k - 1 - Multiset.card ((s i).erase j)) = ∑ i, (k - Multiset.card (s i)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [Multiset.card_erase_of_mem (hj i), Nat.pred_eq_sub_one]
      have := Multiset.card_pos_iff_exists_mem.2 ⟨j, hj i⟩
      omega
  have := hk i₀
  omega

/-- Passing to a proper subfamily decreases the size. -/
private theorem multiplicityPatternSize_comp_lt [Fintype β] (e : β → α)
    (he : Function.Injective e) (hne : ¬ Function.Surjective e) :
    multiplicityPatternSize k (s ∘ e) d < multiplicityPatternSize k s d := by
  unfold multiplicityPatternSize
  have hU := card_insert_biUnion_le (s := s) (t := s ∘ e) (d := d) (Or.inl rfl)
    fun b x hx => Or.inr ⟨e b, hx⟩
  have hcard := Fintype.card_lt_of_injective_not_surjective e he hne
  have hsum : ∑ b, (k - Multiset.card ((s ∘ e) b)) ≤ ∑ i, (k - Multiset.card (s i)) := by
    have : ∑ b, (k - Multiset.card ((s ∘ e) b)) =
        ∑ i ∈ univ.map ⟨e, he⟩, (k - Multiset.card (s i)) := by
      rw [Finset.sum_map]
      rfl
    rw [this]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- Replacing a tight subfamily with at least two members by its infimum decreases the size. -/
private theorem multiplicityPatternSize_tight_merge_lt [DecidableEq α] (I : Finset α)
    (hI : I.Nonempty) (h1 : 1 < #I)
    (htight : ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k) :
    multiplicityPatternSize k
        (fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) d <
      multiplicityPatternSize k s d := by
  unfold multiplicityPatternSize
  beta_reduce
  obtain ⟨a, ha⟩ := id hI
  have hU := card_insert_biUnion_le (s := s)
    (t := fun o : Option {i // i ∉ I} => o.elim (I.inf' hI s) fun i => s i) (d := d)
    (Or.inl rfl) fun b x hx => by
      cases b with
      | none => exact Or.inr ⟨a, Multiset.mem_of_le (Finset.inf'_le s ha) hx⟩
      | some i => exact Or.inr ⟨i, hx⟩
  have hcard : Fintype.card (Option {i // i ∉ I}) + #I = Fintype.card α + 1 := by
    rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe]
    have := Finset.card_le_univ I
    omega
  have hsum : ∑ o : Option {i // i ∉ I}, (k - Multiset.card
      (o.elim (I.inf' hI s) fun i => s i)) = ∑ i, (k - Multiset.card (s i)) := by
    rw [Fintype.sum_option]
    exact sum_compl_tight I hI htight
  omega

/-- Merging `d` into a point `j ≠ d` that occurs in the family decreases the size. -/
private theorem multiplicityPatternSize_map_update_lt {j : ι} (hjd : j ≠ d) {i₁ : α}
    (hj : j ∈ s i₁) :
    multiplicityPatternSize k (fun i => (s i).map (Function.update id d j)) j <
      multiplicityPatternSize k s d := by
  unfold multiplicityPatternSize
  beta_reduce
  have hsub : insert j (univ.biUnion fun i => ((s i).map (Function.update id d j)).toFinset) ⊆
      (insert d (univ.biUnion fun i => (s i).toFinset)).erase d := by
    intro x hx
    rw [Finset.mem_erase]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨hjd, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i₁, Finset.mem_univ _,
        Multiset.mem_toFinset.2 hj⟩)⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hi)
      by_cases hyd : y = d
      · rw [hyd, Function.update_self]
        exact ⟨hjd, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i₁, Finset.mem_univ _,
          Multiset.mem_toFinset.2 hj⟩)⟩
      · rw [Function.update_of_ne hyd]
        exact ⟨hyd, Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
          Multiset.mem_toFinset.2 hy⟩)⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_erase_lt_of_mem (Finset.mem_insert_self d
    (univ.biUnion fun i => (s i).toFinset))
  simp only [Multiset.card_map]
  omega

/-- Adding `d` to one multiset of fewer than `k` elements decreases the size. -/
private theorem multiplicityPatternSize_update_cons_lt [DecidableEq α] {i₀ : α}
    (hlt : Multiset.card (s i₀) < k) :
    multiplicityPatternSize k (Function.update s i₀ (d ::ₘ s i₀)) d <
      multiplicityPatternSize k s d := by
  unfold multiplicityPatternSize
  have hU := card_insert_biUnion_le (s := s) (t := Function.update s i₀ (d ::ₘ s i₀)) (d := d)
    (Or.inl rfl) fun b x hx => by
      by_cases hb : b = i₀
      · rw [hb, Function.update_self, Multiset.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr ⟨i₀, hx⟩
      · rw [Function.update_of_ne hb] at hx
        exact Or.inr ⟨b, hx⟩
  have := sum_update_cons (d := d) hlt
  omega

end Size

section Main

variable {F : Type*} [Field F] [DecidableEq ι]

/-- Merging the indeterminate `X d` into `X j`: independence after the substitution implies
independence before it. -/
private theorem linearIndependent_vanishingFamily_of_map_update {k : ℕ} {s : α → Multiset ι}
    {d j : ι}
    (h : LinearIndependent (MvPolynomial ι F)
      (vanishingFamily (MvPolynomial.X (R := F)) k fun i => (s i).map (Function.update id d j))) :
    LinearIndependent (MvPolynomial ι F) (vanishingFamily (MvPolynomial.X (R := F)) k s) := by
  let φ : MvPolynomial ι F →+* MvPolynomial ι F :=
    (MvPolynomial.rename (Function.update id d j)).toRingHom
  have hc : ∀ i, k - Multiset.card ((s i).map (Function.update id d j)) =
      k - Multiset.card (s i) := fun i => by rw [Multiset.card_map]
  refine linearIndependent_of_linearIndependent_map φ (MvPolynomial.not_isUnit_X_sub_X d j)
    (fun r hr => MvPolynomial.X_sub_X_dvd_of_rename_update_eq_zero hr) ?_
  refine (linearIndependent_equiv' (blockEquiv hc) ?_).1 h
  funext p
  rw [Function.comp_apply, map_vanishingFamily]
  simp only [vanishingFamily, blockEquiv_fst, blockEquiv_snd_val, Multiset.map_map,
    Function.comp_def]
  congr 2
  refine Multiset.map_congr rfl fun x _ => ?_
  simp [φ]

/-- The induction step: linear independence for `s` from linear independence for every generic
multiplicity pattern of smaller size. -/
private theorem linearIndependent_vanishingFamily_of_forall_size_lt {α : Type u} [Fintype α] {k : ℕ}
    {s : α → Multiset ι} {d : ι}
    (ih : ∀ (β : Type u) [Fintype β] [DecidableEq β] (k' : ℕ) (t : β → Multiset ι) (d' : ι),
      IsGenericMultiplicityPattern k' t → CountLeOneExcept d' t →
      multiplicityPatternSize k' t d' < multiplicityPatternSize k s d →
      LinearIndependent (MvPolynomial ι F) (vanishingFamily (MvPolynomial.X (R := F)) k' t))
    (hs : IsGenericMultiplicityPattern k s) (hd : CountLeOneExcept d s) :
    LinearIndependent (MvPolynomial ι F) (vanishingFamily (MvPolynomial.X (R := F)) k s) := by
  classical
  by_cases hsub : Subsingleton α
  · exact linearIndependent_vanishingFamily_of_subsingleton _ _ _
  have : Nontrivial α := not_subsingleton_iff_nontrivial.1 hsub
  by_cases hcommon : ∃ j, ∀ i, j ∈ s i
  · obtain ⟨j, hj⟩ := hcommon
    obtain ⟨hs', hd'⟩ := hs.erase hd j hj
    exact linearIndependent_vanishingFamily_of_erase _ hj
      (ih α _ _ d hs' hd' (multiplicityPatternSize_erase_lt hs.card_lt hj))
  push Not at hcommon
  by_cases htight : ∃ (I : Finset α) (hI : I.Nonempty), 1 < #I ∧ I ≠ univ ∧
      ∑ i ∈ I, (k - Multiset.card (s i)) + Multiset.card (I.inf' hI s) = k
  · obtain ⟨I, hI, h1, hne, ht⟩ := htight
    obtain ⟨hs', hd'⟩ := hs.tight_merge hd I hI ht
    have hns : ¬ Function.Surjective (Subtype.val : I → α) := fun h =>
      hne (eq_univ_of_forall fun a => by obtain ⟨x, rfl⟩ := h a; exact x.2)
    exact linearIndependent_vanishingFamily_of_tight _ I hI ht
      (ih _ _ _ d hs' hd' (multiplicityPatternSize_tight_merge_lt I hI h1 ht))
      (ih I _ _ d (hs.comp _ Subtype.val_injective) (hd.comp _)
        (multiplicityPatternSize_comp_lt _ Subtype.val_injective hns))
  push Not at htight
  obtain ⟨i₀, hi₀⟩ := hcommon d
  by_cases hmerge : ∃ j, j ≠ d ∧ j ∉ s i₀ ∧ ∃ i, j ∈ s i
  · obtain ⟨j, hjd, hj₀, i₁, hj₁⟩ := hmerge
    obtain ⟨hs', hd'⟩ := hs.map_update hd hjd hi₀ hj₀ htight
    exact linearIndependent_vanishingFamily_of_map_update
      (ih α _ _ j hs' hd' (multiplicityPatternSize_map_update_lt hjd hj₁))
  push Not at hmerge
  have hmem := hs.mem_of_forall_not_mem hd hmerge
  rcases Nat.lt_or_ge (Multiset.card (s i₀) + 1) k with hlt | hge
  · obtain ⟨hs', hd'⟩ := hs.update_cons hd hlt
    exact linearIndependent_vanishingFamily_of_update_cons MvPolynomial.X_injective hi₀ hmem hlt
      (ih α _ _ d hs' hd' (multiplicityPatternSize_update_cons_lt (hs.card_lt i₀)))
  · have heq : Multiset.card (s i₀) + 1 = k := le_antisymm (hs.card_lt i₀) hge
    have hns : ¬ Function.Surjective (Subtype.val : {i // i ≠ i₀} → α) := fun h => by
      obtain ⟨x, hx⟩ := h i₀
      exact x.2 hx
    exact linearIndependent_vanishingFamily_of_ne MvPolynomial.X_injective hi₀ hmem heq
      (ih _ _ _ d (hs.comp _ Subtype.val_injective) (hd.comp _)
        (multiplicityPatternSize_comp_lt _ Subtype.val_injective hns))

/-- **Linear independence for generic multiplicity patterns.** If `s` is a generic multiplicity
pattern of dimension `k` whose multiplicities are at most one except at `d`, the polynomials
`X ^ e * ∏_{j ∈ s i} (X - C (X j))`, `e < k - card (s i)`, are linearly independent over
`MvPolynomial ι F`. -/
theorem linearIndependent_vanishingFamily {α : Type u} [Finite α] {k : ℕ}
    {s : α → Multiset ι} {d : ι} (hs : IsGenericMultiplicityPattern k s)
    (hd : CountLeOneExcept d s) :
    LinearIndependent (MvPolynomial ι F) (vanishingFamily (MvPolynomial.X (R := F)) k s) := by
  classical
  have := Fintype.ofFinite α
  suffices h : ∀ (N : ℕ) (β : Type u) [Fintype β] [DecidableEq β] (k' : ℕ)
      (t : β → Multiset ι) (d' : ι), IsGenericMultiplicityPattern k' t → CountLeOneExcept d' t →
      multiplicityPatternSize k' t d' < N →
      LinearIndependent (MvPolynomial ι F) (vanishingFamily (MvPolynomial.X (R := F)) k' t) from
    h _ α k s d hs hd (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => intro β _ _ k' t d' _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ N ihN =>
    intro β _ _ k' t d' hs' hd' hlt
    exact linearIndependent_vanishingFamily_of_forall_size_lt
      (fun γ _ _ k'' t' d'' hs'' hd'' hlt' => ihN γ k'' t' d'' hs'' hd'' (by omega)) hs' hd'

/-- `Polynomial.linearIndependent_vanishingFamily` over the fraction field of
`MvPolynomial ι F`. -/
theorem linearIndependent_vanishingFamily_fractionRing {α : Type u} [Finite α] {k : ℕ}
    {s : α → Multiset ι} {d : ι} (hs : IsGenericMultiplicityPattern k s)
    (hd : CountLeOneExcept d s) :
    LinearIndependent (FractionRing (MvPolynomial ι F)) fun p =>
      (vanishingFamily (MvPolynomial.X (R := F)) k s p).map
        (algebraMap (MvPolynomial ι F) (FractionRing (MvPolynomial ι F))) :=
  linearIndependent_map_algebraMap_iff.2 (linearIndependent_vanishingFamily hs hd)

end Main

/-- **Generic zero patterns, symbolic form.** If `S` is a generic zero pattern of `m` sets of size
`m - 1`, the polynomials `∏_{j ∈ S ℓ} (X - C (X j))` are linearly independent over
`MvPolynomial σ F`. -/
theorem linearIndependent_prod_X_sub_C_of_isGenericZeroPattern {F σ : Type*} [Field F]
    [DecidableEq σ] {m : ℕ} {S : Fin m → Finset σ} (hS : IsGenericZeroPattern m S)
    (hcard : ∀ ℓ, #(S ℓ) + 1 = m) :
    LinearIndependent (MvPolynomial σ F) fun ℓ =>
      ∏ j ∈ S ℓ, (X - C (MvPolynomial.X j : MvPolynomial σ F)) := by
  refine linearIndependent_prod_of_vanishingFamily _ hcard ?_
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨d⟩⟩
  · have : Subsingleton (Fin m) := by
      rcases m with _ | _ | m
      · infer_instance
      · exact (inferInstance : Subsingleton (Fin 1))
      · exfalso
        have h0 := hcard 0
        rw [Finset.eq_empty_of_isEmpty (S 0)] at h0
        simp at h0
    exact linearIndependent_vanishingFamily_of_subsingleton _ _ _
  · exact linearIndependent_vanishingFamily (hS.isGenericMultiplicityPattern hcard)
      (countLeOneExcept_val d S)

/-- **Generic zero patterns over an infinite field.** For a generic zero pattern `S` of `m` sets
in a finite type `σ` and an infinite field `K`, there are pairwise distinct points `α j ∈ K` and
linearly independent polynomials `g ℓ` of degree `< m` such that `g ℓ` vanishes at `α j` for every
`j ∈ S ℓ`. -/
theorem exists_embedding_linearIndependent_of_isGenericZeroPattern {K : Type*} [Field K]
    [Infinite K] {σ : Type u} [Finite σ] [DecidableEq σ] {m : ℕ} {S : Fin m → Finset σ}
    (hS : IsGenericZeroPattern m S) :
    ∃ α : σ ↪ K, ∃ g : Fin m → K[X], (∀ ℓ, g ℓ ∈ degreeLT K m) ∧
      (∀ ℓ, ∀ i ∈ S ℓ, (g ℓ).eval (α i) = 0) ∧ LinearIndependent K g := by
  obtain ⟨τ, _, _, e, S', hS', hcard', hsub⟩ := hS.exists_pad
  let f : Fin m → (MvPolynomial τ K)[X] := fun ℓ => ∏ j ∈ S' ℓ, (X - C (MvPolynomial.X j))
  have hf : LinearIndependent (MvPolynomial τ K) f :=
    linearIndependent_prod_X_sub_C_of_isGenericZeroPattern hS' hcard'
  have hdeg : ∀ ℓ, f ℓ ∈ degreeLT (MvPolynomial τ K) m := fun ℓ =>
    prod_X_sub_C_mem_degreeLT _ _ (by have := hcard' ℓ; omega)
  obtain ⟨x, hx, hxdet⟩ :=
    MvPolynomial.exists_injective_eval_ne_zero ((linearIndependent_iff_det_coeff_ne_zero hdeg).1 hf)
  refine ⟨⟨x ∘ e, hx.comp e.injective⟩, fun ℓ => (f ℓ).map (MvPolynomial.eval x), fun ℓ =>
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 (hdeg ℓ))), ?_,
    linearIndependent_map_of_det_coeff_ne_zero (MvPolynomial.eval x) hdeg hxdet⟩
  intro ℓ i hi
  have hmem : e i ∈ S' ℓ := hsub ℓ (Finset.mem_map_of_mem e hi)
  rw [eval_map, eval₂_finsetProd]
  exact Finset.prod_eq_zero hmem (by simp)

end Polynomial
