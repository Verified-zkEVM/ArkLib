/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Lattice.ScaledLattice
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm


/-!
# A discrete lower bound for the truncated scaled lattice

This file supplies the measure-free part of the repaired scaled-shell
argument. The proof is adapted, with permission, from Kai Zhe Zheng's
`rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`. The free-order extension was
contributed through PR 1 by Pratyush Mishra at commit
`b1e346fc39780adb442ed2504a316b32702b97af`; its metadata records Codex as
author and Pratyush Mishra as committer. The project-owner permission
attestation is recorded in `docs/kb/sources/rs-ld-mca/PERMISSION.md`.

A scaled exponent is the multiplicity sequence of a partition.
Its conjugate partition is a decreasing tuple whose sum is the scaled weight
and whose largest entry is the ordinary degree.  Consequently, bounded
ordinary tuples with every coordinate at most the ordinary-degree cutoff map
injectively to a good scaled exponent together with a permutation.

The remaining loss is controlled by an elementary union bound: an ordinary
tuple outside the coordinate cap has a distinguished coordinate at least
`S + 1`; subtracting that amount embeds it into a smaller simplex.
-/

@[expose] public section

open PolynomialDifferential


open DiscreteSimplex

namespace ReedSolomon
namespace HiddenDerivative

open scoped BigOperators

/-! ## Conjugating a partition -/

/-- Consecutive differences of a decreasing list, with an implicit terminal
zero.  These are the multiplicities of the column heights of the associated
partition. -/
private def partitionDifferences : List ℕ → List ℕ
  | [] => []
  | a :: l => (a - l.headD 0) :: partitionDifferences l

private theorem length_partitionDifferences (l : List ℕ) :
    (partitionDifferences l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [partitionDifferences, ih]

/-- A weighted list sum with weights `w, w+1, ...`. -/
private def weightedListSum : ℕ → List ℕ → ℕ
  | _, [] => 0
  | w, a :: l => w * a + weightedListSum (w + 1) l

private theorem weightedListSum_succ (w : ℕ) (l : List ℕ) :
    weightedListSum (w + 1) l = weightedListSum w l + l.sum := by
  induction l generalizing w with
  | nil => simp [weightedListSum]
  | cons a l ih =>
      simp only [weightedListSum, List.sum_cons, ih]
      ring

private theorem sum_partitionDifferences_of_sorted :
    ∀ {l : List ℕ}, l.Pairwise (· ≥ ·) →
      (partitionDifferences l).sum = l.headD 0 := by
  intro l hl
  induction l with
  | nil => simp [partitionDifferences]
  | cons a l ih =>
      cases l with
      | nil => simp [partitionDifferences]
      | cons b l =>
          have hba : b ≤ a := (List.pairwise_cons.mp hl).1 b (by simp)
          have htail : (b :: l).Pairwise (· ≥ ·) := hl.tail
          rw [partitionDifferences, List.sum_cons, ih htail]
          simp only [List.headD_cons]
          exact Nat.sub_add_cancel hba

private theorem weighted_partitionDifferences_of_sorted :
    ∀ {l : List ℕ}, l.Pairwise (· ≥ ·) →
      weightedListSum 1 (partitionDifferences l) = l.sum := by
  intro l hl
  induction l with
  | nil => simp [partitionDifferences, weightedListSum]
  | cons a l ih =>
      cases l with
      | nil => simp [partitionDifferences, weightedListSum]
      | cons b l =>
          have hba : b ≤ a := (List.pairwise_cons.mp hl).1 b (by simp)
          have htail : (b :: l).Pairwise (· ≥ ·) := hl.tail
          have hsum : (partitionDifferences (b :: l)).sum = b := by
            simpa using sum_partitionDifferences_of_sorted htail
          have hweight : weightedListSum 1
              (partitionDifferences (b :: l)) = (b :: l).sum := ih htail
          calc
            weightedListSum 1 (partitionDifferences (a :: b :: l)) =
                (a - b) +
                  (weightedListSum 1 (partitionDifferences (b :: l)) +
                    (partitionDifferences (b :: l)).sum) := by
              rw [partitionDifferences, weightedListSum,
                weightedListSum_succ]
              simp
            _ = (a - b) + ((b :: l).sum + b) := by
              rw [hweight, hsum]
            _ = (a :: b :: l).sum := by
              simp only [List.sum_cons]
              omega

private theorem partitionDifferences_injective_of_sorted :
    ∀ {l₁ l₂ : List ℕ}, l₁.Pairwise (· ≥ ·) →
      l₂.Pairwise (· ≥ ·) →
      partitionDifferences l₁ = partitionDifferences l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ _ _ h
      cases l₂ <;> simp [partitionDifferences] at h ⊢
  | cons a l₁ ih =>
      intro l₂ hs₁ hs₂ h
      cases l₂ with
      | nil => simp [partitionDifferences] at h
      | cons b l₂ =>
          have htailDiff : partitionDifferences l₁ =
              partitionDifferences l₂ := by
            simpa [partitionDifferences] using congrArg List.tail h
          have htail : l₁ = l₂ := ih hs₁.tail hs₂.tail htailDiff
          subst l₂
          cases l₁ with
          | nil =>
              simpa [partitionDifferences] using h
          | cons c l =>
              have hca : c ≤ a :=
                (List.pairwise_cons.mp hs₁).1 c (by simp)
              have hcb : c ≤ b :=
                (List.pairwise_cons.mp hs₂).1 c (by simp)
              have hab : a - c = b - c := by
                simpa [partitionDifferences] using
                  congrArg (fun l ↦ l.headD 0) h
              have : a = b := by omega
              subst b
              rfl

/-- Interpret consecutive differences of a decreasing tuple as a scaled
exponent. -/
private def partitionMultiplicity {r : ℕ} (y : Fin r → ℕ) : Fin r → ℕ :=
  fun i ↦
    (partitionDifferences (List.ofFn y)).get
      ⟨i.val, by
        rw [length_partitionDifferences, List.length_ofFn]
        exact i.isLt⟩

private theorem ofFn_partitionMultiplicity {r : ℕ} (y : Fin r → ℕ) :
    List.ofFn (partitionMultiplicity y) =
      partitionDifferences (List.ofFn y) := by
  apply List.ext_get
  · simp [length_partitionDifferences]
  · intro i hi₁ hi₂
    simp [partitionMultiplicity]

private theorem weightedListSum_ofFn (w : ℕ) :
    ∀ {r : ℕ} (f : Fin r → ℕ),
      weightedListSum w (List.ofFn f) =
        ∑ i, (w + i.val) * f i := by
  intro r
  induction r generalizing w with
  | zero => intro f; simp [weightedListSum]
  | succ r ih =>
      intro f
      rw [List.ofFn_succ, weightedListSum, Fin.sum_univ_succ]
      rw [ih (w := w + 1)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ]
      congr 1
      omega

private theorem sum_partitionMultiplicity {r : ℕ}
    (y : Fin r → ℕ) (hy : Antitone y) :
    (∑ i, partitionMultiplicity y i) =
      (List.ofFn y).headD 0 := by
  rw [← List.sum_ofFn,
    ofFn_partitionMultiplicity]
  exact sum_partitionDifferences_of_sorted
    (List.pairwise_ofFn.mpr fun _ _ hij ↦ hy hij.le)

private theorem weighted_partitionMultiplicity {r : ℕ}
    (y : Fin r → ℕ) (hy : Antitone y) :
    (∑ i, (i.val + 1) * partitionMultiplicity y i) = ∑ i, y i := by
  have hrewrite :
      (∑ i, (i.val + 1) * partitionMultiplicity y i) =
        ∑ i, (1 + i.val) * partitionMultiplicity y i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  rw [hrewrite, ← weightedListSum_ofFn 1,
    ofFn_partitionMultiplicity,
    weighted_partitionDifferences_of_sorted
      (List.pairwise_ofFn.mpr fun _ _ hij ↦ hy hij.le),
    List.sum_ofFn]

private theorem scaledOrdinaryDegree_partitionMultiplicity {d : ℕ}
    (y : Fin (d - 1) → ℕ) (hy : Antitone y) :
    scaledOrdinaryDegree (partitionMultiplicity y) =
      (List.ofFn y).headD 0 := by
  exact sum_partitionMultiplicity y hy

private theorem scaledWeight_partitionMultiplicity {d : ℕ}
    (y : Fin (d - 1) → ℕ) (hy : Antitone y) :
    scaledWeight (partitionMultiplicity y) = ∑ i, y i := by
  exact weighted_partitionMultiplicity y hy

private theorem partitionMultiplicity_injective_of_antitone {r : ℕ}
    {y₁ y₂ : Fin r → ℕ} (hy₁ : Antitone y₁) (hy₂ : Antitone y₂)
    (h : partitionMultiplicity y₁ = partitionMultiplicity y₂) : y₁ = y₂ := by
  apply List.ofFn_injective
  apply partitionDifferences_injective_of_sorted
    (List.pairwise_ofFn.mpr fun _ _ hij ↦ hy₁ hij.le)
    (List.pairwise_ofFn.mpr fun _ _ hij ↦ hy₂ hij.le)
  rw [← ofFn_partitionMultiplicity, ← ofFn_partitionMultiplicity, h]

/-! ## Sorting capped ordinary tuples -/

/-- Ordinary simplex points whose every coordinate is at most `S`. -/
abbrev CappedOrdinarySimplex (r W S : ℕ) :=
  {a : OrdinarySimplex r W // ∀ i, a.1 i ≤ S}

/-- The permutation putting a tuple in decreasing order. -/
private noncomputable def descendingSortPerm {r : ℕ} (a : Fin r → ℕ) :
    Equiv.Perm (Fin r) :=
  Tuple.sort (fun i ↦ OrderDual.toDual (a i))

private theorem descendingSort_antitone {r : ℕ} (a : Fin r → ℕ) :
    Antitone (a ∘ descendingSortPerm a) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i ↦ OrderDual.toDual (a i)) hij
  simpa [descendingSortPerm, Function.comp_def] using h

private theorem sum_descendingSort {r : ℕ} (a : Fin r → ℕ) :
    ∑ i, (a ∘ descendingSortPerm a) i = ∑ i, a i := by
  exact Equiv.sum_comp (descendingSortPerm a) a

private theorem headD_ofFn_le {r S : ℕ} {a : Fin r → ℕ}
    (ha : ∀ i, a i ≤ S) : (List.ofFn a).headD 0 ≤ S := by
  cases r with
  | zero => simp
  | succ r =>
      rw [List.ofFn_succ]
      simpa using ha 0

/-- Sorting and conjugating, while retaining the sorting permutation, is
injective.  The target cardinality is therefore `|G| * (d-1)!`. -/
private noncomputable def cappedOrdinaryToGoodWithPerm (d W S : ℕ) :
    CappedOrdinarySimplex (d - 1) W S →
      GoodScaledExponent d W S × Equiv.Perm (Fin (d - 1)) :=
  fun a ↦
    let σ := descendingSortPerm a.1.1
    let y := a.1.1 ∘ σ
    let c := partitionMultiplicity y
    ⟨⟨c, mem_goodScaledExponentFinset.mpr ⟨by
          rw [scaledWeight_partitionMultiplicity y
            (descendingSort_antitone a.1.1), sum_descendingSort]
          exact a.1.2,
        by
          rw [scaledOrdinaryDegree_partitionMultiplicity y
            (descendingSort_antitone a.1.1)]
          apply headD_ofFn_le
          intro i
          exact a.2 (σ i)⟩⟩,
      σ⟩

private theorem cappedOrdinaryToGoodWithPerm_injective (d W S : ℕ) :
    Function.Injective (cappedOrdinaryToGoodWithPerm d W S) := by
  intro a b hab
  have hperm : descendingSortPerm a.1.1 = descendingSortPerm b.1.1 :=
    congrArg Prod.snd hab
  have hc :
      partitionMultiplicity (a.1.1 ∘ descendingSortPerm a.1.1) =
        partitionMultiplicity (b.1.1 ∘ descendingSortPerm b.1.1) := by
    simpa [cappedOrdinaryToGoodWithPerm] using
      congrArg (fun p ↦ p.1.1) hab
  have hy : a.1.1 ∘ descendingSortPerm a.1.1 =
      b.1.1 ∘ descendingSortPerm b.1.1 :=
    partitionMultiplicity_injective_of_antitone
      (descendingSort_antitone a.1.1) (descendingSort_antitone b.1.1) hc
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have hi := congrFun hy ((descendingSortPerm a.1.1).symm i)
  simpa [hperm] using hi

noncomputable instance cappedOrdinarySimplexFintype
    (r W S : ℕ) : Fintype (CappedOrdinarySimplex r W S) :=
  Fintype.ofFinite _

/-- Capped ordinary tuples provide a lower bound for the good scaled lattice,
up to the `(d-1)!` possible orderings of their coordinates. -/
theorem card_cappedOrdinarySimplex_le_good_mul_factorial (d W S : ℕ) :
    Fintype.card (CappedOrdinarySimplex (d - 1) W S) ≤
      goodScaledExponentCount d W S * (d - 1).factorial := by
  calc
    Fintype.card (CappedOrdinarySimplex (d - 1) W S) ≤
        Fintype.card
          (GoodScaledExponent d W S × Equiv.Perm (Fin (d - 1))) :=
      Fintype.card_le_of_injective _
        (cappedOrdinaryToGoodWithPerm_injective d W S)
    _ = goodScaledExponentCount d W S * (d - 1).factorial := by
      rw [Fintype.card_prod, Fintype.card_perm]
      simp [goodScaledExponentCount]

/-! ## A discrete union bound -/

/-- Subtract `t` from one distinguished coordinate of an ordinary tuple. -/
private def subtractOrdinaryCoordinate {r W t : ℕ}
    (i : Fin r) (a : OrdinarySimplex r W) (hi : t ≤ a.1 i) :
    OrdinarySimplex r (W - t) :=
  ⟨Function.update a.1 i (a.1 i - t), by
    have hsum : ∑ j, Function.update a.1 i (a.1 i - t) j =
        (∑ j, a.1 j) - t := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sdiff_singleton_eq_erase]
      have hdecomp := Finset.sum_erase_add Finset.univ a.1
        (Finset.mem_univ i)
      omega
    rw [hsum]
    exact Nat.sub_le_sub_right a.2 t⟩

private theorem subtractOrdinaryCoordinate_injective {r W t : ℕ}
    (i : Fin r) :
    Function.Injective
      (fun a : {a : OrdinarySimplex r W // t ≤ a.1 i} ↦
        subtractOrdinaryCoordinate i a.1 a.2) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    have hval := congrArg (fun x ↦ x.1 i) hab
    simp [subtractOrdinaryCoordinate] at hval
    omega
  · have hval := congrArg (fun x ↦ x.1 j) hab
    simpa [subtractOrdinaryCoordinate, Function.update, hji] using hval

/-- Adding the distinguished amount back recovers the tuple before
`subtractOrdinaryCoordinate`. -/
private def restoreOrdinaryCoordinate {r W t : ℕ}
    (p : Fin r × OrdinarySimplex r (W - t)) : Fin r → ℕ :=
  Function.update p.2.1 p.1 (p.2.1 p.1 + t)

private theorem restore_subtractOrdinaryCoordinate {r W t : ℕ}
    (i : Fin r) (a : OrdinarySimplex r W) (hi : t ≤ a.1 i) :
    restoreOrdinaryCoordinate (i, subtractOrdinaryCoordinate i a hi) = a.1 := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [restoreOrdinaryCoordinate, subtractOrdinaryCoordinate,
      Function.update]
    omega
  · simp [restoreOrdinaryCoordinate, subtractOrdinaryCoordinate,
      Function.update, hji]

/-- If a simplex point is not coordinatewise bounded by `S`, choose one bad
coordinate and subtract `S+1` there. -/
private noncomputable def splitOrdinaryAtCap (r W S : ℕ) :
    OrdinarySimplex r W →
      CappedOrdinarySimplex r W S ⊕
        (Fin r × OrdinarySimplex r (W - (S + 1))) :=
  fun a ↦
    if h : ∀ i, a.1 i ≤ S then
      Sum.inl ⟨a, h⟩
    else
      let i := Classical.choose (not_forall.mp h)
      have hi : S + 1 ≤ a.1 i := by
        have hnot := Classical.choose_spec (not_forall.mp h)
        exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
      Sum.inr ⟨i, subtractOrdinaryCoordinate i a hi⟩

private theorem splitOrdinaryAtCap_injective (r W S : ℕ) :
    Function.Injective (splitOrdinaryAtCap r W S) := by
  intro a b hab
  by_cases ha : ∀ i, a.1 i ≤ S
  · by_cases hb : ∀ i, b.1 i ≤ S
    · simpa [splitOrdinaryAtCap, ha, hb] using hab
    · simp [splitOrdinaryAtCap, ha, hb] at hab
  · by_cases hb : ∀ i, b.1 i ≤ S
    · simp [splitOrdinaryAtCap, ha, hb] at hab
    · simp only [splitOrdinaryAtCap, ha, hb, dite_false] at hab
      have hp := Sum.inr.inj hab
      have hrecovered := congrArg
        (restoreOrdinaryCoordinate (W := W) (t := S + 1)) hp
      rw [restore_subtractOrdinaryCoordinate,
        restore_subtractOrdinaryCoordinate] at hrecovered
      exact Subtype.ext hrecovered

/-- Discrete union bound for a coordinate cap in an ordinary simplex. -/
theorem card_ordinarySimplex_le_capped_add_bad (r W S : ℕ) :
    Fintype.card (OrdinarySimplex r W) ≤
      Fintype.card (CappedOrdinarySimplex r W S) +
        r * Fintype.card (OrdinarySimplex r (W - (S + 1))) := by
  calc
    Fintype.card (OrdinarySimplex r W) ≤
        Fintype.card
          (CappedOrdinarySimplex r W S ⊕
            (Fin r × OrdinarySimplex r (W - (S + 1)))) :=
      Fintype.card_le_of_injective _ (splitOrdinaryAtCap_injective r W S)
    _ = Fintype.card (CappedOrdinarySimplex r W S) +
          r * Fintype.card (OrdinarySimplex r (W - (S + 1))) := by
      rw [Fintype.card_sum, Fintype.card_prod]
      simp

/-! ## Cross-multiplied good-lattice bounds -/

/-- Generic lower bound with an explicit union-bound error term.  This is the
integer version of the concentration step and uses no division. -/
theorem pow_le_good_mul_factorial_sq_add_bad
    (d W S : ℕ) :
    W ^ (d - 1) ≤
      goodScaledExponentCount d W S * ((d - 1).factorial ^ 2) +
        (d - 1) *
          (W - (S + 1) + (d - 1)) ^ (d - 1) := by
  let r := d - 1
  calc
    W ^ r ≤ r.factorial * Fintype.card (OrdinarySimplex r W) :=
      pow_le_factorial_mul_card_ordinarySimplex r W
    _ ≤ r.factorial *
          (Fintype.card (CappedOrdinarySimplex r W S) +
            r * Fintype.card (OrdinarySimplex r (W - (S + 1)))) :=
      Nat.mul_le_mul_left _ (card_ordinarySimplex_le_capped_add_bad r W S)
    _ ≤ r.factorial *
          (goodScaledExponentCount d W S * r.factorial +
            r * Fintype.card (OrdinarySimplex r (W - (S + 1)))) := by
      gcongr
      exact card_cappedOrdinarySimplex_le_good_mul_factorial d W S
    _ = goodScaledExponentCount d W S * (r.factorial ^ 2) +
          r * (r.factorial *
            Fintype.card (OrdinarySimplex r (W - (S + 1)))) := by ring
    _ ≤ goodScaledExponentCount d W S * (r.factorial ^ 2) +
          r * ((W - (S + 1) + r) ^ r) := by
      gcongr
      exact factorial_mul_card_ordinarySimplex_le_pow r (W - (S + 1))

/-- If the explicit bad-tuple error is at most half the main term, at least
half of the factorial-normalized simplex survives the ordinary-degree cap. -/
theorem pow_le_two_mul_good_mul_factorial_sq
    (d W S : ℕ)
    (hbad :
      2 * ((d - 1) *
        (W - (S + 1) + (d - 1)) ^ (d - 1)) ≤ W ^ (d - 1)) :
    W ^ (d - 1) ≤
      2 * goodScaledExponentCount d W S * ((d - 1).factorial ^ 2) := by
  have hmain := pow_le_good_mul_factorial_sq_add_bad d W S
  let G := goodScaledExponentCount d W S * ((d - 1).factorial ^ 2)
  let E := (d - 1) * (W - (S + 1) + (d - 1)) ^ (d - 1)
  change W ^ (d - 1) ≤ G + E at hmain
  change 2 * E ≤ W ^ (d - 1) at hbad
  have hresult : W ^ (d - 1) ≤ 2 * G := by omega
  simpa [G, Nat.mul_assoc] using hresult

/-- A shell-ratio bound with all divisions cleared.  The left side uses the
same factorial normalization as the upper lattice estimate, so the
factorials cancel exactly. -/
theorem two_mul_good_mul_shell_pow_ge
    (d W S m R : ℕ)
    (hbad :
      2 * ((d - 1) *
        (W - (S + 1) + (d - 1)) ^ (d - 1)) ≤ W ^ (d - 1))
    (hratio :
      2 * (W + m + d * (d - 1) / 2) ^ (d - 1) ≤
        R * W ^ (d - 1)) :
    2 * scaledExponentCount d (W + m) ≤
      R * (2 * goodScaledExponentCount d W S) := by
  have hupper := scaledExponentCount_mul_factorial_sq_le_pow d (W + m)
  have hlower := pow_le_two_mul_good_mul_factorial_sq d W S hbad
  have hfac : 0 < (d - 1).factorial ^ 2 := pow_pos (Nat.factorial_pos _) _
  refine Nat.le_of_mul_le_mul_right ?_ hfac
  calc
    2 * scaledExponentCount d (W + m) * ((d - 1).factorial ^ 2) ≤
        2 * (W + m + d * (d - 1) / 2) ^ (d - 1) := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hupper
    _ ≤ R * W ^ (d - 1) := hratio
    _ ≤ R *
          (2 * goodScaledExponentCount d W S * ((d - 1).factorial ^ 2)) :=
      Nat.mul_le_mul_left R hlower
    _ = R * (2 * goodScaledExponentCount d W S) *
          ((d - 1).factorial ^ 2) := by ring

/-- Clean cardinal-ratio form of `two_mul_good_mul_shell_pow_ge`. -/
theorem scaledExponentCount_shell_le_mul_goodScaledExponentCount
    (d W S m R : ℕ)
    (hbad :
      2 * ((d - 1) *
        (W - (S + 1) + (d - 1)) ^ (d - 1)) ≤ W ^ (d - 1))
    (hratio :
      2 * (W + m + d * (d - 1) / 2) ^ (d - 1) ≤
        R * W ^ (d - 1)) :
    scaledExponentCount d (W + m) ≤
      R * goodScaledExponentCount d W S := by
  have h := two_mul_good_mul_shell_pow_ge d W S m R hbad hratio
  have h' :
      2 * scaledExponentCount d (W + m) ≤
        2 * (R * goodScaledExponentCount d W S) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_left h' (by omega)

end HiddenDerivative
end ReedSolomon
