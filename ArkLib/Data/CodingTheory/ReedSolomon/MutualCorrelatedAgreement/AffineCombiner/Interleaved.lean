/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ToMathlib.Algebra.Polynomial.Pack
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement
public import ArkLib.ToMathlib.FieldTheory.Finite.Extension
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Theorem

/-!
# Interleaved affine combiners

Rows `f r, g r` of received words are combined with one shared affine challenge `(α, β)`.
A candidate tuple `P` agrees at a point when every row `P r` agrees with `f r + (α + β x) g r`.
A point is lost when some row of the witness tuples fails its received word there.
So the agreement loss of one point is shared by all rows.

The rows are packed into one word over an extension `E` of degree `t` along a basis.
Packing commutes with evaluation and with the combiner.
Equality of packed values is equality in every row.
So an exceptional tuple packs to an exceptional polynomial over `E` at the same challenge.
The count for challenges from a subfield then gives the one-round bound without a factor of `t`.

The definitions and the bound (5.7) follow the proof of Theorem 5.2 of [CWYZ26].
The paper uses `1 ≤ d < n` and `1 ≤ A ≤ n`, where `n` is the domain size.
The definitions also cover boundary values, and `t = 1` recovers the affine definitions.
The rest of Theorem 5.2, the folding over `log₂ k` rounds, is not formalized here.
The bound keeps the hypothesis `d < n` to match the paper.
It follows from the others when `n > 0`.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The error has type `ENNReal` and a counting definition that requires no sampler.
The sibling sampling module identifies it with a supremum of native probabilities.
The counting definition uses classical decidability for predicates over polynomial witnesses.

## Main definitions

* `ReedSolomon.interleavedAgreementSet`: the shared agreement set of a tuple.
* `ReedSolomon.interleavedAgreementLoss`: the shared agreement points lost by witness tuples.
* `ReedSolomon.IsInterleavedLossWitness`: witness tuples with bounded shared loss.
* `ReedSolomon.IsInterleavedAffineExceptional`: exceptional tuples.
* `ReedSolomon.interleavedAffineMcaError`: the uniform error probability.

## Main statements

* `ReedSolomon.le_interleavedAffineMcaError`,
  `ReedSolomon.interleavedAffineMcaError_le_of_forall_exists` and
  `ReedSolomon.interleavedAffineMcaError_le_one`: basic bounds on the error.
* `ReedSolomon.interleavedAgreementSet_one`, `ReedSolomon.interleavedAgreementLoss_one`,
  `ReedSolomon.isInterleavedAffineExceptional_one_iff` and
  `ReedSolomon.interleavedAffineMcaError_one`: one row is the affine combiner.
* `ReedSolomon.IsInterleavedAffineExceptional.pack`: an exceptional tuple packs to an
  exceptional polynomial over an extension.
* `ReedSolomon.exists_interleavedAffineExceptional_finset_card_le` and
  `ReedSolomon.interleavedAffineMcaError_le`: the bound (5.7).

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] {t : ℕ}

/-- The points where every row `P r` agrees with `f r + (α + β x) g r`. -/
def interleavedAgreementSet (domain : ι ↪ F) (f g : Fin t → ι → F) (α β : F)
    (P : Fin t → F[X]) : Finset ι :=
  interleavedPolynomialAgreementSet domain (fun i r ↦ f r i + (α + β * domain i) * g r i) P

/-- A position agrees exactly when every combined row agrees there. -/
@[simp]
theorem mem_interleavedAgreementSet (domain : ι ↪ F) (f g : Fin t → ι → F) (α β : F)
    (P : Fin t → F[X]) (i : ι) :
    i ∈ interleavedAgreementSet domain f g α β P ↔
      ∀ r, (P r).eval (domain i) = f r i + (α + β * domain i) * g r i := by
  simp [interleavedAgreementSet]

/-- The shared agreement points of `P` where some row of `F₀` or `G₀` fails its received word. -/
def interleavedAgreementLoss (domain : ι ↪ F) (f g : Fin t → ι → F) (α β : F)
    (P F₀ G₀ : Fin t → F[X]) : Finset ι :=
  (interleavedAgreementSet domain f g α β P).filter fun i ↦
    ∃ r, (F₀ r).eval (domain i) ≠ f r i ∨ (G₀ r).eval (domain i) ≠ g r i

/-- An agreeing position is lost if either witness differs from its received word in any row. -/
@[simp]
theorem mem_interleavedAgreementLoss (domain : ι ↪ F) (f g : Fin t → ι → F) (α β : F)
    (P F₀ G₀ : Fin t → F[X]) (i : ι) :
    i ∈ interleavedAgreementLoss domain f g α β P F₀ G₀ ↔
      i ∈ interleavedAgreementSet domain f g α β P ∧
        ∃ r, (F₀ r).eval (domain i) ≠ f r i ∨ (G₀ r).eval (domain i) ≠ g r i := by
  simp [interleavedAgreementLoss]

/-- Every row satisfies `P r = F₀ r + (α + β X) G₀ r`.
At most `s` shared agreement points are lost. -/
def IsInterleavedLossWitness (domain : ι ↪ F) (f g : Fin t → ι → F) (s : ℕ) (α β : F)
    (P F₀ G₀ : Fin t → F[X]) : Prop :=
  (∀ r, P r = F₀ r + affineMultiplier α β * G₀ r) ∧
    #(interleavedAgreementLoss domain f g α β P F₀ G₀) ≤ s

/-- The tuple `P` is exceptional for the shared challenge `(α, β)`.

The agreement threshold is `A` and the allowed shared loss is `s`.
Every row has degree at most `d`, and at least `A` points are shared agreements.
Consider witness tuples with `deg F₀ r ≤ d`, `deg G₀ r < d` and `P r = F₀ r + (α + β X) G₀ r`.
No such tuples lose at most `s` shared agreements. -/
def IsInterleavedAffineExceptional (domain : ι ↪ F) (f g : Fin t → ι → F) (d A s : ℕ)
    (α β : F) (P : Fin t → F[X]) : Prop :=
  (∀ r, (P r).degree ≤ d) ∧ A ≤ #(interleavedAgreementSet domain f g α β P) ∧
    ∀ F₀ G₀ : Fin t → F[X], (∀ r, (F₀ r).degree ≤ d) → (∀ r, (G₀ r).degree < d) →
      ¬ IsInterleavedLossWitness domain f g s α β P F₀ G₀

open Classical in
/-- The worst-case probability that a uniform shared challenge has an exceptional tuple.

The supremum ranges over row tuples `(f, g)` and the challenge `(α, β)` is uniform in `F²`.
There are `t` rows and the output degree bound is `d`.
The agreement threshold is `A` and the allowed shared loss is `s`.
`ReedSolomon.interleavedAffineMcaError_eq_iSup_prob` gives the sampling form. -/
noncomputable def interleavedAffineMcaError [Fintype F] (domain : ι ↪ F) (t d A s : ℕ) :
    ENNReal :=
  ⨆ w : (Fin t → ι → F) × (Fin t → ι → F),
    ENNReal.ofReal
      ((#{c : F × F | ∃ P, IsInterleavedAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2)

section Error

variable [Fintype F] (domain : ι ↪ F)

open Classical in
/-- One pair of row tuples bounds the interleaved error from below. -/
theorem le_interleavedAffineMcaError (d A s : ℕ) (f g : Fin t → ι → F) :
    ENNReal.ofReal
      ((#{c : F × F | ∃ P, IsInterleavedAffineExceptional domain f g d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2) ≤ interleavedAffineMcaError domain t d A s := by
  unfold interleavedAffineMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- Suppose every pair of row tuples has a set of at most `B` challenges.
Suppose that set contains every challenge with an exceptional tuple.
Then the error is at most `B / |F|²`. -/
theorem interleavedAffineMcaError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : Fin t → ι → F, ∃ S : Finset (F × F), (S.card : ℝ) ≤ B ∧
      ∀ c ∉ S, ∀ P, ¬ IsInterleavedAffineExceptional domain f g d A s c.1 c.2 P) :
    interleavedAffineMcaError domain t d A s ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ) ^ 2) := by
  classical
  refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨S, hS, hgood⟩ := h w.1 w.2
  gcongr
  calc (#{c : F × F | ∃ P, IsInterleavedAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ)
      ≤ S.card := by
        gcongr
        intro c hc
        by_contra hcS
        obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hc).2
        exact hgood c hcS P hP
    _ ≤ B := hS

/-- The interleaved error is at most one. -/
theorem interleavedAffineMcaError_le_one (t d A s : ℕ) :
    interleavedAffineMcaError domain t d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F | ∃ P, IsInterleavedAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F)).card := by exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 2 := by simp [sq]

end Error

section One

/-- With one row, the shared agreement set is the agreement set of the affine combiner. -/
theorem interleavedAgreementSet_one (domain : ι ↪ F) (f g : Fin 1 → ι → F) (α β : F)
    (P : Fin 1 → F[X]) :
    interleavedAgreementSet domain f g α β P =
      polynomialAgreementSet domain (combinedWord domain (f 0) (g 0) (affineMultiplier α β))
        (P 0) := by
  ext i
  simp [Fin.forall_fin_one]

/-- With one row, the shared loss is the agreement loss of the affine combiner. -/
theorem interleavedAgreementLoss_one (domain : ι ↪ F) (f g : Fin 1 → ι → F) (α β : F)
    (P F₀ G₀ : Fin 1 → F[X]) :
    interleavedAgreementLoss domain f g α β P F₀ G₀ =
      agreementLoss domain (f 0) (g 0) (affineMultiplier α β) (P 0) (F₀ 0) (G₀ 0) := by
  ext i
  simp [agreementLoss, Fin.exists_fin_one, Fin.forall_fin_one]

/-- With one row, a tuple is exceptional exactly when its row is affine exceptional.
The received word pair is the single row. -/
theorem isInterleavedAffineExceptional_one_iff (domain : ι ↪ F) (f g : Fin 1 → ι → F)
    (d A s : ℕ) (α β : F) (P : Fin 1 → F[X]) :
    IsInterleavedAffineExceptional domain f g d A s α β P ↔
      IsAffineExceptional domain (f 0) (g 0) d A s α β (P 0) := by
  simp only [IsInterleavedAffineExceptional, IsAffineExceptional, IsInterleavedLossWitness,
    IsLossWitness, interleavedAgreementSet_one, interleavedAgreementLoss_one, Fin.forall_fin_one]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun h F₀ G₀ hF hG hw ↦ ?_,
    fun h F₀ G₀ hF hG hw ↦ h (F₀ 0) (G₀ 0) hF hG hw⟩
  exact h (fun _ ↦ F₀) (fun _ ↦ G₀) hF hG hw

/-- With one row, the interleaved error is the affine error. -/
theorem interleavedAffineMcaError_one [Fintype F] (domain : ι ↪ F) (d A s : ℕ) :
    interleavedAffineMcaError domain 1 d A s = affineMcaError domain d A s := by
  classical
  unfold interleavedAffineMcaError affineMcaError
  refine (Equiv.prodCongr (Equiv.funUnique (Fin 1) (ι → F))
    (Equiv.funUnique (Fin 1) (ι → F))).iSup_congr fun w ↦ ?_
  congr 3
  refine (congrArg Finset.card (Finset.filter_congr fun c _ ↦ ?_)).symm
  have h := isInterleavedAffineExceptional_one_iff domain w.1 w.2 d A s c.1 c.2
  exact ⟨fun ⟨P, hP⟩ ↦ ⟨P 0, (h P).mp hP⟩, fun ⟨P, hP⟩ ↦ ⟨fun _ ↦ P, (h _).mpr hP⟩⟩

end One

section Packing

variable {E : Type*} [Field E] [DecidableEq E] [Algebra F E]

/-- Let `b` be a basis of a field extension `E` of `F`, indexed by the `t` rows.
Pack the rows `f r` into the word `∑ r, f r · b r` over `E`, and the rows `g r` likewise.
The domain is mapped into `E`.
An exceptional tuple `P` for `(α, β)` packs to the polynomial `∑ r, b r · P r`.
That polynomial is exceptional for `(α, β)` over `E`.
The degree bound, threshold and loss stay the same. -/
theorem IsInterleavedAffineExceptional.pack {domain : ι ↪ F} {f g : Fin t → ι → F}
    {d A s : ℕ} {α β : F} {P : Fin t → F[X]} (b : Module.Basis (Fin t) F E)
    (h : IsInterleavedAffineExceptional domain f g d A s α β P) :
    IsAffineExceptional (domain.trans ⟨algebraMap F E, (algebraMap F E).injective⟩)
      (fun i ↦ ∑ r, f r i • b r) (fun i ↦ ∑ r, g r i • b r) d A s
      (algebraMap F E α) (algebraMap F E β) (Polynomial.pack b P) := by
  set φ := algebraMap F E
  set domainE := domain.trans ⟨φ, φ.injective⟩
  have hli := b.linearIndependent
  have hcomb (u v : Fin t → F) : ∑ r, u r • b r = ∑ r, v r • b r ↔ ∀ r, u r = v r :=
    ⟨fun h ↦ Fintype.linearIndependent_iffₛ.mp hli u v h, fun h ↦ by simp [h]⟩
  have heval (Q : Fin t → F[X]) (i : ι) :
      (Polynomial.pack b Q).eval (domainE i) = ∑ r, (Q r).eval (domain i) • b r :=
    eval_pack _ _ _
  have hword (i : ι) : (∑ r, f r i • b r) + (φ α + φ β * domainE i) * ∑ r, g r i • b r =
      ∑ r, (f r i + (α + β * domain i) * g r i) • b r := by
    have : φ α + φ β * domainE i = φ (α + β * domain i) := by simp [domainE, φ]
    rw [this, ← Algebra.smul_def, Finset.smul_sum]
    simp only [smul_smul, ← Finset.sum_add_distrib, add_smul]
  have hset : polynomialAgreementSet domainE (combinedWord domainE (fun i ↦ ∑ r, f r i • b r)
      (fun i ↦ ∑ r, g r i • b r) (affineMultiplier (φ α) (φ β))) (Polynomial.pack b P) =
      interleavedAgreementSet domain f g α β P := by
    ext i
    rw [mem_polynomialAgreementSet, combinedWord_affineMultiplier, heval, hword, hcomb,
      mem_interleavedAgreementSet]
  have hne (Q : Fin t → F[X]) (w : Fin t → ι → F) (i : ι) :
      (Polynomial.pack b Q).eval (domainE i) ≠ ∑ r, w r i • b r ↔
        ∃ r, (Q r).eval (domain i) ≠ w r i := by
    rw [heval, Ne, hcomb, not_forall]
  obtain ⟨hdeg, hA, hwit⟩ := h
  refine ⟨(degree_pack_le_iff hli P d).mpr hdeg, hset ▸ hA, fun F₀' G₀' hF hG hw ↦ ?_⟩
  obtain ⟨F₀, rfl⟩ := exists_pack_eq b F₀'
  obtain ⟨G₀, rfl⟩ := exists_pack_eq b G₀'
  refine hwit F₀ G₀ ((degree_pack_le_iff hli F₀ d).mp hF) ((degree_pack_lt_iff hli G₀ d).mp hG)
    ⟨fun r ↦ ?_, ?_⟩
  · have h := hw.1
    rw [← map_affineMultiplier, ← pack_mul_left, ← pack_add] at h
    exact congrFun (pack_injective hli h) r
  · refine le_of_eq_of_le ?_ hw.2
    congr 1
    ext i
    simp only [agreementLoss, mem_filter, hset, mem_interleavedAgreementLoss, hne, exists_or]

end Packing

section Bound

/-- With one point of shared agreement loss, few shared challenges are exceptional.

The number `t` of rows is arbitrary.
Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
Take agreement threshold `⌈(√ρ + η) n⌉`, row degree at most `d` and loss one.
At most `4 q / η + 2¹⁴ n² / (ρ³ η¹⁰)` challenges then have an exceptional tuple. -/
theorem exists_interleavedAffineExceptional_finset_card_le [Fintype F] (domain : ι ↪ F)
    (f g : Fin t → ι → F) {d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι)
    (hη : 0 < η) (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    ∃ S : Finset (F × F), (S.card : ℝ) ≤ 4 * Fintype.card F / η +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 / (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10) ∧
      ∀ c ∉ S, ∀ P, ¬ IsInterleavedAffineExceptional domain f g d
        ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 c.1 c.2 P := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- Without rows, the empty witness tuples lose no point.
    refine ⟨∅, ?_, fun c _ P hP ↦ hP.2.2 P P (fun r ↦ r.elim0) (fun r ↦ r.elim0)
      ⟨fun r ↦ r.elim0, by simp [interleavedAgreementLoss]⟩⟩
    rw [Finset.card_empty, Nat.cast_zero]
    exact add_nonneg (div_nonneg (by positivity) hη.le) (by positivity)
  · have : NeZero t := ⟨ht.ne'⟩
    let E := FiniteField.Extension F (ringChar F) t
    let b := FiniteField.Extension.finBasis F t
    obtain ⟨S, hS, hgood⟩ := exists_affineExceptional_finset_card_map_le
      (domain.trans ⟨algebraMap F E, (algebraMap F E).injective⟩) (fun i ↦ ∑ r, f r i • b r)
      (fun i ↦ ∑ r, g r i • b r) ⟨algebraMap F E, (algebraMap F E).injective⟩ hd hdn hη hη1 hn
    exact ⟨S, hS, fun c hc P hP ↦ hgood c hc _ (hP.pack b)⟩

/-- With one point of shared loss, the error is at most `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

The number `t` of rows is arbitrary.
Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `⌈(√ρ + η) n⌉`. -/
theorem interleavedAffineMcaError_le [Fintype F] (domain : ι ↪ F) (t : ℕ) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    interleavedAffineMcaError domain t d ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal (4 / (η * Fintype.card F) + 2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
        (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (interleavedAffineMcaError_le_of_forall_exists domain fun f g ↦
    exists_interleavedAffineExceptional_finset_card_le domain f g hd hdn hη hη1 hn).trans
      (le_of_eq ?_)
  congr 1
  field_simp

end Bound

end ReedSolomon
