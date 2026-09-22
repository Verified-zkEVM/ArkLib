/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact power agreement for Reed–Solomon codes

A tuple `w : Fin (ℓ + 1) → ι → F` of received words is batched by one challenge `z` into
`i ↦ ∑ t, z ^ t * w t i`. A polynomial `Q` of degree below `k` close to the batched word has
*exact power agreement* if `Q = ∑ t, z ^ t • P t` for polynomials `P t` of degree below `k`, and
the coordinates where `Q` agrees with the batched word are exactly the coordinates where every
`P t` agrees with `w t`. This file states that property and its uniform version in polynomial
form, and identifies them with the code-level predicates `Code.HasExactAgreement` and
`Code.UniformExactAgreement` for the Reed–Solomon code and the batching map
`CoreDefinitions.univariatePowersGenerator F ℓ`.

The identification needs no relation between `k` and the agreement threshold or the block
length. Codeword witnesses give polynomial witnesses whose evaluations are correct; if `k`
exceeds the number of evaluation points, the polynomial identity `Q = ∑ t, z ^ t • P t` can
still fail, and it is repaired by adding the difference to `P 0`, whose weight is `z ^ 0 = 1`
(`exists_powerBatchedPolynomial_eq`).

The code-level characterizations let the counting and transfer theorems of
`ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` apply to Reed–Solomon statements. The
interleaved statements are in `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.

## Main definitions

* `ReedSolomon.powerBatchedWord`, `ReedSolomon.powerBatchedPolynomial`: batching of received
  words and of message polynomials.
* `ReedSolomon.commonCurveAgreementSet`: coordinates where every `P t` agrees with `w t`.
* `ReedSolomon.HasExactPowerAgreement`: exact power agreement, with the challenge and the
  candidate polynomial in an extension field `E` given by `φ : F →+* E`.
* `ReedSolomon.UniformExactPowerAgreement`: one exceptional set of at most `e` challenges for
  every candidate with at least `L` agreements.

## Main statements

* `ReedSolomon.determinedByAgreement_code`: Reed–Solomon codewords of message length `k` are
  determined by `a ≥ k` agreements.
* `ReedSolomon.exists_powerBatchedPolynomial_eq`: a codeword decomposition of a polynomial's
  evaluations lifts to a polynomial decomposition.
* `ReedSolomon.uniformExactPowerAgreement_singleton`: a single received word has uniform exact
  power agreement with no exceptional challenge.
* `ReedSolomon.hasExactPowerAgreement_id_iff_hasExactAgreement` and
  `ReedSolomon.uniformExactPowerAgreement_iff_uniformExactAgreement`: the polynomial predicates
  are the code-level predicates for `univariatePowersGenerator`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions

noncomputable section

section Batching

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The received word obtained by batching the words `w t` with the powers `z ^ t` of one
challenge: `i ↦ ∑ t, z ^ t * w t i`. -/
def powerBatchedWord (w : Fin (ℓ + 1) → ι → F) (z : F) : ι → F :=
  fun i ↦ ∑ t, z ^ t.val * w t i

/-- The combination `∑ t, z ^ t • P t` of message polynomials. -/
def powerBatchedPolynomial (P : Fin (ℓ + 1) → F[X]) (z : F) : F[X] :=
  ∑ t, z ^ t.val • P t

/-- Batching preserves the degree bound `degree < k`, including for `k = 0`. -/
theorem powerBatchedPolynomial_degree_lt (P : Fin (ℓ + 1) → F[X]) (z : F) (k : ℕ)
    (hP : ∀ t, (P t).degree < k) : (powerBatchedPolynomial P z).degree < k := by
  rw [← mem_degreeLT]
  exact Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (mem_degreeLT.mpr (hP t))

/-- Evaluation commutes with batching. -/
theorem powerBatchedPolynomial_eval (P : Fin (ℓ + 1) → F[X]) (z x : F) :
    (powerBatchedPolynomial P z).eval x = ∑ t, z ^ t.val * (P t).eval x := by
  simp [powerBatchedPolynomial, eval_finsetSum]

/-- The coordinates where every polynomial `P t` agrees with its received word `w t`. -/
def commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ t, (P t).eval (domain i) = w t i

/-- Coordinate `i` is in `commonCurveAgreementSet domain w P` exactly when every `P t` evaluates
to `w t i` at `domain i`. -/
@[simp] theorem mem_commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) (i : ι) :
    i ∈ commonCurveAgreementSet domain w P ↔ ∀ t, (P t).eval (domain i) = w t i := by
  simp [commonCurveAgreementSet]

/-- The batched word is the combination of the words `w t` under
`univariatePowersGenerator F ℓ`. -/
theorem powerBatchedWord_eq_sum {F : Type} [Field F] (w : Fin (ℓ + 1) → ι → F) (z : F) :
    powerBatchedWord w z = fun i ↦ ∑ t, univariatePowersGenerator F ℓ z t • w t i := rfl

end Batching

section Exact

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E] {ℓ : ℕ}

/-- **Exact power agreement.** The polynomial `Q` over `E` is `∑ t, z ^ t • (P t).map φ` for
message polynomials `P t` over `F` of degree below `k`, and the coordinates where `Q` agrees with
the batched received word are exactly those where every `P t` agrees with `w t`.

The equality of agreement sets is the substance: it says that `Q` has no agreement beyond the
common agreement of the constituents. The embedding `φ` allows the challenge and `Q` to live in an
extension field while the messages and received words stay over `F`; the Reed–Solomon statements
in this file use `φ = RingHom.id F`. -/
def HasExactPowerAgreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (k : ℕ)
    (z : E) (Q : E[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
    Q = powerBatchedPolynomial (fun t ↦ (P t).map φ) z ∧
    polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
        (powerBatchedWord (fun t i ↦ φ (w t i)) z) Q =
      commonCurveAgreementSet domain w P

/-- **Uniform exact power agreement.** One set `bad` of at most `e` challenges, chosen after the
received words `w`, such that every challenge `z ∉ bad` and every polynomial `Q` of degree below
`k` with at least `L` agreements with the batched word has exact power agreement.

The bad set does not depend on `Q`; this quantifier order is what the interleaved transfer
needs. -/
def UniformExactPowerAgreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k L e : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ e ∧ ∀ z ∉ bad, ∀ Q : F[X], Q.degree < k →
    L ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
    HasExactPowerAgreement domain w (RingHom.id F) k z Q

/-- With `φ = RingHom.id F`, exact power agreement is stated over `F` directly: `Q` is
`∑ t, z ^ t • P t` and its agreement set with `powerBatchedWord w z` is the common agreement set
of the `P t`. -/
theorem hasExactPowerAgreement_id_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) (z : F)
    (Q : F[X]) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q ↔
      ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧ Q = powerBatchedPolynomial P z ∧
        polynomialAgreementSet domain (powerBatchedWord w z) Q =
          commonCurveAgreementSet domain w P := by
  have hdomain : domain.trans ⟨RingHom.id F, (RingHom.id F).injective⟩ = domain :=
    Function.Embedding.ext fun _ ↦ rfl
  simp only [HasExactPowerAgreement, Polynomial.map_id, RingHom.id_apply, hdomain]

/-- A single received word has uniform exact power agreement with no exceptional challenge, for
every degree bound `k` and agreement threshold `L`: the witness is `P 0 = Q`. -/
theorem uniformExactPowerAgreement_singleton (domain : ι ↪ F) (w : Fin 1 → ι → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, fun z _ Q hQ _ ↦ ?_⟩
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [powerBatchedWord]

end Exact

section CodeLevel

variable {F : Type} {ι : Type*} [Field F] {ℓ : ℕ}

/-- **Reed–Solomon codewords are determined by `k` agreements.** Two codewords of the code of
message length `k` that agree on at least `a ≥ k` coordinates are equal, since the difference of
their message polynomials has degree below `k` and at least `k` roots among distinct evaluation
points. The hypothesis `k ≤ a` is needed: for `a < k ≤ |ι|`, the code contains a nonzero codeword
vanishing on `a` chosen coordinates. -/
theorem determinedByAgreement_code (domain : ι ↪ F) {k a : ℕ} (hk : k ≤ a) :
    Code.DeterminedByAgreement (code domain k) a := by
  intro c hc c' hc' T hT hcT
  obtain ⟨p, hp, hpc⟩ := mem_code_iff_eval.mp hc
  obtain ⟨p', hp', hpc'⟩ := mem_code_iff_eval.mp hc'
  have hkT : ((k : ℕ) : WithBot ℕ) ≤ (T.card : WithBot ℕ) := by exact_mod_cast hk.trans hT
  have hpp : p = p' := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T)
    domain.injective.injOn (hp.trans_le hkT) (hp'.trans_le hkT) fun i hi ↦ by
      rw [hpc, hpc', hcT i hi]
  funext i
  rw [← hpc, ← hpc', hpp]

/-- **Polynomial decomposition from a codeword decomposition.** Let `Q` have degree below `k` and
let its evaluations be `∑ t, z ^ t * c' t i` for codewords `c' t` of the Reed–Solomon code of
message length `k`. Then there are polynomials `P t` of degree below `k` evaluating to `c' t`
with `Q = ∑ t, z ^ t • P t`.

When `k ≤ |ι|` the evaluations determine the polynomials and any choice of `P t` works. When
`k > |ι|` they do not, and the difference `Q - ∑ t, z ^ t • P t`, which vanishes on the domain,
is added to `P 0`; this uses that the weight of `P 0` is `z ^ 0 = 1`. So no relation between `k`
and `|ι|` is needed. -/
theorem exists_powerBatchedPolynomial_eq (domain : ι ↪ F) {k : ℕ} {z : F} {Q : F[X]}
    (hQ : Q.degree < k) {c' : Fin (ℓ + 1) → ι → F} (hc' : ∀ t, c' t ∈ code domain k)
    (hsum : ∀ i, Q.eval (domain i) = ∑ t, z ^ t.val * c' t i) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ t i, (P t).eval (domain i) = c' t i) ∧ Q = powerBatchedPolynomial P z := by
  choose P₀ hP₀ hP₀c using fun t ↦ mem_code_iff_eval.mp (hc' t)
  set D := Q - powerBatchedPolynomial P₀ z with hD
  have hDdeg : D ∈ degreeLT F k := Submodule.sub_mem _ (mem_degreeLT.mpr hQ)
    (mem_degreeLT.mpr (powerBatchedPolynomial_degree_lt P₀ z k hP₀))
  have hDeval (i : ι) : D.eval (domain i) = 0 := by
    rw [hD, eval_sub, powerBatchedPolynomial_eval, hsum]
    simp [hP₀c]
  refine ⟨fun t ↦ P₀ t + if t = 0 then D else 0, fun t ↦ ?_, fun t i ↦ ?_, ?_⟩
  · rw [← mem_degreeLT]
    refine Submodule.add_mem _ (mem_degreeLT.mpr (hP₀ t)) ?_
    split_ifs
    · exact hDdeg
    · exact Submodule.zero_mem _
  · dsimp only
    split_ifs <;> simp [hP₀c, hDeval]
  · simp only [powerBatchedPolynomial, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_zero, pow_zero, one_smul]
    change Q = powerBatchedPolynomial P₀ z + D
    rw [hD]
    ring

variable [Fintype ι] [DecidableEq F]

/-- **Exact power agreement is exact agreement for the code.** For a polynomial `Q` of degree
below `k`, exact power agreement at `z` (with `φ = RingHom.id F`) is `Code.HasExactAgreement`
for the Reed–Solomon code, the batching map `univariatePowersGenerator F ℓ`, and the codeword
of evaluations of `Q`.

From left to right, the witnesses are the evaluations of the `P t`. From right to left, the
codeword witnesses are lifted by `exists_powerBatchedPolynomial_eq`, which needs no bound
relating `k` and `|ι|`. -/
theorem hasExactPowerAgreement_id_iff_hasExactAgreement (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {k : ℕ} {z : F} {Q : F[X]} (hQ : Q.degree < k) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q ↔
      Code.HasExactAgreement (univariatePowersGenerator F ℓ) (code domain k) z w
        (evalOnPoints domain Q) := by
  constructor
  · rintro ⟨P, hP, hQP, hset⟩
    simp only [Polynomial.map_id] at hQP
    refine ⟨fun t ↦ evalOnPoints domain (P t), fun t ↦
      evalOnPoints_mem_code_of_degree_lt (hP t), ?_, fun i ↦ ?_⟩
    · funext i
      simp [evalOnPoints, hQP, powerBatchedPolynomial_eval]
    · have := congrArg (i ∈ ·) hset
      simpa [evalOnPoints, powerBatchedWord] using this
  · rintro ⟨c', hc', hcsum, hiff⟩
    obtain ⟨P, hP, hPc, hQP⟩ := exists_powerBatchedPolynomial_eq domain hQ hc' fun i ↦ by
      simpa [evalOnPoints] using congrFun hcsum i
    refine ⟨P, hP, by simpa using hQP, ?_⟩
    ext i
    have := hiff i
    simp only [evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, univariatePowersGenerator,
      smul_eq_mul] at this
    simp [powerBatchedWord, hPc, this]

/-- **Uniform exact power agreement is uniform exact agreement for the code.** The polynomial
statement `UniformExactPowerAgreement domain w k L e` is `Code.UniformExactAgreement` for the
Reed–Solomon code of message length `k` and the batching map `univariatePowersGenerator F ℓ`,
with the same threshold `L` and count `e`. No relation between `k` and `L` is needed. -/
theorem uniformExactPowerAgreement_iff_uniformExactAgreement (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {k L e : ℕ} :
    UniformExactPowerAgreement domain w k L e ↔
      Code.UniformExactAgreement (univariatePowersGenerator F ℓ) (code domain k) L e w := by
  constructor
  · rintro ⟨bad, hcard, hbad⟩
    refine ⟨bad, hcard, fun z hz c hc T hT hcT ↦ ?_⟩
    obtain ⟨Q, hQ, hQc⟩ := mem_code_iff_eval.mp hc
    have hc_eq : c = evalOnPoints domain Q := by
      funext i
      simp [evalOnPoints, hQc]
    subst hc_eq
    refine (hasExactPowerAgreement_id_iff_hasExactAgreement domain w hQ).mp
      (hbad z hz Q hQ (hT.trans (Finset.card_le_card fun i hi ↦ ?_)))
    rw [mem_polynomialAgreementSet]
    simpa [evalOnPoints, powerBatchedWord] using hcT i hi
  · rintro ⟨bad, hcard, hbad⟩
    refine ⟨bad, hcard, fun z hz Q hQ hL ↦ ?_⟩
    refine (hasExactPowerAgreement_id_iff_hasExactAgreement domain w hQ).mpr
      (hbad z hz _ (evalOnPoints_mem_code_of_degree_lt hQ) _ hL fun i hi ↦ ?_)
    rw [mem_polynomialAgreementSet] at hi
    simpa [evalOnPoints, powerBatchedWord] using hi

end CodeLevel

end

end ReedSolomon
