/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleFieldExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Uniform

/-!
# Capacity list bounds for the actual physical decoder output

Exact output membership and duplicate freedom identify the length of the supplied coefficient
list with the cardinality of the actual agreeing polynomial set. The original capacity list
bounds therefore apply to this same output, including zero. No new output is selected, and no
executable instruction or cost claim is added. This module uses the underlying list-bound owner
results without importing the capacity capstone, which can import this bridge in turn.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityOutputBounds

open Polynomial JetHornerMachine SeparateSampleFieldExecution ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}

/-- The given physical output length equals the exact agreeing-message set's extended cardinality.
The polynomial map is duplicate-free, so this equality counts the physical vectors. -/
theorem length_eq_encard (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (he : ExactOutput domain received k A out) :
    (out.length : ℕ∞) = (agreeingPolynomials domain k A received).encard := by
  classical
  have hset : (fun p : MessagePolynomial F k ↦ (p : F[X])) ''
      agreeingPolynomials domain k A received =
      ((out.map coefficientPolynomial).toFinset : Set F[X]) := by
    ext f
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (he.2.2.1 _).mpr ⟨Polynomial.mem_degreeLT.mp p.property, hp⟩
    · intro hf
      obtain ⟨hd, ha⟩ := (he.2.2.1 f).mp hf
      exact ⟨⟨f, Polynomial.mem_degreeLT.mpr hd⟩, ha, rfl⟩
  have hcard : ((out.map coefficientPolynomial).toFinset.card : ℕ∞) =
      (agreeingPolynomials domain k A received).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard, ← hset]
    exact Subtype.val_injective.encard_image _
  simpa only [List.toFinset_card_of_nodup he.1, List.length_map] using hcard

/-- The same physical length also equals the natural cardinality of the agreeing set. -/
theorem length_eq_ncard (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (he : ExactOutput domain received k A out) :
    out.length = (agreeingPolynomials domain k A received).ncard := by
  have h := congrArg ENat.toNat (length_eq_encard domain received out he)
  simpa [Set.ncard_def] using h

/-- Exact physical output is empty whenever the threshold exceeds the number of coordinates. -/
theorem oversized_empty (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (he : ExactOutput domain received k A out) (hA : n < A) : out = [] := by
  have hc := length_eq_encard domain received out he
  rw [agreeingPolynomials_eq_empty_of_card_lt (by simpa using hA) received] at hc
  simpa using hc

/-- Any exact small-polynomial output satisfying the exact physical-output contract inherits
the uniform first-order list bound from gap `6/25`.  This theorem only bounds the length of an
already supplied exact output; it does not select interpolation parameters or alter the
executable decoder's regime. -/
theorem uniformFirstOrder_length_le (delta : ℝ) (hdelta : (6 / 25 : ℝ) ≤ delta)
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (hn : 23 ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + delta * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F)
    (he : ExactOutput domain received k A out) :
    out.length ≤ 307 * n := by
  by_cases hAn : A ≤ n
  · have hgapUniform : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hmul := mul_le_mul_of_nonneg_right hdelta hnnonneg
      linarith
    obtain ⟨list, hlist, hcard⟩ := exists_uniformFirstOrder_list
      n k A domain received (by omega) hk hAn hgapUniform hchar
    have hsame : (out.map coefficientPolynomial).toFinset = list := by
      ext P
      simp only [List.mem_toFinset]
      rw [he.2.2.1 P, hlist P]
      simp [closePolynomialSet, polynomialAgreementSet, Code.agree, evalOnPoints]
      tauto
    calc
      out.length = (out.map coefficientPolynomial).length := by simp
      _ = (out.map coefficientPolynomial).toFinset.card :=
        (List.toFinset_card_of_nodup he.1).symm
      _ = list.card := congrArg Finset.card hsame
      _ ≤ 307 * n := hcard
  · rw [oversized_empty domain received out he (lt_of_not_ge hAn)]
    simp

/-- The original gap regimes bound the same supplied exact coefficient-vector output.
The gap-only d,m,N choices and the reduced large-field threshold are unchanged. -/
theorem capacity_output_bounds (delta : ℝ) (hdelta : 0 < delta) (_hOne : delta < 1) :
    let d : ℕ := if (1 / 4 : ℝ) ≤ delta then 0
      else Nat.ceil (Real.exp (((27 : ℝ) / 10) / delta))
    let m : ℕ := Nat.ceil (100 * (d : ℝ) ^ 2 *
      ∑ i ∈ Finset.range (d - 1), (1 : ℝ) / (i + 1))
    let N : ℕ := if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m
    ∀ n k q A : ℕ, N ≤ n → 0 < k → k ≤ n → (hq : q.Prime) → n ≤ q →
      (k : ℝ) + delta * n ≤ A → A ≤ 2 * n →
      let : Fact q.Prime := ⟨hq⟩
      ∀ (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (out : List (List (ZMod q))),
        ExactOutput domain received k A out →
        (n < A → out = []) ∧
        ((1 / 2 : ℝ) ≤ delta → out.length ≤ 1) ∧
        ((1 / 4 : ℝ) ≤ delta → out.length < n) ∧
        (delta < (1 / 4 : ℝ) → out.length ≤ 4 * m * q ^ (2 * d) ∧
          (2 * (m * A + d - max k ⌊delta * (n : ℝ) / 2⌋₊) ≤ q →
            out.length ≤ 4 * m * q ^ d)) := by
  let d := capacityDerivativeOrder delta
  let m := weightedSupportMultiplicity delta
  change ∀ n k q A : ℕ, (if (1 / 4 : ℝ) ≤ delta then 1 else 8 * m) ≤ n → _
  by_cases hquarter : (1 / 4 : ℝ) ≤ delta
  · intro n k q A _hn hk hkn hq hnq hA _hAupper
    let : Fact q.Prime := ⟨hq⟩
    dsimp only
    intro domain received out he
    have hthreshold := (agreementThreshold_le_iff_real hdelta.le n k A).mpr hA
    have hmono := Set.encard_mono (agreeingPolynomials_antitone domain k received hthreshold)
    have hc := length_eq_encard domain received out he
    refine ⟨oversized_empty domain received out he, ?_, ?_, ?_⟩
    · intro hhalf
      have h := hmono.trans (agreeingPolynomials_encard_le_one_of_half hhalf domain hk hkn received)
      rw [← hc] at h
      exact_mod_cast h
    · intro _hquarter
      have h := hmono.trans_lt (agreeingPolynomials_encard_lt_blockLength_of_quarter
        hquarter domain (hk.trans_le hkn) hk hkn received)
      rw [← hc] at h
      exact_mod_cast h
    · intro hsmall
      exact (not_lt_of_ge hquarter hsmall).elim
  · have hsmall : delta < (1 / 4 : ℝ) := lt_of_not_ge hquarter
    intro n k q A hn hk hkn hq hnq hA _hAupper
    let : Fact q.Prime := ⟨hq⟩
    dsimp only
    intro domain received out he
    have hblock : 8 * weightedSupportMultiplicity delta ≤ n := by
      simpa only [if_neg hquarter] using hn
    obtain ⟨⟨certificate⟩, hlarge⟩ := weightedSupport_capacity_list_bound_four_mul delta hdelta
      hsmall n k q hblock hk hkn hq hnq domain
    have hthreshold := (agreementThreshold_le_iff_real hdelta.le n k A).mpr hA
    have hmono := Set.encard_mono (agreeingPolynomials_antitone domain k received hthreshold)
    have hc := length_eq_encard domain received out he
    refine ⟨oversized_empty domain received out he, ?_, ?_, ?_⟩
    · intro hhalf
      linarith
    · intro hquarter'
      exact (hquarter hquarter').elim
    · intro _hsmall
      refine ⟨?_, ?_⟩
      · change out.length ≤ 4 * m * q ^ (2 * d)
        exact_mod_cast hc.le.trans (hmono.trans (certificate.pointwiseListBound received).1)
      · intro hfield
        have hbudget : LargeFieldCondition delta n k q d m := by
          apply le_trans _ hfield
          exact Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right
            (Nat.add_le_add_right (Nat.mul_le_mul_left m hthreshold) d) _)
        obtain ⟨largeCertificate⟩ := hlarge hbudget
        change out.length ≤ 4 * m * q ^ d
        exact_mod_cast hc.le.trans (hmono.trans (largeCertificate.pointwiseListBound received).1)

end ReedSolomon.ListDecoding.CapacityOutputBounds
