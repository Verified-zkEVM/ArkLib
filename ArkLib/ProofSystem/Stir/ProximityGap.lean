/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
module

public import ArkLib.Data.CodingTheory.Basic.DecodingRadius
public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.Basic.LinearCode
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
public import ArkLib.Data.CodingTheory.ReedSolomon
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# ArkLib.ProofSystem.Stir.ProximityGap

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-!
## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

/-- Theorem 4.1 of [ACFY24stir] (due to [BCIKS20]): taking the powers of a uniform `r ∈ F` as
  coefficients, the random linear combination is a proximity generator for `RS[F, ι, degree]`.

  Let `C = RS[F, ι, degree]`, with `0 < degree`, have rate `ρ = degree / |ι|` and let
  `B⋆(ρ) = √ρ`. For every
  `δ ∈ (0, 1 - B⋆(ρ))` and `f₀, …, f_{m-1} : ι → F`, if
  `Pr_{r ← F}[δᵣ(∑ⱼ rʲ * fⱼ, C) ≤ δ] > err⋆(degree, ρ, δ, m)`,
  then there is `S ⊆ ι` with `|S| ≥ (1 - δ) * |ι|` such that every `fᵢ` agrees on `S` with some
  codeword `u ∈ C`.

  The paper numbers the functions from `1` and weights `fⱼ` by `r^{j-1}`; here they are numbered
  from `0`, so the weight of `fⱼ` is `rʲ`.

  The hypothesis `0 < degree` is implicit in the paper: `err⋆` divides by `ρ`. For `degree = 0`
  the convention `x / 0 = 0` makes `err⋆` zero and the statement false. -/
lemma proximity_gap
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F}
  (hdegPos : 0 < degree) (hδPos : 0 < δ)
  (hδLt : δ < 1 - Bstar (LinearCode.rate (code φ degree)))
  (hProb :
    Pr{let r ← $ᵗ F}[δᵣ((fun x => ∑ j : Fin m, r ^ (j : ℕ) * f j x), code φ degree) ≤ δ] >
      ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
  ∃ S : Finset ι,
    S.card ≥ (1 - δ) * (Fintype.card ι) ∧
    ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x := by
  classical
  cases m with
  | zero =>
    refine ⟨Finset.univ, ?_, fun i => Fin.elim0 i⟩
    simp
  | succ k =>
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    have hproper : degree < Fintype.card ι := by
      by_contra h
      have hfull : Fintype.card ι ≤ degree := by omega
      have hrate : LinearCode.rate (code φ degree) = 1 := by
        rw [rateOfLinearCode_eq_min_div, min_eq_right hfull]
        exact div_self (by exact_mod_cast hn.ne')
      simp [Bstar, hrate] at hδLt
    have herr : proximityError F degree (LinearCode.rate (code φ degree)) δ (k + 1) =
        k * ProximityGap.errorBound δ degree φ := by
      by_cases hUD : δ ≤ (1 - LinearCode.rate (code φ degree)) / 2
      · have herror : ProximityGap.errorBound δ degree φ =
            Fintype.card ι / Fintype.card F := by
          simp [ProximityGap.errorBound, hUD]
        rw [herror]
        simp only [proximityError, ite_eq_left hUD, Nat.cast_add, Nat.cast_one,
          add_tsub_cancel_right]
        rw [rateOfLinearCode_eq_div hproper.le]
        push_cast
        have hd : (degree : ℝ≥0) ≠ 0 := by positivity
        have hn' : (Fintype.card ι : ℝ≥0) ≠ 0 := by positivity
        field_simp
      · have hJohnson : δ ∈ Set.Ioo
            ((1 - (LinearCode.rate (code φ degree) : ℝ≥0)) / 2)
            (1 - NNReal.sqrt (LinearCode.rate (code φ degree))) :=
          ⟨lt_of_not_ge hUD, hδLt⟩
        have herror : ProximityGap.errorBound δ degree φ =
            (degree : ℝ≥0) ^ 2 / ((2 * min
              (1 - NNReal.sqrt (LinearCode.rate (code φ degree)) - δ)
              (NNReal.sqrt (LinearCode.rate (code φ degree)) / 20)) ^ 7 * Fintype.card F) := by
          rw [ProximityGap.errorBound_eq_johnson hJohnson]
          rfl
        rw [herror]
        simp only [proximityError, ite_eq_right hUD, ite_eq_left hJohnson.2, Nat.cast_add,
          Nat.cast_one, add_tsub_cancel_right]
        ring
    have hcurve := ProximityGap.correlatedAgreement_affine_curves
      hdegPos hδPos (show δ < 1 - sqrtRate degree φ from hδLt) f
    have hword (r : F) : (fun x => ∑ j : Fin (k + 1), r ^ (j : ℕ) * f j x) =
        ∑ j : Fin (k + 1), r ^ (j : ℕ) • f j := by
      ext x
      simp
    have hprob' : Pr{let r ← $ᵗ F}[
        δᵣ(∑ j : Fin (k + 1), r ^ (j : ℕ) • f j, code φ degree) ≤ δ] >
        (k : ENNReal) * ProximityGap.errorBound δ degree φ := by
      simpa only [herr, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_natCast,
        hword] using hProb
    obtain ⟨S, hS, v, hv⟩ := hcurve hprob'
    refine ⟨S, hS, fun i => ⟨v i, (hv i).1, ?_⟩⟩
    intro x hx
    exact ((Finset.mem_filter.mp ((hv i).2 hx)).2).symm

end STIR
