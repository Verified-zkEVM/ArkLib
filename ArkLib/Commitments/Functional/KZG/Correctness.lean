/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.Commitments.Functional.KZG.Basic
public import ArkLib.OracleReduction.ProgramLogic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.OptionT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
-- `simp [coeff]` and `Raw.coeff`/`Raw.mk` need CompPoly's unexposed bodies.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Correctness of the KZG Polynomial Commitment Scheme

This file proves that the concrete KZG commitment, opening, and verification operations from
`KZG.Basic` satisfy the expected evaluation equation. It then lifts that algebraic statement to
`Commitment.perfectCorrectness` for the commitment-scheme interface.

## Notation

The main algebraic theorem is `KZG.correctness`; the interface-level theorem is
`KZG.CommitmentScheme.correctness`.

## References

This file proves correctness from the definitions.
-/

@[expose] public section

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ} -- the maximal degree of polynomials that can be committed to/opened.

/-- Conversion to mathlib polynomials commutes with division by a monic polynomial. -/
lemma to_poly_div_by_monic {p : ℕ} [Fact (Nat.Prime p)]
    (f q : CPolynomial (ZMod p)) (hq : q.toPoly.Monic) :
    (f.divByMonic q).toPoly = f.toPoly /ₘ q.toPoly :=
  CPolynomial.toPoly_divByMonic f q hq

omit [DecidableEq G₁] [Fact (0 < p)] in
/-- Algebraic correctness of one KZG opening for a coefficient vector. -/
theorem correctness (hpG1 : Nat.card G₁ = p) (n : ℕ) (a : ZMod p)
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) :
  let poly : CPolynomial (ZMod p) :=
    ⟨(Raw.mk (Array.ofFn coeffs)).trim, Raw.Trim.isCanonical_trim _⟩
  let v : ZMod p := eval z poly
  let srs : Vector G₁ (n + 1) × Vector G₂ 2 :=
    Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a
  let C : G₁ := commit srs.1 coeffs
  let opening : G₁ := generateOpening srs.1 coeffs z
  verifyOpening pairing (g₁ := g₁) (g₂ := g₂) srs.2 C opening z v := by
  intro poly v
  unfold verifyOpening Groups.PowerSrs.generate
  simp only [decide_eq_true_eq]
  -- helper facts for the proof
  -- coeffs is the finite coefficients map of poly
  have hcoeffs : coeffs = (coeff poly) ∘ Fin.val := by
    simp_all only [poly]
    ext x : 1
    simp only [Function.comp_apply, coeff]
    rw [Raw.Trim.coeff_eq_coeff]
    simp only [Raw.coeff, Raw.mk]
    have : ↑x < (Array.ofFn coeffs).size := by simp; omega
    simp [Array.getD]
    omega
  -- the (mathematical) degree of poly is at most n
  have hpdeg : degree poly ≤ n := by
    unfold CPolynomial.degree
    cases h : poly.val.size with
    | zero => exact bot_le
    | succ k =>
      simp only [Nat.cast_le]
      have hsz : poly.val.size ≤ n + 1 := by
        change (Raw.mk (Array.ofFn coeffs)).trim.size ≤ n + 1
        exact le_trans (Raw.Trim.size_le_size _) (by simp [Array.size_ofFn])
      omega
  -- expansion of (a-z) to Polynomial form
  have haz : (a - z) = eval a (X - C z) := by
    rw [eval_toPoly, CPolynomial.toPoly_sub, Polynomial.eval_sub, X_toPoly, C_toPoly,
      Polynomial.eval_X, Polynomial.eval_C]
  -- the polynomial form of (a-z) is monic
  have hmonic : Polynomial.Monic ((X : CPolynomial (ZMod p)) - C z).toPoly := by
    rw [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
    exact Polynomial.monic_X_sub_C z
  -- the proof
  -- restate the commitment as the evaluation of poly at a (C => g₁^poly(a))
  simp_rw [hcoeffs, commit_eq_c_polynomial hpG1 poly hpdeg]
  -- define q(X) := (poly(X) - poly(z)) / (X-z)
  -- and restate the opening as the evaluation of q at a (opening => g₁^q(a))
  simp_rw [generateOpening, ←hcoeffs]
  set q := (poly - C (eval z poly)).divByMonic (X - C z)
  have hqdeg : degree q ≤ n := by
    rw [degree_toPoly, to_poly_div_by_monic _ _ hmonic]
    apply le_trans (Polynomial.degree_divByMonic_le _ _)
    rw [CPolynomial.toPoly_sub, C_toPoly]
    apply le_trans (Polynomial.degree_sub_le _ _)
    apply max_le
    · rw [← degree_toPoly]; exact hpdeg
    · exact le_trans Polynomial.degree_C_le (by exact_mod_cast Nat.zero_le n)
  have hfun :
      (fun i ↦ q.coeff ↑i : Fin (n + 1) → ZMod p) = (coeff q) ∘ Fin.val := by
    rfl
  simp_rw [ofFn]
  change pairing (g₁ ^ (eval a poly).val / g₁ ^ v.val) (Groups.PowerSrs.tower g₂ a 1)[0] =
    pairing (commit (Groups.PowerSrs.tower g₁ a n) (fun i : Fin (n + 1) => q.coeff i) : G₁)
      ((Groups.PowerSrs.tower g₂ a 1)[1] / g₂ ^ z.val)
  rw [hfun]
  rw [commit_eq_c_polynomial hpG1 q hqdeg]
  -- evaluate the pairing linearly.
  -- e (g₁^poly(a) / g₂^poly(z), g₂)= e (g₁^q(a), g₂^a / g₂^(z))
  -- => (poly(a) - poly(z)) • e (g₁,g₂) = (q(a) * (a-z)) • e (g₁,g₂)
  simp only [Groups.PowerSrs.tower, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero, pow_one]
  simp_rw [← zpow_natCast_sub_natCast, ← zpow_natCast, ← lin_snd, ← lin_fst, smul_smul]
  -- eliminate the pairing and reason only about the exponents: poly(a) - poly(z) = q(a) * (a-z)
  apply mod_p_eq_additive
  refine (Int.modEq_iff_dvd).2 ?_
  let x : ℤ := (↑(eval a poly).val) - (↑v.val)
  let y : ℤ := (↑(a.val) - ↑(z.val)) * ↑(eval a q).val
  refine (Iff.mp (ZMod.intCast_eq_intCast_iff_dvd_sub (a := x) (b := y) (c := p))) ?_
  subst x y; simp only [ZMod.natCast_val, Int.cast_sub, ZMod.intCast_cast, ZMod.cast_id', id_eq,
    Int.cast_mul]
  -- unfold q to obtain the self canceling goal:
  -- poly(a) - poly(z) = (poly(a) - poly(z)) / (a-z) * (a-z)
  -- prove the goal using the eval isomorphism to mathlib Polynomials
  subst v q
  simp_rw [haz]
  simp_rw [eval_toPoly, to_poly_div_by_monic _ _ hmonic, CPolynomial.toPoly_sub,
    ←Polynomial.eval_mul, C_toPoly, X_toPoly]
  simp_rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    Polynomial.modByMonic_X_sub_C_eq_C_eval]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, sub_self, map_zero, sub_zero]


open Commitment

/-- Local oracle interface for evaluating coefficient vectors as computable polynomials. -/
local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section Correctness

omit [Fact (0 < p)] [DecidableEq G₁] in
/-- The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

After reducing the game to the possible outputs of the unsimulated computation, `prvcgen` walks
key generation, commitment and the one-message opening, and the verifier's pairing check at each
trapdoor is `KZG.correctness`. -/
theorem correctness (hpG1 : Nat.card G₁ = p) {g₁ : G₁} {g₂ : G₂}
    [SampleableType G₁] :
    Commitment.perfectCorrectness (pure ∅) (randomOracle)
    (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) := by
  intro data query
  simp only [ENNReal.coe_zero, tsub_zero]
  refine ge_of_eq ?_
  refine OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support _ _ _ _ ?_
  have : ProverOnly ({ dir := !v[.P_to_V], «Type» := !v[G₁] } : ProtocolSpec 1) :=
    { prover_first' := by simp }
  have hverify (τ : ZMod p) : verifyOpening pairing (g₁ := g₁) (g₂ := g₂) _ _ _ query
      (OracleInterface.answer data query) := KZG.correctness pairing hpG1 n τ data query
  simp only [kzg, Reduction.run_run_eq, Prover.run_of_prover_first, Verifier.run,
    OptionT.run_pure]
  prvcgen [Groups.sampleNonzeroZMod]
  simp [acceptRejectRel, hverify]

end Correctness

end CommitmentScheme

end KZG
