/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.CommitmentScheme.KZG.Algebra
import ArkLib.CommitmentScheme.KZG.Sampling
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Lagrange
import ArkLib.ToCompPoly.Univariate.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# The KZG Polynomial Commitment Scheme

This file defines the KZG polynomial commitment scheme and instantiates it as a
functional commitment scheme. Correctness and security proofs live in sibling files.

## Notation

* `Groups.PowerSrs.generate` builds the prover and verifier structured reference strings.
* `commit`, `generateOpening`, and `verifyOpening` are the concrete KZG operations.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I.,
  *Constant-Size Commitments to Polynomials and Their Applications*][KZG10]
-/

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

/-- To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of
maximum degree `n`), we compute: `∏ i : Fin (n + 1), srs[i] ^ (p.coeff i)`. -/
def commit (srs : Vector G₁ (n + 1)) (coeffs : Fin (n + 1) → ZMod p) : G₁ :=
  ∏ i : Fin (n + 1), srs[i] ^ (coeffs i).val

/-- To generate an opening proving that a polynomial `poly` has a certain evaluation at `z`,
  we return the commitment to the polynomial `q(X) = (poly(X) - poly.eval z) / (X - z)` -/
def generateOpening [Fact (Nat.Prime p)] (srs : Vector G₁ (n + 1))
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) : G₁ :=
    letI poly : CPolynomial (ZMod p) := CPolynomial.ofFn coeffs
    letI q : CPolynomial (ZMod p) := divByMonic (poly - C (eval z poly)) (X - C z)
    commit srs (fun i : Fin (n + 1) => q.coeff i)

/-- To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed
evaluation `v`, we use the pairing to check "in the exponent" that `p(a) - p(z) = q(a) * (a - z)`,
  where `p` is the polynomial and `q` is the quotient of `p` at `z` -/
def verifyOpening (verifySrs : Vector G₂ 2) (commitment : G₁) (opening : G₁)
    (z : ZMod p) (v : ZMod p) : Bool :=
  pairing (commitment / g₁ ^ v.val) (verifySrs[0]) =
    pairing opening (verifySrs[1] / g₂ ^ z.val)

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] [Fact (0 < p)] in
/-- The commitment to a mathlib polynomial `poly` of maximum degree `n` is equal to
`g₁ ^ (poly.1.eval a).val` -/
theorem commit_eq {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : Polynomial.degreeLT (ZMod p) (n + 1)) :
    commit (Groups.PowerSrs.tower g₁ a n) (Polynomial.degreeLTEquiv _ _ poly)
      = g₁ ^ (poly.1.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁ ^ a = g₁ ^ b ↔ g₁ ^ (a : ℤ) = g₁ ^ (b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, Groups.PowerSrs.tower, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
    Polynomial.eval_eq_sum_degreeLTEquiv poly.property,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]
  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd
  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp only [ordp, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_val, Subtype.coe_eta,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_sum,
    Int.cast_mul, Int.cast_pow]
    apply Fintype.sum_congr
    intro x
    exact mul_comm _ _

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] [Fact (0 < p)] in
/-- The commitment to a computable polynomial (CPolynomial) `poly` of
maximum degree `n` is equal to `g₁ ^ (poly.eval a).val`. -/
theorem commit_eq_c_polynomial {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : CPolynomial (ZMod p)) (hn : poly.degree ≤ n) :
    commit (Groups.PowerSrs.tower g₁ a n)
      ((coeff poly) ∘ Fin.val)
      = g₁ ^ (poly.eval a).val := by
  have h_mem : poly.toPoly ∈ Polynomial.degreeLT (ZMod p) (n + 1) := by
    rw [Polynomial.mem_degreeLT, ← degree_toPoly]
    exact lt_of_le_of_lt hn (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  rw [show poly.eval a = poly.toPoly.eval a from eval_toPoly a poly]
  rw [show ((coeff poly) ∘ Fin.val : Fin (n + 1) → ZMod p) =
      Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨poly.toPoly, h_mem⟩ from by
    ext i; simp only [Function.comp_apply, Polynomial.degreeLTEquiv]; exact coeff_toPoly poly i]
  exact commit_eq hpG1 ⟨poly.toPoly, h_mem⟩

omit [DecidableEq Gₜ] [DecidableEq G₁] [Fact (0 < p)] in
/-- Linearity of the pairing in the first argument, written multiplicatively. -/
lemma lin_fst (g₁ : G₁) (g₂ : G₂) (a : ℤ) :
    a • (pairing g₁ g₂) = pairing (g₁ ^ a) g₂ := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul (g₁ ^ a)) (Additive.ofMul g₂)
  simp [ofMul_zpow]

omit [DecidableEq Gₜ] [DecidableEq G₁] [Fact (0 < p)] in
/-- Linearity of the pairing in the second argument, written multiplicatively. -/
lemma lin_snd (g₁ : G₁) (g₂ : G₂) (a : ℤ) :
    a • (pairing g₁ g₂) = pairing g₁ (g₂ ^ a) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul g₁) (Additive.ofMul (g₂ ^ a))
  simp [ofMul_zpow]

omit [Fact (0 < p)] in
/-- Powers with exponents congruent modulo `p` agree in a group of prime order `p`. -/
lemma mod_p_eq (x y : ℤ) (g : G) (hxy : x ≡ y [ZMOD p]) : g ^ x = g ^ y := by
  have hordg : g = 1 ∨ orderOf g = p := by
    have ord_g_dvd : orderOf g ∣ p := by
      have hc : Nat.card G = p := (PrimeOrderWith.hCard : Nat.card G = p)
      simpa [hc] using (orderOf_dvd_natCard g)
    have hdisj : orderOf g = 1 ∨ orderOf g = p := (Nat.dvd_prime hp.out).1 ord_g_dvd
    simpa [orderOf_eq_one_iff] using hdisj
  rcases hordg with ord1 | ordp
  · simp [ord1]
  · have hxmy : (orderOf g : ℤ) ∣ x - y := by
      have hxmy_p : (p : ℤ) ∣ x - y := by
        simpa using (Int.modEq_iff_dvd.mp hxy.symm)
      simpa [ordp] using hxmy_p
    exact (orderOf_dvd_sub_iff_zpow_eq_zpow).1 hxmy

omit [Fact (0 < p)] in
/-- Additive form of `mod_p_eq`. -/
lemma mod_p_eq_additive (x y : ℤ) (g : Additive G) (hxy : x ≡ y [ZMOD p]) :
    x • g = y • g := by
  have hxyeq : (Additive.toMul g) ^ x = (Additive.toMul g) ^ y :=
    mod_p_eq (G := G) (p := p) (g := (Additive.toMul g)) x y hxy
  simpa [ofMul_toMul, ofMul_zpow] using congrArg Additive.ofMul hxyeq

omit [Fact (0 < p)] [DecidableEq G₁] in
/-- Extract the exponent equation enforced by a successful KZG opening verification. -/
lemma verify_opening_equation (α₁ β₁ τ cm prf₁ : ZMod p) (c pf₁ : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hpair : pairing g₁ g₂ ≠ 0) (hcm : c = g₁ ^ cm.val)
    (hprf : pf₁ = g₁ ^ prf₁.val)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 c pf₁ α₁ β₁) :
    cm - β₁ = prf₁ * (τ - α₁) := by
    simp only [verifyOpening, decide_eq_true_eq] at hverify₁
    rw [hsrs] at hverify₁
    simp only [Groups.PowerSrs.generate, Groups.PowerSrs.tower, Nat.reduceAdd, Vector.getElem_ofFn,
      pow_zero, pow_one] at hverify₁
    rw [hcm, hprf] at hverify₁
    simp_rw [← zpow_natCast_sub_natCast, ← zpow_natCast, ← lin_snd, ← lin_fst,
      smul_smul] at hverify₁
    have hne : Additive.toMul (pairing g₁ g₂ : Additive Gₜ) ≠ 1 := hpair
    have hordE : orderOf (Additive.toMul (pairing g₁ g₂ : Additive Gₜ)) = p := by
      have hdvd := orderOf_dvd_natCard (G := Gₜ)
        (Additive.toMul (pairing g₁ g₂ : Additive Gₜ))
      rw [PrimeOrderWith.hCard] at hdvd
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hne
      · exact hp'
    have hdvd : (↑(orderOf (Additive.toMul (pairing g₁ g₂ : Additive Gₜ))) : ℤ) ∣
        ((↑cm.val - ↑β₁.val : ℤ) - ((↑τ.val - ↑α₁.val) * ↑prf₁.val)) :=
      orderOf_dvd_sub_iff_zpow_eq_zpow.mpr (congrArg Additive.toMul hverify₁)
    rw [hordE] at hdvd
    have hcast := ((ZMod.intCast_eq_intCast_iff_dvd_sub ((↑τ.val - ↑α₁.val) *
      ↑prf₁.val : ℤ) (↑cm.val - ↑β₁.val : ℤ) p).mpr hdvd).symm
    push_cast [ZMod.natCast_zmod_val] at hcast
    rw [_root_.mul_comm] at hcast
    exact hcast

omit [Fact (0 < p)] [DecidableEq G₁] in
/-- Solve the exponent equation from `verify_opening_equation` for the proof exponent. -/
lemma verify_opening_prf_equation (α₁ β₁ τ cm prf₁ : ZMod p) (c pf₁ : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
  (hpair : pairing g₁ g₂ ≠ 0)
  (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    srs.2 c pf₁ α₁ β₁)
  (hcm : c = g₁ ^ cm.val) (hprf : pf₁ = g₁ ^ prf₁.val) (hτα : τ ≠ α₁) :
    prf₁ = (cm - β₁) / (τ - α₁) := by
  have h := verify_opening_equation pairing α₁ β₁ τ cm prf₁ c pf₁ srs hsrs hpair hcm
    hprf hverify₁
  rw [h, mul_div_cancel_right₀ prf₁ (sub_ne_zero.mpr hτα)]

open Commitment

/-- Local oracle interface for evaluating coefficient vectors as computable polynomials. -/
local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

/-- The KZG instantiated as a **(functional) commitment scheme**.

  The scheme takes a pregenerated structured reference string (srs) for the
  committer and the verifier (generated by `Groups.PowerSrs.generate`).

  - `commit` : a function that commits to an `n + 1`-tuple of coefficients `coeffs`
  (corresponding to a polynomial of maximum degree `n`)
  - `opening` : a non-interactive reduction (i.e. solely the committer sends a single
  message) to prove the evaluation of the committed polynomial at a point `z`. The
  message from the prover is the witness for the evaluation.
-/
def kzg :
    Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
    (Vector G₁ (n + 1) × Vector G₂ 2)
    (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩ where
  keygen := do
    let a ← Groups.sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a
    return (srs, srs)
  commit := fun ck coeffs => return (commit ck.1 coeffs, ())
  opening := fun (ck, vk) => {
    prover := {
      PrvState := fun
        | 0 => (Fin (n + 1) → ZMod p) × ZMod p
        | _ => Unit

      input := fun ⟨⟨commitment, z, v⟩, ⟨coefficients, _⟩⟩ =>
        (coefficients, z)

      sendMessage := fun ⟨0, _⟩ => fun (coefficients, z) => do
        let opening := generateOpening ck.1 coefficients z
        return (opening, ())

      receiveChallenge := fun ⟨i, h⟩ => by
        have : i = 0 := Fin.eq_zero i
        subst this
        nomatch h

      output := fun _ => return (true, ())
    }

    verifier := {
      verify := fun ⟨commitment, z, v⟩ transcript => do
        let opening : G₁ := transcript ⟨0, by decide⟩
        return verifyOpening (g₁ := g₁) (g₂ := g₂) pairing vk.2 commitment opening z
          (v : ZMod p)
    }
  }


end CommitmentScheme

end KZG
