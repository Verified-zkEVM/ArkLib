/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalOutputSemantics
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Selection.CanonicalProof
/-!
# Exact polynomial membership through the actual base-output collector

Physical descent is derived from polynomial embedding, including all zero padding. The existing
acceptance and collector results are reused directly, without a new filtering program.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputProof

open Polynomial JetHornerMachine
open HiddenDerivative.StageRootsMachine (Record)

namespace Output
export CanonicalOutputMachine (guardInput result runFuel fuel workBound Configuration)
end Output

namespace Roots
export HiddenDerivative.CanonicalRootSelection (accepted selected polynomials)
end Roots

variable {F : Type*} [Field F] [DecidableEq F] {a b : F}

omit [DecidableEq F] in
/-- Base polynomial embedding is injective, including the zero polynomial. -/
theorem polynomial_embedding_injective :
    Function.Injective (Polynomial.map (algebraMap F (QuadraticAlgebra F a b))) :=
  Polynomial.map_injective _ (algebraMap F (QuadraticAlgebra F a b)).injective

omit [DecidableEq F] in
/-- An embedded polynomial forces every physical coefficient to descend, including padding. -/
theorem physical_descent (xs : List (QuadraticAlgebra F a b)) (f : F[X])
    (h : f.map (algebraMap F (QuadraticAlgebra F a b)) = coefficientPolynomial xs) :
    ∃ cs : List F, xs = cs.map (algebraMap F (QuadraticAlgebra F a b)) ∧
      coefficientPolynomial cs = f := by
  induction xs generalizing f with
  | nil =>
      have hf : f = 0 := polynomial_embedding_injective (a := a) (b := b) (by
        simpa [coefficientPolynomial] using h)
      exact ⟨[], rfl, by simp [hf, coefficientPolynomial]⟩
  | cons x xs ih =>
      have hx : algebraMap F (QuadraticAlgebra F a b) (f.coeff xs.length) = x := by
        have he := congrArg (fun p ↦ p.coeff xs.length) h
        simpa only [coeff_map, coeff_coefficientPolynomial_cons_length] using he
      let g := f - C (f.coeff xs.length) * X ^ xs.length
      have hg : g.map (algebraMap F (QuadraticAlgebra F a b)) = coefficientPolynomial xs := by
        simp only [g, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X, h, coefficientPolynomial_cons, hx]
        ring
      obtain ⟨cs, hcs, _hpoly⟩ := ih g hg
      have hxs : x :: xs = (f.coeff xs.length :: cs).map
          (algebraMap F (QuadraticAlgebra F a b)) := by rw [List.map_cons, hx, ← hcs]
      refine ⟨f.coeff xs.length :: cs, hxs, ?_⟩
      apply polynomial_embedding_injective (a := a) (b := b)
      rw [map_coefficientPolynomial, ← hxs]
      exact h.symm

variable [Fact (∀ r : F, r ^ 2 ≠ a + b * r)]

/-- Polynomial values of the existing collector's actual result specification. -/
noncomputable def basePolynomials (d w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b))) : List F[X] :=
  (Output.result d samples w k A rows records).map coefficientPolynomial

/-- One concrete acceptance emits exactly when guard, degree, agreement and embedding all hold. -/
theorem acceptance_polynomial_iff (d w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (record : Record (QuadraticAlgebra F a b)) (hwidth : record.coefficients.length = w)
    (hk : k ≤ w) {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (f : F[X]) :
    (∃ cs, CanonicalAcceptanceMachine.result (Output.guardInput d samples record)
      record.context.previous w k A (List.ofFn fun i ↦ (domain i, received i)) = some cs ∧
      coefficientPolynomial cs = f) ↔
    Roots.accepted d samples record = true ∧ f.degree < k ∧
      A ≤ Code.agree (evalOnPoints domain f) received ∧
      f.map (algebraMap F (QuadraticAlgebra F a b)) =
        coefficientPolynomial record.coefficients := by
  constructor
  · rintro ⟨cs, hcs, rfl⟩
    obtain ⟨hg, _hlen, hd, ha, he⟩ := CanonicalAcceptanceMachine.result_sound
      (Output.guardInput d samples record) record.context.previous w k A hwidth hk
      domain received cs hcs
    exact ⟨hg, hd, ha, he⟩
  · rintro ⟨hg, hd, ha, he⟩
    obtain ⟨bs, hbs, hbpoly⟩ := physical_descent record.coefficients f he
    have hn : CanonicalAcceptanceMachine.result (Output.guardInput d samples record)
        record.context.previous w k A (List.ofFn fun i ↦ (domain i, received i)) ≠ none := by
      apply (CanonicalAcceptanceMachine.result_ne_none_iff _ _ _ _ _ hwidth hk domain received).mpr
      exact ⟨hg, bs, hbs, by simpa only [hbpoly] using hd, by simpa only [hbpoly] using ha⟩
    cases hs : CanonicalAcceptanceMachine.result (Output.guardInput d samples record)
        record.context.previous w k A (List.ofFn fun i ↦ (domain i, received i)) with
    | none => exact False.elim (hn hs)
    | some cs =>
        obtain ⟨_hg, _hlen, _hd, _ha, hpoly⟩ := CanonicalAcceptanceMachine.result_sound
          (Output.guardInput d samples record) record.context.previous w k A hwidth hk
          domain received cs hs
        exact ⟨cs, rfl, polynomial_embedding_injective (hpoly.trans he.symm)⟩

/-- Exact base polynomial membership is canonical root membership plus degree and agreement. -/
theorem mem_basePolynomials_iff (d w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (f : F[X]) :
    f ∈ basePolynomials d w k A samples (List.ofFn fun i ↦ (domain i, received i)) records ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received ∧
      f.map (algebraMap F (QuadraticAlgebra F a b)) ∈ Roots.polynomials d samples records := by
  constructor
  · intro hm
    obtain ⟨cs, hcs, hpoly⟩ := List.mem_map.mp hm
    obtain ⟨record, hr, hacc⟩ := (CanonicalOutputMachine.mem_result_iff _ _ _ _ _ _ _ _).mp hcs
    obtain ⟨hg, hd, ha, he⟩ := (acceptance_polynomial_iff d w k A samples record
      (hwidth record hr) hk domain received f).mp ⟨cs, hacc, hpoly⟩
    exact ⟨hd, ha, List.mem_map.mpr ⟨record, List.mem_filter.mpr ⟨hr, hg⟩, he.symm⟩⟩
  · rintro ⟨hd, ha, hm⟩
    obtain ⟨record, hr, he⟩ := List.mem_map.mp hm
    obtain ⟨hr, hg⟩ := List.mem_filter.mp hr
    obtain ⟨cs, hacc, hpoly⟩ := (acceptance_polynomial_iff d w k A samples record
      (hwidth record hr) hk domain received f).mpr ⟨hg, hd, ha, he.symm⟩
    apply List.mem_map.mpr
    exact ⟨cs, (CanonicalOutputMachine.mem_result_iff _ _ _ _ _ _ _ _).mpr
      ⟨record, hr, hacc⟩, hpoly⟩

/-- The exact collector preserves polynomial uniqueness from canonical root selection. -/
theorem basePolynomials_nodup (d w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) (hk : k ≤ w) {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : (Roots.polynomials d samples records).Nodup) :
    (basePolynomials d w k A samples (List.ofFn fun i ↦ (domain i, received i)) records).Nodup := by
  induction records with
  | nil => simp [basePolynomials, CanonicalOutputMachine.result]
  | cons record records ih =>
      have htail : ∀ r ∈ records, r.coefficients.length = w := fun r hr ↦ hwidth r (by simp [hr])
      cases hg : Roots.accepted d samples record with
      | false =>
          have hntail : (Roots.polynomials d samples records).Nodup := by
            simpa [HiddenDerivative.CanonicalRootSelection.polynomials,
              HiddenDerivative.CanonicalRootSelection.selected, hg] using hn
          have hout := ih htail hntail
          have hguard := hg
          change HiddenDerivative.CanonicalGuardMachine.result (Output.guardInput d samples record)
            record.context.previous = false at hguard
          have hnone : CanonicalAcceptanceMachine.result (Output.guardInput d samples record)
              record.context.previous w k A (List.ofFn fun i ↦ (domain i, received i)) = none := by
            simp [CanonicalAcceptanceMachine.result, hguard]
          simpa [basePolynomials, CanonicalOutputMachine.result, hnone] using hout
      | true =>
          have hsplit : coefficientPolynomial record.coefficients ∉
              Roots.polynomials d samples records ∧
              (Roots.polynomials d samples records).Nodup := by
            simpa [HiddenDerivative.CanonicalRootSelection.polynomials,
              HiddenDerivative.CanonicalRootSelection.selected, hg] using hn
          have hout := ih htail hsplit.2
          cases ha : CanonicalAcceptanceMachine.result (Output.guardInput d samples record)
              record.context.previous w k A (List.ofFn fun i ↦ (domain i, received i)) with
          | none => simpa [basePolynomials, CanonicalOutputMachine.result, ha] using hout
          | some cs =>
              obtain ⟨_hg, _hlen, _hd, _hagree, hpoly⟩ := CanonicalAcceptanceMachine.result_sound
                (Output.guardInput d samples record) record.context.previous w k A
                (hwidth record (by simp)) hk domain received cs ha
              have hnot : coefficientPolynomial cs ∉ basePolynomials d w k A samples
                  (List.ofFn fun i ↦ (domain i, received i)) records := by
                intro hm
                have hroot := ((mem_basePolynomials_iff d w k A samples records htail hk
                  domain received _).mp hm).2.2
                rw [hpoly] at hroot
                exact hsplit.1 hroot
              simpa [basePolynomials, CanonicalOutputMachine.result, ha] using
                List.nodup_cons.mpr ⟨hnot, hout⟩

end ReedSolomon.ListDecoding.CanonicalOutputProof
