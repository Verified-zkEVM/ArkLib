/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SmallBlock.SmallBlockDecoderMachine
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.SmallBlock
public import ArkLib.Data.Polynomial.DegreeTruncationSemantics
/-!
# Exact exceptional-block decoding

The initial size is related to the materialized input by using `List.ofFn` on `Fin n` throughout.
Oversized thresholds give an empty result at any block length. For two coordinates, the actual
quarter-gap integer threshold leaves only dimension one and agreement two when feasible.
The charged leaf therefore works over every field, including characteristic two, without setup.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SmallBlockDecoderProof

open Polynomial JetHornerMachine SmallBlockDecoderMachine

variable {F : Type*} [Field F] [DecidableEq F]

/-- Exact polynomial and fixed-width vector specification, including both uniqueness statements. -/
def Exact {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (out : List (List F)) : Prop :=
  out.Nodup ∧ (out.map coefficientPolynomial).Nodup ∧
    (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
    (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧
      (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received)

private theorem empty_exact {n k A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (h : n < A) : Exact domain received k A [] := by
  have hno (f : F[X]) : ¬A ≤ Code.agree (evalOnPoints domain f) received := by
    have hb := Code.agree_le_card (u := evalOnPoints domain f) (v := received)
    simp only [Fintype.card_fin] at hb
    omega
  simp [Exact, hno]

private theorem full_two (domain : Fin 2 ↪ F) (received : Fin 2 → F) (f : F[X]) :
    2 ≤ Code.agree (evalOnPoints domain f) received ↔
      f.eval (domain 0) = received 0 ∧ f.eval (domain 1) = received 1 := by
  change 2 ≤ (Finset.univ.filter (fun i : Fin 2 ↦
    f.eval (domain i) = received i)).card ↔ _
  rw [Finset.card_filter]
  simp only [Fin.sum_univ_two]
  split_ifs <;> simp_all

private theorem constant_two (domain : Fin 2 ↪ F) (received : Fin 2 → F) (f : F[X]) :
    f.degree < 1 ∧ 2 ≤ Code.agree (evalOnPoints domain f) received ↔
      f = C (received 0) ∧ received 0 = received 1 := by
  rw [full_two]
  constructor
  · rintro ⟨hd, h0, h1⟩
    have he : f = C (f.coeff 0) := by
      by_cases hz : f = 0
      · simp [hz]
      · exact eq_C_of_natDegree_eq_zero (by
          have : f.natDegree < 1 := (natDegree_lt_iff_degree_lt hz).mpr hd
          omega)
    rw [he, eval_C] at h0 h1
    exact ⟨he.trans (congrArg C h0), h0.symm.trans h1⟩
  · rintro ⟨rfl, he⟩
    exact ⟨lt_of_le_of_lt degree_C_le (by decide), by simp [he]⟩

omit [DecidableEq F] in
private theorem singleton_polynomial (y : F) : coefficientPolynomial [y] = C y := by
  simp [coefficientPolynomial]

private theorem two_exact (domain : Fin 2 ↪ F) (received : Fin 2 → F) :
    Exact domain received 1 2 (if received 0 = received 1 then [[received 0]] else []) := by
  by_cases he : received 0 = received 1
  · rw [if_pos he]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro f
      simp only [List.map_cons, List.map_nil, List.mem_singleton, singleton_polynomial]
      simpa only [he, and_true, Nat.cast_one] using (constant_two domain received f).symm
    · intro cs
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨rfl, (constant_two domain received _).mpr
          ⟨singleton_polynomial _, he⟩⟩
      · rintro ⟨hlen, hd, ha⟩
        obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hpoly := ((constant_two domain received _).mp ⟨hd, ha⟩).1
        rw [singleton_polynomial] at hpoly
        have hy := Polynomial.C_injective hpoly
        simp [hy]
  · rw [if_neg he]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · intro f
      simp only [List.map_nil, List.not_mem_nil, false_iff]
      intro hf
      exact he ((constant_two domain received f).mp hf).2
    · intro cs
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨_, hd, ha⟩
      exact he ((constant_two domain received _).mp ⟨hd, ha⟩).2

/-- The leaf's completed execution and correctness, with explicit charged trace bounds. -/
def CertifiedRun {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) : Prop :=
  ∃ out c steps,
    runFuel n A (List.ofFn fun i ↦ (domain i, received i)) 5 .start = (.done out, c) ∧
    Trace n A (List.ofFn fun i ↦ (domain i, received i)) steps .start c (.done out) ∧
    steps ≤ 5 ∧ c ≤ 34 ∧ Exact domain received k A out

private theorem certify {n k A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (out : List (List F)) (c : ℕ)
    (hr : runFuel n A (List.ofFn fun i ↦ (domain i, received i)) 5 .start = (.done out, c))
    (hc : c ≤ 34) (he : Exact domain received k A out) : CertifiedRun domain received k A := by
  obtain ⟨steps, hs, ht⟩ := runFuel_refines n A
    (List.ofFn fun i ↦ (domain i, received i)) 5 .start
  rw [hr] at ht
  exact ⟨out, c, steps, hr, ht, hs, hc, he⟩

/-- Any oversized threshold has an exact empty output, regardless of the message dimension. -/
theorem oversized_exact {n k A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (h : n < A) : CertifiedRun domain received k A := by
  exact certify domain received [] 9 (oversized_run n A _ h) (by decide)
    (empty_exact domain received h)

/-- A positive gap at length one always executes the charged empty branch. -/
theorem one_exact (delta : ℝ) (hdelta : 0 < delta) (k A : ℕ) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta 1 k ≤ A)
    (domain : Fin 1 ↪ F) (received : Fin 1 → F) : CertifiedRun domain received k A := by
  exact oversized_exact domain received
    (HiddenDerivative.OrderZeroDecoderCertificate.threshold_one_oversized delta hdelta k A hk hA)

/-- At length two the feasible quarter-gap branch is exactly a constant with two agreements.
This theorem uses no characteristic or nonsquare premise, so it includes the binary field. -/
theorem two_quarter_exact (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta) (k A : ℕ)
    (hk : 0 < k) (hA : ReedSolomon.agreementThreshold delta 2 k ≤ A)
    (domain : Fin 2 ↪ F) (received : Fin 2 → F) : CertifiedRun domain received k A := by
  by_cases hos : 2 < A
  · exact oversized_exact domain received hos
  have hs :=
    HiddenDerivative.OrderZeroDecoderCertificate.threshold_two_successor delta hdelta k A hA
  have hk1 : k = 1 := by omega
  have hA2 : A = 2 := by omega
  subst k A
  have hrows : List.ofFn (fun i ↦ (domain i, received i)) =
      [(domain 0, received 0), (domain 1, received 1)] := by
    simp [List.ofFn_succ]
  by_cases he : received 0 = received 1
  · apply certify domain received [[received 0]] 34
    · simpa only [hrows, ← he] using equal_run 2 2 (domain 0) (received 0) (domain 1) le_rfl
    · exact le_rfl
    · simpa only [if_pos he] using two_exact domain received
  · apply certify domain received [] 27
    · simpa only [hrows] using
        different_run 2 2 (domain 0) (received 0) (domain 1) (received 1) le_rfl he
    · decide
    · simpa only [if_neg he] using two_exact domain received

end ReedSolomon.ListDecoding.SmallBlockDecoderProof
