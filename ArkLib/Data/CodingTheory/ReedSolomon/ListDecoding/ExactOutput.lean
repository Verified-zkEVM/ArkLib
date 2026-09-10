/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListSpecification
public import ArkLib.Data.Polynomial.DegreeTruncationSemantics
/-!
# Exact output specification for Reed--Solomon decoders

This module owns the backend-independent contract for executable list decoders. Outputs use the
repository's fixed-width descending coefficient convention. Exactness includes duplicate freedom
both before and after interpreting those vectors as polynomials.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding

open Polynomial JetHornerMachine

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- Exact fixed-width coefficient vectors and their polynomial interpretations, with no duplicates
in either representation. Membership means degree below `k` and at least `A` indexed agreements.

The degree comparison uses `Polynomial.degree`, so the zero polynomial satisfies every natural
degree bound, including `k = 0`. In that case its canonical coefficient vector is empty. -/
def ExactOutput (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (out : List (List F)) : Prop :=
  (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
    (∀ f : F[X], f ∈ out.map coefficientPolynomial ↔
      f.degree < k ∧ A ≤ Code.agree (evalOnPoints domain f) received) ∧
    (∀ cs : List F, cs ∈ out ↔ cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received)

omit [DecidableEq F] in
/-- Equal-width descending coefficient vectors are equal when they represent the same polynomial. -/
theorem coefficientVectors_eq {xs ys : List F} (hlen : xs.length = ys.length)
    (hpoly : coefficientPolynomial xs = coefficientPolynomial ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hcoeff := congrArg (fun p : F[X] ↦ p.coeff xs.length) hpoly
          rw [coeff_coefficientPolynomial_cons_length, htail,
            coeff_coefficientPolynomial_cons_length] at hcoeff
          subst b
          rw [coefficientPolynomial_cons, coefficientPolynomial_cons, htail] at hpoly
          exact congrArg (a :: ·) (ih htail (add_left_cancel hpoly))

/-- Build the full exact-output contract from duplicate-free physical output, per-vector
soundness, and polynomial-level completeness. Fixed output width makes polynomial interpretation
injective, so the constructor also proves duplicate freedom after interpretation. -/
theorem exactOutput_of_sound_complete (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (out : List (List F)) (hnodup : out.Nodup)
    (hsound : ∀ cs ∈ out, cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received)
    (hcomplete : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      ∃ cs ∈ out, coefficientPolynomial cs = P) :
    ExactOutput domain received k A out := by
  have hvector (cs : List F) :
      cs ∈ out ↔ cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
    constructor
    · exact hsound cs
    · rintro ⟨hlength, hdegree, hagreement⟩
      obtain ⟨candidate, hcandidate, hpolynomial⟩ :=
        hcomplete (coefficientPolynomial cs) hdegree hagreement
      have heq : candidate = cs :=
        coefficientVectors_eq ((hsound candidate hcandidate).1.trans hlength.symm) hpolynomial
      rwa [← heq]
  have hpolynomialNodup : (out.map coefficientPolynomial).Nodup := by
    apply hnodup.map_on
    intro xs hxs ys hys hpoly
    exact coefficientVectors_eq ((hsound xs hxs).1.trans (hsound ys hys).1.symm) hpoly
  refine ⟨hpolynomialNodup, hnodup, ?_, hvector⟩
  intro P
  constructor
  · intro hP
    rcases List.mem_map.mp hP with ⟨cs, hcs, rfl⟩
    exact (hsound cs hcs).2
  · rintro ⟨hdegree, hagreement⟩
    obtain ⟨cs, hcs, hpolynomial⟩ := hcomplete P hdegree hagreement
    exact List.mem_map.mpr ⟨cs, hcs, hpolynomial⟩

/-- Interpret a physical output list as the mathematical finite set of degree-bounded messages.
The subtype preimage discards any represented polynomial outside the message space; an
`ExactOutput` proof below shows that this does not discard any element of a correct output. -/
noncomputable def coefficientOutput (k : ℕ) (out : List (List F)) :
    Finset (MessagePolynomial F k) :=
  (out.map coefficientPolynomial).toFinset.preimage (messagePolynomialValue k)
    (messagePolynomialValue k).injective.injOn

@[simp]
theorem mem_coefficientOutput (k : ℕ) (out : List (List F)) (p : MessagePolynomial F k) :
    p ∈ coefficientOutput k out ↔ (p : F[X]) ∈ out.map coefficientPolynomial := by
  simp [coefficientOutput]

/-- Lift a physical coefficient-list implementation to the mathematical decoder interface. -/
noncomputable def coefficientListDecoder (k : ℕ) (decode : (Fin n → F) → List (List F)) :
    Decoder F (Fin n) k := fun received ↦ coefficientOutput k (decode received)

/-- Pointwise `ExactOutput` correctness implies the repository's extensional mathematical
`IsExactDecoder` specification. -/
theorem coefficientListDecoder_isExact (domain : Fin n ↪ F) (k A : ℕ)
    (decode : (Fin n → F) → List (List F))
    (hexact : ∀ received, ExactOutput domain received k A (decode received)) :
    IsExactDecoder domain k A (coefficientListDecoder k decode) := by
  intro received p
  change p ∈ coefficientOutput k (decode received) ↔ _
  rw [mem_coefficientOutput, (hexact received).2.2.1]
  exact and_iff_right (Polynomial.mem_degreeLT.mp p.property)

end ReedSolomon.ListDecoding
