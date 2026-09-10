/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.Slice
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
public import ArkLib.Data.Polynomial.SquarefreeSupport

/-!
# Ordinary decoding from a supplied interpolant and regular center

This is an executable path from `Q(X,Y)` to the agreement list. It computes the initial slice
`Q(c,U)`, extracts its monic squarefree support, removes roots where `Q_Y(c,U)=0`, and lifts the
remaining roots together in a polynomial quotient. Materialization then feeds the same agreement
recovery consumer used by other finite-representation constructors.

`run_exact_of_regular_cover` states the constructor-side obligations explicitly: the supplied
interpolant vanishes on every wanted message, its initial slice is nonzero, and every wanted
branch is regular at this center. The modulus, modular inverse, lifted coefficients, and recovery
output are all computed; none is supplied by a coverage oracle.

Constructing the paper's interpolant and choosing a certified regular center are still separate
steps. Lifting uses Newton precision doubling, but its generic arithmetic backend does not yet
carry the paper's near-linear cost proof. A zero slice produces no representations and lies outside
the exactness theorem's hypotheses; it must be handled by the center-selection caller.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.OrdinaryQuotientDecoder
open CompPoly Polynomial ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
variable {E : Type*} [Field E] [Fintype E] [BEq E] [LawfulBEq E]
variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]

/-- Retain exactly the roots of `Q(c,U)` at which the value derivative is nonzero.
Squarefree support preserves inseparable factors; the gcd complement removes singular roots. -/
def regularModulus (Q : CPoly.CMvPolynomial 2 E) (center : E) : CPolynomial E :=
  CPolynomial.gcdComplement
    (CPolynomial.squarefreeSupport pchar (sectionPolynomial Q center)) (slope Q center)

/-- Compute the finite representation at this center. A zero initial slice is rejected;
for a nonzero slice the retained modulus has an invertible slope, so lifting succeeds. -/
def representations (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ) :
    List (FiniteRepresentation E) :=
  if sectionPolynomial Q center == 0 then [] else
    let h := regularModulus pchar Q center
    match newtonLift? Q center h k with
    | none => []
    | some series => [materialize h center k series]

variable {pchar}

/-- The retained modulus is monic and squarefree, and its slope is invertible modulo it. -/
theorem regularModulus_properties (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    (regularModulus pchar Q center).toPoly.Monic ∧
      Squarefree (regularModulus pchar Q center).toPoly ∧
      IsCoprime (slope Q center).toPoly (regularModulus pchar Q center).toPoly := by
  let h := CPolynomial.squarefreeSupport pchar (sectionPolynomial Q center)
  have hne : h ≠ 0 := CPolynomial.squarefreeSupport_ne_zero pchar hsection
  have hm : h.monic := CPolynomial.squarefreeSupport_monic pchar hsection
  have hs : Squarefree h.toPoly := CPolynomial.squarefreeSupport_squarefree pchar hsection
  refine ⟨?_, ?_, ?_⟩
  · exact (CPolynomial.monic_toPoly_iff _).mp (CPolynomial.gcdComplement_monic hm)
  · exact CPolynomial.gcdComplement_squarefree hne hs
  · exact (CPolynomial.gcdComplement_isCoprime_right hne hs).symm

/-- The regular slice has leading coefficient one, as required by quotient reduction. -/
theorem regularModulus_monic (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    (regularModulus pchar Q center).toPoly.Monic :=
  (regularModulus_properties Q center hsection).1

/-- Every geometric initial value occurs with multiplicity one in the retained modulus. -/
theorem regularModulus_squarefree (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    Squarefree (regularModulus pchar Q center).toPoly :=
  (regularModulus_properties Q center hsection).2.1

/-- Removing all zero-slope roots makes the shared initial Newton inverse computable. -/
theorem regularModulus_isCoprime_slope (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    IsCoprime (slope Q center).toPoly (regularModulus pchar Q center).toPoly :=
  (regularModulus_properties Q center hsection).2.2

/-- Every emitted representation satisfies the shared recovery data contract. -/
theorem representations_wellFormed (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ) :
    ∀ r ∈ representations pchar Q center k, r.WellFormed k := by
  intro r hr
  unfold representations at hr
  split at hr
  · simp at hr
  · rename_i hsection
    have hs : sectionPolynomial Q center ≠ 0 := by simpa using hsection
    have hp := regularModulus_properties Q center hs (pchar := pchar)
    dsimp only at hr
    split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact materialize_wellFormed _ center k _ hp.1 hp.2.1

variable (pchar) in
/-- Compute the ordinary representation and invoke the shared base-field agreement recovery. -/
def run {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (Q : CPoly.CMvPolynomial 2 E) (center : E) : List (List F) :=
  AgreementRecovery.decode base domain received k A (representations pchar Q center k)

/-- Removing repetitions and singular roots cannot increase the initial slice degree. -/
theorem regularModulus_degree_le (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    (regularModulus pchar Q center).natDegree ≤ (sectionPolynomial Q center).natDegree := by
  let h := CPolynomial.squarefreeSupport pchar (sectionPolynomial Q center)
  have hne : h ≠ 0 := CPolynomial.squarefreeSupport_ne_zero pchar hsection
  have hdiv : (regularModulus pchar Q center).toPoly ∣ h.toPoly := by
    have hf := congrArg CPolynomial.toPoly
      (CPolynomial.gcdFactor_mul_gcdComplement (h := h) (e := slope Q center) hne)
    rw [CPolynomial.toPoly_mul] at hf
    refine ⟨(CPolynomial.gcdFactor h (slope Q center)).toPoly, ?_⟩
    rw [← hf]
    exact mul_comm _ _
  have hle := Polynomial.natDegree_le_of_dvd hdiv
    ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hne)
  rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly] at hle
  exact hle.trans (CPolynomial.natDegree_squarefreeSupport_le pchar hsection)

/-- The initial slice degree bounds the number of returned messages, including rejection. -/
theorem run_length_le
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (Q : CPoly.CMvPolynomial 2 E) (center : E) :
    (run pchar base domain received k A Q center).length ≤
      (sectionPolynomial Q center).natDegree := by
  by_cases hsection : sectionPolynomial Q center = 0
  · simp [run, representations, hsection, AgreementRecovery.decode]
  · apply (AgreementRecovery.decode_length_le base domain received k A
      (representations pchar Q center k)).trans
    unfold representations
    rw [if_neg (by simpa using hsection)]
    dsimp only
    split
    · simp
    · simpa [materialize] using regularModulus_degree_le Q center hsection (pchar := pchar)

noncomputable section
variable {L : Type*} [Field L]

/-- After any field extension, retained parameter roots are exactly the regular initial values. -/
theorem regularModulus_root_iff (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0) :
    (regularModulus pchar Q center).toPoly.eval₂ ι θ = 0 ↔
      MvPolynomial.eval₂ ι ![ι center, θ] (CPoly.fromCMvPolynomial Q) = 0 ∧
      MvPolynomial.eval₂ ι ![ι center, θ]
        (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0 := by
  rw [regularModulus, CPolynomial.eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero ι θ
    (CPolynomial.squarefreeSupport_ne_zero pchar hsection)
    (CPolynomial.squarefreeSupport_squarefree pchar hsection),
    CPolynomial.eval₂_squarefreeSupport_eq_zero_iff pchar ι θ hsection,
    eval₂_sectionPolynomial, eval₂_slope]

/-- Every regular polynomial solution is covered by the representation that the program emits.
The inverse guard succeeds from the computed modulus properties, so this is producer completeness,
not only correctness conditional on an output certificate. -/
theorem exists_representation_of_regular_solution (ι : E →+* L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (k : ℕ)
    (hsection : sectionPolynomial Q center ≠ 0)
    (P : Polynomial L) (hdegree : P.degree < k)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P]
      (CPoly.fromCMvPolynomial Q) = 0)
    (hregular : MvPolynomial.eval₂ ι ![ι center, P.eval (ι center)]
      (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0) :
    ∃ r ∈ representations pchar Q center k, r.Represents ι (P.eval (ι center)) P := by
  -- The regular slice has no zero-slope roots; one modular inverse lifts all remaining roots.
  obtain ⟨series, hrun⟩ := newtonLift_exists Q center (regularModulus pchar Q center) k
    (regularModulus_isCoprime_slope Q center hsection)
  refine ⟨materialize (regularModulus pchar Q center) center k series, ?_, ?_⟩
  · simp [representations, hsection, hrun]
  · apply newtonLifted_represents_solution ι Q center _
      (regularModulus_monic Q center hsection) k series hrun P hdegree
    · apply (regularModulus_root_iff ι (P.eval (ι center)) Q center hsection).mpr
      exact ⟨solution_at_center ι (CPoly.fromCMvPolynomial Q) P (ι center) hsolution,
        hregular⟩
    · exact hsolution

/-- **Exact ordinary quotient decoding at a regular center.** The supplied `Q` must vanish
on every degree-`< k` message with at least `A` agreements, and those messages must be regular
at the chosen center. Under those explicit constructor premises, the actual run returns exactly
the duplicate-free fixed-width agreement list. -/
theorem run_exact_of_regular_cover
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A)
    (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (hsection : sectionPolynomial Q center ≠ 0)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial Q) = 0)
    (hregular : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ (RingHom.id E) ![center, (P.map base).eval center]
        (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0) :
    ExactOutput domain received k A (run pchar base domain received k A Q center) := by
  apply AgreementRecovery.decode_exact_of_coverage base (RingHom.id E) domain received k A hAk
    (representations pchar Q center k) (representations_wellFormed Q center k)
  intro P hP
  have hdegree : (P.map base).degree < k := by
    simpa only [Polynomial.degree_map_eq_of_injective base.injective] using hP.1
  obtain ⟨r, hr, hrep⟩ := exists_representation_of_regular_solution
    (pchar := pchar) (RingHom.id E) Q center k hsection (P.map base) hdegree
    (by simpa using hsolutions P hP.1 hP.2)
    (by simpa using hregular P hP.1 hP.2)
  exact ⟨r, hr, (P.map base).eval center, by simpa using hrep⟩

end
end ReedSolomon.ListDecoding.OrdinaryQuotientDecoder
