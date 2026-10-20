/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RecursiveCount
public import ArkLib.Data.Polynomial.Differential.RegularIteration

/-!
# First nonzero separant witnesses along the singular chain

Let `P` solve `Q = 0`. Follow the singular chain `Q = Q₀, Q₁ = ∂Q₀/∂Y_{s₀}, …`, where `Y_{sᵢ}` is
the highest active jet of `Qᵢ`. A point `a` is a chain witness for `P` (`ChainWitness Q P a`) when
`P` solves `Q₀, …, Qᵢ` and the separant `∂Qᵢ/∂Y_{sᵢ}` does not vanish at the Hasse jet of `P` at
`a`, for some stage `i`. Requiring `P` to solve every earlier equation makes the stage visible in
the jet: two chain witnesses at the same point with the same jet are at the same stage, since at an
earlier stage the separant vanishes at the jet of the later one. Consequently the jet at `a`
determines `P` among chain-witnessed solutions of degree at most `D`, under the binomial hypothesis
of fixed-jet uniqueness (`ChainWitness.eq_of_polynomialJet_eq`).

Every solution of a nonzero equation that satisfies the cast hypotheses has a nonzero polynomial
`R` of degree at most `differentialWeightedDegree D Q - (D - d)` such that every point outside the
roots of `R` is a chain witness (`exists_chainWitness`): `R` is the separant specialization at the
first regular stage.

The initial equation `initialJetEquation a Q` is `Q` with `X = a`. A chain witness at `a` forces
`initialJetEquation a Q ≠ 0`, and its total degree is at most `jetTotalDegree Q`; the root count in
`TotalJetDegreeCount` uses both. The specialization and its basic laws are defined in `JetDegree`.

## Main statements

* `ChainWitness`, `ChainWitness.solves`, `ChainWitness.jetEvaluation_eq_zero`.
* `ChainWitness.eq_of_polynomialJet_eq`: chain witnesses at one point are determined by the jet.
* `exists_chainWitness`: all but at most `differentialWeightedDegree D Q - (D - d)` points are
  chain witnesses.
* `ChainWitness.initialJetEquation_ne_zero`: a chain witness forces a nonzero initial equation,
  using the specialization and its derivative law from `JetDegree`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Appendix A.3, (122), and
  Appendix A.2, Lemma A.1
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-! ### Chain witnesses -/

/-- `ChainWitness Q P a`: at the first stage `i` of the singular chain below `Q` whose separant
does not vanish at the Hasse jet of `P` at `a`, the solution `P` solves every equation
`Q₀, …, Qᵢ`. The `regular` constructor is the stage where the separant is nonzero at the jet; the
`singular` constructor records that `P` solves the current equation and passes to its separant. -/
inductive ChainWitness [CommSemiring F] :
    DifferentialPolynomial F d → F[X] → F → Prop where
  /-- The separant in the highest active jet `Y_s` is nonzero at the Hasse jet of `P` at `a`. -/
  | regular {Q P a s} (highest : highestActiveJet Q = some s)
      (solves : differentialSpecialization Q P = 0)
      (nonzero : jetEvaluation (separant Q s) a (polynomialJet a P) ≠ 0) :
      ChainWitness Q P a
  /-- `P` solves `Q = 0`, and `a` is a chain witness for `P` below the separant `∂Q/∂Y_s`. -/
  | singular {Q P a s} (highest : highestActiveJet Q = some s)
      (solves : differentialSpecialization Q P = 0)
      (next : ChainWitness (separant Q s) P a) : ChainWitness Q P a

section CommSemiring

variable [CommSemiring F]

/-- A chain-witnessed polynomial solves the original equation. -/
theorem ChainWitness.solves {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : differentialSpecialization Q P = 0 := by
  cases h <;> assumption

/-- The Hasse jet at a chain witness lies on the original equation. -/
theorem ChainWitness.jetEvaluation_eq_zero {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : jetEvaluation Q a (polynomialJet a P) = 0 := by
  rw [← eval_differentialSpecialization, h.solves, eval_zero]

/-- **Chain witnesses exist off a small set.** Let `F` have no zero divisors, `Q ≠ 0`, and let `Q`
satisfy the cast hypotheses at every jet. For every solution `P` of `Q = 0` with
`P.natDegree ≤ D` there is a nonzero `R : F[X]` with
`R.natDegree ≤ differentialWeightedDegree D Q - (D - d)` such that every `a` with `R.eval a ≠ 0` is
a chain witness for `P`.

`R` is the separant specialization of `P` at the first equation of the singular chain where it is
nonzero; such an equation exists by `exists_regularRecursionLeaf`. Its degree is at most the
weighted degree of that equation minus the weight `D - s` of the differentiated jet, and both
weighted degrees and `D - s ≥ D - d` compare with those of `Q`. The hypotheses on `Q` are those of
`exists_regularRecursionLeaf`; without them `Y₀ ^ 2 = 0` over `ZMod 2` has the solution `0` and no
chain witness. -/
theorem exists_chainWitness [NoZeroDivisors F] {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j) {D : ℕ} {P : F[X]}
    (hsolution : differentialSpecialization Q P = 0) (hdegree : P.natDegree ≤ D) :
    ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ differentialWeightedDegree D Q - (D - d) ∧
      ∀ a, R.eval a ≠ 0 → ChainWitness Q P a := by
  suffices h : ∀ current, Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 → (∀ j, JetDegreeCastsNeZero current j) →
        differentialSpecialization current P = 0 →
          ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ differentialWeightedDegree D Q - (D - d) ∧
            ∀ a, R.eval a ≠ 0 → ChainWitness current P a from
    h Q Relation.ReflTransGen.refl hQ hcast hsolution
  intro current
  induction current using (singularStep_wellFounded (F := F) (d := d)).induction with
  | _ equation ih =>
  intro hreach hne hequation hsolves
  cases hactive : highestActiveJet equation with
  | none =>
      exact (hne (eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none
        hactive hsolves)).elim
  | some s =>
      by_cases hzero : differentialSpecialization (separant equation s) P = 0
      · have hstep := singularStep_separant equation hactive
        have hnext := singularStep_preserves hequation hstep
        obtain ⟨R, hR, hdeg, hcover⟩ := ih _ hstep (Relation.ReflTransGen.head hstep hreach)
          hnext.1 hnext.2 hzero
        exact ⟨R, hR, hdeg, fun a ha ↦ .singular hactive hsolves (hcover a ha)⟩
      · refine ⟨_, hzero, ?_, fun a ha ↦ .regular hactive hsolves ?_⟩
        · have hw := differentialWeightedDegree_le_of_reflTransGen_singularStep (D := D) hreach
          have hsep := natDegree_differentialSpecialization_separant_le_sub equation s P hdegree
          have hs := Nat.le_of_lt_succ s.isLt
          omega
        · rwa [← eval_differentialSpecialization]

/-! ### Nonvanishing of the initial equation -/

/-- If `a` is a chain witness for some solution, then the initial equation is nonzero: the
separant at the regular stage is nonzero at a jet, and a partial derivative of the zero polynomial
is zero. -/
theorem ChainWitness.initialJetEquation_ne_zero {Q : DifferentialPolynomial F d} {P : F[X]} {a : F}
    (h : ChainWitness Q P a) : initialJetEquation a Q ≠ 0 := by
  induction h with
  | regular _ _ hreg =>
      intro hzero
      apply hreg
      rw [← aeval_initialJetEquation, ← pderiv_initialJetEquation, hzero, map_zero, map_zero]
  | singular _ _ _ ih =>
      intro hzero
      apply ih
      rw [← pderiv_initialJetEquation, hzero, map_zero]

end CommSemiring

/-! ### Uniqueness given the jet -/

/-- **Chain witnesses are determined by the jet.** Over a domain, let `a` be a chain witness for
two polynomials `P` and `P'` of degree at most `D`, with the same Hasse jet at `a` through order
`d`. If `((k + s).choose s : F) ≠ 0` whenever `0 < k` and `k + s ≤ D`, then `P = P'`.

Both witnesses are at the same stage: if `P` were regular at a stage where `P'` is singular, the
separant would vanish at the jet of `P'`, which is the jet of `P`. At the common regular stage
with highest active jet `Y_s`, fixed-jet uniqueness
(`eq_of_polynomialJet_eq_of_isHighestActiveJet`) applies, with slopes `(k + s choose s) * S` that
are nonzero, hence left-regular in a domain. The binomial hypothesis cannot be dropped: over
`ZMod 2`, `1` and `1 + X ^ 2` solve `y' = 0`, have the same jet at `0` through order `1`, and have
every point as a chain witness. -/
theorem ChainWitness.eq_of_polynomialJet_eq [CommRing F] [IsDomain F]
    {Q : DifferentialPolynomial F d} {P P' : F[X]} {a : F} {D : ℕ}
    (h : ChainWitness Q P a) (h' : ChainWitness Q P' a) (hP : P.degree ≤ D)
    (hP' : P'.degree ≤ D) (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hjet : polynomialJet (d := d) a P = polynomialJet a P') : P = P' := by
  induction h with
  | @regular Q P a s hs hsol hreg =>
      cases h' with
      | regular _ hsol' _ =>
          refine eq_of_polynomialJet_eq_of_isHighestActiveJet Q
            (isHighestActiveJet_of_highestActiveJet_eq_some hs) a hP hP'
            (hsol.trans hsol'.symm)
            (by simpa only [restrictJet_polynomialJet] using congrArg (restrictJet s) hjet)
            fun k hk hkD ↦ IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
              (mul_ne_zero (hbinom k s hk hkD) hreg)
      | singular hs' _ next =>
          cases Option.some.inj (hs.symm.trans hs')
          exact (hreg (hjet ▸ next.jetEvaluation_eq_zero)).elim
  | @singular Q P a s hs _ next ih =>
      cases h' with
      | regular hs' _ hreg' =>
          cases Option.some.inj (hs.symm.trans hs')
          exact (hreg' (hjet ▸ next.jetEvaluation_eq_zero)).elim
      | singular hs' _ next' =>
          cases Option.some.inj (hs.symm.trans hs')
          exact ih next' hP hjet

end

end PolynomialDifferential
