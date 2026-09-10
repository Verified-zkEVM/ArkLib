/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Lifting
public import Mathlib.Algebra.MvPolynomial.Variables


/-!
# Restricting differential equations to their highest active jet

The regular lifting theorem is naturally stated for an equation in `X, Y₀, ..., Y_r` whose pivot
is the literal top variable `Y_r`. The root solver stores equations in one ambient jet depth and
computes an arbitrary highest active coordinate `s`. This file closes that representation seam.

If `s` is the highest active jet of `Q`, every variable occurring in `Q` lies in the prefix through
`Y_s`. Hence `Q` is the injective renaming of a differential polynomial of depth `s`. Differential
specialization, separants, scalar jet evaluation, and regularity commute with this renaming. The
top-coordinate one-step theorem can therefore be applied without pretending that unused higher
jet variables affect the lift.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4 and the `SOLVE`
  recursion in the proof of Theorem 4.3.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F] {d k : ℕ}

/-- Embed the jet variables through `Y_s` into an ambient depth `d`. -/
def jetPrefixEmbedding (s : Fin (d + 1)) : JetVariable s.val ↪ JetVariable d where
  toFun
    | none => none
    | some j => some ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) s.isLt⟩
  inj' := by
    intro i j hij
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · simp at hij
    · simp at hij
    · simp only [Option.some.injEq] at hij
      simp only [Option.some.injEq]
      exact Fin.ext (congrArg (fun z : Fin (d + 1) => z.val) hij)

@[simp]
theorem jetPrefixEmbedding_none (s : Fin (d + 1)) :
    jetPrefixEmbedding s none = none :=
  rfl

@[simp]
theorem jetPrefixEmbedding_top (s : Fin (d + 1)) :
    jetPrefixEmbedding s (some (Fin.last s.val)) = some s := by
  apply congrArg some
  apply Fin.ext
  rfl

/-- Restrict an ambient scalar jet to the prefix ending at `s`. -/
def restrictJet (s : Fin (d + 1)) (jet : Fin (d + 1) → F) : Fin (s.val + 1) → F :=
  fun j => jet ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) s.isLt⟩

@[simp]
theorem restrictJet_polynomialJet (s : Fin (d + 1)) (center : F) (P : F[X]) :
    restrictJet s (polynomialJet (d := d) center P) =
      polynomialJet (d := s.val) center P := by
  funext j
  rfl

/-- Every variable of an equation lies in the prefix ending at its highest active jet. -/
theorem vars_subset_range_jetPrefixEmbedding (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hs : IsHighestActiveJet Q s) :
    (Q.vars : Set (JetVariable d)) ⊆ Set.range (jetPrefixEmbedding s) := by
  intro v hv
  rcases v with _ | j
  · exact ⟨none, rfl⟩
  · have hdegree : jetDegree Q j ≠ 0 := by
      simpa [jetDegree] using
        (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv)
    have hactive : DependsOnJet Q j := Nat.pos_of_ne_zero hdegree
    have hle : j.val ≤ s.val := by
      have hjs : j ≤ s := le_of_not_gt fun hsj => hs.2 j hsj hactive
      exact Fin.le_iff_val_le_val.mp hjs
    let j' : Fin (s.val + 1) := ⟨j.val, Nat.lt_succ_iff.mpr hle⟩
    refine ⟨some j', ?_⟩
    apply congrArg some
    apply Fin.ext
    rfl

/-- An equation whose highest active jet is `s` comes from a unique-variable-prefix
presentation. Existence is all the lifting adapter needs; injectivity of the renaming prevents
loss of polynomial information. -/
theorem exists_prefixDifferentialPolynomial (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hs : IsHighestActiveJet Q s) :
    ∃ Q' : DifferentialPolynomial F s.val,
      MvPolynomial.rename (jetPrefixEmbedding s) Q' = Q := by
  exact MvPolynomial.exists_rename_eq_of_vars_subset_range Q (jetPrefixEmbedding s)
    (jetPrefixEmbedding s).injective (vars_subset_range_jetPrefixEmbedding Q s hs)

/-- Differential specialization commutes with embedding a jet-prefix equation. -/
theorem differentialSpecialization_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (P : F[X]) :
    differentialSpecialization (MvPolynomial.rename (jetPrefixEmbedding s) Q) P =
      differentialSpecialization Q P := by
  rw [differentialSpecialization, differentialSpecialization,
    MvPolynomial.eval₂Hom_rename]
  apply MvPolynomial.eval₂Hom_congr
  · rfl
  · funext v
    rcases v with _ | j
    · rfl
    · rfl
  · rfl

/-- Scalar jet evaluation commutes with embedding a jet-prefix equation. -/
theorem jetEvaluation_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (center : F)
    (jet : Fin (d + 1) → F) :
    jetEvaluation (MvPolynomial.rename (jetPrefixEmbedding s) Q) center jet =
      jetEvaluation Q center (restrictJet s jet) := by
  rw [jetEvaluation, jetEvaluation, MvPolynomial.eval_rename]
  unfold MvPolynomial.eval
  apply MvPolynomial.eval₂Hom_congr
  · rfl
  · funext v
    rcases v with _ | j
    · rfl
    · rfl
  · rfl

/-- The separant in the ambient highest active jet is the renamed top-coordinate separant of the
prefix equation. -/
theorem separant_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) :
    separant (MvPolynomial.rename (jetPrefixEmbedding s) Q) s =
      MvPolynomial.rename (jetPrefixEmbedding s) (separant Q (Fin.last s.val)) := by
  rw [separant, separant, ← MvPolynomial.pderiv_rename (jetPrefixEmbedding s).injective]
  simp

/-- Regularity in an ambient highest active jet is exactly regularity at the top coordinate of
the restricted prefix equation. -/
theorem isRegularJet_rename_jetPrefixEmbedding_iff
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (center : F) (P : F[X]) :
    IsRegularJet (MvPolynomial.rename (jetPrefixEmbedding s) Q) s center
        (polynomialJet (d := d) center P) ↔
      IsRegularJet Q (Fin.last s.val) center (polynomialJet (d := s.val) center P) := by
  rw [IsRegularJet, IsRegularJet, separant_rename_jetPrefixEmbedding,
    jetEvaluation_rename_jetPrefixEmbedding, jetEvaluation_rename_jetPrefixEmbedding,
    restrictJet_polynomialJet]

/-- Apply regular one-step lifting at an arbitrary highest active jet by restricting the equation
to its active prefix. This closes the representation gap between `highestActiveJet` and the
literal-top-coordinate theorem in `RegularLifting`.

The conclusion uses the perturbation degree `k + s`, exactly as Kopparty's recurrence does for an
equation whose highest derivative is `Y_s`. -/
theorem existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet
    (hk : 0 < k) (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hs : IsHighestActiveJet Q s) (center : F) (P : F[X]) (D : ℕ)
    (hregular : IsRegularJet Q s center (polynomialJet center P))
    (hdegree : k + s.val ≤ D) (hD : D < ringChar F)
    (hresidual : (X - C center) ^ k ∣ differentialSpecialization Q P) :
    ∃! gamma : F,
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center gamma k s.val P) := by
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial Q s hs
  rw [← hQ'] at hregular hresidual ⊢
  have hregular' :
      IsRegularJet Q' (Fin.last s.val) center (polynomialJet (d := s.val) center P) :=
    (isRegularJet_rename_jetPrefixEmbedding_iff s Q' center P).mp hregular
  have hresidual' : (X - C center) ^ k ∣ differentialSpecialization Q' P := by
    simpa only [differentialSpecialization_rename_jetPrefixEmbedding] using hresidual
  simpa only [differentialSpecialization_rename_jetPrefixEmbedding] using
    existsUnique_regularLiftCoefficient_centered_of_isRegularJet_of_le_of_lt_ringChar
      hk Q' center P D hregular' hdegree hD hresidual'

end

end ReedSolomon.HiddenDerivative
