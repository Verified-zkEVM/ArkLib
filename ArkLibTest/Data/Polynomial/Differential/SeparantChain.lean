/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.SeparantChain
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for separant chains

* Over `ℚ`, `Y₀ ^ 2` has the explicit chain `Y₀ ^ 2, 2 * Y₀` with terminal equation `2`. Both
  stages have highest active jet `Y₀`, so the bound `length_filter_le_jetDegree` is attained. The
  general existence theorem also applies, and `P = 0` is covered by a regular stage.
* Over `ZMod 2`, `Y₀ ^ 2` has no chain, since its separant `2 * Y₀` is zero: the cast hypothesis
  of `exists_separantChain` is needed.
* Over `ZMod 4`, `2 * Y₀ ^ 2` satisfies the cast hypothesis but has no chain, since its separant
  `4 * Y₀` is zero: the hypothesis `NoZeroDivisors` is needed.
* Over `ℚ[X]`, the equation `X * Y₀` specialized at `X ↦ 0` is solved by `P = 0`, and no stage is
  regular there, so the exceptional set of `exists_finset_regular_stage` must contain `0`.
* The forms with a field of coefficients `F[X]`, with the cast hypothesis up to the total jet
  degree, the conjunctions of stage properties and coefficient heights, and the presentation of
  each stage with its coefficient height follow from the general statements.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- In depth `0`, an equation that depends on `Y₀` has highest active jet `Y₀`. -/
private theorem highestActiveJet_eq_zero {F : Type*} [CommSemiring F]
    {Q : DifferentialPolynomial F 0} (hQ : DependsOnJet Q 0) : highestActiveJet Q = some 0 := by
  cases h : highestActiveJet Q with
  | none => exact absurd hQ ((highestActiveJet_eq_none_iff Q).mp h 0)
  | some j => rw [Fin.fin_one_eq_zero j]

/-- A constant has no active jet. -/
private theorem highestActiveJet_C {F : Type*} [CommSemiring F] {d : ℕ} (c : F) :
    highestActiveJet (C c : DifferentialPolynomial F d) = none :=
  (highestActiveJet_eq_none_iff _).mpr fun j hj ↦ by
    simp [DependsOnJet, jetDegree, degreeOf_C] at hj

/-- `Y₀ ^ 2` in depth `0`, over a commutative semiring. -/
private abbrev squareEquation (F : Type) [CommSemiring F] : DifferentialPolynomial F 0 :=
  X (some 0) ^ 2

private theorem jetDegree_squareEquation (F : Type) [CommSemiring F] [Nontrivial F] :
    jetDegree (squareEquation F) 0 = 2 := by
  classical
  rw [jetDegree, squareEquation, X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  simp

/-- The separant of `Y₀ ^ 2` is `2 * Y₀`. -/
private theorem separant_squareEquation (F : Type) [CommSemiring F] :
    separant (squareEquation F) 0 = C 2 * X (some 0) := by
  have h : separant (squareEquation F) 0 = 2 * X (some 0) := by
    simp [separant, sq, pderiv_X]
    ring
  rw [h, map_ofNat C 2]

/-- The separant of `2 * Y₀` is `2`. -/
private theorem separant_separant_squareEquation (F : Type) [CommSemiring F] :
    separant (separant (squareEquation F) 0) 0 = C 2 := by
  rw [separant_squareEquation]
  simp [separant, pderiv_X]

/-- `P = 0` solves `Y₀ ^ 2 = 0` over every commutative semiring. -/
private theorem differentialSpecialization_squareEquation_zero (F : Type) [CommSemiring F] :
    differentialSpecialization (squareEquation F) 0 = 0 := by
  rw [← differentialSpecializationHom_apply, map_pow, differentialSpecializationHom_apply,
    differentialSpecialization_jet, map_zero, zero_pow two_ne_zero]

/-! ### An explicit chain over `ℚ` -/

/-- The stages of the chain of `Y₀ ^ 2` over `ℚ`. -/
private abbrev squareStages : List (SeparantStage ℚ 0) :=
  [(squareEquation ℚ, 0), (separant (squareEquation ℚ) 0, 0)]

/-- The chain `Y₀ ^ 2, 2 * Y₀` with terminal equation `2`. -/
private theorem squareChain :
    SeparantChain (squareEquation ℚ) squareStages
      (separant (separant (squareEquation ℚ) 0) 0) := by
  refine .active 0 (by simp [squareEquation])
    (highestActiveJet_eq_zero (by simp [DependsOnJet, jetDegree_squareEquation])) ?_
  refine .active 0 (by rw [separant_squareEquation]; simp) (highestActiveJet_eq_zero ?_) ?_
  · change 0 < jetDegree _ 0
    rw [jetDegree_separant_eq_sub_one _ _ (by simp [jetDegree_squareEquation]),
      jetDegree_squareEquation]
    norm_num
  · refine .terminal (by rw [separant_separant_squareEquation]; simp) ?_
    rw [separant_separant_squareEquation]
    exact highestActiveJet_C 2

/-- Both stages have highest active jet `Y₀`, and `Y₀ ^ 2` has degree `2` in `Y₀`: the bound
`length_filter_le_jetDegree` is attained. -/
example : (squareStages.filter fun stage ↦ stage.2 = 0).length =
    jetDegree (squareEquation ℚ) 0 := by
  rw [jetDegree_squareEquation]
  rfl

example : (squareStages.filter fun stage ↦ stage.2 = 0).length ≤
    jetDegree (squareEquation ℚ) 0 :=
  squareChain.length_filter_le_jetDegree 0

example : squareStages.length ≤ jetTotalDegree (squareEquation ℚ) :=
  squareChain.length_le

/-- The general existence theorem applies in characteristic zero. -/
example : ∃ stages terminal, SeparantChain (squareEquation ℚ) stages terminal :=
  exists_separantChain_of_ringChar (by simp [squareEquation]) (Or.inl ringChar.eq_zero)

/-- `P = 0` solves `Y₀ ^ 2 = 0`, and the terminal equation `2` has no solution, so some stage is
regular for `P = 0`. -/
example : ∃ stage ∈ squareStages,
    differentialSpecialization (MvPolynomial.map (RingHom.id ℚ) stage.1) 0 = 0 ∧
      differentialSpecialization (separant (MvPolynomial.map (RingHom.id ℚ) stage.1) stage.2)
        0 ≠ 0 :=
  squareChain.exists_regular_stage (RingHom.id ℚ)
    (by rw [map_id]; exact differentialSpecialization_squareEquation_zero ℚ)
    (squareChain.differentialSpecialization_map_terminal_ne_zero _
      (by rw [map_id, separant_separant_squareEquation]; simp) 0)

/-! ### The cast hypothesis is needed -/

/-- Over `ZMod 2` the cast hypothesis fails for `Y₀ ^ 2`. -/
example : ¬ JetDegreeCastsNeZero (squareEquation (ZMod 2)) 0 := fun h ↦
  h 2 (by decide) (by rw [jetDegree_squareEquation]) (by decide)

/-- Over `ZMod 2`, `Y₀ ^ 2` has no separant chain: its separant `2 * Y₀` is zero. -/
example : ¬ ∃ stages terminal, SeparantChain (squareEquation (ZMod 2)) stages terminal := by
  rintro ⟨stages, terminal, hc⟩
  have hhighest : highestActiveJet (squareEquation (ZMod 2)) = some 0 :=
    highestActiveJet_eq_zero (by simp [DependsOnJet, jetDegree_squareEquation])
  have hsep : separant (squareEquation (ZMod 2)) 0 = 0 := by
    rw [separant_squareEquation, show (C 2 : DifferentialPolynomial (ZMod 2) 0) = 0 by
      rw [C_eq_zero]; decide, zero_mul]
  cases hc with
  | terminal _ hterminal => rw [hhighest] at hterminal; cases hterminal
  | active j _ hj next =>
      rw [hhighest] at hj
      cases hj
      exact next.ne_zero hsep

/-! ### The hypothesis `NoZeroDivisors` is needed -/

/-- `2 * Y₀ ^ 2` over `ZMod 4`. -/
private abbrev zeroDivisorEquation : DifferentialPolynomial (ZMod 4) 0 :=
  monomial (Finsupp.single (some 0) 2) 2

private theorem jetDegree_zeroDivisorEquation : jetDegree zeroDivisorEquation 0 = 2 := by
  classical
  rw [jetDegree, degreeOf_monomial_eq _ _ (by decide)]
  simp

/-- Over `ZMod 4`, the cast hypothesis holds for `2 * Y₀ ^ 2`. -/
example : JetDegreeCastsNeZero zeroDivisorEquation 0 := by
  intro k hk hk2
  rw [jetDegree_zeroDivisorEquation] at hk2
  interval_cases k <;> decide

/-- Over `ZMod 4`, `2 * Y₀ ^ 2` has no separant chain: its separant `4 * Y₀` is zero. -/
example : ¬ ∃ stages terminal, SeparantChain zeroDivisorEquation stages terminal := by
  rintro ⟨stages, terminal, hc⟩
  have hhighest : highestActiveJet zeroDivisorEquation = some 0 :=
    highestActiveJet_eq_zero (by simp [DependsOnJet, jetDegree_zeroDivisorEquation])
  have hsep : separant zeroDivisorEquation 0 = 0 := by
    rw [separant, pderiv_monomial, monomial_eq_zero, Finsupp.single_eq_same]
    decide
  cases hc with
  | terminal _ hterminal => rw [hhighest] at hterminal; cases hterminal
  | active j _ hj next =>
      rw [hhighest] at hj
      cases hj
      exact next.ne_zero hsep

/-! ### The exceptional set is needed -/

/-- `X * Y₀` over `ℚ[X]`. -/
private abbrev challengeEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  C Polynomial.X * X (some 0)

private theorem separant_challengeEquation :
    separant challengeEquation 0 = C Polynomial.X := by
  simp [separant, pderiv_X]

private theorem natDegree_coeff_challengeEquation_le (u : JetVariable 0 →₀ ℕ) :
    (challengeEquation.coeff u).natDegree ≤ 1 := by
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

private theorem challengeChain :
    SeparantChain challengeEquation [(challengeEquation, 0)] (C Polynomial.X) := by
  have hjet : jetDegree challengeEquation 0 = 1 := by
    rw [jetDegree, (degreeOf_mul_X_eq_degreeOf_add_one_iff _ _).mpr
      (by simp [Polynomial.X_ne_zero]), degreeOf_C]
  refine .active 0 (by simp [Polynomial.X_ne_zero])
    (highestActiveJet_eq_zero (by simp [DependsOnJet, hjet])) ?_
  rw [separant_challengeEquation]
  exact .terminal (by simp [Polynomial.X_ne_zero]) (highestActiveJet_C _)

/-- `exists_finset_regular_stage` applies with at most one exceptional value. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ P : Polynomial ℚ,
      differentialSpecialization
        (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) challengeEquation) P = 0 →
      ∃ stage ∈ [(challengeEquation, (0 : Fin 1))],
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1) P = 0 ∧
        differentialSpecialization
          (separant (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1)
            stage.2) P ≠ 0 :=
  challengeChain.exists_finset_regular_stage natDegree_coeff_challengeEquation_le
    (RingHom.id ℚ) Function.injective_id

/-- At `z = 0` the specialized equation is zero, so `P = 0` solves it and no stage is regular:
every exceptional set with the covering property contains `0`. -/
example (exceptional : Finset ℚ)
    (hcover : ∀ z ∉ exceptional, ∀ P : Polynomial ℚ,
      differentialSpecialization
        (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) challengeEquation) P = 0 →
      ∃ stage ∈ [(challengeEquation, (0 : Fin 1))],
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1) P = 0 ∧
        differentialSpecialization
          (separant (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1)
            stage.2) P ≠ 0) :
    (0 : ℚ) ∈ exceptional := by
  have hzero :
      MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) challengeEquation = 0 := by
    simp
  by_contra h0
  obtain ⟨stage, hstage, -, hsep⟩ := hcover 0 h0 0 (by
    rw [hzero, ← differentialSpecializationHom_apply, map_zero])
  rw [List.mem_singleton] at hstage
  subst hstage
  apply hsep
  rw [hzero, separant, map_zero, ← differentialSpecializationHom_apply, map_zero]

/-! ### Derived forms -/

/-- The existence theorem over a coefficient ring `F[X]` for a field `F`, with the characteristic
guard stated for `F`. -/
example {F : Type*} [Field F] {d : ℕ} (Q : DifferentialPolynomial (Polynomial F) d) (hne : Q ≠ 0)
    (hchar : ringChar F = 0 ∨ jetTotalDegree Q < ringChar F) :
    ∃ stages terminal, SeparantChain Q stages terminal :=
  exists_separantChain_of_ringChar hne (by rwa [ringChar.eq (Polynomial F) (ringChar F)])

/-- The existence theorem with the cast hypothesis up to the total jet degree. -/
example {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {d : ℕ}
    (Q : DifferentialPolynomial R d) (hne : Q ≠ 0)
    (hcast : ∀ m : ℕ, 0 < m → m ≤ jetTotalDegree Q → (m : R) ≠ 0) :
    ∃ stages terminal, SeparantChain Q stages terminal :=
  exists_separantChain hne fun j k hk hkj ↦ hcast k hk (hkj.trans (jetDegree_le_total Q j))

/-- The properties of every stage, as one conjunction. -/
example {R : Type*} [CommSemiring R] {d : ℕ} {Q terminal : DifferentialPolynomial R d}
    {stages : List (SeparantStage R d)} (hc : SeparantChain Q stages terminal) :
    ∀ stage ∈ stages, stage.1 ≠ 0 ∧ highestActiveJet stage.1 = some stage.2 ∧
      jetTotalDegree stage.1 ≤ jetTotalDegree Q ∧ ∀ j, jetDegree stage.1 j ≤ jetDegree Q j :=
  fun _ hstage ↦ ⟨hc.ne_zero_of_mem hstage, hc.highestActiveJet_eq_of_mem hstage,
    hc.jetTotalDegree_le_of_mem hstage, hc.jetDegree_le_of_mem hstage⟩

/-- The coefficient height bound for every stage and the terminal equation, as one conjunction. -/
example {F : Type*} [Field F] {d : ℕ} {Q terminal : DifferentialPolynomial (Polynomial F) d}
    {stages : List (SeparantStage (Polynomial F) d)} (hc : SeparantChain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) :
    (∀ stage ∈ stages, ∀ u, (stage.1.coeff u).natDegree ≤ h) ∧
      ∀ u, (terminal.coeff u).natDegree ≤ h :=
  ⟨fun _ hstage ↦ hc.natDegree_coeff_le_of_mem hQ hstage, hc.natDegree_coeff_terminal_le hQ⟩

/-- A presentation of every stage at its highest active jet, with the coefficient height bound. -/
example {F : Type*} [Field F] {d : ℕ} {Q terminal : DifferentialPolynomial (Polynomial F) d}
    {stages : List (SeparantStage (Polynomial F) d)} (hc : SeparantChain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) (stage : SeparantStage (Polynomial F) d)
    (hstage : stage ∈ stages) :
    ∃ A : JetPrefixPresentation stage.1 stage.2,
      A.equation ≠ 0 ∧ jetTotalDegree A.equation = jetTotalDegree stage.1 ∧
      jetDegree A.equation (Fin.last stage.2.val) ≤ jetDegree Q stage.2 ∧
      ∀ u, (A.equation.coeff u).natDegree ≤ h := by
  obtain ⟨A, hne, htotal, hlast⟩ := hc.exists_jetPrefixPresentation_of_mem hstage
  exact ⟨A, hne, htotal, hlast,
    A.natDegree_coeff_equation_le (hc.natDegree_coeff_le_of_mem hQ hstage)⟩

/-- The exceptional-set form for a map between fields. -/
example {F E : Type*} [Field F] [Field E] {d : ℕ}
    {Q terminal : DifferentialPolynomial (Polynomial F) d}
    {stages : List (SeparantStage (Polynomial F) d)} (hc : SeparantChain Q stages terminal)
    {h : ℕ} (hQ : ∀ u, (Q.coeff u).natDegree ≤ h) (ι : F →+* E) :
    ∃ exceptional : Finset E, exceptional.card ≤ h ∧
      ∀ z ∉ exceptional, ∀ P : Polynomial E,
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0 →
        ∃ stage ∈ stages,
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) P = 0 ∧
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom ι z) stage.1) stage.2) P ≠ 0 :=
  hc.exists_finset_regular_stage hQ ι ι.injective

end

end PolynomialDifferential
