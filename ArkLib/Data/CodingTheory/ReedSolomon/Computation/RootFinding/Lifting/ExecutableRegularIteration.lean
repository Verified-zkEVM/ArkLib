/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Step
/-!
# Executable iteration of regular coefficient lifting

This file iterates the executable one-coefficient regular lift.  Starting from a centered
polynomial containing the prescribed coefficients through degree `r`, stage `k` tests every field
element as the coefficient added in centered degree `k + r`.  Only candidates whose residual
coefficient at degree `k` vanishes survive.

The iteration result carries the exact number of field coefficients tested by those filters.  The
public solution list additionally checks the final residual and degree bound.  The latter check is
needed when `D < r`, where no lift stage runs and the supplied prefix need not itself have degree at
most `D`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {r : ℕ}

/-- Accepted values and the number of predicate evaluations used to obtain them. -/
@[ext]
structure EffectiveFilterScan (F : Type*) [DecidableEq F] where
  accepted : Finset F
  tested : ℕ

instance {F : Type*} [DecidableEq F] : Zero (EffectiveFilterScan F) :=
  ⟨⟨∅, 0⟩⟩

instance {F : Type*} [DecidableEq F] : Add (EffectiveFilterScan F) where
  add a b := ⟨a.accepted ∪ b.accepted, a.tested + b.tested⟩

instance {F : Type*} [DecidableEq F] : AddCommMonoid (EffectiveFilterScan F) where
  add_assoc a b c := by
    apply EffectiveFilterScan.ext
    · change (a.accepted ∪ b.accepted) ∪ c.accepted =
        a.accepted ∪ (b.accepted ∪ c.accepted)
      exact sup_assoc _ _ _
    · change (a.tested + b.tested) + c.tested = a.tested + (b.tested + c.tested)
      omega
  zero_add a := by
    apply EffectiveFilterScan.ext
    · change ∅ ∪ a.accepted = a.accepted
      simp
    · change 0 + a.tested = a.tested
      omega
  add_zero a := by
    apply EffectiveFilterScan.ext
    · change a.accepted ∪ ∅ = a.accepted
      simp
    · change a.tested + 0 = a.tested
      omega
  add_comm a b := by
    apply EffectiveFilterScan.ext
    · change a.accepted ∪ b.accepted = b.accepted ∪ a.accepted
      exact sup_comm _ _
    · change a.tested + b.tested = b.tested + a.tested
      omega
  nsmul := nsmulRec

@[simp] theorem EffectiveFilterScan.zero_accepted {F : Type*} [DecidableEq F] :
    (0 : EffectiveFilterScan F).accepted = ∅ := rfl

@[simp] theorem EffectiveFilterScan.zero_tested {F : Type*} [DecidableEq F] :
    (0 : EffectiveFilterScan F).tested = 0 := rfl

@[simp] theorem EffectiveFilterScan.add_accepted {F : Type*} [DecidableEq F]
    (a b : EffectiveFilterScan F) : (a + b).accepted = a.accepted ∪ b.accepted := rfl

@[simp] theorem EffectiveFilterScan.add_tested {F : Type*} [DecidableEq F]
    (a b : EffectiveFilterScan F) : (a + b).tested = a.tested + b.tested := rfl

private theorem mem_sum_effectiveFilterScan_accepted_iff
    {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A → EffectiveFilterScan B) (b : B) :
    b ∈ (∑ a ∈ s, f a).accepted ↔ ∃ a ∈ s, b ∈ (f a).accepted := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, EffectiveFilterScan.add_accepted]
      simp only [Finset.mem_union, ih, Finset.mem_insert]
      aesop

private theorem sum_effectiveFilterScan_tested
    {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A → EffectiveFilterScan B) :
    (∑ a ∈ s, f a).tested = ∑ a ∈ s, (f a).tested := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert, ha, ih]

/-- Scan every field element once with the effective residual-coefficient predicate. -/
def effectiveRegularCoefficientScan (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) : EffectiveFilterScan F :=
  ∑ gamma : F,
    if effectiveResidualCoeff Q center P k gamma = 0 then ⟨{gamma}, 1⟩ else ⟨∅, 1⟩

/-- Candidate prefixes together with the exact number of field coefficients tested so far. -/
structure EffectiveRegularIterationState (F : Type*) [Zero F] where
  /-- Centered polynomial prefixes which survived all completed stages. -/
  candidates : Finset (CPolynomial F)
  /-- Number of field coefficients passed to a residual-coefficient test. -/
  testedCoefficients : ℕ

/-- The actual predicate scan performed by one stage, retaining its source prefix with each
accepted coefficient. -/
def effectiveRegularStageScan (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (prefixes : Finset (CPolynomial F)) : EffectiveFilterScan (CPolynomial F × F) :=
  ∑ P ∈ prefixes, ∑ gamma : F,
    if effectiveResidualCoeff Q center P k gamma = 0 then ⟨{(P, gamma)}, 1⟩ else ⟨∅, 1⟩

@[simp]
theorem mem_effectiveRegularCoefficientScan_accepted
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (k : ℕ) (gamma : F) :
    gamma ∈ (effectiveRegularCoefficientScan Q center P k).accepted ↔
      effectiveResidualCoeff Q center P k gamma = 0 := by
  rw [effectiveRegularCoefficientScan,
    mem_sum_effectiveFilterScan_accepted_iff (Finset.univ : Finset F)]
  constructor
  · rintro ⟨a, ha⟩
    split at ha <;> simp_all
  · intro h
    exact ⟨gamma, by simp [h]⟩

@[simp]
theorem effectiveRegularCoefficientScan_tested
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) (k : ℕ) :
    (effectiveRegularCoefficientScan Q center P k).tested = Fintype.card F := by
  rw [effectiveRegularCoefficientScan,
    sum_effectiveFilterScan_tested (Finset.univ : Finset F)]
  have hterm : ∀ gamma : F,
      (if effectiveResidualCoeff Q center P k gamma = 0 then
          (⟨{gamma}, 1⟩ : EffectiveFilterScan F) else ⟨∅, 1⟩).tested = 1 := by
    intro gamma
    split <;> rfl
  simp_rw [hterm]
  simp

@[simp]
theorem mem_effectiveRegularStageScan_accepted
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (prefixes : Finset (CPolynomial F)) (P : CPolynomial F) (gamma : F) :
    (P, gamma) ∈ (effectiveRegularStageScan Q center k prefixes).accepted ↔
      P ∈ prefixes ∧ effectiveResidualCoeff Q center P k gamma = 0 := by
  rw [effectiveRegularStageScan,
    mem_sum_effectiveFilterScan_accepted_iff prefixes]
  simp only [mem_sum_effectiveFilterScan_accepted_iff (Finset.univ : Finset F)]
  constructor
  · rintro ⟨P', hP', gamma', hmem⟩
    split at hmem <;> simp_all
  · rintro ⟨hP, hresidual⟩
    exact ⟨P, hP, gamma, by simp [hresidual]⟩

@[simp]
theorem effectiveRegularStageScan_tested
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (prefixes : Finset (CPolynomial F)) :
    (effectiveRegularStageScan Q center k prefixes).tested =
      prefixes.card * Fintype.card F := by
  rw [effectiveRegularStageScan, sum_effectiveFilterScan_tested prefixes]
  simp only [sum_effectiveFilterScan_tested (Finset.univ : Finset F)]
  have hterm : ∀ (P : CPolynomial F) (gamma : F),
      (if effectiveResidualCoeff Q center P k gamma = 0 then
          (⟨{(P, gamma)}, 1⟩ : EffectiveFilterScan (CPolynomial F × F))
        else ⟨∅, 1⟩).tested = 1 := by
    intro P gamma
    split <;> rfl
  simp_rw [hterm]
  simp

/-- Run one lifting stage on every surviving prefix.

For each input prefix this tests all `Fintype.card F` field elements, retains exactly the elements
accepted by `effectiveRegularCoefficients`, and adds them in centered degree `k + r`.
-/
def effectiveRegularIterationStep (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (state : EffectiveRegularIterationState F) : EffectiveRegularIterationState F :=
  let scan := effectiveRegularStageScan Q center k state.candidates
  ⟨scan.accepted.image fun pair => effectiveRegularCandidate k r pair.1 pair.2,
    state.testedCoefficients + scan.tested⟩

/-- Iterate regular lifting for `steps` successive coefficients, beginning with residual order one.
Stage `k` (one-indexed) adds the coefficient in centered degree `k + r`. -/
def effectiveRegularIteration (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) : ℕ → EffectiveRegularIterationState F
  | 0 => ⟨{P}, 0⟩
  | steps + 1 =>
      effectiveRegularIterationStep Q center (steps + 1)
        (effectiveRegularIteration Q center P steps)

/-- Prefixes obtained after filling all centered coefficients above `r` through degree `D`. -/
def effectiveRegularPrefixes (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (D : ℕ) : Finset (CPolynomial F) :=
  (effectiveRegularIteration Q center P (D - r)).candidates

/-- Exact number of field coefficients tested while constructing `effectiveRegularPrefixes`. -/
def effectiveRegularTestCount (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (D : ℕ) : ℕ :=
  (effectiveRegularIteration Q center P (D - r)).testedCoefficients

/-- Degree-bounded prefixes whose complete executable residual is zero.

The final residual test prevents a locally consistent prefix from being reported as a solution.
The degree test also handles the zero-stage case `D < r`.
-/
def effectiveRegularSolutions (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (D : ℕ) : Finset (CPolynomial F) :=
  (effectiveRegularPrefixes Q center P D).filter fun candidate =>
    decide (candidate.natDegree ≤ D) && (effectiveResidual Q center candidate == 0)

@[simp]
theorem effectiveRegularIteration_zero (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) :
    effectiveRegularIteration Q center P 0 = ⟨{P}, 0⟩ :=
  rfl

@[simp]
theorem effectiveRegularIteration_succ (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (steps : ℕ) :
    effectiveRegularIteration Q center P (steps + 1) =
      effectiveRegularIterationStep Q center (steps + 1)
        (effectiveRegularIteration Q center P steps) :=
  rfl

@[simp]
theorem effectiveRegularIterationStep_testedCoefficients
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (state : EffectiveRegularIterationState F) :
    (effectiveRegularIterationStep Q center k state).testedCoefficients =
      state.testedCoefficients +
        (effectiveRegularStageScan Q center k state.candidates).tested :=
  rfl

@[simp]
theorem effectiveRegularIteration_testCount_succ
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) (steps : ℕ) :
    (effectiveRegularIteration Q center P (steps + 1)).testedCoefficients =
      (effectiveRegularIteration Q center P steps).testedCoefficients +
        (effectiveRegularStageScan Q center (steps + 1)
          (effectiveRegularIteration Q center P steps).candidates).tested :=
  rfl

/-- Membership in one iteration step exposes the surviving prefix and tested coefficient. -/
theorem mem_effectiveRegularIterationStep_candidates
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (state : EffectiveRegularIterationState F) (candidate : CPolynomial F) :
    candidate ∈ (effectiveRegularIterationStep Q center k state).candidates ↔
      ∃ P ∈ state.candidates, ∃ gamma ∈ effectiveRegularCoefficients Q center P k,
        effectiveRegularCandidate k r P gamma = candidate := by
  simp only [effectiveRegularIterationStep, Finset.mem_image]
  aesop

/-- Every initial prefix is present before the first lift stage. -/
@[simp]
theorem mem_effectiveRegularIteration_zero_iff
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P candidate : CPolynomial F) :
    candidate ∈ (effectiveRegularIteration Q center P 0).candidates ↔ candidate = P := by
  simp [effectiveRegularIteration]

/-- A prefix survives the next stage exactly when it is a retained lift of a previous prefix. -/
theorem mem_effectiveRegularIteration_succ_candidates
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P candidate : CPolynomial F)
    (steps : ℕ) :
    candidate ∈ (effectiveRegularIteration Q center P (steps + 1)).candidates ↔
      ∃ previous ∈ (effectiveRegularIteration Q center P steps).candidates,
        ∃ gamma ∈ effectiveRegularCoefficients Q center previous (steps + 1),
          effectiveRegularCandidate (steps + 1) r previous gamma = candidate := by
  rw [effectiveRegularIteration_succ]
  exact mem_effectiveRegularIterationStep_candidates _ _ _ _ _

/-- Every reported solution passed both the explicit degree check and final residual check. -/
theorem mem_effectiveRegularSolutions_iff
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P candidate : CPolynomial F) (D : ℕ) :
    candidate ∈ effectiveRegularSolutions Q center P D ↔
      candidate ∈ effectiveRegularPrefixes Q center P D ∧
        candidate.natDegree ≤ D ∧ effectiveResidual Q center candidate = 0 := by
  simp [effectiveRegularSolutions]

/-- With the prefix invariant established on every input, stage membership is exactly the
existence of a one-coefficient lift satisfying the next residual-divisibility invariant. -/
theorem mem_effectiveRegularIterationStep_candidates_iff_dvd
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (k : ℕ)
    (state : EffectiveRegularIterationState F) (candidate : CPolynomial F) (hk : 0 < k)
    (hprefix : ∀ P ∈ state.candidates, Polynomial.X ^ k ∣
      shiftedJetSubstitution center (unshift center P) (semanticEquation Q)) :
    candidate ∈ (effectiveRegularIterationStep Q center k state).candidates ↔
      ∃ P ∈ state.candidates, ∃ gamma : F,
        effectiveRegularCandidate k r P gamma = candidate ∧
        Polynomial.X ^ (k + 1) ∣ shiftedJetSubstitution center
          (unshift center candidate) (semanticEquation Q) := by
  rw [mem_effectiveRegularIterationStep_candidates]
  constructor
  · rintro ⟨P, hP, gamma, hgamma, rfl⟩
    exact ⟨P, hP, gamma, rfl,
      (mem_effectiveRegularCoefficients_iff_dvd Q center P gamma hk (hprefix P hP)).1
        hgamma⟩
  · rintro ⟨P, hP, gamma, rfl, hdiv⟩
    exact ⟨P, hP, gamma,
      (mem_effectiveRegularCoefficients_iff_dvd Q center P gamma hk (hprefix P hP)).2
        hdiv, rfl⟩

/-- Every surviving prefix has the residual divisibility promised by its iteration depth.
This is invariant preservation, not completeness of the final solution list. -/
theorem effectiveRegularIteration_residual_dvd
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (hinitial : Polynomial.X ∣
      shiftedJetSubstitution center (unshift center P) (semanticEquation Q))
    (steps : ℕ) :
    ∀ candidate ∈ (effectiveRegularIteration Q center P steps).candidates,
      Polynomial.X ^ (steps + 1) ∣ shiftedJetSubstitution center
        (unshift center candidate) (semanticEquation Q) := by
  induction steps with
  | zero =>
      intro candidate hcandidate
      have heq := (mem_effectiveRegularIteration_zero_iff Q center P candidate).1 hcandidate
      simpa [heq] using hinitial
  | succ steps ih =>
      intro candidate hcandidate
      obtain ⟨previous, hprevious, gamma, hgamma, rfl⟩ :=
        (mem_effectiveRegularIteration_succ_candidates Q center P candidate steps).1 hcandidate
      exact (mem_effectiveRegularCoefficients_iff_dvd Q center previous gamma
        (Nat.succ_pos steps) (ih previous hprevious)).1 hgamma

end ReedSolomon.HiddenDerivative
