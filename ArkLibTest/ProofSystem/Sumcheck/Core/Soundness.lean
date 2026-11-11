/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibTest.ProofSystem.Sumcheck.Core.SingleRound
import Mathlib.Algebra.Field.ZMod

/-!
# Soundness of Sumcheck in the interaction layer

Exact probabilities of one-round runs against committed provers, and instances of the
transferred soundness theorem: committed, randomized and adaptive provers on false claims.
-/

namespace Sumcheck.Core.SoundnessTest

open Polynomial PFunctor Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory Interaction.Core.Legacy
  Sumcheck.Core.SingleRoundTest
open scoped ENNReal NNReal

noncomputable section

/-- The event that the verifier accepts a statement of the final Sumcheck language. -/
def accepted {R : Type} [CommSemiring R] {deg n : ℕ} {d : ℕ} (D : Fin d ↪ R)
    {Out : FreeM.PathAlong oracleSig (protocol R deg n) → Type} :
    Set (Observation oracleSig (protocol R deg n) Out
      (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) :=
  {obs | ∃ t, obs.2.2 = some t ∧ t ∈ (Spec.relationRound R n deg D (Fin.last n)).language}

/-- The soundness event of the Sumcheck languages is the acceptance event. -/
theorem soundnessEvent_eq {R : Type} [CommSemiring R] {deg n : ℕ} {d : ℕ} (D : Fin d ↪ R)
    {Out : FreeM.PathAlong oracleSig (protocol R deg n) → Type} :
    {obs : Observation oracleSig (protocol R deg n) Out
        (Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i)) |
      ∃ t, obs.2.2 = some t ∧
        (langProblem (Spec.relationRound R n deg D (Fin.last n)).language).language () t} =
      accepted D := by
  ext obs
  exact exists_congr fun t => and_congr_right fun _ => langProblem_language _ t

/-! ## Rejection -/

section Rejection

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg : ℕ} {d : ℕ}
  (D : Fin d ↪ R) {ι : Type} (amb : OracleSpec ι) {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl amb (StateT σ ProbComp))

/-- A committed message whose sum over the domain misses the target is rejected with probability
one, for every challenge implementation. -/
theorem rejection_one {Out : Type}
    (ch : QueryImpl (challengeSpec oracleSig (protocol R deg 1)) ProbComp)
    (q : R⦃≤ deg⦄[X]) (finish : R → Out) (c₀ : R)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i)
    (h : ∑ x ∈ Finset.univ.map D, q.val.eval x ≠ stmt.target) :
    letI : MeasurableSpace (Obs1 (R := R) (deg := deg) Out) := ⊤
    𝒟[experiment init impl ch ((verifier R deg 1 D amb).run stmt oStmt
        (oneRound amb q finish c₀))] {obs | obs.2.2 = none} = 1 := by
  let : MeasurableSpace R := ⊤
  rw [outcome_oneRound]
  have hall : obs1 amb D q finish stmt oStmt ⁻¹' {obs | obs.2.2 = none} = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    change Option.map _ _ = none
    rw [verdict_fail amb D stmt q c h]
    rfl
  rw [hall]
  exact OracleComp.evalDist_apply_univ_eq_one _

end Rejection

/-! ## Universal one-round soundness -/

-- Migration rows: Sumcheck Interaction/Soundness #25–#28.

section Universal

variable {R : Type} [Field R] [Fintype R] [DecidableEq R] [SampleableType R] {deg : ℕ} {d : ℕ}
  (D : Fin d ↪ R) {ι : Type} (amb : OracleSpec ι) {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl amb (StateT σ ProbComp))

/-- Against every prover, a false one-round claim is accepted into the final language with
probability at most `deg / |R|`. -/
theorem oneRound_soundness {Out : FreeM.PathAlong oracleSig (protocol R deg 1) → Type}
    (P : Prover oracleSig amb (protocol R deg 1) Out)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i)
    (hfalse : (stmt, oStmt) ∉ (Spec.relationRound R 1 deg D 0).language) :
    letI : MeasurableSpace (Observation oracleSig (protocol R deg 1) Out
      (Spec.StatementRound R 1 (Fin.last 1) × (∀ i, Spec.OracleStatement R 1 deg i))) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol R deg 1))
        ((verifier R deg 1 D amb).run stmt oStmt P)] (accepted D) ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  let : MeasurableSpace (Observation oracleSig (protocol R deg 1) Out
      (Spec.StatementRound R 1 (Fin.last 1) × (∀ i, Spec.OracleStatement R 1 deg i))) := ⊤
  have h := verifier_soundness_rounds R deg 1 D amb init impl Out (stmt, oStmt) trivial
    (by simpa only [langProblem_language] using hfalse) P
  rw [Nat.cast_one, one_mul] at h
  rw [← soundnessEvent_eq]
  exact h

/-- A committed message obeys the one-round bound. -/
theorem committed_soundness {Out : Type} (q : R⦃≤ deg⦄[X]) (finish : R → Out) (c₀ : R)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i)
    (hfalse : (stmt, oStmt) ∉ (Spec.relationRound R 1 deg D 0).language) :
    letI : MeasurableSpace (Obs1 (R := R) (deg := deg) Out) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol R deg 1))
        ((verifier R deg 1 D amb).run stmt oStmt (oneRound amb q finish c₀))] (accepted D) ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
  oneRound_soundness D amb init impl _ stmt oStmt hfalse

/-- The prover that obtains its message from an ambient computation and commits to it. -/
def randomCommitted {Out : Type} (commit : OracleComp amb (R⦃≤ deg⦄[X])) (finish : R → Out)
    (c₀ : R) : Prover oracleSig amb (protocol R deg 1) (fun _ => Out) :=
  show OracleComp amb _ from commit >>= fun q => oneRound amb q finish c₀

/-- A message committed by an arbitrary ambient computation, sampled before the round, obeys
the same bound. -/
theorem randomCommitment_soundness {Out : Type} (commit : OracleComp amb (R⦃≤ deg⦄[X]))
    (finish : R → Out) (c₀ : R)
    (stmt : Spec.StatementRound R 1 0) (oStmt : ∀ i, Spec.OracleStatement R 1 deg i)
    (hfalse : (stmt, oStmt) ∉ (Spec.relationRound R 1 deg D 0).language) :
    letI : MeasurableSpace (Obs1 (R := R) (deg := deg) Out) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol R deg 1))
        ((verifier R deg 1 D amb).run stmt oStmt
          (randomCommitted amb commit finish c₀))] (accepted D) ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) :=
  oneRound_soundness D amb init impl _ stmt oStmt hfalse

end Universal

/-! ## A cheating committed message over `ZMod 17` -/

-- Migration row: Sumcheck Interaction/Soundness #3.

/-- Seventeen is prime. -/
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The field with seventeen elements. -/
abbrev K := ZMod 17

/-- The domain `{0}`. -/
def D₀₁₇ : Fin 1 ↪ K := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

@[simp] theorem D₀₁₇_apply (i : Fin 1) : D₀₁₇ i = 0 := rfl

/-- The polynomial `X₀` in one variable over `ZMod 17`. -/
def polyXK : Spec.OracleStatement K 1 1 () :=
  ⟨MvPolynomial.X 0, by
    rw [MvPolynomial.mem_restrictDegree]
    intro s hs i
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hs
    subst hs
    rw [Finsupp.single_apply]
    split_ifs <;> omega⟩

/-- The constant cheating message one. -/
def cheating : K⦃≤ 1⦄[X] := ⟨1, Polynomial.mem_degreeLE.mpr (by
  rw [← C_1]; exact degree_C_le.trans (by exact_mod_cast Nat.zero_le _))⟩

/-- The claim that `X₀` sums to one over `{0}` is false: the sum is zero. -/
theorem claim_false :
    ((⟨1, Fin.elim0⟩, fun _ => polyXK) : Spec.StatementRound K 1 0 × _) ∉
      (Spec.relationRound K 1 1 D₀₁₇ 0).language := by
  simp [Set.language, Spec.relationRound, polyXK, D₀₁₇_apply]

/-- The committed cheating message on the false claim is accepted into the final language with
probability at most `1/17`. -/
example {σ Out : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (finish : K → Out) (c₀ : K) :
    letI : MeasurableSpace (Obs1 (R := K) (deg := 1) Out) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol K 1 1))
        ((verifier K 1 1 D₀₁₇ ambient).run ⟨1, Fin.elim0⟩ (fun _ => polyXK)
          (oneRound ambient cheating finish c₀))] (accepted D₀₁₇) ≤ 1 / 17 := by
  refine (committed_soundness D₀₁₇ ambient init impl cheating finish c₀ _ _ claim_false).trans ?_
  rw [ZMod.card]
  norm_num

/-! ## Exact probabilities over `ZMod 5` -/

section Exact

open Sumcheck.Core.CompletenessTest

/-- Five is prime. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {Out : Type} (finish : F → Out) (c₀ : F)

/-- The zero message. -/
def msgZero (deg : ℕ) : F⦃≤ deg⦄[X] := ⟨0, Polynomial.mem_degreeLE.mpr (by simp)⟩

-- Migration rows: Sumcheck Interaction/Soundness #5, #15.

/-- A failed sum check rejects with probability one: the zero message on the false claim that
the zero polynomial sums to one over `{0, 1}`. -/
theorem rejection_probability {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    letI : MeasurableSpace (Obs1 (R := F) (deg := 1) Out) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol F 1 1))
        ((verifier F 1 1 D₂ ambient).run (claim 1) (fun _ => poly0 1)
          (oneRound ambient (msgZero 1) finish c₀))] {obs | obs.2.2 = none} = 1 :=
  rejection_one D₂ ambient init impl (challengeQueryImpl oracleSig (protocol F 1 1)) (msgZero 1)
    finish c₀ (claim 1) (fun _ => poly0 1) (by
    simp [msgZero, claim])

-- Migration rows: Sumcheck Interaction/Soundness #6, #16.

/-- Exactly the challenge zero repairs the false claim that the zero polynomial sums to one over
`{0, 1}` with the message `X`: the final language is reached with probability exactly `1/5`. -/
theorem exact_repair_probability (impl : QueryImpl ambient (StateT Unit ProbComp)) :
    letI : MeasurableSpace (Obs1 (R := F) (deg := 1) Out) := ⊤
    𝒟[experiment (pure ()) impl (challengeQueryImpl oracleSig (protocol F 1 1))
        ((verifier F 1 1 D₂ ambient).run (claim 1) (fun _ => poly0 1)
          (oneRound ambient msgX finish c₀))] (accepted D₂) = 1 / 5 := by
  let : MeasurableSpace F := ⊤
  have : MeasurableSingletonClass F := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  rw [outcome_oneRound]
  have hpass (c : F) := verdict_pass ambient D₂ (claim 1) msgX c (by
    simp [msgX, D₂, claim, Fin.sum_univ_two])
  have h : obs1 ambient D₂ msgX finish (claim 1) (fun _ => poly0 1) ⁻¹' accepted D₂ =
      {0} := by
    ext c
    change (∃ t, Option.map _ _ = some t ∧ _) ↔ _
    rw [hpass c]
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    have hch : Fin.snoc (claim 1).challenges c = fun _ : Fin 1 => c :=
      funext fun i => by fin_cases i; rfl
    have hX : msgX.val.eval c = c := by simp [msgX]
    have hiff := relationLast_iff D₂ (poly0 1) (msgX.val.eval c) c
    rw [eval_poly0] at hiff
    rw [hch, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, ⟨⟩⟩, hw, rfl⟩
      exact ((hiff.1 hw).trans hX).symm
    · rintro rfl
      exact ⟨(_, ()), hiff.2 hX.symm, rfl⟩
  rw [h]
  change 𝒟[($ᵗ F : ProbComp F)] _ = _
  rw [SampleableType.evalDist_uniformSample_eq_encard_div, Set.encard_singleton, ZMod.card]
  norm_num

-- Migration rows: Sumcheck Interaction/Soundness #12, #23.

/-- Over the empty domain every message sums to zero, so every message rejects the target one
with probability one. -/
theorem empty_domain_rejection {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (p : Spec.OracleStatement F 1 1 ())
    (q : F⦃≤ 1⦄[X]) :
    letI : MeasurableSpace (Obs1 (R := F) (deg := 1) Out) := ⊤
    𝒟[experiment init impl (challengeQueryImpl oracleSig (protocol F 1 1))
        ((verifier F 1 1 D₀ ambient).run (claim 1) (fun _ => p)
          (oneRound ambient q finish c₀))] {obs | obs.2.2 = none} = 1 :=
  rejection_one D₀ ambient init impl (challengeQueryImpl oracleSig (protocol F 1 1)) q finish c₀
    (claim 1) (fun _ => p) (by
    rw [Finset.univ_eq_empty, Finset.map_empty, Finset.sum_empty]
    exact (by decide : (0 : F) ≠ 1))

-- Migration rows: Sumcheck Interaction/Soundness #10, #21.


-- Migration rows: Sumcheck Interaction/Soundness #7, #8, #9, #11.

/-- The degree-one message carrier excludes `X ^ 2`. -/
theorem excludes_quadratic : (X ^ 2 : F[X]) ∉ Polynomial.degreeLE F 1 := by
  rw [Polynomial.mem_degreeLE, Polynomial.degree_X_pow]
  decide

/-- A degree-two message chosen with knowledge of the challenge `r`: it passes the false claim
that the zero polynomial sums to one over `{0, 1}` and vanishes at `r`. -/
def adaptive (r : F) : F⦃≤ 2⦄[X] :=
  if r = 1 then ⟨1 - X, Polynomial.mem_degreeLE.mpr (by
    apply Polynomial.degree_le_of_natDegree_le
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp))⟩
  else ⟨C (1 - r)⁻¹ * (X * (X - C r)), Polynomial.mem_degreeLE.mpr (by
    apply Polynomial.degree_le_of_natDegree_le
    apply (Polynomial.natDegree_mul_le).trans
    simp only [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_mul_le).trans
    simp)⟩

/-- The adaptive polynomial has endpoint sum one. -/
theorem adaptive_endpoints (r : F) :
    (adaptive r).val.eval 0 + (adaptive r).val.eval 1 = 1 := by
  by_cases h : r = 1
  · simp [adaptive, h]
  · simp [adaptive, h, sub_ne_zero.mpr (Ne.symm h)]

/-- The adaptive polynomial vanishes at the selected challenge. -/
theorem adaptive_hits (r : F) : (adaptive r).val.eval r = 0 := by
  by_cases h : r = 1 <;> simp [adaptive, h]

open Classical in
/-- The challenge implementation that answers the challenge of a one-round run with `r`. -/
def fixedAt (r : F) : QueryImpl (challengeSpec oracleSig (protocol F 2 1)) ProbComp := fun c =>
  if h : c = headNode 0 then
    h ▸ (pure r : ProbComp ((challengeSpec oracleSig (protocol F 2 1)).Range (headNode 0)))
  else $ᵗ _

/-- If the challenge is sampled before the message, the adaptive message reaches the final
language with probability one: the order of sampling matters. -/
theorem challenge_first_probability (impl : QueryImpl ambient (StateT Unit ProbComp)) :
    letI : MeasurableSpace (Obs1 (R := F) (deg := 2) Out) := ⊤
    𝒟[($ᵗ F) >>= fun r => experiment (pure ()) impl (fixedAt r)
        ((verifier F 2 1 D₂ ambient).run (claim 1) (fun _ => poly0 2)
          (oneRound ambient (adaptive r) finish c₀))] (accepted D₂) = 1 := by
  let : MeasurableSpace (Obs1 (R := F) (deg := 2) Out) := ⊤
  let : MeasurableSpace F := ⊤
  have hprog : (($ᵗ F) >>= fun r => experiment (pure ()) impl (fixedAt r)
      ((verifier F 2 1 D₂ ambient).run (claim 1) (fun _ => poly0 2)
        (oneRound ambient (adaptive r) finish c₀))) =
      (fun r => obs1 ambient D₂ (adaptive r) finish (claim 1) (fun _ => poly0 2) r) <$>
        ($ᵗ F) := by
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun r => ?_
    rw [run_oneRound, experiment_drawOne]
    simp only [fixedAt, dite_true]
    rfl
  rw [hprog, evalDist_map _ measurable_from_top,
    Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  have hall : (fun r => obs1 ambient D₂ (adaptive r) finish (claim 1) (fun _ => poly0 2) r) ⁻¹'
      accepted D₂ = Set.univ := by
    refine Set.eq_univ_of_forall fun r => ?_
    change ∃ t, Option.map _ _ = some t ∧ _
    rw [verdict_pass ambient D₂ (claim 1) (adaptive r) r (by
      simpa [D₂, claim, Fin.sum_univ_two] using adaptive_endpoints r)]
    have hch : Fin.snoc (claim 1).challenges r = fun _ : Fin 1 => r :=
      funext fun i => by fin_cases i; rfl
    have hrel : (((⟨(adaptive r).val.eval r, fun _ => r⟩ : Spec.StatementRound F 1 (Fin.last 1)),
        fun _ => poly0 2), ()) ∈ Spec.relationRound F 1 2 D₂ (Fin.last 1) := by
      rw [relationLast_iff, eval_poly0, adaptive_hits]
    rw [hch]
    exact ⟨_, rfl, _, hrel, rfl⟩
  rw [hall]
  exact OracleComp.evalDist_apply_univ_eq_one _

/-- The challenge-first success exceeds the fresh-challenge bound `2 / 5` of one round with
degree-two messages over `F`. -/
theorem fresh_bound_lt_one : (2 : ℝ≥0∞) / 5 < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

end Exact

end

end Sumcheck.Core.SoundnessTest

-- Migration rows: Sumcheck Interaction/Soundness #13, #14, #15, #16, #17–#23, #25–#28.
run_cmd do
  for decl in [``Sumcheck.Core.SoundnessTest.oneRound_soundness,
      ``Sumcheck.Core.SoundnessTest.committed_soundness,
      ``Sumcheck.Core.SoundnessTest.randomCommitment_soundness,
      ``Sumcheck.Core.SoundnessTest.rejection_one,
      ``Sumcheck.Core.SoundnessTest.rejection_probability,
      ``Sumcheck.Core.SoundnessTest.exact_repair_probability,
      ``Sumcheck.Core.SoundnessTest.empty_domain_rejection,
      ``Sumcheck.Core.SoundnessTest.challenge_first_probability,
      ``Sumcheck.Core.SoundnessTest.fresh_bound_lt_one,
      ``Sumcheck.Core.SoundnessTest.excludes_quadratic,
      ``Sumcheck.Core.SoundnessTest.adaptive, ``Sumcheck.Core.SoundnessTest.adaptive_endpoints,
      ``Sumcheck.Core.SoundnessTest.adaptive_hits, ``Sumcheck.Core.SingleRoundTest.poly0,
      ``Sumcheck.Core.CompletenessTest.polyX, ``Sumcheck.Core.SoundnessTest.polyXK,
      ``Sumcheck.Core.verifier_soundness, ``Sumcheck.Core.verifier_soundness_rounds,
      ``Sumcheck.Core.card_challengeIdx] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
