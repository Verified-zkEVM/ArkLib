/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Indexed
import Specs.Kit.Verifier
import Specs.Kit.ClaimReduction

/-!
# A kit instance whose rounds send two messages

This module exercises blocks of several messages and the kit's passive verifier
(`Specs.Kit.Verifier`). The protocol is sum-check in which round `i` sends two messages:

* the round polynomial `gᵢ`, as an evaluation oracle;
* its claimed sum `σᵢ` over the domain `D`, as a plain message;

then receives a ring challenge `rᵢ`. After the last round, the prover sends the claimed final
value as a plain message (the suffix). The verifier

* in round `i`, compares `σᵢ` with the current target, queries `gᵢ` at every point of `D` to
  check that the values sum to `σᵢ`, and moves the target to `gᵢ(rᵢ)` with one more query;
* at the end, compares the claimed final value with the target and outputs the final statement.

`twoProtocol deg k` is the tree by its own recursion, `twoRounds` certifies it, `twoCheck` and
`twoFinish` are the verifier's programs, and `twoVerifier` is the kit-built verifier.
`twoVerifier_soundness` proves it sound with error `n * deg / |R|` from the kit's verifier
theorem `Rounds.verifier_soundness`.

## Design choices

* **The plain message is checked without a query.** The verifier reads `σᵢ` from its view, so the
  check compares it directly. This is the case that a block of only oracle messages cannot
  express.
* **The per-round obligation reuses the claim-reduction step.** The check passes only if `gᵢ`
  sums to the target, which is the hypothesis of `claimReduction_le` for sum-check.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec MeasureTheory
open Sumcheck Polynomial MvPolynomial

section TwoMessage

variable (R : Type) [CommSemiring R] (deg : ℕ) {n d : ℕ}

/-- The round polynomial's evaluation interface. -/
@[reducible]
noncomputable def polyIface : OracleInterface (R⦃≤ deg⦄[X]) :=
  Interpreted.messageInterface (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)

/-- One round: the round polynomial as an oracle and its claimed sum as a plain message, then a
ring challenge. -/
@[reducible]
noncomputable def twoRound : Round := ⟨[.oracle (R⦃≤ deg⦄[X]) (polyIface R deg), .plain R], R⟩

/-- The suffix: the claimed final value. -/
@[reducible]
def twoSuffix : Block := [.plain R]

/-- **The protocol, by its own recursion**, with `k` rounds left. -/
noncomputable def twoProtocol : ℕ → OracleProtocol
  | 0 => .liftBind (.message R) fun _ => .pure PUnit.unit
  | k + 1 => .liftBind (.oracle (R⦃≤ deg⦄[X]) (polyIface R deg)) fun _ =>
      .liftBind (.message R) fun _ => .liftBind (.challenge R) fun _ => twoProtocol k

/-- **The protocol is an instance.** Each case holds by definition of `twoProtocol`. -/
noncomputable def twoRounds : (k j : ℕ) → (h : j + k = n) →
    Rounds (fun _ : Fin n => twoRound R deg) (twoSuffix R) j k h (twoProtocol R deg k)
  | 0, j, h => by subst h; exact .done
  | k + 1, j, h => .round j k h (twoRounds k (j + 1) (by omega))

variable {R deg} [DecidableEq R] (D : Fin d → R)

/-- A query to the round polynomial, from a program on the round's block. -/
noncomputable def askPoly (a : R) :
    OracleComp ((polynomialFamily R n deg).sum (Block.bundle (twoRound R deg).msgs)).spec R :=
  liftM (((polynomialFamily R n deg).sum (Block.bundle (twoRound R deg).msgs)).spec.query
    (.inr (.inl a)))

/-- **The round check.** Compare the claimed sum with the target, check it against the round
polynomial's values on `D`, then move the target to the polynomial's value at the challenge. -/
noncomputable def twoCheck :
    Check (polynomialFamily R n deg) (fun _ : Fin n => twoRound R deg) (RoundStatement R n) :=
  fun i (st : RoundStatement R n i.castSucc) (vals : (twoRound R deg).msgs.ViewValues)
      (r : R) => OptionT.mk do
    let σ : R := vals.2.1
    if σ = st.target then
      let values ← (List.finRange d).mapM fun a => askPoly (n := n) (deg := deg) (D a)
      if values.sum = σ then
        let value ← askPoly (n := n) (deg := deg) r
        return some ⟨value, Fin.snoc st.challenges r⟩
      else return none
    else return none

/-- The round update that the check computes. -/
noncomputable def twoStep : Step (fun _ : Fin n => twoRound R deg) (RoundStatement R n) :=
  fun i (st : RoundStatement R n i.castSucc) (vals : R⦃≤ deg⦄[X] × R × PUnit) (r : R) =>
    if vals.2.1 = st.target then
      if (∑ a, vals.1.val.eval (D a)) = vals.2.1 then
        some ⟨vals.1.val.eval r, Fin.snoc st.challenges r⟩ else none
    else none

/-- The check's queries compute the round update. -/
theorem twoCheck_step (data : (polynomialFamily R n deg).Data) (i : Fin n)
    (st : RoundStatement R n i.castSucc) (vals : R⦃≤ deg⦄[X] × R × PUnit) (r : R) :
    (twoCheck (deg := deg) D).step data i st vals r = twoStep D i st vals r := by
  unfold Check.step Block.run twoCheck twoStep
  change simulateQ _ (if vals.2.1 = st.target then _ else _) = _
  split
  · change simulateQ _ ((List.finRange d).mapM
      (fun a => askPoly (n := n) (deg := deg) (D a)) >>= _) = _
    simp only [simulateQ_bind, simulateQ_list_mapM]
    change ((List.finRange d).mapM (fun a => (pure (vals.1.val.eval (D a)) : Id R)) >>= _) = _
    simp only [List.mapM_pure, LawfulMonad.pure_bind]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    split <;> split <;> rename_i h1 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  · rfl

/-- **The final check.** Compare the claimed final value with the target. -/
def twoFinish : RoundStatement R n (Fin.last n) → (twoSuffix R).ViewValues →
    Block.Program (polynomialFamily R n deg) (twoSuffix R) (RoundStatement R n (Fin.last n)) :=
  fun st vals => OptionT.mk (pure (if vals.1 = st.target then some st else none))

/-- The input statement as the initial state. -/
def twoStart : RoundStatement R n 0 → Block.ViewValues [] →
    Block.Program (polynomialFamily R n deg) [] (RoundStatement R n 0) :=
  fun stmt _ => OptionT.mk (pure (some stmt))

/-- **The per-round obligation**, from the claim-reduction step. -/
theorem two_roundSound [IsDomain R] [Fintype R] [SampleableType R] (p : R⦃≤ deg⦄[X Fin n]) :
    RoundSound (fun _ => $ᵗ R) (twoStep (deg := deg) D) (fun i st => indexedRelation D i st p)
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  intro i st vals hfalse
  have hevent : (fun r => ∃ st', twoStep D i st vals r = some st' ∧
      indexedRelation D i.succ st' p) =
      (fun r => (vals.2.1 = st.target ∧ (∑ a, vals.1.val.eval (D a)) = vals.2.1) ∧
        indexedRelation D i.succ ⟨vals.1.val.eval r, Fin.snoc st.challenges r⟩ p) := by
    funext r
    by_cases h1 : vals.2.1 = st.target <;> by_cases h2 : (∑ a, vals.1.val.eval (D a)) = vals.2.1 <;>
      simp [twoStep, h1, h2]
  simp only [hevent]
  refine claimReduction_le _ _ _ vals.1 (projectedRoundPolynomial D i st.challenges p)
    (fun hs hf => ?_) (fun r _ hr => ?_) hfalse
  · by_contra! h
    exact hf (((sum_projectedRoundPolynomial D i st.challenges p).symm.trans
      (Finset.sum_congr rfl fun a _ => (h (D a)).symm)).trans (hs.2.trans hs.1))
  · exact hr.symm.trans (roundSum_succ D i st.challenges p r)

/-- The draw of the protocol: every challenge is uniform. -/
noncomputable def twoDraw [SampleableType R] :
    QueryImpl (challengeSpec oracleSig (twoProtocol R deg n)) ProbComp :=
  (twoRounds R deg n 0 (Nat.zero_add n)).challengeDraw fun _ => $ᵗ R

variable (R deg n)

/-- The output problem: the final evaluation claim. -/
def twoOutputProblem :
    StatementProblem (RoundStatement R n (Fin.last n) × (∀ i, PolynomialData R n deg i)) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ stmt _ := (stmt.2 ()).val.eval stmt.1.challenges = stmt.1.target
  rel_admissible _ _ _ _ := trivial

variable {R deg n}

/-- **The kit-built verifier.** -/
noncomputable def twoVerifier {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier ambient (Block.then [] (twoProtocol R deg n)) (RoundStatement R n 0)
      (fun _ => RoundStatement R n (Fin.last n)) (polynomialFamily R n deg)
      (fun _ => polynomialFamily R n deg) :=
  (twoRounds R deg n 0 (Nat.zero_add n)).verifier (polynomialFamily R n deg) twoStart
    (twoCheck D) twoFinish ambient

/-- **Soundness of the two-message sum-check verifier, from the kit.** -/
theorem twoVerifier_soundness [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (twoVerifier D ambient).soundness init impl twoDraw (indexedInputProblem D)
      ((twoOutputProblem R deg n).toPathProblem _)
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := Rounds.verifier_soundness (polynomialFamily R n deg) twoStart (twoCheck D) twoFinish
    ambient (twoRounds R deg n 0 (Nat.zero_add n)) init impl (indexedInputProblem D)
    ((twoOutputProblem R deg n).toPathProblem _)
    (fun x i st => indexedRelation D i st (x.2 ())) twoDraw (fun _ => $ᵗ R)
    (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
    (fun _ => Rounds.drawIs_challengeDraw _ _) (fun x _ st _ hs h => ?_)
    (fun x _ q t ht hl => ?_) (fun x i st vals r => ?_)
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  · cases hs
    exact ⟨(), h⟩
  · obtain ⟨st, v, ⟨⟩⟩ := q
    change (if v = st.target then some st else none) = some t at ht
    split at ht
    · cases ht
      obtain ⟨_, hl⟩ := hl
      exact (indexedRelation_last D _ (x.2 ())).mpr hl
    · cases ht
  · rw [show (twoCheck D).step x.2 = twoStep D from
      funext fun i => funext fun st => funext fun vals => funext fun r =>
        twoCheck_step D x.2 i st vals r]
    exact two_roundSound D (x.2 ()) i st vals r

end TwoMessage

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.twoCheck_step
#print axioms Specs.Kit.two_roundSound
#print axioms Specs.Kit.twoVerifier_soundness
