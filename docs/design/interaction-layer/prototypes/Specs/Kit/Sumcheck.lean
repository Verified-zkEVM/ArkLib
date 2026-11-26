/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Indexed
import Specs.Kit.Iteration
import Specs.Kit.ClaimReduction

/-!
# Sum-check through the generalized kit

This module proves the soundness theorem of ArkLib's indexed sum-check verifier,
`Sumcheck.indexedVerifier_soundness`, from the iteration theorem of `Specs.Kit.Iteration`. The
final theorem `indexedVerifier_soundness_viaKit` has exactly that statement, and an `example`
checks it against `type_of% @Sumcheck.indexedVerifier_soundness`.

Sum-check is the kit's simplest instance: no prefix, no suffix, and round `i` is the block
`[.oracle R⦃≤ deg⦄[X] I]` of one round polynomial followed by a ring challenge.

* `scRound`: the round; `scRounds`: the certificate that ArkLib's own tree
  `Sumcheck.protocol R deg k` is `k` such rounds. Each case holds by definition.
* `scStep`: the round update; `sumcheck_roundSound`: the per-round obligation, from the
  claim-reduction step `claimReduction_le`.
* `scVerdict_eq`: the kit's verdict is ArkLib's `Sumcheck.indexedVerdict`.
* `indexedVerifier_rbrSoundness_viaKit` and `indexedVerifier_soundness_viaKit`.

## Design choices

* **ArkLib's own verifier, not a kit-built one.** The theorem is about `indexedVerifier`
  itself, so it replaces ArkLib's proof without changing the verifier. Its acceptance enters the
  iteration theorem as the `accepts` predicate, and the only fact the kit needs about it is
  ArkLib's `indexed_validAcceptance` with `scVerdict_eq`.
* **The round's block is a list of one message.** The generalized round costs this instance
  nothing: the block's values are a pair of the polynomial and `PUnit`, and the certificate still
  holds by definition.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec MeasureTheory
open Sumcheck Polynomial MvPolynomial

section Sumcheck

variable (R : Type) [CommSemiring R] (deg : ℕ) {n d : ℕ}

/-- One sum-check round: the round polynomial as an evaluation oracle, then a ring challenge. -/
@[reducible]
def scRound : Round :=
  ⟨[.oracle (R⦃≤ deg⦄[X])
    (Interpreted.messageInterface (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r))], R⟩

/-- **Sum-check's tree is an instance.** Each case holds by definition of
`Sumcheck.protocol`. -/
def scRounds : (k j : ℕ) → (h : j + k = n) →
    Rounds (fun _ : Fin n => scRound R deg) [] j k h (protocol R deg k)
  | 0, j, h => by subst h; exact .done
  | k + 1, j, h => .round j k h (scRounds k (j + 1) (by omega))

variable {R deg} [DecidableEq R] (D : Fin d → R)

/-- The sum-check round update: check the indexed sum of the round polynomial, then move the
claim to its value at the challenge. -/
noncomputable def scStep : Step (fun _ : Fin n => scRound R deg) (RoundStatement R n) :=
  fun i (st : RoundStatement R n i.castSucc) (vals : R⦃≤ deg⦄[X] × PUnit) (r : R) =>
    if (∑ a, vals.1.val.eval (D a)) = st.target then
      some ⟨vals.1.val.eval r, Fin.snoc st.challenges r⟩ else none

/-- **The per-round obligation of sum-check, from the claim-reduction step.** If the round's
input claim is false, the check passes and the output claim is true with probability at most
`deg / |R|`. -/
theorem sumcheck_roundSound [IsDomain R] [Fintype R] [SampleableType R]
    (p : R⦃≤ deg⦄[X Fin n]) :
    RoundSound (fun _ => $ᵗ R) (scStep (deg := deg) D) (fun i st => indexedRelation D i st p)
      (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  intro i st vals hfalse
  have hevent : (fun r => ∃ st', scStep D i st vals r = some st' ∧
      indexedRelation D i.succ st' p) =
      (fun r => (∑ a, vals.1.val.eval (D a)) = st.target ∧
        indexedRelation D i.succ ⟨vals.1.val.eval r, Fin.snoc st.challenges r⟩ p) := by
    funext r
    by_cases hs : (∑ a, vals.1.val.eval (D a)) = st.target <;> simp [scStep, hs]
  simp only [hevent]
  refine claimReduction_le _ _ _ vals.1 (projectedRoundPolynomial D i st.challenges p)
    (fun hs hf => ?_) (fun r _ hr => ?_) hfalse
  · by_contra! h
    exact hf (((sum_projectedRoundPolynomial D i st.challenges p).symm.trans
      (Finset.sum_congr rfl fun a _ => (h (D a)).symm)).trans hs)
  · exact hr.symm.trans (roundSum_succ D i st.challenges p r)

omit [DecidableEq R] in
/-- The challenge draw of sum-check's tree is uniform in every round. -/
theorem scDrawIs [SampleableType R] : ∀ (k j : ℕ) (h : j + k = n),
    (scRounds R deg k j h).DrawIs (fun _ => $ᵗ R) (indexedDraw (R := R) (deg := deg) k)
  | 0, j, h => by subst h; exact True.intro
  | k + 1, j, h => fun _ => ⟨rfl, scDrawIs k (j + 1) (by omega)⟩

/-- The kit's verdict is `Sumcheck.indexedVerdict`. -/
theorem scVerdict_eq : ∀ (k j : ℕ) (h : j + k = n) (st : RoundStatement R n ⟨j, by omega⟩)
    (tr : Transcript oracleSig (protocol R deg k)),
    (scRounds R deg k j h).verdict (scStep D) (some st) tr =
      (indexedVerdict D k (some ⟨⟨j, by omega⟩, by simpa using h, st⟩) tr).map (·, ⟨⟩)
  | 0, j, h, st, tr => by subst h; rfl
  | k + 1, j, h, st, ⟨msg, r, tail⟩ => by
    rw [indexedVerdict_succ]
    change (scRounds R deg k (j + 1) (by omega)).verdict (scStep D)
      (scStep D ⟨j, by omega⟩ st (msg, ⟨⟩) r) tail = _
    unfold scStep indexedNext
    simp only [Interpreted.message, Interpreted.challenge, Interpreted.tail, Option.bind_some]
    by_cases hs : (∑ a, msg.val.eval (D a)) = st.target
    · simp only [hs, ↓reduceIte]
      exact scVerdict_eq k (j + 1) (by omega) ⟨msg.val.eval r, Fin.snoc st.challenges r⟩ tail
    · simp only [hs, ↓reduceIte, indexedVerdict_none, Option.map_none]
      exact Rounds.verdict_none _ _ _

/-- Round-by-round soundness of `Sumcheck.indexedVerifier`, from the iteration theorem. -/
theorem indexedVerifier_rbrSoundness_viaKit [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).rbrSoundness impl
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      (indexedDraw (R := R) (deg := deg) n)
      (fun c => (fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
        ((scRounds R deg n 0 (Nat.zero_add n)).iterRoundOf (pre := []) c)) := by
  refine (scRounds R deg n 0 (Nat.zero_add n)).rbrSoundness (pre := []) (S := RoundStatement R n)
    (Stmt := RoundStatement R n 0 × (∀ i, PolynomialData R n deg i))
    (admissible := (indexedInputProblem D).admissible ())
    (language := (indexedInputProblem D).language ())
    (accepts := fun stmt tr => (indexedVerifier R deg n D ambient).validAcceptance impl stmt tr
      ((indexedOutputProblem (R := R) (deg := deg) (n := n)).language tr.path))
    (fun x _ => some x.1) (fun _ => scStep D) (fun x i st => indexedRelation D i st (x.2 ()))
    (indexedDraw (R := R) (deg := deg) n) (fun _ => $ᵗ R) _
    (fun _ => scDrawIs n 0 (Nat.zero_add n)) (fun _ _ _ _ hs h => ?_) (fun x tr hacc => ?_)
    (fun x => sumcheck_roundSound D (x.2 ()))
  · cases hs
    exact ⟨(), h⟩
  · obtain ⟨t, ht, hl⟩ := indexed_validAcceptance D impl x tr hacc
    refine ⟨(t, ⟨⟩), ?_, (indexedRelation_last D t (x.2 ())).mpr hl⟩
    refine (scVerdict_eq D n 0 (Nat.zero_add n) x.1 tr).trans ?_
    rw [show indexedVerdict D n (some ⟨⟨0, _⟩, _, x.1⟩) tr = some t from ht]
    rfl

/-- **Sum-check soundness through the kit**, with exactly the statement of
`Sumcheck.indexedVerifier_soundness`. -/
theorem indexedVerifier_soundness_viaKit [IsDomain R] [Fintype R] [SampleableType R]
    {ι σ : Type} (ambient : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) :
    (indexedVerifier R deg n D ambient).soundness init impl
      (indexedDraw (R := R) (deg := deg) n)
      (indexedInputProblem D) (indexedOutputProblem (R := R) (deg := deg) (n := n))
      ((n : ℝ≥0∞) * (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞)) := by
  have h := (scRounds R deg n 0 (Nat.zero_add n)).soundness_of_rbrSoundness (pre := [])
    (init := init) (ε := fun _ => (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞))
    (indexedVerifier_rbrSoundness_viaKit D ambient impl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

/-- The kit's theorem has exactly the statement of ArkLib's. -/
example : type_of% @Sumcheck.indexedVerifier_soundness := @indexedVerifier_soundness_viaKit

end Sumcheck

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.sumcheck_roundSound
#print axioms Specs.Kit.indexedVerifier_rbrSoundness_viaKit
#print axioms Specs.Kit.indexedVerifier_soundness_viaKit
