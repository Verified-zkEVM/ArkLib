/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.ComputableProjection
public import ArkLib.ProofSystem.Sumcheck.Core.InterpretedExecution
public import ArkLib.ProofSystem.Sumcheck.Core.IntervalCompleteness

/-! # Computable honest interval provers and their execution -/

@[expose] public section

namespace Sumcheck.Core.Computable
open CPoly Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n d deg : ℕ} (D : Fin d → R) (poly : CMvPolynomial n R)
  (hpoly : ∀ j, poly.degreeOf j ≤ deg) {stop : Fin (n + 1)}

/-- The computed projection sent from an interval claim with one more round. -/
def intervalHonestMessage (k : ℕ) (st : IntervalClaim R n stop (k + 1)) :
    Impl.Representation.Message R deg :=
  projectedMessage D st.index st.statement.challenges poly hpoly

/-- The computed successor stores the actual challenge and the computed message's value at it. -/
def intervalHonestNext (k : ℕ) (st : IntervalClaim R n stop (k + 1)) (r : R) :
    IntervalClaim R n stop k :=
  st.next (Impl.Representation.evaluate R deg (intervalHonestMessage D poly hpoly k st) r) r

/-- Send computed projections and store each actual challenge in the continuation. -/
def intervalHonestProver {m : Type → Type} [Monad m] (k : ℕ) (st : IntervalClaim R n stop k) :
    Focal oracleSig m (Interpreted.protocol R (Impl.Representation.Message R deg)
      (Impl.Representation.evaluate R deg) k) (fun _ => RoundStatement R n stop) :=
  foldRounds (intervalHonestMessage D poly hpoly) (intervalHonestNext D poly hpoly)
    IntervalClaim.finish k st

/-- Interpreting the whole computed honest prover gives exactly the honest polynomial fold. -/
theorem interpret_intervalHonestProver {m : Type → Type} [Monad m] [LawfulMonad m]
    (k : ℕ) (st : IntervalClaim R n stop k) :
    Interpreted.transportProver (evaluateN := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
      (Impl.Representation.toMessage R deg) k (intervalHonestProver D poly hpoly k st) =
      intervalProver D (toPolynomial poly hpoly) (m := m) k st := by
  refine (Interpreted.transportFocal_foldRounds _ id _ _ _ k st).trans ?_
  refine foldRounds_map (intervalMessage D (toPolynomial poly hpoly))
    (intervalNext D (toPolynomial poly hpoly)) IntervalClaim.finish _ _ _ (fun _ st => st)
    (fun k st => projectedMessage_toMessage D _ _ poly hpoly) (fun k st r => ?_)
    (fun _ => rfl) k st
  exact congrArg (fun v => st.next v r) (projectedMessage_evaluate D _ _ poly hpoly r)

variable [DecidableEq R]

/-- Actual execution of computed honest messages equals mathematical honest execution. -/
theorem execute_honest_eq_native {m : Type → Type} [Monad m] [LawfulMonad m]
    {Data : Type} (next : m R) (k : ℕ) (st : IntervalClaim R n stop k) (data : Data) :
    Interpreted.execute next (intervalCheck D) IntervalClaim.finish k st data
      (intervalHonestProver D poly hpoly k st) =
    Interpreted.execute next (intervalCheck D) IntervalClaim.finish k st data
      (intervalProver D (toPolynomial poly hpoly) k st) := by
  have h := Interpreted.execute_transport
    (evaluateN := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
    next (intervalCheck D) IntervalClaim.finish
    (Impl.Representation.toMessage R deg)
    (fun q r => (Impl.Representation.evaluate_eq R deg q r).symm)
    k st data
    (intervalHonestProver D poly hpoly k st)
  rw [interpret_intervalHonestProver] at h
  exact h.symm

/-- Every honest computed interval is a map of explicit draws, with true endpoint output. -/
theorem execute_honest {m : Type → Type} [Monad m] [LawfulMonad m] {Data : Type}
    (next : m R) (k : ℕ) (st : IntervalClaim R n stop k) (data : Data)
    (h : indexedRelation D st.round st.statement (toPolynomial poly hpoly)) :
    Interpreted.execute next (intervalCheck D) IntervalClaim.finish k st data
      (intervalHonestProver D poly hpoly k st) =
      (fun chals =>
        let t := (foldState (intervalNext D (toPolynomial poly hpoly)) k st chals).finish
        (t, some (t, data))) <$>
        drawChallenges k
          (Interpreted.draw (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) next k) := by
  rw [execute_honest_eq_native]
  unfold Interpreted.execute intervalProver
  rw [run_foldRounds]
  simp only [Functor.map_map]
  congr 1
  funext chals
  change (_, (intervalVerdict D k st _).map _) = _
  rw [(intervalVerdict_honest D (toPolynomial poly hpoly) k st h chals).1]
  rfl

/-- Every supported computed honest interval accepts a true retained-original claim. -/
theorem execute_supportCompleteness {Data : Type} (next : ProbComp R) (k : ℕ)
    (st : IntervalClaim R n stop k) (data : Data)
    (h : indexedRelation D st.round st.statement (toPolynomial poly hpoly)) :
    ∀ result ∈ support (Interpreted.execute next (intervalCheck D) IntervalClaim.finish k st data
      (intervalHonestProver D poly hpoly k st)),
      ∃ t, result.2 = some (t, data) ∧ indexedRelation D stop t (toPolynomial poly hpoly) := by
  rw [execute_honest D poly hpoly next k st data h, MonadAttach.support_map]
  rintro result ⟨chals, _, rfl⟩
  exact ⟨_, rfl, (intervalVerdict_honest D (toPolynomial poly hpoly) k st h chals).2⟩

/-- Computed honest intervals have perfect completeness for every explicit challenge program. -/
theorem execute_perfectCompleteness {Data : Type} (next : ProbComp R) (k : ℕ)
    (st : IntervalClaim R n stop k) (data : Data)
    (h : indexedRelation D st.round st.statement (toPolynomial poly hpoly)) :
    Pr{let result ← (Interpreted.execute next (intervalCheck D) IntervalClaim.finish k st data
      (intervalHonestProver D poly hpoly k st))}[
        ∃ t, result.2 = some (t, data) ∧
          indexedRelation D stop t (toPolynomial poly hpoly)] = 1 := by
  exact prEvent_eq_one_of_forall_mem_support _ _
    (execute_supportCompleteness D poly hpoly next k st data h)

end Sumcheck.Core.Computable
