/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.QuerySoundness
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Rejection semantics of the FRI query verifier

The short-circuiting executable verifier accepts exactly when all its local checks pass.
-/

namespace Fri.Spec.QueryRound

open Domain OracleSpec OracleComp ProtocolSpec Finset
open scoped ProbabilityTheory

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) {l : ℕ}

/-- Resolving a lifted query against the retained commitment history. -/
theorem simulate_lift (o : ∀ j, FinalOracleStatement s ω j)
    (msgs : (pSpec (ω := ω) l).Messages) {A : Type}
    (c : OracleComp [FinalOracleStatement s ω]ₒ A) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) o msgs)
      (liftM c : OracleComp ((emptySpec.{0, 0}) + ([FinalOracleStatement s ω]ₒ +
        [(pSpec (ω := ω) l).Message]ₒ)) A) =
      pure (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o) c).run := by
  exact simulateQ_addLift_add_liftM_left (m := OracleComp (emptySpec.{0, 0}))
    (QueryImpl.id (emptySpec.{0, 0}))
    (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
    (OracleInterface.simOracle0 (pSpec (ω := ω) l).Message msgs) c

private theorem eval_guard_yield {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec Id) (c : OracleComp spec Bool) :
    (simulateQ impl ((do
        guard (← c)
        pure (ForInStep.yield PUnit.unit) :
        OptionT (OracleComp spec) (ForInStep PUnit)).run)).run =
      if (simulateQ impl c).run = true
        then some (ForInStep.yield PUnit.unit) else none := by
  simp [OptionT.run_bind, Option.elimM, simulateQ_bind, simulateQ_map, guard]
  split_ifs <;> rfl

private theorem eval_guard_loop {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec Id) {m : ℕ} (c : Fin m → OracleComp spec Bool) :
    (simulateQ impl ((forIn (List.finRange m) PUnit.unit (fun i _ ↦ do
      guard (← c i)
      pure (ForInStep.yield PUnit.unit)) :
      OptionT (OracleComp spec) PUnit).run)).run =
      if ∀ i, (simulateQ impl (c i)).run = true then some PUnit.unit else none := by
  have h := simulateQ_optionT_finRange_forIn impl PUnit.unit
    (fun i _ ↦ do
      guard (← c i)
      pure (ForInStep.yield PUnit.unit))
    (fun i ↦ (simulateQ impl (c i)).run = true)
    (fun i ↦ eval_guard_yield impl (c i))
  exact h

/-- Exact acceptance semantics of the query verifier's computational core. -/
theorem eval_verifyQueries (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (xs : Fin l → (ω.subdomain 0).toFinset) :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (verifyQueries s hs l α xs).run).run =
      if ∀ j i, (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (checkRound s hs (finalPolynomial s o) (α i) i (xs j))).run = true
      then some α else none := by
  classical
  let impl := OracleInterface.simOracle0 (FinalOracleStatement s ω) o
  let checks (j : Fin l) (i : Fin (k + 1)) :=
    checkRound s hs (finalPolynomial s o) (α i) i (xs j)
  let inner (j : Fin l) : OptionT (OracleComp [FinalOracleStatement s ω]ₒ) PUnit :=
    forIn (List.finRange (k + 1)) PUnit.unit fun i _ ↦ do
      guard (← checks j i)
      pure (ForInStep.yield PUnit.unit)
  let cond (j : Fin l) := ∀ i, (simulateQ impl (checks j i)).run = true
  have hi (j : Fin l) : simulateQ impl (inner j).run =
      pure (if cond j then some PUnit.unit else none) := eval_guard_loop impl (checks j)
  let body (j : Fin l) (_ : PUnit) :
      OptionT (OracleComp [FinalOracleStatement s ω]ₒ) (ForInStep PUnit) := do
    inner j
    pure (ForInStep.yield PUnit.unit)
  have hb (j : Fin l) : simulateQ impl (body j PUnit.unit).run =
      pure (if cond j then some (ForInStep.yield PUnit.unit) else none) := by
    simp only [body, OptionT.run_bind, Option.elimM, simulateQ_bind]
    rw [hi]
    split_ifs <;> rfl
  have ho := simulateQ_optionT_finRange_forIn impl PUnit.unit body cond hb
  simp only [verifyQueries, guard_eq, bind_pure_comp, OptionT.run_bind, Option.elimM,
    OptionT.run_monadLift, monadLift_self, OptionT.run_map, bind_map_left, Option.elim_some,
    simulateQ_bind, eval_getConst, simulateQ_map, Id.run_bind, Id.run_map]
  change Option.map (fun _ ↦ α)
    (simulateQ impl ((forIn (List.finRange l) PUnit.unit body :
      OptionT (OracleComp [FinalOracleStatement s ω]ₒ) PUnit).run)).run = _
  rw [ho]
  split_ifs <;> rfl

/-- The oracle-verifier wrapper has exactly the same acceptance semantics as its core. -/
theorem simulate_queryVerifier (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (ch : (pSpec (ω := ω) l).Challenges) (msgs : (pSpec (ω := ω) l).Messages) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) o msgs)
      ((queryVerifier s hs l).verify α ch).run =
      pure (if ∀ j i,
        (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
          (checkRound s hs (finalPolynomial s o) (α i) i (ch ⟨0, by simp⟩ j))).run = true
      then some α else none) := by
  change simulateQ _ (liftM (verifyQueries s hs l α (ch ⟨0, by simp⟩)).run) = _
  rw [simulate_lift, eval_verifyQueries]

/-- Query verification preserves the retained oracle history. -/
@[simp]
theorem queryVerifier_materializeOutput (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j)
    (ch : (pSpec (ω := ω) l).Challenges) (msgs : (pSpec (ω := ω) l).Messages) :
    (queryVerifier s hs l).materializeOutput ch o msgs = o := by
  rfl

/-- The query reduction's ordinary verifier rejects exactly the failed local checks. -/
theorem queryVerifier_toVerifier_verify (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (tr : (pSpec (ω := ω) l).FullTranscript) :
    ((queryVerifier s hs l).toVerifier.verify (α, o) tr).run =
      pure (if ∀ j i,
        (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
          (checkRound s hs (finalPolynomial s o) (α i) i (tr.challenges ⟨0, by simp⟩ j))).run = true
      then some (α, o) else none) := by
  change Option.map _ <$> simulateQ _ ((queryVerifier s hs l).verify α tr.challenges).run = _
  rw [simulate_queryVerifier, map_pure]
  split_ifs <;> rfl

/-- The actual query core, sampled on its subtype-valued domain, satisfies the updated
query bound. No assumption is made about honesty of the intermediate words. -/
theorem verifyQueries_soundness (d : ℕ+) (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (θ δ : ℝ) (hsafe : SafeHistory s d o α θ)
    (hdegree : (finalPolynomial s o).natDegree < d.val)
    (hdist : ∀ u ∈ ReedSolomon.code ω (2 ^ (∑ j, (s j).val) * d.val),
      δ ≤ (Code.relHammingDist (initialWord s o) u : ℝ)) :
    Pr_{let xs ←$ᵖ (Fin l → (ω.subdomain 0).toFinset)}[
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (verifyQueries s hs l α xs).run).run ≠ none] ≤
      ENNReal.ofReal (1 - min θ δ) ^ l := by
  classical
  let e : (Fin l → Fin (2 ^ n)) ≃ (Fin l → (ω.subdomain 0).toFinset) :=
    Equiv.arrowCongr (Equiv.refl _) (ω.subdomain 0).equivToFinset
  rw [← ProbabilityTheory.Pr_uniform_equiv e]
  have he (zs : Fin l → Fin (2 ^ n)) (j : Fin l) : e zs j = initialQuery (zs j) := by
    apply Subtype.ext
    simp [e, initialQuery, CosetFftDomain.subdomain_zero_eq_self]
  have hpoint (zs : Fin l → Fin (2 ^ n)) :
      ((simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (verifyQueries s hs l α (e zs)).run).run ≠ none) ↔
      ∀ j, zs j ∈ acceptingQueries s hs o α := by
    rw [eval_verifyQueries]
    simp [acceptingQueries, he]
    rfl
  simpa only [hpoint] using queryChecks_soundness s d hs o α θ δ l hsafe hdegree hdist

end Fri.Spec.QueryRound
