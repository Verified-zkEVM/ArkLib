/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ArkLib.OracleReduction.Execution
public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Core `vcgen` on the executions of interactive oracle reductions

VCVio's `prvcgen` proves a statement about the outcomes of one oracle computation, such as
`∀ x ∈ support oa, p x`, `Pr{…}[p] = 1` or an upper bound, by stating it as a core triple of the
matching reading of `OracleComp` and running Lean's `vcgen` through the program.

This module is the entry point to that program logic for ArkLib's completeness and security
proofs. Its public import of `VCVio.ProgramLogic.Tactics.PrVCGen` makes `prvcgen` and VCVio's rules
for every reading available to the modules that import it. It also adds two facts about the
executions defined in `ArkLib.OracleReduction.Execution`:

* `ProtocolSpec.Necessary.Spec.getChallenge`: the necessary-reading rule for a verifier challenge,
  which may be any value;
* `Reduction.run_run_eq`: `Reduction.run` as one oracle computation, the prover's run followed by
  the verifier's, with the `OptionT` layer of the reduction reduced to an `Option.map`.

A completeness proof states the honest prover's run in closed form (the protocol's own
round-unfolding lemma), rewrites the verifier, and lets `vcgen` walk the rest:

```
simp only [Reduction.run_run_eq, reduction, verifier, Verifier.run, OptionT.run_pure]
rw [prover_run_eq K computeW stmt wit hdir]
prvcgen
exact ⟨_, rfl⟩
```

leaving one verification condition per possible challenge. Two variations cover the other honest
executions:

* a prover with no closed form (many challenge rounds) enters through its support,
  `prvcgen [Necessary.Spec.ofSupport (Prover.run _ _ _)]`, and its support lemma closes the
  verification condition;
* a verifier that can reject, `if c then pure a else failure`, is split by `vcgen` once
  `apply_ite OptionT.run`, `OptionT.run_pure` and `OptionT.run_failure` bring the `if` to the top of
  the lifted run, leaving one verification condition per branch.

A soundness bound, `Pr{…}[p] ≤ ε` or `Pr{…}[p] = 0`, is read in the upper-bound reading. The
opaque parts of the game, such as the sampled initial state or a simulated prover run, enter
through `OracleComp.Upper.Spec.ofSupport`, as in `Verifier.id_soundness`. A bound that averages
over a uniform challenge passes the averaging rule `OracleComp.Upper.Spec.uniformSample_avg`, as in
`ProtocolSpec.prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec Std.WP

namespace ProtocolSpec

/-- The necessary-reading rule for a verifier challenge: `pSpec.getChallenge i` may return any
value, so its precondition is that `post` holds at every challenge. -/
@[spec]
theorem Necessary.Spec.getChallenge {n : ℕ} (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdx)
    (post : pSpec.Challenge i → Prop) {epost : EStack⟨⟩} :
    Triple (pSpec.getChallenge i) (∀ c, post c) post epost :=
  ⟨fun h c _ => h c⟩

end ProtocolSpec

section Execution

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-- The run of a reduction as one oracle computation: the prover's run, then the verifier's run
lifted to the reduction's oracles, with a rejection of the verifier as `none`. -/
theorem Reduction.run_run_eq (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.run stmt wit).run = (do
      let pr ← reduction.prover.run stmt wit
      let o ← (liftM (reduction.verifier.run stmt pr.1).run :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) _)
      return o.map (pr, ·)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM]
  rw [show ((liftM (Prover.run stmt wit reduction.prover) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _)).run
      = Prover.run stmt wit reduction.prover >>= fun a => pure (some a) from rfl]
  simp only [bind_assoc, pure_bind, Option.elim_some]
  refine bind_congr fun pr => ?_
  simp only [← monadLift_liftM_OptionT, OptionT.run_monadLift, monadLift_self, bind_map_left,
    Option.elim_some]
  refine bind_congr fun o => ?_
  cases o <;> simp [Option.getM]

end Execution
