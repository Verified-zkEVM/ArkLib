/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vuk Dolijanovic, Claude(Anthropic)
-/

import ArkLib.ProofSystem.GKR.SingleRound
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.ProofSystem.Component.CheckClaim

/-!
# GKR in the oracle model

`SingleRound.lean` and `General.lean` build GKR as a plain `Reduction`. That model has no notion
of what a verifier can afford to compute: the verifier receives its whole input as data, so
nothing stops it from holding the next layer's multilinear extension — and in the plain
development it does, because the statement lens materializes `roundPolyFinOracle … V` and
`Materialized.gkrLayer` instantiates `V := layerMLE`. Completeness still holds, but the object
proved complete is a verifier parameterized by the answer it is meant to check, and soundness for
it would be a theorem about the wrong protocol.

This file restates the whole protocol as an `OracleReduction`, where the verifier receives only
the challenges and reaches everything else through queries. Concretely:

* the layer polynomials become an oracle statement family, `LayerFam`;
* the statement lens becomes an `OracleStatement.ExecutableLens` whose `projStmt` carries no `V`,
  with sum-check's oracle answered query-by-query by `simulateRoundPoly` — two queries to the
  layer oracle plus locally computed public wiring, exactly the two evaluations the wiring
  identity calls for;
* the combine step becomes an `OracleVerifier` querying its message oracle at `0`, `1` and `r`;
* `Combine.oracleVerifier_eq_verifier` shows materializing it recovers the plain verifier, which
  is what lets the existing completeness proof carry over unchanged.

`V` survives only in the statements of the relations, which describe what a true claim is; it is
never executed and the verifier never touches it.

Relations carry a conjunct pinning the oracle family to the circuit's layer MLEs. This is forced
rather than cosmetic: layer `l` outputs a claim about layer `l+1`, layer `l+1` needs that claim as
a wiring sum over layer `l+2`, and `layerMLE_eval_eq_wiring_sum'` — the only bridge between them —
holds only for the honest encodings. It assumes nothing away, since the circuit and the input
determine every layer.

The first section extends `Sumcheck.Spec` with the oracle-level facts the lift needs. Nothing
there is GKR-specific and it would sit equally well in `SumcheckAux.lean`.

Nothing in this file contains a `sorry`. `Combine.oracleVerifier_eq_verifier`,
`Combine.oracleReduction_perfectCompleteness`, `oLayerRelOut_eq_oRelIn` and `oChain_castSucc` are
axiom-clean. The composed `oracleGkr_perfectCompleteness` inherits `sorryAx` through ArkLib's own
unproved `Reduction.liftContext_completeness`, `append_completeness` and
`seqCompose_completeness` — the same three the plain development already relied on.

## References

* [Thaler2022] Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, §4.6.
* [GKR15] Goldwasser, Kalai and Rothblum, *Delegating computation*.
-/

namespace Sumcheck.Spec
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [DecidableEq R] [SampleableType R]

/-- The single round's oracle reduction materializes to the plain single round. -/
theorem singleRound_oracleReduction_toReduction (i : Fin n) :
    (SingleRound.oracleReduction R n deg D oSpec i).toReduction
      = SingleRound.reduction R n deg D oSpec i := by
  rw [SingleRound.oracleReduction, SingleRound.reduction]
  erw [OracleReduction.liftContext_toReduction_comm]
  rw [SingleRound.Simple.oracleReduction_eq_reduction]
  rfl

/-- **The full sum-check oracle reduction materializes to the plain one.** -/
theorem oracleReduction_toReduction :
    (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec := by
  rw [oracleReduction, reduction,
    OracleReduction.seqCompose_toReduction]
  congr 1
  funext i
  exact singleRound_oracleReduction_toReduction R deg D n oSpec i


/-- **The oracle-reduction analogue of `reduction_run_preserves_oracle`.**
Free, because the oracle reduction materializes to the plain one. -/
theorem oracleReduction_run_preserves_oracle
    (stmt : StatementRound R n 0 × (∀ j, OracleStatement R n deg j)) (wit : Unit) :
    ∀ x ∈ _root_.support ((oracleReduction R deg D n oSpec).toReduction.run stmt wit),
      x.1.2.1.2 = stmt.2 := by
  rw [oracleReduction_toReduction]
  exact reduction_run_preserves_oracle R deg D n oSpec stmt wit


variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Perfect completeness for the full sum-check protocol as an ORACLE reduction.**
`Spec/General.lean` states this only for the plain reduction; this is the oracle analogue,
composed the same way. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) :=
  OracleReduction.seqCompose_perfectCompleteness
    (rel := relationRound R n deg D)
    (R := SingleRound.oracleReduction R n deg D oSpec)
    (h := fun i => SingleRound.oracleReduction_perfectCompleteness i)


end Sumcheck.Spec

namespace GKR.Oracle
open MvPolynomial Polynomial OracleSpec OracleComp ProtocolSpec GKR GKR.Combine

variable (R : Type) [CommRing R] [Nontrivial R] [DecidableEq R] (n : ℕ)

@[reducible]
def LayerFam (k : ℕ) : Fin (n + 1) → Type := fun _ => R⦃≤ 1⦄[X Fin k]

variable {ι : Type} (oSpec : OracleSpec ι) {k : ℕ} (c : Circuit k n) (l : Fin n)

/-- `Combine.pSpec`'s single message is a degree-≤k univariate, accessed by evaluation.
Built by hand because `pSpec` is built by hand (cf. `instSampleableChallenge`). -/
instance instOracleInterfaceMessage : ∀ i, OracleInterface ((pSpec R k).Message i)
  | ⟨0, _⟩ => (inferInstance : OracleInterface (R⦃≤ (k : WithBot ℕ)⦄[X]))
  | ⟨1, h⟩ => absurd h (by rw [show (pSpec R k).dir 1 = Direction.V_to_P from rfl]; simp)

/-- Query the prover's message polynomial `q` at one point.  Mirrors sum-check's
`queryRoundInput`, so that a single `@[simp]` lemma resolves it. -/
def queryMsg (pt : R) :
    OracleComp (oSpec + ([LayerFam R n k]ₒ + [(pSpec R k).Message]ₒ)) R :=
  liftM (OracleSpec.query
    (show [(pSpec R k).Message]ₒ.Domain from ⟨⟨0, rfl⟩, pt⟩))

omit [Nontrivial R] [DecidableEq R] in
@[simp] theorem simulateQ_queryMsg (oStmt : ∀ i, LayerFam R n k i)
    (messages : (pSpec R k).Messages) (pt : R) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages) (queryMsg R n oSpec pt)
      = pure ((messages ⟨0, rfl⟩).val.eval pt) := by
  simp only [queryMsg, OracleInterface.simOracle2
]
  rfl

/-- **The combine step's oracle verifier.** It queries the prover's message oracle `q` at
`0`, `1` and `r`, checks the wiring identity, and outputs the layer-`l+1` claim.
It never touches the layer MLE. -/
noncomputable def oracleVerifier :
    OracleVerifier oSpec (StmtIn R n k l.castSucc) (LayerFam R n k)
      (GKRStatement R n k l.succ) (LayerFam R n k) (pSpec R k) where
  verify := fun s challenges => do
    let r : R := challenges ⟨1, rfl⟩
    let q0 : R ← OptionT.lift (queryMsg R n oSpec 0)
    let q1 : R ← OptionT.lift (queryMsg R n oSpec 1)
    let qr : R ← OptionT.lift (queryMsg R n oSpec r)
    guard (s.claim.value =
      MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges)))
          (addPredMLE R c l) * (q0 + q1)
      + MvPolynomial.eval (Sum.elim s.claim.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges)))
          (mulPredMLE R c l) * (q0 * q1))
    pure ⟨line (leftHalf R s.challenges) (rightHalf R s.challenges) r, qr⟩
  outputOracle := .inl {
    embed := ⟨Sum.inl, fun a b h => by simpa using h⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }


omit [Nontrivial R] [DecidableEq R] in
/-- Degree bound extracted from the oracle. -/
theorem layerFam_degreeOf (oStmt : ∀ j, LayerFam R n k j) (j : Fin (n + 1)) (i : Fin k) :
    degreeOf i (oStmt j).val ≤ 1 := by
  have := (oStmt j).2
  rw [mem_restrictDegree_iff_degreeOf_le] at this
  exact this i

/-- **The combine step's oracle prover.** Same protocol as before; the only change is that
`V` is read out of the oracle family rather than passed in as a parameter. -/
noncomputable def oracleProver (V : MvPolynomial (Fin k) R) (hV : ∀ i, degreeOf i V ≤ 1) :
    OracleProver oSpec (StmtIn R n k l.castSucc) (LayerFam R n k) Unit
      (GKRStatement R n k l.succ) (LayerFam R n k) Unit (pSpec R k) where
  PrvState
  | 0 => StmtIn R n k l.castSucc × (∀ j, LayerFam R n k j)
  | 1 => StmtIn R n k l.castSucc × (∀ j, LayerFam R n k j)
  | 2 => (StmtIn R n k l.castSucc × (∀ j, LayerFam R n k j)) × R
  input := Prod.fst
  sendMessage
  | ⟨0, _⟩ => fun s =>
      pure (sentPoly R V hV s.1.challenges, s)
  | ⟨1, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun s => pure fun r => (s, r)
  output := fun ⟨⟨s, oStmt⟩, r⟩ =>
    pure ((⟨line (leftHalf R s.challenges) (rightHalf R s.challenges) r,
      (sentPoly R V hV s.challenges).val.eval r⟩, oStmt), ())


/-- **The combine step as an oracle reduction.** -/
noncomputable def oracleReduction (V : MvPolynomial (Fin k) R)
    (hV : ∀ i, degreeOf i V ≤ 1) :
    OracleReduction oSpec (StmtIn R n k l.castSucc) (LayerFam R n k) Unit
      (GKRStatement R n k l.succ) (LayerFam R n k) Unit (pSpec R k) where
  prover := oracleProver R n oSpec l V hV
  verifier := oracleVerifier R n oSpec c l


/-! ## Relations over the oracle family -/

/-- Input relation: the layer-`l` claim, with `V` read from the oracle family. -/
def oRelIn (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R) :
    Set ((StmtIn R n k l.castSucc × (∀ j, LayerFam R n k j)) × Unit) :=
  { ⟨⟨⟨⟨point, target⟩, ch⟩, oStmt⟩, _⟩ |
    oStmt = W ∧
    target =
      MvPolynomial.eval (Sum.elim point (Sum.elim (leftHalf R ch) (rightHalf R ch)))
          (addPredMLE R c l)
        * (MvPolynomial.eval (leftHalf R ch) V
          + MvPolynomial.eval (rightHalf R ch) V)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (leftHalf R ch) (rightHalf R ch)))
          (mulPredMLE R c l)
        * (MvPolynomial.eval (leftHalf R ch) V
          * MvPolynomial.eval (rightHalf R ch) V) }

/-- Output relation: the surviving single claim about layer `l+1`. -/
def oRelOut (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R) :
    Set ((GKRStatement R n k l.succ × (∀ j, LayerFam R n k j)) × Unit) :=
  { ⟨⟨⟨point', value'⟩, oStmt⟩, _⟩ |
    oStmt = W ∧ MvPolynomial.eval point' V = value' }

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
variable [SampleableType R]

omit [SampleableType R] in
omit [Nontrivial R] in
/-- **The materialized oracle verifier equals the original, with the oracle carried.**
Mirrors `Sumcheck.Spec.SingleRound.Simple.oracleVerifier_eq_verifier`. -/
theorem oracleVerifier_eq_verifier :
    (oracleVerifier R n oSpec c l).toVerifier =
      { verify := fun sO transcript =>
          (fun stmtOut => (stmtOut, sO.2)) <$>
            (GKR.Combine.verifier R n c l oSpec).verify sO.1 transcript } := by
  ext ⟨s, oStmt⟩ transcript
  simp only [OracleVerifier.toVerifier, oracleVerifier, GKR.Combine.verifier,
    OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    simulateQ_queryMsg,
    OptionT.run_bind, OptionT.run_pure, OptionT.run_mk, OptionT.run_lift,
    pure_bind, bind_pure_comp, map_pure,
    FullTranscript.challenges, FullTranscript.messages,
    Option.elimM, simulateQ_bind, simulateQ_map, simulateQ_pure,
    Option.elim_some, guard, apply_ite]
  split_ifs <;> rfl

omit [Nontrivial R] [SampleableType R] in
/-- The materialized oracle reduction: original prover, original verifier + passenger. -/
theorem oracleReduction_toReduction_eq (V : MvPolynomial (Fin k) R)
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (oracleReduction R n oSpec c l V hV).toReduction =
      { prover := oracleProver R n oSpec l V hV,
        verifier := { verify := fun sO transcript =>
          (fun stmtOut => (stmtOut, sO.2)) <$>
            (GKR.Combine.verifier R n c l oSpec).verify sO.1 transcript } } := by
  unfold OracleReduction.toReduction
  congr 1
  exact oracleVerifier_eq_verifier R n oSpec c l

omit [Nontrivial R] in
/-- **Perfect completeness of the ported combine step.** -/
theorem oracleReduction_perfectCompleteness (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R)
    (hV : ∀ i, degreeOf i V ≤ 1) :
    (oracleReduction R n oSpec c l V hV).perfectCompleteness init impl
      (oRelIn R n c l W V) (oRelOut R n l W V) := by
  simp only [OracleReduction.perfectCompleteness]
  rw [oracleReduction_toReduction_eq]
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    ENNReal.coe_zero, tsub_zero]
  intro ⟨s, oStmt⟩ () hValid
  have optionT_lift_eq_map {M : Type → Type} [Monad M] [LawfulMonad M]
      {α : Type} (mx : M α) :
      (OptionT.lift mx : OptionT M α) = OptionT.mk (some <$> mx) := by
    apply OptionT.ext
    change (monadLift mx : OptionT M α).run = some <$> mx
    rw [OptionT.run_monadLift, monadLift_self]
  simp only [oRelIn, Set.mem_ofPred_eq] at hValid
  obtain ⟨hW, hValid⟩ := hValid
  have hCheck := combine_check_passes R c l s.1.point V s.1.value
    (leftHalf R s.challenges) (rightHalf R s.challenges) hValid
  have hCheck' : s.1.value =
      MvPolynomial.eval (Sum.elim s.1.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges))) (addPredMLE R c l)
        * ((sentPoly R V hV s.challenges).val.eval 0
          + (sentPoly R V hV s.challenges).val.eval 1)
      + MvPolynomial.eval (Sum.elim s.1.point
          (Sum.elim (leftHalf R s.challenges) (rightHalf R s.challenges))) (mulPredMLE R c l)
        * ((sentPoly R V hV s.challenges).val.eval 0
          * (sentPoly R V hV s.challenges).val.eval 1) := hCheck
  simp only [Reduction.run, Prover.run, Verifier.run, oracleProver, GKR.Combine.verifier,
    Prover.runToRound, Prover.processRound, Fin.induction_two, pSpec,
    bind_pure_comp, Functor.map_map]
  split <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind]
  split <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
    OracleComp.liftComp_pure, pure_bind, map_pure,
    bind_pure_comp, Transcript.concat,
    guard, optionT_lift_eq_map, OptionT.mk, OptionT.run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  -- ## the execution never fails
  · rw [OptionT.probFailure_eq]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [OptionT.run, support_bind, Set.mem_iUnion, not_exists]
    intro st _ hmem
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hmem
    obtain ⟨⟨_, s'⟩, hmem, rfl⟩ := hmem
    erw [simulateQ_bind] at hmem
    erw [StateT.run_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hmem
    erw [simulateQ_map] at hx
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    erw [simulateQ_bind] at hs
    erw [StateT.run_bind] at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨⟨y, s'''⟩, hy, hs⟩ := hs
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    dsimp only [] at hs
    rcases val2 with _ | out
    · simp only [Option.getM] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      erw [simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨valp, sp⟩, hvalp, heqp⟩ := hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heqp
      -- v4.33: the `pure`-tail no longer needs peeling separately; one map-peel suffices
      erw [simulateQ_map] at hchal
      erw [StateT.run_map] at hchal
      simp only [support_map, Set.mem_image] at hchal
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        OracleQuery.input_query,
        Fin.snoc] at hval2
      norm_num at hval2
      simp only [sentPoly] at hval2
      erw [if_pos hCheck] at hval2
      simp only [map_pure] at hval2
      erw [simulateQ_pure] at hval2
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hval2
      exact absurd (congr_arg Prod.fst hval2) (by simp)
    · simp only [Option.getM] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      exact absurd (congr_arg Prod.fst hs) (by simp)
  -- ## every possible output is correct
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run, support_bind, Set.mem_iUnion] at hx
    obtain ⟨st, _, hx⟩ := hx
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
    obtain ⟨⟨_, s'⟩, hx, rfl⟩ := hx
    erw [simulateQ_bind] at hx
    erw [StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨x_opt, s''⟩, hx_first, hx_rest⟩ := hx
    erw [simulateQ_map] at hx_first
    rw [StateT.run_map] at hx_first
    simp only [support_map, Set.mem_image] at hx_first
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx_first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    erw [simulateQ_bind] at hx_rest
    erw [StateT.run_bind] at hx_rest
    rw [mem_support_bind_iff] at hx_rest
    obtain ⟨⟨y, s'''⟩, hy, hx_rest⟩ := hx_rest
    erw [simulateQ_map] at hy
    erw [simulateQ_map] at hy
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val2, s₁⟩, hval2, heq2⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq2
    dsimp only [] at hx_rest
    rcases val2 with _ | out
    · simp only [Option.getM] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      exact absurd (congr_arg Prod.fst hx_rest) (by simp)
    · simp only [Option.getM] at hx_rest
      erw [simulateQ_pure] at hx_rest
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx_rest
      obtain ⟨rfl, rfl⟩ := hx_rest
      erw [simulateQ_bind] at hval
      erw [StateT.run_bind] at hval
      rw [mem_support_bind_iff] at hval
      obtain ⟨⟨chal_res, s₂⟩, hchal, hval⟩ := hval
      erw [simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨valp, sp⟩, hvalp, heqp⟩ := hval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heqp
      -- v4.33: the `pure`-tail no longer needs peeling separately; one map-peel suffices
      erw [simulateQ_map] at hchal
      erw [StateT.run_map] at hchal
      simp only [support_map, Set.mem_image] at hchal
      obtain ⟨⟨inner_val, s_inner⟩, hinner, heq_c⟩ := hchal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq_c
      simp only [QueryImpl.addLift_def,
        QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hvalp
      obtain ⟨rfl, rfl⟩ := hvalp
      simp only [QueryImpl.addLift_def,
        OracleQuery.input_query,
        Fin.snoc] at hval2
      norm_num at hval2
      simp only [sentPoly] at hval2
      erw [if_pos hCheck] at hval2
      simp only [map_pure] at hval2
      erw [simulateQ_pure] at hval2
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hval2
      obtain ⟨hout, -⟩ := hval2
      subst hout
      refine ⟨⟨hW, ?_⟩, ?_⟩
      -- the surviving claim is true
      · exact (eval_restrictToLine _ _ V _).symm
      -- prover and verifier agree: the prover recomputes the polynomial it sent
      · rfl


/-- Query the layer-`l+1` MLE oracle at one point. -/
def queryLayer {k : ℕ} (l : Fin n) (point : Fin k → R) :
    OracleComp [LayerFam R n k]ₒ R :=
  liftM <| OracleSpec.query (show [LayerFam R n k]ₒ.Domain from ⟨l.succ, point⟩)

/-- **The GKR analogue of `simulateProjectedRoundPolynomial`.**
Answers a query "what is `roundPolyFin` at `(x,y)`?" using two queries to the
layer-`l+1` oracle plus locally-computed public wiring. Nothing is materialized. -/
noncomputable def simulateRoundPoly {k : ℕ} (c : Circuit k n) (l : Fin n) (point : Fin k → R) :
    QueryImpl [Sumcheck.Spec.OracleStatement R (k + k) 2]ₒ
      (OracleComp [LayerFam R n k]ₒ) := fun q => by
  rcases q with ⟨u, xy⟩
  rcases u with ⟨⟩
  exact do
    let x := xy ∘ (finSumFinEquiv ∘ Sum.inl)
    let y := xy ∘ (finSumFinEquiv ∘ Sum.inr)
    let vx ← queryLayer R n l x
    let vy ← queryLayer R n l y
    pure (MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (addPredMLE R c l) * (vx + vy)
        + MvPolynomial.eval (Sum.elim point (Sum.elim x y)) (mulPredMLE R c l) * (vx * vy))


/-- Materialized view: the polynomial the inner sum-check is nominally summing. -/
noncomputable def materializeRoundPoly {k : ℕ} (c : Circuit k n) (l : Fin n)
    (point : Fin k → R) (oStmt : ∀ i, LayerFam R n k i) :
    ∀ i, Sumcheck.Spec.OracleStatement R (k + k) 2 i :=
  fun _ => roundPolyFinOracle R c l point (oStmt l.succ).val
    (fun j => by
      have := (oStmt l.succ).2
      rw [mem_restrictDegree_iff_degreeOf_le] at this
      exact this j)

omit [DecidableEq R] [SampleableType R] in
/-- **The agreement obligation.** Answering a query by two layer-oracle lookups plus
public wiring gives the same value as evaluating the materialized polynomial. -/
theorem simulateRoundPoly_eq {k : ℕ} (c : Circuit k n) (l : Fin n) (point : Fin k → R)
    (oStmt : ∀ i, LayerFam R n k i) (q : [Sumcheck.Spec.OracleStatement R (k + k) 2]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle0 (LayerFam R n k) oStmt)
        (simulateRoundPoly R n c l point q) =
      pure ((inferInstance : OracleInterface
              (Sumcheck.Spec.OracleStatement R (k + k) 2 q.1)).answer
        (materializeRoundPoly R n c l point oStmt q.1) q.2) := by
  rcases q with ⟨u, xy⟩
  rcases u with ⟨⟩
  simp only [simulateRoundPoly, queryLayer, materializeRoundPoly, roundPolyFinOracle,
    simulateQ_bind]
  exact (output_relation_to_wiring_identity R c l point
    (MvPolynomial.eval xy (roundPolyFin R c l point (oStmt l.succ).val)) xy
    (oStmt l.succ).val rfl).symm


/-! ## The full oracle-statement lens for one GKR layer -/

/-- **The executable oracle-statement lens for a GKR layer.**
Outer: a GKR claim `(point, value)` plus the layer-`l+1` MLE as an oracle.
Inner: sum-check's `(target, challenges)` plus its round-polynomial oracle — supplied
*virtually*, never built. -/
noncomputable def layerExecLens {k : ℕ} (c : Circuit k n) (l : Fin n) :
    OracleStatement.ExecutableLens
      (GKRStatement R n k l.castSucc)                       -- OuterStmtIn
      (GKR.Combine.StmtIn R n k l.castSucc)                 -- OuterStmtOut
      (Sumcheck.Spec.StatementRound R (k + k) 0)            -- InnerStmtIn
      (Sumcheck.Spec.StatementRound R (k + k) (Fin.last (k + k)))  -- InnerStmtOut
      (LayerFam R n k) (LayerFam R n k)                   -- outer oracles: the layer MLE
      (Sumcheck.Spec.OracleStatement R (k + k) 2)           -- inner in
      (Sumcheck.Spec.OracleStatement R (k + k) 2)           -- inner out
    where
  projStmt := fun gkrStmt => ⟨gkrStmt.value, Fin.elim0⟩
  materializeInput := fun gkrStmt oStmt =>
    materializeRoundPoly R n c l gkrStmt.point oStmt
  simulateInput := fun gkrStmt => simulateRoundPoly R n c l gkrStmt.point
  simulateInput_eq := fun gkrStmt oStmt q =>
    simulateRoundPoly_eq R n c l gkrStmt.point oStmt q
  liftStmt := fun gkrStmt innerOut => ⟨⟨gkrStmt.point, innerOut.target⟩, innerOut.challenges⟩
  -- the layer MLE passes straight through, exactly as sum-check does with its own oracle
  materializeOutput := fun outerOStmt _ => outerOStmt
  simulateOutput := fun q => liftM <| OracleSpec.query
    (show ([LayerFam R n k]ₒ + [Sumcheck.Spec.OracleStatement R (k + k) 2]ₒ).Domain
      from Sum.inl q)
  simulateOutput_eq := by
    intro outerOStmt innerOStmt q
    rcases q with ⟨u, point⟩
    rcases u with ⟨⟩
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
    rfl


/-- **The full context lens for a GKR layer.** Statement half as above; witness half is
trivial because every witness in this development is `Unit`. -/
noncomputable def layerCtxLens {k : ℕ} (c : Circuit k n) (l : Fin n) :
    OracleContext.ExecutableLens
      (GKRStatement R n k l.castSucc)
      (GKR.Combine.StmtIn R n k l.castSucc)
      (Sumcheck.Spec.StatementRound R (k + k) 0)
      (Sumcheck.Spec.StatementRound R (k + k) (Fin.last (k + k)))
      (LayerFam R n k) (LayerFam R n k)
      (Sumcheck.Spec.OracleStatement R (k + k) 2)
      (Sumcheck.Spec.OracleStatement R (k + k) 2)
      Unit Unit Unit Unit where
  stmt := layerExecLens R n c l
  wit  := Witness.Lens.trivial


/-- The outer output oracle is literally the outer input oracle (the layer MLE passes
through), so it is an *embedding*, not a simulation. -/
def layerOutputEmbedding {k : ℕ} :
    OracleOutputEmbedding (LayerFam R n k)
      (Sumcheck.Spec.pSpec R 2 (k + k)).Message (LayerFam R n k) where
  embed := ⟨Sum.inl, fun a b h => by simpa using h⟩
  hEq := fun _ => rfl
  outputInterface_heq := fun _ => HEq.rfl

/-- The `LiftContextOutput` witnessing that lifting preserves the layer oracle. -/
def layerLiftOutput {k : ℕ} (c : Circuit k n) (l : Fin n) :
    OracleVerifier.LiftContextOutput (layerExecLens R n c l)
      (Sumcheck.Spec.oracleVerifier R 2 (D R) (k + k) []ₒ) where
  outputOracle := .inl (layerOutputEmbedding R n)
  materialize_eq := by intro outerStmt challenges outerOStmt messages; rfl

/-- **The lifted layer**: sum-check, run as an *oracle* reduction, speaking GKR's language.
The verifier never holds the layer MLE — only query access it does not even use. -/
noncomputable def liftedInnerOracle {k : ℕ} (c : Circuit k n) (l : Fin n) :=
  (Sumcheck.Spec.oracleReduction R 2 (D R) (k + k) []ₒ).liftContext
    (layerCtxLens R n c l) (layerLiftOutput R n c l)


/-! ## Completeness by transport (sum-check's own recipe), not by query grinding -/

variable {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl ([]ₒ : OracleSpec PEmpty) (StateT σ ProbComp)}

/-- Outer relation: the GKR layer-`l` claim, `V` read from the oracle. -/
def oLayerRelIn {k : ℕ} (c : Circuit k n) (l : Fin n) (W : ∀ j, LayerFam R n k j) :
    Set ((GKRStatement R n k l.castSucc × (∀ i, LayerFam R n k i)) × Unit) :=
  { ⟨⟨⟨point, value⟩, oStmt⟩, _⟩ |
    oStmt = W ∧
    value = ∑ x : Index k, ∑ y : Index k,
      (MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
          (addPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) (oStmt l.succ).val
          + MvPolynomial.eval (bridge R y) (oStmt l.succ).val)
      + MvPolynomial.eval (Sum.elim point (Sum.elim (bridge R x) (bridge R y)))
          (mulPredMLE R c l)
        * (MvPolynomial.eval (bridge R x) (oStmt l.succ).val
          * MvPolynomial.eval (bridge R y) (oStmt l.succ).val)) }

/-- Outer output relation: sum-check's final claim, in GKR's language. -/
def oLayerRelOut {k : ℕ} (c : Circuit k n) (l : Fin n) (W : ∀ j, LayerFam R n k j) :
    Set ((GKR.Combine.StmtIn R n k l.castSucc × (∀ i, LayerFam R n k i)) × Unit) :=
  { ⟨⟨⟨⟨point, target⟩, ch⟩, oStmt⟩, _⟩ |
    oStmt = W ∧
    MvPolynomial.eval ch (roundPolyFin R c l point (oStmt l.succ).val) = target }


omit [Nontrivial R] [DecidableEq R] [SampleableType R] in
/-- **The junction.** The relation the lifted sum-check lands in is exactly the relation the
combine step consumes: `roundPolyFin` evaluated at the challenge point *is* the wiring
expression. This is what lets the two halves append. -/
theorem oLayerRelOut_eq_oRelIn {k : ℕ} (c : Circuit k n) (l : Fin n)
    (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R) (hVW : (W l.succ).val = V) :
    oLayerRelOut R n c l W = oRelIn R n c l W V := by
  subst hVW
  ext ⟨⟨⟨⟨point, target⟩, ch⟩, oStmt⟩, ⟨⟩⟩
  simp only [oLayerRelOut, oRelIn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, output_relation_to_wiring_identity R c l point target ch _ h⟩
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [h]
    exact output_relation_to_wiring_identity R c l point _ ch (oStmt l.succ).val rfl

/-- **Completeness of the lifted layer, by transport.** The two obligations are exactly the
ones sum-check itself discharges: the inner protocol's completeness, and a lens condition. -/
theorem liftedInnerOracle_perfectCompleteness {k : ℕ} (c : Circuit k n) (l : Fin n)
    (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R) (hVW : (W l.succ).val = V)
    [lensComplete : (layerCtxLens R n c l).toLens.toContext.IsComplete
      (oLayerRelIn R n c l W) (Sumcheck.Spec.relationRound R (k + k) 2 (D R) 0)
      (oLayerRelOut R n c l W)
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k)))
      ((Sumcheck.Spec.oracleReduction R 2 (D R) (k + k) []ₒ).toReduction.compatContext
        (layerCtxLens R n c l).toLens.toContext)] :
    (liftedInnerOracle R n c l).perfectCompleteness init impl
      (oLayerRelIn R n c l W) (oRelIn R n c l W V) := by
  rw [← oLayerRelOut_eq_oRelIn R n c l W V hVW]
  exact OracleReduction.liftContext_perfectCompleteness
    (Sumcheck.Spec.oracleReduction_perfectCompleteness R 2 (D R) (k + k) []ₒ)


/-- **The lens condition.** Its two fields should be the bridge theorems, with `V` read from
the oracle rather than passed as a parameter. -/
instance layerLensComplete {k : ℕ} (c : Circuit k n) (l : Fin n) (W : ∀ j, LayerFam R n k j) :
    (layerCtxLens R n c l).toLens.toContext.IsComplete
      (oLayerRelIn R n c l W) (Sumcheck.Spec.relationRound R (k + k) 2 (D R) 0)
      (oLayerRelOut R n c l W)
      (Sumcheck.Spec.relationRound R (k + k) 2 (D R) (Fin.last (k + k)))
      ((Sumcheck.Spec.oracleReduction R 2 (D R) (k + k) []ₒ).toReduction.compatContext
        (layerCtxLens R n c l).toLens.toContext) where
  proj_complete := by
    rintro ⟨⟨point, value⟩, oStmt⟩ ⟨⟩ ⟨hW, h⟩
    have hdeg : ∀ j, degreeOf j (oStmt l.succ).val ≤ 1 := fun j => by
      have := (oStmt l.succ).2
      rw [mem_restrictDegree_iff_degreeOf_le] at this
      exact this j
    exact relationRound_to_relationRound R c l point value (oStmt l.succ).val hdeg h
  lift_complete := by
    rintro ⟨⟨point, value⟩, oStmt⟩ ⟨⟩ ⟨⟨target, challenges⟩, oOut⟩ ⟨⟩ hCompat ⟨hW, -⟩ hInner
    refine ⟨hW, ?_⟩
    have hdeg : ∀ j, degreeOf j (oStmt l.succ).val ≤ 1 := fun j => by
      have := (oStmt l.succ).2
      rw [mem_restrictDegree_iff_degreeOf_le] at this
      exact this j
    -- the oracle we get back is the one we supplied
    have hOracle : oOut = fun _ => roundPolyFinOracle R c l point (oStmt l.succ).val hdeg := by
      obtain ⟨x, hx, hxeq⟩ := hCompat
      have := Sumcheck.Spec.oracleReduction_run_preserves_oracle R 2 (D R) (k + k) []ₒ
        ⟨⟨value, Fin.elim0⟩,
          fun _ => roundPolyFinOracle R c l point (oStmt l.succ).val hdeg⟩ () x hx
      simp only [Function.comp_apply] at hxeq
      rw [hxeq] at this
      dsimp only at this
      exact this
    subst hOracle
    change MvPolynomial.eval challenges (roundPolyFin R c l point (oStmt l.succ).val) = target
    exact sumcheck_output_mem_to_eval R target challenges
      (fun _ => roundPolyFinOracle R c l point (oStmt l.succ).val hdeg) hInner


/-! ## One full GKR layer, as an oracle reduction

The inner sum-check (lifted into GKR's vocabulary) followed by the combine step — the oracle
analogue of `Combine.layerReduction`. Both halves are `OracleReduction`s over the same layer
family, so they append directly.
-/

instance instOracleInterfaceAppend {k : ℕ} :
    ∀ i, OracleInterface
      ((Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ GKR.Combine.pSpec R k).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend

/-- **One full layer of GKR in the oracle model.** The verifier holds no layer polynomial;
it has query access to the layer family and, in the combine step, to the prover's message. -/
noncomputable def oracleLayer {k : ℕ} (c : Circuit k n) (l : Fin n)
    (V : MvPolynomial (Fin k) R) (hV : ∀ i, degreeOf i V ≤ 1) :
    OracleReduction []ₒ
      (GKRStatement R n k l.castSucc) (LayerFam R n k) Unit
      (GKRStatement R n k l.succ) (LayerFam R n k) Unit
      (Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ GKR.Combine.pSpec R k) :=
  (liftedInnerOracle R n c l).append (oracleReduction R n []ₒ c l V hV)

/-- **Completeness of one full layer.** A true layer-`l` claim goes in; a true layer-`l+1`
claim comes out. -/
theorem oracleLayer_perfectCompleteness {k : ℕ} (c : Circuit k n) (l : Fin n)
    (W : ∀ j, LayerFam R n k j) (V : MvPolynomial (Fin k) R)
    (hVW : (W l.succ).val = V) (hV : ∀ i, degreeOf i V ≤ 1) :
    (oracleLayer R n c l V hV).perfectCompleteness init impl
      (oLayerRelIn R n c l W) (oRelOut R n l W V) :=
  OracleReduction.append_perfectCompleteness _ _
    (liftedInnerOracle_perfectCompleteness R n c l W V hVW)
    (oracleReduction_perfectCompleteness R n []ₒ c l W V hV)

end GKR.Oracle

/-! ## GKR composed across all layers, in the oracle model

`IsDomain R` replaces `Nontrivial R` from here on — the chaining fact
`layerMLE_eval_eq_wiring_sum'` needs it, and it implies the weaker assumption, so the section
above keeps the more general hypothesis and this one does not carry both.
-/

namespace GKR.Oracle
open MvPolynomial Polynomial OracleSpec OracleComp ProtocolSpec GKR GKR.Combine

variable (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] [SampleableType R] (n : ℕ)
variable {k : ℕ} (c : Circuit k n) (input : Index k → R)
variable {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl ([]ₒ : OracleSpec PEmpty) (StateT σ ProbComp)}

/-- The honest layer family: layer `j`'s multilinear extension, as an oracle. -/
noncomputable def honestLayers : ∀ j, LayerFam R n k j :=
  fun j => ⟨layerMLE R c input j, by
    rw [mem_restrictDegree_iff_degreeOf_le]; exact fun i => MLE_degreeOf _ i⟩

/-- The chain relation, in the oracle model: the oracles are the honest layer MLEs, and
`value` is what layer `i`'s MLE gives at `point`. -/
def oChain (i : Fin (n + 1)) : Set ((GKRStatement R n k i × (∀ j, LayerFam R n k j)) × Unit) :=
  { ⟨⟨⟨point, value⟩, oStmt⟩, _⟩ |
    oStmt = honestLayers R n c input ∧
    MvPolynomial.eval point (layerMLE R c input i) = value }

omit [DecidableEq R] [SampleableType R] in
/-- At layer `l` the chain relation *is* the lifted sum-check's input relation. -/
theorem oChain_castSucc (l : Fin n) :
    oChain R n c input l.castSucc = oLayerRelIn R n c l (honestLayers R n c input) := by
  ext ⟨⟨⟨point, value⟩, oStmt⟩, ⟨⟩⟩
  simp only [oChain, oLayerRelIn, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, layerMLE_eval_eq_wiring_sum' R c input l point⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by rw [h]; exact layerMLE_eval_eq_wiring_sum' R c input l point⟩

omit [IsDomain R] [DecidableEq R] [SampleableType R] in
/-- At layer `l+1` the chain relation *is* the combine step's output relation. -/
theorem oChain_succ (l : Fin n) :
    oChain R n c input l.succ
      = oRelOut R n l (honestLayers R n c input) (layerMLE R c input l.succ) := rfl

/-- Each layer takes the chain relation one step down. -/
theorem oracleLayer_chain (l : Fin n) :
    (oracleLayer R n c l (layerMLE R c input l.succ) (fun i => MLE_degreeOf _ i)
      ).perfectCompleteness init impl (oChain R n c input l.castSucc)
        (oChain R n c input l.succ) := by
  rw [oChain_castSucc, oChain_succ]
  exact oracleLayer_perfectCompleteness R n c l (honestLayers R n c input) _ rfl _

/-- **GKR, composed across all `n` layers, in the oracle model.** -/
noncomputable def oracleGkr :
    OracleReduction []ₒ
      (GKRStatement R n k 0) (LayerFam R n k) Unit
      (GKRStatement R n k (Fin.last n)) (LayerFam R n k) Unit
      (ProtocolSpec.seqCompose
        (fun _ : Fin n => Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ GKR.Combine.pSpec R k)) :=
  OracleReduction.seqCompose
    (Stmt := fun i => GKRStatement R n k i)
    (OStmt := fun _ => LayerFam R n k)
    (Wit := fun _ => Unit)
    (fun l => oracleLayer R n c l (layerMLE R c input l.succ) (fun i => MLE_degreeOf _ i))

/-- **Perfect completeness of GKR in the oracle model.** The capstone, with a verifier that
never holds a layer polynomial. -/
theorem oracleGkr_perfectCompleteness :
    (oracleGkr R n c input).perfectCompleteness init impl
      (oChain R n c input 0) (oChain R n c input (Fin.last n)) :=
  OracleReduction.seqCompose_perfectCompleteness
    (rel := oChain R n c input)
    (R := fun l => oracleLayer R n c l (layerMLE R c input l.succ) (fun i => MLE_degreeOf _ i))
    (h := fun l => oracleLayer_chain R n c input l)

/-! ## The terminal check

`oracleGkr` reduces a layer-`0` claim to a layer-`n` claim, but a claim is not a decision. The
last layer is the input, which the verifier holds, so it can finish the protocol itself: evaluate
the input's multilinear extension at the surviving point and compare.

Note what the predicate mentions. Only `input` — never `c`, never `layerMLE`, never
`honestLayers`. That is what makes it a check the verifier can actually run; evaluating the input
extension costs `O(2 ^ k)`, which is GKR's accepted verifier cost, whereas evaluating a layer
extension would cost a full circuit evaluation. The oracle family stays pinned by the relation,
not by the guard, which is why the composition goes through `completeness_relOut_mono` rather
than by strengthening the predicate.
-/

/-- the multilinear extension of the input, which the verifier computes itself -/
noncomputable def inputMLE : MvPolynomial (Fin k) R :=
  MLE (fun w => input (finTwoEquiv ∘ w))

omit [IsDomain R] [DecidableEq R] [SampleableType R] in
/-- the last layer's extension is the input's extension -/
theorem layerMLE_last : layerMLE R c input (Fin.last n) = inputMLE R input := by
  unfold layerMLE inputMLE
  rw [layerValues_last]

/-- what the verifier checks at the end, using only the input it already holds -/
def terminalPred : (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j)) → Prop :=
  fun x => MvPolynomial.eval x.1.point (inputMLE R input) = x.1.value

omit [IsDomain R] [DecidableEq R] [SampleableType R] in
theorem oChain_last_subset :
    oChain R n c input (Fin.last n)
      ⊆ CheckClaim.relIn (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j))
          (terminalPred R n input) := by
  rintro ⟨⟨⟨point, value⟩, oStmt⟩, ⟨⟩⟩ h
  simp only [oChain, Set.mem_ofPred_eq] at h
  rw [layerMLE_last] at h
  simp only [CheckClaim.relIn, terminalPred, Set.mem_ofPred_eq]
  exact h.2

/-- inference does not fire on `++ₚ`; supply it by name, as sum-check and Hachi do -/
instance instSampleableWithCheck :
    ∀ i, SampleableType
      (((ProtocolSpec.seqCompose
          fun _ : Fin n => Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ GKR.Combine.pSpec R k)
        ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

open scoped Classical in
/-- the terminal step: the verifier checks the last claim against the input it holds -/
noncomputable def terminalCheck :
    Reduction ([]ₒ : OracleSpec PEmpty)
      (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j)) Unit
      (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j)) Unit !p[] :=
  CheckClaim.reduction []ₒ _ (terminalPred R n input)

open scoped Classical in
/-- GKR's layers followed by the verifier's own check of the surviving claim -/
noncomputable def gkrWithTerminalCheck :=
  (oracleGkr R n c input).toReduction.append (terminalCheck R n input)

open scoped Classical in
/-- **A true layer-`0` claim leads to the verifier accepting.** The output relation is trivial;
all the content is in the run succeeding, since the terminal `guard` would fail otherwise. -/
theorem gkrWithTerminalCheck_perfectCompleteness [Nonempty σ] :
    (gkrWithTerminalCheck R n c input).perfectCompleteness init impl
      (oChain R n c input 0)
      (CheckClaim.relOut (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j))) := by
  refine Reduction.append_perfectCompleteness _ _ ?_
    (CheckClaim.reduction_completeness []ₒ _ (terminalPred R n input))
  have h : Reduction.completeness init impl (oChain R n c input 0)
      (oChain R n c input (Fin.last n)) (oracleGkr R n c input).toReduction 0 :=
    oracleGkr_perfectCompleteness R n c input
  exact Reduction.completeness_relOut_mono init impl (oChain_last_subset R n c input) h

/-! ## The claimed-output opening

`gkrWithTerminalCheck` reaches a decision, but it still begins by *assuming* a layer-`0` claim.
The real protocol begins with the prover claiming `evalCircuit c input = y`; the verifier samples
a point and evaluates the claimed output's own extension there, and that is the layer-`0` claim.

Completeness here needs no randomness argument: if the circuit really outputs `y` then layer `0`'s
extension *is* `y`'s extension (`layerMLE_zero`), so the claim holds at every point, not merely a
random one. Randomness is what soundness needs, and that is not claimed here.
-/

omit [IsDomain R] [DecidableEq R] [SampleableType R] in
/-- layer 0's extension is the extension of the circuit's output -/
theorem layerMLE_zero : layerMLE R c input 0 = inputMLE R (evalCircuit c input) := by
  unfold layerMLE inputMLE
  rw [layerValues_zero]

/-- one `V_to_P` round carrying the evaluation point -/
def openPSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin k → R]⟩

instance instSampleableOpen : ∀ i, SampleableType ((openPSpec R (k := k)).Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType (Fin k → R))

instance instVerifierOnlyOpen : VerifierOnly (openPSpec R (k := k)) where
  verifier_first' := by simp [openPSpec]

@[reducible] def OpenStmtIn (k : ℕ) := (Index k → R) × (∀ j, LayerFam R n k j)
@[reducible] def OpenStmtOut (k : ℕ) := GKRStatement R n k 0 × (∀ j, LayerFam R n k j)

noncomputable def openProver :
    Prover ([]ₒ : OracleSpec PEmpty) (OpenStmtIn R n k) Unit (OpenStmtOut R n k) Unit
      (openPSpec R (k := k)) where
  PrvState
  | 0 => OpenStmtIn R n k
  | 1 => OpenStmtIn R n k × (Fin k → R)
  input := Prod.fst
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st => pure fun z => (st, z)
  output := fun ⟨⟨y, oStmt⟩, z⟩ =>
    pure ((⟨z, MvPolynomial.eval z (inputMLE R y)⟩, oStmt), ())

noncomputable def openVerifier :
    Verifier ([]ₒ : OracleSpec PEmpty) (OpenStmtIn R n k) (OpenStmtOut R n k)
      (openPSpec R (k := k)) where
  verify := fun s transcript =>
    pure (⟨transcript 0, MvPolynomial.eval (transcript 0) (inputMLE R s.1)⟩, s.2)

noncomputable def openReduction :
    Reduction ([]ₒ : OracleSpec PEmpty) (OpenStmtIn R n k) Unit (OpenStmtOut R n k) Unit
      (openPSpec R (k := k)) where
  prover := openProver R n
  verifier := openVerifier R n

/-- the claim the protocol starts from: the circuit really outputs `y` -/
def openRelIn : Set (OpenStmtIn R n k × Unit) :=
  { ⟨⟨y, oStmt⟩, _⟩ | oStmt = honestLayers R n c input ∧ evalCircuit c input = y }

omit [IsDomain R] [DecidableEq R] in
theorem openReduction_perfectCompleteness :
    (openReduction R n (k := k)).perfectCompleteness init impl
      (openRelIn R n c input) (oChain R n c input 0) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨y, oStmt⟩ ⟨⟩ h x hx
  obtain ⟨hW, hy⟩ := h
  subst hy
  simp only [openReduction, Reduction.run, Prover.run_of_verifier_first,
    openProver, openVerifier, Verifier.run] at hx
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_pure_comp, map_pure,
    OptionT.run_pure, OptionT.run_bind,
    Option.getM, Option.elimM,
    OptionT.run_map,
    support_bind,
    Set.mem_iUnion, exists_prop] at hx
  obtain ⟨i, hi, hx⟩ := hx
  simp only [OptionT.run_monadLift, _root_.monadLift_self, support_map, Set.mem_image] at hi
  obtain ⟨w, ⟨z, -, rfl⟩, rfl⟩ := hi
  simp only [Option.elim_some
] at hx
  subst hx
  refine ⟨_, rfl, ?_, rfl⟩
  simp only [oChain, Set.mem_ofPred_eq]
  exact ⟨hW, by rw [layerMLE_zero]⟩


/-- inference does not fire on `++ₚ`; supply it by name -/
instance instSampleableFull :
    ∀ i, SampleableType
      ((openPSpec R (k := k) ++ₚ
        ((ProtocolSpec.seqCompose
            fun _ : Fin n => Sumcheck.Spec.pSpec R 2 (k + k) ++ₚ GKR.Combine.pSpec R k)
          ++ₚ !p[])).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

open scoped Classical in
/-- **GKR end to end**: from a claim about the circuit's output to the verifier's decision. -/
noncomputable def gkrFull :=
  (openReduction R n (k := k)).append (gkrWithTerminalCheck R n c input)

open scoped Classical in
/-- **The capstone.** If the circuit really outputs `y`, the honest run ends with the verifier
accepting. The output relation is trivial; the content is that the run succeeds, which it does
only because the terminal `guard` passes. -/
theorem gkrFull_perfectCompleteness [Nonempty σ] :
    (gkrFull R n c input).perfectCompleteness init impl
      (openRelIn R n c input)
      (CheckClaim.relOut (GKRStatement R n k (Fin.last n) × (∀ j, LayerFam R n k j))) :=
  Reduction.append_perfectCompleteness _ _
    (openReduction_perfectCompleteness R n c input)
    (gkrWithTerminalCheck_perfectCompleteness R n c input)

end GKR.Oracle
