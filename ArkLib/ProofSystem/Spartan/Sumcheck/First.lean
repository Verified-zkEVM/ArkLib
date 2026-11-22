/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Sumcheck.VirtualOracle
public import ArkLib.ProofSystem.Spartan.Algebra.Computable
public import ArkLib.ProofSystem.Sumcheck.Impl.OracleProver
public import ArkLib.ProofSystem.Spartan.ZeroCheck.Relation
public import ArkLib.ProofSystem.Spartan.Evaluation.Reduction
public import ArkLib.ProofSystem.Sumcheck.Spec.General
public import ArkLib.ProofSystem.Sumcheck.Domain

/-!
# Spartan's first virtual sumcheck

The sumcheck input polynomial is derived from the retained matrix and witness tables. The
executable input lens answers its evaluation queries without adding a prover oracle.
-/

@[expose] public section

namespace Spartan.FirstSumcheck

open OracleComp OracleInterface MvPolynomial Realization

variable {R : Type} [CommRing R] [DecidableEq R] (pp : PublicParams)

/-- The retained zero-check challenge and original public input. -/
abbrev Statement := (Fin pp.ℓ_m → R) × R1CS.Statement R pp.toSizeR1CS

/-- The degree-three virtual polynomial, constructed from the retained tables. -/
def polynomial (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 () :=
  Sumcheck.Impl.Computable.toOracleStatement
    (Computable.firstVirtual (fun i => o (.inl i)) (R1CS.𝕫 s.2 (o (.inr 0))) s.1)
    (Computable.firstVirtual_degreeOf_le _ _ _)

/-- The computational materialization agrees with the semantic first virtual polynomial. -/
theorem polynomial_val (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    (polynomial pp s o).val = Algebra.firstVirtual (fun i => o (.inl i))
      (R1CS.𝕫 s.2 (o (.inr 0))) s.1 := Computable.firstVirtual_toPolynomial _ _ _

/-- The first sumcheck projects the degree-three virtual polynomial and retains every oracle. -/
def lens : OracleStatement.ExecutableLens
    (Statement (R := R) pp) (Evaluation.Statement (R := R) pp)
    (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
    (Sumcheck.Spec.StatementRound R pp.ℓ_m (.last pp.ℓ_m))
    (OracleStatement (R := R) pp) (OracleStatement (R := R) pp)
    (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3)
    (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) where
  projStmt _ := ⟨0, Fin.elim0⟩
  materializeInput s o _ := polynomial pp s o
  simulateInput s q := VirtualOracle.first pp s.2 s.1 q.2
  simulateInput_eq s o q := by
    change simulateQ (simOracle0 (OracleStatement (R := R) pp) o)
      (VirtualOracle.first pp s.2 s.1 q.2) = eval q.2 (polynomial pp s o).val
    rw [polynomial_val]
    exact VirtualOracle.firstVirtual_realizes pp s.2 s.1 q.2 o
  liftStmt s out := ⟨s.2, s.1, out.challenges, out.target⟩
  materializeOutput o _ := o
  simulateOutput q := liftM (OracleSpec.query q)
  simulateOutput_eq _ _ _ := rfl

section

variable [Nontrivial R] [SampleableType R]
    {ι : Type} (oSpec : OracleSpec ι)

/-- The virtual input is internal; the output family consists of the retained original oracles. -/
def output : OracleVerifier.LiftContextOutput (lens (R := R) pp)
    (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec) where
  outputOracle := .inl ⟨Function.Embedding.inl, fun _ => rfl, fun _ => HEq.rfl⟩
  materialize_eq _ _ _ _ := rfl

/-- Route the virtual input to its finite-table program and forward every other query. -/
def verifierQueryImpl (s : Statement (R := R) pp) : QueryImpl
    (oSpec + ([Sumcheck.Spec.OracleStatement R pp.ℓ_m 3]ₒ +
      [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ))
    (OracleComp (oSpec + ([OracleStatement (R := R) pp]ₒ +
      [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ))) :=
  QueryImpl.addLift (QueryImpl.id' oSpec)
    (QueryImpl.addLift
      ((fun q => VirtualOracle.first pp s.2 s.1 q.2) :
        QueryImpl [Sumcheck.Spec.OracleStatement R pp.ℓ_m 3]ₒ
          (OracleComp [OracleStatement (R := R) pp]ₒ))
      (QueryImpl.id' [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ) :
      QueryImpl ([Sumcheck.Spec.OracleStatement R pp.ℓ_m 3]ₒ +
        [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ)
        (OracleComp ([OracleStatement (R := R) pp]ₒ +
          [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ)))

/-- The first sumcheck oracle verifier, with its virtual input and retained context. -/
def oracleVerifier : OracleVerifier oSpec (Statement (R := R) pp)
    (OracleStatement (R := R) pp) (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) where
  verify s challenges := OptionT.mk <|
    Option.map (fun out : Sumcheck.Spec.StatementRound R pp.ℓ_m (.last pp.ℓ_m) =>
      (⟨s.2, s.1, out.challenges, out.target⟩ : Evaluation.Statement pp)) <$>
      simulateQ (verifierQueryImpl pp oSpec s)
        ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).verify
          ⟨0, Fin.elim0⟩ challenges).run
  outputOracle := .inl ⟨Function.Embedding.inl, fun _ => rfl, fun _ => HEq.rfl⟩

/-- The implemented verifier is exactly the executable virtual-polynomial context lift. -/
theorem oracleVerifier_eq_liftContext : oracleVerifier (R := R) pp oSpec =
    (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
      (lens pp) (output pp oSpec) := rfl

/-- The lifted verifier retains every sumcheck rejection guard. The semantic guarded form
mentions mathematical polynomial evaluations. -/
noncomputable def guardedForm : (oracleVerifier (R := R) pp oSpec).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofEq
    (congrArg OracleVerifier.toVerifier (oracleVerifier_eq_liftContext pp oSpec)).symm <|
  OracleVerifier.liftContextGuardedForm (lens pp)
    (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec) (output pp oSpec)
    (Sumcheck.Spec.oracleVerifierGuardedForm R 3 (boolEmbedding R) pp.ℓ_m oSpec)

omit [SampleableType R] in
/-- The projected initial sumcheck relation is exactly the zero-check claim. -/
theorem inputRelation_iff (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    (((lens pp).projStmt s, (lens pp).materializeInput s o), ()) ∈
        Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) 0 ↔
      ZeroCheck.outputRelation pp s o := by
  rw [ZeroCheck.outputRelation_iff_firstVirtual]
  change (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ (pp.ℓ_m - 0),
    (polynomial pp s o).val.eval (Fin.append Fin.elim0 x ∘ Fin.cast (by simp))) = 0 ↔ _
  simp only [Nat.sub_zero, Fin.elim0_append, Function.comp_assoc]
  change (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ pp.ℓ_m,
    (polynomial pp s o).val.eval x) = 0 ↔ _
  rw [show (Finset.univ.map (boolEmbedding R)) ^ᶠ pp.ℓ_m =
    (boolDomain R pp.ℓ_m).cube from rfl, sum_cube_boolDomain, polynomial_val]
  rfl

omit [SampleableType R] in
/-- The final sumcheck relation is polynomial evaluation at its returned challenge vector. -/
theorem outputRelation_iff (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (out : Sumcheck.Spec.StatementRound R pp.ℓ_m (.last pp.ℓ_m)) :
    ((out, (lens pp).materializeInput s o), ()) ∈
        Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (.last pp.ℓ_m) ↔
      Evaluation.inputRelation pp ((lens pp).liftStmt s out) o := by
  simp only [Sumcheck.Spec.relationRound, Set.mem_ofPred_eq, Fin.val_last]
  rw [Fin.sum_piFinset_cast _ (Nat.sub_self pp.ℓ_m)]
  have hdom : (Finset.univ.map (boolEmbedding R)) ^ᶠ 0 = {Fin.elim0} := by
    ext x
    simp only [Fintype.piFinset, Finset.mem_map, Finset.mem_singleton]
    simp only [Finset.mem_pi, Finset.univ_eq_empty, Finset.notMem_empty, Finset.mem_map,
      Finset.mem_univ, true_and, Fin.exists_fin_two, Fin.isValue, boolEmbedding_zero,
      boolEmbedding_one, IsEmpty.forall_iff, Fin.exists_fin_zero_pi]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  rw [hdom, Finset.sum_singleton, Fin.append_right_nil _ _ (Nat.sub_self pp.ℓ_m)]
  change (polynomial pp s o).val.eval out.challenges = out.target ↔ _
  rw [polynomial_val]
  rfl

/-- The prover projects the computed virtual polynomial and retains the original tables. -/
def proverContextLens : Context.Lens
    (Statement (R := R) pp × (∀ i, OracleStatement (R := R) pp i))
    (Evaluation.Statement (R := R) pp × (∀ i, OracleStatement (R := R) pp i))
    (Sumcheck.Spec.StatementRound R pp.ℓ_m 0 ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    (Sumcheck.Spec.StatementRound R pp.ℓ_m (.last pp.ℓ_m) ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := {
    toFunA := fun ⟨s, o⟩ => (⟨0, Fin.elim0⟩, fun _ => polynomial pp s o)
    toFunB := fun ⟨s, o⟩ ⟨out, _⟩ => (⟨s.2, s.1, out.challenges, out.target⟩, o) }

/-- The honest prover computes every round message and output target. -/
def oracleProver : OracleProver oSpec (Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) :=
  Prover.liftContext (proverContextLens pp)
    (Sumcheck.Impl.Computable.generalOracleProver R 3 oSpec pp.ℓ_m (boolEmbedding R))

/-- The executable honest prover agrees with the lifted sumcheck specification. -/
theorem oracleProver_eq : oracleProver (R := R) pp oSpec =
    Prover.liftContext (proverContextLens pp)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).prover := by
  rw [oracleProver, Sumcheck.Impl.Computable.generalOracleProver_eq]

/-- The honest prover's final output uses no ambient oracle queries. -/
instance oracleProver_outputIsPure :
    Prover.OutputIsPure.{0} (oracleProver (R := R) pp oSpec) := by
  apply (congrArg Prover.OutputIsPure (oracleProver_eq (R := R) pp oSpec)).mpr
  have h :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).prover.OutputIsPure := by
    apply Prover.OutputIsPure.seqCompose
    intro i
    change Prover.OutputIsPure
      (Sumcheck.Spec.SingleRound.reduction R pp.ℓ_m 3 (boolEmbedding R) oSpec i).prover
    infer_instance
  let := h
  infer_instance

/-- The first virtual sumcheck reduction with its executable honest prover. -/
def oracleReduction : OracleReduction oSpec (Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) where
  prover := oracleProver pp oSpec
  verifier := oracleVerifier pp oSpec

/-- The first sumcheck verifier queries only its round messages, never its virtual input. -/
theorem sumcheck_verifier_no_inputPolynomial_queries (s : Statement (R := R) pp)
    (challenges : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenges) :
    AllQueriesSatisfy ((oracleVerifier pp oSpec).verify s challenges).run
      (fun q => ∃ j, q = Sum.inr (Sum.inr j)) := by
  change AllQueriesSatisfy (Option.map _ <$> simulateQ
    (OracleVerifier.liftContextQueryImpl (lens pp) s)
    ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).verify
      ((lens pp).projStmt s) challenges).run) _
  rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def]
  apply (Sumcheck.Spec.sumcheck_verifier_no_inputPolynomial_queries
    R 3 (boolEmbedding R) pp.ℓ_m oSpec _ challenges).simulateQ
  rintro q ⟨j, rfl⟩
  simp only [OracleVerifier.liftContextQueryImpl, QueryImpl.addLift_def,
    QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
  change AllQueriesSatisfy (liftM (OracleSpec.query
    (spec := oSpec + ([OracleStatement (R := R) pp]ₒ +
      [(Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Message]ₒ)) (Sum.inr (Sum.inr j)))) _
  exact (allQueriesSatisfy_query_iff _ _).2 ⟨j, rfl⟩

/-- The input relation is the zero-check output. -/
abbrev relIn := ZeroCheck.relOut (R := R) pp

/-- The output relation is the first virtual polynomial's terminal evaluation. -/
abbrev relOut := SendEvaluations.relIn (R := R) pp

/-- Materializing the implemented reduction gives the ordinary context lift of sumcheck. -/
theorem oracleReduction_toReduction : (oracleReduction (R := R) pp oSpec).toReduction =
    (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.liftContext
      (proverContextLens pp) := by
  apply Reduction.ext
  · exact oracleProver_eq pp oSpec
  · change (oracleVerifier pp oSpec).toVerifier = _
    rw [oracleVerifier_eq_liftContext, OracleVerifier.liftContext_toVerifier_comm]
    change Verifier.liftContext (lens pp).toLens _ = Verifier.liftContext _
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
    rw [Sumcheck.Spec.oracleReduction_verifier_eq_oracleVerifier]
    rfl

/-- Honest execution retains the materialized virtual polynomial when lifting completeness. -/
instance contextLens_complete : (proverContextLens (R := R) pp).IsComplete
    (relIn pp) (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) 0)
    (relOut pp) (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (.last pp.ℓ_m))
    ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
      (proverContextLens pp)) where
  proj_complete := by
    rintro ⟨s, o⟩ ⟨⟩ h
    exact (inputRelation_iff pp s o).mpr h
  lift_complete := by
    rintro ⟨s, o⟩ ⟨⟩ ⟨out, innerO⟩ ⟨⟩ hc _ ho
    obtain ⟨z, hz, heq⟩ := hc
    have hp : z.1 ∈ support
        ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).prover.run
          ((lens pp).toLens.proj (s, o)) ()) := by
      change some z ∈ MonadAttach.support
        (((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.run
          ((lens pp).toLens.proj (s, o)) ()).run) at hz
      rw [Reduction.run_run_eq_bind] at hz
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨pr, hpr, value, _, hvalue⟩ := hz
      cases value with
      | none => simp at hvalue
      | some value =>
        simp only [Option.map_some, Option.some.injEq] at hvalue
        subst z
        exact hpr
    rw [← Sumcheck.Impl.Computable.generalOracleProver_eq] at hp
    have hretains := Sumcheck.Impl.Computable.generalOracleProver_run_retains R 3 oSpec pp.ℓ_m
      (boolEmbedding R) _ () z.1 hp
    change z.1.2 = ((out, innerO), ()) at heq
    have horacles : innerO = (lens pp).materializeInput s o :=
      (congrArg (fun q => q.1.2) heq).symm.trans hretains
    rw [horacles] at ho
    exact (outputRelation_iff pp s o out).mp ho

private theorem compatible_oracles (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (out : Sumcheck.Spec.StatementRound R pp.ℓ_m (.last pp.ℓ_m) ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    (hc : Verifier.compatStatement (lens pp).toLens
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).toVerifier (s, o) out) :
    out.2 = (lens pp).materializeInput s o := by
  obtain ⟨tr, ht⟩ := hc
  rw [OptionT.mem_support_iff] at ht
  simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk,
    Sumcheck.Spec.oracleVerifier_materializeOutput] at ht
  rw [support_map] at ht
  obtain ⟨value, _, hv⟩ := ht
  cases value with
  | none => cases hv
  | some value => exact (congrArg Prod.snd (Option.some.inj hv)).symm

/-- The virtual-polynomial lens transports knowledge back to the retained Spartan context. -/
instance lensKnowledgeSound : Extractor.Lens.IsKnowledgeSound
    (relIn (R := R) pp) (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) 0)
    (relOut (R := R) pp)
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (.last pp.ℓ_m))
    ((Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).toVerifier.compatStatement
      (lens pp).toLens) (fun _ _ => True)
    ⟨(lens pp).toLens, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    rintro ⟨s, o⟩ ⟨out, io⟩ ⟨⟩ hc ho
    left
    have hp := compatible_oracles pp oSpec s o (out, io) hc
    change io = (lens pp).materializeInput s o at hp
    subst io
    exact (outputRelation_iff pp s o out).mpr ho
  lift_knowledgeSound := by
    rintro ⟨s, o⟩ ⟨⟩ ⟨⟩ _ h
    exact (inputRelation_iff pp s o).mp h

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The honest first sumcheck is perfectly complete for the zero-check claim and first
terminal evaluation. -/
theorem perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  change (oracleReduction pp oSpec).toReduction.perfectCompleteness _ _ _ _
  rw [oracleReduction_toReduction]
  exact Reduction.liftContext_perfectCompleteness
    (lens := proverContextLens pp)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness R 3 (boolEmbedding R) pp.ℓ_m oSpec
      (init := init) (impl := impl))

end

open scoped NNReal

variable [Fintype R] [IsDomain R] [SampleableType R]
    {ι : Type} (oSpec : OracleSpec ι) {σ : Type}
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

variable (init impl)

/-- The data and bound furnished by the general sumcheck knowledge theorem. -/
structure InnerCertificate where
  witness : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + 1) → Type
  extractor : Extractor.RoundByRound oSpec
    (Sumcheck.Spec.StatementRound R pp.ℓ_m 0 ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i)) Unit Unit
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) witness
  state : Verifier.KnowledgeStateFunction init impl
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) 0)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (.last pp.ℓ_m))
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).toVerifier extractor
  sound : Verifier.rbrKnowledgeSoundnessWith init impl
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) 0)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (.last pp.ℓ_m))
      (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec).toVerifier
      witness extractor state (fun _ => (3 : ℝ≥0) / Fintype.card R)

/-- Choose the witness family, extractor, and state supplied by the proved general sumcheck
certificate. The general theorem exports their existence rather than computational data. -/
noncomputable def innerCertificate : InnerCertificate (R := R) pp oSpec init impl :=
  Classical.choice <| by
    obtain ⟨W, E, K, h⟩ := Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      R 3 (boolEmbedding R) pp.ℓ_m oSpec (init := init) (impl := impl)
    exact ⟨⟨W, E, K, h⟩⟩

/-- The retained terminal witness paired with the chosen inner sumcheck witness family. -/
noncomputable def intermediateWitness :
    Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2) + 1) → Type :=
  fun k => Unit × (innerCertificate (R := R) pp oSpec init impl).witness k

/-- The chosen inner extractor lifted through the explicit virtual-polynomial lens.
Its only noncomputable ingredient is the certificate chosen from the general theorem. -/
noncomputable def rbrExtractor : Extractor.RoundByRound oSpec
    (Statement (R := R) pp ×
      (∀ i, OracleStatement (R := R) pp i)) Unit Unit
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) (intermediateWitness (R := R) pp oSpec init impl) :=
  (innerCertificate (R := R) pp oSpec init impl).extractor.liftContext
    ⟨(lens pp).toLens, Witness.InvLens.trivial⟩

/-- The inner semantic knowledge state transported through the virtual-polynomial lens.
The underlying certificate is chosen from the general sumcheck existence theorem. -/
noncomputable def knowledgeStateFunction :
    (oracleVerifier (R := R) pp oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) (rbrExtractor pp oSpec init impl) := by
  rw [oracleVerifier_eq_liftContext]
  exact OracleVerifier.liftContextKnowledgeStateFunction
    (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec)
      (witLens := Witness.InvLens.trivial)
      (output pp oSpec) (innerCertificate (R := R) pp oSpec init impl).extractor
      (innerCertificate (R := R) pp oSpec init impl).state

/-- Fixed-prefix knowledge soundness for the named lifted certificate, with error
`3 / |R|` per challenge. -/
theorem rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn pp) (relOut pp) (intermediateWitness (R := R) pp oSpec init impl)
      (rbrExtractor pp oSpec init impl) (knowledgeStateFunction pp oSpec init impl)
      (fun _ => (3 : ℝ≥0) / Fintype.card R) := by
  exact OracleVerifier.liftContext_rbrKnowledgeSoundnessWith
    (Sumcheck.Spec.oracleVerifier R 3 (boolEmbedding R) pp.ℓ_m oSpec)
      (witLens := Witness.InvLens.trivial)
      (output pp oSpec) (innerCertificate (R := R) pp oSpec init impl).extractor
      (innerCertificate (R := R) pp oSpec init impl).state
      (innerCertificate (R := R) pp oSpec init impl).sound

variable {init impl}

/-- The first virtual sumcheck has fixed-prefix knowledge error `3 / |R|` per challenge. -/
theorem rbrKnowledgeSoundness :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn pp) (relOut pp) (fun _ => (3 : ℝ≥0) / Fintype.card R) :=
  ⟨intermediateWitness (R := R) pp oSpec init impl, rbrExtractor pp oSpec init impl,
    knowledgeStateFunction pp oSpec init impl,
    rbrKnowledgeSoundnessWith pp oSpec init impl⟩

end Spartan.FirstSumcheck
