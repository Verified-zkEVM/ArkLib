/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Batching.Reduction
public import ArkLib.ProofSystem.Spartan.Terminal
public import ArkLib.ProofSystem.Spartan.Algebra.Computable
public import ArkLib.ProofSystem.Sumcheck.Impl.OracleProver
public import ArkLib.ProofSystem.Sumcheck.Spec.General
public import ArkLib.ProofSystem.Sumcheck.Domain

/-!
# Spartan's second virtual sumcheck

The degree-two virtual polynomial is derived from the retained matrix and witness tables.
Its evaluation program uses the three matrix queries and one witness query of the terminal
equation.
-/

@[expose] public section

namespace Spartan.SecondSumcheck

open OracleComp OracleInterface MvPolynomial Realization
open scoped NNReal

variable {R : Type} [CommRing R] [DecidableEq R] (pp : PublicParams)

/-- The second sumcheck's polynomial is computed from the retained tables and batch. -/
def polynomial (s : Batching.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 () :=
  Sumcheck.Impl.Computable.toOracleStatement
    (Computable.secondVirtual pp s.input.2.x (fun i => o (.inl i)) (o (.inr 0))
      s.input.2.r_x s.ρ)
    (Computable.secondVirtual_degreeOf_le pp _ _ _ _ _)

/-- The computational materialization has precisely the second virtual polynomial's semantics. -/
theorem polynomial_val (s : Batching.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    (polynomial pp s o).val = Algebra.secondVirtual (fun i => o (.inl i))
      (R1CS.𝕫 s.input.2.x (o (.inr 0))) s.input.2.r_x s.ρ :=
  Computable.secondVirtual_toPolynomial pp _ _ _ _ _

/-- A virtual evaluation query uses the terminal evaluation program at the requested point. -/
def queryPolynomial (s : Batching.Statement (R := R) pp) (r_y : Fin pp.ℓ_n → R) :
    OracleComp [OracleStatement (R := R) pp]ₒ R :=
  Terminal.queryValue pp ⟨s, r_y, 0⟩

/-- The virtual query program realizes the materialized degree-two polynomial. -/
theorem queryPolynomial_realizes (s : Batching.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) (r_y : Fin pp.ℓ_n → R) :
    simulateQ (simOracle0 (OracleStatement (R := R) pp) o) (queryPolynomial pp s r_y) =
      pure (eval r_y (polynomial pp s o).val) := by
  rw [polynomial_val]
  exact Terminal.queryValue_realizes pp _ o

/-- The second sumcheck retains the batch and original oracle family at its output. -/
def lens : OracleStatement.ExecutableLens
    (Batching.Statement (R := R) pp) (FinalStatement (R := R) pp)
    (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
    (Sumcheck.Spec.StatementRound R pp.ℓ_n (.last pp.ℓ_n))
    (OracleStatement (R := R) pp) (OracleStatement (R := R) pp)
    (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2)
    (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) where
  projStmt s := ⟨s.c, Fin.elim0⟩
  materializeInput s o _ := polynomial pp s o
  simulateInput s q := queryPolynomial pp s q.2
  simulateInput_eq s o q := by
    change simulateQ (simOracle0 (OracleStatement (R := R) pp) o)
      (queryPolynomial pp s q.2) = eval q.2 (polynomial pp s o).val
    exact queryPolynomial_realizes pp s o q.2
  liftStmt s out := ⟨s, out.challenges, out.target⟩
  materializeOutput o _ := o
  simulateOutput q := liftM (OracleSpec.query q)
  simulateOutput_eq _ _ _ := rfl

variable [Nontrivial R]

/-- The projected initial relation is exactly the second virtual sum claimed by batching. -/
theorem inputRelation_iff (s : Batching.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    (((lens pp).projStmt s, (lens pp).materializeInput s o), ()) ∈
        Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0 ↔
      Batching.outputRelation pp s o := by
  change (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ (pp.ℓ_n - 0),
    (polynomial pp s o).val.eval (Fin.append Fin.elim0 x ∘ Fin.cast (by simp))) = s.c ↔ _
  simp only [Nat.sub_zero, Fin.elim0_append, Function.comp_assoc]
  change (∑ x ∈ (Finset.univ.map (boolEmbedding R)) ^ᶠ pp.ℓ_n,
    (polynomial pp s o).val.eval x) = s.c ↔ _
  rw [show (Finset.univ.map (boolEmbedding R)) ^ᶠ pp.ℓ_n =
    (boolDomain R pp.ℓ_n).cube from rfl, sum_cube_boolDomain, polynomial_val]
  rfl

/-- The final inner relation is the terminal evaluation equation for the retained batch. -/
theorem outputRelation_iff (s : Batching.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (out : Sumcheck.Spec.StatementRound R pp.ℓ_n (.last pp.ℓ_n)) :
    ((out, (lens pp).materializeInput s o), ()) ∈
        Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (.last pp.ℓ_n) ↔
      terminalRelation pp ((lens pp).liftStmt s out) o := by
  simp only [Sumcheck.Spec.relationRound, Set.mem_ofPred_eq, Fin.val_last]
  rw [Fin.sum_piFinset_cast _ (Nat.sub_self pp.ℓ_n)]
  have hdom : (Finset.univ.map (boolEmbedding R)) ^ᶠ 0 = {Fin.elim0} := by
    ext x
    simp only [Fintype.piFinset, Finset.mem_map, Finset.mem_singleton]
    simp only [Finset.mem_pi, Finset.univ_eq_empty, Finset.notMem_empty, Finset.mem_map,
      Finset.mem_univ, true_and, Fin.exists_fin_two, Fin.isValue, boolEmbedding_zero,
      boolEmbedding_one, IsEmpty.forall_iff, Fin.exists_fin_zero_pi]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  rw [hdom, Finset.sum_singleton, Fin.append_right_nil _ _ (Nat.sub_self pp.ℓ_n)]
  change (polynomial pp s o).val.eval out.challenges = out.target ↔ _
  rw [polynomial_val]
  rfl

variable [SampleableType R] {ι : Type} (oSpec : OracleSpec ι)

/-- The virtual input is internal; the output retains the original oracle family. -/
def output : OracleVerifier.LiftContextOutput (lens (R := R) pp)
    (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec) where
  outputOracle := .inl ⟨Function.Embedding.inl, fun _ => rfl, fun _ => HEq.rfl⟩
  materialize_eq _ _ _ _ := rfl

/-- Route virtual-input queries through the retained tables and forward sent-message queries. -/
def queryImpl (s : Batching.Statement (R := R) pp) :
    QueryImpl (oSpec + ([Sumcheck.Spec.OracleStatement R pp.ℓ_n 2]ₒ +
      [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ))
      (OracleComp (oSpec + ([OracleStatement (R := R) pp]ₒ +
        [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ)))
  | .inl q => liftM (OracleSpec.query
      (spec := oSpec + ([OracleStatement (R := R) pp]ₒ +
        [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ)) (Sum.inl q))
  | .inr (.inl q) => OracleComp.liftComp (queryPolynomial (R := R) pp s q.2)
      (oSpec + ([OracleStatement (R := R) pp]ₒ +
        [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ))
  | .inr (.inr q) => liftM (OracleSpec.query
      (spec := oSpec + ([OracleStatement (R := R) pp]ₒ +
        [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ)) (Sum.inr (Sum.inr q)))

omit [Nontrivial R] [SampleableType R] in
/-- Direct query routing agrees with the general context-lifting implementation. -/
theorem queryImpl_eq (s : Batching.Statement (R := R) pp) :
    queryImpl pp oSpec s = OracleVerifier.liftContextQueryImpl (oSpec := oSpec)
      (pSpec := Sumcheck.Spec.pSpec R 2 pp.ℓ_n) (lens pp) s := by
  funext q
  rcases q with q | q
  · rfl
  · rcases q with q | q <;> rfl

/-- The second sumcheck verifier uses the virtual degree-two input and retained context. -/
def oracleVerifier : OracleVerifier oSpec (Batching.Statement (R := R) pp)
    (OracleStatement (R := R) pp) (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) where
  verify s challenges := OptionT.mk <| Option.map
    (fun out : Sumcheck.Spec.StatementRound R pp.ℓ_n (.last pp.ℓ_n) =>
      (⟨s, out.challenges, out.target⟩ : FinalStatement (R := R) pp)) <$>
    simulateQ (queryImpl pp oSpec s)
      ((Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).verify
        ⟨s.c, Fin.elim0⟩ challenges).run
  outputOracle := .inl ⟨Function.Embedding.inl, fun _ => rfl, fun _ => HEq.rfl⟩

/-- The executable verifier is exactly the named context lift of the general sumcheck. -/
theorem oracleVerifier_eq_liftContext : oracleVerifier (R := R) pp oSpec =
    (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext
      (lens pp) (output pp oSpec) := by
  apply OracleVerifier.ext
  · funext s challenges
    simp only [oracleVerifier, OracleVerifier.liftContext, queryImpl_eq]
    rfl
  · rfl

/-- Every rejection guard of the inner sumcheck is retained by the lifted verifier.
The semantic guarded form uses noncomputable mathematical polynomial evaluation. -/
noncomputable def guardedForm : (oracleVerifier (R := R) pp oSpec).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofEq
    (congrArg OracleVerifier.toVerifier (oracleVerifier_eq_liftContext pp oSpec)).symm <|
  OracleVerifier.liftContextGuardedForm (lens pp)
    (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec) (output pp oSpec)
    (Sumcheck.Spec.oracleVerifierGuardedForm R 2 (boolEmbedding R) pp.ℓ_n oSpec)

/-- The prover's context projection computes the polynomial from the original tables. -/
def proverContextLens : Context.Lens
    (Batching.Statement (R := R) pp × (∀ i, OracleStatement (R := R) pp i))
    (FinalStatement (R := R) pp × (∀ i, OracleStatement (R := R) pp i))
    (Sumcheck.Spec.StatementRound R pp.ℓ_n 0 ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i))
    (Sumcheck.Spec.StatementRound R pp.ℓ_n (.last pp.ℓ_n) ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i))
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := {
    toFunA := fun ⟨s, o⟩ => (⟨s.c, Fin.elim0⟩, fun _ => polynomial pp s o)
    toFunB := fun ⟨s, o⟩ ⟨out, _⟩ => (⟨s, out.challenges, out.target⟩, o) }

/-- The honest prover computes every round message and output target. -/
def oracleProver : OracleProver oSpec (Batching.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) :=
  Prover.liftContext (proverContextLens pp)
    (Sumcheck.Impl.Computable.generalOracleProver R 2 oSpec pp.ℓ_n (boolEmbedding R))

/-- The executable honest prover is the specified prover lifted to the Spartan context. -/
theorem oracleProver_eq : oracleProver (R := R) pp oSpec =
    Prover.liftContext (proverContextLens pp)
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).prover := by
  rw [oracleProver, Sumcheck.Impl.Computable.generalOracleProver_eq]

/-- The honest prover's final output uses no ambient oracle queries. -/
instance oracleProver_outputIsPure :
    Prover.OutputIsPure.{0} (oracleProver (R := R) pp oSpec) := by
  apply (congrArg Prover.OutputIsPure (oracleProver_eq (R := R) pp oSpec)).mpr
  have h :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).prover.OutputIsPure := by
    apply Prover.OutputIsPure.seqCompose
    intro i
    change Prover.OutputIsPure
      (Sumcheck.Spec.SingleRound.reduction R pp.ℓ_n 2 (boolEmbedding R) oSpec i).prover
    infer_instance
  let := h
  infer_instance

/-- The second virtual sumcheck reduction with its executable honest prover. -/
def oracleReduction : OracleReduction oSpec (Batching.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (FinalStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) where
  prover := oracleProver pp oSpec
  verifier := oracleVerifier pp oSpec

/-- The input relation is the batched second sumcheck claim. -/
def relIn := Batching.relOut (R := R) pp

/-- The output relation is the terminal second-polynomial evaluation equation. -/
def relOut := Terminal.relIn (R := R) pp

/-- Materializing the implemented reduction gives the ordinary context lift of sumcheck. -/
theorem oracleReduction_toReduction : (oracleReduction (R := R) pp oSpec).toReduction =
    (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.liftContext
      (proverContextLens pp) := by
  apply Reduction.ext
  · exact oracleProver_eq pp oSpec
  · change (oracleVerifier pp oSpec).toVerifier = _
    rw [oracleVerifier_eq_liftContext, OracleVerifier.liftContext_toVerifier_comm]
    change Verifier.liftContext (lens pp).toLens _ = Verifier.liftContext _
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
    rw [Sumcheck.Spec.oracleReduction_verifier_eq_oracleVerifier]
    rfl

/-- Honest execution retains the materialized virtual polynomial when lifting completeness. -/
instance contextLens_complete : (proverContextLens (R := R) pp).IsComplete
    (relIn pp) (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0)
    (relOut pp) (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (.last pp.ℓ_n))
    ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.compatContext
      (proverContextLens pp)) where
  proj_complete := by
    rintro ⟨s, o⟩ ⟨⟩ h
    exact (inputRelation_iff pp s o).mpr h
  lift_complete := by
    rintro ⟨s, o⟩ ⟨⟩ ⟨out, innerO⟩ ⟨⟩ hc _ ho
    obtain ⟨z, hz, heq⟩ := hc
    have hp : z.1 ∈ support
        ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).prover.run
          ((lens pp).toLens.proj (s, o)) ()) := by
      change some z ∈ MonadAttach.support
        (((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.run
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
    have hretains := Sumcheck.Impl.Computable.generalOracleProver_run_retains R 2 oSpec pp.ℓ_n
      (boolEmbedding R) _ () z.1 hp
    change z.1.2 = ((out, innerO), ()) at heq
    have horacles : innerO = (lens pp).materializeInput s o :=
      (congrArg (fun q => q.1.2) heq).symm.trans hretains
    rw [horacles] at ho
    exact (outputRelation_iff pp s o out).mp ho

private theorem compatible_oracles
    (s : Batching.Statement (R := R) pp) (o : ∀ i, OracleStatement (R := R) pp i)
    (out : Sumcheck.Spec.StatementRound R pp.ℓ_n (.last pp.ℓ_n))
    (innerO : ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i)
    (h : (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n
        oSpec).toVerifier.compatStatement
      (lens pp).toLens (s, o) (out, innerO)) :
    innerO = (lens pp).materializeInput s o := by
  obtain ⟨tr, ht⟩ := h
  rw [OptionT.mem_support_iff] at ht
  simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk,
    Sumcheck.Spec.oracleVerifier_materializeOutput] at ht
  rw [support_map] at ht
  obtain ⟨value, _, hv⟩ := ht
  cases value with
  | none => cases hv
  | some value => exact (congrArg Prod.snd (Option.some.inj hv)).symm

/-- The witness-free extractor lens reflects the projected input and terminal relations. -/
instance extractorLens_knowledgeSound : Extractor.Lens.IsKnowledgeSound
    (relIn (R := R) pp) (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0)
    (relOut (R := R) pp)
    (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (.last pp.ℓ_n))
    ((Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).toVerifier.compatStatement
      (lens pp).toLens) (fun _ _ => True)
    (⟨(lens pp).toLens, Witness.InvLens.trivial⟩ :
      Extractor.Lens _ _ _ _ Unit Unit Unit Unit) where
  proj_knowledgeSound := by
    rintro ⟨s, o⟩ ⟨out, innerO⟩ _ hc ho
    left
    have horacles := compatible_oracles pp oSpec s o out innerO hc
    rw [horacles]
    exact (outputRelation_iff pp s o out).mpr ho
  lift_knowledgeSound := by
    rintro ⟨s, o⟩ _ _ _ hi
    exact (inputRelation_iff pp s o).mp hi

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The honest second sumcheck is perfectly complete for the retained batch and terminal claim. -/
theorem perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  change (oracleReduction pp oSpec).toReduction.perfectCompleteness _ _ _ _
  rw [oracleReduction_toReduction]
  exact Reduction.liftContext_perfectCompleteness
    (lens := proverContextLens pp)
    (Sumcheck.Spec.oracleReduction_perfectCompleteness R 2 (boolEmbedding R) pp.ℓ_n oSpec
      (init := init) (impl := impl))

end Spartan.SecondSumcheck

namespace Spartan.SecondSumcheck

open OracleComp OracleInterface Realization
open scoped NNReal

variable {R : Type} [CommRing R] [DecidableEq R] [SampleableType R] [Fintype R] [IsDomain R]
  (pp : PublicParams) {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The data and bound furnished by the general sumcheck knowledge theorem. -/
structure InnerCertificate where
  witness : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 1) → Type
  extractor : Extractor.RoundByRound oSpec
    (Sumcheck.Spec.StatementRound R pp.ℓ_n 0 ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i)) Unit Unit
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) witness
  state : Verifier.KnowledgeStateFunction init impl
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (.last pp.ℓ_n))
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).toVerifier extractor
  sound : Verifier.rbrKnowledgeSoundnessWith init impl
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (.last pp.ℓ_n))
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec).toVerifier
      witness extractor state (fun _ => (2 : ℝ≥0) / Fintype.card R)

/-- Choose the witness family, extractor, and state supplied by the proved general sumcheck
certificate. The general theorem exports their existence rather than computational data. -/
noncomputable def innerCertificate : InnerCertificate (R := R) pp oSpec init impl :=
  Classical.choice <| by
    obtain ⟨W, E, K, h⟩ := Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      R 2 (boolEmbedding R) pp.ℓ_n oSpec (init := init) (impl := impl)
    exact ⟨⟨W, E, K, h⟩⟩

/-- The retained terminal witness paired with the chosen inner sumcheck witness family. -/
noncomputable def intermediateWitness :
    Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 1) → Type :=
  fun k => Unit × (innerCertificate (R := R) pp oSpec init impl).witness k

/-- The chosen inner extractor lifted through the explicit virtual-polynomial lens.
Its only noncomputable ingredient is the certificate chosen from the general theorem. -/
noncomputable def rbrExtractor : Extractor.RoundByRound oSpec
    (Batching.Statement (R := R) pp ×
      (∀ i, OracleStatement (R := R) pp i)) Unit Unit
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) (intermediateWitness (R := R) pp oSpec init impl) :=
  (innerCertificate (R := R) pp oSpec init impl).extractor.liftContext
    ⟨(lens pp).toLens, Witness.InvLens.trivial⟩

/-- The inner semantic knowledge state transported through the virtual-polynomial lens.
The underlying certificate is chosen from the general sumcheck existence theorem. -/
noncomputable def knowledgeStateFunction :
    (oracleVerifier (R := R) pp oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) (rbrExtractor pp oSpec init impl) := by
  let K := OracleVerifier.liftContextKnowledgeStateFunction
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec)
      (outerRelIn := relIn pp) (outerRelOut := relOut pp)
      (witLens := Witness.InvLens.trivial) (output pp oSpec)
      (innerCertificate (R := R) pp oSpec init impl).extractor
      (innerCertificate (R := R) pp oSpec init impl).state
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := by
      rw [oracleVerifier_eq_liftContext]
      exact K.toFun_full }

/-- Fixed-prefix knowledge soundness for the named lifted certificate, with error
`2 / |R|` per challenge. -/
theorem rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn pp) (relOut pp) (intermediateWitness (R := R) pp oSpec init impl)
      (rbrExtractor pp oSpec init impl) (knowledgeStateFunction pp oSpec init impl)
      (fun _ => (2 : ℝ≥0) / Fintype.card R) := by
  intro stmt i tr
  exact OracleVerifier.liftContext_rbrKnowledgeSoundnessWith
      (Sumcheck.Spec.oracleVerifier R 2 (boolEmbedding R) pp.ℓ_n oSpec)
      (outerRelIn := relIn pp) (outerRelOut := relOut pp)
      (witLens := Witness.InvLens.trivial) (output pp oSpec)
      (innerCertificate (R := R) pp oSpec init impl).extractor
      (innerCertificate (R := R) pp oSpec init impl).state
      (innerCertificate (R := R) pp oSpec init impl).sound stmt i tr

/-- The second virtual sumcheck has fixed-prefix knowledge error `2 / |R|` per challenge. -/
theorem rbrKnowledgeSoundness :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn pp) (relOut pp) (fun _ => (2 : ℝ≥0) / Fintype.card R) :=
  ⟨intermediateWitness (R := R) pp oSpec init impl, rbrExtractor pp oSpec init impl,
    knowledgeStateFunction pp oSpec init impl,
    rbrKnowledgeSoundnessWith pp oSpec init impl⟩

end Spartan.SecondSumcheck
