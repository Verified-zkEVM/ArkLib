/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Component.RandomEvaluation.Algebra
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Security.Guarded

/-!
# Random evaluation

A one-round reduction from the claim `P = 0`, for a multivariate polynomial `P` determined by the
statement and oracle statements, to the claim `P(τ) = 0` at a uniform point `τ : Fin m → F`.

The verifier samples `τ` and retains the input statement and oracles; it never evaluates or
queries `P`, which is a semantic view of the context and may be virtual. Completeness is immediate.
Round-by-round knowledge soundness has error `d / |F|` when every `P` has total degree at most `d`
(Schwartz–Zippel), and `m / |F|` when every `P` is multilinear.

A zero-check over the Boolean hypercube (as in Spartan) is an instance: the hypercube identity is
rewritten as the vanishing of a polynomial, and this component tests that polynomial.
-/

@[expose] public section

namespace RandomEvaluation

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec MvPolynomial
open scoped NNReal ENNReal

variable {ι : Type} (oSpec : OracleSpec ι) (F : Type) (m : ℕ)
    (Statement : Type) {κ : Type} (OStatement : κ → Type)
    [∀ i, OracleInterface (OStatement i)]

/-- One uniformly sampled vector challenge. -/
@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin m → F]⟩

/-- The prover retains the context and receives the challenge. -/
def oracleProver : OracleProver oSpec Statement OStatement Unit
    ((Fin m → F) × Statement) OStatement Unit (pSpec F m) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i)
  | 1 => ((Fin m → F) × Statement) × (∀ i, OStatement i)
  input := fun p => p.1
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun p => pure fun τ => ((τ, p.1), p.2)
  output := fun p => pure (p, ())

instance : (oracleProver oSpec F m Statement OStatement).OutputIsPure :=
  ⟨_, fun _ => rfl⟩

/-- The verifier forwards its challenge and retains every original oracle. -/
def oracleVerifier : OracleVerifier oSpec Statement OStatement
    ((Fin m → F) × Statement) OStatement (pSpec F m) where
  verify := fun stmt challenges => pure (challenges ⟨0, rfl⟩, stmt)
  outputOracle := .inl {
    embed := ⟨Sum.inl, Sum.inl_injective⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

@[simp]
theorem materializeOutput (challenges : (pSpec F m).Challenges)
    (oracles : ∀ i, OStatement i) (messages : (pSpec F m).Messages) :
    (oracleVerifier oSpec F m Statement OStatement).materializeOutput
      challenges oracles messages = oracles := by
  funext i
  rfl

/-- The challenge reduction, with no polynomial evaluation and no oracle queries. -/
def oracleReduction : OracleReduction oSpec Statement OStatement Unit
    ((Fin m → F) × Statement) OStatement Unit (pSpec F m) where
  prover := oracleProver oSpec F m Statement OStatement
  verifier := oracleVerifier oSpec F m Statement OStatement

instance : VerifierOnly (pSpec F m) where
  verifier_first' := by simp

/-- The verifier has the always-true guard and deterministic challenge-forwarding verdict. -/
def guardedForm :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.GuardedForm where
  check := fun _ _ => true
  out := fun stmt tr => ((tr.challenges ⟨0, rfl⟩, stmt.1), stmt.2)
  verify_eq := fun stmt tr => by
    simp only [OracleVerifier.toVerifier, oracleVerifier]
    rfl

variable [Field F] [Fintype F] [SampleableType F]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [Fintype F] in
/-- Perfect completeness follows because the zero polynomial vanishes everywhere. -/
theorem challenge_perfectCompleteness :
    (oracleReduction oSpec F m Statement OStatement).perfectCompleteness init impl
      (relIn F m Statement OStatement P) (relOut F m Statement OStatement P) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oracles⟩ wit hP x hx
  simp only [relIn, Set.mem_ofPred_eq] at hP
  simp only [OracleReduction.toReduction, oracleReduction, Reduction.run,
    Prover.run_of_verifier_first, oracleProver, oracleVerifier,
    OracleVerifier.toVerifier] at hx
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun y =>
    (pure (some y) : OracleComp _ _) from rfl] at hx
  simp only [Verifier.run, OracleComp.liftComp_pure, ← OracleComp.liftComp_eq_liftM,
    pure_bind, OptionT.run_mk] at hx
  obtain ⟨qSupport, hqSupport, hx⟩ := hx
  obtain ⟨q, rfl⟩ := hqSupport
  simp only [Challenge, ChallengeIdx, FullTranscript.challenges, Option.getM,
    Fin.isValue, Fin.vcons_of_one, MessageIdx, Message] at hx
  subst x
  refine ⟨_, rfl, ?_, rfl⟩
  change eval _ (P stmt oracles) = 0
  rw [hP, map_zero]

/-- The named backward extractor retains the unique witness. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (Statement × (∀ i, OStatement i)) Unit Unit (pSpec F m) (fun _ => Unit) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- Before sampling, knowledge means polynomial identity; afterwards it means vanishing at the
sampled point. -/
def knowledgeStateFunction :
    (oracleVerifier oSpec F m Statement OStatement).KnowledgeStateFunction init impl
      (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (rbrExtractor oSpec F m Statement OStatement) where
  toFun
  | 0 => fun stmt _ _ => P stmt.1 stmt.2 = 0
  | 1 => fun stmt tr _ => eval (tr ⟨0, by decide⟩) (P stmt.1 stmt.2) = 0
  toFun_empty := fun _ _ h => h
  toFun_next | 0 => fun hDir _ _ _ => by simp at hDir
  toFun_full := fun stmt tr wit => by
    intro h
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hRel⟩ := h
    simp only [Verifier.run, OracleVerifier.toVerifier,
      support_bind, Set.mem_iUnion] at hx
    rw [materializeOutput] at hx
    simp only [oracleVerifier] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
      Set.mem_singleton_iff, Option.map_some, Option.some.injEq] at hx
    subst x
    exact hRel

/-- Fixed-prefix knowledge soundness for the named extractor and knowledge state, with error
`d / |F|` when every polynomial has total degree at most `d`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCaseWith
    (d : ℕ) (hP : ∀ stmt oracles, (P stmt oracles).totalDegree ≤ d) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => Unit) (rbrExtractor oSpec F m Statement OStatement)
      (knowledgeStateFunction oSpec F m Statement OStatement P)
      (fun _ => (d : ℝ≥0) / Fintype.card F) := by
  rintro ⟨stmt, oracles⟩ i tr
  have hi : i = ⟨0, by simp⟩ := by
    apply Subtype.ext
    exact Fin.ext (by omega)
  subst i
  have htr : tr = fun j => Fin.elim0 j := by
    funext j
    exact Fin.elim0 j
  rw [htr]
  dsimp [knowledgeStateFunction, rbrExtractor, pSpec]
  simp only [exists_const]
  have hconcat (τ : Fin m → F) :
      @ProtocolSpec.Transcript.concat 1 (pSpec F m) (0 : Fin 1) τ
        (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1) = τ :=
    ProtocolSpec.Transcript.concat_zero (pSpec := pSpec F m) τ _
  rw [prEvent_congr ($ᵗ (Fin m → F)) _ _ fun τ => by rw [hconcat]]
  have hdenom : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div hdenom]
  exact badEvent_bound (P stmt oracles) d (hP stmt oracles)

/-- Worst-case, fixed-prefix round-by-round knowledge soundness with error `d / |F|`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCase
    (d : ℕ) (hP : ∀ stmt oracles, (P stmt oracles).totalDegree ≤ d) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => (d : ℝ≥0) / Fintype.card F) :=
  ⟨fun _ => Unit, rbrExtractor oSpec F m Statement OStatement,
    knowledgeStateFunction oSpec F m Statement OStatement P,
    challenge_rbrKnowledgeSoundnessWorstCaseWith oSpec F m Statement OStatement P d hP⟩

/-- The multilinear case of `challenge_rbrKnowledgeSoundnessWorstCaseWith`, with error
`m / |F|`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCaseWith_of_degreeOf_le_one
    (hP : ∀ stmt oracles i, degreeOf i (P stmt oracles) ≤ 1) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => Unit) (rbrExtractor oSpec F m Statement OStatement)
      (knowledgeStateFunction oSpec F m Statement OStatement P)
      (fun _ => (m : ℝ≥0) / Fintype.card F) :=
  challenge_rbrKnowledgeSoundnessWorstCaseWith oSpec F m Statement OStatement P m
    fun stmt oracles => totalDegree_le_of_degreeOf_le_one _ (hP stmt oracles)

/-- The multilinear case of `challenge_rbrKnowledgeSoundnessWorstCase`, with error `m / |F|`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCase_of_degreeOf_le_one
    (hP : ∀ stmt oracles i, degreeOf i (P stmt oracles) ≤ 1) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => (m : ℝ≥0) / Fintype.card F) :=
  challenge_rbrKnowledgeSoundnessWorstCase oSpec F m Statement OStatement P m
    fun stmt oracles => totalDegree_le_of_degreeOf_le_one _ (hP stmt oracles)

end RandomEvaluation
