/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.LiftContext.OracleReduction
public import ArkLib.OracleReduction.Security.Guarded

/-!
# Simple Oracle Reduction: Random Query

A one-round oracle reduction that tests an identity `f = g` between two values of a type with an
oracle interface, by comparing their answers at one uniformly random query.

The values `f stmt oracles` and `g stmt oracles` are determined by the input statement and oracle
statements. They may be oracle statements themselves, or virtual values that no party sends,
such as a polynomial assembled from several committed ones.
   - The input relation is `f = g`.
   - The verifier samples a uniform query `q` and sends it to the prover. It performs no checks
     and makes no oracle queries; it outputs `q` alongside the input statement and keeps every
     input oracle.
   - The output relation is that `f` and `g` give the same answer at `q`.

Completeness is immediate. Round-by-round knowledge soundness has error `ε` whenever every pair
of distinct values `f ≠ g` that can occur agrees at a uniform query with probability at most
`ε`. Two special cases:
   - comparing two oracle statements of a type with oracle distance at most `d` (`distanceLE`),
     with error `d / |Query|` (`oracleVerifier_rbrKnowledgeSoundness_of_distanceLE`);
   - polynomial identity testing, comparing a polynomial with `0` by evaluation at a random point
     (`RandomEvaluation`).
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec
open scoped NNReal ENNReal

namespace RandomQuery

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type) {κ : Type}
    (OStatement : κ → Type) [∀ i, OracleInterface (OStatement i)]

section Relations

variable (M : Type) [O : OracleInterface M]


variable (f g : Statement → (∀ i, OStatement i) → M)

/-- The input relation: the two values are equal. -/
def relIn : Set ((Statement × (∀ i, OStatement i)) × Unit) :=
  {p | f p.1.1 p.1.2 = g p.1.1 p.1.2}

/-- The output relation: the two values give the same answer at the sampled query. -/
def relOut : Set (((Query M × Statement) × (∀ i, OStatement i)) × Unit) :=
  {p | answer (f p.1.1.2 p.1.2) p.1.1.1 = answer (g p.1.1.2 p.1.2) p.1.1.1}

end Relations

section Protocol

variable (Q : Type)

/-- One uniformly sampled query from `Q`. -/
@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Q]⟩

/-- The prover retains the context and receives the query. -/
def oracleProver : OracleProver oSpec Statement OStatement Unit
    (Q × Statement) OStatement Unit (pSpec Q) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i)
  | 1 => (Q × Statement) × (∀ i, OStatement i)
  input := fun p => p.1
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun p => pure fun q => ((q, p.1), p.2)
  output := fun p => pure (p, ())

instance : (oracleProver oSpec Statement OStatement Q).OutputIsPure :=
  ⟨_, fun _ => rfl⟩

/-- The verifier forwards its query and retains every input oracle. -/
def oracleVerifier : OracleVerifier oSpec Statement OStatement
    (Q × Statement) OStatement (pSpec Q) where
  verify := fun stmt challenges => pure (challenges ⟨0, rfl⟩, stmt)
  outputOracle := .inl {
    embed := ⟨Sum.inl, Sum.inl_injective⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

@[simp]
theorem oracleVerifier_materializeOutput (challenges : (pSpec Q).Challenges)
    (oracles : ∀ i, OStatement i) (messages : (pSpec Q).Messages) :
    (oracleVerifier oSpec Statement OStatement Q).materializeOutput
      challenges oracles messages = oracles := by
  funext i
  rfl

/-- The random-query reduction, with no oracle queries and no checks. -/
def oracleReduction : OracleReduction oSpec Statement OStatement Unit
    (Q × Statement) OStatement Unit (pSpec Q) where
  prover := oracleProver oSpec Statement OStatement Q
  verifier := oracleVerifier oSpec Statement OStatement Q

instance : VerifierOnly (pSpec Q) where
  verifier_first' := by simp

/-- The verifier has the always-true guard and deterministic query-forwarding verdict. -/
def guardedForm :
    (oracleVerifier oSpec Statement OStatement Q).toVerifier.GuardedForm where
  check := fun _ _ => true
  out := fun stmt tr => ((tr.challenges ⟨0, rfl⟩, stmt.1), stmt.2)
  verify_eq := fun stmt tr => by
    simp only [OracleVerifier.toVerifier, oracleVerifier]
    rfl

/-- The round-by-round extractor retains the unique witness. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (Statement × (∀ i, OStatement i)) Unit Unit (pSpec Q) (fun _ => Unit) where
  extractIn := fun _ w => w
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

end Protocol

variable (M : Type) [O : OracleInterface M] [SampleableType (Query M)]
    (f g : Statement → (∀ i, OStatement i) → M)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}


/-- The random-query reduction is perfectly complete: equal values agree at every query. -/
theorem oracleReduction_completeness :
    (oracleReduction oSpec Statement OStatement (Query M)).perfectCompleteness init impl
      (relIn Statement OStatement M f g) (relOut Statement OStatement M f g) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oracles⟩ wit hfg x hx
  simp only [relIn, Set.mem_ofPred_eq] at hfg
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
  change answer (f stmt oracles) _ = answer (g stmt oracles) _
  rw [hfg]

/-- Before the query, knowledge means the identity `f = g`; afterwards it means agreement at the
sampled query. -/
def knowledgeStateFunction :
    (oracleVerifier oSpec Statement OStatement (Query M)).KnowledgeStateFunction init impl
      (relIn Statement OStatement M f g) (relOut Statement OStatement M f g)
      (rbrExtractor oSpec Statement OStatement (Query M)) where
  toFun
  | 0 => fun stmt _ _ => f stmt.1 stmt.2 = g stmt.1 stmt.2
  | 1 => fun stmt tr _ =>
    answer (f stmt.1 stmt.2) (tr ⟨0, by decide⟩ : Query M) =
      answer (g stmt.1 stmt.2) (tr ⟨0, by decide⟩ : Query M)
  toFun_empty := fun _ _ h => h
  toFun_next | 0 => fun hDir _ _ _ => by simp at hDir
  toFun_full := fun stmt tr wit => by
    intro h
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hRel⟩ := h
    simp only [Verifier.run, OracleVerifier.toVerifier,
      support_bind, Set.mem_iUnion] at hx
    rw [oracleVerifier_materializeOutput] at hx
    simp only [oracleVerifier] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
      Set.mem_singleton_iff, Option.map_some, Option.some.injEq] at hx
    subst x
    exact hRel

/-- Fixed-prefix knowledge soundness for the named extractor and knowledge state, with error `ε`
when every pair of distinct values agrees at a uniform query with probability at most `ε`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith (ε : ℝ≥0)
    (hAgree : ∀ stmt oracles, f stmt oracles ≠ g stmt oracles →
      Pr{let q ← $ᵗ Query M}[answer (f stmt oracles) q = answer (g stmt oracles) q] ≤ ε) :
    (oracleVerifier oSpec Statement OStatement
        (Query M)).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn Statement OStatement M f g) (relOut Statement OStatement M f g)
      (fun _ => Unit) (rbrExtractor oSpec Statement OStatement (Query M))
      (knowledgeStateFunction oSpec Statement OStatement M f g) (fun _ => ε) := by
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
  have hconcat (q : Query M) :
      @ProtocolSpec.Transcript.concat 1 (pSpec (Query M)) (0 : Fin 1) q
        (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1) = q :=
    ProtocolSpec.Transcript.concat_zero (pSpec := pSpec (Query M)) q _
  rw [prEvent_congr ($ᵗ Query M) _ _ fun q => by rw [hconcat]]
  by_cases hfg : f stmt oracles = g stmt oracles
  · simp [hfg]
  · simpa only [hfg, not_false_eq_true, true_and] using hAgree stmt oracles hfg

/-- Fixed-prefix round-by-round knowledge soundness with error `ε`. -/
theorem oracleVerifier_rbrKnowledgeSoundness (ε : ℝ≥0)
    (hAgree : ∀ stmt oracles, f stmt oracles ≠ g stmt oracles →
      Pr{let q ← $ᵗ Query M}[answer (f stmt oracles) q = answer (g stmt oracles) q] ≤ ε) :
    (oracleVerifier oSpec Statement OStatement (Query M)).toVerifier.rbrKnowledgeSoundness
      init impl (relIn Statement OStatement M f g) (relOut Statement OStatement M f g)
      (fun _ => ε) :=
  ⟨fun _ => Unit, rbrExtractor oSpec Statement OStatement (Query M),
    knowledgeStateFunction oSpec Statement OStatement M f g,
    oracleVerifier_rbrKnowledgeSoundnessWith oSpec Statement OStatement M f g ε
      hAgree⟩

section Distance

variable {M} [Fintype (Query M)] [Nonempty (Query M)]
    [∀ q, DecidableEq (O.toOC.spec q)]

/-- Two distinct values of a type with oracle distance at most `d` agree at a uniform query with
probability at most `d / |Query|`. -/
theorem prob_answer_eq_le_of_distanceLE {d : ℕ} (hDist : distanceLE O d) (a b : M)
    (hab : a ≠ b) :
    Pr{let q ← $ᵗ Query M}[answer a q = answer b q] ≤
      ((d : ℝ≥0) / Fintype.card (Query M) : ℝ≥0) := by
  let decPred : DecidablePred (fun q : Query M => answer a q = answer b q) := fun q =>
    (inferInstance : DecidableEq (O.toOC.spec q)) (answer a q) (answer b q)
  rw [@SampleableType.prEvent_uniformSample (Query M) _ _ _ decPred]
  have hfilter : Finset.univ.filter (fun q => answer a q = answer b q) =
      O.agreementQueries a b := by
    ext q
    simp
  rw [hfilter]
  have hdenom : (Fintype.card (Query M) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div hdenom]
  apply ENNReal.div_le_div_right
  exact_mod_cast hDist a b hab

variable (M)

/-- For a type with oracle distance at most `d`, the random-query reduction is round-by-round
knowledge sound with error `d / |Query|`. -/
theorem oracleVerifier_rbrKnowledgeSoundness_of_distanceLE {d : ℕ} (hDist : distanceLE O d) :
    (oracleVerifier oSpec Statement OStatement (Query M)).toVerifier.rbrKnowledgeSoundness
      init impl (relIn Statement OStatement M f g) (relOut Statement OStatement M f g)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query M) : ℝ≥0)) :=
  oracleVerifier_rbrKnowledgeSoundness oSpec Statement OStatement M f g _
    fun _ _ hfg => prob_answer_eq_le_of_distanceLE hDist _ _ hfg

end Distance

end RandomQuery
