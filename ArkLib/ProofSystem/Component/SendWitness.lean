/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
public import Mathlib.Data.FinEnum

/-!
# Simple Oracle Reduction - SendWitness

This file contains the (oracle) reduction for the trivial one-message protocol where the prover
sends the (entire) witness to the verifier. There are two variants:

1. For oracle reduction: the witness is an indexed family of types, and sent in a single oracle
  message to the verifier (using the derived indexed product instance for oracle interface).

  We also define a simpler variant, `SendSingleWitness`, where one sends a single witness (converted
  to be indexed by `Fin 1`).

2. For reduction (`SendWitness`, no oracle statements): the witness is a type, and sent as a
  statement to the verifier.

## Security

The verifier of each variant is **pure** (`Verifier.IsPure` / `OracleVerifier.toVerifier.IsPure`)
and has no challenge rounds, so it is **coordinate-wise special sound** for any `CWSSStructure`
(`verifier_coordinateWiseSpecialSoundWith` and, for the oracle variant,
`SendSingleWitness.oracleVerifier_coordinateWiseSpecialSoundWith`), via the no-challenge bridge
`Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`. The named extractor reads the
witness off the tree's unique transcript (`fun _ tree _ => some (tree.onlyPath.fullTranscript 0)`)
— the canonical "open in the clear" base case.
`SendSingleWitness.Adapter` supplies the shared one-message stage: it maps statements, encodes
honest witnesses, decodes transcript messages, and materializes either embedded or simulated
output oracles. Its constantly true guarded form, transcript-reading extractor, and knowledge state
function prove zero-error round-by-round knowledge soundness from backward relation transfer.
Forward transfer gives perfect completeness. Plonk and Spartan instantiate this adapter, as does the
fixed-output sender via the identity adapter.
These results are `sorryAx`-free. The indexed-family oracle variant (`section OracleReduction`) is
deferred; see the note there.
-/

@[expose] public section

open OracleSpec OracleComp OracleQuery ProtocolSpec Function Equiv

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

namespace SendWitness

/-!
  First, the reduction version (no oracle statements)
-/

section Reduction

variable (Witness : Type)

@[reducible, simp]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

instance : ∀ i, VCVCompatible ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

/-- The `SendWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This is
what makes its (coordinate-wise) special soundness reduce to the no-challenge bridge. -/
instance instIsEmptyChallengeIdx : IsEmpty (pSpec Witness).ChallengeIdx := ⟨fun ⟨0, h⟩ => nomatch h⟩

@[inline, specialize]
def prover : Prover oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => pure (⟨stmt, wit⟩, ())

/-- The `SendWitness` prover has pure output: it pairs up the state it already holds, with no
oracle query. -/
instance instOutputIsPure : (prover oSpec Statement Witness).OutputIsPure := ⟨_, fun _ => rfl⟩

@[inline, specialize]
def verifier : Verifier oSpec Statement (Statement × Witness) (pSpec Witness) where
  verify := fun stmt transcript => pure ⟨stmt, transcript 0⟩

@[inline, specialize]
def reduction : Reduction oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement Witness

variable {Statement} {Witness}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

@[reducible, simp]
def toRelOut : Set ((Statement × Witness) × Unit) :=
  Prod.fst ⁻¹' relIn

/-- The `SendWitness` verifier is pure: it deterministically returns `⟨stmt, transcript 0⟩`. This
discharges the deterministic-left hypothesis of the CWSS/tree-soundness binary append, so the
component can appear as a left factor in a sequential composition. -/
instance instIsPure : (verifier oSpec Statement Witness).IsPure :=
  ⟨fun stmt tr => ⟨stmt, tr 0⟩, fun _ _ => rfl⟩

open Classical in
/-- The `SendWitness` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness init impl relIn (toRelOut relIn) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  let tr : (pSpec Witness).FullTranscript :=
    ProtocolSpec.Transcript.concat (m := 0) witIn
      (default : (pSpec Witness).Transcript 0)
  have hrun : ((reduction oSpec Statement Witness).run stmtIn witIn).run =
      pure (some ((tr, (stmtIn, witIn), ()), (stmtIn, witIn))) := rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨_, rfl, hIn, rfl⟩

/-- **Coordinate-wise special soundness of `SendWitness`, named form.** The verifier has no
challenge rounds, so CWSS collapses (via the no-challenge bridge
`coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`) to a transcript-level extraction
obligation. The named extractor reads the witness off the tree's unique transcript — the witness
*is* the (single) prover message. Since the verifier is pure with output `⟨stmt, tr 0⟩` and
`relOut = Prod.fst ⁻¹' relIn`, acceptance into `relOut.language` forces `⟨stmt, tr 0⟩ ∈ relIn`,
which is exactly the extracted witness. This is the canonical "open in the clear" CWSS base case,
and holds for *any* coordinate-wise structure `D`.

The extractor is **witnessing-agnostic** — the witness is in the tree, so it never consults its
leaf witnessing. That is precisely what makes `SendWitness` a *closing* factor: a chain ending in
it runs as a computable function of `(stmtIn, tree)` alone. -/
theorem verifier_coordinateWiseSpecialSoundWith (D : CWSSStructure (pSpec Witness)) :
    Verifier.coordinateWiseSpecialSoundWith init impl D relIn (toRelOut relIn)
      (verifier oSpec Statement Witness)
      (fun _ tree _ => some (tree.onlyPath.fullTranscript 0)) := by
  have h := Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl D
    (verifier oSpec Statement Witness) relIn (toRelOut relIn) (fun _ tr => tr 0)
    (fun stmtIn tr hAcc => by
      have hmem : (⟨stmtIn, tr 0⟩ : Statement × Witness) ∈ (toRelOut relIn).language :=
        Verifier.mem_of_pure_accepting init impl (verifier oSpec Statement Witness) stmtIn tr
          (toRelOut relIn).language ⟨stmtIn, tr 0⟩ rfl hAcc
      obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
      exact hu)
  exact h

end Reduction

/-!
  Now, the oracle reduction version.

  The oracle version of the indexed-family witness-sending component is not yet formalized.
-/

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  {ιw : Type} [FinEnum ιw] (Witness : ιw → Type) [∀ i, OracleInterface (Witness i)]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[∀ i, Witness i]⟩

/-- The oracle prover for the `SendWitness` oracle reduction.

For each round `i : Fin (FinEnum.card ιw)`, the prover sends the witness
`wit (FinEnum.equiv.symm i)` to the verifier.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement (∀ i, Witness i)
    Statement (OStatement ⊕ᵥ Witness) Unit
    (oraclePSpec Witness) where
  PrvState := fun _ => (Statement × (∀ i, OStatement i)) × (∀ i, Witness i)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  -- No challenge is sent to the prover
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ => pure (⟨stmt, Sum.rec oStmt wit⟩, ())

/-- The `SendWitness` oracle prover has pure output: it exposes the witness alongside the input
oracles, with no oracle query. -/
instance instOutputIsPureOracle :
    (oracleProver oSpec Statement OStatement Witness).OutputIsPure := ⟨_, fun _ => rfl⟩

end OracleReduction

end SendWitness

namespace SendSingleWitness

/-!
  A special case of `SendWitness` oracle reduction where there is only one witness. We implicitly
  convert to `fun _ : Fin 1 => Witness`.
-/

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type) [OracleInterface Witness]

instance instOutputOracleInterface :
    ∀ i : ιₛ ⊕ Fin 1,
      OracleInterface (Sum.elim OStatement (fun _ : Fin 1 => Witness) i) :=
  fun i => OracleInterface.instRecType i

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

/-- The `SendSingleWitness` protocol is a single `P_to_V` message, so it has no challenge rounds.
This is what makes its coordinate-wise special soundness reduce to the no-challenge bridge. -/
instance instIsEmptyChallengeIdx : IsEmpty (oraclePSpec Witness).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Transcript extraction depends only on the decoder, without any oracle interface. -/
def transcriptExtractor {Stmt Wit W : Type} (decode : W → Wit) :
    Extractor.RoundByRound oSpec Stmt Wit Unit (oraclePSpec W) (fun _ => W) where
  extractIn _ w := decode w
  extractMid | ⟨0, _⟩ => fun _ tr _ => tr ⟨0, by simp⟩
  extractOut _ tr _ := tr 0

/-- Adapt a single sent message to a statement map and output oracle representation. -/
structure Adapter {ιᵢ ιₒ : Type} (StmtIn : Type) (OStmtIn : ιᵢ → Type) (WitIn : Type)
    (StmtOut : Type) (OStmtOut : ιₒ → Type) (W : Type)
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
    [OracleInterface W] where
  /-- Map the public statement without inspecting the message. -/
  stmtOut : StmtIn → StmtOut
  /-- The message sent by the honest prover. -/
  encode : WitIn → W
  /-- Recover the input witness from the sent message. -/
  decode : W → WitIn
  /-- Expose input and message oracles by embedding or query simulation. -/
  outputOracle : OracleOutputEmbedding OStmtIn (oraclePSpec W).Message OStmtOut ⊕
    OracleOutputSimulation oSpec OStmtIn OStmtOut (oraclePSpec W)

namespace Adapter

variable {oSpec} {ιᵢ ιₒ : Type} {StmtIn WitIn StmtOut W : Type}
  {OStmtIn : ιᵢ → Type} {OStmtOut : ιₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (OStmtOut i)]
  [OracleInterface W]
  (A : Adapter oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut W)

/-- The full transcript consisting of one sent message. -/
def transcript (w : W) : (oraclePSpec W).FullTranscript := fun | ⟨0, _⟩ => w

/-- The statement and oracles exposed by a particular sent message. -/
def output (s : StmtIn × (∀ i, OStmtIn i)) (w : W) : StmtOut × (∀ i, OStmtOut i) :=
  (A.stmtOut s.1, OracleVerifier.materializeOutputOracle A.outputOracle
    (transcript w).challenges s.2 (transcript w).messages)

/-- Send the encoded witness and materialize the same output as the verifier. -/
def oracleProver : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut Unit
    (oraclePSpec W) where
  PrvState _ := (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨s, w⟩ => pure (A.encode w, (s, w))
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨s, w⟩ => pure (A.output s (A.encode w), ())

/-- Materialization needs no oracle query. -/
instance instOutputIsPure : A.oracleProver.OutputIsPure := ⟨_, fun _ => rfl⟩

/-- The verifier never rejects and exposes the adapter's oracle representation. -/
def oracleVerifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut (oraclePSpec W) where
  verify s _ := pure (A.stmtOut s)
  outputOracle := A.outputOracle

/-- The one-message oracle reduction induced by an adapter. -/
def oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut Unit
    (oraclePSpec W) := ⟨A.oracleProver, A.oracleVerifier⟩

/-- The honest transcript contains the encoded input witness. -/
theorem oracleProver_run (s : StmtIn × (∀ i, OStmtIn i)) (w : WitIn) :
    A.oracleProver.run s w = pure (transcript (A.encode w), A.output s (A.encode w), ()) := by
  change (pure _ : OracleComp _ _) = pure _
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

/-- The materialized verifier returns the output determined by the actual message. -/
theorem verifier_run (s : StmtIn × (∀ i, OStmtIn i))
    (tr : (oraclePSpec W).FullTranscript) :
    A.oracleVerifier.toVerifier.run s tr = pure (A.output s (tr 0)) := by
  have htr : tr = transcript (tr 0) := by
    funext i
    fin_cases i
    rfl
  conv_lhs => rw [htr]
  rfl

/-- Every adapter verifier is deterministic. -/
instance instIsPure : A.oracleVerifier.toVerifier.IsPure :=
  ⟨fun s tr => A.output s (tr 0), A.verifier_run⟩

/-- The stage has a constantly true guard. -/
def guardedForm : A.oracleVerifier.toVerifier.GuardedForm where
  check _ _ := true
  out s tr := A.output s (tr 0)
  verify_eq := A.verifier_run

/-- Read the message from the transcript and decode only at the input boundary. -/
def rbrExtractor : Extractor.RoundByRound oSpec (StmtIn × (∀ i, OStmtIn i))
    WitIn Unit (oraclePSpec W) (fun _ => W) :=
  transcriptExtractor oSpec A.decode

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × Unit))

/-- Decoded relation membership is the knowledge predicate before and after the send. -/
def knowledgeStateFunction
    (hdecode : ∀ s w, (A.output s w, ()) ∈ relOut → (s, A.decode w) ∈ relIn) :
    A.oracleVerifier.toVerifier.KnowledgeStateFunction init impl relIn relOut A.rbrExtractor where
  toFun
    | ⟨0, _⟩ => fun s _ w => (s, A.decode w) ∈ relIn
    | ⟨1, _⟩ => fun s tr _ => (s, A.decode (tr ⟨0, by simp⟩)) ∈ relIn
  toFun_empty _ _ h := h
  toFun_next := by
    intro m _ s tr msg w h
    fin_cases m
    exact h
  toFun_full s tr u h := by
    cases u
    exact hdecode s (tr ⟨0, by simp⟩) ((A.guardedForm.check_and_of_prEvent_pos h).2)

/-- With no verifier challenges, the fixed-prefix knowledge error is zero. -/
theorem rbrKnowledgeSoundnessWith
    (hdecode : ∀ s w, (A.output s w, ()) ∈ relOut → (s, A.decode w) ∈ relIn) :
    A.oracleVerifier.toVerifier.rbrKnowledgeSoundnessWith init impl relIn relOut
      (fun _ => W) A.rbrExtractor
      (A.knowledgeStateFunction init impl relIn relOut hdecode) (fun _ => 0) := by
  intro _ i
  exact isEmptyElim i

/-- Honest relation transfer gives perfect completeness of the actual one-message run. -/
theorem perfectCompleteness
    (hencode : ∀ s w, (s, w) ∈ relIn → (A.output s (A.encode w), ()) ∈ relOut) :
    A.oracleReduction.perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w hw result hresult
  have hrun : (A.oracleReduction.toReduction.run s w).run =
      pure (some ((transcript (A.encode w), A.output s (A.encode w), ()),
        A.output s (A.encode w))) := by
    rw [Reduction.run_run_eq_bind]
    change (do
      let p ← A.oracleProver.run s w
      let t ← (A.oracleVerifier.toVerifier.run s p.1).run
      pure (t.map (p, ·))) = _
    rw [A.oracleProver_run]
    simp only [pure_bind]
    rw [A.verifier_run]
    rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact ⟨_, rfl, hencode s w hw, rfl⟩

end Adapter

/-- The index embedding that exposes every input oracle and the single witness
message as output oracles. -/
def outputIndexEmbedding : (ιₛ ⊕ Fin 1) ↪ ιₛ ⊕ (oraclePSpec Witness).MessageIdx :=
  Function.Embedding.sumMap (.refl _)
    (Equiv.toEmbedding (.symm (subtypeUnivEquiv (by aesop))))

def outputEmbedding : OracleOutputEmbedding OStatement (oraclePSpec Witness).Message
    (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) where
  embed := outputIndexEmbedding Witness
  hEq := by
    intro i
    rcases i with j | j
    · rfl
    · fin_cases j
      rfl
  outputInterface_heq := by
    intro i
    rcases i with j | j
    · rfl
    · fin_cases j
      rfl

/-- The fixed-output witness sender is the identity adapter. -/
def adapter : Adapter oSpec Statement OStatement Witness Statement
    (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Witness where
  stmtOut := id
  encode := id
  decode := id
  outputOracle := .inl (outputEmbedding OStatement Witness)

/-- Send the witness unchanged and expose it alongside the input oracles. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) :=
  (adapter oSpec Statement OStatement Witness).oracleProver

/-- The fixed-output sender has pure output. -/
instance instOutputIsPure :
    (oracleProver oSpec Statement OStatement Witness).OutputIsPure :=
  Adapter.instOutputIsPure _

/-- The oracle verifier for the `SendSingleWitness` oracle reduction.

The verifier receives the input statement `stmt` and returns it, and also specifying the oracle
message as the output oracle statement.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness))
    (oraclePSpec Witness) :=
  (adapter oSpec Statement OStatement Witness).oracleVerifier

@[simp]
theorem oracleVerifier_materializeOutput
    (challenges : (oraclePSpec Witness).Challenges)
    (oStmt : ∀ i, OStatement i) (messages : (oraclePSpec Witness).Messages) :
    (oracleVerifier oSpec Statement OStatement Witness).materializeOutput
        challenges oStmt messages =
      Sum.rec oStmt (fun i => match i with | 0 => messages ⟨0, rfl⟩) := by
  unfold OracleVerifier.materializeOutput oracleVerifier
  change OracleVerifier.materializeOutputOracle
      (Sum.inl (outputEmbedding OStatement Witness)) challenges oStmt messages = _
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  rcases i with j | j
  · rfl
  · fin_cases j
    rfl

@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) :=
  (adapter oSpec Statement OStatement Witness).oracleReduction

variable {Statement} {OStatement} {Witness}

theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : Witness} :
    (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
      pure (fun i => by aesop, ⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ()) := by
  rw [oracleProver, Adapter.oracleProver_run]
  have hout : (adapter oSpec Statement OStatement Witness).output (stmt, oStmt) wit =
      (stmt, Sum.rec oStmt (fun _ => wit)) := by
    apply Prod.ext
    · rfl
    · funext i
      rcases i with j | j
      · rfl
      · fin_cases j
        rfl
  change pure (Adapter.transcript wit,
    (adapter oSpec Statement OStatement Witness).output (stmt, oStmt) wit, ()) = _
  rw [hout]
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (oraclePSpec Witness).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, Sum.rec oStmt (fun i => match i with | 0 => tr 0)⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [oracleVerifier_materializeOutput]
  rfl

/-- The `SendSingleWitness` oracle verifier is pure: its underlying (non-oracle) verifier
deterministically returns the statement together with the output oracle statements read off the
transcript. This discharges the deterministic-left hypothesis of the CWSS binary append. -/
instance instIsPure :
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.IsPure :=
  Adapter.instIsPure (adapter oSpec Statement OStatement Witness)

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (oRelIn : Set ((Statement × (∀ i, OStatement i)) × Witness))

@[reducible, simp]
def toORelOut :
    Set ((Statement × (∀ i, (Sum.elim OStatement fun _ : Fin 1 => Witness) i)) × Unit) :=
  Set.ofPred (fun ⟨⟨stmt, oStmtAndWit⟩, _⟩ =>
    oRelIn ⟨⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩, (oStmtAndWit (Sum.inr 0))⟩)

/-- The `SendSingleWitness` oracle reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness init impl oRelIn
    (toORelOut oRelIn) := by
  apply (adapter oSpec Statement OStatement Witness).perfectCompleteness init impl
  intro s w h
  exact h

/-- **Coordinate-wise special soundness of `SendSingleWitness`, named form.** The oracle verifier
has no challenge rounds, so CWSS collapses (via the oracle no-challenge bridge
`coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`) to a transcript-level extraction
obligation on the combined statement `Statement × (∀ i, OStatement i)`. The named extractor reads
the witness off the tree's unique transcript — the extracted witness *is* the single oracle
message — and is therefore **witnessing-agnostic**, a *closing* factor. Since the verifier is pure
with output `⟨stmt, oStmtOut⟩` (where `oStmtOut` exposes the old oracle statements together with
the message), acceptance into `(toORelOut oRelIn).language` unfolds to exactly
`⟨⟨stmt, oStmt⟩, tr 0⟩ ∈ oRelIn`. Holds for *any* coordinate-wise structure `D`. -/
theorem oracleVerifier_coordinateWiseSpecialSoundWith
    (D : CWSSStructure (oraclePSpec Witness)) :
    (oracleVerifier oSpec Statement OStatement Witness).coordinateWiseSpecialSoundWith init
      impl
      D oRelIn (toORelOut oRelIn)
      (fun _ tree _ => some (tree.onlyPath.fullTranscript 0)) := by
  have h := OracleVerifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl
    D
    (oracleVerifier oSpec Statement OStatement Witness) oRelIn (toORelOut oRelIn)
    (fun _ tr => tr 0)
    (fun s tr hAcc => by
      have hmem := Verifier.mem_of_pure_accepting init impl
        (oracleVerifier oSpec Statement OStatement Witness).toVerifier s tr
        (toORelOut oRelIn).language _ (oracleVerifier_toVerifier_run (oSpec := oSpec)) hAcc
      obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
      exact hu)
  exact h

end SendSingleWitness
