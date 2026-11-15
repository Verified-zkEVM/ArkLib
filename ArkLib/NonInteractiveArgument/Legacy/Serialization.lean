/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Encoding.Serializer
public import ArkLib.NonInteractiveArgument.Legacy
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Security under NARG serialization for legacy verifiers

Parse adversarial bytes before verification or extraction. Valid parses preserve the original
algorithms and their public logs. Invalid parses return a rejecting result without oracle queries.
The reduction uses a fixed fallback payload only to make the induced typed adversary total;
its behavior on invalid bytes can only increase the typed experiment's failure probability.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace NARGSerialization

variable {ι κ κE : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {extractorSpec : OracleSpec κE} {Stmt Payload StmtOut Wit σ : Type}

/-- Event computations can be compared after a shared draw. -/
private theorem prEvent_bind_event_mono {α : Type} (mx : ProbComp α) {f g : α → ProbComp Prop}
    (h : ∀ a, prEvent (f a) ≤ prEvent (g a)) : prEvent (mx >>= f) ≤ prEvent (mx >>= g) := by
  simpa only [id_map] using prEvent_bind_mono_of_forall_le mx f g id id
    (fun a => by simpa only [id_map] using h a)

/-- Parse a whole NARG string, returning the supplied rejecting result on malformed bytes. -/
def verifier (serializer : Serializer Payload)
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut) (reject : Option StmtOut) :
    NonInteractiveVerifier ByteArray oSpec Stmt StmtOut where
  verify stmt messages := OptionT.mk <| match serializer.deserialize (messages 0) with
    | none => pure reject
    | some payload => (V.verify stmt (Fin.cons payload (fun i => i.elim0))).run

/-- Parsing before extraction preserves oracle permissions; malformed inputs return no witness. -/
def extractor (serializer : Serializer Payload)
    (E : Stmt → Payload → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit) :
    Stmt → ByteArray → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit := fun stmt bytes trP trV =>
  match serializer.deserialize bytes with
  | none => failure
  | some payload => E stmt payload trP trV

/-- Convert a byte-producing adversary into a typed adversary without adding queries. -/
def prover (serializer : Serializer Payload) (fallback : Payload)
    (P : OracleComp (oSpec + privateSpec) (Stmt × ByteArray)) :
    OracleComp (oSpec + privateSpec) (Stmt × Payload) :=
  (fun (stmt, bytes) => (stmt, (serializer.deserialize bytes).getD fallback)) <$> P

/-- Parsing and choosing a fallback preserve every query budget exactly. -/
@[simp] theorem prover_isQueryBoundP_iff (serializer : Serializer Payload) (fallback : Payload)
    (P : OracleComp (oSpec + privateSpec) (Stmt × ByteArray))
    (counts : (oSpec + privateSpec).Domain → Prop) [DecidablePred counts] (t : ℕ) :
    (prover serializer fallback P).IsQueryBoundP counts t ↔ P.IsQueryBoundP counts t := by
  simp [prover]

set_option backward.isDefEq.respectTransparency false in
/-- Malformed bytes cannot increase false acceptance; successful parses run the same verifier. -/
theorem soundness_probability_le (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut)
    (reject : Option StmtOut) (langIn : Set Stmt) (langOut : Set StmtOut)
    (hreject : ∀ out ∈ reject, out ∉ langOut)
    (P : OracleComp (oSpec + privateSpec) (Stmt × ByteArray)) :
    Pr{let out ← (adaptiveNARGSoundnessExp init impl privateImpl
      (verifier serializer V reject) P)}[nargSoundFailEvent langIn langOut out] ≤
    Pr{let out ← (adaptiveNARGSoundnessExp init impl privateImpl
      V (prover serializer fallback P))}[nargSoundFailEvent langIn langOut out] := by
  simp only [adaptiveNARGSoundnessExp_eq, prover, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_pure, map_bind, bind_map_left]
  simp only [map_pure]
  refine prEvent_bind_event_mono init ?_
  intro state
  refine prEvent_bind_event_mono
    ((simulateQ (impl.addLift privateImpl : QueryImpl _ (StateT σ ProbComp)) P).run state) ?_
  rintro ⟨⟨stmt, bytes⟩, state'⟩
  cases h : serializer.deserialize bytes with
  | some payload => simp [verifier, h]
  | none =>
    cases reject with
    | none => simp [verifier, h, nargSoundFailEvent]
    | some out =>
      have hn := hreject out (by simp)
      simp [verifier, h, nargSoundFailEvent, hn]

/-- The induced adversary keeps the byte adversary's complete query log unchanged. -/
theorem prover_withQueryLog (serializer : Serializer Payload) (fallback : Payload)
    (P : OracleComp (oSpec + privateSpec) (Stmt × ByteArray)) :
    (prover serializer fallback P).withQueryLog =
      (fun ((stmt, bytes), log) =>
        ((stmt, (serializer.deserialize bytes).getD fallback), log)) <$> P.withQueryLog := by
  simp [prover, withQueryLog]

set_option backward.isDefEq.respectTransparency false in
/-- Parsing preserves the extractor's logs and cannot increase extraction failure. -/
theorem knowledgeSoundness_probability_le (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut)
    (E : Stmt → Payload → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (reject : Option StmtOut) (relIn : Set (Stmt × Wit)) (langOut : Set StmtOut)
    (hreject : ∀ out ∈ reject, out ∉ langOut)
    (P : OracleComp (oSpec + privateSpec) (Stmt × ByteArray)) :
    Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl
      (verifier serializer V reject) (extractor serializer E) P)}[
        nargKSFailEvent relIn langOut out] ≤
    Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl
      V E (prover serializer fallback P))}[nargKSFailEvent relIn langOut out] := by
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq, prover_withQueryLog, simulateQ_bind,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    map_bind, bind_map_left, pure_bind, bind_assoc, map_pure]
  refine prEvent_bind_event_mono init ?_
  intro state
  refine prEvent_bind_event_mono
    ((simulateQ (impl.addLift privateImpl : QueryImpl _ (StateT σ ProbComp))
      P.withQueryLog).run state) ?_
  rintro ⟨⟨⟨stmt, bytes⟩, log⟩, state'⟩
  cases h : serializer.deserialize bytes with
  | some payload => simp [runVerifierWithLog, verifier, extractor, h]
  | none =>
    cases reject with
    | none =>
      simp [runVerifierWithLog, verifier, extractor, h, withQueryLog_pure, nargKSFailEvent]
    | some out =>
      have hn := hreject out (by simp)
      simp [runVerifierWithLog, verifier, extractor, h, withQueryLog_pure, nargKSFailEvent, hn]

/-- Whole-input parsing preserves adaptive soundness and its public-query budget. -/
theorem soundnessQueryBounded (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut)
    (reject : Option StmtOut) (langIn : Set Stmt) (langOut : Set StmtOut)
    (hreject : ∀ out ∈ reject, out ∉ langOut)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal)
    (h : V.adaptiveNARGSoundnessQueryBounded init impl langIn langOut counts t error) :
    (verifier serializer V reject).adaptiveNARGSoundnessQueryBounded
      init impl langIn langOut counts t error := by
  intro P hP
  exact (soundness_probability_le serializer fallback init impl (QueryImpl.id' unifSpec)
    V reject langIn langOut hreject P).trans
      (h (prover serializer fallback P) ((prover_isQueryBoundP_iff _ _ _ _ _).mpr hP))

/-- The parsed extractor preserves knowledge soundness with exactly the same error and budget. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor
    (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut)
    (E : Stmt → Payload → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (reject : Option StmtOut) (relIn : Set (Stmt × Wit)) (langOut : Set StmtOut)
    (hreject : ∀ out ∈ reject, out ∉ langOut)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal)
    (h : V.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init impl extractorImpl
      relIn langOut E counts t error) :
    (verifier serializer V reject).adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
      init impl extractorImpl relIn langOut (extractor serializer E) counts t error := by
  intro P hP
  exact (knowledgeSoundness_probability_le serializer fallback init impl (QueryImpl.id' unifSpec)
    extractorImpl V E reject relIn langOut hreject P).trans
      (h (prover serializer fallback P) ((prover_isQueryBoundP_iff _ _ _ _ _).mpr hP))

/-- One parsed extractor works for every public-query budget. -/
theorem knowledgeSoundnessQueryBounded (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (V : NonInteractiveVerifier Payload oSpec Stmt StmtOut)
    (reject : Option StmtOut) (relIn : Set (Stmt × Wit)) (langOut : Set StmtOut)
    (hreject : ∀ out ∈ reject, out ∉ langOut)
    (counts : ι → Prop) [DecidablePred counts] (error : ℕ → ENNReal)
    (h : V.adaptiveNARGKnowledgeSoundnessQueryBounded init impl extractorImpl
      relIn langOut counts error) :
    (verifier serializer V reject).adaptiveNARGKnowledgeSoundnessQueryBounded
      init impl extractorImpl relIn langOut counts error := by
  obtain ⟨E, hE⟩ := h
  exact ⟨extractor serializer E, fun t => knowledgeSoundnessQueryBoundedWithExtractor
    serializer fallback init impl extractorImpl V E reject relIn langOut hreject
    counts t (error t) (hE t)⟩

end NARGSerialization
