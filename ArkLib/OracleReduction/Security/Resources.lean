/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import VCVio.OracleComp.QueryTracking.MeasuredProgram

/-!
# Knowledge soundness with measured extraction

`knowledgeSoundnessWith` bounds the error of one named extractor but says nothing about its cost.
A measured program (`OracleComp.MeasuredProgram`) supplies a declared instruction count for a
function with the same returned value as a deterministic straightline extractor. The contract adds
two claims to the game: the extractor returns that value purely, without querying `oSpec`, and every
execution path of the named program costs at most a budget. The agreement is extensional; it does
not identify the extractor's implementation trace with the program's trace.

The contract certifies the program's declared instructions only; `OracleComp.MeasuredProgram`
lists what is uncharged. Every deterministic extractor that makes no `oSpec` query has a measured
program with budget zero, so an existential statement over measured programs adds nothing to
`knowledgeSoundnessWith`. Only a named program with a stated instruction set is evidence.

These operation-count security contracts use finite pointwise natural-number profiles. Standard
addition and order are fixed by the definitions. Generic measured programs also support signed,
reversed or idempotent weights; such valuations are not operation counts. Fixed count arithmetic
does not charge pure work or require every instruction to have a nonzero charge.

An empty `Kind` records no resources: its count profile is uniquely zero, so every count budget
is vacuous. A scalar count uses `Unit → Nat`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

namespace Extractor.Straightline

/-- The inputs of a straightline extractor: the input statement, the output witness, the
transcript, and the prover's and verifier's query logs. -/
abbrev Input (oSpec : OracleSpec ι) (StmtIn WitOut : Type) (pSpec : ProtocolSpec n) : Type :=
  StmtIn × WitOut × FullTranscript pSpec × QueryLog oSpec × QueryLog oSpec

/-- A measured program for a deterministic straightline extractor: a measured program on the
extractor's inputs that returns an optional input witness. -/
abbrev MeasuredProgram (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type)
    (pSpec : ProtocolSpec n) (ω : Type) : Type 1 :=
  OracleComp.MeasuredProgram (Input oSpec StmtIn WitOut pSpec) (Option WitIn) ω

/-- The extractor returns the handlers' execution of the program on its view, without querying
`oSpec`. This lifts `OracleComp.MeasuredProgram.Realizes` from a value-returning function to
the extractor's computation by requiring it to return that value purely. -/
def MeasuredProgram.RealizesExtractor {ω : Type}
    (M : MeasuredProgram oSpec StmtIn WitIn WitOut pSpec ω)
    (extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) : Prop :=
  ∀ stmtIn witOut transcript proveQueryLog verifyQueryLog,
    (extractor stmtIn witOut transcript proveQueryLog verifyQueryLog).run =
      pure (M.run (stmtIn, witOut, transcript, proveQueryLog, verifyQueryLog))

end Extractor.Straightline

variable [∀ i, SampleableType (pSpec.Challenge i)]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

/-- Knowledge soundness of a named extractor together with an operation-count bound for a measured
program returning the same result. The budget bounds the program's declared instruction charges
only; see the module documentation for what is uncharged.
The program uses deterministic handlers, agrees with the extractor's pure return, and has a fixed
pointwise natural-number budget. -/
def knowledgeSoundnessWithResources {Kind : Type} [Finite Kind]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0)
    (program : Extractor.Straightline.MeasuredProgram oSpec StmtIn WitIn WitOut pSpec (Kind → Nat))
    (budget : Kind → Nat) : Prop :=
  verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError ∧
    program.RealizesExtractor extractor ∧ program.CostAtMost budget

namespace knowledgeSoundnessWithResources

variable {Kind : Type} [Finite Kind]
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {knowledgeError : ℝ≥0}
  {program : Extractor.Straightline.MeasuredProgram oSpec StmtIn WitIn WitOut pSpec (Kind → Nat)}
  {budget : Kind → Nat}

/-- Forget the measured program, keeping the game for the same named extractor. -/
theorem knowledgeSoundnessWith
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError :=
  h.1

/-- Forget the measured program and the extractor's identity. -/
theorem knowledgeSoundness
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  knowledgeSoundness_of_with init impl h.1

/-- A resource certificate remains valid for any larger budget. -/
theorem mono
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) {budget' : Kind → Nat} (hle : budget ≤ budget') :
    verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget' :=
  ⟨h.1, h.2.1, h.2.2.mono hle⟩

end knowledgeSoundnessWithResources

end Verifier

namespace OracleVerifier

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- Measured knowledge soundness of an oracle verifier is that of its non-oracle verifier. -/
def knowledgeSoundnessWithResources {Kind : Type} [Finite Kind]
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (extractor : Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0)
    (program : Extractor.Straightline.MeasuredProgram oSpec (StmtIn × ∀ i, OStmtIn i)
      WitIn WitOut pSpec (Kind → Nat))
    (budget : Kind → Nat) : Prop :=
  verifier.toVerifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
    knowledgeError program budget

namespace knowledgeSoundnessWithResources

variable {Kind : Type} [Finite Kind]
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
  {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
  {extractor : Extractor.Straightline oSpec (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec}
  {knowledgeError : ℝ≥0}
  {program : Extractor.Straightline.MeasuredProgram oSpec (StmtIn × ∀ i, OStmtIn i)
    WitIn WitOut pSpec (Kind → Nat)}
  {budget : Kind → Nat}

/-- Forget the measured program, keeping the game for the same named extractor. -/
theorem knowledgeSoundnessWith
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError :=
  h.1

/-- Forget the measured program and the extractor's identity. -/
theorem knowledgeSoundness
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  OracleVerifier.knowledgeSoundness_of_with init impl h.1

/-- A resource certificate remains valid for any larger budget. -/
theorem mono
    (h : verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget) {budget' : Kind → Nat} (hle : budget ≤ budget') :
    verifier.knowledgeSoundnessWithResources init impl relIn relOut extractor
      knowledgeError program budget' :=
  Verifier.knowledgeSoundnessWithResources.mono init impl h hle

end knowledgeSoundnessWithResources

end OracleVerifier
