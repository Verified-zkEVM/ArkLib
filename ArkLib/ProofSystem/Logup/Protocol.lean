import ArkLib.ProofSystem.Logup.Common
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# LogUp Protocol

Outer and full protocol specs, prover, verifier, and oracle reductions for LogUp Protocol 2.
-/

namespace Logup

open scoped BigOperators

section ProtocolSpec

open ProtocolSpec

/-- The four outer messages of Protocol 2.

The transcript shape is:
1. `P → V`: multiplicity oracle `m`.
2. `V → P`: challenge `x`.
3. `P → V`: helper oracles `h₁, ..., h_K`.
4. `V → P`: challenge `(z, λ)`.
-/
@[reducible]
def outerPSpec (F : Type) (n : ℕ) {M : ℕ} (params : ProtocolParams M) : ProtocolSpec 4 :=
  ⟨!v[.P_to_V], !v[MultiplicityMessage F n]⟩ ++ₚ
    ⟨!v[.V_to_P], !v[F]⟩ ++ₚ
    ⟨!v[.P_to_V], !v[HelperMessages F n params.numGroups]⟩ ++ₚ
    ⟨!v[.V_to_P], !v[BatchingChallenge F n params.numGroups]⟩

/-- The prover messages in the outer LogUp transcript are oracle-accessible. -/
noncomputable instance instOuterPSpecMessageOracleInterface
    {F : Type} [Field F] {n M : ℕ} {params : ProtocolParams M} :
    ∀ i, OracleInterface ((outerPSpec F n params).Message i) := by
  intro i
  rcases i with ⟨⟨idx, hidx⟩, hi⟩
  rcases idx with _ | idx
  · exact inferInstanceAs (OracleInterface (MultiplicityMessage F n))
  rcases idx with _ | idx
  · exact OracleInterface.instDefault
  rcases idx with _ | idx
  · exact inferInstanceAs (OracleInterface (HelperMessages F n params.numGroups))
  rcases idx with _ | idx
  · exact OracleInterface.instDefault
  omega

/-- The verifier challenges in the outer LogUp transcript are sampled uniformly from their types. -/
instance instOuterPSpecChallengeSampleable
    {F : Type} [Fintype F] [Inhabited F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((outerPSpec F n params).Challenge i)
  | ⟨0, h0⟩ => by
      change Direction.P_to_V = Direction.V_to_P at h0
      cases h0
  | ⟨1, _⟩ => by
      change SampleableType F
      infer_instance
  | ⟨2, h2⟩ => by
      change Direction.P_to_V = Direction.V_to_P at h2
      cases h2
  | ⟨3, _⟩ => by
      change SampleableType (BatchingChallenge F n params.numGroups)
      infer_instance

end ProtocolSpec

section FullProtocolSpec

open ProtocolSpec

/-- Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck. -/
@[reducible]
noncomputable def pSpec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :
    ProtocolSpec (4 + Fin.vsum (fun _ : Fin n => 2)) :=
  outerPSpec F n params ++ₚ logupSumcheckPSpec F n M params

/-- The full LogUp prover messages are oracle-accessible: outer LogUp messages followed by the
embedded sumcheck messages. -/
noncomputable instance instPSpecMessageOracleInterface
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, OracleInterface ((pSpec F n M params).Message i) := by
  change ∀ i,
    OracleInterface (((outerPSpec F n params) ++ₚ logupSumcheckPSpec F n M params).Message i)
  exact ProtocolSpec.instOracleInterfaceMessageAppend

/-- The full LogUp verifier challenges are sampleable: outer LogUp challenges followed by the
embedded sumcheck challenges. -/
noncomputable instance instPSpecChallengeSampleable
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((pSpec F n M params).Challenge i) := by
  letI : Inhabited F := ⟨0⟩
  change ∀ i,
    SampleableType (((outerPSpec F n params) ++ₚ
      logupSumcheckPSpec F n M params).Challenge i)
  exact ProtocolSpec.instSampleableTypeChallengeAppend

end FullProtocolSpec

section OuterProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The outer LogUp prover state. -/
def outerProverState : Fin 5 → Type
  | 0 => ∀ i, OStmtIn F n M i
  | 1 => ∀ i, OStmtIn F n M i
  | 2 => (∀ i, OStmtIn F n M i) × F
  | 3 => (∀ i, OStmtIn F n M i) × F
  | 4 => (∀ i, OStmtIn F n M i) × F × BatchingChallenge F n params.numGroups

/-- The honest prover for the outer LogUp phase. -/
noncomputable def outerProver :
    OracleProver oSpec (StmtIn F n M) (OStmtIn F n M) (WitIn F n M params)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (outerPSpec F n params) where
  PrvState := outerProverState F n M params

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt

  sendMessage
  | ⟨0, _⟩ => fun oStmt => pure (honestMultiplicity oStmt, oStmt)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun state => pure (honestHelpers params state.1 state.2, state)
  | ⟨3, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun oStmt => pure fun x => (oStmt, x)
  | ⟨2, h⟩ => nomatch h
  | ⟨3, _⟩ => fun state => pure fun batch => (state.1, state.2, batch)

  output := fun state =>
    let oStmt := state.1
    let x := state.2.1
    let batch := state.2.2
    pure (({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
      fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt x),
      ())

end OuterProver

section SumcheckProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The prover for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckProver [SampleableType F] :
    OracleProver oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtOut) (OStmtOut) Unit
      (logupSumcheckPSpec F n M params) :=
  (sumcheckOracleReduction oSpec F n M params).prover

end SumcheckProver

section FullProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp prover, composed from the outer prover and embedded sumcheck prover. -/
noncomputable def logupProver :
    OracleProver oSpec (StmtIn F n M) (OStmtIn F n M) (WitIn F n M params)
      (StmtOut) (OStmtOut) Unit
      (pSpec F n M params) :=
  Prover.append (outerProver oSpec F n M params) (sumcheckProver oSpec F n M params)

end FullProver

section OuterVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

@[grind]
def outerChallengeXIdx : (outerPSpec F n params).ChallengeIdx :=
  ⟨1, rfl⟩

@[grind]
def outerChallengeBatchIdx : (outerPSpec F n params).ChallengeIdx :=
  ⟨3, rfl⟩

@[grind]
def outerMultiplicityMessageIdx : (outerPSpec F n params).MessageIdx :=
  ⟨0, rfl⟩

@[grind]
def outerHelpersMessageIdx : (outerPSpec F n params).MessageIdx :=
  ⟨2, rfl⟩

/-- The verifier for the outer LogUp phase. -/
noncomputable def outerVerifier :
    OracleVerifier oSpec (StmtIn F n M) (OStmtIn F n M)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (outerPSpec F n params) where
  verify := fun _ challenges => do
    let x : F := challenges (outerChallengeXIdx F n M params)
  -- TODO: Replace the current table-scan rejection check with a faithful sampler
  -- for x ∉ { -t(u) : u ∈ H }.
    for u in (Finset.univ : Finset (Hypercube n)).toList do
      let tAtU : F ← OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <| OracleSpec.query
          (show [OStmtIn F n M]ₒ.Domain from ⟨InputOracleIdx.table, signPoint F u⟩)) _
      guard (x + tAtU ≠ 0)
    let batch : BatchingChallenge F n params.numGroups :=
      challenges (outerChallengeBatchIdx F n M params)
    pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }

  embed :=
    { toFun := fun
        | .input i => .inl i
        | .multiplicity => .inr (outerMultiplicityMessageIdx F n M params)
        | .helpers => .inr (outerHelpersMessageIdx F n M params)
      inj' := by
        intro a b h
        cases a with grind
    }

  hEq := by
    intro i
    cases i with
    | input j => rfl
    | multiplicity => rfl
    | helpers => rfl

end OuterVerifier

section SumcheckVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The verifier for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckVerifier [SampleableType F] :
    OracleVerifier oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (StmtOut) (OStmtOut)
      (logupSumcheckPSpec F n M params) :=
  (sumcheckOracleReduction oSpec F n M params).verifier

end SumcheckVerifier

section FullVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp verifier, obtained by composing the outer verifier with the embedded sumcheck
verifier. -/
noncomputable def logupVerifier :
    OracleVerifier oSpec (StmtIn F n M) (OStmtIn F n M)
      (StmtOut) (OStmtOut)
      (pSpec F n M params) :=
  OracleVerifier.append (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)

end FullVerifier

section OuterReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The outer LogUp phase as an ArkLib oracle reduction. -/
noncomputable def outerOracleReduction :
    OracleReduction oSpec (StmtIn F n M) (OStmtIn F n M) (WitIn F n M params)
      (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (outerPSpec F n params) where
  prover := outerProver oSpec F n M params
  verifier := outerVerifier oSpec F n M params

end OuterReduction

section FullReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp Protocol as an ArkLib oracle reduction. -/
noncomputable def logupOracleReduction :
    OracleReduction oSpec (StmtIn F n M) (OStmtIn F n M) (WitIn F n M params)
      (StmtOut) (OStmtOut) Unit
      (pSpec F n M params) where
  prover := logupProver oSpec F n M params
  verifier := logupVerifier oSpec F n M params

end FullReduction

end Logup
