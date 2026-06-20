import ArkLib.ProofSystem.Logup.Common
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# LogUp Protocol

Protocol specs, honest prover, verifier, and oracle reductions for Protocol 2 of Haböck's LogUp
lookup argument (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The protocol checks that every value in the `M` lookup-column oracles occurs somewhere in the table
oracle.

## Protocol Specification

Protocol 2 is parameterized by:
- a field `F`;
- a row dimension `n`, with rows indexed by the Boolean hypercube;
- `M` lookup-column oracles `fᵢ : H → F` and one table oracle `t : H → F`;
- a partial-sum size `ell`, stored in `ProtocolParams`, which determines the number `K` of helper
  oracles; and
- the characteristic condition `char(F) > M * 2^n`.

The input relation says that every value appearing in any lookup column also appears somewhere in
the table. The protocol proves this relation as follows.

1. The prover sends the normalized multiplicity oracle `m`, which records how often table values are
   used by the lookup columns. The verifier samples the logarithmic-derivative challenge `x`.
2. Using `x`, the prover sends helper oracles `h₁, ..., h_K` for the partial-sum groups of the
   logarithmic-derivative identity.
3. The verifier samples a point `z : Fin n → F` and batching scalars `λ₁, ..., λ_K`. These data turn
   the helper identities into one batched polynomial `Q`, and the prover and verifier run generic
   sumcheck on the claim `∑ u ∈ H, Q(u) = 0`.
4. Sumcheck leaves a final point `r` and a claimed value `v = Q(r)`. The verifier queries the
   retained LogUp oracles at `r`, reconstructs `Q(r)`, and accepts only if this reconstructed value
   equals `v`.

### Formalization

The LogUp paper writes the row domain as `{±1}^n`; this formalization uses the affine-equivalent
Boolean hypercube together with ArkLib's existing equality polynomial and
[`MLE`](ArkLib/Data/MvPolynomial/Multilinear.lean) definitions.

The formalization is split into three ArkLib reductions.

* The outer LogUp phase sends the multiplicity oracle `m`, samples the challenge `x`, sends the
  helper oracles, and samples the batching challenge `(z, lambda)`. At the end of this phase, the
  verifier has the data needed to state a single zero-sum claim about the LogUp polynomial `Q`.
* The sumcheck phase turns the values retained from the outer phase into the polynomial `Q`, then
  runs ArkLib's generic sumcheck protocol on the claim that `Q` sums to zero. The translation tools
  and polynomial construction live in the
  [`Logup/Sumcheck`](ArkLib/ProofSystem/Logup/Sumcheck/) directory, with the bridge connecting the
  LogUp-specific data to the generic sumcheck input and output.
* The final zero-round phase queries the retained LogUp oracles at sumcheck's final point and checks
  that those oracle values really give the value claimed by sumcheck.

This file defines the transcript shapes; the prover-side objects for the outer, sumcheck,
final-check, and full protocol; the matching verifier-side objects; and then the oracle reductions
for each phase and for the composed protocol.

The main artefacts that define the protocol are `pSpec`, `logupProver`, `logupVerifier`,
and `logupOracleReduction`.

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

section FinalCheckSpec

/-- The final LogUp point check has no transcript messages; it only queries retained oracles. -/
@[reducible]
def finalCheckPSpec : ProtocolSpec 0 :=
  !p[]

end FinalCheckSpec

section FullProtocolSpec

open ProtocolSpec

/-- Protocol 2 before the final point check: outer LogUp followed by generic sumcheck. -/
@[reducible]
noncomputable def pSpecBeforeFinal (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :=
  outerPSpec F n params ++ₚ logupSumcheckPSpec F n M params

/-- Protocol 2 transcript shape: outer LogUp, ArkLib's generic sumcheck, and the final point check.
-/
@[reducible]
noncomputable def pSpec (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n M : ℕ) (params : ProtocolParams M) :=
  pSpecBeforeFinal F n M params ++ₚ finalCheckPSpec

/-- The prover messages before the final check are oracle-accessible: outer LogUp followed by the
embedded sumcheck messages. -/
noncomputable instance instPSpecBeforeFinalMessageOracleInterface
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, OracleInterface ((pSpecBeforeFinal F n M params).Message i) := by
  unfold pSpecBeforeFinal
  exact ProtocolSpec.instOracleInterfaceMessageAppend

/-- The full LogUp prover messages are oracle-accessible: outer LogUp and sumcheck messages; the
final point check has no messages. -/
noncomputable instance instPSpecMessageOracleInterface
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, OracleInterface ((pSpec F n M params).Message i) := by
  unfold pSpec
  exact ProtocolSpec.instOracleInterfaceMessageAppend

/-- The verifier challenges before the final check are sampleable: outer LogUp followed by the
embedded sumcheck challenges. -/
noncomputable instance instPSpecBeforeFinalChallengeSampleable
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((pSpecBeforeFinal F n M params).Challenge i) := by
  letI : Inhabited F := ⟨0⟩
  unfold pSpecBeforeFinal
  exact ProtocolSpec.instSampleableTypeChallengeAppend

/-- The full LogUp verifier challenges are sampleable: the final point check has no challenges. -/
noncomputable instance instPSpecChallengeSampleable
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n M : ℕ}
    {params : ProtocolParams M} :
    ∀ i, SampleableType ((pSpec F n M params).Challenge i) := by
  letI : Inhabited F := ⟨0⟩
  unfold pSpec
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

section ConcreteSumcheckReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- ArkLib's generic sumcheck prover specialized to LogUp's Boolean domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleProver [SampleableType F] :
    OracleProver oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (logupSumcheckPSpec F n M params) :=
  (Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params)
    (booleanDomain F) n oSpec).prover

/-- ArkLib's generic sumcheck verifier specialized to LogUp's Boolean domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleVerifier [SampleableType F] :
    OracleVerifier oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleVerifier F (logupSumcheckDegree M params)
    (booleanDomain F) n oSpec

/-- ArkLib's generic sumcheck reduction specialized to LogUp's Boolean domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleReduction [SampleableType F] :
    OracleReduction oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params)
    (booleanDomain F) n oSpec

end ConcreteSumcheckReduction

section SumcheckProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The prover for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckProver :
    OracleProver oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params) Unit
      (logupSumcheckPSpec F n M params) :=
  let lens :
      OracleContext.Lens.{0, 0, 0, 0}
        (StmtAfterOuter F n M params) (StmtAfterSumcheck F n M params)
        (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
        (OStmtAfterOuter F n M params) (OStmtAfterSumcheck F n M params)
        (LogupSumcheckOracleStatement F n M params)
        (LogupSumcheckOracleStatement F n M params)
        Unit Unit Unit Unit :=
    logupSumcheckContextLens F n M params
  (logupConcreteSumcheckOracleProver oSpec F n M params).liftContext lens

end SumcheckProver

section FinalCheckProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The prover for the final LogUp point check; there are no messages in this phase. -/
noncomputable def finalCheckProver :
    OracleProver oSpec (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params) Unit
      StmtOut OStmtOut Unit
      finalCheckPSpec where
  PrvState := fun _ => StmtAfterSumcheck F n M params ×
    (∀ i, OStmtAfterSumcheck F n M params i)
  input := fun ⟨ctx, _⟩ => ctx
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output := fun _ => pure ((((), fun i => Fin.elim0 i), ()))

end FinalCheckProver

section FullProver

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp prover, composed from the outer prover and embedded sumcheck prover. -/
noncomputable def logupProver :
    OracleProver oSpec (StmtIn F n M) (OStmtIn F n M) (WitIn F n M params)
      (StmtOut) (OStmtOut) Unit
      (pSpec F n M params) :=
  Prover.append
    (Prover.append (outerProver oSpec F n M params) (sumcheckProver oSpec F n M params))
    (finalCheckProver oSpec F n M params)

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
    -- Following Remark 3 of the LogUp paper, the verifier samples `x` uniformly and does not
    -- scan the table to reject poles. Pole challenges are treated as bad/failing inputs for the
    -- honest handoff, and `Completeness.lean` accounts for that event.
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
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The verifier for the embedded sumcheck phase of LogUp Protocol 2. -/
noncomputable def sumcheckVerifier [SampleableType F] :
    OracleVerifier oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params)
      (logupSumcheckPSpec F n M params) :=
  let lens :
      OracleContext.Lens.{0, 0, 0, 0}
        (StmtAfterOuter F n M params) (StmtAfterSumcheck F n M params)
        (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
        (OStmtAfterOuter F n M params) (OStmtAfterSumcheck F n M params)
        (LogupSumcheckOracleStatement F n M params)
        (LogupSumcheckOracleStatement F n M params)
        Unit Unit Unit Unit :=
    logupSumcheckContextLens F n M params
  (logupConcreteSumcheckOracleVerifier oSpec F n M params).liftContext lens.stmt

end SumcheckVerifier

section FinalCheckVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Query one retained LogUp oracle during the final point check. -/
private def finalCheckQuery
    (i : OuterOracleIdx M)
    (q : (instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Query) :
    OptionT
      (OracleComp (oSpec + ([OStmtAfterSumcheck F n M params]ₒ + [finalCheckPSpec.Message]ₒ)))
      ((instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Response q) :=
  OptionT.lift <| OracleComp.liftComp
    (OracleComp.lift <|
      OracleSpec.query (show [OStmtAfterSumcheck F n M params]ₒ.Domain from ⟨i, q⟩))
    _

/-- The verifier's final Protocol 2 check: reconstruct `Q(r)` from retained LogUp oracle
evaluations and compare it with the expected value output by sumcheck. -/
noncomputable def finalCheckVerifier :
    OracleVerifier oSpec (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params)
      StmtOut OStmtOut
      finalCheckPSpec where
  verify := fun stmt _ => do
    let r : Fin n → F := stmt.finalClaim.challenges
    let expectedValue : F := stmt.finalClaim.target
    let multiplicity ← finalCheckQuery oSpec F n M params .multiplicity r
    let table ← finalCheckQuery oSpec F n M params (.input .table) r
    let columnValues ← (Vector.finRange M).mapM
      (fun i => finalCheckQuery oSpec F n M params (.input (.column i)) r)
    let helperValues ← (Vector.finRange params.numGroups).mapM
      (fun k => finalCheckQuery oSpec F n M params .helpers ⟨k, r⟩)
    let evals : PointEvaluations F M params.numGroups :=
      { multiplicity := multiplicity
        table := table
        columns := fun i => columnValues[i]
        helpers := fun k => helperValues[k] }
    guard (qAtPoint (canonicalGroups params) stmt.outer.xChallenge stmt.outer.zChallenge r
      stmt.outer.batchingScalars evals = expectedValue)
    pure ()

  embed :=
    { toFun := fun i => Fin.elim0 i
      inj' := fun i => Fin.elim0 i }

  hEq := fun i => Fin.elim0 i

end FinalCheckVerifier

section FullVerifier

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The full LogUp verifier, obtained by composing the outer verifier with the embedded sumcheck
verifier and final point check. -/
noncomputable def logupVerifier :
    OracleVerifier oSpec (StmtIn F n M) (OStmtIn F n M)
      (StmtOut) (OStmtOut)
      (pSpec F n M params) :=
  OracleVerifier.append
    (OracleVerifier.append (outerVerifier oSpec F n M params)
      (sumcheckVerifier oSpec F n M params))
    (finalCheckVerifier oSpec F n M params)

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

section SumcheckReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The embedded LogUp sumcheck phase, obtained by lifting ArkLib's generic Sumcheck reduction
through the LogUp-to-Sumcheck context lens. -/
noncomputable def sumcheckOracleReduction :
    OracleReduction oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params) Unit
      (logupSumcheckPSpec F n M params) where
  prover := sumcheckProver oSpec F n M params
  verifier := sumcheckVerifier oSpec F n M params

end SumcheckReduction

section FinalCheckReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The final LogUp point check as an ArkLib oracle reduction. -/
noncomputable def finalCheckOracleReduction :
    OracleReduction oSpec (StmtAfterSumcheck F n M params) (OStmtAfterSumcheck F n M params) Unit
      (StmtOut) (OStmtOut) Unit
      finalCheckPSpec where
  prover := finalCheckProver oSpec F n M params
  verifier := finalCheckVerifier oSpec F n M params

end FinalCheckReduction

section FullReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n M : ℕ)
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
