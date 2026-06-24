import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# LogUp Sumcheck Bridge

Adapter between LogUp's outer phase and ArkLib's generic sumcheck protocol, for Protocol 2 of
Haböck's LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The outer phase leaves LogUp-specific data: challenges, input oracles, the multiplicity oracle, and
helper oracles. `SumcheckPolynomial.lean` builds the polynomial `Q` from that data. This file
packages `Q` as the single polynomial oracle expected by `Sumcheck.Spec` and states the zero-sum
claim that starts the sumcheck phase.

The main artefact is `logupSumcheckContextLens`. It takes the output of the outer LogUp phase and presents it to generic sumcheck as
that zero-sum claim for `Q`. When sumcheck finishes, the lens packages the final sumcheck point and
claimed value back together with the retained LogUp data, so the final LogUp verifier can query the
original oracles and check the claim.

The supporting definitions here describe the sumcheck transcript shape, the packaged `Q` oracle, and
the relations used to state that this translation is correct.
-/

namespace Logup

open scoped BigOperators

section SumcheckInterface

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Individual-degree bound for LogUp's embedded sumcheck polynomial. -/
def logupSumcheckDegree (_params : ProtocolParams M) : ℕ :=
  M + 3

/-- The concrete ArkLib Sumcheck transcript shape for LogUp's embedded sumcheck. -/
abbrev logupSumcheckPSpec : ProtocolSpec (Fin.vsum (fun _ : Fin n => 2)) :=
  Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n

/-- The generic sumcheck input statement used by LogUp: target `0`, no prior challenges. -/
abbrev LogupSumcheckStmtIn (_params : ProtocolParams M) : Type :=
  Sumcheck.Spec.StatementRound F n 0

/-- The generic sumcheck output statement: the final claim at verifier point `r`. -/
abbrev LogupSumcheckStmtOut (_params : ProtocolParams M) : Type :=
  Sumcheck.Spec.StatementRound F n (.last n)

/-- LogUp state after the embedded sumcheck, before the final oracle-query check. -/
structure StmtAfterSumcheck where
  /-- The outer transcript data retained for reconstructing `Q(r)`. -/
  outer : StmtAfterOuter F n M params
  /-- Sumcheck's final point claim `Q(r) = v`. -/
  finalClaim : LogupSumcheckStmtOut F n M params

/-- Oracle statements retained after sumcheck for the final LogUp point check. -/
abbrev OStmtAfterSumcheck : OuterOracleIdx M → Type :=
  OStmtAfterOuter F n M params

/-- The generic sumcheck oracle statement: LogUp's bounded-degree `Q` polynomial. -/
abbrev LogupSumcheckOracleStatement : Unit → Type :=
  Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params)

/-- LogUp enters the embedded sumcheck with the zero-sum claim. -/
def logupInitialSumcheckStatement : LogupSumcheckStmtIn F n M params where
  target := 0
  challenges := fun i => Fin.elim0 i

/-- Package `logupQPolynomial` with its degree certificate into ArkLib's oracle statement type. -/
noncomputable def logupSumcheckPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    LogupSumcheckOracleStatement F n M params () := by
  classical
  exact ⟨logupQPolynomial F n M params stmt oStmt, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact logupQPolynomial_degreeOf F n M params stmt oStmt i⟩

/-- Package the LogUp `Q` polynomial as the single oracle statement expected by Sumcheck. -/
noncomputable def logupSumcheckOracleStmt
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    ∀ i, LogupSumcheckOracleStatement F n M params i :=
  fun _ => logupSumcheckPolynomial F n M params stmt oStmt

/-- The LogUp zero-sum claim that is fed to the generic sumcheck. -/
noncomputable def logupOuterSumcheckClaim
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : F :=
  ∑ u : (Fin n → Fin 2),
    qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
      (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u

/-- Relation handed from the outer LogUp phase to the embedded sumcheck: the outer algebra produced
a genuine zero-sum claim. -/
def logupMidRelation :
    Set ((StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) :=
  { x | logupOuterSumcheckClaim F n M params x.1.1 x.1.2 = 0 }

end SumcheckInterface

section SumcheckBridge

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The Boolean sumcheck domain, packaged in the form expected by `Sumcheck.Spec`. -/
def booleanDomain : Fin 2 ↪ F where
  toFun := fun b => (b : F)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · simp at h
    · simp at h
    · rfl

/-- Relation after embedded sumcheck: the final sumcheck point claim is valid for the retained
LogUp polynomial. The final LogUp phase consumes this by querying the retained oracles at that
point and recomputing `Q(r)`. -/
def logupAfterSumcheckRelation :
    Set ((StmtAfterSumcheck F n M params × (∀ i, OStmtAfterSumcheck F n M params i)) × Unit) :=
  { x |
    ((x.1.1.finalClaim,
        logupSumcheckOracleStmt F n M params x.1.1.outer x.1.2), ()) ∈
      Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n) }

/-- The initial generic Sumcheck relation induced by a LogUp outer transcript. -/
def logupSumcheckRelationInput
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ((logupInitialSumcheckStatement F n M params, logupSumcheckOracleStmt F n M params stmt oStmt),
      ()) ∈
    Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0

end SumcheckBridge

section SumcheckLift

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Context lens from LogUp's retained outer state to ArkLib's generic Sumcheck state.

The projection builds the generic zero-sum claim and its single polynomial oracle. The lift keeps
the outer LogUp data and retained oracles together with Sumcheck's final point claim, so the next
LogUp phase can perform the paper's final oracle-query check.
-/
noncomputable def logupSumcheckContextLens :
    OracleContext.Lens
      (StmtAfterOuter F n M params) (StmtAfterSumcheck F n M params)
      (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
      (OStmtAfterOuter F n M params) (OStmtAfterSumcheck F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckOracleStatement F n M params)
      Unit Unit Unit Unit where
  stmt :=
    ⟨fun ctx =>
        (logupInitialSumcheckStatement F n M params,
          logupSumcheckOracleStmt F n M params ctx.1 ctx.2),
      fun ctx inner =>
        ({ outer := ctx.1, finalClaim := inner.1 }, ctx.2)⟩
  wit :=
    ⟨fun _ => (),
      fun _ _ => ()⟩

end SumcheckLift

end Logup
