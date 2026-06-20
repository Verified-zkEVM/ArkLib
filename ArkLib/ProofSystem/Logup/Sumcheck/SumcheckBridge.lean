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
  ∑ u : Hypercube n,
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

private theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : Hypercube n, f (fun j => D (u j)) := by
  let e : Hypercube n ↪ (Fin n → F) := Function.Embedding.arrowCongrRight D
  change (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
    ∑ u : Hypercube n, f (e u)
  rw [← Finset.sum_map]
  congr 1
  ext x
  constructor
  · intro hx
    rw [Fintype.mem_piFinset] at hx
    have hx_coord : ∀ j : Fin n, ∃ b : Fin 2, D b = x j := by
      intro j
      rcases Finset.mem_map.mp (hx j) with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    let u : Hypercube n := fun j => Classical.choose (hx_coord j)
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, by
      funext j
      exact Classical.choose_spec (hx_coord j)⟩
  · intro hx
    rw [Fintype.mem_piFinset]
    intro j
    rcases Finset.mem_map.mp hx with ⟨u, _, rfl⟩
    exact Finset.mem_map.mpr ⟨u j, Finset.mem_univ _, rfl⟩

/-- The initial generic Sumcheck relation induced by a LogUp outer transcript. -/
def logupSumcheckRelationInput
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ((logupInitialSumcheckStatement F n M params, logupSumcheckOracleStmt F n M params stmt oStmt),
      ()) ∈
    Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0

/-- If LogUp's outer algebra proves a zero sum, then the generic Sumcheck input relation is exactly
the claim sent to Sumcheck. -/
theorem logupSumcheckRelationInput_of_zero
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (hZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0) :
    logupSumcheckRelationInput F n M params stmt oStmt := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (booleanDomain F),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := booleanDomain F)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  calc
    (∑ u : Hypercube n,
        MvPolynomial.eval
          ((((fun j => (booleanDomain F) (u j)) ∘ Fin.cast (by omega)) ∘
              Fin.cast (by omega)))
          (logupSumcheckPolynomial F n M params stmt oStmt).val)
        =
      logupOuterSumcheckClaim F n M params stmt oStmt := by
        rw [logupOuterSumcheckClaim]
        apply Finset.sum_congr rfl
        intro u _
        simpa [booleanDomain, logupSumcheckPolynomial] using
          logupQPolynomial_eval_hypercube F n M params stmt oStmt u
    _ = 0 := hZero

/-- The obligations needed to replace the current abstract embedded sumcheck by ArkLib's generic
sumcheck plus LogUp's final oracle-query check. -/
structure LogupSumcheckBridge
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) where
  claimZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0
  finalEval :
    ∀ (r : Fin n → F) (evals : PointEvaluations F M params.numGroups),
      logupPointEvaluationsAgree (F := F) (n := n) (M := M) params r oStmt evals →
        MvPolynomial.eval r (logupSumcheckPolynomial F n M params stmt oStmt).1 =
          qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
            stmt.batchingScalars evals


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
