import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# LogUp Sumcheck Bridge

Bridge from the LogUp outer transcript to ArkLib's generic sumcheck reduction, for Protocol 2 of
Haböck's LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The outer phase produces an `x` challenge, batching data `(z, lambda)`, the original input oracles,
the honest multiplicity oracle, and helper oracles. From these data, `SumcheckPolynomial.lean`
constructs the LogUp polynomial `Q`. This file packages `Q` as the single bounded-degree oracle
statement expected by `Sumcheck.Spec`, states the zero-sum relation that starts the embedded
sumcheck, and defines the context lens/reduction that runs generic sumcheck after the outer phase.

The main bridge predicates are:

* `logupMidRelation`, the handoff relation from outer LogUp into sumcheck;
* `logupSumcheckRelationInput`, the corresponding generic sumcheck initial relation; and
* `logupOutputRelationFromSumcheck`, the final LogUp check after sumcheck.
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

/-- The row-wise claim that `logupQPolynomial` agrees with `qOnHypercube` on `H`. -/
def logupSumcheckPolynomialRowsAgree
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ∀ u : Hypercube n,
    MvPolynomial.eval (signPoint F u) (logupSumcheckPolynomial F n M params stmt oStmt).1 =
      qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
        (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u

/-- The LogUp zero-sum claim that is fed to the generic sumcheck. -/
noncomputable def logupOuterSumcheckClaim
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
      (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u

/-- Relation handed from the outer LogUp phase to the embedded sumcheck: the polynomial bridge
agrees on the hypercube and the outer algebra produced a genuine zero-sum claim. -/
def logupMidRelation :
    Set ((StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) :=
  { x | logupSumcheckPolynomialRowsAgree F n M params x.1.1 x.1.2 ∧
        logupOuterSumcheckClaim F n M params x.1.1 x.1.2 = 0 }

/-- Semantic agreement between final oracle-query answers and the retained LogUp oracles. -/
def logupPointEvaluationsAgree
    (r : Fin n → F)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (evals : PointEvaluations F M params.numGroups) : Prop :=
  evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r ∧
    evals.table = lagrangeOracleEval (oStmt (.input .table)) r ∧
    (∀ i : Fin M, evals.columns i = lagrangeOracleEval (oStmt (.input (.column i))) r) ∧
      ∀ k : Fin params.numGroups, evals.helpers k = lagrangeOracleEval ((oStmt .helpers) k) r

end SumcheckInterface

section SumcheckBridge

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The `{±1}` sumcheck domain, packaged in the form expected by `Sumcheck.Spec`. -/
def signDomain (hSigns : (-1 : F) ≠ 1) : Fin 2 ↪ F where
  toFun := bitToSign F
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h hSigns
    · exact absurd h.symm hSigns
    · rfl

private theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : Hypercube n, f (fun j => D (u j)) := by
  classical
  symm
  refine Finset.sum_nbij (s := (Finset.univ : Finset (Hypercube n)))
    (t := Fintype.piFinset fun _ : Fin n => Finset.univ.map D)
    (i := fun u j => D (u j)) ?hi ?hinj ?hsurj ?hfg
  · intro u _
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_map.mpr ⟨u j, Finset.mem_univ _, rfl⟩
  · intro u _ v _ huv
    funext j
    exact D.injective (congr_fun huv j)
  · intro x hx
    have hx_coord : ∀ j : Fin n, ∃ b : Fin 2, D b = x j := by
      intro j
      have hxj := (Fintype.mem_piFinset.mp hx) j
      rcases Finset.mem_map.mp hxj with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    let u : Hypercube n := fun j => Classical.choose (hx_coord j)
    refine ⟨u, Finset.mem_univ _, ?_⟩
    funext j
    exact Classical.choose_spec (hx_coord j)
  · intro u _
    rfl


/-- The initial generic Sumcheck relation induced by a LogUp outer transcript. -/
def logupSumcheckRelationInput (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ((logupInitialSumcheckStatement F n M params, logupSumcheckOracleStmt F n M params stmt oStmt),
      ()) ∈
    Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F hSigns) 0

/-- If the polynomial bridge agrees on the hypercube and LogUp's outer algebra proves a zero sum,
then the generic Sumcheck input relation is exactly the claim sent to Sumcheck. -/
theorem logupSumcheckRelationInput_of_rowsAgree
    {hSigns : (-1 : F) ≠ 1}
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (hRows : logupSumcheckPolynomialRowsAgree F n M params stmt oStmt)
    (hZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0) :
    logupSumcheckRelationInput F n M params hSigns stmt oStmt := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (signDomain F hSigns),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := signDomain F hSigns)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  calc
    (∑ u : Hypercube n,
        MvPolynomial.eval
          ((((fun j => (signDomain F hSigns) (u j)) ∘ Fin.cast (by omega)) ∘
              Fin.cast (by omega)))
          (logupSumcheckPolynomial F n M params stmt oStmt).val)
        =
      logupOuterSumcheckClaim F n M params stmt oStmt := by
        rw [logupOuterSumcheckClaim]
        apply Finset.sum_congr rfl
        intro u _
        simpa [signDomain, signPoint] using hRows u
    _ = 0 := hZero

/-- The obligations needed to replace the current abstract embedded sumcheck by ArkLib's generic
sumcheck plus LogUp's final oracle-query check. -/
structure LogupSumcheckBridge
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) where
  rowsAgree : logupSumcheckPolynomialRowsAgree F n M params stmt oStmt
  claimZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0
  finalEval :
    ∀ (r : Fin n → F) (evals : PointEvaluations F M params.numGroups),
      logupPointEvaluationsAgree F n M params r oStmt evals →
        MvPolynomial.eval r (logupSumcheckPolynomial F n M params stmt oStmt).1 =
          qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
            stmt.batchingScalars evals


end SumcheckBridge

section ConcreteSumcheckReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The existing generic Sumcheck oracle verifier specialized to LogUp's domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleVerifier [SampleableType F]
    (hSigns : (-1 : F) ≠ 1) :
    OracleVerifier oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleVerifier F (logupSumcheckDegree M params)
    (signDomain F hSigns) n oSpec

/-- The existing generic Sumcheck oracle reduction specialized to LogUp's domain and degree
bound. -/
noncomputable def logupConcreteSumcheckOracleReduction [SampleableType F]
    (hSigns : (-1 : F) ≠ 1) :
    OracleReduction oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params)
    (signDomain F hSigns) n oSpec

end ConcreteSumcheckReduction

section SumcheckLift

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Context lens from LogUp's retained outer state to ArkLib's generic Sumcheck state.

The projection builds the generic zero-sum claim and its single polynomial oracle. The lift drops
the generic Sumcheck output because the top-level LogUp protocol returns only success/failure.
-/
noncomputable def logupSumcheckContextLens :
    OracleContext.Lens
      (StmtAfterOuter F n M params) StmtOut
      (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
      (OStmtAfterOuter F n M params) OStmtOut
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckOracleStatement F n M params)
      Unit Unit Unit Unit where
  stmt :=
    ⟨fun ctx =>
        (logupInitialSumcheckStatement F n M params,
          logupSumcheckOracleStmt F n M params ctx.1 ctx.2),
      fun _ _ => ((), fun i => Fin.elim0 i)⟩
  wit :=
    ⟨fun _ => (),
      fun _ _ => ()⟩

/-- The embedded LogUp sumcheck phase, obtained by lifting ArkLib's generic Sumcheck reduction
through the LogUp-to-Sumcheck context lens. -/
noncomputable def sumcheckOracleReduction [SampleableType F] :
    OracleReduction oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtOut) (OStmtOut) Unit
      (logupSumcheckPSpec F n M params) :=
  let lens :
      OracleContext.Lens.{0, 0, 0, 0}
        (StmtAfterOuter F n M params) StmtOut
        (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
        (OStmtAfterOuter F n M params) OStmtOut
        (LogupSumcheckOracleStatement F n M params)
        (LogupSumcheckOracleStatement F n M params)
        Unit Unit Unit Unit :=
    logupSumcheckContextLens F n M params
  (logupConcreteSumcheckOracleReduction oSpec F n M params
      (Fact.out : (-1 : F) ≠ 1)).liftContext
    lens

end SumcheckLift

end Logup
