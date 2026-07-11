/- 
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Oracle
import ArkLib.Interaction.Oracle.Continuation
import PolyFun.Interaction.TwoParty.Strategy

/-!
# Interaction-Native Sum-Check: Single Round

A single round of sum-check, expressed canonically as an oracle continuation /
oracle reduction over the **original** polynomial oracle.

The round is indexed by a prefix transcript of already-sampled verifier
challenges. From that prefix, the prover derives the current residual
polynomial, sends the corresponding univariate round polynomial, receives the
next challenge, and keeps the original oracle statement unchanged.
-/

namespace Sumcheck

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Advance a residual polynomial by fixing its first variable to the sampled
challenge. This is the stateful prover update for one sum-check round. -/
def stepResidual (chal : R)
    {numVars : ℕ} (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    Sumcheck.PolyStmt R deg numVars :=
  ⟨CMvPolynomial.partialEvalFirst chal poly.1,
    CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly.1 poly.2⟩

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
private def currentResidualGo :
    (prefixLen : Nat) →
    {n : Nat} →
    (h : prefixLen ≤ n) →
    (vals : Fin prefixLen → R) →
    (poly : Sumcheck.PolyStmt R deg n) →
    Sumcheck.PolyStmt R deg (n - prefixLen)
  | 0, n, _, _, poly => by
      simpa using poly
  | prefixLen + 1, 0, h, _, _ => by
      exact False.elim (Nat.not_succ_le_zero _ h)
  | prefixLen + 1, n + 1, h, vals, poly => by
      simpa using
        currentResidualGo
          prefixLen
          (n := n)
          (Nat.le_of_succ_le_succ h)
          (fun i => vals i.succ)
          (stepResidual (R := R) (deg := deg) (vals 0) poly)
termination_by currentResidualGo prefixLen _ _ _ => prefixLen
decreasing_by simp_wf

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
def currentResidual {n prefixLen : Nat} (h : prefixLen ≤ n)
    (vals : Fin prefixLen → R)
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg (n - prefixLen) :=
  currentResidualGo (R := R) (deg := deg) prefixLen h vals poly

/-- The active residual for the round after a prefix of length `prefixLen`. This
is the residual polynomial in `((n - (prefixLen + 1)) + 1)` variables whose
round polynomial will be sent next. -/
def currentRoundResidual {n prefixLen : Nat} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg ((n - (prefixLen + 1)) + 1) := by
  let residual :=
    currentResidual (R := R) (deg := deg) (n := n) (prefixLen := prefixLen)
      (Nat.le_of_lt h)
      (Sumcheck.challengePrefix R deg prefixLen prefixTr)
      poly
  have hk : n - prefixLen = (n - (prefixLen + 1)) + 1 := by
    omega
  simpa [hk] using residual

/-- The honest round polynomial computed from the current active residual. -/
def honestRoundPoly {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D numVars poly.1,
    CMvPolynomial.roundPoly_natDegree_le D poly.1 (fun mono hmono =>
      poly.2 ⟨0, by omega⟩ mono hmono)⟩

/-- The honest round polynomial sent after the prefix transcript `prefixTr`. -/
def honestRoundPolyAtPrefix {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    CDegreeLE R deg :=
  honestRoundPoly (R := R) (deg := deg) D <|
    currentRoundResidual (R := R) (deg := deg) h prefixTr poly

/-- The honest prover step for one round, specialized to the original
polynomial and the already-recorded challenge prefix. -/
def roundProverStep (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    Spec.Strategy.withRoles m (roundSpec R deg) (roundRoles R deg)
      (fun _ => NextState) :=
  let sentPoly := honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

/-- The honest prover step for one round, specialized to a private residual
polynomial witness that is threaded across rounds. -/
def roundProverStepStateful (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1))
    (computeNext : R → NextState) :
    Spec.Strategy.withRoles m (roundSpec R deg) (roundRoles R deg)
      (fun _ => NextState) :=
  let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

@[simp]
theorem roundProverStep_map_fst
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {NextState NextWitness : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState)
    (computeWit : R → NextWitness) :
    Spec.Strategy.mapOutputWithRoles (fun _ out => out.1)
      (roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly
        (fun chal => (computeNext chal, computeWit chal))) =
      roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly computeNext := by
  simp [roundProverStep, roundSpec, roundRoles, Spec.Strategy.mapOutputWithRoles]
  congr
  funext chal
  change Functor.map (fun (x : NextState × NextWitness) => x.1)
      (pure (computeNext chal, computeWit chal) : m (NextState × NextWitness)) =
    (pure (computeNext chal) : m NextState)
  simpa using
    (map_pure (g := fun (x : NextState × NextWitness) => x.1)
      (x := (computeNext chal, computeWit chal)))

@[simp]
theorem roundProverStep_map_residualWitness
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    Spec.Strategy.mapOutputWithRoles
      (fun tr (out : NextState) =>
        ((out, stepResidual (R := R) (deg := deg)
          (Sumcheck.roundChallenge R deg tr)
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)) :
          NextState × Sumcheck.PolyStmt R deg (n - (prefixLen + 1))))
      (roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly computeNext) =
      roundProverStepStateful (m := m) (R := R) (deg := deg) D
        (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)
        (fun chal : R =>
          ((computeNext chal,
            stepResidual (R := R) (deg := deg) chal
              (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)) :
            NextState × Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))) := by
  simp [roundProverStep, roundProverStepStateful, roundSpec, roundRoles,
    honestRoundPolyAtPrefix, Spec.Strategy.mapOutputWithRoles]
  congr
  funext chal
  change Functor.map
      (fun (next : NextState) =>
        (next, stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)))
      (pure (computeNext chal) : m NextState) =
    (pure
      (computeNext chal,
        stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)) :
      m (NextState × Sumcheck.PolyStmt R deg (n - (prefixLen + 1))))
  simpa using
    (map_pure
      (g := fun (next : NextState) =>
        (next, stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)))
      (x := computeNext chal))

@[simp]
theorem roundProverStep_map_honestProverOutputWitness
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {NextStmt : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → HonestProverOutput NextStmt PUnit) :
    Spec.Strategy.mapOutputWithRoles
      (fun tr (out : HonestProverOutput NextStmt PUnit) =>
        ((⟨out.stmt,
          stepResidual (R := R) (deg := deg)
            (Sumcheck.roundChallenge R deg tr)
            (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)⟩) :
          HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))))
      (roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly computeNext) =
      roundProverStepStateful (m := m) (R := R) (deg := deg) D
        (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)
        (fun chal : R =>
          (⟨(computeNext chal).stmt,
            stepResidual (R := R) (deg := deg) chal
              (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)⟩ :
            HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1))))) := by
  simp [roundProverStep, roundProverStepStateful, roundSpec, roundRoles,
    honestRoundPolyAtPrefix, Spec.Strategy.mapOutputWithRoles]
  congr
  funext chal
  change Functor.map
      (fun (out : HonestProverOutput NextStmt PUnit) =>
        (⟨out.stmt, stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)⟩ :
        HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))))
      (pure (computeNext chal) : m (HonestProverOutput NextStmt PUnit)) =
    (pure
      (⟨(computeNext chal).stmt,
        stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)⟩ :
      HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))) :
      m (HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))))
  simpa using
    (map_pure
      (g := fun (out : HonestProverOutput NextStmt PUnit) =>
        (⟨out.stmt, stepResidual (R := R) (deg := deg) chal
          (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)⟩ :
        HonestProverOutput NextStmt (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))))
      (x := computeNext chal))

@[simp]
theorem roundProverStepStateful_fromResidual
    {m : Type → Type} [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    roundProverStepStateful (m := m) (R := R) (deg := deg) D
      (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)
      computeNext =
      roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly computeNext := by
  rfl

/-- Oracle continuation for one live sum-check round after a prefix transcript
of previously sampled challenges. The original polynomial oracle is preserved
unchanged. -/
noncomputable def roundContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let poly := sWithOracles.oracleStmt ()
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D h prefixTr poly
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            some <|
              CPolynomial.eval chal
                (honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly).1
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStep
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg n) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| ([Sumcheck.PolyFamily R deg n]ₒ).query q

/-- Oracle continuation for one live sum-check round with a private residual
polynomial witness. The public oracle statement remains the original polynomial,
but the honest prover updates its residual state incrementally instead of
recomputing it from the prefix transcript. -/
noncomputable def roundContinuationStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {totalVars : ℕ} (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover _ sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) := some (CPolynomial.eval chal sentPoly.1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, stepResidual (R := R) (deg := deg) chal witness⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStep
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg totalVars) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| ([Sumcheck.PolyFamily R deg totalVars]ₒ).query q

/-- Oracle continuation for one chained sum-check round after a possibly-failed
claim. The original polynomial oracle is preserved unchanged. -/
noncomputable def roundContinuationOption
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let poly := sWithOracles.oracleStmt ()
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D h prefixTr poly
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            match sWithOracles.stmt with
            | none => none
            | some _ =>
                some (CPolynomial.eval chal
                  (honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly).1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStepOption
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg n) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| ([Sumcheck.PolyFamily R deg n]ₒ).query q

/-- Oracle continuation for one chained sum-check round with a private residual
polynomial witness. After a prior rejection, the witness still advances
syntactically, but the public claim remains `none`. -/
noncomputable def roundContinuationOptionStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {totalVars : ℕ} (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg totalVars)
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover _ sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            match sWithOracles.stmt with
            | none => none
            | some _ => some (CPolynomial.eval chal sentPoly.1)
          ⟨⟨nextClaim, sWithOracles.oracleStmt⟩, stepResidual (R := R) (deg := deg) chal witness⟩)
  verifier _ {_} accSpec target := by
    simpa using
      oracleVerifierStepOption
        (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg totalVars) accSpec D target sampleChallenge
  simulate _ _ := fun q => by
    exact liftM <| ([Sumcheck.PolyFamily R deg totalVars]ₒ).query q

theorem roundContinuation_publicEq_stateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R)
    (sWithOracles :
      StatementWithOracles
        (fun _ => RoundClaim R) (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit) :
    (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
      (roundContinuationStateful (R := R) (deg := deg) D
        (totalVars := n)
        (n - (prefixLen + 1))
        sampleChallenge).prover PUnit.unit sWithOracles
          (currentRoundResidual (R := R) (deg := deg) h prefixTr (sWithOracles.oracleStmt ())) =
      (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
        (roundContinuation (R := R) (deg := deg) D h prefixTr sampleChallenge).prover
          PUnit.unit sWithOracles PUnit.unit := by
  simp [roundContinuation, roundContinuationStateful, roundProverStepStateful_fromResidual,
    roundProverStep_map_fst, honestRoundPolyAtPrefix]

/-- The chained single-round prover agrees with its stateful residual-witness
variant after transporting the private witness component to the one-step
residual update. -/
theorem roundContinuationOption_proverEq_stateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (sampleChallenge : OracleComp oSpec R)
    (sWithOracles :
      StatementWithOracles (fun _ => Option (RoundClaim R))
        (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit) :
    (Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        ⟨out.stmt,
          stepResidual (R := R) (deg := deg)
            (Sumcheck.roundChallenge R deg tr)
            (currentRoundResidual (R := R) (deg := deg) h prefixTr
              (sWithOracles.oracleStmt ()))⟩) ·) <$>
      (roundContinuationOption (R := R) (deg := deg) D h prefixTr sampleChallenge).prover
        PUnit.unit sWithOracles PUnit.unit =
      (roundContinuationOptionStateful (R := R) (deg := deg) D
        (totalVars := n) (n - (prefixLen + 1)) sampleChallenge).prover
        PUnit.unit sWithOracles
          (currentRoundResidual (R := R) (deg := deg) h prefixTr
            (sWithOracles.oracleStmt ())) := by
  simpa only [roundContinuationOption, roundContinuationOptionStateful,
    honestRoundPolyAtPrefix] using
    congrArg
      (fun x =>
        (pure x :
          OracleComp oSpec
            (Spec.Strategy.withRoles (OracleComp oSpec) (roundSpec R deg) (roundRoles R deg)
              (fun _ =>
                HonestProverOutput
                  (StatementWithOracles (fun _ => Option (RoundClaim R))
                    (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit)
                  (Sumcheck.PolyStmt R deg (n - (prefixLen + 1)))))))
      <|
      (roundProverStep_map_honestProverOutputWitness
        (m := OracleComp oSpec) (R := R) (deg := deg) D h prefixTr
        (sWithOracles.oracleStmt ())
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            match sWithOracles.stmt with
            | none => none
            | some _ =>
                some <|
                  CPolynomial.eval chal
                    (honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr
                      (sWithOracles.oracleStmt ())).1
          (⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩ :
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit)
              PUnit)))

/-- A single-round sum-check oracle reduction. The input oracle statement is the
original polynomial in `numVars + 1` variables, and it is preserved unchanged
as the output oracle statement. -/
noncomputable def roundOracleReduction
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => PUnit) :=
  let prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
    simpa [Sumcheck.fullSpec] using (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
  (roundContinuation (R := R) (deg := deg) D
    (n := numVars + 1)
    (prefixLen := 0)
    (Nat.succ_pos numVars)
    prefixTr
    sampleChallenge).promoteStatementToShared PUnit.unit

/-- A single-round sum-check oracle reduction with a private residual
polynomial witness. The public oracle statement stays fixed as the original
polynomial, while the witness shrinks from `numVars + 1` variables to `numVars`
after the sampled challenge. -/
noncomputable def roundOracleReductionStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDecoration R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) :=
  (roundContinuationStateful (R := R) (deg := deg) D
    (totalVars := numVars + 1) numVars sampleChallenge).promoteStatementToShared PUnit.unit

theorem roundOracleReduction_executePublic_eq_stateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R)
    (claim : RoundClaim R)
    (s :
      StatementWithOracles (fun _ => PUnit)
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim) :
    Interaction.OracleDecoration.OracleReduction.executePublicConcrete
      (roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
      claim s PUnit.unit =
    Interaction.OracleDecoration.OracleReduction.executePublicConcrete
      (roundOracleReductionStateful (R := R) (deg := deg) D numVars sampleChallenge)
      claim s (s.oracleStmt ()) := by
  let prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
    simpa [Sumcheck.fullSpec] using
      (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
  let sCont :
      StatementWithOracles (fun _ => RoundClaim R)
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit :=
    ⟨claim, s.oracleStmt⟩
  have hResidual :
      currentRoundResidual (R := R) (deg := deg)
        (n := numVars + 1) (prefixLen := 0)
        (Nat.succ_pos numVars) prefixTr (s.oracleStmt ()) =
      s.oracleStmt () := by
    simp [currentRoundResidual, currentResidual, currentResidualGo, prefixTr]
  have hStrategyCont :
      (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
        (roundContinuationStateful (R := R) (deg := deg) D
          (totalVars := numVars + 1) numVars sampleChallenge).prover
          PUnit.unit sCont (s.oracleStmt ()) =
      (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
        (roundContinuation (R := R) (deg := deg) D
          (n := numVars + 1) (prefixLen := 0)
          (Nat.succ_pos numVars) prefixTr sampleChallenge).prover
          PUnit.unit sCont PUnit.unit := by
    simpa [hResidual, sCont] using
        (roundContinuation_publicEq_stateful
        (R := R) (deg := deg) D
        (n := numVars + 1) (prefixLen := 0)
        (Nat.succ_pos numVars) prefixTr sampleChallenge sCont)
  let liftStmt :
      (tr : Spec.Transcript (roundSpec R deg)) →
      StatementWithOracles (fun _ => Option (RoundClaim R))
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit →
      StatementWithOracles (fun _ => Option (RoundClaim R))
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim
    | _, stmtOut => ⟨stmtOut.stmt, stmtOut.oracleStmt⟩
  have hStrategy :
      (Spec.Strategy.mapOutputWithRoles liftStmt ·) <$>
        ((Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
          (roundContinuation (R := R) (deg := deg) D
            (n := numVars + 1) (prefixLen := 0)
            (Nat.succ_pos numVars) prefixTr sampleChallenge).prover
            PUnit.unit sCont PUnit.unit) =
      (Spec.Strategy.mapOutputWithRoles liftStmt ·) <$>
        ((Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
          (roundContinuationStateful (R := R) (deg := deg) D
            (totalVars := numVars + 1) numVars sampleChallenge).prover
            PUnit.unit sCont (s.oracleStmt ())) := by
    exact congrArg (Functor.map (Spec.Strategy.mapOutputWithRoles liftStmt)) hStrategyCont.symm
  let pack :
      ((tr : Spec.Transcript (roundSpec R deg)) ×
        StatementWithOracles (fun _ => Option (RoundClaim R))
          (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim ×
        Option (RoundClaim R)) →
      ((tr : Spec.Transcript (roundSpec R deg)) ×
        StatementWithOracles (fun _ => Option (RoundClaim R))
          (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim ×
        (Option (RoundClaim R) ×
          QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
            (OracleComp
              ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                Interaction.OracleDecoration.toOracleSpec
                  (roundSpec R deg) (roundRoles R deg)
                  (roundOracleDecoration R deg) tr)))) :=
    fun a =>
      ⟨a.1, a.2.1, ⟨a.2.2,
        (roundContinuation (R := R) (deg := deg) D
          (n := numVars + 1) (prefixLen := 0)
          (Nat.succ_pos numVars) prefixTr sampleChallenge).simulate PUnit.unit a.1⟩⟩
  let k :=
    fun strategy =>
      pack <$>
        runWithOracleCounterpart
          (OracleInterface.simOracle0 (Sumcheck.PolyFamily R deg (numVars + 1)) s.oracleStmt)
          (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
          []ₒ (fun q => PEmpty.elim q)
          strategy
          ((roundContinuation (R := R) (deg := deg) D
            (n := numVars + 1) (prefixLen := 0)
            (Nat.succ_pos numVars) prefixTr sampleChallenge).verifier PUnit.unit []ₒ claim)
  let runTop :=
    fun stratM =>
      (do
        let strategy ← stratM
        k strategy :
        OracleComp oSpec
          ((tr : Spec.Transcript (roundSpec R deg)) ×
            StatementWithOracles (fun _ => Option (RoundClaim R))
              (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim ×
            (Option (RoundClaim R) ×
              QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
                (OracleComp
                  ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                    Interaction.OracleDecoration.toOracleSpec
                      (roundSpec R deg) (roundRoles R deg)
                      (roundOracleDecoration R deg) tr)))))
  have hRun : runTop
      ((Spec.Strategy.mapOutputWithRoles liftStmt ·) <$>
        ((Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
          (roundContinuation (R := R) (deg := deg) D
            (n := numVars + 1) (prefixLen := 0)
            (Nat.succ_pos numVars) prefixTr sampleChallenge).prover
            PUnit.unit sCont PUnit.unit)) =
    runTop
      ((Spec.Strategy.mapOutputWithRoles liftStmt ·) <$>
        ((Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) ·) <$>
          (roundContinuationStateful (R := R) (deg := deg) D
            (totalVars := numVars + 1) numVars sampleChallenge).prover
            PUnit.unit sCont (s.oracleStmt ()))) :=
    congrArg runTop hStrategy
  simpa [runTop, Interaction.OracleDecoration.OracleReduction.executePublicConcrete,
    roundOracleReduction, roundOracleReductionStateful,
    Interaction.OracleDecoration.OracleReduction.promoteStatementToShared,
    sCont, liftStmt, pack, k] using hRun

theorem roundOracleReduction_execute_eq_stateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R)
    (claim : RoundClaim R)
    (s :
      StatementWithOracles (fun _ => PUnit)
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim) :
    OracleReduction.mapExecuteWitness
      (oSpec := oSpec)
      (Context := fun _ => roundSpec R deg)
      (Roles := fun _ => roundRoles R deg)
      (oracleDeco := fun _ => roundOracleDecoration R deg)
      (LocalStmt := fun _ => PUnit)
      (StatementOut := fun _ _ => Option (RoundClaim R))
      (OStmtOut := fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (WitnessOut₁ := fun _ _ => PUnit)
      (WitnessOut₂ := fun _ _ => Sumcheck.PolyStmt R deg numVars)
      claim
      s
      (fun tr _ =>
        stepResidual (R := R) (deg := deg)
          (Sumcheck.roundChallenge R deg tr)
          (s.oracleStmt ())) <$>
      OracleReduction.executeConcrete
        (roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
        claim s PUnit.unit =
    OracleReduction.executeConcrete
      (roundOracleReductionStateful (R := R) (deg := deg) D numVars sampleChallenge)
      claim s (s.oracleStmt ()) := by
  let prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
    simpa [Sumcheck.fullSpec] using
      (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
  let sCont :
      StatementWithOracles (fun _ => RoundClaim R)
        (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit :=
    ⟨claim, s.oracleStmt⟩
  have hResidual :
      currentRoundResidual (R := R) (deg := deg)
        (n := numVars + 1) (prefixLen := 0)
        (Nat.succ_pos numVars) prefixTr (s.oracleStmt ()) =
      s.oracleStmt () := by
    simp [currentRoundResidual, currentResidual, currentResidualGo, prefixTr]
  have hStrategyCont :
      (Spec.Strategy.mapOutputWithRoles
        (fun tr out =>
          ⟨out.stmt,
            stepResidual (R := R) (deg := deg)
              (Sumcheck.roundChallenge R deg tr)
              (s.oracleStmt ())⟩) ·) <$>
        (roundContinuation (R := R) (deg := deg) D
          (n := numVars + 1) (prefixLen := 0)
          (Nat.succ_pos numVars) prefixTr sampleChallenge).prover
          PUnit.unit sCont PUnit.unit =
        (roundContinuationStateful (R := R) (deg := deg) D
        (totalVars := numVars + 1) numVars sampleChallenge).prover
          PUnit.unit sCont (s.oracleStmt ()) := by
    simpa [roundContinuation, roundContinuationStateful, hResidual, sCont, map_pure,
      honestRoundPolyAtPrefix] using
      congrArg
        (fun x =>
          (pure x :
            OracleComp oSpec
              (Spec.Strategy.withRoles (OracleComp oSpec) (roundSpec R deg) (roundRoles R deg)
                (fun _ =>
                  HonestProverOutput
                    (StatementWithOracles (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit)
                    (Sumcheck.PolyStmt R deg numVars)))))
        <|
        (roundProverStep_map_honestProverOutputWitness
          (m := OracleComp oSpec) (R := R) (deg := deg) D
          (h := Nat.succ_pos numVars)
          prefixTr (s.oracleStmt ())
          (fun chal =>
            let nextClaim : Option (RoundClaim R) :=
              some <|
                CPolynomial.eval chal
                  (honestRoundPolyAtPrefix (R := R) (deg := deg) D
                    (Nat.succ_pos numVars) prefixTr (s.oracleStmt ())).1
            (⟨⟨nextClaim, s.oracleStmt⟩, PUnit.unit⟩ :
              HonestProverOutput
                (StatementWithOracles (fun _ => Option (RoundClaim R))
                  (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit)
                PUnit)))
  let liftOut :
      (tr : Spec.Transcript (roundSpec R deg)) →
      HonestProverOutput
        (StatementWithOracles (fun _ => Option (RoundClaim R))
          (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) PUnit.unit)
        (Sumcheck.PolyStmt R deg numVars) →
      HonestProverOutput
        (StatementWithOracles (fun _ => Option (RoundClaim R))
          (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
        (Sumcheck.PolyStmt R deg numVars)
    | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
  let verifier :=
    (roundContinuation (R := R) (deg := deg) D
      (n := numVars + 1) (prefixLen := 0)
      (Nat.succ_pos numVars) prefixTr sampleChallenge).verifier PUnit.unit []ₒ claim
  let simulate :=
    (roundContinuation (R := R) (deg := deg) D
      (n := numVars + 1) (prefixLen := 0)
      (Nat.succ_pos numVars) prefixTr sampleChallenge).simulate PUnit.unit
  let statelessProver :=
    (Spec.Strategy.mapOutputWithRoles liftOut ·) <$>
      ((Spec.Strategy.mapOutputWithRoles
          (fun tr out =>
            ⟨out.stmt,
              stepResidual (R := R) (deg := deg)
                (Sumcheck.roundChallenge R deg tr)
                (s.oracleStmt ())⟩) ·) <$>
        ((roundContinuation (R := R) (deg := deg) D
          (n := numVars + 1) (prefixLen := 0)
          (Nat.succ_pos numVars) prefixTr sampleChallenge).prover
          PUnit.unit sCont PUnit.unit))
  let statefulProver :=
    (Spec.Strategy.mapOutputWithRoles liftOut ·) <$>
      ((roundContinuationStateful (R := R) (deg := deg) D
        (totalVars := numVars + 1) numVars sampleChallenge).prover
        PUnit.unit sCont (s.oracleStmt ()))
  have hStrategy :
      statelessProver = statefulProver := by
    exact congrArg (Functor.map (Spec.Strategy.mapOutputWithRoles liftOut)) hStrategyCont
  let verifierStateless :=
    (roundContinuation (R := R) (deg := deg) D
      (n := numVars + 1) (prefixLen := 0)
      (Nat.succ_pos numVars) prefixTr sampleChallenge).verifier PUnit.unit []ₒ claim
  let verifierStateful :=
    (roundContinuationStateful (R := R) (deg := deg) D
      (totalVars := numVars + 1) numVars sampleChallenge).verifier PUnit.unit []ₒ claim
  have hVerifier : verifierStateless = verifierStateful := by
    simp [verifierStateless, verifierStateful, roundContinuation, roundContinuationStateful]
  let simulateStateless :=
    (roundContinuation (R := R) (deg := deg) D
      (n := numVars + 1) (prefixLen := 0)
      (Nat.succ_pos numVars) prefixTr sampleChallenge).simulate PUnit.unit
  let simulateStateful :=
    (roundContinuationStateful (R := R) (deg := deg) D
      (totalVars := numVars + 1) numVars sampleChallenge).simulate PUnit.unit
  have hSimulate : simulateStateless = simulateStateful := by
    funext tr
    simp [simulateStateless, simulateStateful, roundContinuation, roundContinuationStateful]
  let gStateless :
      Spec.Strategy.withRoles (OracleComp oSpec) (roundSpec R deg) (roundRoles R deg)
        (fun _ =>
          HonestProverOutput
            (StatementWithOracles (fun _ => Option (RoundClaim R))
              (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
            (Sumcheck.PolyStmt R deg numVars)) →
      OracleComp oSpec
        ((tr : Spec.Transcript (roundSpec R deg)) ×
          HonestProverOutput
            (StatementWithOracles (fun _ => Option (RoundClaim R))
              (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
            (Sumcheck.PolyStmt R deg numVars) ×
          (Option (RoundClaim R) ×
            QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
              (OracleComp
                ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                  Interaction.OracleDecoration.toOracleSpec
                    (roundSpec R deg) (roundRoles R deg)
                    (roundOracleDecoration R deg) tr)))) :=
    fun strategy =>
      (fun a => ⟨a.1, a.2.1, ⟨a.2.2, simulateStateless a.1⟩⟩) <$>
        runWithOracleCounterpart
          (OracleInterface.simOracle0 (Sumcheck.PolyFamily R deg (numVars + 1)) s.oracleStmt)
          (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
          []ₒ (fun q => PEmpty.elim q)
          strategy
          verifierStateless
  let gStateful :
      Spec.Strategy.withRoles (OracleComp oSpec) (roundSpec R deg) (roundRoles R deg)
        (fun _ =>
          HonestProverOutput
            (StatementWithOracles (fun _ => Option (RoundClaim R))
              (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
            (Sumcheck.PolyStmt R deg numVars)) →
      OracleComp oSpec
        ((tr : Spec.Transcript (roundSpec R deg)) ×
          HonestProverOutput
            (StatementWithOracles (fun _ => Option (RoundClaim R))
              (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
            (Sumcheck.PolyStmt R deg numVars) ×
          (Option (RoundClaim R) ×
            QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
              (OracleComp
                ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                  Interaction.OracleDecoration.toOracleSpec
                    (roundSpec R deg) (roundRoles R deg)
                    (roundOracleDecoration R deg) tr)))) :=
    fun strategy =>
      (fun a => ⟨a.1, a.2.1, ⟨a.2.2, simulateStateful a.1⟩⟩) <$>
        runWithOracleCounterpart
          (OracleInterface.simOracle0 (Sumcheck.PolyFamily R deg (numVars + 1)) s.oracleStmt)
          (roundSpec R deg) (roundRoles R deg) (roundOracleDecoration R deg)
          []ₒ (fun q => PEmpty.elim q)
          strategy
          verifierStateful
  let runTopStateless :=
    fun stratM =>
      (do
        let strategy ← stratM
        gStateless strategy :
        OracleComp oSpec
          ((tr : Spec.Transcript (roundSpec R deg)) ×
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
              (Sumcheck.PolyStmt R deg numVars) ×
            (Option (RoundClaim R) ×
              QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
                (OracleComp
                  ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                    Interaction.OracleDecoration.toOracleSpec
                      (roundSpec R deg) (roundRoles R deg)
                      (roundOracleDecoration R deg) tr)))))
  let runTopStateful :=
    fun stratM =>
      (do
        let strategy ← stratM
        gStateful strategy :
        OracleComp oSpec
          ((tr : Spec.Transcript (roundSpec R deg)) ×
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) claim)
              (Sumcheck.PolyStmt R deg numVars) ×
            (Option (RoundClaim R) ×
              QueryImpl [Sumcheck.PolyFamily R deg (numVars + 1)]ₒ
                (OracleComp
                  ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ +
                    Interaction.OracleDecoration.toOracleSpec
                      (roundSpec R deg) (roundRoles R deg)
                      (roundOracleDecoration R deg) tr)))))
  have hLeft :
      (OracleReduction.mapExecuteWitness
        (oSpec := oSpec)
        (Context := fun _ => roundSpec R deg)
        (Roles := fun _ => roundRoles R deg)
        (oracleDeco := fun _ => roundOracleDecoration R deg)
        (LocalStmt := fun _ => PUnit)
        (StatementOut := fun _ _ => Option (RoundClaim R))
        (OStmtOut := fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
        (WitnessOut₁ := fun _ _ => PUnit)
        (WitnessOut₂ := fun _ _ => Sumcheck.PolyStmt R deg numVars)
        (i := claim)
        (s := s)
        (liftWitness := fun tr _ =>
          stepResidual (R := R) (deg := deg)
            (Sumcheck.roundChallenge R deg tr)
            (s.oracleStmt ()))) <$>
        OracleReduction.executeConcrete
          (roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
          claim s PUnit.unit =
      runTopStateless statelessProver := by
    simpa [runTopStateless, roundOracleReduction,
      Interaction.OracleDecoration.OracleReduction.promoteStatementToShared,
      sCont, liftOut, statelessProver,
      verifierStateless, simulateStateless, gStateless] using
      (Interaction.OracleDecoration.OracleReduction.mapExecuteWitness_eq_execute_mappedOutput
        (reduction :=
          roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
        (Context := fun _ => roundSpec R deg)
        (Roles := fun _ => roundRoles R deg)
        (oracleDeco := fun _ => roundOracleDecoration R deg)
        (LocalStmt := fun _ => PUnit)
        (StatementOut := fun _ _ => Option (RoundClaim R))
        (OStmtOut := fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
        (WitnessOut₁ := fun _ _ => PUnit)
        (WitnessOut₂ := fun _ _ => Sumcheck.PolyStmt R deg numVars)
        (i := claim) (s := s) (w := PUnit.unit)
        (liftWitness := fun tr _ =>
          stepResidual (R := R) (deg := deg)
            (Sumcheck.roundChallenge R deg tr)
            (s.oracleStmt ())))
  have hRun₁ : runTopStateless statelessProver = runTopStateless statefulProver := by
    exact congrArg runTopStateless hStrategy
  have hRun₂ : runTopStateless statefulProver = runTopStateful statefulProver := by
    simp [runTopStateless, runTopStateful, gStateless, gStateful, hVerifier, hSimulate]
  have hRight :
      OracleReduction.executeConcrete
        (roundOracleReductionStateful (R := R) (deg := deg) D numVars sampleChallenge)
        claim s (s.oracleStmt ()) =
      runTopStateful statefulProver := by
    simp [runTopStateful, roundOracleReductionStateful,
      Interaction.OracleDecoration.OracleReduction.executeConcrete,
      Interaction.OracleDecoration.OracleReduction.promoteStatementToShared,
      sCont, liftOut, statefulProver, verifierStateful, simulateStateful, gStateful]
  exact hLeft.trans <| hRun₁.trans <| hRun₂.trans hRight.symm

/-- The stateless recomputing round reduction and the stateful residual-witness
round reduction are honestly publicly equivalent: once we relate the stateful
input witness to the current residual polynomial, their honest executions have
the same public behavior. -/
theorem roundOracleReduction_honestPubliclyEquivalentStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.OracleDecoration.OracleReduction.HonestPubliclyEquivalent
      (fun _ s _ => s.oracleStmt ())
      (roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
      (roundOracleReductionStateful (R := R) (deg := deg) D numVars sampleChallenge) := by
  intro claim s _
  exact roundOracleReduction_executePublic_eq_stateful
    (R := R) (deg := deg) D numVars sampleChallenge claim s

/-- The stateless and stateful single-round sum-check reductions are
honestly execution-equivalent: after relating the stateful input witness to the
original oracle polynomial, the full honest execution agrees once the
stateless output witness is transported to the corresponding residual
polynomial. -/
theorem roundOracleReduction_honestExecutionEquivalentStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.OracleDecoration.OracleReduction.HonestExecutionEquivalent
      (fun _ s _ => s.oracleStmt ())
      (fun _ s tr _ =>
        stepResidual (R := R) (deg := deg)
          (Sumcheck.roundChallenge R deg tr)
          (s.oracleStmt ()))
      (roundOracleReduction (R := R) (deg := deg) D numVars sampleChallenge)
      (roundOracleReductionStateful (R := R) (deg := deg) D numVars sampleChallenge) := by
  intro claim s _
  exact roundOracleReduction_execute_eq_stateful
    (R := R) (deg := deg) D numVars sampleChallenge claim s

end

end Sumcheck
