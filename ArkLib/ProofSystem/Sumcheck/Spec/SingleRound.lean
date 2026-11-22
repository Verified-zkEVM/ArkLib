/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.LiftContext.OracleReduction
public import ArkLib.OracleReduction.LiftContext.Purity
public import VCVio.OracleComp.SimSemantics.OptionT.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import ArkLib.Data.Probability.Instances
public import ArkLib.OracleReduction.Security.GuardedSoundness
public import ArkLib.Data.Fin.Basic
public import ArkLib.Data.MvPolynomial.EvalExcept
-- `Vector.finRange` is unfolded by `rw` below; its body is not exposed by default.
import all Init.Data.Vector.FinRange

/-!
# Single round of the Sum-check Protocol

We define a single round of the sum-check protocol as a two-message oracle reduction. The simple
round and its lifted form have perfect completeness and round-by-round knowledge soundness
with error `deg / |R|` at every fixed prefix.
`General.lean` composes the rounds into the full protocol.

## Protocol Description

The sum-check protocol is parameterized by the following:
- `R`: the underlying commutative semiring (for soundness, finite with `IsDomain R`)
- `n + 1 : ℕ+`: the number of variables (also number of rounds)
- `deg : ℕ`: the individual degree bound for the polynomial
- `D : Fin m ↪ R`: the set of `m` evaluation points for each variable (for some `m`), represented as
  an injection `Fin m ↪ R`. The image of `D` as a finite subset of `R` is written as
  `Finset.univ.map D`.
- `oSpec : OracleSpec ι`: the set of underlying oracles (e.g. random oracles) that may be needed for
  other reductions. However, the sum-check protocol does _not_ use any oracles.

The sum-check relation has no witness. The statement for the `i`-th round, where `i : Fin (n + 1)`,
 contains:
- `target : R`, which is the target value for sum-check
- `challenges : Fin i → R`, which is the list of challenges sent from the verifier to the prover in
  previous rounds

There is a single oracle statement, which is:
- `poly : MvPolynomial (Fin (n + 1)) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round checks that:

  `∑ x ∈ (univ.map D) ^ᶠ (n - i), poly ⸨challenges, x⸩ = target`.

Note that the last statement (when `i = n`) is the output statement of the sum-check protocol.

For `i = 0, ..., n - 1`, the `i`-th round of the sum-check protocol consists of the following:

1. The prover sends a univariate polynomial `pᵢ ∈ R⦃≤ deg⦄[X]` of degree at most `deg`. If the
   prover is honest, then we have:

    `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨X ⦃i⦄, challenges, x⸩`.

  Here, `poly ⸨X ⦃i⦄, challenges, x⸩` is the polynomial `poly` evaluated at the concatenation of the
  prior challenges `challenges`, the `i`-th variable as the new indeterminate `X`, and the rest of
  the values `x ∈ (univ.map D) ^ᶠ (n - i - 1)`.

  In the oracle protocol, this polynomial `pᵢ` is turned into an oracle for which the verifier can
  query for evaluations at arbitrary points.

2. The verifier then sends the `i`-th challenge `rᵢ` sampled uniformly at random from `R`.

3. The (oracle) verifier then performs queries for the evaluations of `pᵢ` at all points in
   `(univ.map D)`, and checks that: `∑ x in (univ.map D), pᵢ.eval x = target`.

   If the check fails, then the verifier outputs `failure`.

   Otherwise, it outputs a statement for the next round as follows:
   - `target` is updated to `pᵢ.eval rᵢ`
   - `challenges` is updated to the concatenation of the previous challenges and `rᵢ`

## Simplification

We may break this down further into two one-message oracle reductions.

1. The first message from the prover to the verifier can be seen as invoking a ``virtual'' protocol
   as follows:

- `𝒫` holds some data `d` available as an oracle statement to `𝒱`, and wants to convince `𝒱` of
  some predicate `pred` on `d`, expressible as an oracle computation leveraging the oracle
  statement's query structure.
- `𝒫` sends `d'` to `𝒱` as an oracle message. `𝒱` directly checks `pred d'` by performing said
  oracle computation on `d'` and outputs the result.

2. The second message (a challenge) from the verifier to the prover can be seen as invoking a
   ``virtual'' protocol as follows:

- `𝒫` holds two data `d₁` and `d₂`, available as oracle statements, and wants to convince `𝒱` that
  `d₁ = d₂`.
- `𝒱` sends a random query `q` to `𝒫`. It then checks that `oracle d₁ q = oracle d₂ q = r`, and
  outputs `r` as the output statement.

The virtual aspect is because of the substitution: `d = d' = s_i(X)`, where recall
`s_i(X) = ∑ x ∈ D^{n - i - 1}, p(r_0, ..., r_{i-1}, X, x)`.

The predicate is that `∑ y ∈ D, s_i(y) = claim_i`.

-/

@[expose] public section

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

-- The variables for sum-check
variable (R : Type) [CommSemiring R] (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- The input statement for sum-check, which just consists of the target value for the sum -/
def InputStatement := R

/-- Statement for sum-check, parameterized by the ring `R`, the number of variables `n`,
and the round index `i : Fin (n + 1)`

Note that when `i = Fin.last n`, this is the output statement of the sum-check protocol.
When `i = 0`, this has the (redundant) empty challenge vector.
See `InputStatement` for the non-redundant version. -/
structure StatementRound (i : Fin (n + 1)) where
  -- The target value for sum-check
  target : R
  -- The challenges sent from the verifier to the prover from previous rounds
  challenges : Fin i → R

abbrev OutputStatement := StatementRound R _ (.last n)

/-- Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of
  individual degree at most `deg`, equipped with the poly evaluation oracle interface. -/
@[reducible]
def OracleStatement : Unit → Type := fun _ => R⦃≤ deg⦄[X Fin n]

/-- The sum-check relation for the `i`-th round, for `i ≤ n` -/
def relationRound (i : Fin (n + 1)) :
    Set (((StatementRound R n i) × (∀ i, OracleStatement R n deg i)) × Unit) :=
  { ⟨⟨⟨target, challenges⟩, polyOracle⟩, _⟩ |
    ∑ x ∈ (univ.map D) ^ᶠ (n - i), (polyOracle ()).val ⸨challenges, x⸩ = target }

namespace SingleRound

/-- The protocol specification for a single round of sum-check.
Has the form `⟨!v[.P_to_V, .V_to_P], !v[R⦃≤ deg⦄[X], R]⟩` -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩ ++ₚ !p[]

instance : IsSingleRound (pSpec R deg) where
  prover_first' := by aesop
  verifier_last' := by aesop

-- Don't know why instance synthesis requires restating these instances
-- Doesn't seem like instance synthesis can infer the instances for the appends
-- TODO: may need to tweak synthesis?

instance instOI₁ : ∀ i, OracleInterface ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[]).Message i) :=
  instOracleInterfaceMessageAppend

instance instOI₂ : ∀ i, OracleInterface
    ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩).Message i) :=
  instOracleInterfaceMessageAppend

instance instOracleInterfaceMessagePSpec : ∀ i, OracleInterface ((pSpec R deg).Message i) :=
  instOracleInterfaceMessageAppend

instance instST₁ : ∀ i, SampleableType ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[]).Challenge i) :=
  instSampleableTypeChallengeAppend

instance instST₂ [SampleableType R] : ∀ i, SampleableType
    ((⟨!v[.P_to_V], !v[R⦃≤ deg⦄[X]]⟩ ++ₚ !p[] ++ₚ ⟨!v[.V_to_P], !v[R]⟩).Challenge i) :=
  instSampleableTypeChallengeAppend

instance instSampleableTypeChallengePSpec [SampleableType R] :
    ∀ i, SampleableType ((pSpec R deg).Challenge i) :=
  instSampleableTypeChallengeAppend

namespace Simple

-- Let's try to simplify a single round of sum-check, and appeal to compositionality to lift
-- the result to the full protocol.

-- In this simplified setting, the sum-check protocol consists of a _univariate_ polynomial
-- `p : R⦃≤ d⦄[X]` of degree at most `d`, and the relation is that
-- `∑ x ∈ univ.map D, p.eval x = newTarget`.

@[reducible, simp]
def StmtIn : Type := R

@[reducible, simp]
def StmtOut : Type := R × R

@[reducible, simp]
def OStmtIn : Unit → Type := fun _ => R⦃≤ deg⦄[X]

@[reducible, simp]
def OStmtOut : Unit → Type := fun _ => R⦃≤ deg⦄[X]

def inputRelation : Set ((StmtIn R × (∀ i, OStmtIn R deg i)) × Unit) :=
  { ⟨⟨target, oStmt⟩, _⟩ | ∑ x ∈ (univ.map D), (oStmt ()).1.eval x = target }

def outputRelation : Set ((StmtOut R × (∀ i, OStmtOut R deg i)) × Unit) :=
  { ⟨⟨⟨newTarget, chal⟩, oStmt⟩, _⟩ | (oStmt ()).1.eval chal = newTarget }

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The prover in the simple description of a single round of sum-check.

  Takes in input `target : R` and `poly : R⦃≤ deg⦄[X]`, and:
  - Sends a message `poly' := poly` to the verifier
  - Receive `chal` from the verifier
  - Outputs `(newTarget, chal) : R × R`, where `newTarget := poly.eval chal`
-/
def prover : OracleProver oSpec (StmtIn R) (OStmtIn R deg) Unit (StmtOut R) (OStmtOut R deg) Unit
    (pSpec R deg) where
  PrvState
    | 0 => R⦃≤ deg⦄[X]
    | 1 => R⦃≤ deg⦄[X]
    | 2 => R⦃≤ deg⦄[X] × R

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt ()

  sendMessage
  | ⟨0, _⟩ => fun polyLE => pure ⟨polyLE, polyLE⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun polyLE => pure fun chal => ⟨polyLE, chal⟩

  output := fun ⟨polyLE, chal⟩ => pure (((polyLE.val.eval chal, chal), fun _ => polyLE), ())

/-- The simple round's output computes only polynomial values and performs no oracle query. -/
instance instOutputIsPureProver : (prover R deg oSpec).OutputIsPure :=
  ⟨_, fun _ => rfl⟩

variable [DecidableEq R] [SampleableType R]

/-- The verifier for the simple description of a single round of sum-check -/
def verifier : Verifier oSpec (StmtIn R × (∀ i, OStmtIn R deg i))
    (StmtOut R × (∀ i, OStmtOut R deg i)) (pSpec R deg) where
  verify := fun ⟨target, oStmt⟩ transcript => do
    let polyLE : R⦃≤ deg⦄[X] := transcript 0
    guard (∑ x ∈ (univ.map D), polyLE.val.eval x = target)
    let chal : R := transcript 1
    pure ⟨⟨polyLE.val.eval chal, chal⟩, fun _ => oStmt ()⟩

/-- The simple verifier rejects an inconsistent round sum, then computes its next statement. -/
def verifierGuardedForm : (verifier R deg D oSpec).GuardedForm where
  check := fun input tr => decide (∑ x ∈ (univ.map D), (tr 0).val.eval x = input.1)
  out := fun input tr =>
    (((tr 0).val.eval (tr 1), tr 1), fun _ => input.2 ())
  verify_eq := by
    intro input tr
    simp only [verifier, OracleComp.guard_eq]
    split <;> simp_all

/-- The reduction for the simple description of a single round of sum-check -/
def reduction : Reduction oSpec (StmtIn R × (∀ i, OStmtIn R deg i)) Unit
    (StmtOut R × (∀ i, OStmtOut R deg i)) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := verifier R deg D oSpec

-- dtumad: Why is this instance needed?
instance t {ι₁ ι₂ ι₃}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} : MonadLiftT (OracleQuery spec₂)
  (OracleQuery (spec₁ + (spec₂ + spec₃))) := by
  infer_instance

open Function in
def oracleVerifier : OracleVerifier oSpec (StmtIn R) (OStmtIn R deg) (StmtOut R) (OStmtOut R deg)
    (pSpec R deg) where
  verify := fun target chal => do
    let evals : Vector R m ← (Vector.finRange m).mapM
      (fun i => OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <|
          OracleSpec.query (show [(pSpec R deg).Message]ₒ.Domain from ⟨default, D i⟩))
        _)
    guard (evals.sum = target)
    let newTarget ← OptionT.lift <| OracleComp.liftComp
      (OracleComp.lift <|
        OracleSpec.query (show [(pSpec R deg).Message]ₒ.Domain from ⟨default, chal default⟩))
      _
    pure (newTarget, chal default)
  outputOracle := .inl {
    embed := .inl
    hEq := fun i => by simp [pSpec]
    outputInterface_heq := by
      intro i
      rw [show Function.Embedding.inl i = Sum.inl i from rfl] }

def oracleReduction : OracleReduction oSpec (StmtIn R) (OStmtIn R deg) Unit
    (StmtOut R) (OStmtOut R deg) Unit (pSpec R deg) where
  prover := prover R deg oSpec
  verifier := oracleVerifier R deg D oSpec

omit [SampleableType R] in
/-- Every query made by the simple verifier is to its round message oracle. -/
theorem oracleVerifier_only_message_queries (target : StmtIn R)
    (challenges : (pSpec R deg).Challenges) :
    AllQueriesSatisfy ((oracleVerifier R deg D oSpec).verify target challenges).run
      (fun q => ∃ i, q = Sum.inr (Sum.inr i)) := by
  let P : (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)).Domain → Prop :=
    fun q => ∃ i, q = Sum.inr (Sum.inr i)
  let ask (x : R) : OptionT
      (OracleComp (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ))) R :=
    OptionT.lift <| OracleComp.liftComp
      (OracleComp.lift <| OracleSpec.query
        (show [(pSpec R deg).Message]ₒ.Domain from ⟨default, x⟩)) _
  have hquery (x : R) : AllQueriesSatisfy (ask x).run P := by
    simp only [ask, OptionT.lift, OracleComp.liftComp_query,
      OracleQuery.cont_query, OracleQuery.input_query]
    change AllQueriesSatisfy
      (some <$> (liftM (OracleSpec.query
        (spec := oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)) (Sum.inr (Sum.inr
        (show [(pSpec R deg).Message]ₒ.Domain from ⟨default, x⟩)))) :
        OracleComp (oSpec + ([OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)) R)) P
    rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def]
    exact (allQueriesSatisfy_query_iff _ _).2 ⟨_, rfl⟩
  have hvector {k : ℕ} (v : Vector (Fin m) k) :
      AllQueriesSatisfy (v.mapM (fun i => ask (D i))).run P := by
    induction k with
    | zero =>
        rw [Vector.eq_empty (xs := v)]
        simp only [Vector.mapM_mk_empty, OptionT.run_pure]
        exact allQueriesSatisfy_pure _ _
    | succ k ih =>
        obtain ⟨v, i, rfl⟩ := Vector.exists_push (xs := v)
        have hsingle : (#v[i].mapM (fun i => ask (D i))).run =
            (Option.map fun x => #v[x]) <$> (ask (D i)).run := by
          have heq : (#v[i].mapM (fun i => ask (D i))) =
              (fun x => #v[x]) <$> ask (D i) := by
            apply Vector.map_toArray_inj.mp
            simp
          rw [heq, OptionT.run_map]
        rw [← Vector.append_singleton, Vector.mapM_append]
        simp only [OptionT.run_bind, OptionT.run_pure, Option.elimM]
        apply allQueriesSatisfy_bind (ih v)
        intro x
        cases x with
        | none => exact allQueriesSatisfy_pure _ _
        | some x =>
            apply allQueriesSatisfy_bind
            · rw [hsingle]
              rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def]
              exact hquery (D i)
            · intro y; cases y <;> exact allQueriesSatisfy_pure _ _
  change AllQueriesSatisfy ((do
    let evals ← (Vector.finRange m).mapM (fun i => ask (D i))
    guard (evals.sum = target)
    let newTarget ← ask (challenges default)
    pure (newTarget, challenges default) : OptionT _ _).run) P
  simp only [OptionT.run_bind, OptionT.run_pure, Option.elimM]
  change AllQueriesSatisfy
    (((Vector.finRange m).mapM (fun i => ask (D i))).run >>= fun evals =>
      Option.elim evals (pure none) (fun evals =>
        ((guard (evals.sum = target) : OptionT _ Unit).run >>= fun checked =>
          Option.elim checked (pure none) (fun _ =>
            (ask (challenges default)).run >>= fun newTarget =>
              pure (Option.map (fun x => (x, challenges default)) newTarget))))) P
  apply allQueriesSatisfy_bind (hvector _)
  intro evals
  cases evals with
  | none => exact allQueriesSatisfy_pure _ _
  | some evals =>
      simp only [Option.elim_some]
      by_cases h : evals.sum = target
      · simp only [OracleComp.guard_eq, h, ite_true, OptionT.run_pure, pure_bind, Option.elim_some]
        apply allQueriesSatisfy_bind (hquery _)
        intro x
        exact allQueriesSatisfy_pure _ _
      · simp only [OracleComp.guard_eq, h, ite_false, OptionT.run_failure, pure_bind,
          Option.elim_none]
        exact allQueriesSatisfy_pure _ _

open Reduction
open scoped NNReal ENNReal

omit [SampleableType R] in
theorem oracleVerifier_eq_verifier :
    (oracleVerifier R deg D oSpec).toVerifier = verifier R deg D oSpec := by
  ext ⟨target, oStmt⟩ transcript
  simp only [OracleVerifier.toVerifier, verifier, oracleVerifier, pSpec,
    OracleInterface.simOracle2,
    QueryImpl.addLift_def,
    OptionT.run, OptionT.mk, OptionT.lift,
    OracleComp.liftComp_query,
    OracleQuery.cont_query, OracleQuery.input_query,
    bind_pure_comp, id_map,
    FullTranscript.challenges]
  -- Push simulateQ through the outer bind (mapM >>= rest)
  erw [simulateQ_bind]
  -- Each oracle query in mapM resolves to pure evaluation
  set impl := (QueryImpl.liftTarget (OracleComp oSpec) (QueryImpl.id oSpec) +
    QueryImpl.liftTarget (OracleComp oSpec)
      ((OracleInterface.simOracle0 (OStmtIn R deg) oStmt).add
        (OracleInterface.simOracle0
          (fun i => (pSpec R deg).Message i) transcript.messages)))
  have hmapM := simulateQ_optionT_vector_mapM_pure impl
    (fun (i : Fin m) => (some <$> (OracleComp.liftComp
        (OracleComp.lift <|
          OracleSpec.query (show [(pSpec R deg).Message]ₒ.Domain from ⟨default, D i⟩))
        _ : OracleComp _ R) : OracleComp _ (Option R)))
    (fun i => (transcript.messages default).1.eval (D i))
    (Vector.finRange m)
    (by
      intro i; simp only [impl, OracleComp.liftComp_query,
        OracleQuery.cont_query, OracleQuery.input_query,
        id_map]
      -- The query goes through SubSpec lifts; each liftM = liftComp (lift ...)
      -- After simulateQ, the message oracle answers with transcript.messages
      rfl)
  erw [hmapM]; clear hmapM
  simp only [pure_bind]
  -- Push simulateQ through the guard bind
  erw [simulateQ_bind]
  simp only [guard, Alternative.failure, OptionT.fail, OptionT.mk]
  erw [simulateQ_ite, simulateQ_pure, simulateQ_pure]
  -- Bridge: Vector.sum to Finset.sum
  have hsum : (Vector.map (fun i => (transcript.messages default).1.eval (D i))
      (Vector.finRange _)).sum = ∑ x ∈ Finset.map D Finset.univ,
      Polynomial.eval x ↑(transcript.messages default).1 := by
    simp only [Vector.sum]
    rw [← Array.sum_toList, Vector.toList_toArray, Vector.toList_map,
        Vector.finRange, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Finset.sum_map]
    simp [Function.comp]
  rw [hsum]
  simp only [OracleComp.ite_bind, pure_bind, simulateQ_pure, apply_ite (Functor.map _)]
  split_ifs with h1 h2
  · -- Both true: resolve newTarget query
    erw [simulateQ_bind]
    simp only [map_pure, Function.comp, simulateQ_map]
    rfl
  · exfalso; simp only [FullTranscript.messages, pSpec] at *; tauto
  · exfalso; simp only [FullTranscript.messages, pSpec] at *; tauto
  · rfl

omit [SampleableType R] in
/-- The oracle reduction is equivalent to the non-oracle reduction -/
theorem oracleReduction_eq_reduction :
    (oracleReduction R deg D oSpec).toReduction = reduction R deg D oSpec := by
  ext : 1 <;>
  simp [OracleReduction.toReduction, oracleReduction, reduction, oracleVerifier_eq_verifier]

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Perfect completeness for the (non-oracle) reduction -/
theorem reduction_perfectCompleteness :
    (reduction R deg D oSpec).perfectCompleteness init impl
      (inputRelation R deg D) (outputRelation R deg) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨target, oStmt⟩ ⟨⟩ hValid x hx
  have step1 : (prover R deg oSpec).runToRound ((1 : Fin 2).castSucc) (target, oStmt) () =
      (prover R deg oSpec).processRound 0
        ((prover R deg oSpec).runToRound ((0 : Fin 2).castSucc) (target, oStmt) ()) :=
    Prover.runToRound_succ 0 _ _ _
  have hround : (prover R deg oSpec).runToRound (Fin.last 2) (target, oStmt) () = (do
      let chal ← (pSpec R deg).getChallenge ⟨1, rfl⟩
      pure (FullTranscript.mk2 (oStmt ()) chal, (oStmt (), chal))) := by
    refine (Prover.runToRound_succ 1 _ _ _).trans ?_
    rw [step1, Prover.processRound_of_dir_eq_P_to_V 0 rfl,
      Prover.processRound_of_dir_eq_V_to_P 1 rfl]
    simp only [prover, Prover.runToRound_zero_of_prover_first, Nat.reduceAdd, Fin.castSucc_zero,
      Fin.reduceLast, Fin.coe_ofNat_eq_mod, liftM_pure, bind_pure_comp, map_pure, pure_bind]
    congr 1
    funext c
    exact congrArg (·, oStmt (), c) (FullTranscript.mk2_eq_snoc_snoc _ _).symm
  simp only [inputRelation, Set.mem_ofPred_eq, Finset.sum_map] at hValid
  simp only [Reduction.run, Prover.run, reduction, hround] at hx
  simp only [verifier, Verifier.run, prover, hValid, Nat.reduceAdd, Fin.reduceLast,
    Fin.coe_ofNat_eq_mod, bind_pure_comp, liftM_pure, map_pure, Functor.map_map, liftM_map, sum_map,
    guard_eq, OptionT.run_map, bind_map_left, ↓reduceIte, OptionT.run_pure, pure_bind,
    Option.map_some, Option.getM_some, OptionT.run_monadLift, MonadAttach.support_map,
    Set.mem_image] at hx
  obtain ⟨c, -, rfl⟩ := hx
  exact ⟨_, rfl, rfl, rfl⟩

/-- Perfect completeness for the oracle reduction -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R deg D oSpec).perfectCompleteness init impl
      (inputRelation R deg D) (outputRelation R deg) := by
  unfold OracleReduction.perfectCompleteness
  rw [oracleReduction_eq_reduction]
  exact reduction_perfectCompleteness R deg D oSpec

private def state (k : Fin 3)
    (stmt : StmtIn R × (∀ j, OStmtIn R deg j))
    (tr : Transcript k (pSpec R deg)) (_ : Unit) : Prop :=
  (stmt, ()) ∈ inputRelation R deg D ∨
    if h : k.val = 2 then
      let q : R⦃≤ deg⦄[X] := tr ⟨0, by omega⟩
      let r : R := tr ⟨1, by omega⟩
      (∑ x ∈ univ.map D, q.val.eval x = stmt.1) ∧
        (stmt.2 ()).val.eval r = q.val.eval r
    else False

private def knowledge : (verifier R deg D oSpec).KnowledgeStateFunction init impl
    (inputRelation R deg D) (outputRelation R deg)
    Extractor.RoundByRound.unit where
  toFun := state R deg D
  toFun_empty := by intro stmt w h; simpa [state, Extractor.RoundByRound.unit] using h
  toFun_next := by
    intro k hk stmt tr msg w h
    fin_cases k
    · simpa [state] using h
    · exact Direction.noConfusion (show Direction.V_to_P = Direction.P_to_V from hk)
  toFun_full := by
    intro stmt tr w hp
    have h := (verifierGuardedForm R deg D oSpec).check_and_of_prEvent_pos hp
    simp only [state, Fin.val_last]
    exact Or.inr (by simpa [verifierGuardedForm, outputRelation] using h)

omit [DecidableEq R] [SampleableType R] in
private theorem bad_event_iff (stmt : StmtIn R × (∀ j, OStmtIn R deg j))
    (tr : Transcript (1 : Fin 2).castSucc (pSpec R deg)) (r : R) :
    (∃ w : Unit, ¬ state R deg D 1 stmt tr () ∧
      state R deg D 2 stmt (tr.concat r) w) ↔
    (stmt, ()) ∉ inputRelation R deg D ∧
      (∑ x ∈ univ.map D, (tr ⟨0, by decide⟩).val.eval x = stmt.1) ∧
      (stmt.2 ()).val.eval r = (tr ⟨0, by decide⟩).val.eval r := by
  have h0 : (tr.concat r) ⟨0, by decide⟩ = tr ⟨0, by decide⟩ :=
    eq_of_heq (Transcript.concat_apply_lt tr r 0 (by decide) (by decide))
  have h1 : (tr.concat r) ⟨1, by decide⟩ = r :=
    eq_of_heq (Transcript.concat_apply_last tr r 1 rfl (by decide))
  simp only [state, show (1 : Fin 3).val ≠ 2 by decide,
    show (2 : Fin 3).val = 2 from rfl, dite_eq_left]
  erw [h0, h1]
  simp only [dite_eq_right (fun h : False => h), or_false]
  constructor
  · rintro ⟨w, hn, hs⟩
    exact ⟨hn, hs.resolve_left hn⟩
  · rintro ⟨hn, hs⟩
    exact ⟨(), hn, Or.inr hs⟩

omit [DecidableEq R] in
private theorem fixed_message_bound [Fintype R] [IsDomain R]
    (target : R) (p q : R⦃≤ deg⦄[X]) :
    Pr{let r ← $ᵗ R}[
      (∑ x ∈ univ.map D, p.val.eval x) ≠ target ∧
      (∑ x ∈ univ.map D, q.val.eval x) = target ∧
      p.val.eval r = q.val.eval r] ≤
      (((deg : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hsum : (∑ x ∈ univ.map D, q.val.eval x) = target
  · by_cases hfalse : (∑ x ∈ univ.map D, p.val.eval x) ≠ target
    · have hne : (∑ x ∈ univ.map D, p.val.eval x) ≠ ∑ x ∈ univ.map D, q.val.eval x :=
        fun h => hfalse (h.trans hsum)
      exact (prEvent_mono _ _ _ (fun _ h => h.2.2)).trans
        (Probability.prob_agreement_of_sum_ne (univ.map D) p q hne)
    · exact (prEvent_eq_zero_of_forall_not ($ᵗ R) _ (fun _ h => hfalse h.1)).le.trans zero_le
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ R) _ (fun _ h => hsum h.2.1)).le.trans zero_le

/-- At every fixed prefix, a false sum becomes valid with probability at most `deg / |R|`. -/
theorem verifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (verifier R deg D oSpec).rbrKnowledgeSoundness init impl
      (inputRelation R deg D) (outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  refine ⟨fun _ => Unit, Extractor.RoundByRound.unit, knowledge R deg D oSpec, ?_⟩
  intro stmt i tr
  rcases i with ⟨i, hi⟩
  fin_cases i
  · exact Direction.noConfusion (show Direction.P_to_V = Direction.V_to_P from hi)
  · change Pr{let r ← $ᵗ R}[
      ∃ w : Unit, ¬ state R deg D 1 stmt tr () ∧
        state R deg D 2 stmt (tr.concat r) w] ≤ _
    refine le_trans (prEvent_mono _ _ _ ?_)
      (fixed_message_bound R deg D stmt.1 (stmt.2 ()) (tr ⟨0, Nat.zero_lt_succ 0⟩))
    intro r hr
    simpa only [inputRelation, Set.mem_ofPred_eq] using
      (bad_event_iff R deg D stmt tr r).mp hr

/-- Round-by-round knowledge soundness for the oracle verifier. -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R deg D oSpec).toVerifier.rbrKnowledgeSoundness init impl
    (inputRelation R deg D) (outputRelation R deg) (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_eq_verifier]
  exact verifier_rbrKnowledgeSoundness R deg D oSpec

-- TODO: break down the oracle reduction into a series of oracle reductions as stated above

end Simple

/-- Assignment to all variables except round `i`'s free coordinate, formed by appending
the prior challenges to a remaining-domain suffix.  Naming this cast-sensitive
map keeps the materialized polynomial and executable query path definitionally
aligned. -/
def roundSuffix (i : Fin n) (challenges : Fin i.castSucc → R)
    (x : Fin (n - 1 - i) → R) : Fin (n - 1) → R :=
  Fin.append challenges x ∘ Fin.cast (by have := i.isLt; simp; omega)

/-- The univariate round polynomial obtained from the multivariate sum-check
oracle at round `i`.  This named definition is shared by the extensional lens
and its query-by-query implementation. -/
def projectedRoundPolynomial (i : Fin n) (challenges : Fin i.castSucc → R)
    (poly : R⦃≤ deg⦄[X Fin n]) : R⦃≤ deg⦄[X] :=
  ⟨∑ x ∈ (univ.map D) ^ᶠ (n - 1 - i),
      poly.val.evalExcept i (roundSuffix R n i challenges x),
    Submodule.sum_mem _ fun _ _ => MvPolynomial.evalExcept_mem_degreeLE i _ poly.property⟩

/-- The projected polynomial satisfies the univariate sum claim of the input round. -/
theorem projected_sum_of_relationRound (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc) :
    ((univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum =
        stmt.target := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hlist := Multiset.sum_map_toList (univ.map D).1
      (fun a => (projectedRoundPolynomial R (n + 1) deg D i stmt.challenges p).val.eval a)
    change _ = ∑ a ∈ univ.map D, _ at hlist
    apply hlist.trans
    simp only [projectedRoundPolynomial, Polynomial.eval_finsetSum]
    refine (MvPolynomial.sum_eval_evalExcept_append (l := n - i) i stmt.challenges
      (fun _ => univ.map D) (by omega) p.val).trans ?_
    change (∑ z ∈ (univ.map D) ^ᶠ (n + 1 - i.val),
      p.val.eval (Fin.append stmt.challenges z ∘ Fin.cast (by simp))) = _ at h
    rw [Fin.sum_piFinset_cast _ (show n + 1 - i.val = (n - i.val) + 1 by omega)] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fin.append_cast_right]
    rfl

/-- The projected sum claim and the current multivariate relation are equivalent. -/
theorem projected_sum_iff_relationRound (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) :
    ((univ.map D).toList.map (fun x =>
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum =
        stmt.target ↔ ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc := by
  let total := ∑ x ∈ (univ.map D) ^ᶠ (n - i.val),
    p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by simp))
  have h := projected_sum_of_relationRound R n deg D i
    ⟨total, stmt.challenges⟩ p (by rfl)
  change _ = total at h
  change _ = stmt.target ↔ total = stmt.target
  rw [h]

/-- Updating the target to the projected evaluation establishes the next multivariate round. -/
theorem relationRound_projected_output (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (r : R) :
    (((⟨(projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r,
      Fin.snoc stmt.challenges r⟩ : Spec.StatementRound R n i.succ), fun _ => p), ()) ∈
        Spec.relationRound R n deg D i.succ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    change _ = (∑ x ∈ (univ.map D) ^ᶠ (n - i),
      p.val.evalExcept i (Fin.append stmt.challenges x ∘ Fin.cast (by simp; omega))).eval r
    simp only [Polynomial.eval_finsetSum, MvPolynomial.eval_evalExcept_append]
    change (∑ x ∈ (univ.map D) ^ᶠ (n + 1 - (i + 1)),
      p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp; omega))) = _
    rw [Fin.sum_piFinset_cast (univ.map D)
      (show n + 1 - (i + 1) = n - i by omega)]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fin.append_cast_right]
    rfl

/-- For an arbitrary next target, the successor relation is exactly projected evaluation. -/
theorem relationRound_output_iff (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (r target : R) :
    (((⟨target, Fin.snoc stmt.challenges r⟩ : Spec.StatementRound R n i.succ),
      fun _ => p), ()) ∈ Spec.relationRound R n deg D i.succ ↔
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r = target := by
  have h := relationRound_projected_output R n deg D i stmt p r
  change (∑ x ∈ (univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = _ at h
  change (∑ x ∈ (univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = target ↔ _
  rw [h]

/-- The oracle statement lens that connect the simple to the full single-round sum-check protocol

The round index guarantees positive arity. The projection sums over the suffix domain. -/
def oStmtLens (i : Fin n) : OracleStatement.Lens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg) where

  toFunA := fun ⟨⟨target, challenges⟩, oStmt⟩ =>
    ⟨target, fun _ => projectedRoundPolynomial R n deg D i challenges (oStmt ())⟩

  toFunB := fun ⟨⟨_oldTarget, challenges⟩, oStmt⟩ ⟨⟨newTarget, chal⟩, _⟩ =>
    ⟨⟨newTarget, Fin.snoc challenges chal⟩, oStmt⟩

/-- Query the multivariate sum-check input oracle at one point. -/
def queryRoundInput (point : Fin n → R) :
    OracleComp [OracleStatement R n deg]ₒ R :=
  liftM <| OracleSpec.query
    (show [OracleStatement R n deg]ₒ.Domain from ⟨(), point⟩)

@[simp]
theorem simulateQ_queryRoundInput (oStmt : ∀ j, OracleStatement R n deg j)
    (point : Fin n → R) :
    simulateQ (OracleInterface.simOracle0 (OracleStatement R n deg) oStmt)
        (queryRoundInput R n deg point) = pure ((oStmt ()).val.eval point) := by
  simp only [queryRoundInput]
  rfl

/-- Query implementation of `projectedRoundPolynomial`.  A univariate
evaluation query is answered by querying the multivariate input oracle once
for every remaining suffix in the sum-check domain and summing the answers. -/
def simulateProjectedRoundPolynomial (i : Fin n)
    (stmt : StatementRound R n i.castSucc) :
    QueryImpl [Simple.OStmtIn R deg]ₒ
      (OracleComp [OracleStatement R n deg]ₒ) := fun q => by
  rcases q with ⟨u, r⟩
  rcases u with ⟨⟩
  match h : n with
  | 0 => exact Fin.elim0 (h ▸ i)
  | n + 1 =>
      exact do
        let evals ← ((univ.map D) ^ᶠ (n - i)).toList.mapM fun x =>
          queryRoundInput R (n + 1) deg <| Fin.insertNth i r
            (roundSuffix R (n + 1) i stmt.challenges x)
        pure evals.sum

theorem simulateProjectedRoundPolynomial_eq (i : Fin n)
    (stmt : StatementRound R n i.castSucc)
    (oStmt : ∀ j, OracleStatement R n deg j)
    (q : [Simple.OStmtIn R deg]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle0 (OracleStatement R n deg) oStmt)
        (simulateProjectedRoundPolynomial R n deg D i stmt q) =
      (inferInstance : OracleInterface (Simple.OStmtIn R deg q.1)).answer
        (projectedRoundPolynomial R n deg D i stmt.challenges (oStmt ())) q.2 := by
  rcases q with ⟨u, r⟩
  rcases u with ⟨⟩
  match h : n with
  | 0 => exact Fin.elim0 (h ▸ i)
  | n + 1 =>
      change _ = Polynomial.eval r
        (projectedRoundPolynomial R (n + 1) deg D i stmt.challenges (oStmt ())).val
      simp only [simulateProjectedRoundPolynomial, simulateQ_bind,
        simulateQ_list_mapM, simulateQ_queryRoundInput, List.mapM_pure,
        pure_bind]
      change
        (List.map (fun x => (oStmt ()).val.eval <|
            Fin.insertNth i r
              (roundSuffix R (n + 1) i stmt.challenges x))
          ((univ.map D) ^ᶠ (n - i)).toList).sum =
        Polynomial.eval r
          (projectedRoundPolynomial R (n + 1) deg D i stmt.challenges (oStmt ())).val
      calc
        _ = ∑ x ∈ (univ.map D) ^ᶠ (n - i), (oStmt ()).val.eval
              (Fin.insertNth i r
                (roundSuffix R (n + 1) i stmt.challenges x)) := by
            exact Multiset.sum_map_toList
              (((univ.map D) ^ᶠ (n - i)).1) _
        _ = _ := by
          symm
          simp only [projectedRoundPolynomial, Polynomial.eval_finsetSum,
            MvPolynomial.eval_evalExcept]
          rfl

/-- Executable oracle-statement lens for a full sum-check round. -/
def oStmtExecutableLens (i : Fin n) : OracleStatement.ExecutableLens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ)
    (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg) where
  projStmt := StatementRound.target
  materializeInput := fun stmt oStmt _ =>
    projectedRoundPolynomial R n deg D i stmt.challenges (oStmt ())
  simulateInput := simulateProjectedRoundPolynomial R n deg D i
  simulateInput_eq := simulateProjectedRoundPolynomial_eq R n deg D i
  liftStmt := fun stmt ⟨newTarget, chal⟩ =>
    ⟨newTarget, Fin.snoc stmt.challenges chal⟩
  materializeOutput := fun outerOStmt _ => outerOStmt
  simulateOutput := fun q => liftM <| OracleSpec.query
    (show ([OracleStatement R n deg]ₒ + [Simple.OStmtOut R deg]ₒ).Domain from Sum.inl q)
  simulateOutput_eq := by
    intro outerOStmt innerOStmt q
    rcases q with ⟨u, point⟩
    rcases u with ⟨⟩
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
    rfl

@[simp]
theorem oStmtExecutableLens_toLens (i : Fin n) :
    (oStmtExecutableLens R n deg D i).toLens = oStmtLens R n deg D i := by
  rfl

/-- The lifted round exposes the original multivariate oracle.  It is written
as a virtual identity oracle so the same query semantics survives every
adapter and sequential composition path. -/
def liftOutputSimulation {ι : Type} (oSpec : OracleSpec ι) :
    OracleOutputSimulation oSpec (OracleStatement R n deg)
      (OracleStatement R n deg) (pSpec R deg) where
  materializeOutput := fun _ oStmt _ => oStmt
  simulateOutputQuery := fun _ q => liftM <| OracleSpec.query
    (show (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ)).Domain from
      Sum.inr (Sum.inl q))
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rcases q with ⟨u, point⟩
    rcases u with ⟨⟩
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      OracleInterface.simOracle2]
    rfl

def liftContextOutput {ι : Type} (oSpec : OracleSpec ι)
    [DecidableEq R] [SampleableType R] (i : Fin n) :
    OracleVerifier.LiftContextOutput (oStmtExecutableLens R n deg D i)
      (Simple.oracleVerifier R deg D oSpec) where
  outputOracle := .inr (liftOutputSimulation R n deg oSpec)
  materialize_eq := by
    intro outerStmt challenges outerOStmt messages
    rfl

@[simp]
def oCtxExecutableLens (i : Fin n) : OracleContext.ExecutableLens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ)
    (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg)
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := oStmtExecutableLens R n deg D i

@[simp]
def oCtxLens (i : Fin n) : OracleContext.Lens
    (StatementRound R n i.castSucc) (StatementRound R n i.succ) (Simple.StmtIn R) (Simple.StmtOut R)
    (OracleStatement R n deg) (OracleStatement R n deg)
    (Simple.OStmtIn R deg) (Simple.OStmtOut R deg)
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := oStmtLens R n deg D i

@[simp]
def extractorLens (i : Fin n) : Extractor.Lens
    (StatementRound R n i.castSucc × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i))
    (Simple.StmtIn R × (∀ i, Simple.OStmtIn R deg i))
    (Simple.StmtOut R × (∀ i, Simple.OStmtOut R deg i))
    Unit Unit Unit Unit where
  stmt := oStmtLens R n deg D i
  wit := Witness.InvLens.trivial

variable {ι : Type} (oSpec : OracleSpec ι) [DecidableEq R]

/-- The verifier for the `i`-th round of the sum-check protocol -/
def verifier (i : Fin n) : Verifier oSpec
    (StatementRound R n i.castSucc × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) (pSpec R deg) :=
  (Simple.verifier R deg D oSpec).liftContext (oStmtLens R n deg D i)

/-- The verifier forwards base and message queries.  Its univariate input handler
is unreachable because the simple verifier queries only message polynomials. -/
def verifierQueryImpl : QueryImpl
    (oSpec + ([Simple.OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ))
    (OracleComp (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ))) :=
  QueryImpl.addLift (QueryImpl.id' oSpec)
    (QueryImpl.addLift ((fun q => by
      rcases q with ⟨u, point⟩
      rcases u with ⟨⟩
      exact pure (0 : R)) : QueryImpl [Simple.OStmtIn R deg]ₒ
        (OracleComp [OracleStatement R n deg]ₒ))
      (QueryImpl.id' [(pSpec R deg).Message]ₒ) :
      QueryImpl ([Simple.OStmtIn R deg]ₒ + [(pSpec R deg).Message]ₒ)
        (OracleComp ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ)))

/-- The oracle verifier for the `i`-th round of the sum-check protocol. -/
def oracleVerifier [SampleableType R] (i : Fin n) :
    OracleVerifier oSpec (StatementRound R n i.castSucc)
    (OracleStatement R n deg) (StatementRound R n i.succ) (OracleStatement R n deg) (pSpec R deg)
    where
  verify := fun stmt challenges => OptionT.mk <|
    Option.map (fun result : R × R =>
      (⟨result.1, Fin.snoc stmt.challenges result.2⟩ : StatementRound R n i.succ)) <$>
      simulateQ (verifierQueryImpl R n deg oSpec)
        ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run
  outputOracle := .inr (liftOutputSimulation R n deg oSpec)

variable [SampleableType R]

/-- The message-only verifier agrees exactly with the virtual-polynomial context lift. -/
theorem oracleVerifier_eq_liftContext (i : Fin n) :
    oracleVerifier R n deg D oSpec i =
      (Simple.oracleVerifier R deg D oSpec).liftContext
        (oStmtExecutableLens R n deg D i) (liftContextOutput R n deg D oSpec i) := by
  apply OracleVerifier.ext
  · funext stmt challenges
    apply OptionT.ext
    change Option.map (fun result : R × R =>
        (⟨result.1, Fin.snoc stmt.challenges result.2⟩ : StatementRound R n i.succ)) <$>
        simulateQ (verifierQueryImpl R n deg oSpec)
          ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run =
      Option.map (fun result : R × R =>
        (⟨result.1, Fin.snoc stmt.challenges result.2⟩ : StatementRound R n i.succ)) <$>
        simulateQ (OracleVerifier.liftContextQueryImpl (oStmtExecutableLens R n deg D i) stmt)
          ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run
    congr 1
    have hb := Simple.oracleVerifier_only_message_queries R deg D oSpec stmt.target challenges
    generalize
      ((Simple.oracleVerifier R deg D oSpec).verify stmt.target challenges).run = oa at hb ⊢
    revert hb
    induction oa using OracleComp.inductionOn with
    | pure x => intro _; rfl
    | query_bind q next ih =>
        intro hb
        obtain ⟨⟨j, rfl⟩, hnext⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 hb
        simp only [simulateQ_bind, simulateQ_spec_query]
        have hh : verifierQueryImpl R n deg oSpec (Sum.inr (Sum.inr j)) =
            OracleVerifier.liftContextQueryImpl (oStmtExecutableLens R n deg D i) stmt
              (Sum.inr (Sum.inr j)) := by
          simp only [verifierQueryImpl, OracleVerifier.liftContextQueryImpl,
            QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
        rw [hh]
        congr 1
        funext answer
        exact ih answer (hnext answer)
  · rfl

/-- A full sum-check round queries only its sent message polynomial.  Its virtual
projection of the input polynomial is never evaluated by the verifier. -/
theorem oracleVerifier_only_message_queries (i : Fin n)
    (stmt : StatementRound R n i.castSucc) (challenges : (pSpec R deg).Challenges) :
    AllQueriesSatisfy ((oracleVerifier R n deg D oSpec i).verify stmt challenges).run
      (fun q => ∃ j, q = Sum.inr (Sum.inr j)) := by
  rw [oracleVerifier_eq_liftContext]
  change AllQueriesSatisfy (Option.map _ <$> simulateQ
    (OracleVerifier.liftContextQueryImpl (oStmtExecutableLens R n deg D i) stmt)
    ((Simple.oracleVerifier R deg D oSpec).verify
      ((oStmtExecutableLens R n deg D i).projStmt stmt) challenges).run) _
  rw [allQueriesSatisfy_def, isQueryBound_map_iff, ← allQueriesSatisfy_def]
  apply (Simple.oracleVerifier_only_message_queries R deg D oSpec _ challenges).simulateQ
  rintro q ⟨j, rfl⟩
  simp only [OracleVerifier.liftContextQueryImpl, QueryImpl.addLift_def,
    QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
  change AllQueriesSatisfy (liftM (OracleSpec.query
    (spec := oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg).Message]ₒ))
    (Sum.inr (Sum.inr j)))) _
  exact (allQueriesSatisfy_query_iff _ _).2 ⟨j, rfl⟩

/-- The sum-check reduction for the `i`-th round of the sum-check protocol -/
def reduction (i : Fin n) : Reduction oSpec
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)) Unit
    ((StatementRound R n i.succ) × (∀ i, OracleStatement R n deg i)) Unit (pSpec R deg) :=
  (Simple.reduction R deg D oSpec).liftContext (oCtxLens R n deg D i).toContext

/-- Ordinary context lifting retains pure prover output for a full sum-check round. -/
instance instOutputIsPureReduction (i : Fin n) :
    (reduction R n deg D oSpec i).prover.OutputIsPure := by
  change (Prover.liftContext (oCtxLens R n deg D i).toContext
    (Simple.prover R deg oSpec)).OutputIsPure
  infer_instance

/-- The lifted full round retains the simple verifier's rejection guard. -/
def verifierGuardedForm (i : Fin n) :
    (reduction R n deg D oSpec i).verifier.GuardedForm :=
  Verifier.GuardedForm.liftContext (oStmtLens R n deg D i)
    (Simple.verifier R deg D oSpec) (Simple.verifierGuardedForm R deg D oSpec)

/-- The sum-check oracle reduction for the `i`-th round of the sum-check protocol -/
def oracleReduction (i : Fin n) : OracleReduction oSpec
    (StatementRound R n i.castSucc) (OracleStatement R n deg) Unit
    (StatementRound R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) :=
  (Simple.oracleReduction R deg D oSpec).liftContext
    (oCtxExecutableLens R n deg D i) (liftContextOutput R n deg D oSpec i)

omit [SampleableType R] in
@[simp]
lemma reduction_verifier_eq_verifier {i : Fin n} :
    (reduction R n deg D oSpec i).verifier = verifier R n deg D oSpec i := by
  rfl

@[simp]
lemma oracleReduction_verifier_eq_verifier {i : Fin n} :
    (oracleReduction R n deg D oSpec i).verifier = oracleVerifier R n deg D oSpec i := by
  exact (oracleVerifier_eq_liftContext R n deg D oSpec i).symm

/-- Materializing the oracle round gives its ordinary context-lifted reduction. -/
@[simp]
theorem oracleReduction_toReduction (i : Fin n) :
    (oracleReduction R n deg D oSpec i).toReduction = reduction R n deg D oSpec i := by
  calc
    _ = (Simple.oracleReduction R deg D oSpec).toReduction.liftContext
        (oCtxExecutableLens R n deg D i).toLens.toContext :=
      OracleReduction.liftContext_toReduction_comm (oCtxExecutableLens R n deg D i)
        (Simple.oracleReduction R deg D oSpec) (liftContextOutput R n deg D oSpec i)
    _ = reduction R n deg D oSpec i := by
      rw [Simple.oracleReduction_eq_reduction]
      rfl

section Security

open Reduction
open scoped NNReal

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} (i : Fin n)

omit [DecidableEq R] [SampleableType R] in
private lemma input_projection (stmt : StatementRound R n i.castSucc)
    (os : ∀ j, OracleStatement R n deg j) :
    (((oStmtLens R n deg D i).proj (stmt, os)), ()) ∈ Simple.inputRelation R deg D ↔
      ((stmt, os), ()) ∈ relationRound R n deg D i.castSucc := by
  have h := projected_sum_iff_relationRound R n deg D i stmt (os ())
  have hsum := Multiset.sum_map_toList (univ.map D).val
    (fun x => (projectedRoundPolynomial R n deg D i stmt.challenges (os ())).val.eval x)
  change (List.map _ (univ.map D).toList).sum = ∑ x ∈ univ.map D, _ at hsum
  rw [hsum] at h
  simpa [Simple.inputRelation, oStmtLens, Statement.Lens.proj] using h

omit [DecidableEq R] [SampleableType R] in
private lemma output_projection (stmt : StatementRound R n i.castSucc)
    (os : ∀ j, OracleStatement R n deg j) (target r : R) :
    (((oStmtLens R n deg D i).lift (stmt, os) ((target, r), fun _ =>
      projectedRoundPolynomial R n deg D i stmt.challenges (os ()))), ()) ∈
        relationRound R n deg D i.succ ↔
      ((((target, r), fun _ => projectedRoundPolynomial R n deg D i stmt.challenges (os ())), ()) ∈
        Simple.outputRelation R deg) := by
  simpa [oStmtLens, Statement.Lens.lift, Simple.outputRelation] using
    relationRound_output_iff R n deg D i stmt (os ()) r target

omit [SampleableType R] in
private lemma verifier_polynomial (stmt : StatementRound R n i.castSucc)
    (os : ∀ j, OracleStatement R n deg j)
    (out : Simple.StmtOut R × (∀ j, Simple.OStmtOut R deg j))
    (hc : (Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement
      (oStmtLens R n deg D i) (stmt, os) out) :
    out.2 () = projectedRoundPolynomial R n deg D i stmt.challenges (os ()) := by
  rw [Simple.oracleVerifier_eq_verifier] at hc
  rcases hc with ⟨tr, htr⟩
  simp only [Simple.StmtOut, Simple.OStmtOut, Verifier.run, Simple.StmtIn, Simple.OStmtIn,
    Simple.verifier, Fin.isValue, sum_map, guard_eq, bind_pure_comp, Statement.Lens.proj,
    oStmtLens, Fin.val_castSucc, ofPFunctor_toPFunctor, Fin.val_succ, MonadAttach.support_map,
    MonadAttach.support_ite, MonadAttach.support_pure, support_failure, Set.mem_image,
    Set.mem_ite_empty_right, Set.mem_singleton_iff, and_true, exists_const] at htr
  exact (congrFun (congrArg Prod.snd htr.2) ()).symm

private lemma reduction_prover_support {SI WI SO WO : Type} {k : ℕ} {ps : ProtocolSpec k}
    (red : Reduction oSpec SI WI SO WO ps) (x : SI) (w : WI)
    (z : (FullTranscript ps × SO × WO) × SO)
    (hz : z ∈ support (red.run x w)) : z.1 ∈ support (red.prover.run x w) := by
  change some z ∈ support (red.run x w).run at hz
  rw [Reduction.run_run_eq_bind] at hz
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
  rcases hz with ⟨pr, hpr, o, _ho, heq⟩
  cases o with
  | none => simp at heq
  | some out =>
    simp only [Option.map_some, Option.some.injEq] at heq
    subst z
    exact hpr

omit [DecidableEq R] [SampleableType R] in
private lemma honest_round (stmt : Simple.StmtIn R × (∀ j, Simple.OStmtIn R deg j)) :
    (Simple.prover R deg oSpec).runToRound (Fin.last 2) stmt () = (do
      let chal ← (pSpec R deg).getChallenge ⟨1, rfl⟩
      pure (FullTranscript.mk2 (stmt.2 ()) chal, (stmt.2 (), chal))) := by
  have step1 : (Simple.prover R deg oSpec).runToRound ((1 : Fin 2).castSucc) stmt () =
      (Simple.prover R deg oSpec).processRound 0
        ((Simple.prover R deg oSpec).runToRound ((0 : Fin 2).castSucc) stmt ()) :=
    Prover.runToRound_succ 0 _ _ _
  refine (Prover.runToRound_succ 1 _ _ _).trans ?_
  rw [step1, Prover.processRound_of_dir_eq_P_to_V 0 rfl,
    Prover.processRound_of_dir_eq_V_to_P 1 rfl]
  simp only [Simple.prover, Prover.runToRound_zero_of_prover_first, Nat.reduceAdd,
    Fin.castSucc_zero, Fin.reduceLast, Fin.coe_ofNat_eq_mod, liftM_pure,
    bind_pure_comp, map_pure, pure_bind]
  congr 1
  funext c
  exact congrArg (·, stmt.2 (), c) (FullTranscript.mk2_eq_snoc_snoc _ _).symm

instance oCtxLens_complete :
    (oCtxLens R n deg D i).toContext.IsComplete
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleReduction R deg D oSpec).toReduction.compatContext
        (oCtxLens R n deg D i).toContext)
where
  proj_complete := by
    rintro ⟨stmt, os⟩ ⟨⟩ h
    exact (input_projection i stmt os).mpr h
  lift_complete := by
    rintro ⟨stmt, os⟩ ⟨⟩ out ⟨⟩ hc _hi _ho
    rw [Simple.oracleReduction_eq_reduction] at hc
    rcases hc with ⟨z, hz, hout⟩
    have hp := reduction_prover_support (Simple.reduction R deg D oSpec) _ _ z hz
    change z.1 ∈ support ((Simple.prover R deg oSpec).run
      ((oStmtLens R n deg D i).proj (stmt, os)) ()) at hp
    rw [Prover.run, honest_round] at hp
    simp only [Simple.StmtOut, Simple.OStmtOut, ChallengeIdx, Nat.reduceAdd, Nat.add_zero,
      Fin.vcons_fin_zero, Fin.vappend_zero, Challenge, Fin.reduceLast, Simple.StmtIn,
      Simple.OStmtIn, Simple.prover, Fin.isValue, MessageIdx, Message, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two,
      HasQuery.instOfMonadLift_query, Fin.coe_ofNat_eq_mod, Nat.reduceMod, bind_pure_comp,
      liftM_pure, map_pure, Functor.map_map, MonadAttach.support_map, Set.mem_image,
      MonadAttach.mem_support] at hp
    obtain ⟨c, _hc, heq⟩ := hp
    change z.1.2 = (out, ()) at hout
    rw [← heq] at hout
    simp only [Prod.mk.injEq, and_true] at hout
    subst out
    exact (output_projection i stmt os _ c).mpr rfl

instance extractorLens_rbr_knowledge_soundness :
    Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement (oStmtLens R n deg D i))
      (fun _ _ => True)
      ⟨oStmtLens R n deg D i, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    rintro ⟨stmt, os⟩ ⟨⟨target, r⟩, ios⟩ ⟨⟩ hc ho
    left
    have hp := verifier_polynomial i stmt os ((target, r), ios) hc
    have hi := (output_projection i stmt os target r).mp ho
    change ios () = projectedRoundPolynomial R n deg D i stmt.challenges (os ()) at hp
    simpa [Simple.outputRelation, hp] using hi
  lift_knowledgeSound := by
    rintro ⟨stmt, os⟩ ⟨⟩ ⟨⟩ _ h
    exact (input_projection i stmt os).mp h

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem reduction_perfectCompleteness :
    (reduction R n deg D oSpec i).perfectCompleteness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  Reduction.liftContext_perfectCompleteness
    (lens := (oCtxLens R n deg D i).toContext)
    (lensComplete := by
      rw [← Simple.oracleReduction_eq_reduction]
      exact oCtxLens_complete i)
    (Simple.reduction_perfectCompleteness R deg D oSpec)

/-- Round-by-round knowledge soundness for the lifted round verifier. -/
theorem verifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (verifier R n deg D oSpec i).rbrKnowledgeSoundness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  exact Verifier.liftContext_rbrKnowledgeSoundness
    (stmtLens := oStmtLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.verifier R deg D oSpec)
    (lensKS := by
      rw [← Simple.oracleVerifier_eq_verifier]
      exact extractorLens_rbr_knowledge_soundness i)
    (Simple.verifier_rbrKnowledgeSoundness R deg D oSpec)

/-- Completeness theorem for single-round of sum-check, obtained by transporting the completeness
proof for the simplified version -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R n deg D oSpec i).perfectCompleteness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  OracleReduction.liftContext_perfectCompleteness
    (R := Simple.oracleReduction R deg D oSpec)
    (lens := oCtxExecutableLens R n deg D i)
    (output := liftContextOutput R n deg D oSpec i)
    (lensComplete := by
      change (oCtxLens R n deg D i).toContext.IsComplete
        (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
        (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
        ((Simple.oracleReduction R deg D oSpec).toReduction.compatContext
          (oCtxLens R n deg D i).toContext)
      exact oCtxLens_complete i)
    (Simple.oracleReduction_perfectCompleteness R deg D oSpec)

local instance : Inhabited R := ⟨0⟩

/-- Round-by-round knowledge soundness for the lifted oracle verifier. -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R n deg D oSpec i).toVerifier.rbrKnowledgeSoundness init impl
    (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
    (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_eq_liftContext]
  exact OracleVerifier.liftContext_rbrKnowledgeSoundness
    (stmtLens := oStmtExecutableLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.oracleVerifier R deg D oSpec)
    (liftContextOutput R n deg D oSpec i)
    (lensKS := by simpa using extractorLens_rbr_knowledge_soundness i)
    (Simple.oracleVerifier_rbrKnowledgeSoundness R deg D oSpec)

end Security

namespace Unfolded

-- The rest of the below are for equivalence checking. We have deduced the construction & security
-- of the single round protocol from its simplified version via context lifting.

@[reducible]
def proverState (i : Fin n) : ProverState 2 where
  PrvState
  | 0 => (StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 1 => (StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i)
  | 2 => (StatementRound R n i.succ) × (∀ i, OracleStatement R n deg i)

/-- Prover input for the `i`-th round of the sum-check protocol, where `i < n` -/
def proverInput (i : Fin n) : ProverInput
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    Unit ((proverState R n deg i).PrvState 0) where
  input := Prod.fst

/-- Prover interaction for the `i`-th round of the sum-check protocol, where `i < n`. -/
def proverRound (i : Fin n) : ProverRound oSpec (pSpec R deg) where
  PrvState := (proverState R n deg i).PrvState

  sendMessage
  | ⟨0, _⟩ => fun state =>
    let ⟨⟨_, challenges⟩, oStmt⟩ := state
    pure ⟨projectedRoundPolynomial R n deg D i challenges (oStmt ()), state⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨target, challenges⟩, oStmt⟩ => pure fun chal =>
    let ⟨poly, hp⟩ := oStmt 0
    letI newChallenges : Fin i.succ → R := Fin.snoc challenges chal
    letI newTarget := ∑ x ∈ (univ.map D) ^ᶠ (n - i - 1), poly ⸨newChallenges, x⸩'(by simp; omega)
    ⟨⟨newTarget, newChallenges⟩, fun _ => ⟨poly, hp⟩⟩

/-- Since there is no witness, the prover's output for each round `i < n` of the sum-check protocol
  is trivial -/
def proverOutput (i : Fin n) : ProverOutput oSpec
    ((StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) × Unit)
    ((proverState R n deg i).PrvState (Fin.last 2)) where
  output := fun x => pure (x, ())

/-- The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only
  well-defined for `n > 0`, since when `n = 0` there is no protocol. -/
def prover (i : Fin n) : OracleProver oSpec
    (StatementRound R n i.castSucc) (OracleStatement R n deg) Unit
    (StatementRound R n i.succ) (OracleStatement R n deg) Unit (pSpec R deg) where
  toProverState := proverState R n deg i
  toProverInput := proverInput R n deg i
  sendMessage := (proverRound R n deg D oSpec i).sendMessage
  receiveChallenge := (proverRound R n deg D oSpec i).receiveChallenge
  toProverOutput := proverOutput R n deg oSpec i

/-- The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1` -/
def verifier (i : Fin n) : Verifier oSpec
    ((StatementRound R n i.castSucc) × (∀ i, OracleStatement R n deg i))
    (StatementRound R n i.succ × (∀ i, OracleStatement R n deg i)) (pSpec R deg) where
  verify := fun ⟨⟨target, challenges⟩, oStmt⟩ transcript => do
    let ⟨p_i, _⟩ : R⦃≤ deg⦄[X] := transcript 0
    let r_i : R := transcript 1
    guard (∑ x ∈ (univ.map D), p_i.eval x = target)
    pure ⟨⟨p_i.eval r_i, Fin.snoc challenges r_i⟩, oStmt⟩

end Unfolded

omit [SampleableType R] in
/-- Projecting the input and lifting the output gives the explicit legacy round verifier. -/
theorem verifier_eq_unfolded (i : Fin n) :
    verifier R n deg D oSpec i = Unfolded.verifier R n deg D oSpec i := by
  ext ⟨stmt, oStmt⟩ transcript
  rcases hq : transcript 0 with ⟨q, hqdeg⟩
  simp [verifier, Verifier.liftContext, Simple.verifier, Unfolded.verifier,
    oStmtLens, Statement.Lens.proj, Statement.Lens.lift, hq, OracleComp.guard_eq]

/-- The executable oracle projection preserves the repaired legacy verifier. -/
theorem oracleVerifier_eq_verifier (i : Fin n) :
    (oracleVerifier R n deg D oSpec i).toVerifier = verifier R n deg D oSpec i := by
  rw [oracleVerifier_eq_liftContext, OracleVerifier.liftContext_toVerifier_comm,
    Simple.oracleVerifier_eq_verifier, oStmtExecutableLens_toLens]
  rfl

end SingleRound

end Spec

-- end for noncomputable section
end

end Sumcheck
