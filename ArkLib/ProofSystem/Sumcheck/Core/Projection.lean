/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.IntervalCompleteness

/-! # Projected round oracles over indexed domains

Each projected evaluation queries the original polynomial once for every suffix assignment of
domain indices. Its oracle-map law identifies those answers with the honest round polynomial.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg n d : ℕ} (D : Fin d → R)

/-- The evaluation oracle of one degree-bounded univariate polynomial. -/
noncomputable def roundFamily (R : Type) [CommSemiring R] (deg : ℕ) :
    OracleFamily Unit (fun _ => R⦃≤ deg⦄[X]) := ⟨fun _ => inferInstance⟩

/-- A query to the original multivariate polynomial. -/
noncomputable def projectionInput (point : Fin n → R) :
    OracleComp (polyFamily R deg n).spec R :=
  liftM ((polyFamily R deg n).spec.query ⟨(), point⟩)

/-- The realized input answers with its polynomial evaluation. -/
@[simp] theorem simulateQ_projectionInput (data : ∀ j, PolynomialData R n deg j)
    (point : Fin n → R) :
    simulateQ ((polyFamily R deg n).behaviorOfRealizations data) (projectionInput point) =
      (pure ((data ()).val.eval point) : Id R) := rfl

/-- Simulate a projected evaluation by summing queries over suffix domain assignments. -/
noncomputable def projectedQuery (i : Fin n) (c : Fin i.castSucc → R) (r : R) :
    OracleComp (polyFamily R deg n).spec R := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    exact do
      let values ← (Finset.univ : Finset (Fin (n + 1 - 1 - i) → Fin d)).toList.mapM fun x =>
        projectionInput (Fin.insertNth i r (roundSuffix i c (D ∘ x)))
      pure values.sum

/-- Answering projected queries from the input realizes the honest round polynomial. -/
theorem simulateQ_projectedQuery (i : Fin n) (c : Fin i.castSucc → R)
    (data : ∀ j, PolynomialData R n deg j) (r : R) :
    simulateQ ((polyFamily R deg n).behaviorOfRealizations data) (projectedQuery D i c r) =
      (projectedRoundPolynomial D i c (data ())).val.eval r := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    unfold projectedQuery
    simp only [simulateQ_bind, simulateQ_list_mapM, simulateQ_projectionInput,
      List.mapM_pure, LawfulMonad.pure_bind, simulateQ_pure]
    change (List.map (fun x : Fin (n + 1 - 1 - i) → Fin d =>
      (data ()).val.eval (Fin.insertNth i r (roundSuffix i c (D ∘ x))))
        (Finset.univ : Finset (Fin (n + 1 - 1 - i) → Fin d)).toList).sum =
          (projectedRoundPolynomial D i c (data ())).val.eval r
    refine (Multiset.sum_map_toList
      (Finset.univ : Finset (Fin (n + 1 - 1 - i) → Fin d)).val _).trans ?_
    simp only [projectedRoundPolynomial, Polynomial.eval_finsetSum, MvPolynomial.eval_evalExcept]
    rfl

/-- The native projected oracle map, including its concrete realization and query implementation. -/
noncomputable def projectedMap (i : Fin n) (c : Fin i.castSucc → R) :
    OracleMap (polyFamily R deg n) (roundFamily R deg) where
  f data _ := projectedRoundPolynomial D i c (data ())
  impl q := projectedQuery D i c q.2
  law data q := simulateQ_projectedQuery D i c data q.2

/-- Concrete data exported by the projection is the native honest round polynomial. -/
@[simp] theorem projectedMap_f (i : Fin n) (c : Fin i.castSucc → R)
    (data : ∀ j, PolynomialData R n deg j) (u : Unit) :
    (projectedMap (deg := deg) D i c).f data u =
      projectedRoundPolynomial D i c (data ()) := rfl

/-- A true input sum gives the projected oracle's sum claim, for every indexed domain. -/
theorem projectedMap_sum (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j)
    (h : indexedRelation D i.castSucc stmt (data ())) :
    (∑ a : Fin d, ((projectedMap (deg := deg) D i stmt.challenges).f data ()).val.eval
      (D a)) = stmt.target := (sum_projectedRoundPolynomial D i stmt.challenges (data ())).trans h

/-- The projected input handler answers by running the projection's actual query implementation
against the original input handler. -/
noncomputable def projectedInput (i : Fin n) (c : Fin i.castSucc → R)
    (data : ∀ j, PolynomialData R n deg j) : QueryImpl (R →ₒ R) Id := fun r =>
  simulateQ ((polyFamily R deg n).behaviorOfRealizations data)
    ((projectedMap (deg := deg) D i c).impl ⟨(), r⟩)

/-- The derived handler agrees at every query with honest projected polynomial evaluation. -/
theorem projectedInput_eq (i : Fin n) (c : Fin i.castSucc → R)
    (data : ∀ j, PolynomialData R n deg j) :
    projectedInput D i c data = fun r =>
      (pure ((projectedRoundPolynomial D i c (data ())).val.eval r) : Id R) :=
  funext (simulateQ_projectedQuery D i c data)

/-- Simulating any standalone oracle program through the derived handler is identical to
answering from the projected polynomial. This includes every standalone verifier decision. -/
theorem simulateQ_projectedInput {α : Type} (i : Fin n) (c : Fin i.castSucc → R)
    (data : ∀ j, PolynomialData R n deg j) (program : OracleComp (R →ₒ R) α) :
    simulateQ (projectedInput D i c data) program =
      simulateQ (fun r => (pure ((projectedRoundPolynomial D i c (data ())).val.eval r) :
        Id R)) program := by
  rw [projectedInput_eq]

section Execute
variable [DecidableEq R]

/-- Execute a standalone round against the projected input oracle, with any sent message and
any explicit challenge computation. -/
noncomputable def projectedExecute {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (msg : R⦃≤ deg⦄[X]) :=
  indexedExecute D ambient impl challenge
    (fun _ => univariateData ((projectedMap (deg := deg) D i stmt.challenges).f data ()))
    msg stmt.target

/-- The actual projected execution preserves its original projected oracle and the sent
message's evaluations, including rejection of an incorrect indexed sum. -/
theorem projectedExecute_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j) (msg : R⦃≤ deg⦄[X]) :
    projectedExecute D ambient impl challenge i stmt data msg =
      indexedRoundResult D
        (fun _ => univariateData ((projectedMap (deg := deg) D i stmt.challenges).f data ()))
        msg stmt.target <$> challenge := indexedExecute_eq D ambient impl challenge _ msg _

/-- On a true input claim, the actual standalone honest execution always accepts its projected
polynomial and returns its evaluation at the supplied challenge. -/
theorem projectedExecute_honest_eq {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j)
    (h : indexedRelation D i.castSucc stmt (data ())) :
    let q := projectedRoundPolynomial D i stmt.challenges (data ())
    projectedExecute D ambient impl challenge i stmt data q =
      (fun r => (⟨roundTranscript q r, (q.val.eval r, r),
        some (⟨q.val.eval r, Fin.snoc Fin.elim0 r⟩, fun _ => univariateData q)⟩ :
          Observation oracleSig (protocol R deg 1) (fun _ => R × R)
            (fun _ => RoundStatement R 1 (Fin.last 1) ×
              (∀ j, PolynomialData R 1 deg j)))) <$> challenge := by
  dsimp only
  rw [projectedExecute_eq]
  congr 1
  funext r
  unfold indexedRoundResult
  rw [ite_eq_left ((sum_projectedRoundPolynomial D i stmt.challenges (data ())).trans h)]
  rfl

/-- Closing projected execution retains the actual derived input handler as its output behavior,
including every query to the original multivariate oracle used to answer that handler. -/
theorem projectedExecute_closed {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j)
    (h : indexedRelation D i.castSucc stmt (data ())) :
    (fun result => result.2.2.map (fun t =>
      (t.1.target, t.1.challenges ⟨0, by decide⟩,
        fun x => (t.2 ()).val.eval (fun _ : Fin 1 => x)))) <$>
      projectedExecute D ambient impl challenge i stmt data
        (projectedRoundPolynomial D i stmt.challenges (data ())) =
      (fun r => some ((projectedRoundPolynomial D i stmt.challenges (data ())).val.eval r,
        r, projectedInput D i stmt.challenges data)) <$> challenge := by
  rw [projectedExecute_honest_eq D ambient impl challenge i stmt data h, Functor.map_map]
  congr 1
  funext r
  dsimp only [Function.comp_apply, Option.map_some]
  apply congrArg some
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext x
      rw [projectedInput_eq]
      have hp : (fun _ : Fin 1 => x) = Fin.snoc Fin.elim0 x := by
        funext j
        have hj : j = 0 := Fin.eq_zero j
        subst j
        rfl
      change (univariateData (projectedRoundPolynomial D i stmt.challenges (data ()))).val.eval
        (fun _ : Fin 1 => x) = (projectedRoundPolynomial D i stmt.challenges (data ())).val.eval x
      rw [hp, univariateData_eval]

/-- The actual projected honest execution returns a true standalone evaluation claim. -/
theorem projectedExecute_related {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) (challenge : m R)
    (i : Fin n) (stmt : RoundStatement R n i.castSucc)
    (data : ∀ j, PolynomialData R n deg j)
    (h : indexedRelation D i.castSucc stmt (data ())) :
    (fun result => result.2.2.map (fun t =>
      (t.2 ()).val.eval t.1.challenges = t.1.target)) <$>
      projectedExecute D ambient impl challenge i stmt data
        (projectedRoundPolynomial D i stmt.challenges (data ())) =
      (fun _ : R => some True) <$> challenge := by
  rw [projectedExecute_honest_eq D ambient impl challenge i stmt data h, Functor.map_map]
  congr 1
  funext r
  change some ((univariateData (projectedRoundPolynomial D i stmt.challenges (data ()))).val.eval
    (Fin.snoc Fin.elim0 r) = _) = some True
  rw [univariateData_eval]
  simp only [eq_self]


end Execute

end Sumcheck.Core
