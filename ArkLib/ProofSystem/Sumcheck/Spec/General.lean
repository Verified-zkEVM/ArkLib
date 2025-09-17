/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`. See `SingleRound.lean` for a single round of the protocol, and the definition of the
sum-check relations.

In the future, we will have files that deal with implementations of the protocol, and we will prove
that those implementations derive security from that of the abstract protocol.

## Protocol Specification

The sum-check protocol is parameterized by the following:
- `R`: the underlying ring (for soundness, required to be finite and a domain)
- `n : ℕ+`: the number of variables (also number of rounds)
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
- `poly : MvPolynomial (Fin n) R`, the multivariate polynomial that is summed over

The sum-check relation for the `i`-th round, where `i = 0, ..., n`, checks that:

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

## Notes & TODOs

Note that to represent sum-check as a series of IORs, we will need to implicitly constrain the
degree of the polynomials via using subtypes, such as `Polynomial.degreeLE` and
`MvPolynomial.degreeOf`. This is because the oracle verifier only gets oracle access to evaluating
the polynomials, but does not see the polynomials in the clear.

When this is compiled to an interactive proof, the corresponding polynomial commitment schemes will
enforce that the declared degree bound holds, via letting the (non-oracle) verifier perform explicit
degree checks.

There are some generalizations that we could consider later:

- Generalize to `degs : Fin n → ℕ` and `domain : Fin n → (Fin m ↪ R)`, e.g. can vary the
  degree bound and the summation domain for each variable. Note: this requires generalizing
  `MvPolynomial.restrictDegree` to have different degree bounds for each variable.

- Generalize the challenges to come from a suitable subset of `R` (e.g. subtractive sets), and not
  necessarily the whole domain. This is used in lattice-based protocols.

- Sumcheck over modules instead of just rings. This will require extending `MvPolynomial` to have
  such a notion of evaluation, something like `evalModule (x : σ → M) (p : MvPolynomial σ R) : M`,
  where we have `[Module R M]`.

## References

[JACM:LFKN92]

[C:BooChiSot21]

-/

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

noncomputable section

namespace Spec

variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)

variable {ι : Type} (oSpec : OracleSpec ι)

/-
  Recall that the types for the statements, oracle statements, witnesses, and the relations, have
  all been defined in `SingleRound.lean`.
-/

/-- The protocol specification for the general sum-check protocol, which is the composition of the
  single-round protocol specifications -/
@[reducible]
def pSpec : ProtocolSpec (Fin.vsum (fun _ : Fin n => 2)) :=
  ProtocolSpec.seqCompose (fun _ => SingleRound.pSpec R deg)
  -- n * 2
  -- fun i => if i % 2 = 0 then (.P_to_V, R⦃≤ d⦄[X]) else (.V_to_P, R)

-- TODO: the input statement should not mention sum-check challenges at all (currently it does,
-- initial challenge vector is empty). We can compose with a `ReduceClaim` (oracle) reduction to get
-- the correct input statement type

/-- The input statement for the (full) sum-check protocol, which contains only the target sum value
-/
@[reducible, simp]
def StmtIn := R

-- def relIn : (StmtIn R) × (∀ i, OStmtIn R d n i) → WitIn → Prop :=
--   fun ⟨target, polyOracle⟩ _ => ∑ x ∈ (univ.map D) ^ᶠ (n + 1), (polyOracle ()).val ⸨x⸩ = target

-- def relOut : (StmtOut R n) × (∀ i, OStmtOut R d n i) → WitOut → Prop :=
--   fun ⟨⟨target, challenges⟩, polyOracle⟩ _ => (polyOracle ()).1 ⸨challenges⸩ = target

variable [DecidableEq R] [SelectableType R]

/-- The verifier for the (full) sum-check protocol -/
@[reducible]
def verifier : Verifier oSpec (StatementRound R n 0 × (∀ i, OracleStatement R n deg i))
    (StatementRound R n (.last n) × (∀ i, OracleStatement R n deg i)) (pSpec R deg n) :=
  Verifier.seqCompose (oSpec := oSpec)
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.verifier R n deg D oSpec)

/-- The oracle verifier for the (full) sum-check protocol -/
@[reducible]
def oracleVerifier : OracleVerifier oSpec (StatementRound R n 0) (OracleStatement R n deg)
    (StatementRound R n (.last n)) (OracleStatement R n deg) (pSpec R deg n) :=
  OracleVerifier.seqCompose (oSpec := oSpec)
    (Stmt := StatementRound R n)
    (OStmt := fun _ => OracleStatement R n deg)
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.oracleVerifier R n deg D oSpec)

/-- The sum-check protocol as a reduction -/
@[reducible]
def reduction : Reduction oSpec
    (StatementRound R n 0 × ∀ i, OracleStatement R n deg i) Unit
    (StatementRound R n (.last n) × ∀ i, OracleStatement R n deg i) Unit
    (pSpec R deg n) :=
  Reduction.seqCompose (oSpec := oSpec)
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (Wit := fun _ => Unit)
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.reduction R n deg D oSpec)

/-- The sum-check protocol as an oracle reduction -/
@[reducible]
def oracleReduction : OracleReduction oSpec
    (StatementRound R n 0) (OracleStatement R n deg) Unit
    (StatementRound R n (.last n)) (OracleStatement R n deg) Unit
    (pSpec R deg n) :=
  OracleReduction.seqCompose (oSpec := oSpec)
    (Stmt := StatementRound R n)
    (OStmt := fun _ => OracleStatement R n deg)
    (Wit := fun _ => Unit)
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.oracleReduction R n deg D oSpec)

omit [SelectableType R] in
@[simp]
lemma reduction_verifier_eq_verifier :
    (reduction R deg D n oSpec).verifier = verifier R deg D n oSpec := by
  rfl

omit [SelectableType R] in
@[simp]
lemma oracleReduction_verifier_eq_oracleVerifier :
    (oracleReduction R deg D n oSpec).verifier = oracleVerifier R deg D n oSpec := by
  rfl

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

open NNReal

/-- Perfect completeness for the (full) sum-check protocol -/
theorem reduction_perfectCompleteness (hInit : init.neverFails) :
    (reduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) :=
  Reduction.seqCompose_perfectCompleteness hInit
    (rel := relationRound R n deg D)
    (R := SingleRound.reduction R n deg D oSpec)
    (h := fun i => SingleRound.reduction_perfectCompleteness i hInit)

/-- Round-by-round knowledge soundness with error `deg / |R|` per challenge for the (full)
  sum-check protocol -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] :
    (oracleVerifier R deg D n oSpec).rbrKnowledgeSoundness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n))
      (fun _ => (deg : ℝ≥0) / (Fintype.card R)) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundness
    (rel := relationRound R n deg D)
    (V := SingleRound.oracleVerifier R n deg D oSpec)
    (h := fun i => SingleRound.oracleVerifier_rbrKnowledgeSoundness i)

end Spec

-- end for noncomputable section
end

end Sumcheck
