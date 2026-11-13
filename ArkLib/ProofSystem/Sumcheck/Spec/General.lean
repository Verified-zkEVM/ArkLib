/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.OracleReduction.Composition.Sequential.GuardedNary
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
public import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# The Sum-check Protocol

We define the sum-check protocol as a series of Interactive Oracle Reductions (IORs), where the
underlying polynomials are represented using Mathlib's noncomputable types `Polynomial` and
`MvPolynomial`. See `SingleRound.lean` for a single round of the protocol, and the definition of the
sum-check relations.

The oracle verifier computes only with the sent univariate messages.
`Sumcheck.Impl.Computable.generalOracleProver` implements the honest prover with an exact
refinement to the semantic protocol.

## Protocol Specification

The sum-check protocol is parameterized by the following:
- `R`: the underlying commutative semiring (for soundness, finite with `IsDomain R`)
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

* [Lund, C., Fortnow, L., Karloff, H., and Nisan, N., *Algebraic methods for interactive
    proof systems*][LFKN92]
* [Bosshard, A.G., Bootle, J., and Sprenger, C., *Formal Verification of the Sumcheck Protocol*]
    [BBS24]

-/

@[expose] public section

namespace Sumcheck

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

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

/-- Every sent sum-check polynomial uses the univariate evaluation interface. -/
instance instOracleInterfaceMessagePSpec : ∀ i, OracleInterface ((pSpec R deg n).Message i) :=
  inferInstanceAs (∀ i, OracleInterface ((ProtocolSpec.seqCompose
    (fun _ : Fin n => SingleRound.pSpec R deg)).Message i))

instance instOracleInterfaceMessageStep (rounds : ℕ) :
    ∀ i, OracleInterface (((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message i) :=
  instOracleInterfaceMessageAppend

-- TODO: the input statement should not mention sum-check challenges at all (currently it does,
-- initial challenge vector is empty). We can compose with a `ReduceClaim` (oracle) reduction to get
-- the correct input statement type

/-- The input statement for the (full) sum-check protocol, which contains only the target sum value
-/
@[reducible, simp]
def StmtIn := R

variable [DecidableEq R] [SampleableType R]

/-- The ordinary sum-check verifier materializes its polynomial oracles using mathematical
evaluation, which is noncomputable for Mathlib polynomials. -/
@[reducible]
noncomputable def verifier :
    Verifier oSpec (StatementRound R n 0 × (∀ i, OracleStatement R n deg i))
    (StatementRound R n (.last n) × (∀ i, OracleStatement R n deg i)) (pSpec R deg n) :=
  Verifier.seqCompose (oSpec := oSpec)
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.verifier R n deg D oSpec)

/-- Retype a round computation to its sent-message oracle. -/
def messageOnlyRoundProgram {α : Type} :
    (oa : OracleComp (oSpec + ([OracleStatement R n deg]ₒ +
      [(SingleRound.pSpec R deg).Message]ₒ)) α) →
    AllQueriesSatisfy oa (fun q => ∃ j, q = Sum.inr (Sum.inr j)) →
    OracleComp [(SingleRound.pSpec R deg).Message]ₒ α
  | .pure x, _ => pure x
  | .queryBind (Sum.inl q) next, h => False.elim (by
      obtain ⟨⟨j, hj⟩, _⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 h
      cases hj)
  | .queryBind (Sum.inr (Sum.inl q)) next, h => False.elim (by
      obtain ⟨⟨j, hj⟩, _⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 h
      cases hj)
  | .queryBind (Sum.inr (Sum.inr q)) next, h =>
      liftM (OracleSpec.query (spec := [(SingleRound.pSpec R deg).Message]ₒ) q) >>= fun answer =>
        messageOnlyRoundProgram (next answer)
          (((allQueriesSatisfy_query_bind_iff _ _ _).1 h).2 answer)

omit [DecidableEq R] [SampleableType R] in
/-- Lifting the restricted round program restores the original program. -/
private theorem messageOnlyRoundProgram_lift {α : Type}
    (oa : OracleComp (oSpec + ([OracleStatement R n deg]ₒ +
      [(SingleRound.pSpec R deg).Message]ₒ)) α)
    (h : AllQueriesSatisfy oa (fun q => ∃ j, q = Sum.inr (Sum.inr j))) :
    OracleComp.liftComp (messageOnlyRoundProgram R deg n oSpec oa h)
      (oSpec + ([OracleStatement R n deg]ₒ + [(SingleRound.pSpec R deg).Message]ₒ)) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q next ih =>
      obtain ⟨⟨j, rfl⟩, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 h
      change OracleComp.liftComp (liftM (OracleSpec.query
        (spec := [(SingleRound.pSpec R deg).Message]ₒ) j) >>= fun answer =>
        messageOnlyRoundProgram R deg n oSpec (next answer) (hn answer)) _ = _
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_liftM_query]
      congr 1
      funext answer
      exact ih answer (hn answer)

/-- Embed a round's message queries in the prefix of a sum-check transcript. -/
def leftMessageQuery (rounds : ℕ) :
    QueryImpl [(SingleRound.pSpec R deg).Message]ₒ
      (OracleComp [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ) :=
  fun ⟨i, q⟩ => by
    have hType : (SingleRound.pSpec R deg).Message i =
        ((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message (MessageIdx.inl i) := by
      simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
    exact OracleVerifier.queryAlongHEq inferInstance inferInstance hType (message_interface_inl i)
      (fun point => liftM (OracleSpec.query
        (spec := [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ)
        ⟨MessageIdx.inl i, point⟩)) q

/-- Embed the remaining message queries in the suffix of a sum-check transcript. -/
def rightMessageQuery (rounds : ℕ) :
    QueryImpl [(pSpec R deg rounds).Message]ₒ
      (OracleComp [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ) :=
  fun ⟨i, q⟩ => by
    have hType : (pSpec R deg rounds).Message i =
        ((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message (MessageIdx.inr i) := by
      simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
    exact OracleVerifier.queryAlongHEq inferInstance inferInstance hType (message_interface_inr i)
      (fun point => liftM (OracleSpec.query
        (spec := [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ)
        ⟨MessageIdx.inr i, point⟩)) q

/-- Compose round programs using only the sent univariate-polynomial oracles. -/
def oracleVerifierProgram {rounds : ℕ} (S : Fin (rounds + 1) → Type)
    (V : (i : Fin rounds) → S i.castSucc → (SingleRound.pSpec R deg).Challenges →
      OptionT (OracleComp [(SingleRound.pSpec R deg).Message]ₒ) (S i.succ)) :
    S 0 → (pSpec R deg rounds).Challenges →
      OracleComp [(pSpec R deg rounds).Message]ₒ (Option (S (Fin.last rounds))) :=
  match rounds with
  | 0 => fun stmt _ => pure (some stmt)
  | rounds + 1 => fun stmt
      (challenges : ((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Challenges) =>
    (simulateQ (leftMessageQuery R deg rounds) (V 0 stmt challenges.fst).run >>= fun next =>
      match next with
      | some next => simulateQ (rightMessageQuery R deg rounds)
          (oracleVerifierProgram (S ∘ Fin.succ) (fun i => V i.succ) next challenges.snd)
      | none => pure none :
      OracleComp [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ
        (Option (S (Fin.last (rounds + 1)))))

omit [DecidableEq R] [SampleableType R] in
/-- The message-only fold implements ordinary sequential oracle verification. -/
private theorem oracleVerifierProgram_lift {rounds : ℕ} (S : Fin (rounds + 1) → Type)
    (V : (i : Fin rounds) → OracleVerifier oSpec (S i.castSucc) (OracleStatement R n deg)
      (S i.succ) (OracleStatement R n deg) (SingleRound.pSpec R deg))
    (hV : ∀ i stmt challenges, AllQueriesSatisfy ((V i).verify stmt challenges).run
      (fun q => ∃ j, q = Sum.inr (Sum.inr j)))
    (stmt : S 0) (challenges : (pSpec R deg rounds).Challenges) :
    OracleComp.liftComp ((oracleVerifierProgram R deg S (fun i s c => OptionT.mk
      (messageOnlyRoundProgram R deg n oSpec ((V i).verify s c).run (hV i s c)))
        stmt challenges))
      (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg rounds).Message]ₒ)) =
      ((OracleVerifier.seqCompose S (fun _ => OracleStatement R n deg) V).verify
        stmt challenges).run := by
  have htransport {A B : Type} (OA : OracleInterface A) (OB : OracleInterface B)
      (hType : A = B) (hInterface : HEq OA OB) {ι₁ ι₂ : Type}
      {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
      [MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]
      (impl : (q : OB.Query) → OracleComp spec₁ (OB.Response q)) (q : OA.Query) :
      OracleComp.liftComp (OracleVerifier.queryAlongHEq OA OB hType hInterface impl q) spec₂ =
        OracleVerifier.queryAlongHEq OA OB hType hInterface
          (fun q => OracleComp.liftComp (impl q) spec₂) q := by
    cases hType
    cases eq_of_heq hInterface
    rfl
  have hleft (k : ℕ) (q : [(SingleRound.pSpec R deg).Message]ₒ.Domain) :
      OracleComp.liftComp (leftMessageQuery R deg k q)
        (oSpec + ([OracleStatement R n deg]ₒ +
          [((SingleRound.pSpec R deg) ++ₚ pSpec R deg k).Message]ₒ)) =
        messageQueryInl (oSpec := oSpec) (OStmt₁ := OracleStatement R n deg)
          (pSpec₁ := SingleRound.pSpec R deg) (pSpec₂ := pSpec R deg k) q := by
    rcases q with ⟨i, point⟩
    dsimp only [leftMessageQuery, messageQueryInl]
    exact htransport _ _ _ _ _ _
  have hright (k : ℕ) (q : [(pSpec R deg k).Message]ₒ.Domain) :
      OracleComp.liftComp (rightMessageQuery R deg k q)
        (oSpec + ([OracleStatement R n deg]ₒ +
          [((SingleRound.pSpec R deg) ++ₚ pSpec R deg k).Message]ₒ)) =
        messageQueryInr (oSpec := oSpec) (OStmt₁ := OracleStatement R n deg)
          (pSpec₁ := SingleRound.pSpec R deg) (pSpec₂ := pSpec R deg k) q := by
    rcases q with ⟨i, point⟩
    dsimp only [rightMessageQuery, messageQueryInr]
    exact htransport _ _ _ _ _ _
  have hprefix (k : ℕ) {α : Type} (oa : OracleComp [(SingleRound.pSpec R deg).Message]ₒ α) :
      OracleComp.liftComp (simulateQ (leftMessageQuery R deg k) oa)
        (oSpec + ([OracleStatement R n deg]ₒ +
          [((SingleRound.pSpec R deg) ++ₚ pSpec R deg k).Message]ₒ)) =
      simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OracleStatement R n deg)
        (pSpec₁ := SingleRound.pSpec R deg) (pSpec₂ := pSpec R deg k))
        (OracleComp.liftComp oa
          (oSpec + ([OracleStatement R n deg]ₒ + [(SingleRound.pSpec R deg).Message]ₒ))) := by
    induction oa using OracleComp.inductionOn with
    | pure x => rfl
    | query_bind q next ih =>
        simp only [simulateQ_bind, OracleComp.liftComp_bind, simulateQ_spec_query,
          OracleComp.liftComp_liftM_query]
        simp only [firstQueryImpl, QueryImpl.simulateQ_add_add_liftM_query_right,
          QueryImpl.add_apply_inr]
        rw [hleft]
        exact bind_congr ih
  have hsuffix (k : ℕ) {S₁ S₂ : Type}
      (W : OracleVerifier oSpec S₁ (OracleStatement R n deg) S₂ (OracleStatement R n deg)
        (SingleRound.pSpec R deg)) (c : (SingleRound.pSpec R deg).Challenges)
      {α : Type} (oa : OracleComp [(pSpec R deg k).Message]ₒ α) :
      OracleComp.liftComp (simulateQ (rightMessageQuery R deg k) oa)
        (oSpec + ([OracleStatement R n deg]ₒ +
          [((SingleRound.pSpec R deg) ++ₚ pSpec R deg k).Message]ₒ)) =
      simulateQ (secondQueryImpl (pSpec₂ := pSpec R deg k) W c)
        (OracleComp.liftComp oa
          (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg k).Message]ₒ))) := by
    induction oa using OracleComp.inductionOn with
    | pure x => rfl
    | query_bind q next ih =>
        simp only [simulateQ_bind, OracleComp.liftComp_bind, simulateQ_spec_query,
          OracleComp.liftComp_liftM_query]
        simp only [secondQueryImpl, QueryImpl.simulateQ_add_add_liftM_query_right,
          QueryImpl.add_apply_inr]
        rw [hright]
        exact bind_congr ih
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [OracleVerifier.seqCompose_succ]
      change ((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Challenges at challenges
      change S ((0 : Fin (rounds + 1)).castSucc) at stmt
      simp only [oracleVerifierProgram, OracleVerifier.append]
      have hraw : OracleComp.liftComp
        (simulateQ (leftMessageQuery R deg rounds)
          (messageOnlyRoundProgram R deg n oSpec ((V 0).verify stmt challenges.fst).run
            (hV 0 stmt challenges.fst)) >>= fun next =>
          match next with
          | some next => simulateQ (rightMessageQuery R deg rounds)
              (oracleVerifierProgram R deg (S ∘ Fin.succ) (fun i s c => OptionT.mk
                (messageOnlyRoundProgram R deg n oSpec ((V i.succ).verify s c).run
                  (hV i.succ s c))) next challenges.snd)
          | none => pure none)
        (oSpec + ([OracleStatement R n deg]ₒ +
          [((SingleRound.pSpec R deg) ++ₚ pSpec R deg rounds).Message]ₒ)) =
        (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OracleStatement R n deg)
          (pSpec₁ := SingleRound.pSpec R deg) (pSpec₂ := pSpec R deg rounds))
            ((V 0).verify stmt challenges.fst).run >>= fun next =>
          match next with
          | some next => simulateQ (secondQueryImpl (pSpec₂ := pSpec R deg rounds)
              (V 0) challenges.fst)
              ((OracleVerifier.seqCompose (S ∘ Fin.succ)
                (fun _ => OracleStatement R n deg) (fun i => V i.succ)).verify
                  next challenges.snd).run
          | none => pure none) := by
        rw [OracleComp.liftComp_bind, hprefix, messageOnlyRoundProgram_lift]
        apply bind_congr
        intro next
        cases next with
        | none => rfl
        | some next =>
            rw [hsuffix, ih]
      dsimp only [OptionT.run, Bind.bind, OptionT.instMonad, OptionT.bind, OptionT.mk] at hraw ⊢
      apply Eq.trans hraw
      congr 1
      funext next
      cases next <;> rfl

/-- The oracle verifier for the full sum-check protocol. It computes only with the sent messages. -/
@[reducible]
def oracleVerifier : OracleVerifier oSpec (StatementRound R n 0) (OracleStatement R n deg)
    (StatementRound R n (.last n)) (OracleStatement R n deg) (pSpec R deg n) where
  verify stmt challenges := OptionT.mk <| OracleComp.liftComp
    (oracleVerifierProgram R deg (StatementRound R n) (fun i s c => OptionT.mk
      (messageOnlyRoundProgram R deg n oSpec
        ((SingleRound.oracleVerifier R n deg D oSpec i).verify s c).run
        (SingleRound.oracleVerifier_only_message_queries R n deg D oSpec i s c)))
      stmt challenges)
    (oSpec + ([OracleStatement R n deg]ₒ + [(pSpec R deg n).Message]ₒ))
  outputOracle := .inl ⟨Function.Embedding.inl, fun _ => rfl, fun _ => HEq.rfl⟩

/-- The executable verifier has the same query program as sequential round verification. -/
theorem oracleVerifier_verify_eq_seqCompose
    (stmt : StatementRound R n 0) (challenges : (pSpec R deg n).Challenges) :
    ((oracleVerifier R deg D n oSpec).verify stmt challenges).run =
      ((OracleVerifier.seqCompose (StatementRound R n) (fun _ => OracleStatement R n deg)
        (SingleRound.oracleVerifier R n deg D oSpec)).verify stmt challenges).run :=
  oracleVerifierProgram_lift R deg n oSpec (StatementRound R n)
    (SingleRound.oracleVerifier R n deg D oSpec)
    (SingleRound.oracleVerifier_only_message_queries R n deg D oSpec) stmt challenges

/-- The full sum-check verifier queries only the univariate polynomials sent in
the rounds.  It never queries the input multivariate polynomial. -/
theorem sumcheck_verifier_no_inputPolynomial_queries
    (stmt : StatementRound R n 0) (challenges : (pSpec R deg n).Challenges) :
    AllQueriesSatisfy ((oracleVerifier R deg D n oSpec).verify stmt challenges).run
      (fun q => ∃ i, q = Sum.inr (Sum.inr i)) := by
  rw [oracleVerifier_verify_eq_seqCompose]
  exact OracleVerifier.seqCompose_only_message_queries (StatementRound R n)
    (fun _ => OracleStatement R n deg) (SingleRound.oracleVerifier R n deg D oSpec)
    (SingleRound.oracleVerifier_only_message_queries R n deg D oSpec) stmt challenges

/-- Sum-check retains the original input polynomial as its output oracle. -/
@[simp]
private theorem seqCompose_materializeOutput
    (challenges : (pSpec R deg n).Challenges)
    (oStmt : ∀ i, OracleStatement R n deg i) (messages : (pSpec R deg n).Messages) :
    (OracleVerifier.seqCompose (StatementRound R n) (fun _ => OracleStatement R n deg)
      (SingleRound.oracleVerifier R n deg D oSpec)).materializeOutput
        challenges oStmt messages = oStmt := by
  exact OracleVerifier.seqCompose_materializeOutput (StatementRound R n)
    (OracleStatement R n deg) (SingleRound.oracleVerifier R n deg D oSpec)
    (fun _ _ _ _ => rfl) challenges oStmt messages

/-- Sum-check retains its original input polynomial as its output oracle. -/
@[simp]
theorem oracleVerifier_materializeOutput
    (challenges : (pSpec R deg n).Challenges)
    (oStmt : ∀ i, OracleStatement R n deg i) (messages : (pSpec R deg n).Messages) :
    (oracleVerifier R deg D n oSpec).materializeOutput challenges oStmt messages = oStmt := rfl

/-- Materializing the executable verifier agrees with sequential round verification. -/
theorem oracleVerifier_toVerifier_eq_seqCompose :
    (oracleVerifier R deg D n oSpec).toVerifier =
      (OracleVerifier.seqCompose (StatementRound R n) (fun _ => OracleStatement R n deg)
        (SingleRound.oracleVerifier R n deg D oSpec)).toVerifier := by
  ext ⟨stmt, oStmt⟩ transcript
  simp only [OracleVerifier.toVerifier, oracleVerifier_materializeOutput,
    seqCompose_materializeOutput]
  congr 4
  exact oracleVerifier_verify_eq_seqCompose R deg D n oSpec stmt transcript.challenges

/-- The sum-check reduction with semantic polynomial projection in its honest prover.
`Sumcheck.Impl.Computable.generalOracleProver` supplies an executable refinement. -/
@[reducible]
noncomputable def reduction : Reduction oSpec
    (StatementRound R n 0 × ∀ i, OracleStatement R n deg i) Unit
    (StatementRound R n (.last n) × ∀ i, OracleStatement R n deg i) Unit
    (pSpec R deg n) :=
  Reduction.seqCompose (oSpec := oSpec)
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (Wit := fun _ => Unit)
    (pSpec := fun _ => SingleRound.pSpec R deg)
    (SingleRound.reduction R n deg D oSpec)

/-- The oracle sum-check reduction. Its semantic honest prover materializes polynomial projections;
`Sumcheck.Impl.Computable.generalOracleProver` computes the same messages and outputs. -/
@[reducible]
noncomputable def oracleReduction : OracleReduction oSpec
    (StatementRound R n 0) (OracleStatement R n deg) Unit
    (StatementRound R n (.last n)) (OracleStatement R n deg) Unit
    (pSpec R deg n) where
  prover := Prover.seqCompose
    (fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (fun _ => Unit) (fun i => (SingleRound.oracleReduction R n deg D oSpec i).prover)
  verifier := oracleVerifier R deg D n oSpec

omit [SampleableType R] in
@[simp]
lemma reduction_verifier_eq_verifier :
    (reduction R deg D n oSpec).verifier = verifier R deg D n oSpec := by
  rfl

@[simp]
lemma oracleReduction_verifier_eq_oracleVerifier :
    (oracleReduction R deg D n oSpec).verifier = oracleVerifier R deg D n oSpec := by
  rfl

/-- Materializing the oracle protocol gives the ordinary sum-check reduction. -/
@[simp]
theorem oracleReduction_toReduction :
    (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec := by
  apply Reduction.ext
  · rfl
  · change (oracleVerifier R deg D n oSpec).toVerifier = verifier R deg D n oSpec
    rw [oracleVerifier_toVerifier_eq_seqCompose, OracleVerifier.seqCompose_toVerifier]
    congr 1
    funext i
    exact SingleRound.oracleVerifier_eq_verifier R n deg D oSpec i

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

open NNReal

/-- Perfect completeness for the (full) sum-check protocol -/
theorem reduction_perfectCompleteness :
    (reduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) :=
  Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (fun i => StatementRound R n i × ∀ j, OracleStatement R n deg j)
    (fun _ => Unit) init impl (relationRound R n deg D)
    (SingleRound.reduction R n deg D oSpec)
    (fun _ => inferInstance) (SingleRound.verifierGuardedForm R n deg D oSpec)
    (fun i s => SingleRound.reduction_perfectCompleteness (init := pure s) i)

/-- Perfect completeness of the full oracle sum-check protocol. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n)) := by
  change (oracleReduction R deg D n oSpec).toReduction.perfectCompleteness init impl _ _
  rw [oracleReduction_toReduction]
  exact reduction_perfectCompleteness R deg D n oSpec

/-- The full oracle verifier retains the checks of every sum-check round.
This semantic guarded form uses the noncomputable polynomial interfaces of the round lifts. -/
noncomputable def oracleVerifierGuardedForm :
    (oracleVerifier R deg D n oSpec).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofEq (oracleVerifier_toVerifier_eq_seqCompose R deg D n oSpec).symm <|
  OracleVerifier.seqComposeGuardedForm (StatementRound R n)
    (fun _ => OracleStatement R n deg) (fun i =>
      Verifier.GuardedForm.ofEq (SingleRound.oracleVerifier_eq_verifier R n deg D oSpec i).symm
        (SingleRound.verifierGuardedForm R n deg D oSpec i))

/-- Knowledge soundness with error `deg / |R|` at every challenge. -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R deg D n oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n))
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_toVerifier_eq_seqCompose]
  exact OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded
    (StatementRound R n) (fun _ => OracleStatement R n deg) (fun _ => Unit)
    (relationRound R n deg D) (SingleRound.oracleVerifier R n deg D oSpec)
    (fun i => Verifier.GuardedForm.ofEq
      (SingleRound.oracleVerifier_eq_verifier R n deg D oSpec i).symm
      (SingleRound.verifierGuardedForm R n deg D oSpec i))
    (fun _ _ => (deg : ℝ≥0) / Fintype.card R)
    (fun i => SingleRound.oracleVerifier_rbrKnowledgeSoundness i)

/-- Ordinary knowledge soundness with the sum of the per-challenge errors. -/
theorem oracleVerifier_knowledgeSoundness [Fintype R] [IsDomain R] :
    (oracleVerifier R deg D n oSpec).knowledgeSoundness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (.last n))
      (∑ _ : (pSpec R deg n).ChallengeIdx, (deg : ℝ≥0) / Fintype.card R) :=
  OracleVerifier.knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded
    (oracleVerifierGuardedForm R deg D n oSpec)
    (oracleVerifier_rbrKnowledgeSoundness R deg D n oSpec)

end Spec

end Sumcheck
