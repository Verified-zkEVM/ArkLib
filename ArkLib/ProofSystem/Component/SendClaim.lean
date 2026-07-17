/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SeqCompose

/-!
  # Simple Oracle Reduction - SendClaim

  The prover sends a **claim** (a single oracle message) to the verifier, computed from the input
  (combined) statement by a function `f`. This is the "prover-computed message" building block, e.g.
  the Greyhound [NS24] / Hachi [NOZ26] first message `v := D ŵ` or the Sumcheck round polynomial
  `q`.

  - There is no witness (`Witness = Unit`).
  - The prover sends a message of type `Message` (with an `OracleInterface`), namely `f stmt oStmt`.
  - The **verifier is a pure pass-through** (`verify := fun stmt _ => pure stmt`): the claim is
    *not* checked by a runtime `guard`; the check lives in the output relation `toORelOut` (the
    predicate `P` over statement / oracle statements / message).
  - The output oracle statements are the input oracle statements together with the sent message,
    `OStatement ⊕ᵥ (fun _ : Fin 1 => Message)`.

  ## Security

  The verifier is pure and has no challenge rounds, hence **coordinate-wise special sound**
  (`oracleVerifier_coordinateWiseSpecialSound`) for any `CWSSStructure`, via the no-challenge bridge
  `OracleVerifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx`. The extractor is trivial
  (`e := fun _ _ => ()`, there is no witness) and the output relation `toORelOut relIn P` refines
  the input relation by the claim predicate `P`, so accepting into its language forces the input
  into `relIn`. These results are `sorryAx`-free. This mirrors `SendSingleWitness` (the special
  case `Message := Witness`) on the verifier side.

  Perfect completeness — that an honest prover's claim `f stmt oStmt` lands in `toORelOut` whenever
  the input is in `relIn` and `f` respects `P` — is deferred: it needs the same all-pure
  oracle-reduction completeness reasoning as `SendSingleWitness.oracleReduction_completeness`, and
  is orthogonal to the CWSS target here. This design supersedes the previous effectful-verifier one
  (whose completeness proof no longer applies).

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec Function Equiv

namespace SendClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) [∀ i, OracleInterface (OStatement i)]
  (Message : Type) [OracleInterface Message]

/-- One prover→verifier message carrying the claim of type `Message`. -/
@[reducible, simp]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Message]⟩

/-- `SendClaim` is a single `P_to_V` message, so it has no challenge rounds. This makes its
coordinate-wise special soundness reduce to the no-challenge bridge. -/
instance instIsEmptyChallengeIdx : IsEmpty (pSpec Message).ChallengeIdx :=
  ⟨fun ⟨0, h⟩ => nomatch h⟩

variable (f : Statement → (∀ i, OStatement i) → Message)

/-- The oracle prover for `SendClaim`: it computes the claim `f stmt oStmt` and sends it as the only
oracle message, exposing it (together with the input oracle statements) as the output oracles. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Message)) Unit
    (pSpec Message) where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, oStmt⟩ => pure (f stmt oStmt, ⟨stmt, oStmt⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt⟩ => pure (⟨stmt, Sum.rec oStmt (fun _ => f stmt oStmt)⟩, ())

/-- The oracle verifier for `SendClaim` is a **pure pass-through**: it returns the statement and
exposes the input oracle statements together with the prover's message as the output oracles. The
claim predicate is enforced in `toORelOut`, not at runtime, keeping the verifier `IsPure`. -/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Message))
    (pSpec Message) where
  verify := fun stmt _ => pure stmt
  embed := .sumMap (.refl _)
    <| Equiv.toEmbedding
    <| .symm (subtypeUnivEquiv (by aesop))
  hEq := by
    intro i; rcases i with j | j
    · rfl
    · fin_cases j; rfl

/-- The oracle reduction for `SendClaim`. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Message)) Unit
    (pSpec Message) where
  prover := oracleProver oSpec Statement OStatement Message f
  verifier := oracleVerifier oSpec Statement OStatement Message

variable {Statement} {OStatement} {Message}

/-- The pure pass-through oracle verifier's underlying non-oracle verifier returns the statement
together with the output oracle statements (input oracles at `inl`, the message at `inr 0`). -/
theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (pSpec Message).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement Message).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, Sum.rec oStmt (fun i => match i with | 0 => tr 0)⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  rw [show simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
        (pure stmt : OptionT (OracleComp _) Statement)
      = (pure stmt : OptionT (OracleComp oSpec) Statement) from rfl, pure_bind]
  congr 1
  congr 1
  funext idx
  rcases idx with j | j
  · rfl
  · fin_cases j; rfl

/-- The `SendClaim` oracle verifier is pure, discharging the deterministic-left hypothesis of the
CWSS binary append. -/
instance instIsPure :
    (oracleVerifier oSpec Statement OStatement Message).toVerifier.IsPure :=
  ⟨fun p tr => ⟨p.1, Sum.rec p.2 (fun i => match i with | 0 => tr 0)⟩,
   fun ⟨_, _⟩ _ => oracleVerifier_toVerifier_run (oSpec := oSpec)⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set ((Statement × ∀ i, OStatement i) × Unit))
  (P : Statement → (∀ i, OStatement i) → Message → Prop)

/-- The output relation of `SendClaim`: the input relation (read off the pass-through oracles at
`inl`) together with the claim predicate `P` applied to the statement, the input oracles, and the
sent message (the oracle at `inr 0`). Because the verifier is a pure pass-through, "acceptance" is
membership in `toORelOut.language`; the `P` check is enforced here rather than at runtime. -/
@[reducible, simp]
def toORelOut :
    Set ((Statement × (∀ i, (Sum.elim OStatement fun _ : Fin 1 => Message) i)) × Unit) :=
  setOf (fun ⟨⟨stmt, oStmtAndMsg⟩, _⟩ =>
    (⟨⟨stmt, fun i => oStmtAndMsg (Sum.inl i)⟩, ()⟩ ∈ relIn) ∧
      P stmt (fun i => oStmtAndMsg (Sum.inl i)) (oStmtAndMsg (Sum.inr 0)))

/-- **Coordinate-wise special soundness of `SendClaim`.** The verifier is a pure pass-through with
no challenge rounds, so CWSS collapses (via the oracle no-challenge bridge) to a transcript-level
obligation. The extractor is trivial (`e := fun _ _ => ()`, there is no witness); since the output
oracle statements at `inl` are the input oracles unchanged and `toORelOut relIn P` refines `relIn`,
accepting into `toORelOut.language` forces the input into `relIn`. Holds for any `D`. -/
theorem oracleVerifier_coordinateWiseSpecialSound (D : CWSSStructure (pSpec Message)) :
    (oracleVerifier oSpec Statement OStatement Message).coordinateWiseSpecialSound init impl D
      relIn (toORelOut relIn P) := by
  refine OracleVerifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx init impl D
    (oracleVerifier oSpec Statement OStatement Message) relIn (toORelOut relIn P)
    (fun _ _ => ()) ?_
  rintro ⟨stmt, oStmt⟩ tr hAcc
  have hmem := Verifier.mem_of_pure_accepting init impl
    (oracleVerifier oSpec Statement OStatement Message).toVerifier ⟨stmt, oStmt⟩ tr
    (toORelOut relIn P).language _ (oracleVerifier_toVerifier_run (oSpec := oSpec)) hAcc
  obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
  exact hu.1

end SendClaim
