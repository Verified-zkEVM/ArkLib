/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ArkLib.ToVCVio.OracleComp.RbrGame

/-!
# Toy problem oracle reduction (ABF26 Construction 6.2)

We describe the ABF26 §6 toy-problem IOR as an `OracleReduction` over
ArkLib's `OracleReduction` framework, following the conventions used by
`ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` and
`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`:

* `Statement`, `OracleStatement`, `Witness`, `OutputStatement` — input /
  oracle / witness / output type aliases (all `@[reducible]`).
* `pSpec` — the 3-round `ProtocolSpec` (`V → P` γ, `P → V` g, `V → P`
  spot-checks).
* `OracleInterface`, `Inhabited`, `Fintype` instances for the messages
  and challenges of `pSpec`.
* `inputRelationFor` / `outputRelationFor` — IOR input/output relations
  (Definitions 6.1 and 6.3, in IOR shape, pinned to the verifier's fixed
  encoder).
* `accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete.
Completeness (C6.2, `oracleReduction_perfectCompleteness`) and
round-by-round knowledge soundness (L6.8,
`protocol62_rbrKnowledgeSound`) are **fully proven** here. Plain
knowledge soundness (L6.6, `protocol62_knowledgeSound`) is **fully
proven** in the sibling file `Spec/KnowledgeSoundness.lean`, with the
convex-combination error
`(1-δ)^t + (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|)·(1 - (1-δ)^t)`, which is `≤` the
sum `(ε_mca + |Λ|/|F|) + (1-δ)^t` stated in [ABF26] Lemma 6.6 (current `.tex`,
~line 2215) and so is at least as strong. (An earlier draft printed the unsound
`max` of the two terms; it was author-confirmed and corrected to the sum.) The
per-round game bounds proven in this file
(`gamma_round_game_bound`, `spotcheck_round_game_bound`) are shared by
both the L6.8 and L6.6 proofs.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → F`. The protocol runs:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`. In the
     honest case `g = M₁ + γ · M₂` is the combination of the underlying
     messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier accepts iff `⟨g, v⟩ = μ₁ + γ · μ₂` (linear-constraint
check) and for every `j ∈ Fin t`, `encode(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`
(spot-check).

## Paper ↔ framework mapping

How each step of Construction 6.2 lands on an ArkLib / VCV-io primitive:

* `γ ←$ F` (combination randomness) ↦ `pSpec` round 0 (`.V_to_P`); the
  security games sample it via the `SampleableType F` instance on the
  challenge type.
* prover claim `ḡ ∈ F^k` ↦ `pSpec` round 1 (`.P_to_V`), with
  `OracleInterface.instDefault` as its message-oracle interface.
* spot-check positions `x₁, …, xₜ` ↦ `pSpec` round 2 (`.V_to_P`), of
  type `Fin t → ι`.
* oracle access to `f₁, f₂` ↦ `OracleStatement` queried via `queryF`,
  routed through the per-index `OracleInterface` instances.
* the §6.1 decision predicate ↦ `accepts`.
* verifier query routing ↦ `OracleInterface.simOracle2` / `simulateQ`
  (VCV-io's query-simulation semantics).
* completeness game ↦ `OracleReduction.perfectCompleteness`.
* knowledge-soundness games (paper App A.1, Defs A.2 / A.4 / A.5) ↦
  `OracleVerifier.knowledgeSoundness` / `OracleVerifier.rbrKnowledgeSoundness`.
  Two caveats: extraction **time** (the paper's `O(enc + ecor)` extractor
  cost) is outside ArkLib's cost-free model, and the verifier's query
  complexity (`2t + 1`) is documented, not enforced
  (`OracleVerifier.numQueries` is upstream-sorried).

## Codeword alphabet `A` (folding-generic)

The paper's Construction 6.1/6.2 inputs are `f : [n] → F^s` for a folding
parameter `s` (and the §6.3 tables sweep `s = 2^0, …, 2^12`). This
formalization is generic over the codeword alphabet `A` (an `F`-module):
words are `ι → A`, with `A = F` the scalar `s = 1` interleaved case
(`Impl/IRS.lean`) and `A = Fin s → F` the genuine `s > 1` folded case
(`Impl/FRS.lean`, e.g. `s = 2^5`). The relative Hamming metric is over `A`
(one symbol = one `A`-coordinate), which is exactly the right folded metric —
reindexing `ι := [n] × [s]` over a scalar alphabet would **not** recover it,
hence the genuine `F`-module `A` rather than a flattened index set. The
challenge `γ`, constraint vector `v`, and constraint values `μ` stay scalar
(`F`); only the codeword values and the encoder `(Fin k → F) →ₗ[F] (ι → A)`
range over `A`. Combination of codeword values is the module action
`f₀ + γ • f₁` (it specializes to `f₀ + γ · f₁` when `A = F`).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal ProbabilityTheory
open Probability

-- `[Fintype A]`/`[DecidableEq A]` are used inside the bodies of the code-theoretic
-- terms (`epsMCA`, `interleavedCodeSet`, the `accepts` decidability) but do not
-- surface in the alphabet-generic lemma types; suppress the `unused…InType` linter
-- file-wide (the same toy idiom used in `SoundnessBounds.lean`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `relaxedRelationFor`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
variable (k t : ℕ)

/-- Input (explicit) statement of Construction 6.2: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of Construction 6.2: the two purported codewords
`f₁, f₂ : ι → F`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι A : Type) : Fin 2 → Type := fun _ ↦ ι → A

instance : ∀ i, OracleInterface (OracleStatement ι A i) :=
  fun _ ↦ inferInstance

/-- Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose
encodings are the oracle codewords `f₁, f₂`. -/
@[reducible]
def Witness : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a yes/no test — accept (return `()`) or
short-circuit to `none` via `OptionT`. -/
@[reducible]
def OutputStatement : Type := Unit

/-- Output oracle statement: the IOR has no output oracle component. -/
@[reducible]
def OutputOracleStatement : (Fin 0) → Type := nofun

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for Construction 6.2: three rounds, in the
order

    V → P  (γ : F)            -- combination randomness
    P → V  (g : Fin k → F)    -- combined message claim
    V → P  (xs : Fin t → ι)   -- spot-check positions.

Marked `@[reducible]` so per-round type access `pSpec.Type i` reduces
in client code (cf. FRI / Sumcheck single-round specs). -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault
  | ⟨2, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The challenges of the toy-problem `pSpec` are `SampleableType` when
the underlying field `F` and the codeword index `ι` are. This is needed
to instantiate the (round-by-round) knowledge-soundness games, which
sample challenges from the protocol's challenge spaces. -/
instance [SampleableType F] [SampleableType ι] :
    ∀ j, SampleableType ((pSpec (ι := ι) (F := F) k t).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => (inferInstance : SampleableType (Fin t → ι))

/-- The §6.1 decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def accepts (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι A i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ • f 1 (xs j)

/-- The IOR-shaped **fixed-encoding** input relation (Definition 6.1).

`((v, μ₁, μ₂), (f₀, f₁)) ∈ inputRelationFor encode` with witness `M`
iff the oracle codewords are the `encode`-images of the witness messages
(`fᵢ = encode (M i)`) and the witness satisfies the linear constraint
(`⟨M i, v⟩ = μᵢ`). The encoding is the verifier's **fixed** `encode` (a plain
function, matching `oracleVerifier`), and the witness `M` is tied to the
statement — this is what the honest prover sends `g = M₀ + γ·M₁` against and
what `accepts_of_inputRelation` consumes.

This replaces the earlier existential-encoding form (`ToyProblem.relation`,
`∃ encode'`), under which honest completeness is unprovable / false: the honest
prover's `encode g` need not match `fᵢ = encode' (Mᵢ)` when `encode' ≠ encode`
(the same defect found for the L6.12 attack — see `ToyProblem.relationFor`). -/
def inputRelationFor (encode : (Fin k → F) → (ι → A)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι A i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, input.1.2 i = encode (input.2 i)) ∧
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j = ![input.1.1.2.1, input.1.1.2.2] i)

/-- The IOR-shaped **fixed-encoding** *relaxed* output relation (Definition 6.3).
The soundness statement of L6.6/6.8 is with respect to this: the verifier's
"accept" guarantee is that the input `(f₀, f₁)` is `δ`-close (on a common
agreement column set) to a valid instance `encode (M i)` for some constraint-
satisfying messages `M`. Uses the verifier's fixed plain `encode` (cf.
`ToyProblem.relaxedRelationFor`), and checks the witness component supplied by
the ArkLib knowledge extractor; this is a witness-bearing relation, not merely
language membership. -/
def outputRelationFor (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι A i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j =
      ![input.1.1.2.1, input.1.1.2.2] i) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i : Fin 2, ∀ j ∈ S, input.1.2 i j = encode (input.2 i) j

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelationFor` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Honest prover, verifier, and reduction

This section mirrors the `foldProver` / `foldVerifier` / `foldOracleReduction`
pattern in [`Fri/Spec/SingleRound.lean`](../../../Fri/Spec/SingleRound.lean).
Because `OracleStatement ι A i = ι → A` is a plain function (not an
oracle that needs the `OracleQuery` machinery), we use the **non-oracle**
`Prover` / `Verifier` / `Reduction` triple with the oracle codewords
threaded through the bundled input `StmtIn = Statement × (∀ i, OracleStatement i)`.
This is sound — it's the same shape produced by
`OracleReduction.toReduction` — and avoids the `embed` / `hEq`
plumbing. The `OracleProver` / `OracleVerifier` flavour (the target of
the completeness and soundness statements) follows in the next section.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]

/-- Honest prover for Construction 6.2. After receiving the combination
randomness `γ`, the prover sends `g := M 0 + γ · M 1` (point-wise on
`Fin k`). The spot-check positions `xs` are not used by the prover —
they only feed the verifier's spot-check at the end.

State machine (`PrvState : Fin 4 → Type`):
  * `PrvState 0` — initial: the bundled `(stmt, oStmt) × witness`.
  * `PrvState 1, 2, 3` — same plus the combination randomness `γ`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure ((), ())

/-- The §6.1 decision predicate is decidable: it's a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance accepts.instDecidable
    (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι A i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold accepts; infer_instance

/-- Honest verifier for Construction 6.2. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `accepts` holds for the supplied encoding.

Computable — `accepts` is decidable, so no `Classical.dec` is needed.
This mirrors FRI's `foldVerifier`, which is also a plain `def`. -/
def verifier (encode : (Fin k → F) → (ι → A)) :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      OutputStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    let g : Fin k → F := tr ⟨1, by decide⟩
    let xs : Fin t → ι := tr ⟨2, by decide⟩
    if accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for Construction 6.2: the package
`{prover, verifier}` over the bundled-input `Reduction` type. -/
def reduction (encode : (Fin k → F) → (ι → A)) :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := prover (ι := ι) (F := F) (k := k) (t := t)
  verifier := verifier (k := k) (t := t) encode

/-! ### Oracle-flavour prover, verifier, reduction

These are the `OracleProver` / `OracleVerifier` / `OracleReduction`
flavours of the same protocol, exposing `(f₁, f₂)` as oracle inputs
rather than bundling them into `StmtIn`. They match FRI/Sumcheck's
exact idiom and are necessary to make the *query complexity* of the
verifier explicit (`2t + 1` queries per execution: one for `g`, two
per spot-check).

The honest-completeness, knowledge-soundness, and round-by-round
knowledge-soundness lemmas below are all stated against these
oracle-flavour objects: completeness via
`OracleReduction.perfectCompleteness`, L6.6 via
`OracleVerifier.knowledgeSoundness`, and L6.8 via
`OracleVerifier.rbrKnowledgeSoundness`. The latter two are
definitionally `toVerifier.knowledgeSoundness` /
`toVerifier.rbrKnowledgeSoundness`, so the oracle-flavour statements
carry no extra proof burden over the bundled-input forms.

**Framework vacuity (KS) — RESOLVED 2026-06-11.** The historical trap —
`Verifier.knowledgeSoundness` admitted an always-failing `OptionT`
extractor that drove the bad-event probability to `0` — was fixed by
PR #569 (`fix/knowledge-soundness-failing-extractor`), now merged and
synced into this branch: extraction failure (`extractedWitIn? = none`)
is scored against the prover. The KS sorries below
(`protocol62_knowledgeSound`, and `simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean`) may be closed on their mathematical merits.
`Verifier.rbrKnowledgeSoundness` was never affected, so
`protocol62_rbrKnowledgeSound` is provable as-is (and is the natural
first target; KS then follows via the rbrKS → KS implication).
-/

/-- Same as `prover` but exposed at the `OracleProver` signature. The
underlying `Prover` is identical (after the `OracleProver` type-alias
unfolds to a `Prover` on bundled in/out types). The output is the
trivial `(((), nofun), ())` since the IOR has no output oracle
statements (`OutputOracleStatement : Fin 0 → Type`). -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι A) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure (((), nofun), ())

/-- Query helper: fetch the prover's combined-message claim `g`
(`pSpec` round 1 — the `P → V` direction). Mirrors FRI's `getConst`. -/
def queryG : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by simpa using ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryF (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι A]ₒ A :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι A]ₒ.Domain from ⟨i, (by simpa using x)⟩)

/-- Oracle verifier for Construction 6.2.

Queries the prover's message `g` once and the two oracle codewords
`f₁, f₂` at each of the `t` spot-check positions (query complexity:
`2t + 1`), then `guard (accepts …)` to decide.

`embed` and `hEq` are trivial — `OutputOracleStatement : Fin 0 → Type`
is empty, so the output-oracle family is vacuously a subset of input
oracles + prover messages. -/
def oracleVerifier (encode : (Fin k → F) → (ι → A)) :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι A)
      OutputStatement OutputOracleStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    let g : Fin k → F ← liftM <| queryG (ι := ι) (F := F) (k := k) (t := t)
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      let f₀ : A ← liftM <| queryF (ι := ι) (A := A) 0 (xs j)
      let f₁ : A ← liftM <| queryF (ι := ι) (A := A) 1 (xs j)
      guard (encode g (xs j) = f₀ + γ • f₁)
    pure ()
  embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
  hEq := fun i ↦ i.elim0

/-- Honest oracle reduction for Construction 6.2: the
`OracleProver` / `OracleVerifier` pair packaged as `OracleReduction`. -/
def oracleReduction (encode : (Fin k → F) → (ι → A)) :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι A) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := oracleProver (ι := ι) (F := F) (k := k) (t := t)
  verifier := oracleVerifier (k := k) (t := t) encode

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- The honest oracle verifier's body, simulated through `simOracle2` against the prover's
messages `msgs` and the input codewords `oStmt`, resolves to `pure (some ())` whenever the two
accept conditions hold for the supplied challenge `γ`, spot-check positions `xs`, and prover
message `g = msgs ⟨1, rfl⟩`:

  * `hAcc1`: the linear-constraint check `∑ j, g j · v j = μ₁ + γ · μ₂`, and
  * `hAcc2`: the per-spot-check `encode g (xs j) = f₀(xs j) + γ · f₁(xs j)`.

This is the monadic core of `oracleReduction_perfectCompleteness`: the residual support obligation
after the `Pr[…] = 1` goal is reduced via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
forces every honest-run output to be `some` of an accepting output, which this lemma certifies by
resolving each query (the prover claim `g` and the `2t` codeword reads) against `simOracle2` and
discharging both guards. The query/loop routing uses the staged `simulateQ`/`OptionT` toolkit
(`OracleComp.monadLift_liftM_OptionT`, `simulateQ_optionT_bind`/`_lift`,
`simulateQ_optionT_forIn_yield_pure_some`); the `change`/`conv` steps bridge the definitional —
but not syntactic — equalities between the elaborated verifier's `MonadLift`/`ForIn` instance
trees and the toolkit lemmas' canonical spellings. -/
lemma verifierBody_simulateQ_eq_pure
    (encode : (Fin k → F) → (ι → A))
    (oStmt : (i : Fin 2) → OracleStatement ι A i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι)
    (hAcc1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2)
    (hAcc2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
      = oStmt 0 (xs j) + γ • oStmt 1 (xs j)) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : A ← liftM (queryF (ι := ι) (A := A) 0 (xs j))
            let f₁ : A ← liftM (queryF (ι := ι) (A := A) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ • f₁) :
        OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (some ()) := by
  -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
  rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
      = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (A := A) i x) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) A)
      = OptionT.lift (liftM (queryF (ι := ι) (A := A) i x) :
          OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) A) from
        fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
  -- Push `simulateQ` through the OptionT bind / lift / map structure.
  simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
    queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
  -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
  conv_lhs =>
    enter [1, 1]
    change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
    rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
  rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
      = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
  -- Guard 1 passes (hAcc1): `guard True = pure ()`, then `simulateQ impl (pure …) = pure …`.
  rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = pure PUnit.unit from by rw [hAcc1]; simp [guard]]
  conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = OptionT.lift (pure PUnit.unit) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_pure]
  rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
      = pure PUnit.unit from rfl, pure_bind]
  -- Resolve the spot-check `forIn` to `pure (some ())` via the yield-pure induction lemma.
  -- `hForIn`'s type is checked against the goal-shaped equation by `isDefEq` (bridging the
  -- lift-instance gaps); a `conv … change` then re-spells the goal's loop to `hForIn`'s LHS.
  have hForIn :
      simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (A := A) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
            OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      = (pure (some PUnit.unit) : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro j
    simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
    -- Resolve the two `queryF` reads (`f₀ = oStmt 0 (xs j)`, `f₁ = oStmt 1 (xs j)`) by defeq.
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
        = (pure (oStmt 0 (xs j)) : OracleComp []ₒ A) from rfl]
    rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) A)
        = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) A) from rfl, pure_bind]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
        = (pure (oStmt 1 (xs j)) : OracleComp []ₒ A) from rfl]
    rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) A)
        = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) A) from rfl, pure_bind]
    -- Guard passes by hAcc2; then `simulateQ impl (pure …) = pure …`.
    rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ • oStmt 1 (xs j)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = pure PUnit.unit from by rw [hAcc2 j]; simp [guard]]
    conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
          ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = OptionT.lift (pure PUnit.unit) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure,
      show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
        = pure PUnit.unit from rfl, pure_bind]
    -- Trailing `(pure ∘ yield) unit = pure (yield unit)`, simulated to `pure (some (yield unit))`.
    change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
          (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
    conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
        = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure]
    rfl
  -- Collapse the loop. The goal's bound `simulateQ … (forIn …)` is defeq to `hForIn`'s LHS but
  -- not `rw`-matchable (the `ForIn`/`MonadLift` instance trees differ syntactically). A
  -- `conv … change` re-spells the focused loop as `hForIn`'s exact LHS (the universes are pinned
  -- to `0` by the `emptySpec.{0,0}` ascription in the statement), after which `rw [hForIn]` fires.
  conv_lhs =>
    enter [1]
    change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (A := A) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
            OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
  rw [hForIn]
  -- After collapsing the loop the goal is `(pure (some ()) : OracleComp []ₒ _) >>= …`; the bind
  -- runs the constant `(pure ∘ id)` continuation, leaving
  -- `simulateQ impl (pure ()) = pure (some ())`.
  change ((pure (some PUnit.unit) : OracleComp []ₒ (Option PUnit)) >>= fun _ ↦
      simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        ((pure PUnit.unit : OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit) :
          OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Option PUnit))) = _
  rw [pure_bind]
  exact simulateQ_pure _ (some PUnit.unit)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- Two-sided (`ite`) companion of `verifierBody_simulateQ_eq_pure`: the simulated verifier
body is the **deterministic** computation `pure (some ())` when both §6.1 accept conditions
hold for the supplied challenge `γ`, prover message `msgs ⟨1, rfl⟩`, and spot-check positions
`xs`, and `pure none` otherwise (a failed `guard` propagates through the remaining `OptionT`
binds, short-circuiting the spot-check loop).

The accepting direction delegates to `verifierBody_simulateQ_eq_pure`; the failing directions
re-run the same defeq bridges (see that lemma's docstring for the toolkit) and collapse the
failed `guard` via `simulateQ_optionT_failure` / `OptionT.failure_bind`, using
`simulateQ_optionT_forIn_yield_pure_none` for a failure inside the spot-check `forIn`. This is
the monadic core of the soundness direction (`accepts_of_mem_support_verifier_run` below):
a successful simulated run forces both accept conditions. -/
lemma verifierBody_simulateQ_eq_pure_ite
    (encode : (Fin k → F) → (ι → A))
    (oStmt : (i : Fin 2) → OracleStatement ι A i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : A ← liftM (queryF (ι := ι) (A := A) 0 (xs j))
            let f₁ : A ← liftM (queryF (ι := ι) (A := A) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ • f₁) :
        OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (if (∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2) ∧
            (∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
              = oStmt 0 (xs j) + γ • oStmt 1 (xs j))
          then some () else none) := by
  by_cases h1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2
  case pos =>
    by_cases h2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
        = oStmt 0 (xs j) + γ • oStmt 1 (xs j)
    case pos =>
      rw [if_pos ⟨h1, h2⟩]
      exact verifierBody_simulateQ_eq_pure (k := k) (t := t)
        encode oStmt msgs stmt1 mu1 mu2 γ xs h1 h2
    case neg =>
      rw [if_neg (fun hc ↦ h2 hc.2)]
      -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
      rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
          = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
              OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
            (OracleComp.monadLift_liftM_OptionT _).symm]
      simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (A := A) i x) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) A)
          = OptionT.lift (liftM (queryF (ι := ι) (A := A) i x) :
              OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) A) from
            fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
      -- Push `simulateQ` through the OptionT bind / lift / map structure.
      simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
        queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
      -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
      conv_lhs =>
        enter [1, 1]
        change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
          = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
      rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
          = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
      -- Guard 1 passes (h1): `guard True = pure ()`, then collapse the simulated pure.
      rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = pure PUnit.unit from by rw [h1]; simp [guard]]
      conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
            ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = OptionT.lift (pure PUnit.unit) from rfl]
      rw [simulateQ_optionT_lift, simulateQ_pure]
      rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
          = pure PUnit.unit from rfl, pure_bind]
      -- Collapse the spot-check `forIn` to `pure none` (some spot check fails, by `h2`).
      have hForIn :
          simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (A := A) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
                OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
          = (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
        refine simulateQ_optionT_forIn_yield_pure_none _ _ _ _
          (fun j ↦ encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ • oStmt 1 (xs j))
          (fun j ↦ ?_) (fun hall ↦ h2 (fun j ↦ hall j (List.mem_finRange j)))
        simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
          queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
        -- Resolve the two `queryF` reads (`f₀`, `f₁`) by defeq, as in the `some` direction.
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
            = (pure (oStmt 0 (xs j)) : OracleComp []ₒ A) from rfl]
        rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) A)
            = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) A) from rfl, pure_bind]
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι A]ₒ.Domain)))
            = (pure (oStmt 1 (xs j)) : OracleComp []ₒ A) from rfl]
        rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) A)
            = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) A) from rfl, pure_bind]
        -- Per-spot-check guard: passes or fails according to `cond j`.
        by_cases hj : encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ • oStmt 1 (xs j)
        · rw [if_pos hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ • oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = pure PUnit.unit from by rw [hj]; simp [guard]]
          conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
                ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = OptionT.lift (pure PUnit.unit) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure,
            show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
              = pure PUnit.unit from rfl, pure_bind]
          change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
              ([OracleStatement ι A]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
                (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
          conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
              = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure]
          rfl
        · rw [if_neg hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ • oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = failure from by simp only [guard, if_neg hj]]
          rw [simulateQ_optionT_failure, OptionT.failure_bind]
          rfl
      -- Re-spell the goal's loop to `hForIn`'s LHS and collapse; failure then propagates.
      conv_lhs =>
        enter [1]
        change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (A := A) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
                OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      rw [hForIn]
      rw [show (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit))
          = ((failure : OptionT (OracleComp (emptySpec.{0, 0})) PUnit) :
              OracleComp (emptySpec.{0, 0}) (Option PUnit)) from rfl,
        OptionT.failure_bind]
  case neg =>
    rw [if_neg (fun hc ↦ h1 hc.1)]
    -- Bridge the `g`-query, resolve it by defeq, then fail on the linear-constraint guard.
    rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
        = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
          (OracleComp.monadLift_liftM_OptionT _).symm]
    simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryG, OracleInterface.simOracle2, QueryImpl.addLift_def]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι A) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
    rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
        = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
    rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = failure from by simp only [guard, if_neg h1]]
    rw [simulateQ_optionT_failure, OptionT.failure_bind]
    rfl

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- **Soundness direction of the verifier-run support characterization** (converse companion
of the completeness-side `verifierBody_simulateQ_eq_pure`): if the simulated run of the C6.2
oracle verifier (routed through `toVerifier` / `simOracle2`, then through an arbitrary
empty-spec `impl`) on a **fixed** full transcript `tr` can succeed — `some _` lies in the run's
support — then the §6.1 decision predicate `accepts` holds for that transcript's challenge
`γ = tr 0`, prover message `g = tr 1`, and spot-check positions `xs = tr 2`.

Proof: the empty-spec simulation can only shrink support
(`support_simulateQ_run'_subset`), and after `toVerifier` routing the verifier body is the
deterministic `pure (if accepts-conditions then some () else none)`
(`verifierBody_simulateQ_eq_pure_ite`), so a `some` in the support forces the condition. -/
lemma accepts_of_mem_support_verifier_run
    {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) (s₀ : σ)
    (encode : (Fin k → F) → (ι → A))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    {y : OutputStatement × (∀ i, OutputOracleStatement i)}
    (hy : some y ∈ support ((simulateQ impl
        (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run' s₀)) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  -- Drop the `impl` simulation layer (an empty-spec impl can only shrink the support).
  have hy' := support_simulateQ_run'_subset impl _ s₀ hy
  -- Expose the `toVerifier`-routed verifier body and collapse it to its `ite` normal form.
  simp only [OracleVerifier.toVerifier, oracleVerifier, Verifier.run, bind_pure_comp] at hy'
  rw [verifierBody_simulateQ_eq_pure_ite (encode := encode) (stmt1 := stmtIn.1.1)
      (mu1 := stmtIn.1.2.1) (mu2 := stmtIn.1.2.2)] at hy'
  -- Peel the trailing output-assembly bind; a `none` head contradicts `some y` in the support.
  rcases OptionT.mem_support_run_bind _ _ hy' with ⟨hnone, hcontra⟩ | ⟨a, ha, _⟩
  · exact absurd hcontra (by simp)
  · have ha := OracleComp.eq_of_mem_support_pure _ ha
    split at ha
    · rename_i hcond
      exact hcond
    · exact absurd ha (by simp)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- Round-by-round-framework wrapper for `accepts_of_mem_support_verifier_run`, consuming the
exact hypothesis shape that `KnowledgeStateFunction.toFun_full`
(`ArkLib/OracleReduction/Security/RoundByRound.lean`) provides for the C6.2 oracle verifier:
if the verifier's simulated run on a fixed transcript outputs, with positive probability, a
statement that is `relOut`-related to some `witOut` (for **any** `relOut`, in particular
`Set.univ`), then the §6.1 decision predicate `accepts` holds on that transcript. This is the
entry point for the L6.8 round-by-round knowledge-soundness state function: at the full
transcript it converts the framework's `Pr[…] > 0` acceptance hypothesis into the concrete
accept equations that the [ABF26] §6.2 argument consumes. -/
lemma accepts_of_probEvent_pos_verifier_run
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) → (ι → A))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    (witOut : OutputWitness)
    (relOut : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
    (h : Pr[ fun stmtOut ↦ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do
          (simulateQ impl
              (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run'
            (← init)] > 0) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨stmtOut, hmem, -⟩ := h
  obtain ⟨s₀, -, hmem⟩ := OptionT.mem_support_bind_mk init _ hmem
  rw [OptionT.mem_support_iff] at hmem
  exact accepts_of_mem_support_verifier_run (k := k) (t := t) impl s₀ encode stmtIn tr hmem

/-! ### Remark 6.7 of [ABF26] — MCA, not just CA

The L6.6 soundness argument depends on **mutual** correlated agreement
(MCA). With only correlated agreement (CA), one cannot prove every
codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)` decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/

/-! ### Lemma 6.8 assembly — extractor, knowledge state function, per-round bounds.
The post-spot-check state is the §6.1 acceptance predicate itself
(witness-ignoring). This deliberately deviates from the paper's printed
full-transcript knowledge state: taken literally, the paper's state checks the
verifier's two conditions against the *state witness* `C(F̄)` rather than the
prover's claim `ḡ`, which violates the "iff the verifier accepts" requirement of
its own knowledge-state definition (a witness `F̄ ≠ ḡ` can pass the spot checks
while the verifier, checking `ḡ`, rejects — and makes the `(1−δ)^t` transition
bound false). The acceptance predicate is what the transition analysis actually
uses. -/

/-- `Pr_{x ← D}[P x] = 0` for a never-satisfied predicate `P`. -/
private lemma Pr_eq_zero_of_forall_not {α : Type} (D : PMF α) (P : α → Prop)
    (h : ∀ x, ¬ P x) : Pr_{let x ← D}[P x] = 0 := by
  classical rw [prob_tsum_form_singleton]; simp [h]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The post-`γ` knowledge state of the L6.8 argument ([ABF26] §6.2): `m`
satisfies the folded linear constraint at `γ`, and `f₁ + γ·f₂` agrees with
`encode m` on a `≥ (1-δ)`-fraction column set. Shaped to match the event of
`ToyProblem.gamma_transition_prob_le` exactly.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) reuses it as its γ-round prefix event. -/
def gammaState (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) (γ : F) (m : Fin k → F) : Prop :=
  (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
  ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
    ∀ j ∈ S, f₁ j + γ • f₂ j = encode m j

/-- L6.8 intermediate witness types: input witness at round 0, the γ-round
candidate message during rounds 1–2, nothing after the spot-check round. -/
private def rbrWitMid : Fin 4 → Type
  | ⟨0, _⟩ => Witness (F := F) k
  | ⟨1, _⟩ => Fin k → F
  | ⟨2, _⟩ => Fin k → F
  | ⟨3, _⟩ => PUnit

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
open Classical in
/-- Round-0 extraction for L6.8: if *any* witness completes `stmtIn` in the
relaxed output relation, return one by choice; otherwise a dummy.

Public (not `private`) because L6.10 reuses it verbatim: the C6.9 input relation is
the same `R̃²_{C,δ}` (`outputRelationFor`), so the L6.10 straightline extractor is this
same classical choice (`SimplifiedIOR.simplifiedIOR_knowledgeSound`). -/
noncomputable def extractZero (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Witness (F := F) k :=
  if h : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ then h.choose
  else fun _ _ ↦ 0

omit [DecidableEq ι] [DecidableEq F] [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A] in
/-- If a relaxed-relation witness exists at all, `extractZero` returns one.
(Shared by the L6.8 γ-round bound and the L6.10 game bound.) -/
lemma extractZero_mem {encode : (Fin k → F) → (ι → A)} {δ : ℝ≥0}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)}
    (hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ) :
    (stmtIn, extractZero k encode δ stmtIn) ∈ outputRelationFor k encode δ := by
  unfold extractZero; rw [dif_pos hw]; exact hw.choose_spec

omit [DecidableEq ι] in
/-- The L6.8 round-by-round extractor ([ABF26] §6.2): round 0 extracts a
relaxed-relation witness by choice, round 1 passes the candidate message
through, round 2 reads the prover's claim `g` off the transcript. -/
private noncomputable def rbrExtractor (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    Extractor.RoundByRound []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) (rbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn _ _ ↦ extractZero k encode δ stmtIn
  | ⟨1, _⟩ => fun _ _ w ↦ w
  | ⟨2, _⟩ => fun _ tr _ ↦ tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

omit [DecidableEq ι] in
/-- The L6.8 knowledge state function ([ABF26] §6.2): relaxed-relation
membership at round 0, `gammaState` after rounds 1–2, and the §6.1 acceptance
predicate after the spot-check round (the witness-ignoring final state is a
deliberate repair of the paper's printed state — see the §6.8-assembly section
comment above). -/
private noncomputable def rbrKSF (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((oracleVerifier (k := k) (t := t) encode).toVerifier).KnowledgeStateFunction init impl
      (outputRelationFor k encode δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (rbrExtractor k t encode δ) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦ (stmtIn, w) ∈ outputRelationFor k encode δ
  | ⟨1, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨2, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
        (tr ⟨0, Nat.zero_lt_succ _⟩) (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
        (tr ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
    | ⟨1, _⟩ => fun _ _ _ _ _ h ↦ h
    | ⟨2, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    accepts_of_probEvent_pos_verifier_run (k := k) (t := t) init impl encode
      stmtIn tr witOut _ h

omit [DecidableEq ι] [DecidableEq F] in
/-- `epsMCA` is a supremum of probabilities, hence `≤ 1 < ⊤`. Generic over the
codeword alphabet `A` (an `F`-module): the bound is alphabet-agnostic, so it
serves both the scalar (`A = F`) and folded (`A = Fin s → F`) instantiations.
The alphabet is bound locally (rather than via the section variable) so the
unused section instances do not leak into the type. (Candidate for relocation
to `ProximityGap/Errors.lean`. Public because the L6.10 coercion endgame in
`Spec/SimplifiedIOR.lean` and the leaderboard bridge in `Leaderboard.lean`
reuse it.) -/
lemma epsMCA_ne_top [Nonempty ι] {A : Type} [Fintype A] [DecidableEq A]
    [AddCommGroup A] [Module F A] (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ PMF.coe_le_one _ _)

omit [DecidableEq ι] in
/-- Per-transcript γ-round bound for the L6.8 game ([ABF26] §6.2, via
`ToyProblem.gamma_transition_prob_le`), stated in the definitionally reduced
form of the game event so the master rbr-game lemma can consume it.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its γ-round prefix bound. -/
lemma gamma_round_game_bound [SampleableType F] [Nonempty ι]
    (C : Set (ι → A)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ) (hδ_lt : δ < (minRelHammingDistCode C : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Pr[fun γ : F ↦ ∃ w : Fin k → F,
        (stmtIn, extractZero k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          gammaState k (encode : (Fin k → F) → (ι → A)) δ stmtIn.1.1 stmtIn.1.2.1
            stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ w
      | $ᵗ F] ≤
      (((epsMCA (F := F) (A := A) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro γ ⟨w, hne, -⟩
    exact hne (extractZero_mem k hw)
  · refine le_trans (Pr_le_Pr_of_implies _ _
      (fun γ ↦ ∃ m, gammaState k (encode : (Fin k → F) → (ι → A)) δ stmtIn.1.1
        stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ m) ?_) ?_
    · rintro γ ⟨w, -, hst⟩
      exact ⟨w, hst⟩
    · have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
          (∀ i : Fin 2, ∑ j, M i j * stmtIn.1.1 j = ![stmtIn.1.2.1, stmtIn.1.2.2] i) ∧
          ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
            ∀ i : Fin 2, ∀ j ∈ S, ![stmtIn.2 0, stmtIn.2 1] i j = encode (M i) j := by
        rintro ⟨M, h1, S, h2, h3⟩
        refine hw ⟨M, h1, S, h2, fun i j hj ↦ ?_⟩
        fin_cases i
        · simpa using h3 0 j hj
        · simpa using h3 1 j hj
      refine le_trans (gamma_transition_prob_le C δ encode hinj hC hδ_pos hδ_lt
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) hNoWit)
        (le_of_eq ?_)
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal (epsMCA_ne_top C δ),
        ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        ENNReal.coe_natCast, ENNReal.coe_natCast]

omit [DecidableEq ι] [Fintype F] [Fintype A] in
-- `[DecidableEq F]` is used in the proof (`by_cases` on the linear constraint, the agreement
-- filter) but does not surface in the statement; same false-positive pattern as
-- `ToyProblem.pair_violates` (SoundnessBounds.lean).
set_option linter.unusedDecidableInType false in
/-- Per-transcript spot-check-round bound for the L6.8 game ([ABF26] §6.2):
for any fixed `(γ, g)` with the post-`γ` state false, the probability over
uniform spot checks that the verifier accepts is at most `(1-δ)^t`. Stated in
the definitionally reduced form of the game event.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its spot-check tail bound. -/
lemma spotcheck_round_game_bound [Nonempty ι]
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (γ : F) (g : Fin k → F) [SampleableType (Fin t → ι)] :
    Pr[fun xs : Fin t → ι ↦ ∃ _w : PUnit,
        ¬ gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g ∧
          accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2 γ g xs
      | $ᵗ (Fin t → ι)] ≤ (((1 - δ) ^ t : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hbad : gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
      (stmtIn.2 0) (stmtIn.2 1) γ g
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, hne, -⟩
    exact hne hbad
  by_cases hlin : ∑ j, g j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2
  swap
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, -, hacc⟩
    exact hlin (And.left hacc)
  set S₀ : Finset ι :=
    Finset.univ.filter (fun j ↦ stmtIn.2 0 j + γ • stmtIn.2 1 j = encode g j) with hS₀
  have hι : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAcard : (S₀.card : ℝ) < (1 - (δ : ℝ)) * Fintype.card ι :=
    not_le.mp fun hge ↦ hbad ⟨hlin, S₀, hge, fun j hj ↦ (Finset.mem_filter.mp hj).2⟩
  have hδ1 : δ ≤ 1 := by
    by_contra hgt
    have h1δ : (1 : ℝ) - (δ : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast not_le.mp hgt)
    linarith [mul_neg_of_neg_of_pos h1δ hι, (Nat.cast_nonneg S₀.card : (0 : ℝ) ≤ S₀.card)]
  have hbase : ((S₀.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ 1 - δ := by
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ≥0) < Fintype.card ι),
      ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hδ1]
    linarith
  refine le_trans (Pr_le_Pr_of_implies _ _ (fun xs ↦ ∀ j, xs j ∈ S₀) ?_) ?_
  · rintro xs ⟨-, -, hacc⟩ j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (And.right hacc j).symm⟩
  · refine le_trans (prob_uniform_pi_mem_finset_le S₀ t) ?_
    rw [ENNReal.coe_pow]
    refine pow_le_pow_left' ?_ t
    rw [show ((S₀.card : ℝ≥0∞)) = ((S₀.card : ℝ≥0) : ℝ≥0∞) from (ENNReal.coe_natCast _).symm,
      show ((Fintype.card ι : ℝ≥0∞)) = ((Fintype.card ι : ℝ≥0) : ℝ≥0∞) from
        (ENNReal.coe_natCast _).symm,
      ← ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    exact ENNReal.coe_le_coe.mpr hbase

omit [DecidableEq ι] in
/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the IOR has round-by-round knowledge soundness (ArkLib's
`OracleVerifier.rbrKnowledgeSoundness`, definitionally
`toVerifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with
per-round errors

**Quantification note (paper Definition A.5 vs the ArkLib game).** The
paper's rbr definition bounds the bad-transition probability for *every*
fixed transcript prefix (worst case); ArkLib's game samples the prefix
challenges uniformly inside the prover run and bounds the *mixture*. The
in-tree statement is therefore the averaged form, implied by the paper's.
The per-round lemmas feeding this proof (`gamma_round_game_bound`,
`spotcheck_round_game_bound`) hold for every fixed prefix — i.e. they ARE
the paper-strength worst-case facts — so the paper's mathematical content
is fully in-tree; only the bundled top-level game statement averages.

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `(Lambda …).toNat` in the γ-round error is faithful: `Lambda` is
never `⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`).

**Status: fully proven (sorry-free).** The `KnowledgeStateFunction` is
`rbrKSF` above (relation membership → `gammaState` → the acceptance
predicate; the witness-ignoring final state is a deliberate repair of the
paper's printed full-transcript state — see the §6.8-assembly section comment),
the extractor is `rbrExtractor` (round-0 extraction by classical choice),
and the two per-round bounds are `gamma_round_game_bound` (via
`ToyProblem.gamma_transition_prob_le`) and `spotcheck_round_game_bound`,
plugged into the game shape by
`ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le`. -/
theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → A)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → A))).rbrKnowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
        (fun i ↦
          -- round 0 (combination randomness γ): MCA + list-decoding term;
          -- round 2 (spot checks): `(1-δ)^t`.
          if i.1 = 0 then
            (epsMCA (F := F) (A := A) C δ).toNNReal +
              ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
                / (Fintype.card F : ℝ≥0)
          else (1 - δ) ^ t) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨rbrWitMid (F := F) k,
    rbrExtractor k t (encode : (Fin k → F) → (ι → A)) δ,
    rbrKSF k t (encode : (Fin k → F) → (ι → A)) δ init impl, ?_⟩
  intro stmtIn witIn prover i
  obtain ⟨⟨iv, hi⟩, hdir⟩ := i
  rcases iv with _ | _ | _ | iv
  · -- Round 0 (combination randomness γ): the MCA + list-decoding bound.
    refine probEvent_simulateQ_addLift_getChallenge_bind_le init impl
      (prover.runWithLogToRound _ stmtIn witIn) ⟨⟨0, hi⟩, hdir⟩
      (fun x c ↦ (x.1.1, c, x.2)) _ ?_
    exact fun _ ↦ gamma_round_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min stmtIn
  · exact absurd hdir (fun h ↦ Direction.noConfusion h)
  · -- Round 2 (spot checks): the `(1-δ)^t` bound, per fixed `(γ, g)`.
    refine probEvent_simulateQ_addLift_getChallenge_bind_le init impl
      (prover.runWithLogToRound _ stmtIn witIn) ⟨⟨2, hi⟩, hdir⟩
      (fun x c ↦ (x.1.1, c, x.2)) _ ?_
    exact fun x ↦ spotcheck_round_game_bound k t (encode : (Fin k → F) → (ι → A)) δ
      stmtIn (x.1.1 ⟨0, Nat.zero_lt_succ _⟩)
      (x.1.1 ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
  · exact absurd hi (by omega)

end Protocol

end Spec

end ToyProblem

