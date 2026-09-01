/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ArkLib.OracleReduction.Security.RbrGame

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
* `Accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete.
Completeness (C6.2, `oracleReduction_perfectCompleteness`) and
round-by-round knowledge soundness (L6.8,
`oracleVerifier_rbrKnowledgeSoundnessWorstCase`, with
`oracleVerifier_rbrKnowledgeSoundness` as its averaged corollary) are **fully proven** here. Plain
knowledge soundness (L6.6, `oracleVerifier_knowledgeSoundness_winningSetUpperBound`) is **fully
proven** in the sibling file `Spec/KnowledgeSoundness.lean`. The generic theorem
uses the sharper Definition 6.11 winning-set expression
`(1-δ)^t + winningSetDensity·(1 - (1-δ)^t)`. The executable IRS corollary bounds
that quantity by
`(1-δ)^t + (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|)·(1 - (1-δ)^t)`, which is `≤` the
sum `(ε_mca + |Λ|/|F|) + (1-δ)^t` stated in [ABF26] Lemma 6.6
(`lemma:toy-soundness`) and so is at least as strong.  (The `max` of the two
terms would be a strictly weaker — and unsound — target; the sum is the correct
reading of the paper.) The
per-round game bounds proven in this file
(`gamma_round_game_bound`, `spotcheck_round_game_bound`) are shared by
both the L6.8 and L6.6 proofs.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → A`. The protocol runs:

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
* oracle access to `f₁, f₂` ↦ `OracleStatement` queried via `queryOracleStatement`,
  routed through the per-index `OracleInterface` instances.
* the §6.1 decision predicate ↦ `Accepts`.
* the exact input relation (Definition 6.1) ↦ `inputRelationFor`; the relaxed
  output relation (Definition 6.3) ↦ `outputRelationFor` — both with the
  verifier's encoder **fixed** (see `inputRelationFor` for why).
* the §6.2 round-by-round state and extractor (L6.8) ↦ `GammaState`,
  `rbrKnowledgeStateFunction`, `rbrExtractor`.
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

The paper's Construction 6.1/6.2 inputs are `f : [n] → F^s` for an
interleaving parameter `s` (and the §6.3 tables sweep `s = 2^0, …, 2^12`).
This formalization is generic over the codeword alphabet `A` (an `F`-module):
words are `ι → A`, with `A = F` the scalar specialization and
`A = Fin s → F` the genuine interleaved alphabet implemented by
`Impl/IRS.lean`. `Impl/FRS.lean` provides the distinct folded-RS model.
The relative Hamming metric is over `A` (one symbol = one `A`-coordinate),
which is the required column metric; reindexing `ι := [n] × [s]` over a
scalar alphabet would **not** recover it. The challenge `γ`, constraint
vector `v`, and constraint values `μ` stay scalar (`F`); only codeword
values and the encoder `(Fin k → F) →ₗ[F] (ι → A)` range over `A`.
Combination of codeword values is the module action `f₀ + γ • f₁` (it
specializes to `f₀ + γ · f₁` when `A = F`).

## Verified vs. admitted

What is verified here is the **reduction**, with a **symbolic** error. Every theorem in
`ProofSystem/ToyProblem/` is `sorry`-free, and the headline declarations (completeness, the plain
and round-by-round knowledge-soundness theorems, the named-extractor contracts, the attack lower
bounds, and the actual-vs-certified bridges) depend only on `propext`, `Classical.choice`, and
`Quot.sound`. But the shipped knowledge error
`(1-δ)^t + (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|)·(1 - (1-δ)^t)` keeps the bracket
**opaque**: `ε_mca` and `Λ` are the definitions of `ProximityGap/Errors.lean` and
`Code.Lambda`, not numerals. Nothing in this directory evaluates them.

Numeric values for the bracket come from the MCA/CA capacity bounds under
`Data/CodingTheory/ProximityGap/CapacityBounds`. Several of those are fully proven; the rest
are **external admits** (each `sorry` is tagged with the primary source it stands in for) —
in particular the Johnson-range MCA input `rs_mcaError_le_in_johnson_range`.
That subtree is deliberately **not** in this directory's import cone, so the quarantine is
structural rather than a convention: no toy-problem theorem can silently acquire a numeric
claim, admit-backed or otherwise. Consequently the
theorems apply at production parameter sizes — they are parametric in `C`, `δ`, and `t` — but
no numeric error value is proven in-tree at any production shape. For the interleaved-RS profile
the remaining distance is short and is spelled out in `Impl/IRS.lean`.

One further admitted region sits outside every proof here and must not be read as backing any
statement in this file: the generic `StateT` security-composition theorems of
`OracleReduction/Composition/Sequential/Append.lean` (admitted, with no toy-problem
consumer — the virtual-output *execution* lemmas that composition needs are proven
separately).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ProximityGap
open scoped NNReal ENNReal ProbabilityTheory
open Probability

-- `[Fintype A]`/`[DecidableEq A]` are used inside code-theoretic and
-- decidability bodies but do not surface in the alphabet-generic lemma types;
-- suppress the `unused…InType` linter file-wide (the same toy idiom used in
-- `SoundnessBounds.lean`).

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `RelaxedRelationFor`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
variable (k t : ℕ)

/-- Input (explicit) statement of the toy protocol: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of the toy protocol: the two purported codewords
`f₁, f₂ : ι → A`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι A : Type) : Fin 2 → Type := fun _ ↦ ι → A

@[reducible] instance (priority := 10000) : ∀ i, OracleInterface (OracleStatement ι A i) :=
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

@[reducible] instance (i : Fin 0) : OracleInterface (OutputOracleStatement i) :=
  i.elim0

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for the toy protocol: three rounds, in the
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

@[reducible] instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
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

/-- The decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def Accepts (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι A i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ • f 1 (xs j)

/-- The IOR-shaped **fixed-encoding** input relation.

`((v, μ₁, μ₂), (f₀, f₁)) ∈ inputRelationFor encode` with witness `M`
iff the oracle codewords are the `encode`-images of the witness messages
(`fᵢ = encode (M i)`) and the witness satisfies the linear constraint
(`⟨M i, v⟩ = μᵢ`). The encoding is the verifier's **fixed** `encode` (a plain
function, matching `oracleVerifier`), and the witness `M` is tied to the
statement — this is what the honest prover sends `g = M₀ + γ·M₁` against and
what `accepts_of_mem_inputRelationFor` consumes.

The fixed encoder is load-bearing: with an existentially quantified encoder
(`∃ encode', fᵢ = encode' (Mᵢ)`) honest completeness is false — the honest
prover's `encode g` need not match `encode' (Mᵢ)` when `encode' ≠ encode` — and
the attack lower bound breaks the same way. See `ToyProblem.RelationFor` for
the shared fixed-encoder relation family. -/
def inputRelationFor (encode : (Fin k → F) → (ι → A)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι A i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, input.1.2 i = encode (input.2 i)) ∧
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j = ![input.1.1.2.1, input.1.1.2.2] i)

/-- The IOR-shaped **fixed-encoding** *relaxed* output relation.
The soundness statement of L6.6/6.8 is with respect to this: the verifier's
"accept" guarantee is that the input `(f₀, f₁)` is `δ`-close (on a common
agreement column set) to a valid instance `encode (M i)` for some constraint-
satisfying messages `M`. Uses the verifier's fixed plain `encode` (cf.
`ToyProblem.RelaxedRelationFor`), and checks the witness component supplied by
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

omit [Fintype ι] in
/-- The language-level exact relation `RelationFor` is precisely the
existential closure of the witness-bearing C6.2 input relation.  This bridge
keeps paper-facing statements and OracleReduction security statements on one
public contract. -/
theorem relationFor_iff_exists_inputRelationFor
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (stmt : Statement (F := F) k)
    (oStmt : ∀ i, OracleStatement ι A i) :
    RelationFor encode stmt.1 ![stmt.2.1, stmt.2.2] oStmt ↔
      ∃ M, ((stmt, oStmt), M) ∈
        inputRelationFor k (encode : (Fin k → F) → (ι → A)) := by
  rfl

/-- The language-level relaxed relation `RelaxedRelationFor` is precisely the
existential closure of the witness-bearing C6.2 output relation.  Both sides
use one common agreement set for the two interleaved words. -/
theorem relaxedRelationFor_iff_exists_outputRelationFor
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (stmt : Statement (F := F) k)
    (oStmt : ∀ i, OracleStatement ι A i) :
    RelaxedRelationFor encode δ stmt.1 ![stmt.2.1, stmt.2.2] oStmt ↔
      ∃ M, ((stmt, oStmt), M) ∈
        outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ := by
  constructor
  · rintro ⟨Wstar, ⟨M, hW, hlin⟩, S, hcard, hagree⟩
    refine ⟨M, hlin, S, hcard, ?_⟩
    intro i j hj
    change oStmt i j = encode (M i) j
    rw [hagree i j hj, hW i]
  · rintro ⟨M, hlin, S, hcard, hagree⟩
    refine ⟨fun i ↦ encode (M i), ⟨M, ?_, hlin⟩, S, hcard, hagree⟩
    intro i
    rfl

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelationFor` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Honest prover, verifier, and reduction

This section provides the bundled `Prover` / `Verifier` / `Reduction`
compatibility view, with codewords threaded through
`StmtIn = Statement × (∀ i, OracleStatement i)`. It is the extensional
shape produced by `OracleReduction.toReduction`. The canonical
`OracleProver` / `OracleVerifier` flavour, which routes codeword access
through VCV's query machinery and is the target of the completeness and
soundness statements, follows in the next section.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]

/-- Honest prover for the toy protocol. After receiving the combination
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

/-- The decision predicate is decidable: it is a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance Accepts.instDecidable
    (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι A i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (Accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold Accepts; infer_instance

/-- Honest verifier for the toy protocol. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `Accepts` holds for the supplied encoding.

Computable — `Accepts` is decidable, so no `Classical.dec` is needed.
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
    if Accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for the toy protocol: the package
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

**Extractor-failure polarity.** In `Verifier.knowledgeSoundness`, extraction
failure (`extractedWitIn? = none`) is scored against the prover; an
always-failing `OptionT` extractor therefore certifies nothing, and none of the
knowledge-soundness statements below can be discharged vacuously through it.
The generic existence theorems (`oracleVerifier_knowledgeSoundness_winningSetUpperBound`,
`oracleVerifier_rbrKnowledgeSoundnessWorstCase` with its averaged corollary
`oracleVerifier_rbrKnowledgeSoundness`, and the alphabet-generic
`verifier_knowledgeSoundness` in `Spec/SimplifiedIOR.lean`) use the classical
`chooseRelaxedWitness` selector; `Impl/IRS.lean` supplies the principal
executable path — exact named straightline and worst-case/averaged RBR
extractors for both the three-round protocol and the virtual-oracle reduction.
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
def queryMessage : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by change Unit; exact ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryOracleStatement (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι A]ₒ A :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι A]ₒ.Domain from ⟨i, (by change ι; exact x)⟩)

/-- Oracle verifier for the toy protocol.

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
    let g : Fin k → F ← liftM <| queryMessage (ι := ι) (F := F) (k := k) (t := t)
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      let f₀ : A ← liftM <| queryOracleStatement (ι := ι) (A := A) 0 (xs j)
      let f₁ : A ← liftM <| queryOracleStatement (ι := ι) (A := A) 1 (xs j)
      guard (encode g (xs j) = f₀ + γ • f₁)
    pure ()
  outputOracle := .inl {
    embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
    hEq := fun i ↦ i.elim0
    outputInterface_heq := fun i ↦ i.elim0 }

/-- Honest oracle reduction for the toy protocol: the
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
lemma oracleVerifier_verify_simulateQ_eq_pure
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
        let g : Fin k → F ← liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : A ← liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))
            let f₁ : A ← liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ • f₁) :
        OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (some ()) := by
  -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
  rw [show (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
      = OptionT.lift (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
          OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryOracleStatement (ι := ι) (A := A) i x) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) A)
      = OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) i x) :
          OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) A) from
        fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
  -- Push `simulateQ` through the OptionT bind / lift / map structure.
  simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
    queryMessage, queryOracleStatement, OracleInterface.simOracle2, QueryImpl.addLift_def]
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
          (OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))) >>=
              fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
            OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      = (pure (some PUnit.unit) : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro j
    simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryOracleStatement, OracleInterface.simOracle2, QueryImpl.addLift_def]
    -- Resolve the two `queryOracleStatement` reads (`f₀ = oStmt 0 (xs j)`,
    -- `f₁ = oStmt 1 (xs j)`) by defeq.
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
          (OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))) >>=
              fun f₁ ↦
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
/-- Two-sided (`ite`) companion of `oracleVerifier_verify_simulateQ_eq_pure`: the simulated verifier
body is the **deterministic** computation `pure (some ())` when both accept conditions
hold for the supplied challenge `γ`, prover message `msgs ⟨1, rfl⟩`, and spot-check positions
`xs`, and `pure none` otherwise (a failed `guard` propagates through the remaining `OptionT`
binds, short-circuiting the spot-check loop).

The accepting direction delegates to `oracleVerifier_verify_simulateQ_eq_pure`; the failing
directions
re-run the same defeq bridges (see that lemma's docstring for the toolkit) and collapse the
failed `guard` via `simulateQ_optionT_failure` / Batteries' `failure_bind`, using
`simulateQ_optionT_forIn_yield_pure_none` for a failure inside the spot-check `forIn`. This is
the monadic core of the soundness direction (`accepts_of_mem_support_verifier_run` below):
a successful simulated run forces both accept conditions. -/
lemma oracleVerifier_verify_simulateQ_eq_pure_ite
    (encode : (Fin k → F) → (ι → A))
    (oStmt : (i : Fin 2) → OracleStatement ι A i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : A ← liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))
            let f₁ : A ← liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))
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
      exact oracleVerifier_verify_simulateQ_eq_pure (k := k) (t := t)
        encode oStmt msgs stmt1 mu1 mu2 γ xs h1 h2
    case neg =>
      rw [if_neg (fun hc ↦ h2 hc.2)]
      -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
      rw [show (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
          = OptionT.lift (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
              OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
            (OracleComp.monadLift_liftM_OptionT _).symm]
      simp only [show ∀ (i : Fin 2) (x : ι),
          (liftM (queryOracleStatement (ι := ι) (A := A) i x) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) A)
          = OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) i x) :
              OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) A) from
            fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
      -- Push `simulateQ` through the OptionT bind / lift / map structure.
      simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
        queryMessage, queryOracleStatement, OracleInterface.simOracle2, QueryImpl.addLift_def]
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
              (OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))) >>=
                fun f₀ ↦
                OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))) >>=
              fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
                OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
          = (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
        refine simulateQ_optionT_forIn_yield_pure_none _ _ _ _
          (fun j ↦ encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ • oStmt 1 (xs j))
          (fun j ↦ ?_) (fun hall ↦ h2 (fun j ↦ hall j (List.mem_finRange j)))
        simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
          queryOracleStatement, OracleInterface.simOracle2, QueryImpl.addLift_def]
        -- Resolve the two `queryOracleStatement` reads (`f₀`, `f₁`) by defeq, as in the
        -- `some` direction.
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
          rw [simulateQ_optionT_failure, failure_bind]
          rfl
      -- Re-spell the goal's loop to `hForIn`'s LHS and collapse; failure then propagates.
      conv_lhs =>
        enter [1]
        change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 0 (xs j))) >>=
                fun f₀ ↦
                OptionT.lift (liftM (queryOracleStatement (ι := ι) (A := A) 1 (xs j))) >>=
              fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ • f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit) :
                OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι A]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      rw [hForIn]
      rw [show (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit))
          = ((failure : OptionT (OracleComp (emptySpec.{0, 0})) PUnit) :
              OracleComp (emptySpec.{0, 0}) (Option PUnit)) from rfl,
        failure_bind]
  case neg =>
    rw [if_neg (fun hc ↦ h1 hc.1)]
    -- Bridge the `g`-query, resolve it by defeq, then fail on the linear-constraint guard.
    rw [show (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
        = OptionT.lift (liftM (queryMessage (ι := ι) (F := F) (k := k) (t := t)) :
            OracleComp ([]ₒ + ([OracleStatement ι A]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
          (OracleComp.monadLift_liftM_OptionT _).symm]
    simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryMessage, OracleInterface.simOracle2, QueryImpl.addLift_def]
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
    rw [simulateQ_optionT_failure, failure_bind]
    rfl

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- The executable C6.2 oracle verifier, after routing its oracle and message queries, is exactly
the decidable acceptance predicate. Keeping this bridge at the `OracleVerifier` boundary
prevents clients from depending on the verifier body's elaborated proof terms. -/
lemma oracleVerifier_simulateQ_eq_pure_ite
    (encode : (Fin k → F) → (ι → A))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι A i)
    (challenges : (pSpec (ι := ι) (F := F) k t).Challenges)
    (msgs : (pSpec (ι := ι) (F := F) k t).Messages) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        ((oracleVerifier (k := k) (t := t) encode).verify stmt challenges).run =
      pure (if Accepts (k := k) (t := t) encode stmt oStmt
        (challenges ⟨0, rfl⟩) (msgs ⟨1, rfl⟩) (challenges ⟨2, rfl⟩)
        then some () else none) := by
  unfold oracleVerifier
  convert oracleVerifier_verify_simulateQ_eq_pure_ite (encode := encode)
    (oStmt := oStmt) (msgs := msgs) (stmt1 := stmt.1)
    (mu1 := stmt.2.1) (mu2 := stmt.2.2)
    (γ := challenges ⟨0, rfl⟩) (xs := challenges ⟨2, rfl⟩) using 1
  all_goals (simp only [Accepts, bind_pure_comp]; try congr 1)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- **Soundness direction of the verifier-run support characterization** (converse companion
of the completeness-side `oracleVerifier_verify_simulateQ_eq_pure`): if the simulated run of
the
oracle verifier (routed through `toVerifier` / `simOracle2`, then through an arbitrary
empty-spec `impl`) on a **fixed** full transcript `tr` can succeed — `some _` lies in the run's
support — then the decision predicate `Accepts` holds for that transcript's challenge
`γ = tr 0`, prover message `g = tr 1`, and spot-check positions `xs = tr 2`.

Proof: the empty-spec simulation can only shrink support
(`support_simulateQ_run'_subset`), and after `toVerifier` routing the verifier body is the
deterministic `pure (if accepts-conditions then some () else none)`
(`oracleVerifier_verify_simulateQ_eq_pure_ite`), so a `some` in the support forces the condition. -/
lemma accepts_of_mem_support_verifier_run
    {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) (s₀ : σ)
    (encode : (Fin k → F) → (ι → A))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    {y : OutputStatement × (∀ i, OutputOracleStatement i)}
    (hy : some y ∈ support ((simulateQ impl
        (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run' s₀)) :
    Accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  -- Drop the `impl` simulation layer (an empty-spec impl can only shrink the support).
  have hy' := support_simulateQ_run'_subset impl _ s₀ hy
  -- Peel the output-oracle assembly map introduced by `OracleVerifier.toVerifier`.
  let V := oracleVerifier (k := k) (t := t) encode
  let assemble := fun (stmtOut : OutputStatement) =>
    (stmtOut, V.materializeOutput tr.challenges stmtIn.2 tr.messages)
  have hyMap : some y ∈ support
      (Option.map assemble <$> simulateQ
        (OracleInterface.simOracle2 []ₒ stmtIn.2 tr.messages)
        (V.verify stmtIn.1 tr.challenges).run) := by
    exact hy'
  obtain ⟨result, hresult, hresult_eq⟩ :=
    mem_support_map_peel (Option.map assemble) _ hyMap
  cases result with
  | none => simp at hresult_eq
  | some a =>
      -- Collapse the verifier body itself to the deterministic acceptance predicate.
      have hVerify :
          simulateQ (OracleInterface.simOracle2 []ₒ stmtIn.2 tr.messages)
              (V.verify stmtIn.1 tr.challenges).run =
            pure (if Accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
              (tr.challenges ⟨0, rfl⟩) (tr.messages ⟨1, rfl⟩)
              (tr.challenges ⟨2, rfl⟩)
              then some () else none) := by
        simpa only [V] using oracleVerifier_simulateQ_eq_pure_ite
          (k := k) (t := t) encode stmtIn.1 stmtIn.2 tr.challenges tr.messages
      rw [hVerify] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      split at hresult
      · rename_i hcond
        exact hcond
      · contradiction

omit [Fintype ι] [DecidableEq ι] [Fintype F] [Fintype A] in
/-- Round-by-round-framework wrapper for `accepts_of_mem_support_verifier_run`, consuming the
exact hypothesis shape that `KnowledgeStateFunction.toFun_full`
(`ArkLib/OracleReduction/Security/RoundByRound.lean`) provides for the C6.2 oracle verifier:
if the verifier's simulated run on a fixed transcript outputs, with positive probability, a
statement that is `relOut`-related to some `witOut` (for **any** `relOut`, in particular
`Set.univ`), then the decision predicate `Accepts` holds on that transcript. This is the
entry point for the L6.8 round-by-round knowledge-soundness state function: at the full
transcript it converts the framework's `Pr[…] > 0` acceptance hypothesis into the concrete
accept equations that the soundness arguments consume. -/
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
    Accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
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
/-- The post-`γ` knowledge state of the round-by-round argument: `m`
satisfies the folded linear constraint at `γ`, and `f₁ + γ·f₂` agrees with
`encode m` on a `≥ (1-δ)`-fraction column set. Shaped to match the event of
`ToyProblem.gamma_transition_prob_le` exactly.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) reuses it as its γ-round prefix event. -/
def GammaState (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
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

Public (not `private`) because the alphabet-generic compatibility theorems reuse
it. The executable C6.9/L6.10 path does not: it is instantiated in
`Impl/IRS.lean` with `simplifiedStraightlineExtractor` and
`simplifiedRbrExtractor`.

**Generic extractor status (B06).** This is a *nonconstructive existence* selector: it is
`noncomputable`, returning a witness via `Classical.choice`. It serves as the abstract
knowledge-extractor *interface* the alphabet-generic L6.6 / L6.8 soundness
proofs are stated against — the only property they consume is `chooseRelaxedWitness_mem`. It is
**not** the paper's deterministic `O(enc + ecor)` erasure-decoder ([ABF26] App A.1).
`Spec/ErasureDecoder.lean` supplies the reusable erasure-decoding kernel;
`Impl/IRS.lean` applies it to the module alphabet `Fin s → F`, computes the
maximal agreement set, and proves the exact extractor-specific game theorems. -/
noncomputable def chooseRelaxedWitness (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Witness (F := F) k :=
  if h : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ then h.choose
  else fun _ _ ↦ 0

omit [DecidableEq ι] [DecidableEq F] [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A] in
/-- If a relaxed-relation witness exists at all, `chooseRelaxedWitness` returns one.
(Shared by the L6.8 γ-round bound and the L6.10 game bound.) -/
lemma chooseRelaxedWitness_mem {encode : (Fin k → F) → (ι → A)} {δ : ℝ≥0}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)}
    (hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ) :
    (stmtIn, chooseRelaxedWitness k encode δ stmtIn) ∈ outputRelationFor k encode δ := by
  unfold chooseRelaxedWitness; rw [dif_pos hw]; exact hw.choose_spec

/-- **Decoder-parametrized extractor wrapper** (B06, conditional). Given a
per-oracle decoder `dec : (ι → A) → (Fin k → F)`, decode each oracle codeword
`stmtIn.2 i` independently. This is a *thin wrapper*: it delegates all work to `dec`
and proves nothing about `dec`'s correctness on its own.

`#print axioms erasureExtractor` is axiom-free — but only because it is trivial (it
does nothing without a decoder). It is not, by itself, the computable extractor, and the
alphabet-generic proofs still use `chooseRelaxedWitness` (`Classical.choice`). The scalar-RS path
in `Spec/ErasureDecoder.lean` does not use this fixed-input wrapper: after `γ` and `g` are
known, it computes the actual agreement set and invokes its concrete erasure decoder on
both rows. This avoids the raw-error-decoding problem entirely and retains the full
`δ < δ_min` range.

**Cost (aspirational, unclocked).** For an ideal decoder the paper's `O(enc + ecor)`
would be one `dec` per oracle; ArkLib has no cost harness (prose bounds only, cf.
`Data/CodingTheory/Erasure.lean`). Not realized end-to-end here. -/
def erasureExtractor (dec : (ι → A) → (Fin k → F))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Witness (F := F) k :=
  fun i ↦ dec (stmtIn.2 i)

omit [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
omit [AddCommGroup A] [Module F A] in
/-- **Conditional membership for the wrapper.** If some valid witness `M` exists *and* the
decoder already recovers it (`erasureExtractor dec stmtIn = M`), then the decoded witness
lies in the relaxed output relation. Note this hypothesis is strictly stronger than
`chooseRelaxedWitness_mem`'s (which needs only existence): here the decoder's correctness is
*assumed*, not established — this lemma does not by itself produce a valid witness, it
merely propagates one the decoder is assumed to already find. Proven constructively (no
`choose_spec`). -/
lemma erasureExtractor_mem {encode : (Fin k → F) → (ι → A)} {δ : ℝ≥0}
    {dec : (ι → A) → (Fin k → F)}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)}
    (hrec : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ ∧
      erasureExtractor k dec stmtIn = M) :
    (stmtIn, erasureExtractor k dec stmtIn) ∈ outputRelationFor k encode δ := by
  obtain ⟨M, hM, hEq⟩ := hrec
  rw [hEq]; exact hM

omit [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
omit [AddCommGroup A] [Module F A] in
/-- **Conditional reduction via an assumed left-inverse decoder.** If `dec` left-inverts
`encode` on the oracle codewords of *every* valid witness (`dec (stmtIn.2 i) = M i`), the
wrapper satisfies the output relation. The left-inverse hypothesis `hli` is the crux and
is **assumed, not proven here**: for a Reed–Solomon / interpolation code an interpolating
decoder reproduces `M i` only when it interpolates through `k` genuinely *uncorrupted*
coordinates, and `outputRelationFor` guarantees only that *some* size-`≥ (1−δ)|ι|`
agreement set exists — not which coordinates it contains. The scalar-RS transition
extractor in `Spec/ErasureDecoder.lean` obtains those coordinates from the post-`γ`
equality with the supplied `g`; this generic fixed-input lemma deliberately does not model
that extra transition data. Cf.
`Data/CodingTheory/Erasure.lean` (uniqueness below `minDist` erasures,
`eq_of_consistent_with_erased`). The paper's generic polynomial-time implementation claim remains
outside ArkLib's current cost model. -/
lemma erasureExtractor_mem_of_leftInverse {encode : (Fin k → F) → (ι → A)} {δ : ℝ≥0}
    {dec : (ι → A) → (Fin k → F)}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)}
    (hex : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ)
    (hli : ∀ M, (stmtIn, M) ∈ outputRelationFor k encode δ →
      ∀ i, dec (stmtIn.2 i) = M i) :
    (stmtIn, erasureExtractor k dec stmtIn) ∈ outputRelationFor k encode δ := by
  obtain ⟨M, hM⟩ := hex
  exact erasureExtractor_mem (k := k) ⟨M, hM, funext (hli M hM)⟩

omit [DecidableEq ι] in
/-- The round-by-round extractor: round 0 extracts a
relaxed-relation witness by choice, round 1 passes the candidate message
through, round 2 reads the prover's claim `g` off the transcript. -/
private noncomputable def rbrExtractor (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    Extractor.RoundByRound []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) (rbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn _ _ ↦ chooseRelaxedWitness k encode δ stmtIn
  | ⟨1, _⟩ => fun _ _ w ↦ w
  | ⟨2, _⟩ => fun _ tr _ ↦ tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

omit [DecidableEq ι] in
/-- The round-by-round knowledge state function: relaxed-relation
membership at round 0, `GammaState` after rounds 1–2, and the acceptance
predicate after the spot-check round (the witness-ignoring final state is a
deliberate repair of the paper's printed state — see the assembly section
comment above). -/
private noncomputable def rbrKnowledgeStateFunction
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((oracleVerifier (k := k) (t := t) encode).toVerifier).KnowledgeStateFunction init impl
      (outputRelationFor k encode δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (rbrExtractor k t encode δ) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦ (stmtIn, w) ∈ outputRelationFor k encode δ
  | ⟨1, _⟩ => fun stmtIn tr w ↦
      GammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨2, _⟩ => fun stmtIn tr w ↦
      GammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      Accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
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

omit [DecidableEq ι] [DecidableEq F] [Fintype A] in
/-- Per-transcript combination-round bound for the generic classical
toy-protocol extractor.  The error is the certified affine-line
MCA-plus-two-row-list upper bound. -/
lemma gamma_round_game_bound [SampleableType F] [Nonempty ι] [Finite A]
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = (C : Set (ι → A)))
    (hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Pr[fun γ : F ↦ ∃ w : Fin k → F,
        (stmtIn, chooseRelaxedWitness k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          GammaState k (encode : (Fin k → F) → (ι → A)) δ
            stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ w
      | $ᵗ F] ≤ (certifiedGammaError C δ : ENNReal) := by
  classical
  let _ := Fintype.ofFinite A
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M,
      (stmtIn, M) ∈ outputRelationFor k
        (encode : (Fin k → F) → (ι → A)) δ
  · refine le_trans (le_of_eq ?_) zero_le
    rw [prob_tsum_form_singleton]
    have hnot : ∀ γ : F, ¬ (∃ w : Fin k → F,
        (stmtIn, chooseRelaxedWitness k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          GammaState k (encode : (Fin k → F) → (ι → A)) δ
            stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ w) :=
      fun _ h ↦ h.choose_spec.1 (chooseRelaxedWitness_mem k hw)
    simp [hnot]
  · refine le_trans (Pr_le_Pr_of_implies _ _
      (fun γ ↦ ∃ m : Fin k → F,
        (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j) ?_) ?_
    · rintro γ ⟨m, -, hm⟩
      exact ⟨m, hm⟩
    · have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
          (∀ i : Fin 2, ∑ j, M i j * stmtIn.1.1 j =
            ![stmtIn.1.2.1, stmtIn.1.2.2] i) ∧
          ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
            ∀ i : Fin 2, ∀ j ∈ S,
              ![stmtIn.2 0, stmtIn.2 1] i j = encode (M i) j := by
        rintro ⟨M, h1, S, h2, h3⟩
        refine hw ⟨M, h1, S, h2, fun i j hj ↦ ?_⟩
        fin_cases i
        · simpa using h3 0 j hj
        · simpa using h3 1 j hj
      refine le_trans (gamma_transition_prob_le C δ encode hinj hC hδ_pos hδ_lt
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) hNoWit) (le_of_eq ?_)
      rw [coe_certifiedGammaError]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- Per-transcript spot-check-round bound for the toy protocol: if the
post-combination knowledge state is false, uniform spot checks accept with
probability at most `(1 - δ)^t`. -/
lemma spotcheck_round_game_bound [Nonempty ι]
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (γ : F) (g : Fin k → F) [SampleableType (Fin t → ι)] :
    Pr[fun xs : Fin t → ι ↦ ∃ _w : PUnit,
        ¬ GammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g ∧
          Accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2 γ g xs
      | $ᵗ (Fin t → ι)] ≤ (((1 - δ) ^ t : ℝ≥0) : ENNReal) := by
  classical
  let _ : DecidableEq F := Classical.decEq F
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hbad : GammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
      (stmtIn.2 0) (stmtIn.2 1) γ g
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le
    rintro xs ⟨-, hne, -⟩
    exact hne hbad
  by_cases hlin : ∑ j, g j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2
  swap
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le
    rintro xs ⟨-, -, hacc⟩
    exact hlin hacc.1
  let S₀ : Finset ι :=
    Finset.univ.filter (fun j ↦ stmtIn.2 0 j + γ • stmtIn.2 1 j = encode g j)
  have hι : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAcard : (S₀.card : ℝ) < (1 - (δ : ℝ)) * Fintype.card ι :=
    not_le.mp fun hge ↦ hbad ⟨hlin, S₀, hge,
      fun j hj ↦ (Finset.mem_filter.mp hj).2⟩
  have hδ1 : δ ≤ 1 := by
    by_contra hgt
    have h1δ : (1 : ℝ) - (δ : ℝ) < 0 :=
      sub_neg.mpr (by exact_mod_cast not_le.mp hgt)
    linarith [mul_neg_of_neg_of_pos h1δ hι,
      (Nat.cast_nonneg S₀.card : (0 : ℝ) ≤ S₀.card)]
  have hbase : ((S₀.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ 1 - δ := by
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ≥0) < Fintype.card ι), ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hδ1]
    linarith
  refine le_trans (Pr_le_Pr_of_implies _ _ (fun xs ↦ ∀ j, xs j ∈ S₀) ?_) ?_
  · rintro xs ⟨-, -, hacc⟩ j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hacc.2 j).symm⟩
  · refine le_trans (prob_uniform_pi_mem_finset_le S₀ t) ?_
    rw [ENNReal.coe_pow]
    refine pow_le_pow_left' ?_ t
    rw [show ((S₀.card : ENNReal)) = ((S₀.card : ℝ≥0) : ENNReal) from
        (ENNReal.coe_natCast _).symm,
      show ((Fintype.card ι : ENNReal)) =
        ((Fintype.card ι : ℝ≥0) : ENNReal) from (ENNReal.coe_natCast _).symm,
      ← ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    exact ENNReal.coe_le_coe.mpr hbase

omit [DecidableEq ι] [Fintype A] in
/-- Worst-case-per-fixed-prefix round-by-round knowledge soundness of
the toy protocol in the alphabet-generic classical-extractor form.  Concrete
IRS clients should prefer `Impl.IRS.oracleVerifier_rbrKnowledgeSoundnessWorstCase`,
whose extractor is executable and named. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWorstCase
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Finite A]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = (C : Set (ι → A)))
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ <
      (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0)) :
    ((oracleVerifier (k := k) (t := t)
      (encode : (Fin k → F) → (ι → A))).toVerifier).rbrKnowledgeSoundnessWorstCase
      (WitIn := Witness (F := F) k) (WitOut := OutputWitness)
      init impl (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness))
      (fun i ↦ if i.1 = 0 then certifiedGammaError C δ else (1 - δ) ^ t) := by
  let _ := Fintype.ofFinite A
  unfold Verifier.rbrKnowledgeSoundnessWorstCase
  refine ⟨rbrWitMid (F := F) k,
    rbrExtractor k t (encode : (Fin k → F) → (ι → A)) δ,
    rbrKnowledgeStateFunction k t (encode : (Fin k → F) → (ι → A)) δ init impl, ?_⟩
  intro stmtIn i transcript
  obtain ⟨⟨iv, hi⟩, hdir⟩ := i
  rcases iv with _ | _ | _ | iv
  · exact gamma_round_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min stmtIn
  · exact absurd hdir (fun h ↦ Direction.noConfusion h)
  · exact spotcheck_round_game_bound k t
      (encode : (Fin k → F) → (ι → A)) δ stmtIn
      (transcript ⟨0, Nat.zero_lt_succ _⟩)
      (transcript ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
  · exact absurd hi (by omega)

omit [DecidableEq ι] [Fintype A] in
/-- Averaged round-by-round knowledge soundness, retained under the established
public API name as a corollary of the stronger worst-case-per-prefix theorem. -/
theorem oracleVerifier_rbrKnowledgeSoundness
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Finite A]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = (C : Set (ι → A)))
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ <
      (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0)) :
    (oracleVerifier (k := k) (t := t)
      (encode : (Fin k → F) → (ι → A))).rbrKnowledgeSoundness
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
        OutputWitness))
      (fun i ↦ if i.1 = 0 then certifiedGammaError C δ else (1 - δ) ^ t) := by
  let _ := Fintype.ofFinite A
  unfold OracleVerifier.rbrKnowledgeSoundness
  exact Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    init impl (oracleVerifier_rbrKnowledgeSoundnessWorstCase k t init impl C δ encode
      hinj hC hδ_pos hδ_lt_min)

end Protocol

end Spec

end ToyProblem
