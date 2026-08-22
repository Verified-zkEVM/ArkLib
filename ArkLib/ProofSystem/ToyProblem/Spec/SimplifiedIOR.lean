/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.ToyProblem.Spec.General
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds

/-!
# Simplified toy-problem IOR (ABF26 Construction 6.9)

The "attack target" simplified IOR from ABF26 §6.4. Unlike the full
Construction 6.2, this version:

  * has **one round** (V→P combination randomness only — no spot-check),
  * does **not** test acceptance (no final `guard`); instead it
    *reduces* the input instance `(v, μ₁, μ₂, f₁, f₂)` to a smaller
    instance `(v, μ₁ + γ·μ₂, f₁ + γ·f₂)`,
  * is therefore a reduction from the fixed-encoding `R̃²_{C,δ}` to the
    fixed-encoding `R̃¹_{C,δ}`.

This file follows the FRI/Sumcheck `Spec/` convention exactly (mirroring
`ToyProblem/Spec/General.lean`). The two protocols live in sibling
files because they are structurally distinct (C6.2 is a 3-round
yes/no test; C6.9 is a 1-round reducing protocol).

## Protocol

```
Verifier input  : (v, μ₁, μ₂) explicit, (f₁, f₂) oracle.
Prover witness  : (M₁, M₂) ∈ (F^k)² with C(Mᵢ) = fᵢ, ⟨Mᵢ, v⟩ = μᵢ.

Round 0  V → P : γ ←$ F.
Outputs:
  Verifier sets statement x* := (v, μ₁ + γ·μ₂) and oracle y* := f₁ + γ·f₂.
  Honest prover sets witness w* := M₁ + γ·M₂.
```

Perfect completeness says that an input in `R̃²_{C,δ}` maps to an output in
`R̃¹_{C,δ}` for every challenge. In the converse direction, L6.10 bounds the
probability that an input outside `R̃²_{C,δ}` nevertheless maps into `R̃¹_{C,δ}`.

## Codeword alphabet `A` (folding-generic)

As in `Spec/General.lean`, this layer is generic over the codeword
alphabet `A` (an `F`-module). The scalar specialization is `A = F`.
`Impl/IRS.lean` realizes genuine interleaved Reed--Solomon with
`A = Fin s → F`, while `Impl/FRS.lean` is the separate folded-RS model.
The relative Hamming metric is over `A` (one symbol = one
`A`-coordinate); reindexing `ι := [n] × [s]` over a scalar alphabet would
not recover that column metric. The challenge `γ` and constraints stay
scalar; the combined output oracle is `f₁ + γ • f₂` over `A`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.4, Construction 6.9, Lemma 6.10).
-/

namespace ToyProblem

namespace SimplifiedIOR

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ProximityGap
open scoped NNReal ENNReal
open Probability
open ToyProblem.Spec (Statement OracleStatement Witness)

-- The code-theoretic certificate uses `[Fintype A]`/`[DecidableEq A]`
-- (and `[DecidableEq F]` via the `classical` proofs) in their bodies but not in the
-- alphabet-generic lemma types; suppress the `unused…InType` linter file-wide (the same toy
-- idiom as `SoundnessBounds.lean` / `Spec/General.lean`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Output types and the output relation

These need only `[Fintype ι]` (for `RelaxedRelationFor`'s `Fintype.card ι`
call) and `[Field F]`. The heavier `[DecidableEq ι] [Fintype F]
[DecidableEq F]` instances come in below for the protocol-object
definitions. -/

variable {ι F A : Type} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]
variable (k : ℕ)

/-- Output statement for C6.9: the new `(v, μ_new)` pair. The
constraint count drops from 2 to 1 (a single combined linear
constraint). -/
@[reducible]
def OutputStatement : Type := (Fin k → F) × F

/-- Output oracle statement: the single combined codeword
`f_new := f₁ + γ • f₂ : ι → A`. -/
@[reducible]
def OutputOracleStatement (ι A : Type) : Fin 1 → Type := fun _ ↦ ι → A

/- Keep the public output-oracle API canonical even when `A` is itself a
function type: a query selects one coordinate of the codeword. -/
@[reducible] instance (priority := 10000) :
    ∀ i, OracleInterface (OutputOracleStatement ι A i) :=
  fun _ ↦ OracleInterface.instFunction

/-- Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`. -/
@[reducible]
def OutputWitness : Type := Fin k → F

/-- The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of
the simplified IOR.

Bundles the post-step instance `((v, μ_new), f_new)` together with the
post-step witness `M_new` and asserts that `(v, μ_new, f_new)` is
`δ`-close to `encode M_new` and that `M_new` satisfies the combined
linear constraint.

Type-aligned with `OutputStatement × (∀ i, OutputOracleStatement ι A i)
× OutputWitness`, i.e. directly consumable by the L6.10 knowledge-
soundness statement against `verifier.knowledgeSoundness`. -/
def outputRelationFor (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0) :
    Set ((OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) ×
      OutputWitness (F := F) k) :=
  fun input ↦
    (∑ j, input.2 j * input.1.1.1 j = input.1.1.2) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ j ∈ S, input.1.2 0 j = encode input.2 j

/-- The language-level one-word relaxed relation is precisely the existential
closure of the witness-bearing C6.9 output relation. -/
theorem relaxedRelationFor_iff_exists_outputRelationFor
    (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (stmt : OutputStatement (F := F) k)
    (oStmt : ∀ i, OutputOracleStatement ι A i) :
    RelaxedRelationFor (ℓ := 1) encode δ stmt.1 (fun _ ↦ stmt.2) oStmt ↔
      ∃ M, ((stmt, oStmt), M) ∈
        outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ := by
  constructor
  · rintro ⟨Wstar, ⟨M, hW, hlin⟩, S, hcard, hagree⟩
    refine ⟨M 0, ?_, S, hcard, ?_⟩
    · simpa using hlin 0
    · intro j hj
      change oStmt 0 j = encode (M 0) j
      rw [hagree 0 j hj, hW 0]
  · rintro ⟨M, hlin, S, hcard, hagree⟩
    refine ⟨fun _ ↦ encode M, ⟨fun _ ↦ M, ?_, ?_⟩, S, hcard, ?_⟩
    · intro i
      fin_cases i
      rfl
    · intro i
      fin_cases i
      simpa using hlin
    · intro i j hj
      fin_cases i
      exact hagree j hj

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]

/-- Protocol specification for the simplified IOR: a single
`V → P` round sending the combination randomness `γ : F`. -/
@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[F]⟩

instance : ∀ j, OracleInterface ((pSpec (F := F)).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (F := F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance [SampleableType F] : ∀ j, SampleableType ((pSpec (F := F)).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)

instance : ProtocolSpec.VerifierFirst (pSpec (F := F)) := ⟨rfl⟩

instance : ProtocolSpec.VerifierOnly (pSpec (F := F)) := ⟨⟩

/-- Honest prover for the simplified IOR. After receiving `γ`, sets the
new witness `M_new := M₀ + γ·M₁` and outputs the reduced instance.

State machine (`PrvState : Fin 2 → Type`):
  * `PrvState 0` — initial: bundled `(stmt, oStmt) × witness`.
  * `PrvState 1` — after receiving γ: `γ × bundle`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) (OutputWitness (F := F) k)
      (pSpec (F := F)) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι A i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h

  output := fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦ pure <|
    ⟨⟨(stmt.1, stmt.2.1 + γ * stmt.2.2),
       fun _ ↦ fun j ↦ oStmt 0 j + γ • oStmt 1 j⟩,
      fun j ↦ M 0 j + γ * M 1 j⟩

/-- Honest verifier for the simplified IOR. Reads `γ` from the transcript
and produces the new statement `(v, μ₁ + γ·μ₂)` and oracle
`f_new := f₁ + γ·f₂`. Always accepts — the "test" semantics of C6.2
become a "reduce" semantics here.

`encode` is not used (the reduced instance is what it is — testing it
against the code is a separate downstream concern). -/
def verifier :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i))
      (pSpec (F := F)) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    pure ((stmt.1, stmt.2.1 + γ * stmt.2.2),
           fun _ ↦ fun j ↦ oStmt 0 j + γ • oStmt 1 j)

/-- Honest reduction for the simplified IOR. -/
def reduction :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) (OutputWitness (F := F) k)
      (pSpec (F := F)) where
  prover := prover (ι := ι) (F := F) (k := k)
  verifier := verifier (k := k)

/-! ### Genuine virtual-oracle IOR

Construction 6.9's output oracle is derived rather than forwarded. The
`OracleOutputSimulation` below gives both views required by ArkLib:

* `materializeOutput` supplies the extensional function used by relation-facing
  bundled semantics;
* `simulateOutputQuery` answers each downstream query by querying both input oracles at
  that point and returning their `γ`-linear combination.

The agreement field proves these are the same oracle. -/

/-- Query an input codeword at one coordinate in the full verifier oracle
context. -/
def queryInput {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (pSpec.Message i)] (i : Fin 2) (x : ι) :
    OracleComp ([]ₒ + ([OracleStatement ι A]ₒ + [pSpec.Message]ₒ)) A :=
  liftM <| OracleSpec.query
    (show ([]ₒ + ([OracleStatement ι A]ₒ + [pSpec.Message]ₒ)).Domain from
      Sum.inr (Sum.inl ⟨i, x⟩))

omit [Fintype ι] [AddCommGroup A] [DecidableEq ι] [Fintype A] [DecidableEq A] in
@[simp]
theorem simulateQ_queryInput {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (pSpec.Message i)]
    (oStmt : ∀ i, OracleStatement ι A i) (messages : pSpec.Messages)
    (i : Fin 2) (x : ι) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt messages)
        (queryInput (A := A) pSpec i x) = pure (oStmt i x) := by
  simp only [MessageIdx, Message, OracleInterface.simOracle2, QueryImpl.addLift,
    queryInput, Lean.Elab.WF.paramLet, simulateQ_query, OracleQuery.input_query,
    add_apply_inr, add_apply_inl, OracleQuery.cont_query, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change id <$> (pure (oStmt i x) : OracleComp []ₒ A) = pure (oStmt i x)
  simp only [map_pure, id_eq]

/-- Virtual implementation of the combined C6.9 output oracle. -/
def outputSimulation :
    OracleOutputSimulation []ₒ
      (OracleStatement ι A)
      (OutputOracleStatement ι A) (pSpec (F := F)) where
  materializeOutput := fun challenges oStmt _ _ j ↦
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    oStmt 0 j + γ • oStmt 1 j
  simulateOutputQuery := fun challenges q ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let f₀ : A ← queryInput (A := A) (pSpec (F := F)) 0 q.2
    let f₁ : A ← queryInput (A := A) (pSpec (F := F)) 1 q.2
    pure (f₀ + γ • f₁)
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rcases q with ⟨i, j⟩
    fin_cases i
    rw [simulateQ_bind, simulateQ_queryInput, pure_bind]
    rw [simulateQ_bind, simulateQ_queryInput, pure_bind]
    simp only [OracleInterface.simOracle2, QueryImpl.addLift_def,
      QueryImpl.simulateQ_add_liftM_left, simulateQ_pure]
    with_unfolding_all rfl

/-- Honest prover at the oracle-reduction signature. -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι A) (Witness (F := F) k)
      (OutputStatement (F := F) k) (OutputOracleStatement ι A)
      (OutputWitness (F := F) k) (pSpec (F := F)) :=
  prover (ι := ι) (F := F) (k := k)

/-- Oracle verifier for the simplified IOR. The explicit output is the combined
linear claim; the output codeword is supplied by `outputSimulation`. -/
def oracleVerifier :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι A)
      (OutputStatement (F := F) k) (OutputOracleStatement ι A)
      (pSpec (F := F)) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    pure (stmt.1, stmt.2.1 + γ * stmt.2.2)
  outputOracle := .inr (outputSimulation (ι := ι) (F := F) (A := A))

/-- The simplified protocol as a genuine interactive oracle reduction. -/
def oracleReduction :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι A) (Witness (F := F) k)
      (OutputStatement (F := F) k) (OutputOracleStatement ι A)
      (OutputWitness (F := F) k) (pSpec (F := F)) where
  prover := oracleProver (ι := ι) (F := F) (k := k)
  verifier := oracleVerifier (ι := ι) (F := F) (A := A) (k := k)

/-- The unique C6.9 verifier challenge in a full transcript. -/
def transcriptGamma (tr : (pSpec (F := F)).FullTranscript) : F :=
  tr.challenges ⟨⟨0, by decide⟩, by rfl⟩

/-- The explicit statement and extensional virtual oracle derived by C6.9. -/
def derivedOutput
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (γ : F) : OutputStatement (F := F) k ×
      (∀ i, OutputOracleStatement ι A i) :=
  ((stmtIn.1.1, stmtIn.1.2.1 + γ * stmtIn.1.2.2),
    fun _ j ↦ stmtIn.2 0 j + γ • stmtIn.2 1 j)

/-- Turn a deterministic C6.9 transition algorithm into the straightline
extractor shape used by ArkLib's exact-extractor game. -/
def transitionStraightlineExtractor
    (transition :
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) →
        F → (Fin k → F) → Witness (F := F) k) :
    Extractor.Straightline []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i))
      (Witness (F := F) k) (OutputWitness (F := F) k)
      (pSpec (F := F)) :=
  fun stmtIn g tr _ _ ↦ pure <|
    transition stmtIn (transcriptGamma (F := F) tr) g

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] in
@[simp]
theorem oracleVerifier_toVerifier_run_eq_pure
    (stmtIn : Statement (F := F) k ×
      (∀ i, OracleStatement ι A i))
    (tr : (pSpec (F := F)).FullTranscript) :
    ((oracleVerifier (ι := ι) (F := F) (A := A) (k := k)).toVerifier).run
        stmtIn tr =
      pure (derivedOutput (ι := ι) (F := F) (A := A) k stmtIn
        (transcriptGamma (F := F) tr)) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier,
    outputSimulation, transcriptGamma, derivedOutput, bind_pure_comp]
  erw [simulateQ_optionT_pure
    (OracleInterface.simOracle2 []ₒ stmtIn.2 tr.messages)
    (stmtIn.1.1, stmtIn.1.2.1 +
      transcriptGamma (F := F) tr * stmtIn.1.2.2)]
  rfl

set_option linter.unusedSectionVars false in
/-- The bundled security view of the virtual-oracle verifier is extensionally
the original materialized C6.9 verifier. -/
theorem oracleVerifier_toVerifier_eq_verifier :
    (oracleVerifier (ι := ι) (F := F) (A := A) (k := k)).toVerifier =
      verifier (ι := ι) (F := F) (A := A) (k := k) := by
  ext stmtIn tr
  exact oracleVerifier_toVerifier_run_eq_pure (k := k) stmtIn tr

set_option linter.unusedSectionVars false in
/-- Positive probability of producing an output related to `witOut` forces the
deterministic C6.9 derived output itself to be related to `witOut`. -/
theorem mem_outputRelationFor_of_probEvent_pos_oracleVerifier_run
    {X : Type} (init : ProbComp X)
    (impl : QueryImpl []ₒ (StateT X ProbComp))
    (encode : (Fin k → F) → (ι → A)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i))
    (tr : (pSpec (F := F)).FullTranscript)
    (witOut : OutputWitness (F := F) k)
    (h : Pr[ fun stmtOut ↦ (stmtOut, witOut) ∈ outputRelationFor k encode δ
      | OptionT.mk do
          (simulateQ impl
            (((oracleVerifier (ι := ι) (F := F) (A := A) (k := k)).toVerifier).run
              stmtIn tr)).run' (← init)] > 0) :
    (derivedOutput (ι := ι) (F := F) (A := A) k stmtIn
      (transcriptGamma (F := F) tr), witOut) ∈ outputRelationFor k encode δ := by
  have hrun (s : X) :
      (simulateQ impl
        (((oracleVerifier (ι := ι) (F := F) (A := A) (k := k)).toVerifier).run
          stmtIn tr)).run' s =
        (pure (some (derivedOutput (ι := ι) (F := F) (A := A) k stmtIn
          (transcriptGamma (F := F) tr))) : ProbComp _) := by
    rw [oracleVerifier_toVerifier_run_eq_pure]
    rw [simulateQ_optionT_pure]
    rfl
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨stmtOut, hmem, hrel⟩ := h
  obtain ⟨s₀, -, hmem⟩ := OptionT.mem_support_bind_mk init _ hmem
  rw [OptionT.mem_support_iff] at hmem
  rw [hrun] at hmem
  simp only [OptionT.run_mk, support_pure, Set.mem_singleton_iff,
    Option.some.injEq] at hmem
  rwa [hmem] at hrel

/-! ### Knowledge-soundness assembly

`knowledgeSoundnessWith_of_transition_failure_prob_le` is the principal assembly: it keeps a
deterministic transition extractor in the game type and applies equally to
the virtual-oracle verifier. `gamma_game_bound` and
`verifier_knowledgeSoundness` retain the older alphabet-generic
classical-choice existence result as a compatibility fallback. -/

omit [DecidableEq ι] in
/-- The γ-round bound (via
`ToyProblem.gamma_transition_prob_le`): if the choice extractor fails on
`stmtIn` then no `R̃²` witness exists, and the probability over a uniform `γ`
that the folded instance has an `R̃¹` witness is at most
`ε_mca + |Λ(C^{≡2}, δ)| / |F|`. Stated in the reduced form of the L6.10 game
event so the master lemma's challenge-only hypothesis can consume it. -/
private lemma gamma_game_bound [SampleableType F] [Nonempty ι]
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = (C : Set (ι → A)))
    (hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Pr[fun γ : F ↦
        (stmtIn, Spec.chooseRelaxedWitness k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          ∃ m : Fin k → F,
            (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
            ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
              ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j
      | $ᵗ F] ≤
      (certifiedGammaError C δ : ENNReal) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M,
      (stmtIn, M) ∈ Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ
  · -- The choice extractor succeeds, so the event is empty.
    refine le_trans (le_of_eq ?_) zero_le
    rw [prob_tsum_form_singleton]
    have hnot : ∀ γ : F, ¬ (
        (stmtIn, Spec.chooseRelaxedWitness k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          ∃ m : Fin k → F,
            (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
            ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
              ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j) :=
      fun _ h ↦ h.1 (Spec.chooseRelaxedWitness_mem k hw)
    simp [hnot]
  · refine le_trans (Pr_le_Pr_of_implies _ _
      (fun γ ↦ ∃ m : Fin k → F,
        (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j) ?_) ?_
    · rintro γ ⟨-, hm⟩
      exact hm
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
      rw [coe_certifiedGammaError]

set_option linter.unusedSectionVars false in
/-- Exact-extractor C6.9 knowledge-soundness assembly.  Any deterministic
transition algorithm whose challenge failure event has probability at most
`gammaError` yields a straightline game theorem that keeps that algorithm in
the proposition type. -/
theorem knowledgeSoundnessWith_of_transition_failure_prob_le
    [SampleableType F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (δ gammaError : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (transition :
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) →
        F → (Fin k → F) → Witness (F := F) k)
    (hgamma : ∀ stmtIn,
      Pr[ fun γ : F ↦ ∃ g : Fin k → F,
          (stmtIn, transition stmtIn γ g) ∉
              Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
            Spec.GammaState k (encode : (Fin k → F) → (ι → A)) δ
              stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
              (stmtIn.2 0) (stmtIn.2 1) γ g
        | $ᵗ F] ≤ (gammaError : ENNReal)) :
    (oracleVerifier (ι := ι) (F := F) (A := A) (k := k)).knowledgeSoundnessWith
      (WitOut := OutputWitness (F := F) k)
      init impl
      (Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
      (transitionStraightlineExtractor k transition) gammaError := by
  classical
  unfold OracleVerifier.knowledgeSoundnessWith
  rw [oracleVerifier_toVerifier_eq_verifier (k := k)]
  unfold Verifier.knowledgeSoundnessWith
  rintro ⟨stmt, oStmt⟩ witIn prover
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ (liftComp (prover.receiveChallenge ⟨0, rfl⟩
        (prover.input ((stmt, oStmt), witIn))) ([]ₒ + [(pSpec (F := F)).Challenge]ₒ))
      >>= fun fc ↦ prover.output (fc γ))
    (fun (γ : F) t ↦ ((stmt, oStmt),
      some (transition (stmt, oStmt) γ t.2),
      ((stmt.1, stmt.2.1 + γ * stmt.2.2),
        (fun _ j ↦ oStmt 0 j + γ • oStmt 1 j :
          ∀ i, OutputOracleStatement ι A i)),
      t.2))
    _ ?_ ?_
  · simp only [Reduction.runWithLog, Verifier.run, verifier,
      transitionStraightlineExtractor, Prover.runWithLog,
      OptionT.run_pure, liftM_pure, pure_bind, bind_assoc]
    simp only [loggingOracle.run_simulateQ_optionT_pure, liftM_pure, pure_bind,
      Option.getM_some]
    simp only [OptionT.liftM_def, bind_pure_comp]
    simp only [OptionT.run_map, OptionT.run_lift, bind_pure_comp, Functor.map_map,
      Option.map_some]
    refine Eq.trans (loggingOracle.map_fst_run_simulateQ
      (Prover.run (stmt, oStmt) witIn prover)
      (fun y : (pSpec (F := F)).FullTranscript ×
          ((OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) ×
            OutputWitness (F := F) k) ↦
        let γ : F := y.1 ⟨0, Nat.one_pos⟩
        some ((stmt, oStmt), some (transition (stmt, oStmt) γ y.2.2),
          ((stmt.1, stmt.2.1 + γ * stmt.2.2),
            fun _ j ↦ oStmt 0 j + γ • oStmt 1 j),
          y.2.2))) ?_
    rw [Prover.run_of_verifier_first]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
    rfl
  · refine le_trans ?_ (hgamma (stmt, oStmt))
    refine probEvent_mono ?_
    rintro γ - ⟨t, hbad, hrel⟩
    exact ⟨t.2, hbad _ rfl, hrel⟩

omit [DecidableEq ι] in
/-- Legacy alphabet-generic straightline knowledge-soundness existence
theorem for C6.9. It uses the noncomputable `Spec.chooseRelaxedWitness` selector and
therefore is not the deterministic round-by-round Definition A.5 result.

The executable exact-extractor contracts are
`Impl.IRS.simplifiedOracleVerifier_knowledgeSoundnessWith_straightlineExtractor`
and
`Impl.IRS.simplifiedOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`;
existential knowledge soundness is a corollary there. -/
theorem verifier_knowledgeSoundness
    [SampleableType F] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = (C : Set (ι → A)))
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ <
      (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0)) :
      (verifier (ι := ι) (F := F) (k := k)).knowledgeSoundness
        (WitOut := OutputWitness (F := F) k)
        init impl
        (ToyProblem.Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
        (outputRelationFor (ι := ι) (F := F) k (encode : (Fin k → F) → (ι → A)) δ)
        (certifiedGammaError C δ) := by
  classical
  unfold Verifier.knowledgeSoundness
  -- The straightline extractor: classical choice of any `R̃²` witness, from the
  -- input statement alone (always-`some`; cf. `Spec.chooseRelaxedWitness`).
  refine ⟨fun stmtIn _ _ _ _ ↦
    pure (Spec.chooseRelaxedWitness k ((encode : (Fin k → F) → (ι → A))) δ stmtIn), ?_⟩
  rintro ⟨stmt, oStmt⟩ witIn prover
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ (liftComp (prover.receiveChallenge ⟨0, rfl⟩
        (prover.input ((stmt, oStmt), witIn))) ([]ₒ + [(pSpec (F := F)).Challenge]ₒ))
      >>= fun fc ↦ prover.output (fc γ))
    (fun (γ : F) t ↦ ((stmt, oStmt),
      some (Spec.chooseRelaxedWitness k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
      ((stmt.1, stmt.2.1 + γ * stmt.2.2),
        (fun _ j ↦ oStmt 0 j + γ • oStmt 1 j : ∀ i, OutputOracleStatement ι A i)),
      t.2))
    _ ?_ ?_
  · -- Game-shape reduction: peel the logs and the pure verifier.
    simp only [Reduction.runWithLog, Verifier.run, verifier, Prover.runWithLog,
      OptionT.run_pure, liftM_pure, pure_bind, bind_assoc]
    simp only [loggingOracle.run_simulateQ_optionT_pure, liftM_pure, pure_bind,
      Option.getM_some]
    simp only [OptionT.liftM_def, bind_pure_comp]
    simp only [OptionT.run_map, OptionT.run_lift, bind_pure_comp, Functor.map_map,
      Option.map_some]
    refine Eq.trans (loggingOracle.map_fst_run_simulateQ
      (Prover.run (stmt, oStmt) witIn prover)
      (fun y : (pSpec (F := F)).FullTranscript ×
          ((OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) ×
            OutputWitness (F := F) k) ↦
        let γ : F := y.1 ⟨0, Nat.one_pos⟩
        some ((stmt, oStmt),
          some (Spec.chooseRelaxedWitness k
            ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
          ((stmt.1, stmt.2.1 + γ * stmt.2.2),
            fun _ j ↦ oStmt 0 j + γ • oStmt 1 j),
          y.2.2))) ?_
    rw [Prover.run_of_verifier_first]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
    rfl
  · -- The challenge-only bound: weaken the game event to the γ-round event and
    -- apply `gamma_game_bound`.
    refine le_trans ?_
      (gamma_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min (stmt, oStmt))
    refine probEvent_mono ?_
    rintro c - ⟨t, h1, h2⟩
    exact ⟨h1 _ rfl, t.2, h2⟩

end Protocol

end SimplifiedIOR

end ToyProblem
