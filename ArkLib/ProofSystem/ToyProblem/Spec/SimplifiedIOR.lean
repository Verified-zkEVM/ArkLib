/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ProofSystem.ToyProblem.Spec.General

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

The new instance lies in `R̃¹_{C,δ}` iff the original lay in
`R̃²_{C,δ}` (up to the soundness error of L6.10).

## Codeword alphabet `A` (folding-generic)

As in `Spec/General.lean`: generic over the codeword alphabet `A` (an
`F`-module), with `A = F` the scalar `s = 1` interleaved case
(`Impl/IRS.lean`) and `A = Fin s → F` the genuine `s > 1` folded case
(`Impl/FRS.lean`). The relative Hamming metric is over `A` (one symbol =
one `A`-coordinate), the right folded metric — `ι := [n] × [s]` over a
scalar alphabet would not recover it. The challenge `γ` and constraints
stay scalar; the combined output oracle is `f₁ + γ • f₂` over `A`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.4, Construction 6.9, Lemma 6.10).
-/

namespace ToyProblem

namespace SimplifiedIOR

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal
open Probability
open ToyProblem.Spec (Statement OracleStatement Witness)

-- The code-theoretic terms (`epsMCA`, `interleavedCodeSet`) use `[Fintype A]`/`[DecidableEq A]`
-- (and `[DecidableEq F]` via the `classical` proofs) in their bodies but not in the
-- alphabet-generic lemma types; suppress the `unused…InType` linter file-wide (the same toy
-- idiom as `SoundnessBounds.lean` / `Spec/General.lean`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Output types and the output relation

These need only `[Fintype ι]` (for `relaxedRelationFor`'s `Fintype.card ι`
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
`f_new := f₁ + γ·f₂ : ι → F`. -/
@[reducible]
def OutputOracleStatement (ι A : Type) : Fin 1 → Type := fun _ ↦ ι → A

/-- Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`. -/
@[reducible]
def OutputWitness : Type := Fin k → F

/-- The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of
Construction 6.9.

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

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A]

/-- Protocol specification for Construction 6.9: a single
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

/-- Honest prover for Construction 6.9. After receiving `γ`, sets the
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

/-- Honest verifier for Construction 6.9. Reads `γ` from the transcript
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

/-- Honest reduction for Construction 6.9. -/
def reduction :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι A i)) (Witness (F := F) k)
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι A i)) (OutputWitness (F := F) k)
      (pSpec (F := F)) where
  prover := prover (ι := ι) (F := F) (k := k)
  verifier := verifier (k := k)

/-! ### Why there is no `OracleReduction` flavour for Construction 6.9

C6.9 maps the input oracle pair `(f₁, f₂)` to a **combined** output
oracle `f_new := f₁ + γ·f₂`. ArkLib's current `OracleVerifier`
framework (`ArkLib/OracleReduction/Basic.lean :: OracleVerifier`) only
allows the output oracle family to be a *subset* of the input oracles
plus prover messages, specified via the `embed : ιₛₒ ↪ ιₛᵢ ⊕
pSpec.MessageIdx` field. Concretely, `OracleVerifier.toVerifier`
reads `OStmtOut i` *verbatim* from `embed`, not from the `verify`
body's `OracleComp`.

There is therefore no way, within the current framework, to declare
an output oracle whose contents are a `γ`-dependent linear combination
of the inputs. The concrete prerequisite is **`simOStmt`-based virtual
output oracles**: a refactor sketched in
[`OracleReduction/Basic.lean`](../../OracleReduction/Basic.lean) at
lines 278 and 293 (`simOStmt : QueryImpl [OStmtOut]ₒ
(OracleComp ([OStmtIn]ₒ + [pSpec.Message]ₒ))`), under which the output
oracle `f_new` would be *simulated* by querying `f₁, f₂` and combining.
Once that lands, a C6.9 oracle flavour can be added back here.

Until then, the bundled-input non-oracle `reduction` above captures
the full protocol semantics, and C6.9 as formalized is sound for the
**standalone** statements L6.10 (`simplifiedIOR_knowledgeSound`), L6.12
and L6.13 (`Leaderboard.lean`) — but it is **not composable as an IOR**:
sequential composition with a downstream oracle reduction (which would
consume `f_new` as an input *oracle*) requires the oracle flavour, hence
the `simOStmt` refactor. Downstream IRS instantiations
(`ToyProblem/Impl/IRS.lean :: simplifiedReductionIRS`) consume the
bundled `reduction` directly and are unaffected. -/

/-! ### Lemma 6.10 assembly — γ-round bound and game-shape reduction.

The L6.10 game is the single-round analogue of the L6.8 γ-round
(`Spec/General.lean :: gamma_round_game_bound`): the extractor is the same
classical choice `Spec.extractZero`, and the mathematical content is the same
`ToyProblem.gamma_transition_prob_le`. What is new is the game-shape
reduction: the plain knowledge-soundness game wraps the challenge draw inside
`Reduction.runWithLog`, so we peel the logging (the extractor here ignores
the query logs) and the always-accepting pure verifier to reach the
challenge-first shape consumed by
`ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`. -/

omit [DecidableEq ι] in
/-- The L6.10 γ-round bound ([ABF26] §6.4, via
`ToyProblem.gamma_transition_prob_le`): if the choice extractor fails on
`stmtIn` then no `R̃²` witness exists, and the probability over a uniform `γ`
that the folded instance has an `R̃¹` witness is at most
`ε_mca + |Λ(C^{≡2}, δ)| / |F|`. Stated in the reduced form of the L6.10 game
event so the master lemma's challenge-only hypothesis can consume it. -/
private lemma gamma_game_bound [SampleableType F] [Nonempty ι]
    (C : Set (ι → A)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ) (hδ_lt : δ < (minRelHammingDistCode C : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι A i)) :
    Pr[fun γ : F ↦
        (stmtIn, Spec.extractZero k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          ∃ m : Fin k → F,
            (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
            ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
              ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j
      | $ᵗ F] ≤
      (((epsMCA (F := F) (A := A) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M,
      (stmtIn, M) ∈ Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ
  · -- The choice extractor succeeds, so the event is empty.
    refine le_trans (le_of_eq ?_) zero_le'
    rw [prob_tsum_form_singleton]
    have hnot : ∀ γ : F, ¬ (
        (stmtIn, Spec.extractZero k (encode : (Fin k → F) → (ι → A)) δ stmtIn) ∉
            Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ ∧
          ∃ m : Fin k → F,
            (∑ j, m j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2) ∧
            ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
              ∀ j ∈ S, stmtIn.2 0 j + γ • stmtIn.2 1 j = encode m j) :=
      fun _ h ↦ h.1 (Spec.extractZero_mem k hw)
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
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal (Spec.epsMCA_ne_top C δ),
        ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        ENNReal.coe_natCast, ENNReal.coe_natCast]

omit [DecidableEq ι] in
/-- **Lemma 6.10 of [ABF26]** (knowledge soundness of Construction 6.9).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the simplified IOR has knowledge soundness (paper Def A.5) from
`R̃²_{C,δ}` to `R̃¹_{C,δ}` with error

  `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|`.

Note the cleaner error term compared with L6.6: there's no `(1-δ)^t`
spot-check term because C6.9 has no spot-check round.

The `(Lambda …).toNat` in the error term is faithful: `Lambda` is never
`⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`).

**Status: fully proven (sorry-free).** The proof is the "1-round version"
of L6.8 ([ABF26] §6.4: "easy to see by adapting Lemma 6.8"): the
straightline extractor is the same classical choice `Spec.extractZero`
(always-`some` — under the post-PR-#569 game, extraction failure scores
against the prover, so an always-`some` extractor is strictly stronger),
and the γ-round mathematical content is the same
`ToyProblem.gamma_transition_prob_le` (via `gamma_game_bound` above).
The game-shape reduction peels the query logs
(`loggingOracle.map_fst_run_simulateQ` — the extractor ignores them) and
the always-accepting pure verifier
(`loggingOracle.run_simulateQ_optionT_pure`), exposing the
challenge-first shape consumed by the master mixture lemma
`ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`. -/
theorem simplifiedIOR_knowledgeSound
    [SampleableType F] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → A)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → A))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (verifier (ι := ι) (F := F) (k := k)).knowledgeSoundness
        (WitOut := OutputWitness (F := F) k)
        init impl
        (ToyProblem.Spec.outputRelationFor k (encode : (Fin k → F) → (ι → A)) δ)
        (outputRelationFor (ι := ι) (F := F) k (encode : (Fin k → F) → (ι → A)) δ)
        ((epsMCA (F := F) (A := A) C δ).toNNReal +
          ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
            / (Fintype.card F : ℝ≥0)) := by
  classical
  unfold Verifier.knowledgeSoundness
  -- The straightline extractor: classical choice of any `R̃²` witness, from the
  -- input statement alone (always-`some`; cf. `Spec.extractZero`).
  refine ⟨fun stmtIn _ _ _ _ ↦
    pure (Spec.extractZero k ((encode : (Fin k → F) → (ι → A))) δ stmtIn), ?_⟩
  rintro ⟨stmt, oStmt⟩ witIn prover
  refine ProtocolSpec.probEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le
    init impl _ ⟨0, rfl⟩
    (fun γ ↦ (liftComp (prover.receiveChallenge ⟨0, rfl⟩
        (prover.input ((stmt, oStmt), witIn))) ([]ₒ + [(pSpec (F := F)).Challenge]ₒ))
      >>= fun fc ↦ prover.output (fc γ))
    (fun (γ : F) t ↦ ((stmt, oStmt),
      some (Spec.extractZero k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
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
          some (Spec.extractZero k ((encode : (Fin k → F) → (ι → A))) δ (stmt, oStmt)),
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
