/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, scaraven
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSplit
public import ArkLib.OracleReduction.Security.SoundnessInitialization
public import ArkLib.OracleReduction.Composition.Sequential.Append.OrdinaryComposition

/-!
# Ordinary soundness and knowledge soundness of sequential composition

`Verifier.append_soundness` and its oracle-verifier wrapper are proved for a guarded first
verifier and a second-stage soundness bound valid from every deterministic oracle state. The
first-stage bound uses the given initialization, and the composite error is the sum of the two
errors. The proof restricts an arbitrary adversarial prover at the seam and retains its private
state and the actual shared oracle state.

Knowledge soundness composes pure statement/output/transcript extractors using
`GuardedForm.appendExtract`. The first-stage adversary computes the intermediate witness by
playing the suffix against presampled challenges in its output step. Ambient oracle queries
remain real and retain their shared state. No inhabitance assumption on the intermediate witness
type is needed. The named-extractor and existential forms have the sum of the component errors.

For proved completeness interfaces, use `Append/Completeness.lean` and
`Sequential/GuardedCompleteness.lean`. The proved soundness interface in `Append/RoundByRound.lean`
requires component bounds and a pure first verifier. The proved knowledge-soundness
interface in `Append/GuardedRoundByRound.lean` requires component bounds and a guarded
first verifier.
-/

@[expose] public section

open OracleComp OracleSpec SubSpec

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section Security

open scoped NNReal

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

namespace Verifier

/-- A guarded first verifier and a second verifier sound from every deterministic oracle state
compose with the sum of their soundness errors. The first bound uses the given initialization;
the second verifier need not be guarded.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_soundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    [V₁.IsGuarded]
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : ∀ s : σ, V₂.soundness (pure s) impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  obtain ⟨check, out, hG⟩ := (inferInstance : V₁.IsGuarded).is_guarded
  let G : V₁.GuardedForm := ⟨check, out, hG⟩
  rw [soundness_iff_run]
  intro Aux Out wit P stmt hstmt
  have hpref := G.soundness_iff.mp h₁ _ _ wit (P.appendPrefix (out stmt)) stmt hstmt
  rw [ENNReal.coe_add]
  simp only [Prover.simulateQ_run_appendSplit impl P (out stmt), bind_assoc, pure_bind]
  rw [← bind_assoc]
  refine (prEvent_bind_le_prEvent_add _ _
    (fun z => check stmt z.1.1 = true ∧ out stmt z.1.1 ∈ lang₂) _ ?_).trans
      (add_le_add hpref (le_refl (soundnessError₂ : ENNReal)))
  intro z hz
  by_cases hc : check stmt z.1.1 = true
  · have hy : out stmt z.1.1 ∉ lang₂ := fun hy => hz ⟨hc, hy⟩
    have hs := soundness_iff_run.mp (h₂ z.2) _ _ z.1.2.2
      (P.appendSuffix (Stmt₂ := Stmt₂)) (out stmt z.1.1) hy
    simpa only [pure_bind, append_run_guardedLeft V₁ V₂ check out hG, hc, ite_true] using hs
  · simp only [append_run_guardedLeft V₁ V₂ check out hG, ite_eq_right hc]
    apply prEvent_bind_le_of_forall_le
    intro z₂
    change Pr{let v ← (pure (none, z₂.2) : ProbComp (Option Stmt₃ × σ))}[
      v.1.elim False (fun v => v ∈ lang₃)] ≤ _
    simp

/-- Pure transcript-and-output extractors compose through a guarded first verifier. The second
component's bound must hold from every deterministic shared oracle state, at the same extractor.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_knowledgeSoundnessWith
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    (G₁ : V₁.GuardedForm)
    (e₁ : Stmt₁ → Wit₂ → pSpec₁.FullTranscript → Option Wit₁)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂) {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) ε₁)
    (h₂ : ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) ε₂) :
    (V₁.append V₂).knowledgeSoundnessWith init impl rel₁ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput (G₁.appendExtract e₁ e₂)) (ε₁ + ε₂) := by
  classical
  rw [knowledgeSoundnessWith_iff_run]
  intro Aux stmt aux P
  let pre := do
    let s ← init
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((P.appendPrefix (G₁.out stmt)).run stmt aux)).run s
  let core := do
    let z ← pre
    let r ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((P.appendSuffix (Stmt₂ := Stmt₂)).run (G₁.out stmt z.1.1) z.1.2.2)).run z.2
    pure (z, r)
  let verify := fun (r :
    ((pSpec₁.FullTranscript × Stmt₂ × P.PrvState (ChallengeTree.leftRound (Fin.last m))) × σ) ×
      ((pSpec₂.FullTranscript × Stmt₃ × Wit₃) × σ)) => (simulateQ impl
    ((V₁.append V₂).run stmt (r.1.1.1 ++ₜ r.2.1.1))).run r.2.2
  let prefixBad := fun (r :
    ((pSpec₁.FullTranscript × Stmt₂ × P.PrvState (ChallengeTree.leftRound (Fin.last m))) × σ) ×
      ((pSpec₂.FullTranscript × Stmt₃ × Wit₃) × σ)) =>
    G₁.check stmt r.1.1.1 = true ∧
      ∃ w₂ ∈ e₂ (G₁.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1,
        (∀ w₁ ∈ e₁ stmt w₂ r.1.1.1, (stmt, w₁) ∉ rel₁) ∧
          (G₁.out stmt r.1.1.1, w₂) ∈ rel₂
  let suffixBad := fun (r :
    ((pSpec₁.FullTranscript × Stmt₂ × P.PrvState (ChallengeTree.leftRound (Fin.last m))) × σ) ×
      ((pSpec₂.FullTranscript × Stmt₃ × Wit₃) × σ)) (v : Option Stmt₃ × σ) =>
    v.1.elim False (fun out =>
      (∀ w₂ ∈ e₂ (G₁.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1,
        (G₁.out stmt r.1.1.1, w₂) ∉ rel₂) ∧ (out, r.2.1.2.2) ∈ rel₃)
  have hsplit := prEvent_bind_split_le core verify
    (fun r v => v.1.elim False (fun out =>
      (∀ w₁ ∈ (e₂ (G₁.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1 >>= fun w₂ =>
        e₁ stmt w₂ r.1.1.1), (stmt, w₁) ∉ rel₁) ∧ (out, r.2.1.2.2) ∈ rel₃))
    prefixBad suffixBad (by
      dsimp only [prefixBad, suffixBad]
      intro r v hv hb
      by_cases hc : G₁.check stmt r.1.1.1 = true
      · cases ho : v.1 with
        | none => simp [ho] at hb
        | some out =>
          simp only [ho, Option.elim_some] at hb ⊢
          by_cases he : ∃ w₂ ∈ e₂ (G₁.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1,
              (G₁.out stmt r.1.1.1, w₂) ∈ rel₂
          · obtain ⟨w₂, hw₂, hr₂⟩ := he
            refine Or.inl ⟨hc, w₂, hw₂, ?_, hr₂⟩
            intro w₁ hw₁
            apply hb.1 w₁
            have he₂ : e₂ (G₁.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1 = some w₂ := hw₂
            simpa only [he₂, Option.bind_eq_bind, Option.bind_some] using hw₁
          · exact Or.inr ⟨fun w₂ hw₂ hr₂ => he ⟨w₂, hw₂, hr₂⟩, hb.2⟩
      · have hv' : v = (none, r.2.2) := by
          simp only [verify, append_run_guardedLeft V₁ V₂ G₁.check G₁.out G₁.verify_eq,
            ite_eq_right hc] at hv
          change v ∈ support (pure (none, r.2.2) : ProbComp (Option Stmt₃ × σ)) at hv
          exact OracleComp.eq_of_mem_support_pure _ hv
        simp [hv'] at hb)
  have hp := G₁.append_prefix_bad_le e₁ e₂ h₁ stmt aux P
  have hs : Pr{let r ← (do let a ← core; let v ← verify a; pure (a, v))}[
      suffixBad r.1 r.2] ≤ ε₂ := by
    simp only [suffixBad, core, bind_assoc, pure_bind]
    apply prEvent_bind_le_of_forall_le
    intro z
    have hb := (knowledgeSoundnessWith_iff_run e₂).mp (h₂ z.2) _
      (G₁.out stmt z.1.1) z.1.2.2 (P.appendSuffix (Stmt₂ := Stmt₂))
    by_cases hc : G₁.check stmt z.1.1 = true
    · simpa only [verify, append_run_guardedLeft V₁ V₂ G₁.check G₁.out G₁.verify_eq,
        hc, ite_true, pure_bind, map_bind, Functor.map_map, map_pure,
        bind_pure_comp] using hb
    · simp only [verify, append_run_guardedLeft V₁ V₂ G₁.check G₁.out G₁.verify_eq,
        ite_eq_right hc]
      apply prEvent_bind_le_of_forall_le
      intro r
      change Pr{let v ← (pure (none, r.2) : ProbComp (Option Stmt₃ × σ))}[
        v.1.elim False (fun out =>
          (∀ w₂ ∈ e₂ (G₁.out stmt z.1.1) r.1.2.2 r.1.1,
            (G₁.out stmt z.1.1, w₂) ∉ rel₂) ∧ (out, r.1.2.2) ∈ rel₃)] ≤ _
      simp
  simp only [prefixBad, suffixBad, core, pre, bind_assoc] at hsplit hs
  have hbound := hsplit.trans (add_le_add hp hs)
  rw [ENNReal.coe_add]
  simp only [Prover.simulateQ_run_appendSplit impl P (G₁.out stmt)]
  simpa [verify, bind_assoc, GuardedForm.appendExtract, bind_pure_comp] using hbound

/-- Existential pure transcript-and-output extractors compose with the sum of the errors.
The suffix extractor is fixed uniformly over its initial oracle state.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_knowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (G₁ : V₁.GuardedForm)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : ∃ e₁, V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) knowledgeError₁)
    (h₂ : ∃ e₂, ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        rel₁ rel₃ (knowledgeError₁ + knowledgeError₂) := by
  obtain ⟨e₁, h₁⟩ := h₁
  obtain ⟨e₂, h₂⟩ := h₂
  exact knowledgeSoundness_of_with init impl (append_knowledgeSoundnessWith G₁ e₁ e₂ h₁ h₂)

end Verifier

end Protocol

section OracleProtocol

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))} {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- Oracle verifiers compose with the sum of their soundness errors when the first induced
verifier is guarded and the second bound holds from every deterministic oracle state.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_soundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    [V₁.toVerifier.IsGuarded]
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : ∀ s : σ, V₂.soundness (pure s) impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold soundness
  convert Verifier.append_soundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- The named pure transcript-and-output extractor composition theorem for oracle verifiers.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_knowledgeSoundnessWith
    {V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁}
    {V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂}
    (G₁ : V₁.toVerifier.GuardedForm)
    (e₁ : (Stmt₁ × ∀ i, OStmt₁ i) → Wit₂ → pSpec₁.FullTranscript → Option Wit₁)
    (e₂ : (Stmt₂ × ∀ i, OStmt₂ i) → Wit₃ → pSpec₂.FullTranscript → Option Wit₂)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) ε₁)
    (h₂ : ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) ε₂) :
    (V₁.append V₂).knowledgeSoundnessWith init impl rel₁ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput (G₁.appendExtract e₁ e₂)) (ε₁ + ε₂) := by
  unfold knowledgeSoundnessWith
  rw [append_toVerifier]
  exact Verifier.append_knowledgeSoundnessWith G₁ e₁ e₂ h₁ h₂

/-- Oracle verifiers with pure transcript-and-output extractors compose through a guarded first
verifier and a uniform suffix bound over deterministic shared oracle states.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. It therefore cannot justify a
second-stage bound that relies on the prover not knowing the sampled oracle state (a hidden
trapdoor or an eagerly sampled random function); lazily sampled oracles meet the requirement. -/
theorem append_knowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (G₁ : V₁.toVerifier.GuardedForm)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : ∃ e₁, V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) knowledgeError₁)
    (h₂ : ∃ e₂, ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃
        (knowledgeError₁ + knowledgeError₂) := by
  unfold knowledgeSoundness
  rw [append_toVerifier]
  exact Verifier.append_knowledgeSoundness V₁.toVerifier V₂.toVerifier G₁ h₁ h₂

end OracleVerifier

end OracleProtocol

end Security
