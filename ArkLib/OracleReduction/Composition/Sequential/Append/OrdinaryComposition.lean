/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSplit
public import ArkLib.OracleReduction.Security.KnowledgeSoundnessRun
public import ArkLib.OracleReduction.Security.ChallengePresampling

/-!
# Extractors and adversaries for ordinary composition

The composed extractor first recovers the intermediate witness from the suffix, then uses it
with the prefix transcript. To charge a failed prefix extraction, the prefix adversary plays the
suffix in its output step using fixed challenges and the actual ambient oracle.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Compose pure transcript-and-output extractors through the first verifier's guarded output. -/
def Verifier.GuardedForm.appendExtract
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} (G₁ : V₁.GuardedForm)
    (e₁ : Stmt₁ → Wit₂ → pSpec₁.FullTranscript → Option Wit₁)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂) :
    Stmt₁ → Wit₃ → (pSpec₁ ++ₚ pSpec₂).FullTranscript → Option Wit₁ :=
  fun x w₃ tr => e₂ (G₁.out x tr.fst) w₃ tr.snd >>= fun w₂ => e₁ x w₂ tr.fst

namespace Prover

/-- Restrict a prover to the prefix, but compute its output witness by playing the suffix
against a fixed challenge vector. The fallback is used only when suffix extraction returns none. -/
def appendPrefixExtract
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂)
    (c : ∀ i, pSpec₂.Challenge i) (fallback : Wit₂) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁ where
  PrvState := (P.appendPrefix out).PrvState
  input := (P.appendPrefix out).input
  sendMessage := (P.appendPrefix out).sendMessage
  receiveChallenge := (P.appendPrefix out).receiveChallenge
  output st := do
    let r ← simulateQ (fixedChallengeImpl c)
      ((P.appendSuffix (Stmt₂ := Stmt₂)).run (out st.1) st.2)
    pure (out st.1, (e₂ (out st.1) r.2.2 r.1).getD fallback)

/-- Changing only the prefix's output leaves its interaction unchanged. -/
theorem appendPrefixExtract_runToRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂)
    (c : ∀ i, pSpec₂.Challenge i) (fallback : Wit₂)
    (i : Fin (m + 1)) (stmt : Stmt₁) (aux : Wit₁) :
    (P.appendPrefixExtract out e₂ c fallback).runToRound i stmt aux =
      (P.appendPrefix out).runToRound i stmt aux := rfl

private theorem appendPrefix_transcript_eq
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂) (i : Fin (m + 1))
    (stmt : Stmt₁) (aux : Wit₁)
    (z : pSpec₁.Transcript i × pSpec₁.Transcript i ×
      P.PrvState (ChallengeTree.leftRound i))
    (hz : z ∈ support ((P.appendPrefix out).runToRound i stmt aux)) : z.2.1 = z.1 := by
  induction i using Fin.induction with
  | zero =>
    simp only [runToRound_zero_of_prover_first] at hz
    subst z
    rfl
  | succ j ih =>
    rw [runToRound_succ] at hz
    cases hd : pSpec₁.dir j with
    | P_to_V =>
      rw [processRound_of_dir_eq_P_to_V _ hd] at hz
      simp only [appendPrefix, liftM_bind, liftM_pure, bind_assoc, pure_bind] at hz
      obtain ⟨z₀, hz₀, hz⟩ := OracleComp.mem_support_bind_peel _ _ hz
      obtain ⟨r, _, hz⟩ := OracleComp.mem_support_bind_peel _ _ hz
      obtain rfl := OracleComp.eq_of_mem_support_pure _ hz
      dsimp only
      rw [ih z₀ hz₀]
    | V_to_P =>
      rw [processRound_of_dir_eq_V_to_P _ hd] at hz
      simp only [appendPrefix, liftM_bind, liftM_pure, bind_assoc, pure_bind] at hz
      obtain ⟨z₀, hz₀, hz⟩ := OracleComp.mem_support_bind_peel _ _ hz
      obtain ⟨c, _, hz⟩ := OracleComp.mem_support_bind_peel _ _ hz
      obtain ⟨f, _, hz⟩ := OracleComp.mem_support_bind_peel _ _ hz
      obtain rfl := OracleComp.eq_of_mem_support_pure _ hz
      exact congrArg (fun tr => tr.concat c) (ih z₀ hz₀)

/-- The prefix extractor adversary is the prefix restriction followed by the fixed-challenge
suffix, with the extracted intermediate witness returned as its own output. -/
theorem appendPrefixExtract_run
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (out : pSpec₁.FullTranscript → Stmt₂)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂)
    (c : ∀ i, pSpec₂.Challenge i) (fallback : Wit₂)
    (stmt : Stmt₁) (aux : Wit₁) :
    (P.appendPrefixExtract out e₂ c fallback).run stmt aux = (do
      let z ← (P.appendPrefix out).run stmt aux
      let r ← liftM (simulateQ (fixedChallengeImpl c)
        ((P.appendSuffix (Stmt₂ := Stmt₂)).run (out z.1) z.2.2))
      pure (z.1, out z.1, (e₂ (out z.1) r.2.2 r.1).getD fallback)) := by
  unfold run
  rw [appendPrefixExtract_runToRound]
  simp only [appendPrefixExtract, appendPrefix, liftM_bind, liftM_pure,
    bind_assoc, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro z hz
  rw [appendPrefix_transcript_eq P out (Fin.last m) stmt aux z hz]
  rfl

end Prover

namespace Verifier.GuardedForm

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}

/-- The first component bounds accepted failed prefix extraction, even when the intermediate
witness is obtained from the suffix. If the intermediate witness type is empty, this event is
empty; no inhabitance assumption is required. -/
theorem append_prefix_bad_le (G : V₁.GuardedForm)
    (e₁ : Stmt₁ → Wit₂ → pSpec₁.FullTranscript → Option Wit₁)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂) {ε : ℝ≥0}
    (h₁ : V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) ε)
    {Aux : Type} (stmt : Stmt₁) (aux : Aux)
    (P : Prover oSpec Stmt₁ Aux Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Pr{let r ← (do
      let s ← init
      let z ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        ((P.appendPrefix (G.out stmt)).run stmt aux)).run s
      let r ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        ((P.appendSuffix (Stmt₂ := Stmt₂)).run (G.out stmt z.1.1) z.1.2.2)).run z.2
      pure (z, r))}[
        G.check stmt r.1.1.1 = true ∧
          ∃ w₂ ∈ e₂ (G.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1,
            (∀ w₁ ∈ e₁ stmt w₂ r.1.1.1, (stmt, w₁) ∉ rel₁) ∧
              (G.out stmt r.1.1.1, w₂) ∈ rel₂] ≤ ε := by
  classical
  let prefixBad := fun (r :
    ((pSpec₁.FullTranscript × Stmt₂ × P.PrvState (ChallengeTree.leftRound (Fin.last m))) × σ) ×
      ((pSpec₂.FullTranscript × Stmt₃ × Wit₃) × σ)) =>
    G.check stmt r.1.1.1 = true ∧
      ∃ w₂ ∈ e₂ (G.out stmt r.1.1.1) r.2.1.2.2 r.2.1.1,
        (∀ w₁ ∈ e₁ stmt w₂ r.1.1.1, (stmt, w₁) ∉ rel₁) ∧
          (G.out stmt r.1.1.1, w₂) ∈ rel₂
  by_cases hW : Nonempty Wit₂
  · let fallback : Wit₂ := Classical.choice hW
    let : ∀ i, Fintype (pSpec₂.Challenge i) := fun _ => Fintype.ofFinite _
    let : SampleableType (∀ i, pSpec₂.Challenge i) :=
      SampleableType.piOfFintype pSpec₂.Challenge
    let pre := do
      let s ← init
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        ((P.appendPrefix (G.out stmt)).run stmt aux)).run s
    have hd := EvalDistEq.bind_right pre (fun z =>
      (((P.appendSuffix (Stmt₂ := Stmt₂)).orderedChallenges_run
        (G.out stmt z.1.1) z.1.2.2).presample impl z.2).symm.map (fun r => (z, r)))
    simp only [map_bind] at hd
    have hs := OracleComp.EvalDistEq.bind_bind_swap pre ($ᵗ (∀ i, pSpec₂.Challenge i))
      (fun z c => (fun r => (z, r)) <$>
        (simulateQ impl (simulateQ (fixedChallengeImpl c)
          ((P.appendSuffix (Stmt₂ := Stmt₂)).run (G.out stmt z.1.1) z.1.2.2))).run z.2)
    have heq := (hd.trans hs).prEvent_eq prefixBad
    dsimp only [prefixBad] at heq
    simp only [pre, bind_assoc] at heq
    simp only [bind_pure_comp]
    rw [heq]
    apply prEvent_bind_le_of_forall_le
    intro c
    have hb := (G.knowledgeSoundnessWith_iff e₁).mp h₁ Aux stmt aux
      (P.appendPrefixExtract (G.out stmt) e₂ c fallback)
    simp only [Prover.appendPrefixExtract_run, simulateQ_bind, simulateQ_pure,
      QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left, QueryImpl.liftTarget_self,
      StateT.run_bind, StateT.run_pure] at hb
    refine le_trans ?_ hb
    apply prEvent_bind_mono_of_forall_le
    intro s
    apply prEvent_bind_mono_of_forall_le
    intro z
    simp only [prEvent_map, bind_pure_comp]
    apply prEvent_mono
    intro r hr
    obtain ⟨hc, w₂, hw₂, hfail, hrel⟩ := hr
    have he : e₂ (G.out stmt z.1.1) r.1.2.2 r.1.1 = some w₂ := hw₂
    simpa only [he, Option.getD_some] using And.intro hc (And.intro hfail hrel)
  · have hz : Pr{let r ← (do
        let s ← init
        let z ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          ((P.appendPrefix (G.out stmt)).run stmt aux)).run s
        let r ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          ((P.appendSuffix (Stmt₂ := Stmt₂)).run (G.out stmt z.1.1) z.1.2.2)).run z.2
        pure (z, r))}[
          prefixBad r] = 0 := by
      apply prEvent_eq_zero_of_forall_not
      rintro r ⟨_, w₂, _⟩
      exact hW ⟨w₂⟩
    rw [hz]
    exact bot_le

end Verifier.GuardedForm

/-- Split an event after a continuation into an event already determined by its input and a
remaining continuation event. The first term pays only once for the prefix event. -/
theorem OracleComp.prEvent_bind_split_le {A B : Type} (pre : ProbComp A) (next : A → ProbComp B)
    (bad : A → B → Prop) (left : A → Prop) (right : A → B → Prop)
    (h : ∀ a b, b ∈ support (next a) → bad a b → left a ∨ right a b) :
    Pr{let r ← (do let a ← pre; let b ← next a; pure (a, b))}[bad r.1 r.2] ≤
      Pr{let a ← pre}[left a] +
        Pr{let r ← (do let a ← pre; let b ← next a; pure (a, b))}[right r.1 r.2] := by
  let joint := do let a ← pre; let b ← next a; pure (a, b)
  have hm := prEvent_mono_of_support joint (fun r => bad r.1 r.2)
    (fun r => left r.1 ∨ right r.1 r.2) (by
      intro r hr
      obtain ⟨a, _, hr⟩ := OracleComp.mem_support_bind_peel _ _ hr
      obtain ⟨b, hb, hr⟩ := OracleComp.mem_support_bind_peel _ _ hr
      obtain rfl := OracleComp.eq_of_mem_support_pure _ hr
      exact h a b hb)
  have hu := prEvent_or_le joint (fun r => left r.1) (fun r => right r.1 r.2)
  refine (hm.trans hu).trans (add_le_add ?_ le_rfl)
  apply prEvent_bind_le_prEvent_of_support pre _ left
  intro a _ ha
  simp only [bind_pure_comp, prEvent_map]
  exact prEvent_eq_zero_of_forall_not _ _ (fun _ => ha)
