/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.KnowledgeComposition.Extraction

/-!
# Composing round-by-round knowledge bounds

Statement-indexed witness maps transport knowledge certificates across a deterministic middle
claim. This file ships three kinds of composition result:

* Relation-level composition for any signature lens: `rbrKnowledgeSoundness_append_prefix` and
  `rbrKnowledgeSoundness_append_of_mid_prefix`, with node-indexed corollaries
  `rbrKnowledgeSoundness_append` and `rbrKnowledgeSoundness_append_of_mid`. The oracle form
  `rbrKnowledgeSoundness_append_view` takes draws that read only the verifier's view and chooses
  the suffix draw from the first stage's view.
* Plain verifier composition: `Verifier.rbrKnowledgeSoundness_append_prefix` and
  `Verifier.rbrKnowledgeSoundness_append_of_pure_prefix`, with node-indexed corollaries. They take
  the two components' standalone verifier knowledge theorems and an identified middle claim:
  every supported accepted prefix result equals `mid stmt tr₁`.
* An oracle acceptance decomposition, not a standalone oracle-verifier composition theorem.
  `OracleVerifier.validAcceptance_append` splits a positive composite acceptance into supported
  accepted prefix and suffix decisions on the routed bundle data, with the prefix's final ambient
  state as the suffix's initial state. A client composes relation-level certificates with it.

The plain acceptance decomposition `Verifier.validAcceptance_append` also retains the ambient
state at the seam.
-/

@[expose] public section

universe uA

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle MeasureTheory
open scoped ENNReal

variable {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly.{0})

namespace KnowledgeStateFunction

variable {l} {S : Type}

section restrict

variable {s : FreeM P PUnit.{1}} {Win : S → Type} {W : S → Transcript l s → Type}
    {admissible : S →
    Prop}
  {relIn : (stmt : S) → Win stmt → Prop} {validOutput : (stmt : S) → (tr : Transcript l s) → W stmt
    tr → Prop}

/-- The state function whose states, and valid outputs, apply to admissible statements only. -/
def guard (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput) :
    KnowledgeStateFunction l s S W Win admissible relIn
      (fun stmt tr w => admissible stmt → validOutput stmt tr w) where
  Witness := F.Witness
  toFun stmt {_} sp history w := admissible stmt → F.toFun stmt sp history w
  extractRoot := F.extractRoot
  extractStep := F.extractStep
  extractLeaf := F.extractLeaf
  root stmt hadm w h := F.root stmt hadm w (h hadm)
  send sp history stmt ho x w h hadm := F.send sp history stmt ho x w (h hadm)
  leaf sp history stmt w h hadm := F.leaf sp history stmt w (h hadm)

/-- Conjoin a statement predicate to all states and to the extracted input relation.
The output obligation supplies the same predicate at every leaf cursor. -/
def condition (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)
    (gate : S → Prop)
    {validOutput' : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop}
    (hout : ∀ stmt tr w, validOutput' stmt tr w → gate stmt ∧ validOutput stmt tr w) :
    KnowledgeStateFunction l s S W Win admissible (fun stmt w => gate stmt ∧ relIn
    stmt w)
      validOutput' where
  Witness := F.Witness
  toFun stmt {_} sp history w := gate stmt ∧ F.toFun stmt sp history w
  extractRoot := F.extractRoot
  extractStep := F.extractStep
  extractLeaf := F.extractLeaf
  root stmt ha w h := ⟨h.1, F.root stmt ha w h.2⟩
  send sp history stmt ho x w h := ⟨h.1, F.send sp history stmt ho x w h.2⟩
  leaf sp history stmt w h :=
    ⟨(hout stmt _ w h).1, F.leaf sp history stmt w (hout stmt _ w h).2⟩

/-- Pull back statements and output witnesses, and map the extracted input witnesses. -/
def comap {S' : Type} {Win' : S' → Type} {W' : S' → Transcript l s → Type}
    (f : S' → S) (F : KnowledgeStateFunction l s S W Win admissible relIn validOutput)
    (inputMap : ∀ stmt, Win (f stmt) → Win' stmt)
    (outputMap : ∀ stmt tr, W' stmt tr → W (f stmt) tr)
    {validOutput' : (stmt : S') → (tr : Transcript l s) → W' stmt tr → Prop}
    (hout : ∀ stmt tr w, validOutput' stmt tr w →
      validOutput (f stmt) tr (outputMap stmt tr w)) :
    KnowledgeStateFunction l s S' W' Win' (fun stmt => admissible (f stmt))
      (fun stmt w => ∃ v, relIn (f stmt) v ∧ inputMap stmt v = w) validOutput' where
  Witness stmt := F.Witness (f stmt)
  toFun stmt := F.toFun (f stmt)
  extractRoot stmt w := inputMap stmt (F.extractRoot (f stmt) w)
  extractStep stmt := F.extractStep (f stmt)
  extractLeaf stmt sp history w := F.extractLeaf (f stmt) sp history (outputMap stmt _ w)
  root stmt h w hw := ⟨_, F.root (f stmt) h w hw, rfl⟩
  send sp history stmt := F.send sp history (f stmt)
  leaf sp history stmt w h := F.leaf sp history (f stmt) _ (hout stmt _ w h)

end restrict

variable {P : PFunctor.{uA, 0}} {l : PFunctor.Lens P rolePoly}

section restrictBounds

variable {s : FreeM P PUnit.{1}} {Win : S → Type}
  {W : S → Transcript l s → Type} {admissible : S → Prop}
  {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop}

/-- Guarding keeps the bound at an admissible statement. -/
theorem BoundedAt.guard {F : KnowledgeStateFunction l s S W Win admissible relIn
    validOutput}
    {draw : PrefixDraw l ProbComp s} {ε : PrefixError l s} {stmt : S}
    (h : F.BoundedAt draw ε stmt) (hadm : admissible stmt) : F.guard.BoundedAt draw ε stmt :=
  fun a next sp ho history => by
    refine le_trans (measure_mono ?_) (h a next sp ho history)
    rintro x ⟨wit, hbad, hgood⟩
    exact ⟨wit, fun h' => hbad fun _ => h', hgood hadm⟩

/-- Conjoining a statement predicate does not enlarge the local bad-challenge event. -/
theorem BoundedAt.condition {F : KnowledgeStateFunction l s S W Win admissible relIn
    validOutput}
    {gate : S → Prop}
    {validOutput' : (stmt : S) → (tr : Transcript l s) → W stmt tr → Prop}
    {hout : ∀ stmt tr w, validOutput' stmt tr w → gate stmt ∧ validOutput stmt tr w}
    {draw : PrefixDraw l ProbComp s} {ε : PrefixError l s} {stmt : S}
    (h : F.BoundedAt draw ε stmt) : (F.condition gate hout).BoundedAt draw ε stmt := by
  intro a next sp ho history
  refine le_trans (measure_mono ?_) (h a next sp ho history)
  rintro x ⟨w, hbad, hgood⟩
  exact ⟨w, fun h' => hbad ⟨hgood.1, h'⟩, hgood.2⟩

/-- Pulling back statements and witness maps keeps the original local bound. -/
theorem BoundedAt.comap {S' : Type} {Win' : S' → Type} {W' : S' → Transcript l s → Type}
    {f : S' → S} {F : KnowledgeStateFunction l s S W Win admissible relIn validOutput}
    {inputMap : ∀ stmt, Win (f stmt) → Win' stmt}
    {outputMap : ∀ stmt tr, W' stmt tr → W (f stmt) tr}
    {validOutput' : (stmt : S') → (tr : Transcript l s) → W' stmt tr → Prop}
    {hout : ∀ stmt tr w, validOutput' stmt tr w →
      validOutput (f stmt) tr (outputMap stmt tr w)}
    {draw : PrefixDraw l ProbComp s} {ε : PrefixError l s} {stmt : S'}
    (h : F.BoundedAt draw ε (f stmt)) :
    (F.comap f inputMap outputMap hout).BoundedAt draw ε stmt := h

end restrictBounds

section security

variable {s₁ : FreeM P PUnit.{1}} {s₂ : Path s₁ → FreeM P PUnit.{1}}
  {Wmid : S → Transcript l s₁ → Type}
    {W : S → Transcript l (s₁.append s₂) → Type} {Win : S → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : Transcript l s₁) → Wmid stmt tr → Prop}
  {admissible₂ : Transcript l s₁ → S → Prop}
  {relMid : (tr₁ : Transcript l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
  {validOutput : (stmt : S) → (tr : Transcript l (s₁.append s₂)) → W stmt tr → Prop}

/-- Local bounds compose: with suffix admissibility implied by prefix admissibility, the
composite is bounded by the prefix errors at prefix challenges and the suffix errors at suffix
challenges. -/
theorem LocallyBounded.append
    {F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid}
    {F₂ : (tr₁ : Transcript l s₁) → KnowledgeStateFunction l (s₂ tr₁.path)
      S (fun stmt tr₂ => W stmt (Transcript.append s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w)}
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    {draw₁ : PrefixDraw l ProbComp s₁}
    {draw₂ : (tr₁ : Transcript l s₁) →
      PrefixDraw l ProbComp (s₂ tr₁.path)}
    {ε₁ : PrefixError l s₁}
    {ε₂ : (tr₁ : Transcript l s₁) → PrefixError l (s₂ tr₁.path)}
    (h₁ : F₁.LocallyBounded draw₁ ε₁)
    (h₂ : ∀ tr₁, (F₂ tr₁).LocallyBounded (draw₂ tr₁)
      (ε₂ tr₁))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt) :
    (append F₁ F₂ seam).LocallyBounded (combinePrefixDraw l s₁ s₂ draw₁ draw₂)
      (combinePrefixDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) :=
  fun stmt h => BoundedAt.append F₁ F₂ seam draw₁ draw₂ ε₁ ε₂ stmt (h₁ stmt h)
    fun tr₁ => h₂ tr₁ stmt (hadm tr₁ stmt h)

/-- Node-indexed local bounds compose by specializing full-prefix composition. -/
theorem LocallyBoundedOfNodes.append
    {F₁ : KnowledgeStateFunction l s₁ S Wmid Win admissible relIn validMid}
    {F₂ : (tr₁ : Transcript l s₁) → KnowledgeStateFunction l (s₂ tr₁.path)
      S (fun stmt tr₂ => W stmt (Transcript.append s₁ s₂ tr₁ tr₂)) (fun stmt => Wmid stmt tr₁)
        (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w)}
    (seam : ∀ tr₁ stmt w, (F₂ tr₁).toFun stmt (.root _) ⟨⟩ w →
      validMid stmt tr₁ ((F₂ tr₁).extractRoot stmt w))
    {draw₁ : QueryImpl (challengeSpec l s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode l s₁ → ℝ≥0∞} {ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞}
    (h₁ : F₁.LocallyBoundedOfNodes draw₁ ε₁)
    (h₂ : ∀ tr₁, (F₂ tr₁).LocallyBoundedOfNodes (draw₂ tr₁.path)
      (ε₂ tr₁.path))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt) :
    (append F₁ F₂ seam).LocallyBoundedOfNodes (combineDraw l s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  simpa only [combinePrefixDraw_ofNodes, combinePrefixError_ofNodes] using
    (LocallyBounded.append seam h₁ h₂ hadm)

end security

end KnowledgeStateFunction

variable {P : PFunctor.{uA, 0}} (l : PFunctor.Lens P rolePoly)

section security

variable {s₁ : FreeM P PUnit.{1}} {s₂ : Path s₁ → FreeM P PUnit.{1}} {S : Type}
    {Win : S → Type}
  {Wmid : S → Transcript l s₁ → Type} {W : S → Transcript l (s₁.append s₂) → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : Transcript l s₁) → Wmid stmt tr → Prop}
  {validOutput : (stmt : S) → (tr : Transcript l (s₁.append s₂)) → W stmt tr → Prop}
  {draw₁ : PrefixDraw l ProbComp s₁}
  {draw₂ : (tr₁ : Transcript l s₁) →
      PrefixDraw l ProbComp (s₂ tr₁.path)}
  {ε₁ : PrefixError l s₁}
  {ε₂ : (tr₁ : Transcript l s₁) → PrefixError l (s₂ tr₁.path)}

/-- Round-by-round knowledge soundness composes sequentially. The suffix is knowledge sound at
every prefix transcript for a transcript-dependent intermediate relation; on admissible
statements, suffix admissibility holds and the intermediate relation implies a valid prefix
output. The composite error is the prefix error at prefix challenges and the suffix error at
suffix challenges, selecting the suffix family by the full first transcript. -/
theorem rbrKnowledgeSoundness_append_prefix {admissible₂ : Transcript l s₁ → S → Prop}
    {relMid : (tr₁ : Transcript l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
    (h₁ : rbrKnowledgeSoundness l s₁ admissible relIn validMid draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundness l (s₂ tr₁.path)
    (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w)
      (draw₂ tr₁) (ε₂ tr₁))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt)
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ stmt w → validMid stmt tr₁ w) :
    rbrKnowledgeSoundness l (s₁.append s₂) admissible relIn validOutput
      (combinePrefixDraw l s₁ s₂ draw₁ draw₂) (combinePrefixDraw
      (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  obtain ⟨F₁, hF₁⟩ := h₁
  choose F₂ hF₂ using h₂
  exact ⟨KnowledgeStateFunction.append F₁.guard F₂
      (fun tr₁ stmt w h hadm' => glue tr₁ stmt _ hadm'
        ((F₂ tr₁).root stmt (hadm tr₁ stmt hadm') w h)),
    KnowledgeStateFunction.LocallyBounded.append _
      (fun stmt h => KnowledgeStateFunction.BoundedAt.guard (hF₁ stmt h) h) hF₂ hadm⟩

/-- Sequential composition through a deterministic intermediate statement. The suffix is knowledge
sound for its own statements; `mid` computes the suffix statement from the input statement and
the prefix transcript, and composite valid outputs are suffix valid outputs at that statement. -/
theorem rbrKnowledgeSoundness_append_of_mid_prefix {T : Transcript l s₁ → Type} (mid :
    (stmt : S) →
    (tr : Transcript l s₁) → T tr)
    {Wmid₂ : (tr₁ : Transcript l s₁) → T tr₁ → Type}
    {W₂ : (tr₁ : Transcript l s₁) → T tr₁ →
      Transcript l (s₂ tr₁.path) → Type}
    {admissible₂ : (tr₁ : Transcript l s₁) → T tr₁ → Prop}
    {relMid : (tr₁ : Transcript l s₁) → (t : T tr₁) → Wmid₂ tr₁ t → Prop}
    {validOutput₂ : (tr₁ : Transcript l s₁) → (t : T tr₁) →
      (tr₂ : Transcript l (s₂ tr₁.path)) → W₂ tr₁ t tr₂ → Prop}
    (h₁ : rbrKnowledgeSoundness l s₁ admissible relIn
      (fun stmt tr w => validMid stmt tr w) draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundness l (s₂ tr₁.path)
      (admissible₂ tr₁) (relMid tr₁) (validOutput₂ tr₁)
      (draw₂ tr₁) (ε₂ tr₁))
    (midWitness : ∀ stmt tr₁, Wmid₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ (mid stmt tr₁) w →
      validMid stmt tr₁ (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ w, validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w →
      validOutput₂ tr₁ (mid stmt tr₁) tr₂ (outWitness stmt tr₁ tr₂ w)) :
    rbrKnowledgeSoundness l (s₁.append s₂) admissible relIn validOutput
      (combinePrefixDraw l s₁ s₂ draw₁ draw₂)
      (combinePrefixDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  apply rbrKnowledgeSoundness_append_prefix l (admissible₂ := fun tr stmt =>
    admissible₂ tr (mid stmt tr))
    (relMid := fun tr stmt w => ∃ v, relMid tr (mid stmt tr) v ∧ midWitness stmt tr v = w) h₁
  · intro tr₁
    obtain ⟨F, hF⟩ := h₂ tr₁
    exact ⟨F.comap (fun stmt => mid stmt tr₁) (fun stmt => midWitness stmt tr₁)
        (fun stmt tr₂ => outWitness stmt tr₁ tr₂) (fun stmt tr₂ w => hout stmt tr₁ tr₂ w),
      fun stmt h => hF _ h⟩
  · exact hadm
  · rintro tr₁ stmt w ha ⟨v, hv, rfl⟩
    exact glue tr₁ stmt v ha hv

/-- Node-indexed knowledge composition is a corollary of full-prefix composition. -/
theorem rbrKnowledgeSoundness_append {draw₁ : QueryImpl (challengeSpec l s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode l s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞} {admissible₂ : Transcript l s₁ → S → Prop}
    {relMid : (tr₁ : Transcript l s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
    (h₁ : rbrKnowledgeSoundnessOfNodes l s₁ admissible relIn validMid draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundnessOfNodes l (s₂ tr₁.path)
    (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w)
      (draw₂ tr₁.path) (ε₂ tr₁.path))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt)
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ stmt w → validMid stmt tr₁ w) :
    rbrKnowledgeSoundnessOfNodes l (s₁.append s₂) admissible relIn validOutput
      (combineDraw l s₁ s₂ draw₁ draw₂) (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  simpa only [combinePrefixDraw_ofNodes, combinePrefixError_ofNodes] using
    (rbrKnowledgeSoundness_append_prefix l (draw₁ := PrefixDraw.ofNodes l draw₁)
      (draw₂ := fun tr => PrefixDraw.ofNodes l (draw₂ tr.path))
      (ε₁ := PrefixError.ofNodes l ε₁)
      (ε₂ := fun tr => PrefixError.ofNodes l (ε₂ tr.path)) h₁ h₂ hadm glue)

/-- Node-indexed knowledge composition is a corollary of full-prefix composition. -/
theorem rbrKnowledgeSoundness_append_of_mid {draw₁ : QueryImpl (challengeSpec l s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec l (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode l s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode l (s₂ p) → ℝ≥0∞} {T : Transcript l s₁ → Type} (mid :
    (stmt : S) →
    (tr : Transcript l s₁) → T tr)
    {Wmid₂ : (tr₁ : Transcript l s₁) → T tr₁ → Type}
    {W₂ : (tr₁ : Transcript l s₁) → T tr₁ →
      Transcript l (s₂ tr₁.path) → Type}
    {admissible₂ : (tr₁ : Transcript l s₁) → T tr₁ → Prop}
    {relMid : (tr₁ : Transcript l s₁) → (t : T tr₁) → Wmid₂ tr₁ t → Prop}
    {validOutput₂ : (tr₁ : Transcript l s₁) → (t : T tr₁) →
      (tr₂ : Transcript l (s₂ tr₁.path)) → W₂ tr₁ t tr₂ → Prop}
    (h₁ : rbrKnowledgeSoundnessOfNodes l s₁ admissible relIn
      (fun stmt tr w => validMid stmt tr w) draw₁ ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundnessOfNodes l (s₂ tr₁.path)
      (admissible₂ tr₁) (relMid tr₁) (validOutput₂ tr₁)
      (draw₂ tr₁.path) (ε₂ tr₁.path))
    (midWitness : ∀ stmt tr₁, Wmid₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ (mid stmt tr₁) w →
      validMid stmt tr₁ (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ w, validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w →
      validOutput₂ tr₁ (mid stmt tr₁) tr₂ (outWitness stmt tr₁ tr₂ w)) :
    rbrKnowledgeSoundnessOfNodes l (s₁.append s₂) admissible relIn validOutput
      (combineDraw l s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) l s₁ s₂ ε₁ ε₂) := by
  simpa only [combinePrefixDraw_ofNodes, combinePrefixError_ofNodes] using
    (rbrKnowledgeSoundness_append_of_mid_prefix l (draw₁ := PrefixDraw.ofNodes l draw₁)
      (draw₂ := fun tr => PrefixDraw.ofNodes l (draw₂ tr.path))
      (ε₁ := PrefixError.ofNodes l ε₁)
      (ε₂ := fun tr => PrefixError.ofNodes l (ε₂ tr.path)) mid h₁ h₂
      midWitness outWitness hadm glue hout)

end security

section view

variable {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}} {S : Type}
  {Win : S → Type} {Wmid : S → Transcript oracleSig s₁ → Type}
  {W : S → Transcript oracleSig (s₁.append s₂) → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validMid : (stmt : S) → (tr : Transcript oracleSig s₁) → Wmid stmt tr → Prop}
  {validOutput : (stmt : S) → (tr : Transcript oracleSig (s₁.append s₂)) → W stmt tr → Prop}

/-- Round-by-round knowledge soundness composes for oracle protocols whose challenges read only
the verifier's view. The prefix draw reads the view of each prefix, and the suffix draw is chosen
from the shape path and the first stage's view (`combineViewPrefixDraw`). The errors, the state
functions and the seam keep the full prefix, oracle messages included. -/
theorem rbrKnowledgeSoundness_append_view {admissible₂ : Transcript oracleSig s₁ → S → Prop}
    {relMid : (tr₁ : Transcript oracleSig s₁) → (stmt : S) → Wmid stmt tr₁ → Prop}
    {draw₁ : PrefixDraw viewSig ProbComp s₁}
    {draw₂ : (p : Path s₁) → View s₁ p → PrefixDraw viewSig ProbComp (s₂ p)}
    {ε₁ : PrefixError oracleSig s₁}
    {ε₂ : (tr₁ : Transcript oracleSig s₁) → PrefixError oracleSig (s₂ tr₁.path)}
    (h₁ : rbrKnowledgeSoundness oracleSig s₁ admissible relIn validMid
      (PrefixDraw.ofView draw₁) ε₁)
    (h₂ : ∀ tr₁, rbrKnowledgeSoundness oracleSig (s₂ tr₁.path) (admissible₂ tr₁)
      (relMid tr₁) (fun stmt tr₂ w => validOutput stmt (Transcript.append s₁ s₂ tr₁ tr₂) w)
      (PrefixDraw.ofView (draw₂ tr₁.path (toView s₁ tr₁))) (ε₂ tr₁))
    (hadm : ∀ tr₁ stmt, admissible stmt → admissible₂ tr₁ stmt)
    (glue : ∀ tr₁ stmt w, admissible stmt → relMid tr₁ stmt w → validMid stmt tr₁ w) :
    rbrKnowledgeSoundness oracleSig (s₁.append s₂) admissible relIn validOutput
      (PrefixDraw.ofView (combineViewPrefixDraw s₁ s₂ draw₁ draw₂))
      (combinePrefixDraw (m := fun _ => ℝ≥0∞) oracleSig s₁ s₂ ε₁ ε₂) := by
  rw [ofView_combineViewPrefixDraw]
  exact rbrKnowledgeSoundness_append_prefix oracleSig h₁ h₂ hadm glue

end view

/-- A positive composite acceptance decomposes into two supported accepted decisions, with
exactly the same ambient state at their boundary. -/
theorem Verifier.validAcceptance_append {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι} {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    (V₁ : Verifier ambient s₁ S T)
    (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (impl : QueryImpl ambient (StateT σ ProbComp)) (stmt : S)
    (tr₁ : Transcript plainSig s₁)
    (tr₂ : Transcript plainSig (s₂ tr₁.path))
    (langOut : splitFamily U (Transcript.path (Transcript.append s₁ s₂ tr₁ tr₂)) → Prop)
    (h : (V₁.append V₂).validAcceptance impl stmt
      (Transcript.append s₁ s₂ tr₁ tr₂) langOut) :
    ∃ state mid between out final original,
      (some mid, between) ∈ support ((simulateQ impl
        (V₁.decide stmt tr₁.path (toPlainView s₁ tr₁)).run).run state) ∧
      (some out, final) ∈ support ((simulateQ impl
        ((V₂ tr₁.path).decide mid
          tr₂.path (toPlainView _ tr₂)).run).run between) ∧
      HEq out original ∧ langOut original := by
  obtain ⟨state, out, final, hr, ho⟩ := (Verifier.validAcceptance_iff_support ..).mp h
  obtain ⟨mid, between, hp, hs⟩ := V₁.support_append V₂ impl stmt _ _ state final out hr
  let pred := fun z : (ps : (p₁ : Path s₁) × Path (s₂ p₁)) ×
      TranscriptAt plainSig s₁ ps.1 × TranscriptAt plainSig (s₂ ps.1) ps.2 =>
    ∃ state mid between out final original,
      (some mid, between) ∈ support
        ((simulateQ impl (V₁.decide stmt z.1.1 z.2.1).run).run state) ∧
      (some out, final) ∈ support
        ((simulateQ impl ((V₂ z.1.1).decide mid z.1.2 z.2.2).run).run between) ∧
      HEq out original ∧ langOut original
  have hp' : pred ⟨_, PlainView.split s₁ s₂ _
      (toPlainView _ (Transcript.append s₁ s₂ tr₁ tr₂))⟩ :=
    ⟨state, mid, between, out, final, out, hp, hs, HEq.rfl, ho⟩
  have he := TranscriptAt.split_pair plainSig s₁ s₂ _
    (toPlainView _ (Transcript.append s₁ s₂ tr₁ tr₂))
  dsimp only [toPlainView] at he
  rw [Transcript.split_append] at he
  exact (congrArg pred he).mp hp'

/-- Standalone verifier knowledge theorems compose at an identified middle claim. The prefix
may use ambient effects; every supported accepted prefix result must equal the named claim.
The suffix theorem is stated solely for the suffix verifier and its own output relation. -/
theorem Verifier.rbrKnowledgeSoundness_append_prefix {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {Win : S → Type} {Wmid : S → Transcript plainSig s₁ → Type}
    {Win₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Type}
    {W : S → Transcript plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : Transcript plainSig s₁) → T tr₁.path →
      Transcript plainSig (s₂ tr₁.path) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : Transcript plainSig s₁) → T tr.path
    → Wmid stmt tr → Prop}
    {admissible₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Prop}
    {relMid : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) →
      (tr₂ : Transcript plainSig (s₂ tr₁.path)) →
      U tr₁.path tr₂.path → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : Transcript plainSig (s₁.append s₂)) →
      splitFamily U tr.path → W stmt tr → Prop}
    {draw₁ : PrefixDraw plainSig ProbComp s₁}
    {draw₂ : (tr₁ : Transcript plainSig s₁) →
      PrefixDraw plainSig ProbComp (s₂ tr₁.path)}
    {ε₁ : PrefixError plainSig s₁}
    {ε₂ : (tr₁ : Transcript plainSig s₁) →
      PrefixError plainSig (s₂ tr₁.path)}
    (mid : (stmt : S) → (tr₁ : Transcript plainSig s₁) → T tr₁.path)
    (accepted : ∀ stmt tr state t final,
      (some t, final) ∈ support ((simulateQ impl
        (V₁.decide stmt (Transcript.path tr) (toPlainView s₁ tr)).run).run state) →
      t = mid stmt tr)
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : Verifier.rbrKnowledgeSoundness V₁ impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, Verifier.rbrKnowledgeSoundness
      (V₂ tr₁.path) impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ tr₁)
      (ε₂ tr₁))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out original w, HEq out original →
      relOut stmt (Transcript.append s₁ s₂ tr₁ tr₂) original w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    Verifier.rbrKnowledgeSoundness (V₁.append V₂) impl admissible relIn relOut
      (combinePrefixDraw plainSig s₁ s₂ draw₁ draw₂)
      (combinePrefixDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  let valid := fun stmt tr w =>
    (V₁.append V₂).validAcceptance impl stmt tr (fun out => relOut stmt tr out w)
  let gate := fun tr₁ stmt => V₁.validAcceptance impl stmt tr₁ (fun t => t = mid stmt tr₁)
  have decompose : ∀ stmt tr₁ tr₂ w,
      valid stmt (Transcript.append s₁ s₂ tr₁ tr₂) w → gate tr₁ stmt ∧
      (V₂ tr₁.path).validAcceptance impl
        (mid stmt tr₁) tr₂
        (fun out => relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) := by
    intro stmt tr₁ tr₂ w h
    obtain ⟨state, t, between, out, final, original, hp, hs, he, ho⟩ :=
      V₁.validAcceptance_append V₂ impl stmt tr₁ tr₂ _ h
    obtain rfl := accepted stmt tr₁ state t between hp
    exact ⟨(Verifier.validAcceptance_iff_support ..).mpr ⟨state, _, between, hp, rfl⟩,
      (Verifier.validAcceptance_iff_support ..).mpr
        ⟨between, out, final, hs, hout stmt tr₁ tr₂ out original w he ho⟩⟩
  apply Interaction.rbrKnowledgeSoundness_append_prefix plainSig h₁
    (admissible₂ := fun tr₁ stmt => admissible₂ tr₁ (mid stmt tr₁))
    (relMid := fun tr₁ stmt w => gate tr₁ stmt ∧
      ∃ v, relMid tr₁ (mid stmt tr₁) v ∧ midWitness stmt tr₁ v = w)
  · intro tr₁
    obtain ⟨F, hF⟩ := h₂ tr₁
    let G := F.comap (fun stmt => mid stmt tr₁) (fun stmt => midWitness stmt tr₁)
      (fun stmt tr₂ => outWitness stmt tr₁ tr₂)
      (fun stmt tr₂ w h => (decompose stmt tr₁ tr₂ w h).2)
    exact ⟨G.condition (gate tr₁) (fun stmt tr₂ w h => ⟨(decompose stmt tr₁ tr₂ w h).1, h⟩),
      fun stmt h => KnowledgeStateFunction.BoundedAt.condition (hF _ h)⟩
  · exact fun tr₁ stmt h => hadm stmt tr₁ h
  · rintro tr₁ stmt w _ ⟨hg, v, hv, rfl⟩
    obtain ⟨state, t, final, hp, ht⟩ := (Verifier.validAcceptance_iff_support ..).mp hg
    exact (Verifier.validAcceptance_iff_support ..).mpr
      ⟨state, t, final, hp, ht.symm ▸ glue stmt tr₁ v hv⟩

/-- A prefix that returns its middle claim without effects satisfies verifier knowledge
composition from the two standalone knowledge theorems. -/
theorem Verifier.rbrKnowledgeSoundness_append_of_pure_prefix {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {Win : S → Type} {Wmid : S → Transcript plainSig s₁ → Type}
    {Win₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Type}
    {W : S → Transcript plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : Transcript plainSig s₁) → T tr₁.path →
      Transcript plainSig (s₂ tr₁.path) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : Transcript plainSig s₁) → T tr.path
    → Wmid stmt tr → Prop}
    {admissible₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Prop}
    {relMid : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) →
      (tr₂ : Transcript plainSig (s₂ tr₁.path)) →
      U tr₁.path tr₂.path → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : Transcript plainSig (s₁.append s₂)) →
      splitFamily U tr.path → W stmt tr → Prop}
    {draw₁ : PrefixDraw plainSig ProbComp s₁}
    {draw₂ : (tr₁ : Transcript plainSig s₁) →
      PrefixDraw plainSig ProbComp (s₂ tr₁.path)}
    {ε₁ : PrefixError plainSig s₁}
    {ε₂ : (tr₁ : Transcript plainSig s₁) →
      PrefixError plainSig (s₂ tr₁.path)}
    (mid : (stmt : S) → (tr₁ : Transcript plainSig s₁) → T tr₁.path)
    (decision : ∀ stmt tr, V₁.decide stmt (Transcript.path tr)
      (toPlainView s₁ tr) = pure (mid stmt tr))
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : Verifier.rbrKnowledgeSoundness V₁ impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, Verifier.rbrKnowledgeSoundness
      (V₂ tr₁.path) impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ tr₁)
      (ε₂ tr₁))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out original w, HEq out original →
      relOut stmt (Transcript.append s₁ s₂ tr₁ tr₂) original w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    Verifier.rbrKnowledgeSoundness (V₁.append V₂) impl admissible relIn relOut
      (combinePrefixDraw plainSig s₁ s₂ draw₁ draw₂)
      (combinePrefixDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  apply Verifier.rbrKnowledgeSoundness_append_prefix V₁ V₂ impl mid _ midWitness outWitness
    h₁ h₂ hadm glue hout
  intro stmt tr state t final h
  rw [decision] at h
  simp only [OptionT.run_pure, simulateQ_pure, StateT.run_pure, _root_.support_pure,
    Set.mem_singleton_iff,
    Prod.mk.injEq, Option.some.injEq] at h
  exact h.1

/-- Node-indexed standalone verifier composition specializes the full-prefix law. -/
theorem Verifier.rbrKnowledgeSoundness_append {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {Win : S → Type} {Wmid : S → Transcript plainSig s₁ → Type}
    {Win₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Type}
    {W : S → Transcript plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : Transcript plainSig s₁) → T tr₁.path →
      Transcript plainSig (s₂ tr₁.path) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : Transcript plainSig s₁) → T tr.path
    → Wmid stmt tr → Prop}
    {admissible₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Prop}
    {relMid : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) →
      (tr₂ : Transcript plainSig (s₂ tr₁.path)) →
      U tr₁.path tr₂.path → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : Transcript plainSig (s₁.append s₂)) →
      splitFamily U tr.path → W stmt tr → Prop}
    {draw₁ : QueryImpl (challengeSpec plainSig s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec plainSig (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode plainSig s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode plainSig (s₂ p) → ℝ≥0∞}
    (mid : (stmt : S) → (tr₁ : Transcript plainSig s₁) → T tr₁.path)
    (accepted : ∀ stmt tr state t final,
      (some t, final) ∈ support ((simulateQ impl
        (V₁.decide stmt (Transcript.path tr) (toPlainView s₁ tr)).run).run state) →
      t = mid stmt tr)
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : Verifier.rbrKnowledgeSoundnessOfNodes V₁
    impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, Verifier.rbrKnowledgeSoundnessOfNodes
      (V₂ tr₁.path) impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ tr₁.path)
      (ε₂ tr₁.path))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out original w, HEq out original →
      relOut stmt (Transcript.append s₁ s₂ tr₁ tr₂) original w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    Verifier.rbrKnowledgeSoundnessOfNodes (V₁.append V₂)
    impl admissible relIn relOut
      (combineDraw plainSig s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  simpa only [combinePrefixDraw_ofNodes, combinePrefixError_ofNodes] using
    (Verifier.rbrKnowledgeSoundness_append_prefix (draw₁ := PrefixDraw.ofNodes plainSig draw₁)
      (draw₂ := fun tr => PrefixDraw.ofNodes plainSig (draw₂ tr.path))
      (ε₁ := PrefixError.ofNodes plainSig ε₁)
      (ε₂ := fun tr => PrefixError.ofNodes plainSig (ε₂ tr.path))
      V₁ V₂ impl mid accepted midWitness outWitness h₁ h₂ hadm glue hout)

/-- Node-indexed standalone verifier composition specializes the full-prefix law. -/
theorem Verifier.rbrKnowledgeSoundness_append_of_pure {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι}
    {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {Win : S → Type} {Wmid : S → Transcript plainSig s₁ → Type}
    {Win₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Type}
    {W : S → Transcript plainSig (s₁.append s₂) → Type}
    {W₂ : (tr₁ : Transcript plainSig s₁) → T tr₁.path →
      Transcript plainSig (s₂ tr₁.path) → Type}
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) (T p) (U p))
    (impl : QueryImpl ambient (StateT σ ProbComp))
    {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
    {relOut₁ : (stmt : S) → (tr : Transcript plainSig s₁) → T tr.path
    → Wmid stmt tr → Prop}
    {admissible₂ : (tr₁ : Transcript plainSig s₁) →
      T tr₁.path → Prop}
    {relMid : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) → Win₂ tr₁ t → Prop}
    {relOut₂ : (tr₁ : Transcript plainSig s₁) → (t : T tr₁.path) →
      (tr₂ : Transcript plainSig (s₂ tr₁.path)) →
      U tr₁.path tr₂.path → W₂ tr₁ t tr₂ → Prop}
    {relOut : (stmt : S) → (tr : Transcript plainSig (s₁.append s₂)) →
      splitFamily U tr.path → W stmt tr → Prop}
    {draw₁ : QueryImpl (challengeSpec plainSig s₁) ProbComp}
    {draw₂ : (p : Path s₁) → QueryImpl (challengeSpec plainSig (s₂ p)) ProbComp}
    {ε₁ : ChallengeNode plainSig s₁ → ℝ≥0∞}
    {ε₂ : (p : Path s₁) → ChallengeNode plainSig (s₂ p) → ℝ≥0∞}
    (mid : (stmt : S) → (tr₁ : Transcript plainSig s₁) → T tr₁.path)
    (decision : ∀ stmt tr, V₁.decide stmt (Transcript.path tr)
      (toPlainView s₁ tr) = pure (mid stmt tr))
    (midWitness : ∀ stmt tr₁, Win₂ tr₁ (mid stmt tr₁) → Wmid stmt tr₁)
    (outWitness : ∀ stmt tr₁ tr₂,
      W stmt (Transcript.append s₁ s₂ tr₁ tr₂) → W₂ tr₁ (mid stmt tr₁) tr₂)
    (h₁ : Verifier.rbrKnowledgeSoundnessOfNodes V₁
    impl admissible relIn relOut₁ draw₁ ε₁)
    (h₂ : ∀ tr₁, Verifier.rbrKnowledgeSoundnessOfNodes
      (V₂ tr₁.path) impl
      (admissible₂ tr₁) (relMid tr₁) (relOut₂ tr₁) (draw₂ tr₁.path)
      (ε₂ tr₁.path))
    (hadm : ∀ stmt tr₁, admissible stmt → admissible₂ tr₁ (mid stmt tr₁))
    (glue : ∀ stmt tr₁ w, relMid tr₁ (mid stmt tr₁) w →
      relOut₁ stmt tr₁ (mid stmt tr₁) (midWitness stmt tr₁ w))
    (hout : ∀ stmt tr₁ tr₂ out original w, HEq out original →
      relOut stmt (Transcript.append s₁ s₂ tr₁ tr₂) original w →
      relOut₂ tr₁ (mid stmt tr₁) tr₂ out (outWitness stmt tr₁ tr₂ w)) :
    Verifier.rbrKnowledgeSoundnessOfNodes (V₁.append V₂)
    impl admissible relIn relOut
      (combineDraw plainSig s₁ s₂ draw₁ draw₂)
      (combineDraw (m := fun _ => ℝ≥0∞) plainSig s₁ s₂ ε₁ ε₂) := by
  simpa only [combinePrefixDraw_ofNodes, combinePrefixError_ofNodes] using
    (Verifier.rbrKnowledgeSoundness_append_of_pure_prefix
    (draw₁ := PrefixDraw.ofNodes plainSig draw₁)
      (draw₂ := fun tr => PrefixDraw.ofNodes plainSig (draw₂ tr.path))
      (ε₁ := PrefixError.ofNodes plainSig ε₁)
      (ε₂ := fun tr => PrefixError.ofNodes plainSig (ε₂ tr.path))
      V₁ V₂ impl mid decision midWitness outWitness h₁ h₂ hadm glue hout)

/-- Positive oracle acceptance decomposes into supported accepted middle and final results.
The suffix uses the prefix's final ambient state and the actual routed bundle data. -/
theorem OracleVerifier.validAcceptance_append {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι} {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {J : Path s₁ → Type} {B : (p : Path s₁) → J p → Type}
    {K : (p : Path s₁) → Path (s₂ p) → Type}
    {C : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → K p₁ p₂ → Type}
    {inputs : OracleBundle}
    {middle : (p : Path s₁) → OracleFamily.{0, 0, 0} (J p) (B p)}
    {outputs : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
      OracleFamily.{0, 0, 0} (K p₁ p₂) (C p₁ p₂)}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : V₁.OutputCompatibility V₂) (impl : QueryImpl ambient (StateT σ ProbComp))
    (stmt : S × inputs.Data) (tr : Transcript oracleSig (s₁.append s₂))
    (langOut : OracleVerifier.Output (splitFamily U)
      (fun p => C (Path.split s₁ s₂ p).1 (Path.split s₁ s₂ p).2)
      tr.path → Prop)
    (h : (V₁.append V₂ compatible).validAcceptance impl stmt tr langOut) :
    let p := tr.path
    let v := toView _ tr
    let data := (stmt.2, oracleMessages _ tr)
    ∃ state mid between out final,
      (some mid, between) ∈ support ((simulateQ impl
        (V₁.decideWith stmt.1 (Path.split s₁ s₂ p).1 (View.split s₁ s₂ p v).1
          ((OracleVerifier.prefixRoute (inputs := inputs) p).f data))).run state) ∧
      (some out, final) ∈ support ((simulateQ impl
        ((V₂ (Path.split s₁ s₂ p).1).decideWith mid (Path.split s₁ s₂ p).2
          (View.split s₁ s₂ p v).2
          ((OracleVerifier.suffixRoute V₁ stmt.1 p v).f data))).run between) ∧
      langOut (out, ((V₂ (Path.split s₁ s₂ p).1).outputMap mid (Path.split s₁ s₂ p).2
        (View.split s₁ s₂ p v).2).f ((OracleVerifier.suffixRoute V₁ stmt.1 p v).f data)) := by
  obtain ⟨state, out, final, hr, ho⟩ := (OracleVerifier.validAcceptance_iff_support ..).mp h
  obtain ⟨mid, between, hp, hs⟩ := V₁.support_append V₂ compatible impl stmt.1
    tr.path (toView _ tr) ((stmt.2, oracleMessages _ tr))
    state final out hr
  have hp' : some mid ∈ support (V₁.decideWith stmt.1
      (Path.split s₁ s₂ tr.path).1
      (View.split s₁ s₂ _ (toView _ tr)).1
      ((OracleVerifier.prefixRoute (inputs := inputs)
        tr.path).f ((stmt.2, oracleMessages _ tr)))) := by
    apply OracleComp.support_simulateQ_run'_subset impl _ state
    rw [StateT.run'_eq, _root_.support_map]
    exact ⟨(some mid, between), hp, rfl⟩
  have he := compatible.agrees stmt.1 tr.path (toView _ tr)
    ((stmt.2, oracleMessages _ tr)) mid hp'
  change langOut (out, (compatible.outputMap stmt.1 _ _).f _) at ho
  rw [he] at ho
  exact ⟨state, mid, between, out, final, hp, hs, ho⟩

end Interaction
