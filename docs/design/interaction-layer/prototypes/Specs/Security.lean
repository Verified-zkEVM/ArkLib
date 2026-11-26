/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Run
import ArkLib.Interaction.Security.Completeness
import ArkLib.Interaction.Security.Soundness
import ArkLib.Interaction.Security.RoundByRound

/-!
# Security statements for specifications

This module states completeness, soundness and round-by-round soundness of a specification as
ArkLib's statements about the specification's derived prover (`Spec.prover`) and verifier
(`Spec.verifier`), and gives the languages that a specification's stage claims denote.

* `Spec.Sound`, `Spec.RBRSound`, `Spec.RBRKnowledgeSound` and `Spec.Complete` are ArkLib's
  `OracleVerifier.soundness`, `OracleVerifier.rbrSoundness`,
  `OracleVerifier.rbrKnowledgeSoundnessOfNodes` and `Interaction.completeness` (in the classical
  model) applied to the specification's verifier and honest prover. Each has an `iff` lemma to the
  ArkLib statement (`Spec.sound_iff`, `Spec.rbrSound_iff`, `Spec.rbrKnowledgeSound_iff`,
  `Spec.complete_iff`), so this module adds no trusted definition.
* `Desc.inClaim` and `Desc.outClaim` evaluate a description's stage claims: the input claim of
  the first stage, read before any move, and the output claim of the last stage along a full
  transcript. `Spec.inputProblem` and `Spec.outputProblem` are the ArkLib problems whose
  languages these claims denote. A soundness statement with these problems reads "if the input
  claim is false, the verifier accepts an output whose claim is true with probability at most
  `ε`".
* `Spec.verdict_of_validAcceptance`: an accepting decision of the specification's verifier is an
  accepting pure verdict. Soundness proofs through the kit use it for the leaf obligation.
* `Spec.Sound.mono`: soundness is monotone in the input and output languages.
* Stage contracts: `Spec.ClaimSound` and `Spec.ClaimRBRSound` (soundness and round-by-round
  soundness with `Spec.inputProblem` and `Spec.outputProblem`), `Spec.ClaimComplete` (a true input
  claim makes every check hold on the honest values and the output claim true on every honest
  transcript) and `Spec.StageContract` (both). `Spec.ClaimComplete.accepts` turns completeness into
  acceptance with a true output claim, and `Spec.ClaimSound.of_sound` derives the soundness contract
  from soundness on other problems by comparing languages. `Specs.Claims` instantiates them for
  sum-check.

## Design choices

* The statements take the challenge draw, the ambient oracles and the input and output problems
  as arguments, exactly as ArkLib's do. *Why:* the front end then adds nothing to the meaning of
  ArkLib's notions, and a theorem about a specification is literally a theorem about its derived
  verifier.
* `Spec.Complete` runs the honest prover with its output paired with the input oracle data
  (`Spec.honestProver`). *Why:* ArkLib's completeness compares the prover's claimed output with
  the verifier's output, and the verifier of a specification outputs its statement together with
  the input oracles it keeps.
* A stage claim is a Boolean formula. A description without a stage claim denotes the claim
  `true`. *Why:* the input language is then everything (soundness is vacuous) and the output
  language accepts every output, so soundness says that the verifier accepts with probability at
  most `ε`. This is plain soundness of a decision protocol.
* The output problem judges an output `(o, d)` at a path `p`. Its language holds when some run of
  the specification with input data `d` and a transcript on `p` returns `o` and makes the output
  claim true. *Why:* ArkLib's output language reads only the output and the path, while a stage's
  output claim reads values of the transcript. When the claim reads only values that the output
  determines, as sum-check's `p(r) = c_n` does, the language is the claim on the output
  (`Specs.Claims` proves the inclusion in ArkLib's output language for sum-check).
* The stage contracts are about the input claim of the first stage and the output claim of the
  last stage. *Why:* these are the claims `Spec.inClaim` and `Spec.outClaim` read, so a contract of
  a single-stage specification is the contract of its stage. A contract for each stage of a
  multi-stage specification needs the state between stages and is not stated here.
* The completeness contract is deterministic and takes a witness relation `wit`. *Why:* the stage
  claims read the statement and the input oracles, not the witness, so the contract must say
  which witness the honest prover uses, and a description's checks hold or fail for each choice of
  challenges, with no probability involved.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens
open scoped ENNReal

variable {In : OracleBundle} {W T : Type}

/-! ## Stage claims of a description -/

namespace Desc

/-- The input claim of a description: the claim of its first stage, evaluated with the input
oracles answered by `ans`. It is `none` when a move or the end comes before any stage. Input
reads, local values, checks and markers before the stage are walked through. -/
noncomputable def inClaim (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks → Handlers Id → ℕ → Option Bool
  | _, _, .done _, _, _ => none
  | _, _, .message .., _, _ => none
  | _, _, .oracle .., _, _ => none
  | _, _, .challenge .., _, _ => none
  | _, _, .branch .., _, _ => none
  | _, _, .check _ _ _ _ _ rest, env, ℓ => rest.inClaim ans env ℓ
  | _, _, .compute _ _ _ _ φ args _ rest, env, ℓ =>
      (rest ((φ.inst args).eval (askId env))).inClaim ans env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).inClaim ans (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1)
  | _, _, .stageIn _ _ φ args _ _ _, env, _ => some ((φ.inst args).eval (askId env))
  | _, _, .stageOut .., _, _ => none
  | _, _, .mark _ rest, env, ℓ => rest.inClaim ans env ℓ
  | _, _, .loop _ _ _ inner, env, ℓ => inner.inClaim ans env ℓ

/-- The output claim of a description along a full transcript: the claim of the last stage that
ends on the way, evaluated with the input oracles answered by `ans` and the oracle messages read
from the transcript. `acc` is the claim of the last stage ended so far. Checks do not stop the
walk, so the output claim is defined on rejected transcripts too. -/
noncomputable def outClaim (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks → Transcript oracleSig t →
      Handlers Id → ℕ → Option Bool → Option Bool
  | _, _, .done _, _, _, _, acc => acc
  | _, _, .message _ _ _ _ _ _ rest, ⟨x, tr⟩, env, ℓ, acc => (rest x).outClaim ans tr env ℓ acc
  | _, _, .oracle _ _ I _ hA dflt _ _ _ _ rest, ⟨x, tr⟩, env, ℓ, acc =>
      (rest ⟨⟨ℓ, dflt⟩⟩).outClaim ans tr (env.ext ℓ (honestEntry I hA x)) (ℓ + 1) acc
  | _, _, .challenge _ _ _ _ rest, ⟨c, tr⟩, env, ℓ, acc => (rest c).outClaim ans tr env ℓ acc
  | _, _, .check _ _ _ _ _ rest, tr, env, ℓ, acc => rest.outClaim ans tr env ℓ acc
  | _, _, .compute _ _ _ _ φ args _ rest, tr, env, ℓ, acc =>
      (rest ((φ.inst args).eval (askId env))).outClaim ans tr env ℓ acc
  | _, _, .input _ _ _ _ embed resp dflt rest, tr, env, ℓ, acc =>
      (rest ⟨⟨ℓ, dflt⟩⟩).outClaim ans tr (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1) acc
  | _, _, .branch _ _ _ _ _ _ rest, ⟨x, tr⟩, env, ℓ, acc => (rest x).outClaim ans tr env ℓ acc
  | _, _, .stageIn _ _ _ _ _ _ rest, tr, env, ℓ, acc => rest.outClaim ans tr env ℓ acc
  | _, _, .stageOut _ ψ args rest, tr, env, ℓ, _ =>
      rest.outClaim ans tr env ℓ (some ((ψ.inst args).eval (askId env)))
  | _, _, .mark _ rest, tr, env, ℓ, acc => rest.outClaim ans tr env ℓ acc
  | _, _, .loop _ _ _ inner, tr, env, ℓ, acc => inner.outClaim ans tr env ℓ acc

end Desc

namespace Spec
variable {S : Type} {t : OracleProtocol} {ks : Skel}

/-- The input claim of a specification on a statement and input oracle data. -/
noncomputable def inClaim (s : Spec In S W T t ks) (x : S × In.Data) : Option Bool :=
  (s.desc x.1).inClaim (In.answer x.2) .empty 0

/-- The output claim of a specification along a full transcript. -/
noncomputable def outClaim (s : Spec In S W T t ks) (stmt : S) (data : In.Data)
    (tr : Transcript oracleSig t) : Option Bool :=
  (s.desc stmt).outClaim (In.answer data) tr .empty 0 none

/-- The input claim holds. A specification without an input claim has the claim `true`. -/
def InClaim (s : Spec In S W T t ks) (x : S × In.Data) : Prop :=
  (s.inClaim x).getD true = true

/-- The problem whose language the input claim denotes. -/
def inputProblem (s : Spec In S W T t ks) : StatementProblem (S × In.Data) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := s.InClaim x
  rel_admissible _ _ _ _ := trivial

/-- The problem whose language the output claim denotes: some run with the same input data and a
transcript on the path returns the output and makes the output claim true. A specification
without an output claim has the claim `true`. -/
def outputProblem (s : Spec In S W T t ks) : PathProblem t (fun _ => T × In.Data) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel p o _ := ∃ (stmt : S) (tr : Transcript oracleSig t), Transcript.path tr = p ∧
    s.verdict stmt o.2 tr = some o.1 ∧ (s.outClaim stmt o.2 tr).getD true = true
  rel_admissible _ _ _ _ := trivial

theorem inputProblem_language (s : Spec In S W T t ks) (x : S × In.Data) :
    s.inputProblem.language () x ↔ s.InClaim x :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem outputProblem_language (s : Spec In S W T t ks) (p : Path t) (o : T × In.Data) :
    s.outputProblem.language p o ↔ ∃ (stmt : S) (tr : Transcript oracleSig t),
      Transcript.path tr = p ∧ s.verdict stmt o.2 tr = some o.1 ∧
        (s.outClaim stmt o.2 tr).getD true = true :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

/-! ## The statements -/

section Statements
variable (s : Spec In S W T t ks) {ι σ : Type} (ambient : OracleSpec ι)

/-- Soundness of the specification's verifier: ArkLib's `OracleVerifier.soundness` of
`s.verifier ambient`. -/
def Sound (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (ε : ℝ≥0∞) : Prop :=
  (s.verifier ambient).soundness init impl draw input output ε

theorem sound_iff (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (ε : ℝ≥0∞) :
    s.Sound ambient init impl draw input output ε ↔
      (s.verifier ambient).soundness init impl draw input output ε :=
  Iff.rfl

/-- Round-by-round soundness of the specification's verifier: ArkLib's
`OracleVerifier.rbrSoundness` of `s.verifier ambient`, with an error at each challenge node. -/
def RBRSound (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (ε : ChallengeNode oracleSig t → ℝ≥0∞) : Prop :=
  (s.verifier ambient).rbrSoundness impl input output draw ε

theorem rbrSound_iff (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (ε : ChallengeNode oracleSig t → ℝ≥0∞) :
    s.RBRSound ambient impl input output draw ε ↔
      (s.verifier ambient).rbrSoundness impl input output draw ε :=
  Iff.rfl

/-- Round-by-round knowledge soundness of the specification's verifier, with node-indexed draws
and errors: ArkLib's `OracleVerifier.rbrKnowledgeSoundnessOfNodes` of `s.verifier ambient`. -/
def RBRKnowledgeSound {Win : S × In.Data → Type}
    {Wout : S × In.Data → Transcript oracleSig t → Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (admissible : S × In.Data → Prop)
    (relIn : (x : S × In.Data) → Win x → Prop)
    (relOut : (x : S × In.Data) → (tr : Transcript oracleSig t) → T × In.Data → Wout x tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (ε : ChallengeNode oracleSig t → ℝ≥0∞) : Prop :=
  (s.verifier ambient).rbrKnowledgeSoundnessOfNodes impl admissible relIn relOut draw ε

theorem rbrKnowledgeSound_iff {Win : S × In.Data → Type}
    {Wout : S × In.Data → Transcript oracleSig t → Type}
    (impl : QueryImpl ambient (StateT σ ProbComp)) (admissible : S × In.Data → Prop)
    (relIn : (x : S × In.Data) → Win x → Prop)
    (relOut : (x : S × In.Data) → (tr : Transcript oracleSig t) → T × In.Data → Wout x tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (ε : ChallengeNode oracleSig t → ℝ≥0∞) :
    s.RBRKnowledgeSound ambient impl admissible relIn relOut draw ε ↔
      (s.verifier ambient).rbrKnowledgeSoundnessOfNodes impl admissible relIn relOut draw ε :=
  Iff.rfl

/-- The honest prover over the ambient oracles, with its output paired with the input oracle
data, as ArkLib's verifier output is. -/
noncomputable def honestProver (x : S × In.Data) (w : W) :
    Prover oracleSig ambient t (fun _ => T × In.Data) :=
  Strategy.mapOutput (fun _ out => (out, x.2)) (s.prover (m := OracleComp ambient) x.1 w x.2)

/-- Completeness of the specification: ArkLib's `Interaction.completeness` in the classical model
of `s.verifier ambient`, for the honest prover `s.honestProver` with the witness that
`witness` reads from an input witness. `readWitness` reads the output witness of an accepted
outcome, as in `OutputJudgement.ofOutcome`. -/
def Complete (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (witness : ∀ x, input.Witness () x → W)
    (readWitness : ∀ obs : Outcome oracleSig t (fun _ => T × In.Data)
        (OracleVerifier.Output (fun _ => T) (fun _ => In)),
      ∀ o, obs.2.2 = some o → output.Witness (Transcript.path obs.1) o)
    (ε : ℝ≥0∞) : Prop :=
  letI : MeasurableSpace (Outcome oracleSig t (fun _ => T × In.Data)
    (OracleVerifier.Output (fun _ => T) (fun _ => In))) := ⊤
  Interaction.completeness ((s.verifier ambient).classicalModel init impl draw) input output
    (OutputJudgement.ofOutcome output (fun _ o => o) readWitness)
    (fun x w => s.honestProver ambient x (witness x w)) ε

theorem complete_iff (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (input : StatementProblem (S × In.Data)) (output : PathProblem t (fun _ => T × In.Data))
    (witness : ∀ x, input.Witness () x → W)
    (readWitness : ∀ obs : Outcome oracleSig t (fun _ => T × In.Data)
        (OracleVerifier.Output (fun _ => T) (fun _ => In)),
      ∀ o, obs.2.2 = some o → output.Witness (Transcript.path obs.1) o)
    (ε : ℝ≥0∞) :
    s.Complete ambient init impl draw input output witness readWitness ε ↔
      letI : MeasurableSpace (Outcome oracleSig t (fun _ => T × In.Data)
        (OracleVerifier.Output (fun _ => T) (fun _ => In))) := ⊤
      Interaction.completeness ((s.verifier ambient).classicalModel init impl draw) input output
        (OutputJudgement.ofOutcome output (fun _ o => o) readWitness)
        (fun x w => s.honestProver ambient x (witness x w)) ε :=
  Iff.rfl

/-- Soundness is monotone: a smaller set of false inputs and a smaller output language keep it. -/
theorem Sound.mono {init : ProbComp σ} {impl : QueryImpl ambient (StateT σ ProbComp)}
    {draw : QueryImpl (challengeSpec oracleSig t) ProbComp}
    {input input' : StatementProblem (S × In.Data)}
    {output output' : PathProblem t (fun _ => T × In.Data)} {ε : ℝ≥0∞}
    (hin : ∀ x, input'.admissible () x → ¬ input'.language () x →
      input.admissible () x ∧ ¬ input.language () x)
    (hout : ∀ p o, output'.language p o → output.language p o)
    (h : s.Sound ambient init impl draw input output ε) :
    s.Sound ambient init impl draw input' output' ε := by
  unfold Spec.Sound OracleVerifier.soundness Interaction.soundness at *
  intro Out stmt hadm hlang adv
  obtain ⟨hadm', hlang'⟩ := hin stmt hadm hlang
  refine le_trans (MeasureTheory.measure_mono ?_) (h Out stmt hadm' hlang' adv)
  rintro obs ⟨o, ho, hl⟩
  exact ⟨o, ho, hout _ _ hl⟩

/-- An accepting decision of the specification's verifier on a full transcript is an accepting
verdict whose output, paired with the input data, is in the event. -/
theorem verdict_of_validAcceptance (impl : QueryImpl ambient (StateT σ ProbComp))
    (x : S × In.Data) (tr : Transcript oracleSig t) (event : T × In.Data → Prop) :
    (s.verifier ambient).validAcceptance impl x tr event →
      ∃ o, s.verdict x.1 x.2 tr = some o ∧ event (o, x.2) := by
  unfold OracleVerifier.validAcceptance
  dsimp only
  rw [Spec.decide_eq_verdict]
  intro h
  obtain ⟨state, hs⟩ := h
  classical
  by_contra hf
  cases hv : s.verdict x.1 x.2 tr with
  | none => simp [hv] at hs
  | some o =>
    have hne : ¬ event (o, x.2) := fun he => hf ⟨o, hv, he⟩
    simp [hv, Spec.verifier, OracleMap.fst, hne] at hs

end Statements

/-! ## Stage contracts

A stage contract states what a specification's stage claims mean for its verifier and its honest
prover, in the two directions of a reduction. Each is a thin definition over the statements
above. -/

section Contracts
variable (s : Spec In S W T t ks)

/-- The output claim holds along the transcript. A specification without an output claim has the
claim `true`. -/
def OutClaim (stmt : S) (data : In.Data) (tr : Transcript oracleSig t) : Prop :=
  (s.outClaim stmt data tr).getD true = true

theorem outputProblem_language_of_verdict {stmt : S} {data : In.Data}
    {tr : Transcript oracleSig t} {o : T} (hv : s.verdict stmt data tr = some o)
    (hc : s.OutClaim stmt data tr) : s.outputProblem.language (Transcript.path tr) (o, data) :=
  (s.outputProblem_language _ _).mpr ⟨stmt, tr, rfl, hv, hc⟩

variable {ι σ : Type} (ambient : OracleSpec ι)

/-- **Soundness contract of the stage claims.** If the input claim is false, the verifier accepts
an output whose output claim is true with probability at most `ε`: `Spec.Sound` with the
problems that the claims denote, `Spec.inputProblem` and `Spec.outputProblem`. -/
def ClaimSound (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp) (ε : ℝ≥0∞) : Prop :=
  s.Sound ambient init impl draw s.inputProblem s.outputProblem ε

/-- **Round-by-round soundness contract of the stage claims**: `Spec.RBRSound` with the problems
that the claims denote. -/
def ClaimRBRSound (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp)
    (ε : ChallengeNode oracleSig t → ℝ≥0∞) : Prop :=
  s.RBRSound ambient impl s.inputProblem s.outputProblem draw ε

/-- **Completeness contract of the stage claims.** For every input `x` and witness `w` that `wit`
relates, if the input claim holds, then every check holds on the honest values for every choice
of challenges (`Desc.Complete`, so the verdict accepts every honest transcript by
`Spec.verdict_isSome`), and the output claim holds on every honest transcript. `wit` says which
witness the honest prover runs with, for example that the witness is the input oracle. -/
def ClaimComplete (wit : S × In.Data → W → Prop) : Prop :=
  ∀ x w, wit x w → s.InClaim x →
    (s.desc x.1).Complete w (In.answer x.2) .empty 0 ∧
      ∀ tr, (s.desc x.1).Honest w (In.answer x.2) tr .empty 0 → s.OutClaim x.1 x.2 tr

/-- **The stage contract**: the soundness and completeness contracts of the stage claims. A
protocol author proves it once per stage. -/
structure StageContract (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig t) ProbComp) (ε : ℝ≥0∞)
    (wit : S × In.Data → W → Prop) : Prop where
  sound : s.ClaimSound ambient init impl draw ε
  complete : s.ClaimComplete wit

variable {s ambient}

/-- Under the completeness contract, an honest run with a true input claim is accepted, its
output claim is true, and its output is in the output language. -/
theorem ClaimComplete.accepts {wit : S × In.Data → W → Prop} (h : s.ClaimComplete wit)
    {x : S × In.Data} {w : W} (hw : wit x w) (hin : s.InClaim x) (tr : Transcript oracleSig t)
    (hh : (s.desc x.1).Honest w (In.answer x.2) tr .empty 0) :
    ∃ o, s.verdict x.1 x.2 tr = some o ∧ s.OutClaim x.1 x.2 tr ∧
      s.outputProblem.language (Transcript.path tr) (o, x.2) := by
  obtain ⟨hc, hout⟩ := h x w hw hin
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (s.verdict_isSome x.1 w x.2 tr hc hh)
  exact ⟨o, ho, hout tr hh, s.outputProblem_language_of_verdict ho (hout tr hh)⟩

/-- **Soundness on the stage claims from soundness on other problems.** The input claim's
language must contain the other input language on admissible inputs, and the other output
language must contain the output claim's language. -/
theorem ClaimSound.of_sound {init : ProbComp σ} {impl : QueryImpl ambient (StateT σ ProbComp)}
    {draw : QueryImpl (challengeSpec oracleSig t) ProbComp}
    {input : StatementProblem (S × In.Data)} {output : PathProblem t (fun _ => T × In.Data)}
    {ε : ℝ≥0∞} (hadm : ∀ x, input.admissible () x)
    (hin : ∀ x, input.language () x → s.InClaim x)
    (hout : ∀ p o, s.outputProblem.language p o → output.language p o)
    (h : s.Sound ambient init impl draw input output ε) :
    s.ClaimSound ambient init impl draw ε :=
  Spec.Sound.mono s ambient
    (fun x _ hx => ⟨hadm x, fun hl => hx ((s.inputProblem_language x).mpr (hin x hl))⟩) hout h

end Contracts

end Spec

#print axioms Spec.ClaimComplete.accepts
#print axioms Spec.ClaimSound.of_sound
#print axioms Spec.Sound.mono
#print axioms Spec.verdict_of_validAcceptance
#print axioms Spec.sound_iff
#print axioms Spec.complete_iff

end Specs
