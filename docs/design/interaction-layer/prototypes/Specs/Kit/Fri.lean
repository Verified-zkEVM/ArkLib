/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.FoldingSoundness
import ArkLib.ProofSystem.Fri.QuerySoundness
import ArkLib.Data.CodingTheory.ProximityGenerator.PolynomialGenerator
import Specs.Kit.Iteration

/-!
# The FRI commit phase through the generalized kit

This module proves round-by-round soundness of FRI's commit phase from the iteration theorem of
`Specs.Kit.Iteration`. FRI is the kit's first instance whose message types vary per round.

## The protocol

The input is a word `f₀` on the evaluation domain `ω` of size `2 ^ N`, which the verifier reads
as an oracle. Round `i < r` folds once:

* the prover sends the word `fᵢ` on the domain `dom ω i`, the domain `ω` halved `i` times, as an
  oracle (round `0` sends nothing, since `f₀` is the input);
* the verifier sends a folding challenge `αᵢ : F`.

After round `r - 1`, the prover sends the final polynomial, of degree less than `d`, as a plain
message. `commitPhase ω d j k` is this tree from round `j` with `k` rounds left, defined by its own
recursion, and `friRounds` certifies it as an iteration with rounds `friRound ω i` and suffix
`friSuffix d F`. Every case of the certificate holds by definition.

## The analysis

The state before round `i` is a proposition, "no fold so far has failed", where a fold fails
when ArkLib's bad event `Fri.FoldingAgreementFailure` happens at its challenge. The claim of the
state is "if no fold has failed, the input is close": with the safe flag `b`, the claim is
`b → ¬ Far x`, where `Far δ x` says that `x` has relative distance at least `δ` from every
codeword of the Reed–Solomon code of degree `2 ^ r * d` on `ω`.

* `hroot`: the initial flag is `True`, so the initial claim is the input language `¬ Far δ x`.
* `hround`: from a false claim (the flag holds and the input is far), the next claim is true
  exactly when the fold fails. ArkLib's `Fri.foldingAgreementFailure_prob_le` bounds that
  probability by its mutual correlated agreement error `mcaError`, so the per-round obligation
  holds with error `foldError ω d r θ i` and needs no hypothesis.
* `hleaf`: the output language is `¬ Far δ x ∨ ¬ Safe x tr`: the input is close or some fold
  failed. An accepted transcript of this language has a final state whose claim holds.

The theorem `commitPhase_rbrSoundness` is the result: from a far input, the transcript reaches
a failed fold with round-by-round error `foldError ω d r θ i` at round `i`'s challenge, and the
errors along every path sum to `∑ i, foldError ω d r θ i` (`commitPhase_sum_errors`). This is the
commit-phase half of FRI's soundness. Outside its output language the input is far and no fold
fails. That is the per-fold condition of ArkLib's `Fri.FoldTrace.Safe`, which the query-phase
bound `Fri.query_soundness` assumes. This module does not formalize the link: `FoldTrace` indexes
its domains by `subdomain` chains, and relating them to `dom ω i` needs cast lemmas.

* `commitPhase_rbrSoundness_of_isMCAGenerator`: the same with the error of any MCA certificate
  `IsMCAGenerator` for each round's code, taken as the hypothesis `hMCA`.
* `commitPhase_rbrSoundness_johnson`: the same with explicit errors `johnsonError`, for a positive
  final degree bound `d` and a sharpness parameter `m ≥ 3`. ArkLib's
  `RSCode.isMCAGenerator_univariatePowersGenerator` discharges `hMCA`, so this theorem has no
  hypothesis beyond its parameters.

## Design choices

* **The domains are a sigma-valued recursion.** `dom ω i` carries its dimension, and
  `dom ω (i + 1)` is `(dom ω i).2.subdomain 1`. The word of round `i` lives on `dom ω i` without
  a cast, and ArkLib's folding bound applies to it as stated.
* **Round `0` has an empty block.** The input word plays the role of round `0`'s message, so
  the rounds of an iteration need not all send a message. `wordOf` picks the input or the
  round's message.
* **The analysis tracks a flag, not the folded word.** FRI's bad event at round `i` depends only
  on `fᵢ` and `αᵢ`, so the state needs no word, and the per-round bound is ArkLib's bound for
  one fold.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open PFunctor FreeM Interaction Interaction.TwoParty Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec MeasureTheory
open Fri Polynomial Domain ProximityGap ReedSolomon LinearCode CoreDefinitions

namespace Fri

variable {F : Type} [Field F] [DecidableEq F] {N : ℕ} (ω : SmoothCosetFftDomain N F)

/-! ## The protocol -/

/-- The evaluation domain of round `i`: `ω` halved `i` times, with its dimension. -/
def dom : ℕ → Σ m, SmoothCosetFftDomain m F
  | 0 => ⟨N, ω⟩
  | i + 1 => ⟨(dom i).1 - 1, (dom i).2.subdomain 1⟩

/-- A word on the domain of round `i`. -/
abbrev Word (i : ℕ) : Type := Fin (2 ^ (dom ω i).1) → F

/-- The block of round `i`: nothing in round `0`, the word `fᵢ` as an oracle afterwards. -/
@[reducible]
def friMsgs : ℕ → Block
  | 0 => []
  | i + 1 => [.oracle (Word ω (i + 1)) OracleInterface.instFunction]

/-- Round `i` of the commit phase: its block, then a folding challenge. -/
@[reducible]
def friRound (i : ℕ) : Round := ⟨friMsgs ω i, F⟩

variable (d : ℕ)

/-- The suffix: the final polynomial over `K`, of degree less than `d`. -/
@[reducible]
def friSuffix (K : Type) [Field K] : Block := [.plain (Polynomial.degreeLT K d)]

/-- **The commit phase, by its own recursion**, from round `j` with `k` rounds left. -/
def commitPhase : (j k : ℕ) → OracleProtocol
  | _, 0 => .liftBind (.message (Polynomial.degreeLT F d)) fun _ => .pure PUnit.unit
  | 0, k + 1 => .liftBind (.challenge F) fun _ => commitPhase 1 k
  | j + 1, k + 1 => .liftBind (.oracle (Word ω (j + 1)) OracleInterface.instFunction) fun _ =>
      .liftBind (.challenge F) fun _ => commitPhase (j + 1 + 1) k

variable (r : ℕ)

/-- **The commit phase is an instance.** Each case holds by definition of `commitPhase`. -/
def friRounds : (j k : ℕ) → (h : j + k = r) →
    Rounds (fun i : Fin r => friRound ω i.val) (friSuffix d F) j k h (commitPhase ω d j k)
  | j, 0, h => by subst h; exact .done
  | 0, k + 1, h => .round 0 k h (friRounds 1 k (by omega))
  | j + 1, k + 1, h => .round (j + 1) k h (friRounds (j + 1 + 1) k (by omega))

/-- The draw of the commit phase: every folding challenge is uniform. -/
noncomputable def friDraw [SampleableType F] :
    QueryImpl (challengeSpec oracleSig (commitPhase ω d 0 r)) ProbComp :=
  (friRounds ω d r 0 r (Nat.zero_add r)).challengeDraw fun _ => $ᵗ F

/-! ## The analysis -/

variable {ω d r}

/-- The word that round `i` folds: the input in round `0`, the round's message afterwards. -/
def wordOf (x : Word ω 0) : (i : ℕ) → (friMsgs ω i).Values → Word ω i
  | 0, _ => x
  | _ + 1, vals => vals.1

variable (ω d r)

/-- The input `x` is `δ`-far from the Reed–Solomon code of degree `2 ^ r * d` on `ω`. -/
def Far (δ : ℝ) (x : Word ω 0) : Prop :=
  ∀ u ∈ code (ω : Fin (2 ^ N) ↪ F) (2 ^ r * d), δ ≤ (Code.relHammingDist x u : ℝ)

/-- The fold of round `i` fails: ArkLib's bad event for folding the word `f` on `dom ω i` once
with challenge `α`, into degree `2 ^ (r - (i + 1)) * d`. -/
def FoldFails (θ : ℝ) (i : ℕ) (f : Word ω i) (α : F) : Prop :=
  FoldingAgreementFailure (dom ω i).2 f 1 (2 ^ (r - (i + 1)) * d) θ α

/-- No fold from round `j` on fails along the transcript, by recursion along `commitPhase`. -/
def SafeFrom (θ : ℝ) (x : Word ω 0) :
    (j k : ℕ) → Transcript oracleSig (commitPhase ω d j k) → Prop
  | _, 0, _ => True
  | 0, k + 1, tr => ¬ FoldFails ω d r θ 0 x tr.1 ∧ SafeFrom θ x 1 k tr.2
  | j + 1, k + 1, tr =>
      ¬ FoldFails ω d r θ (j + 1) tr.1 tr.2.1 ∧ SafeFrom θ x (j + 1 + 1) k tr.2.2

/-- No fold of the commit phase fails. -/
abbrev Safe (θ : ℝ) (x : Word ω 0) (tr : Transcript oracleSig (commitPhase ω d 0 r)) : Prop :=
  SafeFrom ω d r θ x 0 r tr

/-- The round update: the flag stays true while no fold fails. The commit phase has no check. -/
def friStep (θ : ℝ) (x : Word ω 0) :
    Step (fun i : Fin r => friRound ω i.val) (fun _ => Prop) :=
  fun i b vals α => some (b ∧ ¬ FoldFails ω d r θ i (wordOf x i vals) α)

/-- The claim of the flag `b`: if no fold has failed, the input is close. -/
def friGood (δ : ℝ) (x : Word ω 0) : ∀ _ : Fin (r + 1), Prop → Prop :=
  fun _ b => b → ¬ Far ω d r δ x

/-- The error of round `i`: ArkLib's mutual correlated agreement error for folding once on
`dom ω i` into degree `2 ^ (r - (i + 1)) * d`. -/
noncomputable def foldError [SampleableType F] (θ : ℝ) (i : Fin r) : ℝ≥0∞ :=
  mcaError (fun α (j : Fin (2 ^ 1)) ↦ α ^ (j : ℕ))
    (code ((dom ω i).2.subdomain 1 : Fin (2 ^ ((dom ω i).1 - 1)) ↪ F)
      (2 ^ (r - (i + 1)) * d)) θ

/-- **The per-round obligation of FRI, from ArkLib.** From a far input and a safe flag, the
next claim holds only if the fold fails, which `Fri.foldingAgreementFailure_prob_le` bounds. -/
theorem fri_roundSound [SampleableType F] (θ δ : ℝ) (x : Word ω 0) :
    RoundSound (fun _ => $ᵗ F) (friStep ω d r θ x) (friGood ω d r δ x) (foldError ω d r θ) := by
  intro i b vals hfalse
  simp only [friGood, not_imp, not_not] at hfalse
  refine (prEvent_mono _ _ _ fun α hα => ?_).trans
    (foldingAgreementFailure_prob_le (k := 1) (d := 2 ^ (r - (i + 1)) * d) (dom ω i).2
      (wordOf x i vals) θ)
  obtain ⟨st', hst', hgood⟩ := hα
  cases hst'
  by_contra hok
  exact hgood ⟨hfalse.1, hok⟩ hfalse.2

/-- The kit's verdict from flag `b` is a flag that holds when `b` holds and no fold from round
`j` on fails. -/
theorem friVerdict (θ : ℝ) (x : Word ω 0) : ∀ (j k : ℕ) (h : j + k = r) (b : Prop)
    (tr : Transcript oracleSig (commitPhase ω d j k)),
    ∃ p, (friRounds ω d r j k h).verdict (friStep ω d r θ x) (some b) tr = some p ∧
      (p.1 ↔ b ∧ SafeFrom ω d r θ x j k tr)
  | j, 0, h, b, tr => by
    subst h
    exact ⟨_, rfl, ⟨fun hb => ⟨hb, trivial⟩, And.left⟩⟩
  | 0, k + 1, h, b, tr => by
    obtain ⟨p, hp, hiff⟩ := friVerdict θ x 1 k (by omega) (b ∧ ¬ FoldFails ω d r θ 0 x tr.1) tr.2
    exact ⟨p, hp, hiff.trans and_assoc⟩
  | j + 1, k + 1, h, b, tr => by
    obtain ⟨p, hp, hiff⟩ := friVerdict θ x (j + 1 + 1) k (by omega)
      (b ∧ ¬ FoldFails ω d r θ (j + 1) tr.1 tr.2.1) tr.2.2
    exact ⟨p, hp, hiff.trans and_assoc⟩

/-! ## Round-by-round soundness -/

/-- **Round-by-round soundness of FRI's commit phase, from the iteration theorem.** From an
input that is `δ`-far from the code, the commit phase reaches a transcript on which some fold
fails with round-by-round error `foldError ω d r θ i` at round `i`'s folding challenge. Every
hypothesis is discharged: the per-round bound is ArkLib's `foldingAgreementFailure_prob_le`. -/
theorem commitPhase_rbrSoundness [SampleableType F] (θ δ : ℝ) :
    Interaction.rbrSoundness oracleSig (commitPhase ω d 0 r) (fun _ => True)
      (fun x : Word ω 0 => ¬ Far ω d r δ x)
      (fun x tr => ¬ Far ω d r δ x ∨ ¬ Safe ω d r θ x tr) (friDraw ω d r)
      (fun c => foldError ω d r θ ((friRounds ω d r 0 r (Nat.zero_add r)).iterRoundOf
        (pre := []) c)) := by
  refine (friRounds ω d r 0 r (Nat.zero_add r)).rbrSoundness (pre := []) (S := fun _ => Prop)
    (Stmt := Word ω 0) (fun _ _ => some True) (friStep ω d r θ) (friGood ω d r δ)
    (friDraw ω d r) (fun _ => $ᵗ F) (foldError ω d r θ)
    (fun _ => Rounds.drawIs_challengeDraw _ _) (fun x _ st _ hs h => ?_) (fun x tr hacc => ?_)
    (fun x => fri_roundSound ω d r θ δ x)
  · cases hs
    exact h True.intro
  · obtain ⟨p, hp, hiff⟩ := friVerdict ω d r θ x 0 r (Nat.zero_add r) True tr
    refine ⟨p, hp, fun hb => ?_⟩
    rcases hacc with hclose | hunsafe
    · exact hclose
    · exact absurd (hiff.mp hb).2 hunsafe

omit [DecidableEq F] in
/-- Along every path of the commit phase, the round errors sum to `∑ i, foldError ω d r θ i`. -/
theorem commitPhase_sum_errors [SampleableType F] (θ : ℝ) (p : Path (commitPhase ω d 0 r)) :
    ∑ c ∈ challengeNodesOn oracleSig (commitPhase ω d 0 r) p,
      foldError ω d r θ ((friRounds ω d r 0 r (Nat.zero_add r)).iterRoundOf (pre := []) c) =
      ∑ i, foldError ω d r θ i :=
  Rounds.sum_iterRoundOf (pre := []) _ _ p

/-- **FRI's commit phase with MCA certificates.** If ArkLib's `IsMCAGenerator` holds for the
powers generator on each round's code with error `εMCA i`, the commit phase is round-by-round
sound with error `εMCA i θ` at round `i`. `commitPhase_rbrSoundness_johnson` discharges `hMCA`
with ArkLib's Johnson-regime certificate. -/
theorem commitPhase_rbrSoundness_of_isMCAGenerator [SampleableType F]
    (εMCA : Fin r → unitInterval → ℝ≥0)
    (hMCA : ∀ i : Fin r, IsMCAGenerator (fun α (j : Fin (2 ^ 1)) ↦ α ^ (j : ℕ)) (εMCA i)
      (code ((dom ω i).2.subdomain 1 : Fin (2 ^ ((dom ω i).1 - 1)) ↪ F)
        (2 ^ (r - (i + 1)) * d)))
    (θ : unitInterval) (δ : ℝ) :
    Interaction.rbrSoundness oracleSig (commitPhase ω d 0 r) (fun _ => True)
      (fun x : Word ω 0 => ¬ Far ω d r δ x)
      (fun x tr => ¬ Far ω d r δ x ∨ ¬ Safe ω d r θ x tr) (friDraw ω d r)
      (fun c => (εMCA ((friRounds ω d r 0 r (Nat.zero_add r)).iterRoundOf (pre := []) c) θ :
        ℝ≥0∞)) := by
  refine (friRounds ω d r 0 r (Nat.zero_add r)).rbrSoundness (pre := []) (S := fun _ => Prop)
    (Stmt := Word ω 0) (fun _ _ => some True) (friStep ω d r θ) (friGood ω d r δ)
    (friDraw ω d r) (fun _ => $ᵗ F) (fun i => (εMCA i θ : ℝ≥0∞))
    (fun _ => Rounds.drawIs_challengeDraw _ _) (fun x _ st _ hs h => ?_) (fun x tr hacc => ?_)
    (fun x i b vals hfalse => (fri_roundSound ω d r θ δ x i b vals hfalse).trans (hMCA i θ))
  · cases hs
    exact h True.intro
  · obtain ⟨p, hp, hiff⟩ := friVerdict ω d r θ x 0 r (Nat.zero_add r) True tr
    refine ⟨p, hp, fun hb => ?_⟩
    rcases hacc with hclose | hunsafe
    · exact hclose
    · exact absurd (hiff.mp hb).2 hunsafe

/-- The Johnson-regime error of round `i`: ArkLib's MCA error function `reedSolomonMCAError`
for the powers generator of degree `1` on the Reed–Solomon code of round `i`'s fold, at sharpness
parameter `m` and radius `θ`. -/
noncomputable def johnsonError [Fintype F] (m : ℕ) (θ : unitInterval) (i : Fin r) : ℝ≥0∞ :=
  (RSCode.reedSolomonMCAError (2 ^ (r - (i + 1)) * d)
    ((dom ω i).2.subdomain 1 : Fin (2 ^ ((dom ω i).1 - 1)) ↪ F) 1 m θ : ℝ≥0∞)

/-- **FRI's commit phase with explicit errors.** For a positive final degree bound `d` and a
sharpness parameter `m ≥ 3`, the commit phase is round-by-round sound with error
`johnsonError ω d r m θ i` at round `i`. Every hypothesis is discharged by ArkLib: the per-round
bound by `Fri.foldingAgreementFailure_prob_le` and the MCA certificate by
`RSCode.isMCAGenerator_univariatePowersGenerator`. -/
theorem commitPhase_rbrSoundness_johnson [Fintype F] [SampleableType F] [NeZero d] (m : ℕ)
    (hm : 3 ≤ m) (θ : unitInterval) (δ : ℝ) :
    Interaction.rbrSoundness oracleSig (commitPhase ω d 0 r) (fun _ => True)
      (fun x : Word ω 0 => ¬ Far ω d r δ x)
      (fun x tr => ¬ Far ω d r δ x ∨ ¬ Safe ω d r θ x tr) (friDraw ω d r)
      (fun c => johnsonError ω d r m θ
        ((friRounds ω d r 0 r (Nat.zero_add r)).iterRoundOf (pre := []) c)) :=
  commitPhase_rbrSoundness_of_isMCAGenerator ω d r
    (fun i => RSCode.reedSolomonMCAError (2 ^ (r - (i + 1)) * d)
      ((dom ω i).2.subdomain 1 : Fin (2 ^ ((dom ω i).1 - 1)) ↪ F) 1 m)
    (fun i => by
      have : NeZero (2 ^ (r - (i + 1)) * d) :=
        ⟨mul_ne_zero (pow_ne_zero _ two_ne_zero) (NeZero.ne d)⟩
      exact RSCode.isMCAGenerator_univariatePowersGenerator _ _ 1 m hm) θ δ

end Fri

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.Fri.fri_roundSound
#print axioms Specs.Kit.Fri.friVerdict
#print axioms Specs.Kit.Fri.commitPhase_rbrSoundness
#print axioms Specs.Kit.Fri.commitPhase_sum_errors
#print axioms Specs.Kit.Fri.commitPhase_rbrSoundness_of_isMCAGenerator
#print axioms Specs.Kit.Fri.commitPhase_rbrSoundness_johnson
