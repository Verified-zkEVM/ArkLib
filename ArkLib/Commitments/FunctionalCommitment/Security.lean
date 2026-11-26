/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.Basic
public import ArkLib.Interaction.Security.Completeness
public import ToMathlib.Control.Monad.Fold
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Security games for functional commitments

This file defines adaptive correctness and `L`-claim fixed-claim binding for functional
commitments. Both games give the public parameters to the chooser or adversary.

## Running a game

A game is a program `OracleComp (unifSpec + ambient) Bool`. `runGame init impl` interprets it in
`StateT σ ProbComp`: `unifSpec` queries pass through to `ProbComp` and `ambient` queries go to the
stateful implementation `impl`, whose initial state `init` samples. This is the interpretation of
`Interaction.experiment` with the private coins in the left summand. The state is shared by every
phase of the game, so a random oracle answers the commit phase and the opening phase
consistently.

The verifier can query only `ambient` and cannot call the private-coin oracle. The games take a
challenge sampler `chal` as a parameter. The paper notions assume uniform challenges, which
`ChallengeSampler.uniform` draws using `Interaction.challengeQueryImpl`. The `interact` function
runs the prover against `chal q` and returns the verifier's decision as a computation. The
fixed-claim binding game runs all opening interactions before it runs the decisions.

## Games

* `correctnessExperiment` gives `pp` to the chooser, who supplies data `d` and a continuation.
  The honest committer commits to `d`, the continuation sees `cm` and chooses `q`, and the
  honest prover opens `cm` to `I.answer d q`. `Correctness Adv ε` requires acceptance with
  probability at least `1 - ε` for every chooser in `Adv` ([KZG10] Definition 5, evaluation
  clause).
* `fixedClaimBindingExperiment L` gives `pp` to the adversary, who returns a commitment `cm`
  and fixes every claim and opening prover before any opening runs. The adversary wins when
  the verifier accepts every opening and no data agrees with all claimed answers.
  `FixedClaimBinding L Adv ε` bounds the advantage of each adversary in `Adv` by `ε`.

For one-message openings, which have no challenges, fixed-claim binding is [CGKY25] Definition
3.17. For interactive openings it is weaker than the joint game planned for a later PR.

The planned extraction game uses the query interface. The extractor outputs data `d` at
commitment time, and the adversary wins if the verifier accepts an opening of `(q, r)` with
`r ≠ I.answer d q`. Hiding and the state-restoration game with setup are also planned.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I.,
  *Constant-Size Commitments to Polynomials and Their Applications*][KZG10]
* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat–Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

@[expose] public section

open OracleComp OracleSpec Interaction PFunctor FreeM
open scoped ENNReal

namespace FunctionalCommitment

variable {ι : Type} {ambient : OracleSpec.{0, 0} ι} {Data : Type} {I : OracleInterface Data}

section Run

/-- The handler of a game: `unifSpec` queries pass through to `ProbComp`, and `ambient` queries
go to `impl`. -/
def ambientImpl {σ : Type} (impl : QueryImpl ambient (StateT σ ProbComp)) :
    QueryImpl (unifSpec + ambient) (StateT σ ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + impl

/-- Run a game: sample the initial state with `init` and interpret the program with
`ambientImpl impl`. -/
def runGame {σ α : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (program : OracleComp (unifSpec + ambient) α) : ProbComp α := do
  (simulateQ (ambientImpl impl) program).run' (← init)

/-- Every possible result of a run of a game is a possible result of the game program. -/
theorem support_runGame_subset {σ α : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (program : OracleComp (unifSpec + ambient) α) :
    support (runGame init impl program) ⊆ support program := by
  intro x hx
  simp only [runGame, mem_support_bind_iff] at hx
  obtain ⟨s, -, hx⟩ := hx
  exact support_simulateQ_run'_subset _ program s hx

end Run

variable (FC : FunctionalCommitment ambient Data I)

/-- A challenge sampler draws the challenges of each opening protocol. -/
abbrev ChallengeSampler :=
  (q : I.Query) → QueryImpl (challengeSpec plainSig (FC.openSpec q)) ProbComp

/-- Sample fresh challenges with the uniform sampler from `Interaction.challengeQueryImpl`
for each opening protocol. -/
def ChallengeSampler.uniform [∀ q c, SampleableType (challengeSpec plainSig (FC.openSpec q) c)] :
    FC.ChallengeSampler :=
  fun q => Interaction.challengeQueryImpl plainSig (FC.openSpec q)

/-- Run the opening interaction for the query `q` and return the verifier's decision on
`stmt` as a computation that has not run yet. The prover interacts with the sampler, whose
challenges `chal q` draws with private coins. -/
def interact (chal : FC.ChallengeSampler) (q : I.Query) (stmt : FC.PP × FC.Cm × I.spec q)
    (P : Prover plainSig (unifSpec + ambient) (FC.openSpec q) (fun _ => PUnit)) :
    OracleComp (unifSpec + ambient) (OracleComp (unifSpec + ambient) Bool) :=
  (fun r => Option.isSome <$>
      ((FC.verifier q).liftAmbient.decide stmt (Transcript.path r.1) (toPlainView _ r.1)).run) <$>
    TwoParty.Lens.run (FC.openSpec q) P
      (sampler plainSig (FC.openSpec q) fun c => liftComp (chal q c) (unifSpec + ambient))

/-! ### Correctness -/

/-- A data chooser sees the public parameters and returns data and a continuation. The
continuation sees the public commitment and chooses the query. -/
abbrev DataChooser :=
  FC.PP → OracleComp (unifSpec + ambient) (Data × (FC.Cm → OracleComp (unifSpec + ambient) I.Query))

/-- The chooser supplies data after setup and chooses the query after seeing the commitment.
The game returns the verifier's decision on the honest opening. -/
def correctnessGame (chal : FC.ChallengeSampler) (chooser : FC.DataChooser) :
    OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let (d, next) ← chooser pp
  let (cm, aux) ← FC.commit pp d
  let q ← next cm
  let r := I.answer d q
  let decision ← FC.interact chal q (pp, cm, r) (FC.prover q pp cm r d aux)
  decision

/-- Run the correctness game with initial state sampled by `init` and ambient handler `impl`. -/
def correctnessExperiment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler)
    (chooser : FC.DataChooser) : ProbComp Bool :=
  runGame init impl (FC.correctnessGame chal chooser)

/-- For each chooser in `Adv`, the verifier accepts the honest evaluation opening with
probability at least `1 - ε` ([KZG10] Definition 5, evaluation clause). -/
def Correctness {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (Adv : Set FC.DataChooser) (ε : ℝ≥0∞) : Prop :=
  ∀ chooser ∈ Adv, 1 - ε ≤ Pr{let b ← FC.correctnessExperiment init impl chal chooser}[b = true]

/-! ### Fixed-data correctness -/

/-- An adaptive query chooser sees the public parameters and the commitment. -/
abbrev QueryChooser := FC.PP → FC.Cm → OracleComp (unifSpec + ambient) I.Query

/-- The committer uses the fixed data `d`. After seeing the public parameters and the
commitment, the chooser picks a query. The game returns the verifier's decision on the honest
opening. -/
def fixedDataCorrectnessGame (chal : FC.ChallengeSampler) (d : Data) (chooser : FC.QueryChooser) :
    OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let ca ← FC.commit pp d
  let q ← chooser pp ca.1
  let decision ← FC.interact chal q (pp, ca.1, I.answer d q)
    (FC.prover q pp ca.1 (I.answer d q) d ca.2)
  decision

/-- For every fixed data value and each query chooser in `Adv`, the verifier accepts the honest
opening with probability at least `1 - ε`. -/
def FixedDataCorrectness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (Adv : Set FC.QueryChooser) (ε : ℝ≥0∞) : Prop :=
  ∀ d : Data, ∀ chooser ∈ Adv,
    1 - ε ≤ Pr{let b ← runGame init impl (FC.fixedDataCorrectnessGame chal d chooser)}[b = true]

/-- Embed a fixed data value and a query chooser into the adaptive chooser class. -/
def fixed (d : Data) (chooser : FC.QueryChooser) : FC.DataChooser :=
  fun pp => pure (d, chooser pp)

/-- The correctness game with an embedded chooser runs the fixed-data game. -/
theorem correctnessGame_fixed (chal : FC.ChallengeSampler) (d : Data)
    (chooser : FC.QueryChooser) :
    FC.correctnessGame chal (FC.fixed d chooser) = FC.fixedDataCorrectnessGame chal d chooser := by
  simp [correctnessGame, fixed, fixedDataCorrectnessGame]

variable {FC} in
/-- Adaptive correctness implies fixed-data correctness when the adaptive class contains
every embedding of the fixed-data class. -/
theorem Correctness.toFixedData {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl ambient (StateT σ ProbComp)} {chal : FC.ChallengeSampler}
    {D : Set FC.DataChooser} {Q : Set FC.QueryChooser} {ε : ℝ≥0∞}
    (ok : FC.Correctness init impl chal D ε) (incl : ∀ d, ∀ a ∈ Q, FC.fixed d a ∈ D) :
    FC.FixedDataCorrectness init impl chal Q ε := by
  intro d a ha
  simpa only [correctnessExperiment, correctnessGame_fixed] using ok (FC.fixed d a) (incl d a ha)

/-! ### Fixed-claim binding -/

/-- No data is consistent with all claims `(qᵢ, rᵢ)`, as a Boolean. It is decided
classically. -/
noncomputable def noConsistentData {L : ℕ} (claims : Fin L → (q : I.Query) × I.spec q) : Bool :=
  @decide (¬ ∃ d : Data, ∀ i, I.answer d (claims i).1 = (claims i).2)
    (Classical.propDecidable _)

theorem noConsistentData_eq_true_iff {L : ℕ} (claims : Fin L → (q : I.Query) × I.spec q) :
    noConsistentData claims = true ↔ ¬ ∃ d : Data, ∀ i, I.answer d (claims i).1 = (claims i).2 :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- A claim for fixed-claim binding consists of a query `q`, a claimed answer `r` and an opening
prover for `q`. -/
abbrev Claim :=
  (q : I.Query) × I.spec q × Prover plainSig (unifSpec + ambient) (FC.openSpec q) (fun _ => PUnit)

/-- The adversary sees the public parameters and fixes its commitment, all `L` claims and all
opening provers before any opening runs. -/
abbrev FixedClaimAdversary (L : ℕ) :=
  FC.PP → OracleComp (unifSpec + ambient) (FC.Cm × (Fin L → FC.Claim))

/-- The adversary fixes all claims and provers before any opening runs. The game returns
`true` if the verifier accepts every opening and no data agrees with all claims.
For one-message openings, which have no challenges, this is [CGKY25] Definition 3.17.
For interactive openings it is weaker than the joint game planned for a later PR. -/
noncomputable def fixedClaimBindingGame (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FixedClaimAdversary L) : OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let out ← A pp
  let decisions ← Fin.mOfFn L fun i =>
    FC.interact chal (out.2 i).1 (pp, out.1, (out.2 i).2.1) (out.2 i).2.2
  let verdicts ← Fin.mOfFn L decisions
  return (decide (∀ i, verdicts i = true) &&
    noConsistentData fun i => ⟨(out.2 i).1, (out.2 i).2.1⟩)

/-- Run the fixed-claim binding game with initial state sampled by `init` and ambient handler
`impl`. -/
noncomputable def fixedClaimBindingExperiment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FixedClaimAdversary L) : ProbComp Bool :=
  runGame init impl (FC.fixedClaimBindingGame chal L A)

/-- The probability that the adversary wins the fixed-claim binding experiment. -/
noncomputable def fixedClaimBindingAdvantage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FixedClaimAdversary L) : ℝ≥0∞ :=
  Pr{let b ← FC.fixedClaimBindingExperiment init impl chal L A}[b = true]

/-- Every adversary in `Adv` has fixed-claim binding advantage at most `ε`.
The adversary fixes all claims and provers before any opening runs. For one-message openings,
which have no challenges, the game is [CGKY25] Definition 3.17. For interactive openings it is
weaker than the joint game planned for a later PR. -/
def FixedClaimBinding {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (L : ℕ) (Adv : Set (FC.FixedClaimAdversary L))
    (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ Adv, FC.fixedClaimBindingAdvantage init impl chal L A ≤ ε

end FunctionalCommitment
