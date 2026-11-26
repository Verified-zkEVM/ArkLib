/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.Basic
public import ToMathlib.Control.Monad.Fold
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Security games for functional commitments

This file states correctness and `L`-claim function binding of a functional commitment as games
with setup. Both games are adaptive: the adversary sees the public parameters before it chooses
the query or the claims.

## Running a game

A game is a program `OracleComp (unifSpec + ambient) Bool`. `runGame init impl` interprets it in
`StateT σ ProbComp`: `unifSpec` queries pass through to `ProbComp` and `ambient` queries go to the
stateful implementation `impl`, whose initial state `init` samples. This is the interpretation of
`Interaction.experiment` with the private coins in the left summand. The state is shared by every
phase of the game, so a random oracle answers the commit phase and the opening phase
consistently.

An opening runs with `interact`: the prover interacts with the sampler, which draws each
challenge with the challenge sampler `chal q` (for example `Interaction.challengeQueryImpl`).
`interact` returns the verifier's decision as a computation that has not run yet. The
function-binding game first runs every opening interaction and then every decision. With
one-message openings this is the order of the non-interactive game of [CGKY25]: the adversary
outputs all proofs, and then the verifier checks them.

## Games

* `correctnessExperiment`: setup gives `pp`, the honest committer commits to `d`, an adaptive
  chooser picks the query `q` from `pp` and `cm`, and the honest prover opens `cm` to
  `I.answer d q`. `Correctness Adv ε` says that this run accepts with probability at least
  `1 - ε` for every `d` and every chooser in `Adv` ([KZG10] Def. 5).
* `functionBindingExperiment L`: setup gives `pp`, and the adversary returns a commitment `cm`,
  `L` claims `(qᵢ, rᵢ)` and `L` opening provers. The adversary wins when every opening is
  accepted and no `d : Data` has `I.answer d qᵢ = rᵢ` for all `i` ([CGKY25] Def. 3.17).
  `FunctionBinding L Adv ε` bounds the advantage of every adversary in `Adv` by `ε`.

The opening relation `Opens`, hiding, extractability and the state-restoration game with setup
are planned for later work.

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

/-- An adaptive query chooser sees the public parameters and the commitment. -/
abbrev QueryChooser := FC.PP → FC.Cm → OracleComp (unifSpec + ambient) I.Query

/-- The correctness game for data `d`: setup, honest commitment to `d`, a query chosen by
`chooser`, and the honest opening of `cm` to `I.answer d q`. It returns the verifier's
decision. -/
def correctnessGame (chal : FC.ChallengeSampler) (d : Data) (chooser : FC.QueryChooser) :
    OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let ca ← FC.commit pp d
  let q ← chooser pp ca.1
  let decision ← FC.interact chal q (pp, ca.1, I.answer d q)
    (FC.prover q pp ca.1 (I.answer d q) d ca.2)
  decision

/-- The correctness experiment: the correctness game run with `init` and `impl`. -/
def correctnessExperiment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (d : Data)
    (chooser : FC.QueryChooser) : ProbComp Bool :=
  runGame init impl (FC.correctnessGame chal d chooser)

/-- **Correctness.** For every data `d` and every chooser in `Adv`, the honest opening accepts
with probability at least `1 - ε`. -/
def Correctness {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (Adv : Set FC.QueryChooser) (ε : ℝ≥0∞) : Prop :=
  ∀ d : Data, ∀ chooser ∈ Adv,
    1 - ε ≤ Pr{let b ← FC.correctnessExperiment init impl chal d chooser}[b = true]

/-! ### Function binding -/

/-- No data is consistent with all claims `(qᵢ, rᵢ)`, as a Boolean. It is decided
classically. -/
noncomputable def noConsistentData {L : ℕ} (claims : Fin L → (q : I.Query) × I.spec q) : Bool :=
  @decide (¬ ∃ d : Data, ∀ i, I.answer d (claims i).1 = (claims i).2)
    (Classical.propDecidable _)

theorem noConsistentData_eq_true_iff {L : ℕ} (claims : Fin L → (q : I.Query) × I.spec q) :
    noConsistentData claims = true ↔ ¬ ∃ d : Data, ∀ i, I.answer d (claims i).1 = (claims i).2 :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- A function-binding claim: a query `q`, a claimed answer `r` and a malicious opening prover
for `q`. -/
abbrev Claim :=
  (q : I.Query) × I.spec q × Prover plainSig (unifSpec + ambient) (FC.openSpec q) (fun _ => PUnit)

/-- An `L`-claim function-binding adversary sees the public parameters and returns a commitment
and `L` claims with their opening provers. -/
abbrev FunctionBindingAdversary (L : ℕ) :=
  FC.PP → OracleComp (unifSpec + ambient) (FC.Cm × (Fin L → FC.Claim))

/-- The `L`-claim function-binding game. Setup gives `pp`, and the adversary returns `cm` and
the claims. The game runs every opening interaction, then every decision, and returns whether
every opening is accepted and no data is consistent with the claims. -/
noncomputable def functionBindingGame (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FunctionBindingAdversary L) : OracleComp (unifSpec + ambient) Bool := do
  let pp ← FC.setup
  let out ← A pp
  let decisions ← Fin.mOfFn L fun i =>
    FC.interact chal (out.2 i).1 (pp, out.1, (out.2 i).2.1) (out.2 i).2.2
  let verdicts ← Fin.mOfFn L decisions
  return (decide (∀ i, verdicts i = true) &&
    noConsistentData fun i => ⟨(out.2 i).1, (out.2 i).2.1⟩)

/-- The function-binding experiment: the function-binding game run with `init` and `impl`. -/
noncomputable def functionBindingExperiment {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FunctionBindingAdversary L) : ProbComp Bool :=
  runGame init impl (FC.functionBindingGame chal L A)

/-- The function-binding advantage of one adversary. -/
noncomputable def functionBindingAdvantage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (chal : FC.ChallengeSampler) (L : ℕ)
    (A : FC.FunctionBindingAdversary L) : ℝ≥0∞ :=
  Pr{let b ← FC.functionBindingExperiment init impl chal L A}[b = true]

/-- **`L`-claim function binding.** Every adversary in `Adv` has function-binding advantage at
most `ε`. -/
def FunctionBinding {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : FC.ChallengeSampler) (L : ℕ) (Adv : Set (FC.FunctionBindingAdversary L))
    (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ Adv, FC.functionBindingAdvantage init impl chal L A ≤ ε

end FunctionalCommitment
