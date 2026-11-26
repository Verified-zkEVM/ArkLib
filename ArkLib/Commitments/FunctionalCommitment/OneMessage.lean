/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.FunctionalCommitment.Security

/-!
# Functional commitments with one-message openings

Most functional commitments open with a single proof: KZG sends one group element and a Merkle
tree sends one authentication path. `FunctionalCommitment.oneMessage` builds a functional
commitment from
* `setup` and `commit`;
* a proof type `Proof q` for each query `q`;
* an honest proof algorithm `prove pp cm d aux q`, with private coins;
* a check `check pp cm q r π : OracleComp ambient Bool`, which may query the shared oracle.

The opening protocol for `q` is `oneMessageSpec (Proof q)`: the prover sends one proof, and the
verifier accepts when `check` returns `true`.

One-message openings have no challenges, so fixed-claim binding is the plain game of [CGKY25]
Definition 3.17. The adversary fixes its commitment `cm` and all claims and proofs
`(qᵢ, rᵢ, πᵢ)` before any opening runs. The adversary wins when `check` accepts every claim
and no data agrees with all claimed answers (`plainFixedClaimBindingGame`).
`ofPlainAdversary` and `toPlainAdversary` convert the adversaries and preserve the game.

## Main statements

* `FunctionalCommitment.fixedClaimBindingGame_oneMessage` identifies the fixed-claim game of
  `oneMessage` against `A` with the plain game against `toPlainAdversary A`.
* `FunctionalCommitment.fixedClaimBindingGame_ofPlainAdversary` identifies the fixed-claim game
  of `oneMessage` against `ofPlainAdversary B` with the plain game against `B`.
* `FunctionalCommitment.correctnessGame_oneMessage` expands the adaptive correctness game into
  setup, data choice, commitment, query choice, proof and check.
* `FunctionalCommitment.correctness_oneMessage` shows that if every possible result of `check`
  on an honest proof is `true`, then `oneMessage` is correct with error `0` for every ambient
  implementation and every chooser.

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

/-! ### Dependent sequencing -/

section Sequencing

variable {m : Type → Type} [Monad m]

/-- Run a `Fin n`-indexed family of computations with index-dependent result types in index order,
and collect the results as a dependent function. -/
def piMOfFn : (n : ℕ) → {β : Fin n → Type} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0, _, _ => pure fun i => i.elim0
  | n + 1, _, f => do
    let a ← f 0
    let rest ← piMOfFn n fun i => f i.succ
    pure (Fin.cons a rest)

/-- Mapping each component of a dependent family and sequencing is sequencing the dependent family
and mapping its result. -/
theorem mOfFn_map_eq_map_piMOfFn [LawfulMonad m] {α : Type} :
    (n : ℕ) → {β : Fin n → Type} → (f : (i : Fin n) → m (β i)) → (g : (i : Fin n) → β i → α) →
    Fin.mOfFn n (fun i => g i <$> f i) = (fun v i => g i (v i)) <$> piMOfFn n f
  | 0, _, _, _ => by
    simp only [Fin.mOfFn_zero, piMOfFn, LawfulApplicative.map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, _, f, g => by
    rw [Fin.mOfFn_succ, mOfFn_map_eq_map_piMOfFn n (fun i => f i.succ) (fun i => g i.succ)]
    simp only [piMOfFn, bind_map_left, _root_.map_bind, LawfulApplicative.map_pure]
    refine bind_congr fun a => bind_congr fun rest => ?_
    congr 1
    funext i
    cases i using Fin.cases <;> simp

/-- Sequencing pure computations returns the family of their values. -/
theorem piMOfFn_pure [LawfulMonad m] :
    (n : ℕ) → {β : Fin n → Type} → (f : (i : Fin n) → β i) →
    piMOfFn n (fun i => (pure (f i) : m (β i))) = pure f
  | 0, _, f => by
    simp only [piMOfFn]
    congr 1
    funext i
    exact i.elim0
  | n + 1, _, f => by
    simp only [piMOfFn, LawfulMonad.pure_bind]
    rw [piMOfFn_pure n (fun i => f i.succ), LawfulMonad.pure_bind]
    exact congrArg pure (Fin.cons_self_tail f)

end Sequencing

/-! ### One-message protocols -/

/-- The protocol with one prover message of type `X`. -/
abbrev oneMessageSpec (X : Type) : Protocol := .liftBind (.message X) (fun _ => .pure ⟨⟩)

section Protocol

variable {κ : Type} {spec : OracleSpec.{0, 0} κ} {X : Type}

/-- The prover that computes its message with `prove`, sends it and does nothing at the leaf. -/
def oneMessageProver (prove : OracleComp spec X) :
    Prover plainSig spec (oneMessageSpec X) (fun _ => PUnit) :=
  (fun x => (⟨x, pure ⟨⟩⟩ : (_ : X) × OracleComp spec PUnit)) <$> prove

/-- Run a one-message prover through its message slot and its leaf, and return its message. -/
def oneMessageProof (P : Prover plainSig spec (oneMessageSpec X) (fun _ => PUnit)) :
    OracleComp spec X :=
  (P : OracleComp spec ((_ : X) × OracleComp spec PUnit)) >>= fun v =>
    v.2 >>= fun _ => pure v.1

/-- The message of `oneMessageProver prove` is computed by `prove`. -/
@[simp]
theorem oneMessageProof_oneMessageProver (prove : OracleComp spec X) :
    oneMessageProof (oneMessageProver prove) = prove := by
  change ((fun x => (⟨x, pure ⟨⟩⟩ : (_ : X) × OracleComp spec PUnit)) <$> prove) >>=
    (fun v => v.2 >>= fun _ => pure v.1) = prove
  simp only [bind_map_left, LawfulMonad.pure_bind, _root_.bind_pure]

/-- Running a one-message protocol against the sampler runs the prover's message slot, then its
leaf, and draws no challenge. -/
theorem run_oneMessageSpec_bind {β : Type}
    (P : Prover plainSig spec (oneMessageSpec X) (fun _ => PUnit))
    (draw : (c : ChallengeNode plainSig (oneMessageSpec X)) →
      OracleComp spec (challengeSpec plainSig (oneMessageSpec X) c))
    (g : ((_ : Transcript plainSig (oneMessageSpec X)) × PUnit × Unit) → OracleComp spec β) :
    (TwoParty.Lens.run (oneMessageSpec X) P (sampler plainSig (oneMessageSpec X) draw) >>= g) =
      ((P : OracleComp spec ((_ : X) × OracleComp spec PUnit)) >>= fun v =>
        v.2 >>= fun o => g ⟨⟨v.1, ⟨⟩⟩, o, ⟨⟩⟩) := by
  refine (run_sampler_sender (l := plainSig) (a := .message X) (next := fun _ => .pure ⟨⟩) rfl
    P draw g).trans ?_
  refine bind_congr fun v => ?_
  erw [TwoParty.Lens.run_done]
  simp only [bind_assoc, LawfulMonad.pure_bind]
  rfl

end Protocol

variable {ι : Type} {ambient : OracleSpec.{0, 0} ι} {Data : Type} {I : OracleInterface Data}
variable {PP Cm Aux : Type} {Proof : I.Query → Type}

/-- The verifier that reads the proof from the message and accepts when `check` returns
`true`. -/
def oneMessageVerifier
    (check : PP → Cm → (q : I.Query) → I.spec q → Proof q → OracleComp ambient Bool)
    (q : I.Query) :
    Verifier ambient (oneMessageSpec (Proof q)) (PP × Cm × I.spec q) (fun _ => PUnit) where
  decide stmt p _ := OptionT.mk
    ((fun b => if b then some PUnit.unit else none) <$> check stmt.1 stmt.2.1 q stmt.2.2 p.1)

/-- The functional commitment whose opening for `q` is one proof of type `Proof q`, computed by
`prove` and checked by `check`. It is reducible so that `(oneMessage ...).PP` unfolds to `PP`
when lemmas about `oneMessage` rewrite. -/
abbrev oneMessage (setup : OracleComp (unifSpec + ambient) PP)
    (commit : PP → Data → OracleComp (unifSpec + ambient) (Cm × Aux))
    (prove : PP → Cm → Data → Aux → (q : I.Query) → OracleComp (unifSpec + ambient) (Proof q))
    (check : PP → Cm → (q : I.Query) → I.spec q → Proof q → OracleComp ambient Bool) :
    FunctionalCommitment ambient Data I where
  PP := PP
  Cm := Cm
  Aux := Aux
  setup := setup
  commit := commit
  openSpec q := oneMessageSpec (Proof q)
  prover q pp cm _ d aux := oneMessageProver (prove pp cm d aux q)
  verifier q := oneMessageVerifier check q

variable (setup : OracleComp (unifSpec + ambient) PP)
  (commit : PP → Data → OracleComp (unifSpec + ambient) (Cm × Aux))
  (prove : PP → Cm → Data → Aux → (q : I.Query) → OracleComp (unifSpec + ambient) (Proof q))
  (check : PP → Cm → (q : I.Query) → I.spec q → Proof q → OracleComp ambient Bool)

/-- An opening interaction of `oneMessage` runs the prover to its proof `π`, and its decision
runs `check` on `π`. -/
theorem interact_oneMessage (chal : (oneMessage setup commit prove check).ChallengeSampler)
    (q : I.Query) (stmt : PP × Cm × I.spec q)
    (P : Prover plainSig (unifSpec + ambient) (oneMessageSpec (Proof q)) (fun _ => PUnit)) :
    (oneMessage setup commit prove check).interact chal q stmt P =
      (fun π => liftComp (check stmt.1 stmt.2.1 q stmt.2.2 π) (unifSpec + ambient)) <$>
        oneMessageProof P := by
  unfold interact
  rw [map_eq_bind_pure_comp]
  refine (run_oneMessageSpec_bind _ _ _).trans ?_
  simp only [oneMessageProof, _root_.map_bind, LawfulApplicative.map_pure, Function.comp]
  refine bind_congr fun v => bind_congr fun o => ?_
  congr 1
  change Option.isSome <$> liftComp ((fun b : Bool => if b then some PUnit.unit else none) <$>
    check stmt.1 stmt.2.1 q stmt.2.2 v.1) (unifSpec + ambient) = _
  rw [liftComp_map, Functor.map_map]
  refine (congrArg (· <$> _) ?_).trans (LawfulFunctor.id_map _)
  funext b
  cases b <;> rfl

/-! ### Fixed-claim binding -/

variable (ambient PP Cm Proof) in
/-- The plain adversary sees the public parameters and fixes the commitment, all `L` claims and
their proofs before any opening runs. -/
abbrev PlainAdversary (L : ℕ) :=
  PP → OracleComp (unifSpec + ambient) (Cm × (Fin L → (q : I.Query) × I.spec q × Proof q))

variable (ambient PP Cm Proof) in
/-- The fixed-claim adversary against `oneMessage` fixes every claim and one-message prover
before any opening runs. -/
abbrev OneMessageAdversary (L : ℕ) :=
  PP → OracleComp (unifSpec + ambient) (Cm × (Fin L → (q : I.Query) × I.spec q ×
    Prover plainSig (unifSpec + ambient) (oneMessageSpec (Proof q)) (fun _ => PUnit)))

/-- The plain game implements [CGKY25] Definition 3.17 for one-message openings without
challenges. The adversary fixes the commitment and all claims and proofs before the game runs
`check`. It wins if `check` accepts every claim and no data agrees with all claims. -/
noncomputable def plainFixedClaimBindingGame (L : ℕ) (B : PlainAdversary ambient PP Cm Proof L) :
    OracleComp (unifSpec + ambient) Bool := do
  let pp ← setup
  let out ← B pp
  let verdicts ← Fin.mOfFn L fun i =>
    liftComp (check pp out.1 (out.2 i).1 (out.2 i).2.1 (out.2 i).2.2) (unifSpec + ambient)
  return (decide (∀ i, verdicts i = true) &&
    noConsistentData fun i => ⟨(out.2 i).1, (out.2 i).2.1⟩)

/-- The probability that `B` wins the plain fixed-claim game run with `init` and `impl`. -/
noncomputable def plainFixedClaimBindingAdvantage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp)) (L : ℕ)
    (B : PlainAdversary ambient PP Cm Proof L) : ℝ≥0∞ :=
  Pr{let b ← runGame init impl (plainFixedClaimBindingGame setup check L B)}[b = true]

/-- Turn a plain adversary into an adversary against `oneMessage`: each opening prover sends the
plain adversary's proof. -/
def ofPlainAdversary {L : ℕ} (B : PlainAdversary ambient PP Cm Proof L) :
    OneMessageAdversary ambient PP Cm Proof L := fun pp =>
  (fun out => (out.1, fun i => ⟨(out.2 i).1, (out.2 i).2.1, oneMessageProver (pure (out.2 i).2.2)⟩))
    <$> B pp

/-- Turn an adversary against `oneMessage` into a plain adversary: it runs the adversary, then
runs every opening prover in index order to its proof. -/
def toPlainAdversary {L : ℕ} (A : OneMessageAdversary ambient PP Cm Proof L) :
    PlainAdversary ambient PP Cm Proof L := fun pp => do
  let out ← A pp
  let proofs ← piMOfFn L fun i => oneMessageProof (out.2 i).2.2
  pure (out.1, fun i => ⟨(out.2 i).1, (out.2 i).2.1, proofs i⟩)

/-- Converting a plain adversary to a `oneMessage` adversary and back gives the plain adversary
again. -/
theorem toPlainAdversary_ofPlainAdversary {L : ℕ} (B : PlainAdversary ambient PP Cm Proof L) :
    toPlainAdversary (ofPlainAdversary B) = B := by
  funext pp
  simp only [toPlainAdversary, ofPlainAdversary, bind_map_left, oneMessageProof_oneMessageProver,
    piMOfFn_pure, LawfulMonad.pure_bind]
  exact _root_.bind_pure _

/-- The fixed-claim binding game of `oneMessage` against `A` is the
plain game against `toPlainAdversary A`. -/
theorem fixedClaimBindingGame_oneMessage
    (chal : (oneMessage setup commit prove check).ChallengeSampler) (L : ℕ)
    (A : OneMessageAdversary ambient PP Cm Proof L) :
    (oneMessage setup commit prove check).fixedClaimBindingGame chal L A =
      plainFixedClaimBindingGame setup check L (toPlainAdversary A) := by
  simp only [fixedClaimBindingGame, plainFixedClaimBindingGame, toPlainAdversary, bind_assoc]
  refine bind_congr fun pp => bind_congr fun out => ?_
  rw [show (Fin.mOfFn L fun i => (oneMessage setup commit prove check).interact chal (out.2 i).1
      (pp, out.1, (out.2 i).2.1) (out.2 i).2.2) = Fin.mOfFn L fun i =>
        (fun π => liftComp (check pp out.1 (out.2 i).1 (out.2 i).2.1 π) (unifSpec + ambient)) <$>
          oneMessageProof (out.2 i).2.2 from
      congrArg _ (funext fun i => interact_oneMessage setup commit prove check chal _ _ _),
    mOfFn_map_eq_map_piMOfFn, bind_map_left]
  simp only [LawfulMonad.pure_bind]

/-- The fixed-claim binding game of `oneMessage` against
`ofPlainAdversary B` is the plain game against `B`. -/
theorem fixedClaimBindingGame_ofPlainAdversary
    (chal : (oneMessage setup commit prove check).ChallengeSampler) (L : ℕ)
    (B : PlainAdversary ambient PP Cm Proof L) :
    (oneMessage setup commit prove check).fixedClaimBindingGame chal L (ofPlainAdversary B) =
      plainFixedClaimBindingGame setup check L B := by
  exact (fixedClaimBindingGame_oneMessage setup commit prove check chal L _).trans
    (congrArg _ (toPlainAdversary_ofPlainAdversary B))

/-- The fixed-claim binding advantage of `A` against `oneMessage` equals the plain advantage of
`toPlainAdversary A`. -/
theorem fixedClaimBindingAdvantage_oneMessage {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : (oneMessage setup commit prove check).ChallengeSampler) (L : ℕ)
    (A : OneMessageAdversary ambient PP Cm Proof L) :
    (oneMessage setup commit prove check).fixedClaimBindingAdvantage init impl chal L A =
      plainFixedClaimBindingAdvantage setup check init impl L (toPlainAdversary A) := by
  simp only [fixedClaimBindingAdvantage, fixedClaimBindingExperiment,
    plainFixedClaimBindingAdvantage, fixedClaimBindingGame_oneMessage]

/-- The fixed-claim binding advantage of `ofPlainAdversary B` against `oneMessage` equals the plain
advantage of `B`. -/
theorem fixedClaimBindingAdvantage_ofPlainAdversary {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : (oneMessage setup commit prove check).ChallengeSampler) (L : ℕ)
    (B : PlainAdversary ambient PP Cm Proof L) :
    (oneMessage setup commit prove check).fixedClaimBindingAdvantage init impl chal L
        (ofPlainAdversary B) =
      plainFixedClaimBindingAdvantage setup check init impl L B := by
  simp only [fixedClaimBindingAdvantage, fixedClaimBindingExperiment,
    plainFixedClaimBindingAdvantage]
  rw [fixedClaimBindingGame_ofPlainAdversary]

/-! ### Correctness -/

/-- The chooser selects the data after setup and the query after commitment. The game
generates the honest proof for that query and runs the check. -/
def oneMessageCorrectnessGame (chooser : (oneMessage setup commit prove check).DataChooser) :
    OracleComp (unifSpec + ambient) Bool := do
  let pp ← setup
  let (d, next) ← chooser pp
  let (cm, aux) ← commit pp d
  let q ← next cm
  let π ← prove pp cm d aux q
  liftComp (check pp cm q (I.answer d q) π) (unifSpec + ambient)

/-- The correctness game of `oneMessage` is `oneMessageCorrectnessGame`. -/
theorem correctnessGame_oneMessage
    (chal : (oneMessage setup commit prove check).ChallengeSampler)
    (chooser : (oneMessage setup commit prove check).DataChooser) :
    (oneMessage setup commit prove check).correctnessGame chal chooser =
      oneMessageCorrectnessGame setup commit prove check chooser := by
  simp only [correctnessGame, oneMessageCorrectnessGame]
  refine bind_congr fun pp => bind_congr fun ⟨d, _⟩ => bind_congr fun ⟨cm, aux⟩ =>
    bind_congr fun q => ?_
  have h := interact_oneMessage setup commit prove check chal q (pp, cm, I.answer d q)
    (oneMessageProver (prove pp cm d aux q))
  rw [oneMessageProof_oneMessageProver] at h
  exact (congrArg (· >>= id) h).trans (bind_map_left _ _ _)

/-- If `check` always accepts an honest proof of an honest commitment, then `oneMessage`
satisfies adaptive correctness with error `0` ([KZG10] Definition 5, evaluation clause). The
result holds for every initial state computation, ambient implementation, challenge sampler
and set of data choosers. -/
theorem correctness_oneMessage
    (h : ∀ pp ∈ support setup, ∀ d : Data, ∀ ca ∈ support (commit pp d), ∀ q : I.Query,
      ∀ π ∈ support (prove pp ca.1 d ca.2 q),
      ∀ b ∈ support (check pp ca.1 q (I.answer d q) π), b = true)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (chal : (oneMessage setup commit prove check).ChallengeSampler)
    (Adv : Set (oneMessage setup commit prove check).DataChooser) :
    (oneMessage setup commit prove check).Correctness init impl chal Adv 0 := by
  intro chooser _
  rw [tsub_zero]
  refine le_of_eq ((prEvent_eq_one_iff _ _).2 fun b hb => ?_).symm
  have hb : b ∈ support (oneMessageCorrectnessGame setup commit prove check chooser) := by
    rw [← correctnessGame_oneMessage setup commit prove check chal]
    exact support_runGame_subset init impl _ hb
  simp only [oneMessageCorrectnessGame, mem_support_bind_iff, support_liftComp] at hb
  obtain ⟨pp, hpp, ⟨d, _⟩, -, ca, hca, q, -, π, hπ, hb⟩ := hb
  exact h pp hpp d ca hca q π hπ b hb

end FunctionalCommitment
