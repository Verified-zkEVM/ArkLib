/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape

/-!
  # Committed scalar phase (generic commit-then-challenge CWSS shell)

  A recurring two-round shape: the prover **commits** to an opening, the verifier sends one
  **scalar challenge**, and the output statement retains both values. This file owns that shape
  once — protocol, anchored relation, escape event, and the extraction argument — so that each
  instantiation supplies only its challenge-local predicate and one recovery theorem.

  This is deliberately *not* a ring-switching module. It is the protocol/security seam that
  quotient-evaluation ring switches such as [HMZ25] (Hachi [NOZ26] Figure 4 / Lemma 9) happen to
  have, but nothing here mentions rings, polynomials, or packing: the ingredients are a
  `BindingCommitment` and a `checkAt` predicate. The basis-packing ring switch of DP24 and Hachi §3
  is a different construction (`ProofSystem/RingSwitching/Packing/`); with this file it shares the
  `ScalarRound.pSpecScalar` wire format (this file's verifier is the check-free case of the
  check-then-update round shape on that wire — `ProofSystem/RingSwitching/RoundVerifiers.lean`).

  ## Where the binding break lives

  Commitments of interest here are only binding on **short** openings, so a committed scalar phase
  cannot promise a `relIn`-witness unconditionally: an adversary who breaks the commitment gets to
  choose the branch openings. In this development that failure is an **escape event** on the
  transcript tree (`ChallengeTree.EscapeEvent`), never a value the extractor returns. Concretely
  `escLocal` says *"two of the tree's branch openings are a short collision of the round-0
  commitment"*, and the certificate `coordinateWiseSpecialSoundWithEscape` concludes
  `escEvent stmt tree ∨ extraction succeeds on every valid leaf witnessing`.

  Making this an event rather than an extractor output is forced: `BindingCommitment.Collision` is
  nonempty for every compressing commitment, so a certificate whose escape branch were an
  extractor *output* would be dischargeable by a constant function and carry no content. Events on
  `(stmt, tree)` are the only objects a certificate author cannot choose. Per the
  `ChallengeTree.EscapeEvent` contract, `escLocal` reads only the commitment and the branch
  responses; the ambient `escEventScalar` pins those responses to the **output** relation, which is
  what keeps the event tight.

  ## Contents

  * `BindingCommitment W Short` — a deterministic commitment together with the shortness regime its
    binding guarantee is restricted to, plus its **short-collision set**
    `BindingCommitment.Collision` (the hardness target the escape event points at).
  * `CommittedScalar.Statement`, `CommittedScalar.rel` — the output statement
    `Stmt × TCom × Challenge` and the anchored relation (commitment consistency + `checkAt` +
    `Short`).
  * `CommittedScalar.verifier` / `CommittedScalar.prover` — the pure statement-extending verifier
    and the honest prover shell (the commitment is derived from the output opening by construction).
  * `CommittedScalar.mkWitness` / `CommittedScalar.escLocal` — the plain per-family assembler and
    the local escape event; `CommittedScalar.escEvent` / `CommittedScalar.treeExtractor` are their
    tree-level forms, both via `ScalarRound`.
  * `CommittedScalar.mkWitness_mem` — the disjunctive correctness theorem, parameterized by the
    single instance-specific `recover` hypothesis (one common short opening satisfying `checkAt` at
    `k` pairwise-distinct challenges recovers the input relation).
  * `CommittedScalar.verifierPureForm` — the verifier's purity as data, which the package carries
    so that composition reads the seam statement without choice.
  * `CommittedScalar.coordinateWiseSpecialSoundWithEscape` / `CommittedScalar.package` — the
    generic certificate at `scalarStructure k` and its `EscapeCWSSPackage` bundle, ready for `▷`
    composition against packages of any of the four kinds.

  ## Consumers

  * The generic HMZ25 quotient-evaluation lift (`ProofSystem/RingSwitching/Lift/Reduction.lean`),
    and through it Hachi's ring switch (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`)
    at `k = 2d`.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace CoordinateWise

/-- A deterministic commitment together with the shortness regime `Short` its binding guarantee is
restricted to.

Lemma-9-style extraction needs nothing but the commitment map itself: weak binding enters as the
*escape event* `CommittedScalar.escLocal`, whose hardness target is the short-collision set
`Collision` below. Exact binding is the degenerate case where `Collision` is empty. -/
structure BindingCommitment (W : Type) (Short : W → Prop) where
  /-- The commitment space (the wire type of the round-0 prover message). -/
  TCom : Type
  /-- The (deterministic) commitment map. -/
  com : W → TCom

namespace BindingCommitment

variable {W : Type} {Short : W → Prop}

/-- The **short-collision set** of the commitment: pairs of distinct `Short` openings that collide.

For an Ajtai-style commitment an element of this set is a Module-SIS solution for the fixed key
([NOZ26] Lemma 7), so it is the hardness target a committed scalar phase's escape event points at.
Taking `Short` from the structure's own index keeps an event from being stated at a mismatched
shortness regime. Note this set is nonempty for every compressing commitment, which is exactly why
exhibiting a member has to be an *event on the transcript tree* rather than an extractor output. -/
def Collision (K : BindingCommitment W Short) : Set (W × W) :=
  {p | p.1 ≠ p.2 ∧ K.com p.1 = K.com p.2 ∧ Short p.1 ∧ Short p.2}

/-- Membership in the short-collision set, unfolded. -/
theorem mem_Collision (K : BindingCommitment W Short) (w w' : W) :
    (w, w') ∈ K.Collision ↔
      w ≠ w' ∧ K.com w = K.com w' ∧ Short w ∧ Short w' := Iff.rfl

end BindingCommitment

namespace CommittedScalar

open OracleComp OracleSpec ProtocolSpec ScalarRound

variable {Stmt W Challenge WitIn : Type} {Short : W → Prop}

/-- Output statement of a committed scalar phase: input statement, commitment, challenge. -/
abbrev Statement (Stmt TCom Challenge : Type) : Type := Stmt × TCom × Challenge

/-- The anchored output relation for a committed scalar phase.

The framework fixes commitment consistency and admissibility (`Short`); an instantiation supplies
only its challenge-local predicate `checkAt`. Soundness additionally requires a recovery theorem
from `k` distinct challenges, so `checkAt` cannot by itself certify a vacuous instance. -/
def rel (K : BindingCommitment W Short) (checkAt : Stmt → Challenge → W → Prop) :
    Set (Statement Stmt K.TCom Challenge × W) :=
  {p | K.com p.2 = p.1.2.1 ∧ checkAt p.1.1 p.1.2.2 p.2 ∧ Short p.2}

/-- Pure statement-extending verifier shared by committed scalar phases. -/
def verifier {ι : Type} {oSpec : OracleSpec ι} (K : BindingCommitment W Short) :
    Verifier oSpec Stmt (Statement Stmt K.TCom Challenge)
      (pSpecScalar K.TCom Challenge) where
  verify := fun stmt tr =>
    pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- Honest prover shell for a committed scalar phase.

The commitment is derived from `computeW`; the API cannot send a commitment unrelated to its
output opening. -/
def prover {ι : Type} {oSpec : OracleSpec ι} (K : BindingCommitment W Short)
    (computeW : Stmt → WitIn → W) :
    Prover oSpec Stmt WitIn (Statement Stmt K.TCom Challenge) W
      (pSpecScalar K.TCom Challenge) where
  PrvState
    | 0 => Stmt × WitIn
    | 1 => Stmt × WitIn
    | 2 => (Stmt × WitIn) × Challenge
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (K.com (computeW st.1 st.2), st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    let w := computeW stmt wit
    pure ((stmt, K.com w, c), w)

/-- The committed-scalar assembler: project the branch-`0` opening back to an input witness.

There is no case analysis to do. On families where the branches do **not** share an opening,
`escLocal` fires and the certificate's left disjunct carries the conclusion, so the choice of
branch `0` is soundness-irrelevant; on families that do share one, every branch gives the same
answer. -/
def mkWitness {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short) (project : W → WitIn)
    (_s : Stmt) (_t : K.TCom) (_fam : Fin k → Challenge) (resp : Fin k → W) : WitIn :=
  project (resp ⟨0, by omega⟩)

/-- **The committed-scalar escape event, local form** — the `escLocal` argument of
`ScalarRound.escEventScalar`: two of the tree's branch openings are a short collision of the
round-0 commitment `t`.

Against the `ChallengeTree.EscapeEvent` contract: the conjunct `(resp j, resp j') ∈ K.Collision` is
a binding break of the *fixed, statement-independent* key at **every** `(s, t, fam, resp)`,
including families no honest execution produces; and it mentions neither `relIn`, nor the extractor,
nor acceptance, nor the verifier, nor the sampling. It reads only `t` and the branch responses,
which the ambient `escEventScalar` pins to `rel K checkAt` — that pinning is what rules out the
statement-only event "some collision of this commitment exists" and makes the event tight. -/
def escLocal {k : ℕ} (K : BindingCommitment W Short) :
    Stmt → K.TCom → (Fin k → Challenge) → (Fin k → W) → Prop :=
  fun _ t _ resp => ∃ j j', (resp j, resp j') ∈ K.Collision ∧ K.com (resp j) = t

/-- The tree-level escape event of a committed scalar phase: `escLocal` transported along
`ScalarRound.escEventScalar`, whose per-branch validity is membership in the output relation (the
verifier is statement-extending). -/
def escEvent {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short)
    (checkAt : Stmt → Challenge → W → Prop) :
    ChallengeTree.EscapeEvent Stmt (pSpecScalar K.TCom Challenge)
      (CWSSStructure.toShape
        (scalarStructure (Msg := K.TCom) (C := Challenge) k hk)).arity :=
  ScalarRound.escEventScalar hk (rel K checkAt) (escLocal K)

/-- The committed-scalar named extractor: `mkWitness` transported along
`ScalarRound.treeExtractorScalar`, which reads the commitment and the `k` sibling challenges off
the tree through the same `readPre` / `readFam` the escape event uses, and the `k` branch openings
off the leaf witnessing.

Computable, and not parameterized by `checkAt`: the openings are supplied by the witnessing
rather than recovered by inverting `rel K checkAt`. -/
def treeExtractor {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short) (project : W → WitIn) :
    Extractor.TreeBased Stmt WitIn W (pSpecScalar K.TCom Challenge)
      (CWSSStructure.toShape
        (scalarStructure (Msg := K.TCom) (C := Challenge) k hk)).arity :=
  ScalarRound.treeExtractorScalar hk (mkWitness hk K project)

/-- **Correctness of the committed-scalar assembly**, parameterized by the only
construction-specific fact `recover`: one common short opening satisfying `checkAt` at `k` distinct
challenges recovers `relIn`.

Either two branches disagree — and then their openings are a short collision of the shared
commitment, so `escLocal` fires — or all branches agree and `recover` applies. Every conjunct
needed on the collision side is supplied by `rel` itself: `hresp` gives commitment agreement
(`K.com (resp j) = t`) and shortness for each branch. -/
theorem mkWitness_mem {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short) (project : W → WitIn)
    (checkAt : Stmt → Challenge → W → Prop) (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (s : Stmt) (t : K.TCom) (fam : Fin k → Challenge) (resp : Fin k → W)
    (hresp : ∀ j, ((s, t, fam j), resp j) ∈ rel K checkAt)
    (hinj : Function.Injective fam) :
    escLocal K s t fam resp ∨ (s, mkWitness hk K project s t fam resp) ∈ relIn := by
  classical
  letI : ∀ f g : Fin k → W, Decidable (∃ j, f j ≠ g j) :=
    fun _ _ => Classical.propDecidable _
  set first : Fin k := ⟨0, by omega⟩ with hfirst
  by_cases hcol : ∃ j, resp j ≠ resp first
  · obtain ⟨j, hj⟩ := hcol
    exact Or.inl ⟨j, first,
      ⟨hj, (hresp j).1.trans (hresp first).1.symm, (hresp j).2.2, (hresp first).2.2⟩,
      (hresp j).1⟩
  · push Not at hcol
    exact Or.inr (recover s (resp first) fam hinj
      (fun j => hcol j ▸ (hresp j).2.1) (hresp first).2.2)

/-- The committed-scalar verifier's purity **as data**: its verdict is the input statement extended
by the transcript's commitment and challenge. This is the `PureForm` the package carries, so that
composition can read the seam statement without `Classical.choice`. -/
def verifierPureForm {ι : Type} {oSpec : OracleSpec ι} (K : BindingCommitment W Short) :
    (verifier (oSpec := oSpec) (Stmt := Stmt) (Challenge := Challenge) K).PureForm where
  verify := fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)
  verify_eq := fun _ _ => rfl

/-- **Generic escape-threaded CWSS certificate for committed scalar phases.** All
protocol-independent extraction and tree reasoning is reused from `ScalarRound`; `recover` is the
instance's substantive algebra. -/
theorem coordinateWiseSpecialSoundWithEscape {ι : Type} {oSpec : OracleSpec ι}
    {σ : Type} {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short)
    (project : W → WitIn) (checkAt : Stmt → Challenge → W → Prop)
    (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl (scalarStructure k hk)
      (escEvent hk K checkAt) relIn (rel K checkAt)
      (verifier (oSpec := oSpec) K) (treeExtractor hk K project) :=
  ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar init impl hk
    (verifier K)
    (fun _ _ => rfl) relIn (rel K checkAt) (mkWitness hk K project) (escLocal K)
    (fun s t fam resp hbranch hinj =>
      mkWitness_mem hk K project checkAt relIn recover s t fam resp hbranch hinj)

/-- Bundled committed scalar phase, ready for CWSS composition.

This lands in the **pure, escape-aware** corner of the package lattice: the verifier is `pure (…)`
and never `failure`, so it is a valid left factor, while the commitment's escape event needs the
`esc` field. Escape-free neighbours compose against it for free through the universal `▷`
(`CWSSPackage.toEscape`), so no separate plain-`CWSSPackage` variant is needed — at an injective
`com` the event simply never fires. -/
def package {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short)
    (project : W → WitIn) (checkAt : Stmt → Challenge → W → Prop)
    (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    EscapeCWSSPackage init impl Stmt WitIn (Statement Stmt K.TCom Challenge) W
      (pSpecScalar K.TCom Challenge) where
  verifier := verifier K
  struct := scalarStructure k hk
  relIn := relIn
  relOut := rel K checkAt
  esc := escEvent hk K checkAt
  isPure := verifierPureForm K
  extractor := treeExtractor hk K project
  isCWSS := coordinateWiseSpecialSoundWithEscape hk K project checkAt relIn recover init impl

/-! ## Completeness of a committed scalar phase

The honest counterpart of `coordinateWiseSpecialSoundWithEscape`, owned here for the same reason:
the execution of the two-round commit-then-challenge shape is protocol-independent, so an
instantiation should supply only the two facts about its own `computeW` that the *relation*
`rel K checkAt` asks for — the challenge-local check at every challenge, and admissibility.
-/

section Completeness

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **The committed scalar phase as a protocol object**: the honest prover shell paired with the
statement-extending verifier. The verifier field is `verifier K`, the very verifier `package`
certifies, so the two security directions of an instantiated phase cannot drift apart. -/
def reduction (K : BindingCommitment W Short) (computeW : Stmt → WitIn → W) :
    Reduction oSpec Stmt WitIn (Statement Stmt K.TCom Challenge) W
      (pSpecScalar K.TCom Challenge) where
  prover := prover K computeW
  verifier := verifier K

section Execution

variable (K : BindingCommitment W Short) (computeW : Stmt → WitIn → W)

/-- **Honest execution of both rounds.** Running the prover shell to the last round appends the
commitment `K.com (computeW stmt wit)` (round 0, a message round that leaves the state untouched),
then draws the challenge `c` (round 1) and stores it, ending at the transcript `⟨K.com w, c⟩`
(`FullTranscript.mk2`) with state `((stmt, wit), c)`.

Proved by the two framework round-unfoldings rather than by induction — there are only two rounds.
`hdir` is `pSpecScalar.dir 1 = .V_to_P`, taken as a named argument rather than `rfl` so that the
round-1 challenge index stays type-correct at the transparency `rw` uses. The `Challenge`
ascription on `prover` is load-bearing too: the output statement is the only place that type
argument occurs, so without it the statement elaborates with an unassigned challenge type. -/
lemma prover_runToRound_last (stmt : Stmt) (wit : WitIn)
    (hdir : (pSpecScalar K.TCom Challenge).dir 1 = .V_to_P) :
    (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
        computeW).runToRound (Fin.last 2) stmt wit
      = (do
          let c ← (pSpecScalar K.TCom Challenge).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (K.com (computeW stmt wit)) c, ((stmt, wit), c))) := by
  have step2 : (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
        computeW).runToRound (Fin.last 2) stmt wit
      = (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
          computeW).processRound (1 : Fin 2)
          ((prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
            computeW).runToRound ((1 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (1 : Fin 2) stmt wit _
  have step1 : (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
        computeW).runToRound ((1 : Fin 2).castSucc) stmt wit
      = (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
          computeW).processRound (0 : Fin 2)
          ((prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
            computeW).runToRound ((0 : Fin 2).castSucc) stmt wit) :=
    Prover.runToRound_succ (0 : Fin 2) stmt wit _
  have step0 : (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K
        computeW).runToRound ((0 : Fin 2).castSucc) stmt wit
      = pure ((fun i => Fin.elim0 i), (stmt, wit)) := rfl
  refine step2.trans ?_
  rw [step1, step0, Prover.processRound_of_dir_eq_P_to_V (0 : Fin 2) rfl,
    Prover.processRound_of_dir_eq_V_to_P (1 : Fin 2) hdir]
  simp only [prover, liftM, monadLift, MonadLift.monadLift, OracleComp.liftComp_pure,
    monad_norm, FullTranscript.mk2_eq_snoc_snoc]
  rfl

/-- **The honest prover's run in closed form**: draw `c`, then emit the transcript `⟨K.com w, c⟩`,
the output statement `(stmt, K.com w, c)` and the opening `w = computeW stmt wit`. Everything about
the run is a function of the single challenge. -/
lemma prover_run_eq (stmt : Stmt) (wit : WitIn)
    (hdir : (pSpecScalar K.TCom Challenge).dir 1 = .V_to_P) :
    (prover (oSpec := oSpec) (WitIn := WitIn) (Challenge := Challenge) K computeW).run stmt wit
      = (do
          let c ← (pSpecScalar K.TCom Challenge).getChallenge ⟨1, hdir⟩
          pure (FullTranscript.mk2 (K.com (computeW stmt wit)) c,
            (stmt, K.com (computeW stmt wit), c), computeW stmt wit)) := by
  unfold Prover.run
  rw [prover_runToRound_last K computeW stmt wit hdir]
  simp only [prover, liftM, monadLift, MonadLift.monadLift]
  rfl

/-- **Honest-run characterization.** Every element of the support of an honest run is a success
determined by the drawn challenge alone: prover and verifier both output `(stmt, K.com w, c)`, and
the prover hands on the opening `w = computeW stmt wit`.

Failure is impossible because the only `OptionT` layer in `Reduction.run` comes from the verifier,
and `verifier` is a `pure` statement extension with no acceptance test — all the checks of a
committed scalar phase live in `rel K checkAt`. -/
lemma reduction_run_support (stmt : Stmt) (wit : WitIn)
    (hdir : (pSpecScalar K.TCom Challenge).dir 1 = .V_to_P) :
    ∀ x ∈ support ((reduction (oSpec := oSpec) (Challenge := Challenge) K computeW).run
        stmt wit).run,
      ∃ c : Challenge,
        x = some ((FullTranscript.mk2 (K.com (computeW stmt wit)) c,
              (stmt, K.com (computeW stmt wit), c), computeW stmt wit),
            (stmt, K.com (computeW stmt wit), c)) := by
  intro x hx
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨prOpt, hpr, hx⟩ := hx
  rw [show ((liftM (Prover.run stmt wit
        (reduction (oSpec := oSpec) (Challenge := Challenge) K computeW).prover) :
        OptionT (OracleComp _) _)).run
      = (Prover.run stmt wit
          (reduction (oSpec := oSpec) (Challenge := Challenge) K computeW).prover)
        >>= fun a => pure (some a) from rfl] at hpr
  rw [mem_support_bind_iff] at hpr
  obtain ⟨pr, hpr, hprOpt⟩ := hpr
  rw [mem_support_pure_iff] at hprOpt
  subst hprOpt
  rw [show (reduction (oSpec := oSpec) (Challenge := Challenge) K computeW).prover
      = prover (WitIn := WitIn) (Challenge := Challenge) K computeW from rfl,
    prover_run_eq K computeW stmt wit hdir, mem_support_bind_iff] at hpr
  obtain ⟨c, -, hpr⟩ := hpr
  rw [mem_support_pure_iff] at hpr
  subst hpr
  refine ⟨c, ?_⟩
  simp only [Option.elim_some, reduction, verifier, Verifier.run] at hx
  simp only [ProtocolSpec.ChallengeIdx, ProtocolSpec.Challenge, OptionT.run_pure, liftM_pure,
    ProgrammingPolicy.empty_apply, pure_bind, Option.elim_some, Option.getM_some, support_pure,
    Set.mem_singleton_iff] at hx
  exact hx

end Execution

/-- **Perfect completeness of a committed scalar phase**, at error exactly `0`.

The two hypotheses are precisely the two conjuncts of `rel K checkAt` that are not true by
construction: `hcheck`, the challenge-local predicate at **every** challenge (which is why the error
is `0` and why no property of the challenge distribution is used), and `hshort`, admissibility of
the opening the honest prover computes. Commitment consistency is definitional — the prover shell
derives its round-0 message from `computeW`, so it cannot commit to anything else.

`SampleableType Challenge` is needed only so that execution can draw the challenge at all. -/
theorem reduction_perfectCompleteness [SampleableType Challenge]
    (K : BindingCommitment W Short) (computeW : Stmt → WitIn → W)
    (checkAt : Stmt → Challenge → W → Prop) (relIn : Set (Stmt × WitIn))
    (hcheck : ∀ stmt wit, (stmt, wit) ∈ relIn → ∀ c, checkAt stmt c (computeW stmt wit))
    (hshort : ∀ stmt wit, (stmt, wit) ∈ relIn → Short (computeW stmt wit))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (reduction (oSpec := oSpec) K computeW).perfectCompleteness init impl relIn
      (rel K checkAt) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hIn x hx
  obtain ⟨c, rfl⟩ := reduction_run_support K computeW stmt wit rfl x hx
  exact ⟨_, rfl, ⟨rfl, hcheck stmt wit hIn c, hshort stmt wit hIn⟩, rfl⟩

end Completeness

end CommittedScalar

end CoordinateWise
