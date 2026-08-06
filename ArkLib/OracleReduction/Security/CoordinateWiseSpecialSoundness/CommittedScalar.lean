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
  `escEvent stmt tree ∨ (stmt, treeExtractor stmt tree) ∈ relIn`.

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

noncomputable section

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
the tree through the same `readPre` / `readFam` the escape event uses. -/
def treeExtractor [Nonempty W] {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short)
    (checkAt : Stmt → Challenge → W → Prop) (project : W → WitIn) :
    Extractor.TreeBased Stmt WitIn (pSpecScalar K.TCom Challenge)
      (CWSSStructure.toShape
        (scalarStructure (Msg := K.TCom) (C := Challenge) k hk)).arity :=
  ScalarRound.treeExtractorScalar hk (rel K checkAt) (mkWitness hk K project)

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

/-- **Generic escape-threaded CWSS certificate for committed scalar phases.** All
protocol-independent extraction and tree reasoning is reused from `ScalarRound`; `recover` is the
instance's substantive algebra. -/
theorem coordinateWiseSpecialSoundWithEscape [Nonempty W] {ι : Type} {oSpec : OracleSpec ι}
    {σ : Type} {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W Short)
    (project : W → WitIn) (checkAt : Stmt → Challenge → W → Prop)
    (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl (scalarStructure k hk)
      (escEvent hk K checkAt) relIn (rel K checkAt)
      (verifier (oSpec := oSpec) K) (treeExtractor hk K checkAt project) :=
  ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar init impl hk (verifier K)
    (fun _ _ => rfl) relIn (rel K checkAt) (mkWitness hk K project) (escLocal K)
    (fun s t fam resp hbranch hinj =>
      mkWitness_mem hk K project checkAt relIn recover s t fam resp hbranch hinj)

/-- Bundled committed scalar phase, ready for CWSS composition.

This lands in the **pure, escape-aware** corner of the package lattice: the verifier is `pure (…)`
and never `failure`, so it is a valid left factor, while the commitment's escape event needs the
`esc` field. Escape-free neighbours compose against it for free through the universal `▷`
(`CWSSPackage.toEscape`), so no separate plain-`CWSSPackage` variant is needed — at an injective
`com` the event simply never fires. -/
def package [Nonempty W] {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
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
  isPure := ⟨fun stmt tr =>
    (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  extractor := treeExtractor hk K checkAt project
  isCWSS := coordinateWiseSpecialSoundWithEscape hk K project checkAt relIn recover init impl

end

end CommittedScalar

end CoordinateWise
