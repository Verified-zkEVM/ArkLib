/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Escape
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Committed scalar phase (generic commit-then-challenge CWSS shell)

  A recurring two-round shape: the prover **commits** to an opening, the verifier sends one
  **scalar challenge**, and the output statement retains both values.  This file owns that
  shape once — protocol, anchored relation, and the extraction argument — so that each
  instantiation supplies only its challenge-local predicate and one recovery theorem.

  This is deliberately *not* a ring-switching module.  It is the protocol/security seam that
  quotient-evaluation ring switches such as [HMZ25] (Hachi [NOZ26] Figure 4 / Lemma 9) happen
  to have, but nothing here mentions rings, polynomials, or packing: the ingredients are a
  `BindingCommitment` (binding restricted to `Short` openings, with an escape budget for the
  weak-binding case) and a `checkAt` predicate.  The basis-packing ring switch of DP24 and
  Hachi §3 is a different construction (`ProofSystem/RingSwitching/Packing/`); with this
  file it shares the `ScalarRound.pSpecScalar` wire format (this file's verifier is the
  check-free case of the check-then-update round shape on that wire —
  `ProofSystem/RingSwitching/RoundVerifiers.lean`).

  ## Contents

  * `BindingCommitment W E Short` — deterministic commitment whose binding guarantee is
    restricted to `Short` openings; two distinct short openings yield an element of the escape
    set `esc`.  Exact binding instantiates `E` empty; Hachi's weak binding instantiates `E`
    with its Module-SIS escape budget.
  * `CommittedScalar.Statement`, `CommittedScalar.rel` — the output statement
    `Stmt × TCom × Challenge` and the anchored relation (commitment consistency + `checkAt` +
    `Short`).
  * `CommittedScalar.verifier` / `CommittedScalar.prover` — the pure statement-extending
    verifier and the honest prover shell (the commitment is derived from the output opening by
    construction).
  * `CommittedScalar.buildWitness` — the three-way extractor: escape pass-through /
    commitment-collision escape / common-opening projection — with its correctness theorem
    `buildWitness_mem`, parameterized by the single instance-specific `recover` hypothesis
    (one common short opening satisfying `checkAt` at `k` pairwise-distinct challenges recovers
    the input relation).
  * `CommittedScalar.coordinateWiseSpecialSound` / `CommittedScalar.package` — the generic
    CWSS theorem at `scalarStructure k` and its `CWSSPackage` bundle, ready for `▷`
    composition.

  ## Consumers

  * Hachi's HMZ25 quotient-evaluation ring switch
    (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`), at `k = 2d`.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace CoordinateWise

/-- A deterministic commitment whose binding guarantee is restricted to `Short` openings.

Two distinct short openings of one commitment produce an element of `esc`.  This is the common
interface needed by committed scalar phases: exact binding uses an empty escape type, while
Hachi's weak binding instantiates `E` with its Module-SIS escape budget. -/
structure BindingCommitment (W E : Type) (Short : W → Prop) where
  /-- Commitment/message type. -/
  TCom : Type
  /-- Deterministic commitment map. -/
  com : W → TCom
  /-- Valid binding-break artifacts. -/
  esc : Set E
  /-- Artifact extracted from two candidate openings. -/
  escOfCollision : W → W → E
  /-- Norm-conditioned binding: distinct short openings of the same commitment yield an escape. -/
  collision_mem : ∀ w w', w ≠ w' → com w = com w' → Short w → Short w' →
    escOfCollision w w' ∈ esc

namespace CommittedScalar

noncomputable section

open OracleComp OracleSpec ProtocolSpec ScalarRound

variable {Stmt W E Challenge WitIn : Type} {Short : W → Prop}

/-- Output statement of a committed scalar phase: input statement, commitment, challenge. -/
abbrev Statement (Stmt TCom Challenge : Type) : Type := Stmt × TCom × Challenge

/-- The anchored output relation for a committed scalar phase.

The framework fixes commitment consistency and admissibility (`Short`); an instantiation supplies
only its challenge-local predicate `checkAt`.  Soundness additionally requires a recovery theorem
from `k` distinct challenges, so `checkAt` cannot by itself certify a vacuous instance. -/
def rel (K : BindingCommitment W E Short) (checkAt : Stmt → Challenge → W → Prop) :
    Set (Statement Stmt K.TCom Challenge × W) :=
  {p | K.com p.2 = p.1.2.1 ∧ checkAt p.1.1 p.1.2.2 p.2 ∧ Short p.2}

/-- Pure statement-extending verifier shared by committed scalar phases. -/
def verifier {ι : Type} {oSpec : OracleSpec ι} (K : BindingCommitment W E Short) :
    Verifier oSpec Stmt (Statement Stmt K.TCom Challenge)
      (pSpecScalar K.TCom Challenge) where
  verify := fun stmt tr =>
    pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- Honest prover shell for a committed scalar phase.

The commitment is derived from `computeW`; the API cannot send a commitment unrelated to its
output opening. -/
def prover {ι : Type} {oSpec : OracleSpec ι} (K : BindingCommitment W E Short)
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

/-- Read the real opening from an escaped response.  The fallback is unreachable on the
common-opening extraction path, which first proves that every response is an `inl`. -/
noncomputable def responseOpening [Nonempty W] (r : W ⊕ E) : W :=
  r.elim id fun _ => Classical.ofNonempty

@[simp] theorem responseOpening_inl [Nonempty W] (w : W) :
    responseOpening (Sum.inl (β := E) w) = w := rfl

/-- Generic three-way assembler for a committed scalar phase.

It passes through an existing escape, turns two distinct openings of the shared commitment into
a binding escape, and otherwise projects the shared opening back to the input witness. -/
noncomputable def buildWitness [Nonempty W] {k : ℕ} (hk : 2 ≤ k)
    (K : BindingCommitment W E Short) (project : W → WitIn)
    (_s : Stmt) (_t : K.TCom) (_fam : Fin k → Challenge)
    (resp : Fin k → (W ⊕ E)) : WitIn ⊕ E := by
  classical
  let first : Fin k := ⟨0, by omega⟩
  letI : Decidable (∃ j : Fin k, (resp j).isRight) := Classical.propDecidable _
  letI : Decidable (∃ j : Fin k,
      responseOpening (W := W) (E := E) (resp j) ≠
        responseOpening (W := W) (E := E) (resp first)) := Classical.propDecidable _
  exact if he : ∃ j, (resp j).isRight then
      (resp he.choose).map project id
    else if hcol : ∃ j, responseOpening (resp j) ≠ responseOpening (resp first) then
      .inr (K.escOfCollision (responseOpening (resp hcol.choose))
        (responseOpening (resp first)))
    else
      .inl (project (responseOpening (resp first)))

/-- Correctness of `buildWitness`, parameterized by the only construction-specific fact:
one common short opening satisfying `checkAt` at `k` distinct challenges recovers `relIn`. -/
theorem buildWitness_mem [Nonempty W] {k : ℕ} (hk : 2 ≤ k)
    (K : BindingCommitment W E Short) (project : W → WitIn)
    (checkAt : Stmt → Challenge → W → Prop) (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (s : Stmt) (t : K.TCom) (fam : Fin k → Challenge) (resp : Fin k → (W ⊕ E))
    (hresp : ∀ j, ((s, t, fam j), resp j) ∈ (rel K checkAt).withEscape K.esc)
    (hinj : Function.Injective fam) :
    (s, buildWitness hk K project s t fam resp) ∈ relIn.withEscape K.esc := by
  classical
  let first : Fin k := ⟨0, by omega⟩
  letI : Decidable (∃ j : Fin k, (resp j).isRight) := Classical.propDecidable _
  letI : Decidable (∃ j : Fin k,
      responseOpening (W := W) (E := E) (resp j) ≠ responseOpening (resp first)) :=
    Classical.propDecidable _
  have hreal : ∀ j w, resp j = .inl w → ((s, t, fam j), w) ∈ rel K checkAt := by
    intro j w hjw
    have h := hresp j
    rwa [hjw] at h
  by_cases he : ∃ j, (resp j).isRight
  · simp only [buildWitness, he, ↓reduceDIte]
    obtain ⟨e, hje⟩ := Sum.isRight_iff.mp he.choose_spec
    have hmem := hresp he.choose
    rw [hje] at hmem ⊢
    exact hmem
  · simp only [buildWitness, he, ↓reduceDIte]
    by_cases hcol : ∃ j, responseOpening (resp j) ≠ responseOpening (resp first)
    · simp only [first, hcol, ↓reduceDIte]
      push Not at he
      have hleft : ∀ j, ∃ w, resp j = .inl w := by
        intro j
        exact Sum.isLeft_iff.mp (Sum.not_isRight.mp (by simpa using he j))
      obtain ⟨wA, hwA⟩ := hleft hcol.choose
      obtain ⟨wB, hwB⟩ := hleft first
      have hA : responseOpening (resp hcol.choose) = wA := by rw [hwA]; rfl
      have hB : responseOpening (resp first) = wB := by rw [hwB]; rfl
      have hrelA := hreal hcol.choose wA hwA
      have hrelB := hreal first wB hwB
      have hne : responseOpening (resp hcol.choose) ≠
          responseOpening (resp first) := hcol.choose_spec
      have hcom : K.com (responseOpening (resp hcol.choose)) =
          K.com (responseOpening (resp first)) := by
        rw [hA, hB, hrelA.1, hrelB.1]
      exact K.collision_mem _ _ hne hcom
        (by rw [hA]; exact hrelA.2.2) (by rw [hB]; exact hrelB.2.2)
    · simp only [first, hcol, ↓reduceDIte]
      push Not at he hcol
      have hleft : ∀ j, ∃ w, resp j = .inl w := by
        intro j
        exact Sum.isLeft_iff.mp (Sum.not_isRight.mp (by simpa using he j))
      obtain ⟨W, hW⟩ := hleft first
      have hWo : responseOpening (resp first) = W := by rw [hW]; rfl
      have hallW : ∀ j, resp j = .inl W := by
        intro j
        obtain ⟨w, hw⟩ := hleft j
        have hjo : responseOpening (resp j) = w := by rw [hw]; rfl
        have hsame := hcol j
        rw [hjo, hWo] at hsame
        rw [hw, hsame]
      have hrel : ∀ j, ((s, t, fam j), W) ∈ rel K checkAt :=
        fun j => hreal j W (hallW j)
      rw [hWo]
      exact Set.mem_withEscape_inl _ _ _ _ |>.mpr
        (recover s W fam hinj (fun j => (hrel j).2.1) (hrel first).2.2)

/-- Generic CWSS theorem for committed scalar phases.  All protocol-independent extraction and
tree reasoning is reused from `ScalarRound`; `recover` is the instance's substantive algebra. -/
theorem coordinateWiseSpecialSound [Nonempty W] {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W E Short)
    (project : W → WitIn) (checkAt : Stmt → Challenge → W → Prop)
    (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (verifier (oSpec := oSpec) K).coordinateWiseSpecialSound init impl
      (scalarStructure k hk) (relIn.withEscape K.esc) ((rel K checkAt).withEscape K.esc) :=
  coordinateWiseSpecialSound_of_mkWitness_scalar init impl hk (verifier K)
    (fun _ _ => rfl) (relIn.withEscape K.esc) ((rel K checkAt).withEscape K.esc)
    (buildWitness hk K project)
    (fun s t fam resp hbranch hinj =>
      buildWitness_mem hk K project checkAt relIn recover s t fam resp hbranch hinj)

/-- Bundled committed scalar phase, ready for CWSS composition. -/
def package [Nonempty W] {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    {k : ℕ} (hk : 2 ≤ k) (K : BindingCommitment W E Short)
    (project : W → WitIn) (checkAt : Stmt → Challenge → W → Prop)
    (relIn : Set (Stmt × WitIn))
    (recover : ∀ (s : Stmt) (w : W) (fam : Fin k → Challenge),
      Function.Injective fam → (∀ j, checkAt s (fam j) w) → Short w →
        (s, project w) ∈ relIn)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    CWSSPackage init impl Stmt (WitIn ⊕ E) (Statement Stmt K.TCom Challenge) (W ⊕ E)
      (pSpecScalar K.TCom Challenge) where
  verifier := verifier K
  struct := scalarStructure k hk
  relIn := relIn.withEscape K.esc
  relOut := (rel K checkAt).withEscape K.esc
  isPure := ⟨fun stmt tr =>
    (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := coordinateWiseSpecialSound hk K project checkAt relIn recover init impl

end

end CommittedScalar

end CoordinateWise
