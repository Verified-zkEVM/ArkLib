/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
  # Escape-threaded coordinate-wise special soundness

  Protocol-agnostic plumbing for **escape threading** in composed special-soundness chains

  In a composed reduction chain, a downstream extractor may fail to produce a "real" witness and
  instead produce a cryptographic **escape** — e.g. a binding break of a commitment introduced in
  the middle of the chain (Hachi's `w̃`-commitment of Figure 4, whose collision is a Module-SIS
  solution via weak binding, [NOZ26] Remark 2 / Lemma 7). Composed extraction feeds each
  extractor's output into the *previous* seam relation, so every relation upstream of the escape's
  origin must have a home for it. `Set.withEscape` widens a relation `Set (S × W)` to
  `Set (S × (W ⊕ E))` by adjoining an escape set `esc : Set E` on the right summand.

  `EscapeCWSSPackage` keeps this widening internal to its special-soundness certificate. Its public
  `relIn` and `relOut` fields are the ordinary protocol relations, while `escIn` and `escOut` track
  the parallel escape seam. Packages compose with `EscapeCWSSPackage.append` (infix `▷ₑ`) when
  both their ordinary relation seam and their escape seam agree.

  Crucially, `esc` is **statement-independent**: an MSIS/collision solution is checkable against
  the (parametric) commitment key alone, so escapes pass through statement maps trivially, and the
  escape branch of every seam extractor is the identity `Sum.inr`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace Set

variable {S W E : Type*}

/-- Widen a relation by an escape disjunct: a witness is either a real witness `w : W` related to
the statement by `rel`, or an escape `e : E` in the statement-independent escape set `esc`. -/
def withEscape (rel : Set (S × W)) (esc : Set E) : Set (S × (W ⊕ E)) :=
  {p | match p with
       | (s, .inl w) => (s, w) ∈ rel
       | (_, .inr e) => e ∈ esc}

/-- A real witness `Sum.inl w` is in the widened relation iff `(s, w)` is in the original one. -/
@[simp]
theorem mem_withEscape_inl (rel : Set (S × W)) (esc : Set E) (s : S) (w : W) :
    (s, Sum.inl w) ∈ rel.withEscape esc ↔ (s, w) ∈ rel := Iff.rfl

/-- An escape `Sum.inr e` is in the widened relation iff `e` is in the escape set, regardless of
the statement. -/
@[simp]
theorem mem_withEscape_inr (rel : Set (S × W)) (esc : Set E) (s : S) (e : E) :
    (s, Sum.inr e) ∈ rel.withEscape esc ↔ e ∈ esc := Iff.rfl

/-- The language of an escape-widened relation: a statement is in the language iff it is in the
original language, or *any* escape exists (escapes are statement-independent, so a single escape
puts every statement in the widened language). This is the formal price of escape threading: the
widened acceptance condition is meaningful *relative to the extractor structure*, exactly as the
MSIS disjuncts of Hachi's `relIn` already are. -/
theorem mem_withEscape_language_iff (rel : Set (S × W)) (esc : Set E) (s : S) :
    s ∈ (rel.withEscape esc).language ↔ s ∈ rel.language ∨ esc.Nonempty := by
  simp only [Set.mem_language_iff]
  constructor
  · rintro ⟨w | e, hw⟩
    · exact Or.inl ⟨w, hw⟩
    · exact Or.inr ⟨e, hw⟩
  · rintro (⟨w, hw⟩ | ⟨e, he⟩)
    · exact ⟨Sum.inl w, hw⟩
    · exact ⟨Sum.inr e, he⟩

/-- Degeneration: widening by the empty escape set over an empty escape type loses nothing —
membership is exactly membership of the underlying relation through `Sum.inl`. Together with
`Empty`'s emptiness this witnesses that the escape-threaded chain generalizes the un-threaded
one. -/
theorem withEscape_empty_iff (rel : Set (S × W)) (s : S) (w : W ⊕ Empty) :
    (s, w) ∈ rel.withEscape (∅ : Set Empty) ↔ ∃ w', w = Sum.inl w' ∧ (s, w') ∈ rel := by
  rcases w with w' | e
  · simp
  · exact e.elim

end Set

noncomputable section

open OracleComp OracleSpec ProtocolSpec

/-- The escape-widened witness type remains inhabited whenever its ordinary witness type is. -/
instance {W E : Type} [Nonempty W] : Nonempty (W ⊕ E) :=
  ⟨.inl Classical.ofNonempty⟩

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled escape-aware coordinate-wise-special-sound reduction**.

The public `relIn` and `relOut` fields describe the ordinary witness flow between protocols.
Separately, `escIn` and `escOut` describe the escape budget before and after extraction through
this package. Only `isCWSS` combines these two flows, widening the ordinary relations with
`Set.withEscape`.

This separation keeps composed protocol statements readable while permitting each extractor to
add its own cryptographic failure artifacts to the escape flow. Compose packages with
`EscapeCWSSPackage.append` / the infix `▷ₑ`. -/
structure EscapeCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (E StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier. -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The ordinary input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The ordinary output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- Escapes that may be returned when extracting an input witness. -/
  escIn : Set E
  /-- Escapes accepted from the next extractor in the chain. -/
  escOut : Set E
  /-- Extraction may preserve or grow the escape set, but never discard an accepted escape. -/
  escape_mono : escOut ⊆ escIn
  /-- The verifier is pure: its verdict is a deterministic function of statement and transcript.
  Needed to place this package as the left factor of an `append`. -/
  isPure : verifier.IsPure
  /-- The certificate over the parallel ordinary and escape flows. -/
  isCWSS : verifier.coordinateWiseSpecialSound init impl struct
    (relIn.withEscape escIn) (relOut.withEscape escOut)

namespace EscapeCWSSPackage

/-- **Compose two escape-aware packages along matching ordinary and escape seams.**

`hRel` identifies the ordinary relation seam and `hEsc` identifies the parallel escape seam; both
are discharged by `rfl` when a chain uses named seam relations and escape budgets. The resulting
package exposes the left package's input relation and escape set and the right package's output
relation and escape set. Written infix as `L₁ ▷ₑ L₂`. -/
def append {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl)
    (hEsc : L₁.escOut = L₂.escIn := by rfl) :
    EscapeCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  escIn := L₁.escIn
  escOut := L₂.escOut
  escape_mono := by
    intro e he
    apply L₁.escape_mono
    rw [hEsc]
    exact L₂.escape_mono he
  isPure := Verifier.IsPure.append L₁.verifier L₂.verifier L₁.isPure L₂.isPure
  isCWSS := by
    obtain ⟨verify₁, hV₁⟩ := L₁.isPure.is_pure
    have h₂ := L₂.isCWSS
    rw [← hRel, ← hEsc] at h₂
    exact Verifier.append_coordinateWiseSpecialSound init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct verify₁ hV₁ L₁.isCWSS h₂

end EscapeCWSSPackage

@[inherit_doc EscapeCWSSPackage.append]
scoped infixr:65 " ▷ₑ " => EscapeCWSSPackage.append

/-- A guarded escape-aware CWSS package. Its public relations and escape sets remain separate;
only the CWSS certificate widens the relations with their corresponding escape budgets. -/
structure EscapeGCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (E StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier (which may reject at runtime). -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The ordinary input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The ordinary output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- Escapes that may be returned when extracting an input witness. -/
  escIn : Set E
  /-- Escapes accepted from the next extractor in the chain. -/
  escOut : Set E
  /-- Extraction may preserve or grow the escape set, but never discard an accepted escape. -/
  escape_mono : escOut ⊆ escIn
  /-- The verifier is guarded by a deterministic Boolean check. -/
  isGuarded : verifier.IsGuarded
  /-- The certificate over the parallel ordinary and escape flows. -/
  isCWSS : verifier.coordinateWiseSpecialSound init impl struct
    (relIn.withEscape escIn) (relOut.withEscape escOut)

namespace EscapeGCWSSPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Regard a pure escape-aware package as guarded. -/
def _root_.CoordinateWise.EscapeCWSSPackage.toGuarded
    {E StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (L : EscapeCWSSPackage init impl E StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl E StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  escIn := L.escIn
  escOut := L.escOut
  escape_mono := L.escape_mono
  isGuarded := Verifier.IsGuarded.of_isPure L.verifier L.isPure
  isCWSS := L.isCWSS

/-- Compose two guarded escape-aware packages along matching ordinary and escape seams. -/
def append {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeGCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl)
    (hEsc : L₁.escOut = L₂.escIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  escIn := L₁.escIn
  escOut := L₂.escOut
  escape_mono := by
    intro e he
    apply L₁.escape_mono
    rw [hEsc]
    exact L₂.escape_mono he
  isGuarded := Verifier.IsGuarded.append L₁.verifier L₂.verifier L₁.isGuarded L₂.isGuarded
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hRel, ← hEsc] at h₂
    exact Verifier.append_coordinateWiseSpecialSound_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.isGuarded L₁.isCWSS h₂

end EscapeGCWSSPackage

@[inherit_doc EscapeGCWSSPackage.append]
scoped infixr:65 " ▷ₑᵍ " => EscapeGCWSSPackage.append

end CoordinateWise

end
