/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Prelude

/-!
  # Escape-threaded relations (`Set.withEscape`)

  Protocol-agnostic plumbing for **escape threading** in composed special-soundness chains
  (Hachi [NOZ26] §4.3+; design decision G1 of the sumcheck-track plan).

  In a composed reduction chain, a downstream extractor may fail to produce a "real" witness and
  instead produce a cryptographic **escape** — e.g. a binding break of a commitment introduced in
  the middle of the chain (Hachi's `w̃`-commitment of Figure 4, whose collision is a Module-SIS
  solution via weak binding, [NOZ26] Remark 2 / Lemma 7). Composed extraction feeds each
  extractor's output into the *previous* seam relation, so every relation upstream of the escape's
  origin must have a home for it. `Set.withEscape` widens a relation `Set (S × W)` to
  `Set (S × (W ⊕ E))` by adjoining an escape set `esc : Set E` on the right summand.

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

@[simp]
theorem mem_withEscape_inl (rel : Set (S × W)) (esc : Set E) (s : S) (w : W) :
    (s, Sum.inl w) ∈ rel.withEscape esc ↔ (s, w) ∈ rel := Iff.rfl

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
