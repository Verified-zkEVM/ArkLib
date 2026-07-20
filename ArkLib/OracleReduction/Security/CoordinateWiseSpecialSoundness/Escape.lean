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
  the parallel escape seam. Packages compose with `EscapeCWSSPackage.append` (infix `▷`, explicit
  synonym `▷ₑ`) when both their ordinary relation seam and their escape seam agree.

  Crucially, `esc` is **statement-independent**: an MSIS/collision solution is checkable against
  the (parametric) commitment key alone, so escapes pass through statement maps trivially, and the
  escape branch of every seam extractor is the identity `Sum.inr`.

  ## Lifting escape-free packages and the package lattice

  Escape packages need only be *defined* for the subprotocols that genuinely produce escapes.
  An escape-free `CWSSPackage` (or guarded `GCWSSPackage`) enters an escape chain automatically:
  `Verifier.coordinateWiseSpecialSound.withEscape` widens its certificate to any escape set, and
  `CWSSPackage.withEscape` / `GCWSSPackage.withEscape` package the lift with a constant escape
  budget (`escIn = escOut` — an escape-free extractor passes downstream escapes through
  unchanged).

  Together with the (lossless) purity-to-guardedness lift `toGuarded`, the four package kinds
  form the 2×2 lattice escape? × guarded?, and every ordered pair composes at its join: the
  mixed appends insert the required lifts on the fly, and all sixteen compositions are reached
  through the universal `▷` — a single scoped elaborator that dispatches on the factors' package
  kinds (the kind-marked `▷ᵍ`, `▷ₑ`, `▷ₑᵍ` remain as explicit synonyms). Composing two
  escape-free packages stays escape-free, two pure packages stay pure (on the proven pure append
  theorem); a single escape-aware or guarded factor lifts the rest of the chain. Repo code
  composes with the universal `▷` throughout.

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

namespace Verifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Escape-widening transport for tree special soundness.** A tree-special-sound verifier stays
tree special sound after widening both relations by the same escape set `esc`.

If `esc = ∅`, the widened output language coincides with the original one
(`Set.mem_withEscape_language_iff`) and the original extractor lifts through `Sum.inl`. If `esc`
is nonempty, the widened acceptance hypothesis is vacuous, so the extractor returns a fixed
escape via `Sum.inr` — the same degenerate branch a *hand-written* certificate for an escape-free
protocol in an escape chain must take on trees accepted only through the escape disjunct. The
lift therefore loses nothing relative to hand-threading escapes through an escape-free protocol;
it automates exactly the certificate one would write (cf. the "formal price" note on
`Set.mem_withEscape_language_iff`). -/
theorem treeSpecialSound.withEscape {E : Type} (esc : Set E)
    {S : ChallengeTreeShape pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (h : verifier.treeSpecialSound init impl S relIn relOut) :
    verifier.treeSpecialSound init impl S (relIn.withEscape esc) (relOut.withEscape esc) := by
  rcases esc.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · obtain ⟨Ext, hExt⟩ := h
    refine ⟨fun stmt tree => Sum.inl (Ext stmt tree), fun stmtIn tree hstr hacc => ?_⟩
    rw [Set.mem_withEscape_inl]
    refine hExt stmtIn tree hstr ?_
    rwa [show (relOut.withEscape (∅ : Set E)).language = relOut.language from
      Set.ext fun _ => by simp] at hacc
  · exact ⟨fun _ _ => Sum.inr e, fun _ _ _ _ => (Set.mem_withEscape_inr relIn esc _ e).mpr he⟩

/-- **Escape-widening transport for coordinate-wise special soundness**
(`Verifier.treeSpecialSound.withEscape` at the CWSS shape): a CWSS certificate for
`relIn ⇒ relOut` widens to one for `relIn.withEscape esc ⇒ relOut.withEscape esc`. This is what
lets an escape-free package enter an escape-threaded chain (`CWSSPackage.withEscape`,
`GCWSSPackage.withEscape`). -/
theorem coordinateWiseSpecialSound.withEscape {E : Type} (esc : Set E)
    {D : CWSSStructure pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (h : verifier.coordinateWiseSpecialSound init impl D relIn relOut) :
    verifier.coordinateWiseSpecialSound init impl D
      (relIn.withEscape esc) (relOut.withEscape esc) :=
  treeSpecialSound.withEscape esc h

end Verifier

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled escape-aware coordinate-wise-special-sound reduction**.

The public `relIn` and `relOut` fields describe the ordinary witness flow between protocols.
Separately, `escIn` and `escOut` describe the escape budget before and after extraction through
this package. Only `isCWSS` combines these two flows, widening the ordinary relations with
`Set.withEscape`.

This separation keeps composed protocol statements readable while permitting each extractor to
add its own cryptographic failure artifacts to the escape flow. Compose packages with
`EscapeCWSSPackage.append` / the infix `▷` (explicit synonym `▷ₑ`). -/
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
relation and escape set. Written infix as `L₁ ▷ L₂` (explicit synonym `▷ₑ`). -/
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

/-! ### Lifting escape-free packages into an escape chain

An escape-free `CWSSPackage` enters the escape world for free: `CWSSPackage.withEscape` widens
its certificate with `Verifier.coordinateWiseSpecialSound.withEscape`, using the *same* escape
set on both seams — an escape-free extractor passes downstream escapes through unchanged, so its
escape budget neither grows nor shrinks. The mixed appends `CWSSPackage.appendEscape` and
`EscapeCWSSPackage.appendPure` insert this lift automatically, choosing the escape budget that
makes the escape seam hold definitionally.

All escape-world compositions are reachable through the universal `▷` (the elaborator at the end
of this file), so a chain may mix escape-free and escape-aware packages freely: two escape-free
packages compose to an escape-free package (`CWSSPackage.append`), and one escape-aware factor
lifts the rest of the chain. Escape packages thus need only be *defined* for the subprotocols
that genuinely produce escapes. -/

section Lift

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Lift an escape-free package into the escape world with a constant escape budget `esc`:
verifier, structure, relations, and purity carry over, `escIn = escOut = esc`, and the CWSS
certificate is widened by `Verifier.coordinateWiseSpecialSound.withEscape`. -/
def CWSSPackage.withEscape {E StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) (esc : Set E) :
    EscapeCWSSPackage init impl E StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  escIn := esc
  escOut := esc
  escape_mono := subset_rfl
  isPure := L.isPure
  isCWSS := L.isCWSS.withEscape esc

/-- **Compose an escape-free left factor with an escape-aware right factor.** The left package is
lifted with the right package's *input* escape budget (`CWSSPackage.withEscape`), so the escape
seam holds definitionally and only the ordinary relation seam `hRel` remains (discharged by
`rfl`). The composed package accepts escapes exactly as `L₂` does and passes them through
unchanged. Dispatched by the universal `▷`. -/
def CWSSPackage.appendEscape {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  (L₁.withEscape L₂.escIn).append L₂ hRel rfl

/-- **Compose an escape-aware left factor with an escape-free right factor.** The right package
is lifted with the left package's *output* escape budget (`CWSSPackage.withEscape`), so the
escape seam holds definitionally and only the ordinary relation seam `hRel` remains (discharged
by `rfl`). Dispatched by the universal `▷`. -/
def EscapeCWSSPackage.appendPure {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append (L₂.withEscape L₁.escOut) hRel rfl

end Lift

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

/-! ### Lifting into the escape-guarded corner: the full package lattice

The four package kinds form the 2×2 grid escape? × guarded? (`CWSSPackage`,
`EscapeCWSSPackage`, `GCWSSPackage`, `EscapeGCWSSPackage`), ordered by the two one-way,
lossless lifts `withEscape` (constant escape budget) and `toGuarded` (trivially-true guard).
This section provides `GCWSSPackage.withEscape` and every mixed append whose join is the
escape-guarded corner; each lifts its factors to the join automatically, so a package is
declared in the *weakest* world it honestly lives in and composition computes the join.

All sixteen ordered pairs are dispatched by the universal `▷` elaborator at the end of this file
(the escape-free appends live in `Package.lean`/`Guarded.lean`, the pure escape-world ones in the
`Lift` section above, the rest here); each pair of factor kinds determines its append uniquely.
The kind-marked infixes `▷ᵍ`, `▷ₑ`, `▷ₑᵍ` remain as explicit synonyms, but repo code composes
with the universal `▷` throughout.

Note the proof-status consequence: composing two pure packages stays on the *proven* pure append
theorem, while any factor that is genuinely guarded moves the composite — visibly in its type —
onto the (currently sorried, B4) guarded append theorem. The automatic lifts fire only in chains
that already contain a guarded factor, so no chain silently loses proof strength. -/

section GuardedLift

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Lift an escape-free guarded package into the escape world with a constant escape budget
`esc`: verifier, structure, relations, and guardedness carry over, `escIn = escOut = esc`, and
the CWSS certificate is widened by `Verifier.coordinateWiseSpecialSound.withEscape`. -/
def GCWSSPackage.withEscape {E StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (L : GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) (esc : Set E) :
    EscapeGCWSSPackage init impl E StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  escIn := esc
  escOut := esc
  escape_mono := subset_rfl
  isGuarded := L.isGuarded
  isCWSS := L.isCWSS.withEscape esc

/-- **Compose an escape-free guarded left factor with an escape-aware guarded right factor.** The
left package is lifted with the right package's *input* escape budget (`GCWSSPackage.withEscape`),
so the escape seam holds definitionally and only the ordinary relation seam `hRel` remains
(discharged by `rfl`). Dispatched by the universal `▷` (explicit synonym `▷ᵍ`). -/
def GCWSSPackage.appendEscapeGuarded {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  (L₁.withEscape L₂.escIn).append L₂ hRel rfl

/-- **Compose an escape-aware guarded left factor with an escape-free guarded right factor.** The
right package is lifted with the left package's *output* escape budget
(`GCWSSPackage.withEscape`), so the escape seam holds definitionally and only the ordinary
relation seam `hRel` remains (discharged by `rfl`). Dispatched by the universal `▷` (explicit
synonym `▷ᵍ`). -/
def EscapeGCWSSPackage.appendGuarded {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeGCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append (L₂.withEscape L₁.escOut) hRel rfl

/-- **Compose a pure escape-free left factor with an escape-aware guarded right factor.** The
left package is lifted with the right package's *input* escape budget and the trivially-true
guard, so the escape seam holds definitionally and only the ordinary relation seam `hRel`
remains (discharged by `rfl`). Dispatched by the universal `▷`. -/
def CWSSPackage.appendEscapeGuarded {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  (L₁.withEscape L₂.escIn).toGuarded.append L₂ hRel rfl

/-- **Compose an escape-aware guarded left factor with a pure escape-free right factor.** The
right package is lifted with the left package's *output* escape budget and the trivially-true
guard, so the escape seam holds definitionally and only the ordinary relation seam `hRel`
remains (discharged by `rfl`). Dispatched by the universal `▷`. -/
def EscapeGCWSSPackage.appendPure {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeGCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append (L₂.withEscape L₁.escOut).toGuarded hRel rfl

/-- **Compose an escape-aware pure left factor with an escape-free guarded right factor.** The
left package gains the trivially-true guard and the right package is lifted with the left
package's *output* escape budget, so the escape seam holds definitionally and only the ordinary
relation seam `hRel` remains (discharged by `rfl`). Dispatched by the universal `▷`. -/
def EscapeCWSSPackage.appendGuarded {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append (L₂.withEscape L₁.escOut) hRel rfl

/-- **Compose an escape-free guarded left factor with an escape-aware pure right factor.** The
left package is lifted with the right package's *input* escape budget and the right package
gains the trivially-true guard, so the escape seam holds definitionally and only the ordinary
relation seam `hRel` remains (discharged by `rfl`). Dispatched by the universal `▷`. -/
def GCWSSPackage.appendEscape {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  (L₁.withEscape L₂.escIn).append L₂.toGuarded hRel rfl

/-- **Compose an escape-aware pure left factor with an escape-aware guarded right factor.** The
left package gains the trivially-true guard; both the ordinary relation seam `hRel` and the
escape seam `hEsc` remain (discharged by `rfl`). Dispatched by the universal `▷`. -/
def EscapeCWSSPackage.appendEscapeGuarded {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl)
    (hEsc : L₁.escOut = L₂.escIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂ hRel hEsc

/-- **Compose an escape-aware guarded left factor with an escape-aware pure right factor.** The
right package gains the trivially-true guard; both the ordinary relation seam `hRel` and the
escape seam `hEsc` remain (discharged by `rfl`). Dispatched by the universal `▷`. -/
def EscapeGCWSSPackage.appendEscape {E StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeGCWSSPackage init impl E StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl E StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl)
    (hEsc : L₁.escOut = L₂.escIn := by rfl) :
    EscapeGCWSSPackage init impl E StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toGuarded hRel hEsc

@[inherit_doc EscapeGCWSSPackage.append]
scoped infixr:65 " ▷ᵍ " => EscapeGCWSSPackage.append

@[inherit_doc GCWSSPackage.appendEscapeGuarded]
scoped infixr:65 " ▷ᵍ " => GCWSSPackage.appendEscapeGuarded

@[inherit_doc EscapeGCWSSPackage.appendGuarded]
scoped infixr:65 " ▷ᵍ " => EscapeGCWSSPackage.appendGuarded

end GuardedLift

/-! ### The universal append `▷`

A single (scoped) elaborator rather than sixteen overloaded notations: `L₁ ▷ L₂` elaborates both
factors once, reads the head constant of their types to determine the package kinds, and applies
the unique append that composes them at their join. Overloaded-notation `choice` nodes would
re-elaborate nested alternatives once per outer candidate — exponential in chain length, and a
five-link Hachi chain already exhausts the heartbeat budget — whereas this dispatch is linear.
The kind-marked infixes `▷ₑ`, `▷ᵍ`, `▷ₑᵍ` remain as single-target explicit synonyms. -/

section UniversalAppend

open Lean Elab Term Meta

/-- The dispatch table of the universal append `▷`: the package kinds of the left and right
factor determine the append that composes them at their join (inserting the `withEscape` /
`toGuarded` lifts as needed). -/
private def univAppendFn : Name → Name → Option Name
  | ``CWSSPackage,        ``CWSSPackage        => some ``CWSSPackage.append
  | ``CWSSPackage,        ``EscapeCWSSPackage  => some ``CWSSPackage.appendEscape
  | ``CWSSPackage,        ``GCWSSPackage       => some ``CWSSPackage.appendGuarded
  | ``CWSSPackage,        ``EscapeGCWSSPackage => some ``CWSSPackage.appendEscapeGuarded
  | ``EscapeCWSSPackage,  ``CWSSPackage        => some ``EscapeCWSSPackage.appendPure
  | ``EscapeCWSSPackage,  ``EscapeCWSSPackage  => some ``EscapeCWSSPackage.append
  | ``EscapeCWSSPackage,  ``GCWSSPackage       => some ``EscapeCWSSPackage.appendGuarded
  | ``EscapeCWSSPackage,  ``EscapeGCWSSPackage => some ``EscapeCWSSPackage.appendEscapeGuarded
  | ``GCWSSPackage,       ``CWSSPackage        => some ``GCWSSPackage.appendPure
  | ``GCWSSPackage,       ``EscapeCWSSPackage  => some ``GCWSSPackage.appendEscape
  | ``GCWSSPackage,       ``GCWSSPackage       => some ``GCWSSPackage.append
  | ``GCWSSPackage,       ``EscapeGCWSSPackage => some ``GCWSSPackage.appendEscapeGuarded
  | ``EscapeGCWSSPackage, ``CWSSPackage        => some ``EscapeGCWSSPackage.appendPure
  | ``EscapeGCWSSPackage, ``EscapeCWSSPackage  => some ``EscapeGCWSSPackage.appendEscape
  | ``EscapeGCWSSPackage, ``GCWSSPackage       => some ``EscapeGCWSSPackage.appendGuarded
  | ``EscapeGCWSSPackage, ``EscapeGCWSSPackage => some ``EscapeGCWSSPackage.append
  | _,                    _                    => none

/-- The package kind — the head constant of the type — of an elaborated `▷` factor. -/
private def packageKindOf (e : Expr) : TermElabM Name := do
  let t ← whnf (← instantiateMVars (← inferType e))
  match t.getAppFn.constName? with
  | some n => return n
  | none =>
    throwError "▷: cannot determine the package kind of{indentExpr e}\nof type{indentExpr t}"

/-- **The universal package append.** `L₁ ▷ L₂` composes any two CWSS packages — pure, guarded,
escape-aware, or both — at the join of their kinds, lifting each factor as needed
(`withEscape` with the escape partner's budget, `toGuarded` with the trivially-true check). The
remaining relation seam (and, between two escape-aware factors, the escape seam) is discharged
by `rfl`; for non-definitional seams call the dispatched append (see `univAppendFn`) explicitly
with the seam proofs. -/
scoped elab:65 l:term:66 " ▷ " r:term:65 : term => do
  let lE ← elabTerm l none
  let rE ← elabTerm r none
  let lN ← packageKindOf lE
  let rN ← packageKindOf rE
  let some fn := univAppendFn lN rN
    | throwError "▷: no package append composes `{lN}` with `{rN}`"
  let f ← mkConstWithFreshMVarLevels fn
  elabAppArgs f #[] #[.expr lE, .expr rE] (expectedType? := none)
    (explicit := false) (ellipsis := false)

end UniversalAppend

end CoordinateWise

end
