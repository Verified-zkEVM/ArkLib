/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
  # Escape-aware CWSS packages and the package lattice

  Some reductions cannot always extract a witness: instead their extraction exhibits a
  cryptographic **escape**, e.g. a binding break of a commitment introduced mid-chain (Hachi's
  `w̃`-commitment of Figure 4, whose collision is a Module-SIS solution by weak binding,
  [NOZ26] Remark 2 / Lemma 7). An escape is an **event on the observable data** `(stmtIn, tree)`
  (`ChallengeTree.EscapeEvent`) entering the certificate as a disjunct of its conclusion:

  ```
  ∀ stmt tree, IsStructured → IsAccepting → esc stmt tree ∨ (stmt, Ext stmt tree) ∈ relIn
  ```

  Relations, witness types and extractors therefore stay plain; `esc` is the only escape-specific
  field a package carries. Since `esc` never mentions the extractor, no choice of extractor can
  discharge a certificate vacuously — the certificate is exactly as strong as its event is honest.
  `esc` is a **trusted specification**, on the same footing as `relIn`/`relOut`; its contract is
  stated once, on `ProtocolSpec.ChallengeTree.EscapeEvent`. Read it before writing an event.

  Packages carry their extraction algorithm as an explicit `extractor` field, so a composed chain
  exposes an actual end-to-end extractor `chain.extractor` — the algorithm a later knowledge-error
  accounting must run against the escape probability.

  ## The package lattice

  `CWSSPackage`, `EscapeCWSSPackage`, `GCWSSPackage`, `EscapeGCWSSPackage` form the 2×2 lattice
  escape? × guarded?, ordered by two **lossless** lifts: `toEscape` (at the never-firing event
  `fun _ _ => False`, so extractor and certificate are unchanged) and `toGuarded` (at the
  trivially-true check). A package is declared in the weakest corner it honestly lives in, and
  every ordered pair composes at the join through the universal `▷` — one scoped elaborator
  dispatching on the factors' package kinds (`▷ᵍ`, `▷ₑ`, `▷ₑᵍ` remain as explicit synonyms).

  Composition identifies only the relation seam `hRel`: escape events are combined by
  `ChallengeTree.EscapeEvent.append`, so factors tracking breaks of entirely different assumptions
  compose freely. Two pure packages compose on the *proven* pure append theorem; a genuinely
  guarded factor moves the composite — visibly in its type — onto the sorried guarded one.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled escape-aware coordinate-wise-special-sound reduction**: `CWSSPackage` with one
extra field, the **escape event** `esc`. Its certificate `isCWSS` concludes
`esc stmt tree ∨ extraction succeeds` on every structured accepting tree, so `relIn`/`relOut` and
`extractor` stay ordinary.

`esc` is a trusted specification — reading its definition is the reader's obligation, just as for
`relIn`/`relOut` (contract: `ChallengeTree.EscapeEvent`). Compose with `EscapeCWSSPackage.append` /
the universal infix `▷` (explicit synonym `▷ₑ`). -/
structure EscapeCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier. -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- The **escape event**: the cryptographic failure this package's extraction may exhibit
  instead of a witness. A trusted spec — see `ChallengeTree.EscapeEvent`. -/
  esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape struct).arity
  /-- The verifier is pure: its verdict is a deterministic function of statement and transcript.
  Needed to place this package as the left factor of an `append`. -/
  isPure : verifier.IsPure
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` produces a `relIn`-witness. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor

namespace EscapeCWSSPackage

/-- **Compose two escape-aware packages along a matching relation seam** `hRel` (discharged by
`rfl` when a chain uses named seam relations). The composed event is
`ChallengeTree.EscapeEvent.append`: the left event on the prefix tree, or the right event on the
suffix tree below some prefix leaf, at the verdict `L₁.isPure` computes there. Written infix as
`L₁ ▷ L₂` (explicit synonym `▷ₑ`). -/
def append {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isPure.is_pure.choose
  isPure := Verifier.IsPure.append L₁.verifier L₂.verifier L₁.isPure L₂.isPure
  extractor := fun stmt tree => L₁.extractor stmt tree.appendSplit.fst
  isCWSS := by
    have h₂ := L₂.isCWSS.toEscape
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.esc L₂.esc
      L₁.isPure.is_pure.choose L₁.isPure.is_pure.choose_spec L₁.extractor L₁.isCWSS h₂

end EscapeCWSSPackage

@[inherit_doc EscapeCWSSPackage.append]
scoped infixr:65 " ▷ₑ " => EscapeCWSSPackage.append

/-- A **guarded escape-aware CWSS package**: `EscapeCWSSPackage` with the purity witness relaxed
to a guardedness witness (the verifier may `failure` at runtime). -/
structure EscapeGCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier (which may reject at runtime). -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- The **escape event**: a trusted spec (see `ChallengeTree.EscapeEvent`). -/
  esc : ChallengeTree.EscapeEvent StmtIn pSpec (CWSSStructure.toShape struct).arity
  /-- The verifier is guarded by a deterministic Boolean check. -/
  isGuarded : verifier.IsGuarded
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` produces a `relIn`-witness. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor

namespace EscapeGCWSSPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Regard a pure escape-aware package as guarded, at the trivially-true check; every other field
carries over unchanged. Lossless. -/
def _root_.CoordinateWise.EscapeCWSSPackage.toGuarded
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (L : EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := L.esc
  isGuarded := Verifier.IsGuarded.of_isPure L.verifier L.isPure
  extractor := L.extractor
  isCWSS := L.isCWSS

/-- **Compose two guarded escape-aware packages along a matching relation seam.** As in
`EscapeCWSSPackage.append`, but the composed event is taken at the guard's output map `out₁`, which
`IsGuardedWith` leaves unconstrained on rejected prefixes — harmless, since escape events must be
honest at *all* `(stmt, tree)` pairs. Certificate:
`Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft` (sorried). Written infix
as `L₁ ▷ L₂` (explicit synonym `▷ₑᵍ`). -/
def append {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isGuarded.is_guarded.choose_spec.choose
  isGuarded := Verifier.IsGuarded.append L₁.verifier L₂.verifier L₁.isGuarded L₂.isGuarded
  extractor := fun stmt tree => L₁.extractor stmt tree.appendSplit.fst
  isCWSS := by
    have h₂ := L₂.isCWSS.toEscape
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct
      L₁.isGuarded.is_guarded.choose L₁.isGuarded.is_guarded.choose_spec.choose
      L₁.isGuarded.is_guarded.choose_spec.choose_spec
      L₁.esc L₂.esc L₁.extractor L₁.isCWSS h₂

end EscapeGCWSSPackage

@[inherit_doc EscapeGCWSSPackage.append]
scoped infixr:65 " ▷ₑᵍ " => EscapeGCWSSPackage.append

/-! ### Lifting escape-free packages into an escape chain

An escape-free package enters the escape world at the never-firing event `fun _ _ => False`, where
`Verifier.coordinateWiseSpecialSoundWith.withEscape` is the trivial `Or.inr`: extractor and
certificate are unchanged, and `coordinateWiseSpecialSoundWithEscape_false_iff` recovers the plain
notion exactly. Escape packages are therefore only *defined* for the subprotocols that genuinely
produce escapes; the mixed appends below (and the universal `▷`) insert the lifts on the fly. -/

section Lift

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Lift a pure escape-free package to the never-firing event; every other field carries over
unchanged. Lossless. -/
def CWSSPackage.toEscape
    (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isPure := L.isPure
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS

/-- Lift a guarded escape-free package to the never-firing event; every other field carries over
unchanged. Lossless. -/
def GCWSSPackage.toEscape
    (L : GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isGuarded := L.isGuarded
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS

end Lift

/-! ### The mixed appends

Every ordered pair of package kinds whose join is escape-aware (pure or guarded). Each lifts its
factors to the join and delegates, leaving only the relation seam `hRel` (discharged by `rfl`). All
are reached through the universal `▷` below; the escape-free appends live in `Package.lean`
(`CWSSPackage.append`) and `Guarded.lean` (`GCWSSPackage.append`, `CWSSPackage.appendGuarded`,
`GCWSSPackage.appendPure`). -/

section MixedAppend

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {StmtA WitA StmtB WitB StmtC WitC : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]

/-- **Pure escape-free ▷ pure escape-aware.** Lifts the left factor. -/
def CWSSPackage.appendEscape
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂ hRel

/-- **Pure escape-aware ▷ pure escape-free.** Lifts the right factor, so the composed event is
the left event on the prefix (its right disjunct never fires). -/
def EscapeCWSSPackage.appendPure
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape hRel

/-- **Pure escape-free ▷ guarded escape-aware.** Lifts the left factor twice. -/
def CWSSPackage.appendEscapeGuarded
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.toGuarded.append L₂ hRel

/-- **Guarded escape-aware ▷ pure escape-free.** Lifts the right factor twice. -/
def EscapeGCWSSPackage.appendPure
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape.toGuarded hRel

/-- **Guarded escape-free ▷ pure escape-aware.** Lifts the left factor to the never-event and the
right factor to the trivially-true guard. -/
def GCWSSPackage.appendEscape
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂.toGuarded hRel

/-- **Guarded escape-free ▷ guarded escape-aware.** Lifts the left factor to the never-event. -/
def GCWSSPackage.appendEscapeGuarded
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂ hRel

/-- **Pure escape-aware ▷ guarded escape-free.** Lifts the left factor to the trivially-true guard
and the right factor to the never-event. -/
def EscapeCWSSPackage.appendGuarded
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂.toEscape hRel

/-- **Pure escape-aware ▷ guarded escape-aware.** Lifts the left factor to the trivially-true
guard; both factors keep their own events. -/
def EscapeCWSSPackage.appendEscapeGuarded
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂ hRel

/-- **Guarded escape-aware ▷ guarded escape-free.** Lifts the right factor to the never-event. -/
def EscapeGCWSSPackage.appendGuarded
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toEscape hRel

/-- **Guarded escape-aware ▷ pure escape-aware.** Lifts the right factor to the trivially-true
guard; both factors keep their own events. -/
def EscapeGCWSSPackage.appendEscape
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toGuarded hRel

end MixedAppend

/-! ### The universal append `▷`

A single (scoped) elaborator rather than sixteen overloaded notations: `L₁ ▷ L₂` elaborates both
factors once, reads the head constant of their types to determine the package kinds, and applies
the unique append that composes them at their join. Overloaded-notation `choice` nodes would
re-elaborate nested alternatives once per outer candidate — exponential in chain length, and a
five-link Hachi chain already exhausts the heartbeat budget — whereas this dispatch is linear.
The kind-marked infixes `▷ₑ`, `▷ᵍ`, `▷ₑᵍ` remain as single-target explicit synonyms. -/

section UniversalAppend

open Lean Elab Term Meta

/-- The dispatch table of the universal append `▷`: the two factors' package kinds determine the
append that composes them at their join. -/
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
escape-aware, or both — at the join of their kinds, lifting each factor as needed. The relation
seam is discharged by `rfl`; for a non-definitional seam call the dispatched append (see
`univAppendFn`) explicitly with the seam proof. -/
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
