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
  compose freely. Two pure packages compose on the pure append theorem; a genuinely guarded factor
  moves the composite — visibly in its type — onto the guarded one. A composed event reads the left
  verdict map off `L₁.isPure.verify` / `L₁.isGuarded.out`, i.e. off *data*, which is what keeps a
  composed chain's extractor computable.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/


open OracleComp OracleSpec ProtocolSpec

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ## The escape-aware packages

The top half of the lattice: `EscapeCWSSPackage` and `EscapeGCWSSPackage` are `CWSSPackage` /
`GCWSSPackage` with one extra field, the escape event `esc`. `ChallengeTree.EscapeEvent.append`
takes the left verdict map as its index, and the packages carry that map as *data*, so a composed
`esc` reads `L₁.isPure.verify` (resp. `L₁.isGuarded.out`) rather than laundering it out of a `Prop`
with `Classical.choice`. -/

section CanonicalEscapePackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A **bundled escape-aware coordinate-wise-special-sound reduction**: `CWSSPackage` with one extra
field, the **escape event** `esc`. Its certificate `isCWSS` concludes `esc stmt tree ∨ extraction
succeeds` on every structured accepting tree, so `relIn`/`relOut` and `extractor` stay ordinary.

`esc` is a trusted specification — reading its definition is the reader's obligation, just as for
`relIn`/`relOut` (contract: `ChallengeTree.EscapeEvent`). -/
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
  /-- The verifier is pure, **with its verdict function as data**: composition reads that function
  both for the composed extractor and for the composed escape event. -/
  isPure : verifier.PureForm
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` succeeds on every valid leaf witnessing. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor

/-- A **guarded escape-aware CWSS package**: `EscapeCWSSPackage` with the purity witness relaxed to
a guardedness witness (the verifier may `failure` at runtime), again at the data form. -/
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
  /-- The verifier is guarded, **with its check and verdict map as data**. -/
  isGuarded : verifier.GuardedForm
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: on every structured accepting tree, either the tree exhibits the escape
  event `esc`, or `extractor` succeeds on every valid leaf witnessing. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWithEscape init impl struct esc
    relIn relOut verifier extractor

/-! ### The canonical lattice lifts -/

section CanonicalLift

variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Lift a pure escape-free package to the never-firing event; every other field carries over
unchanged. Lossless and computable. -/
def CWSSPackage.toEscape (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isPure := L.isPure
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS

/-- Lift a guarded escape-free package to the never-firing event. Lossless and computable. -/
def GCWSSPackage.toEscape (L : GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := fun _ _ => False
  isGuarded := L.isGuarded
  extractor := L.extractor
  isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ L.isCWSS

/-- Regard a pure escape-aware package as guarded, at the trivially-true check, via
`Verifier.PureForm.toGuardedForm`. Lossless and computable. -/
def EscapeCWSSPackage.toGuarded
    (L : EscapeCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    EscapeGCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  esc := L.esc
  isGuarded := L.isPure.toGuardedForm
  extractor := L.extractor
  isCWSS := L.isCWSS

end CanonicalLift

/-! ### The appends

The two same-kind escape-aware appends, then the ten mixed ones — each lifting its factors to the
join and delegating. The escape-free same-kind appends live in `Package.lean`
(`CWSSPackage.append`) and `Guarded.lean` (`GCWSSPackage.append`, `CWSSPackage.appendGuarded`,
`GCWSSPackage.appendPure`). -/

section CanonicalAppend

variable {StmtA WitA StmtB WitB StmtC WitC : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]

/-- **Compose two escape-aware packages along a matching relation seam.** The composed event is
`ChallengeTree.EscapeEvent.append` at `L₁.isPure.verify` — the left verdict map as *data*, no choice
laundering — and the composed extractor is `Extractor.TreeBased.append` at the same map. -/
def EscapeCWSSPackage.append
    (L₁ : EscapeCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isPure.verify
  isPure := L₁.isPure.append L₂.isPure
  extractor := L₁.extractor.append L₁.isPure.verify L₂.extractor
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.esc L₂.esc
      L₁.isPure.verify L₁.isPure.verify_eq L₁.extractor L₂.extractor L₁.isCWSS h₂

/-- **Compose two guarded escape-aware packages along a matching relation seam.** As in
`EscapeCWSSPackage.append`, but the event and the extractor are taken at the guard's output map
`L₁.isGuarded.out`, which `IsGuardedWith` leaves unconstrained on rejected prefixes — harmless,
since escape events must be honest at *all* `(stmt, tree)` pairs. The certificate is
`Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft`, its positivity hypothesis
discharged by `CWSSStructure.toShape_arity_pos`. -/
def EscapeGCWSSPackage.append
    (L₁ : EscapeGCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeGCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeGCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  esc := L₁.esc.append L₂.esc L₁.isGuarded.out
  isGuarded := L₁.isGuarded.append L₂.isGuarded
  extractor := L₁.extractor.append L₁.isGuarded.out L₂.extractor
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hRel] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct
      L₁.isGuarded.check L₁.isGuarded.out L₁.isGuarded.verify_eq
      (CWSSStructure.toShape_arity_pos L₂.struct)
      L₁.esc L₂.esc L₁.extractor L₂.extractor L₁.isCWSS h₂

/-- **Pure escape-free ▷ pure escape-aware.** Lifts the left factor. -/
def CWSSPackage.appendEscape
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : EscapeCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    EscapeCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toEscape.append L₂ hRel

/-- **Pure escape-aware ▷ pure escape-free.** Lifts the right factor. -/
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

/-- **Pure escape-aware ▷ guarded escape-aware.** Lifts the left factor to the trivially-true guard;
both factors keep their own events. -/
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

end CanonicalAppend

end CanonicalEscapePackage

@[inherit_doc EscapeCWSSPackage.append]
scoped infixr:65 " ▷ₑ " => EscapeCWSSPackage.append

@[inherit_doc EscapeGCWSSPackage.append]
scoped infixr:65 " ▷ₑᵍ " => EscapeGCWSSPackage.append

/-! ### The universal append `▷`

A single (scoped) elaborator rather than sixteen overloaded notations: `L₁ ▷ L₂` elaborates both
factors once, reads the head constant of their types to determine the package kinds, and applies
the unique append that composes them at their join. Overloaded-notation `choice` nodes would
re-elaborate nested alternatives once per outer candidate — exponential in chain length, and a
five-link Hachi chain already exhausts the heartbeat budget — whereas this dispatch is linear.
The kind-marked infixes `▷ₑ`, `▷ᵍ`, `▷ₑᵍ` remain as single-target explicit synonyms. -/

section UniversalAppend

open Lean Elab Term Meta

/-- The dispatch table of the universal append `▷` over the **canonical** package kinds: the two
factors' kinds determine the append that composes them at their join. -/
private def canonAppendFn : Name → Name → Option Name
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

/-- Apply a named append to two elaborated factors. -/
private def applyAppend (fn : Name) (lE rE : Expr) : TermElabM Expr := do
  let f ← mkConstWithFreshMVarLevels fn
  elabAppArgs f #[] #[.expr lE, .expr rE] (expectedType? := none)
    (explicit := false) (ellipsis := false)

/-- **The universal package append.** `L₁ ▷ L₂` composes any two CWSS packages — pure, guarded,
escape-aware, or both — at the join of their kinds, lifting each factor as needed. The relation
seam is discharged by `rfl`; for a non-definitional seam call the dispatched append (see
`canonAppendFn`) explicitly with the seam proof.

Dispatch is by kind, and deterministic: the two factors' kinds index `canonAppendFn`, the single
dispatch table. -/
scoped elab:65 l:term:66 " ▷ " r:term:65 : term => do
  let lE ← elabTerm l none
  let rE ← elabTerm r none
  let lN ← packageKindOf lE
  let rN ← packageKindOf rE
  let some fn := canonAppendFn lN rN
    | throwError "▷: no package append composes `{lN}` with `{rN}`"
  applyAppend fn lE rE

end UniversalAppend

end CoordinateWise
