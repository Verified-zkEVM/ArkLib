/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Guarded verifiers and guarded CWSS composition (`GCWSSPackage`, `▷ᵍ`)

  **Skeleton of milestone B4** of the Hachi sumcheck track (see
  `HACHI_SUMCHECK_TRACK_PLAN.md` §2): coordinate-wise special soundness (CWSS) composition
  where the *left* factor may **reject at runtime**.

  ## Why guarded verifiers

  The existing composition machinery (`Verifier.append_coordinateWiseSpecialSound`,
  `CWSSPackage.append` = `▷`) requires the left verifier to be *pure*: its verdict is a
  deterministic total function of statement and transcript, with all acceptance conditions living
  in the output **relation**. This works whenever the data a check reads survives into the output
  statement (the `QuadEval` pattern). It fails exactly where a runtime check reads *sent or input*
  data that the downstream statement type **drops** — in Hachi:

  1. each sumcheck round's check `gᵢ(0) + gᵢ(1) = target` (the old target is dropped by the next
     round's statement) — [NOZ26] Figure 6;
  2. the final-evaluation check against the last sumcheck targets — [NOZ26] Figure 7 tail;
  3. the §4.5 recursion handoff's trace check (the next-iteration statement type is pinned to
     `QuadEvalStatement`, which cannot retain it).

  A **guarded** verifier `if check stmt tr then pure (out stmt tr) else failure` is the faithful
  model (`failure` is native: the verifier monad is `OptionT (OracleComp _)`). Its acceptance
  probability is `0` on the `failure` branch, so on an *accepting* tree every leaf has
  `check = true` — which is exactly the paper's "valid transcripts" premise, and which the
  guarded composition theorem below feeds to the left extraction.

  ## Contents

  * `Verifier.IsGuardedWith` / `Verifier.IsGuarded` — the guard predicate (`Bool`-valued check,
    design decision G3); purity is the `check := fun _ _ => true` special case
    (`IsGuarded.of_isPure`).
  * `Verifier.IsGuarded.append` — closure of guardedness under `Verifier.append` (**sorried**;
    B4.4: composite check `check₁ s tr.fst && check₂ (out₁ s tr.fst) tr.snd`, mirroring
    `Verifier.IsPure.append`).
  * `Verifier.append_coordinateWiseSpecialSound_of_guardedLeft` — the guarded binary CWSS append
    (**sorried**; B4.3: transplant of the pure proof with two deltas — (i) rewrite the composed
    run via a guarded `append_run` lemma and dismiss the `check = false` branch against
    acceptance-probability `1` vs `failure`'s probability `0`; (ii) certify left-leaf outputs in
    `rel₂.language` via a guarded `accepting_of_mem`).
  * `GCWSSPackage` — the guarded analogue of `CWSSPackage` (`isPure` ↝ `isGuarded`), with
    `CWSSPackage.toGuarded` and the composition `GCWSSPackage.append` = infix `▷ᵍ`.

  A guarded n-ary `seqCompose` variant (B4.4) is deliberately not skeletonized here: the Hachi
  composition builds its guarded loop by *recursion over binary `▷ᵍ`*
  (`ArkLib/Commitments/Functional/Hachi/Sumcheck/Rounds.lean`), which only needs the binary
  theorem.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- A verifier is **guarded with** a `Bool`-valued `check` and a deterministic output map `out` if
its verdict is `pure (out stmt tr)` when the check passes and `failure` otherwise. This is the
faithful model of a verifier that rejects at runtime (design decision G3 of the sumcheck-track
plan: `Bool`-valued checks; decidable-`Prop` consumers use `decide`). -/
def IsGuardedWith (V : Verifier oSpec StmtIn StmtOut pSpec)
    (check : StmtIn → FullTranscript pSpec → Bool)
    (out : StmtIn → FullTranscript pSpec → StmtOut) : Prop :=
  ∀ stmt tr, V.verify stmt tr = if check stmt tr then pure (out stmt tr) else failure

/-- A verifier is **guarded** if it is guarded with *some* check and output map. Purity is the
special case `check := fun _ _ => true` (`IsGuarded.of_isPure`). -/
class IsGuarded (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop where
  is_guarded : ∃ check out, V.IsGuardedWith check out

/-- Every pure verifier is guarded, with the trivially-true check. -/
theorem IsGuarded.of_isPure (V : Verifier oSpec StmtIn StmtOut pSpec) (h : V.IsPure) :
    V.IsGuarded := by
  obtain ⟨f, hf⟩ := h.is_pure
  exact ⟨fun _ _ => true, f, fun stmt tr => by simp [hf stmt tr]⟩

instance (V : Verifier oSpec StmtIn StmtOut pSpec) [h : V.IsPure] : V.IsGuarded :=
  IsGuarded.of_isPure V h

section Append

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- Guardedness is closed under `Verifier.append`: the composite check runs the left check on the
transcript prefix and, if it passes, the right check on the suffix from the left output.

**Sorried (B4.4).** Proof plan: mirror `Verifier.IsPure.append`
(`OracleReduction/Composition/Sequential/IsPure.lean`) — destructure both guard witnesses, take
`check := fun s tr => check₁ s tr.fst && check₂ (out₁ s tr.fst) tr.snd` and
`out := fun s tr => out₂ (out₁ s tr.fst) tr.snd`, and normalize
`Verifier.append`'s bind with `failure_bind`/`pure_bind` under the two `if`-splits. -/
theorem IsGuarded.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (h₁ : V₁.IsGuarded) (h₂ : V₂.IsGuarded) :
    (V₁.append V₂).IsGuarded := by
  sorry

/-- **Guarded binary CWSS append (skeleton of B4.3, the core of milestone B4).** Coordinate-wise
special soundness is preserved by `Verifier.append` when the left factor is merely *guarded*
(rather than pure).

**Sorried.** Proof plan (transplant of `Verifier.append_coordinateWiseSpecialSound`,
`Composition.lean`, with two deltas):
1. A guarded left-run lemma `append_run_guardedLeft`:
   `(V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) = if check₁ stmt tr₁ then V₂.run (out₁ stmt tr₁) tr₂
   else failure` (mirror of `append_run_pure_left`, plus `failure_bind`). On an accepting leaf
   (`Pr = 1`), the `check₁ = false` branch contradicts `failure`'s acceptance probability `0`
   (rejection lemma B4.1), so every surviving leaf has `check₁ = true` and the proof is literally
   the pure proof from there.
2. Where the pure proof certifies each left-leaf output in `rel₂.language` via
   `pure_accepting_of_mem`, use its guarded analogue fed by the `check₁ = true` fact from delta 1.
   (Each left leaf learns `check₁ = true` from *some* suffix transcript — the same nonemptiness
   the pure proof already extracts via `LeafPath.exists_of_mem_fullTranscripts`.)

The tree machinery (`appendSplit` and friends) is untouched. -/
theorem append_coordinateWiseSpecialSound_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (hV₁ : V₁.IsGuarded)
    (h₁ : V₁.coordinateWiseSpecialSound init impl D₁ rel₁ rel₂)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
    (V₁.append V₂).coordinateWiseSpecialSound init impl
      (CWSSStructure.append D₁ D₂) rel₁ rel₃ := by
  sorry

end Append

end Verifier

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled guarded coordinate-wise-special-sound reduction**: `CWSSPackage` with the purity
witness relaxed to a guardedness witness. Guarded packages compose with `GCWSSPackage.append`
(infix `▷ᵍ`); a pure package enters the guarded world via `CWSSPackage.toGuarded`. -/
structure GCWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier (may reject at runtime). -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- The verifier is guarded: its verdict is a deterministic function of statement and
  transcript behind a `Bool` check. Needed to place this package as the left factor of a guarded
  append. -/
  isGuarded : verifier.IsGuarded
  /-- The certificate: `verifier` is coordinate-wise special sound for `struct`, reducing `relIn`
  to `relOut`. -/
  isCWSS : verifier.coordinateWiseSpecialSound init impl struct relIn relOut

namespace GCWSSPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Forget purity: every (pure) `CWSSPackage` is a `GCWSSPackage` with the trivially-true
check. -/
def _root_.CoordinateWise.CWSSPackage.toGuarded
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  isGuarded := Verifier.IsGuarded.of_isPure L.verifier L.isPure
  isCWSS := L.isCWSS

/-- **Compose two guarded packages along a matching seam** (`hseam` discharged by `rfl`): the
guarded analogue of `CWSSPackage.append`/`▷`. The composed verdict is guarded by the conjunction
of both checks (`Verifier.IsGuarded.append`), and the composed certificate is the guarded binary
append theorem `Verifier.append_coordinateWiseSpecialSound_of_guardedLeft` (both currently
sorried B4 milestones — this definition is the *interface* the Hachi chain composes through).
Written infix as `L₁ ▷ᵍ L₂`. -/
def append {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hseam : L₁.relOut = L₂.relIn := by rfl) :
    GCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  isGuarded := Verifier.IsGuarded.append L₁.verifier L₂.verifier L₁.isGuarded L₂.isGuarded
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hseam] at h₂
    exact Verifier.append_coordinateWiseSpecialSound_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.isGuarded L₁.isCWSS h₂

end GCWSSPackage

@[inherit_doc GCWSSPackage.append]
scoped infixr:65 " ▷ᵍ " => GCWSSPackage.append

end CoordinateWise

end
