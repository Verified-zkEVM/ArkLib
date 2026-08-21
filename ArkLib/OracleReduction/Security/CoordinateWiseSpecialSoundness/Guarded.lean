/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Guarded verifiers and guarded CWSS composition (`GCWSSPackage`)

  **Skeleton** of coordinate-wise special soundness (CWSS) composition where the *left* factor may
  **reject at runtime**, as needed by the Hachi sumcheck ([NOZ26]); inventoried as *generic
  machinery* in `Commitments/Functional/Hachi/Composition.lean`.

  ## Why guarded verifiers

  The pure composition machinery (`Verifier.append_coordinateWiseSpecialSoundWith`,
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

  * `Verifier.IsGuardedWith` / `Verifier.IsGuarded` — the guard predicate (`Bool`-valued check);
    purity is the `check := fun _ _ => true` special case
    (`IsGuarded.of_isPure`).
  * `Verifier.GuardedForm` — guardedness with its check and verdict map as **data** (the guarded
    mirror of `Verifier.PureForm`), with `GuardedForm.isGuarded` forgetting back to the class and
    `PureForm.toGuardedForm` the data form of `IsGuarded.of_isPure`. A guarded package carries this,
    since its composed escape event must *name* the left verdict map.
  * `Verifier.GuardedForm.append` — closure of guardedness **data** under `Verifier.append`:
    composite check `check₁ s tr.fst && check₂ (out₁ s tr.fst) tr.snd`, mirroring
    `Verifier.PureForm.append`. Its `verify_eq` is the file's one remaining **sorry**;
    `Verifier.IsGuarded.append` is the forgetful corollary.
  * `Verifier.append_treeSpecialSoundWith_guardedLeft` / `…WithEscape_guardedLeft` and their CWSS
    wrappers `Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft` / `…WithEscape…` — the
    guarded binary appends at the witness-only extractor, **proved**. The guarded seam lemmas they
    run on (`append_run_guardedLeft`, `append_run_outputs_guardedLeft`,
    `outputs_guarded_subsingleton`, `guarded_accepting_of_mem`, `guarded_verdict_mem_outputs`) live
    here too, since they mention `IsGuardedWith`.
  * `GCWSSPackage` — the guarded analogue of `CWSSPackage` (`isPure` ↝ `isGuarded`, at the data
    form), with `CWSSPackage.toGuarded`, the composition `GCWSSPackage.append` = infix `▷` (explicit
    synonym `▷ᵍ`), and the two mixed appends `CWSSPackage.appendGuarded` /
    `GCWSSPackage.appendPure`.

  As everywhere in the CWSS development, composition here is **binary only**: the Hachi composition
  builds its guarded loop by *recursion over the binary guarded append*
  (`ArkLib/Commitments/Functional/Hachi/Sumcheck/Rounds.lean`), so no `n`-ary guarded variant is
  needed (nor does an `n`-ary CWSS composition exist to mirror).

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/


open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- A verifier is **guarded with** a `Bool`-valued `check` and a deterministic output map `out` if
its verdict is `pure (out stmt tr)` when the check passes and `failure` otherwise. This is the
faithful model of a verifier that rejects at runtime (the check is `Bool`-valued; decidable-`Prop`
consumers use `decide`). -/
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

/-- Every pure verifier is guarded automatically: the instance form of `IsGuarded.of_isPure`. -/
instance (V : Verifier oSpec StmtIn StmtOut pSpec) [h : V.IsPure] : V.IsGuarded :=
  IsGuarded.of_isPure V h

/-- A **guardedness witness carrying check and output map as data**: the bundled form of
`Verifier.IsGuardedWith`, and the guarded mirror of `Verifier.PureForm`.

As for purity, the `IsGuarded` *class* only asserts that some `(check, out)` pair exists, so
reading `out` off it costs `Classical.choice`. A guarded package carries this data instead, since
its composed escape event and extractor must *name* the left verdict map `out`. -/
structure GuardedForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The runtime guard. -/
  check : StmtIn → FullTranscript pSpec → Bool
  /-- The verdict where the guard passes. -/
  out : StmtIn → FullTranscript pSpec → StmtOut
  /-- The verifier is guarded with exactly these. -/
  verify_eq : V.IsGuardedWith check out

/-- Forget the data: a `Verifier.GuardedForm` yields the `Verifier.IsGuarded` class. -/
theorem GuardedForm.isGuarded {V : Verifier oSpec StmtIn StmtOut pSpec} (G : V.GuardedForm) :
    V.IsGuarded :=
  ⟨G.check, G.out, G.verify_eq⟩

/-- Every pure form is a guarded form, at the trivially-true check: the data form of
`Verifier.IsGuarded.of_isPure`. Lossless, and computable — the verdict function carries over. -/
def PureForm.toGuardedForm {V : Verifier oSpec StmtIn StmtOut pSpec} (P : V.PureForm) :
    V.GuardedForm where
  check := fun _ _ => true
  out := P.verify
  verify_eq := fun stmt tr => by rw [P.verify_eq stmt tr]; simp

section GuardedFormAppend

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- **Guardedness data composes computably**: the composed guard runs the left check on the
transcript prefix and, if it passes, the right check on the suffix from the statement the left
verifier outputs at the seam; the composed verdict is the right verdict there. The guarded mirror of
`Verifier.PureForm.append`, and transcript-level in the same way — the seam is `tr.fst`/`tr.snd`,
with no challenge-tree path machinery.

The data half is what a guarded package needs: its composed escape event and extractor must *name*
the left verdict map, and reading one off the `IsGuarded` class would cost `Classical.choice`.

`verify_eq` normalizes `Verifier.append`'s bind under the two `if`-splits, mirroring
`Verifier.PureForm.append`; `Verifier.IsGuarded.append` is proved from it by forgetting the
data. -/
def GuardedForm.append {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂} (G₁ : V₁.GuardedForm) (G₂ : V₂.GuardedForm) :
    (V₁.append V₂).GuardedForm where
  check := fun stmt tr => G₁.check stmt tr.fst && G₂.check (G₁.out stmt tr.fst) tr.snd
  out := fun stmt tr => G₂.out (G₁.out stmt tr.fst) tr.snd
  verify_eq := fun stmt tr => by
    simp only [Verifier.append]
    rw [G₁.verify_eq stmt tr.fst]
    by_cases hc₁ : G₁.check stmt tr.fst = true
    · rw [if_pos hc₁, pure_bind, G₂.verify_eq (G₁.out stmt tr.fst) tr.snd]
      by_cases hc₂ : G₂.check (G₁.out stmt tr.fst) tr.snd = true <;> simp [hc₁, hc₂]
    · rw [if_neg hc₁]
      simp [hc₁]

/-- Guardedness is closed under `Verifier.append`: forget the data of `GuardedForm.append`. -/
theorem IsGuarded.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (h₁ : V₁.IsGuarded) (h₂ : V₂.IsGuarded) :
    (V₁.append V₂).IsGuarded :=
  (GuardedForm.append ⟨_, _, h₁.is_guarded.choose_spec.choose_spec⟩
    ⟨_, _, h₂.is_guarded.choose_spec.choose_spec⟩).isGuarded

end GuardedFormAppend

section Append

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-! ### The guarded seam at the witness-only extractor

Five lemmas replay the pure seam of `Composition.lean` for a guarded left factor, each conditioned
on the guard passing: `append_run_guardedLeft` is `append_run_pure_left` behind an `if`,
`append_run_outputs_guardedLeft` and `guarded_verdict_mem_outputs` are its `Verifier.Outputs`-level
consequences, `outputs_guarded_subsingleton` pins the output set (the rejecting branch reaches no
statement at all), and `guarded_accepting_of_mem` is `pure_accepting_of_mem` where the check passes.

With those, the guarded composition theorems are the pure skeleton with **one move in front**: on an
accepting composed tree every prefix guard must already pass (`hcheck`), learned by exhibiting one
suffix leaf — which is what `ChallengeTree.somePath` supplies and what the `harity₂` hypothesis
buys. `Verifier.not_accepting_of_failure` then refutes the rejecting branch. -/

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- Running an appended verifier whose left factor is **guarded**: the composed run is the right
verifier's at the left verdict where the left check passes, and `failure` where it does not. The
guarded analogue of `append_run_pure_left`. -/
theorem append_run_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
      (V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) =
        if check₁ stmt tr₁ then V₂.run (out₁ stmt tr₁) tr₂ else failure := by
  rw [Verifier.append_run]
  simp only [Verifier.run, FullTranscript.append_fst, FullTranscript.append_snd, hV₁ stmt tr₁]
  by_cases hc : check₁ stmt tr₁ <;> simp [hc]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- On a guarded left factor with a **passing** guard, the appended verifier's reachable outputs at
a glued transcript are the right verifier's at the left verdict: the guarded analogue of
`append_run_outputs`, and the lemma that transfers leaf-witnessing validity across a guarded
seam. -/
theorem append_run_outputs_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript)
    (hc : check₁ stmt tr₁ = true) :
      Outputs init impl (V₁.append V₂) stmt (tr₁ ++ₜ tr₂)
        = Outputs init impl V₂ (out₁ stmt tr₁) tr₂ := by
  unfold Outputs
  rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt tr₁ tr₂, if_pos hc]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- A guarded verifier's reachable outputs pin **both** the guard and the verdict: any reachable
output is the verdict, and where the guard fails nothing is reachable at all. The guarded analogue
of `outputs_pure_subsingleton`. -/
theorem outputs_guarded_subsingleton
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) {out : Stmt₂}
    (hout : out ∈ Outputs init impl V₁ stmt tr) : out = out₁ stmt tr := by
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV₁ stmt tr] at hout
  by_cases hc : check₁ stmt tr
  · rw [if_pos hc] at hout
    have : (do (simulateQ impl
        (pure (out₁ stmt tr) : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
        ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some (out₁ stmt tr))) := by
      congr 1
    rw [this] at hout
    simp only [support_bind_const, support_pure, Set.mem_setOf_eq] at hout
    exact Option.some.inj hout.1
  · rw [if_neg (by simpa using hc)] at hout
    have : (do (simulateQ impl (failure : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
        ProbComp (Option Stmt₂)) = (init >>= fun _ => pure none) := by
      congr 1
    rw [this] at hout
    simp only [support_bind_const, support_pure, Set.mem_setOf_eq] at hout
    exact absurd hout.1 (by simp)

/-- A guarded verifier accepts a transcript whose verdict lies in the language, **provided its guard
passes**: `pure_accepting_of_mem` fed the passing branch of `IsGuardedWith`. -/
theorem guarded_accepting_of_mem
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (hc : check₁ stmt tr = true)
    (lang : Set Stmt₂) (hmem : out₁ stmt tr ∈ lang) :
      Pr[ (· ∈ lang) |
        OptionT.mk do (simulateQ impl (V₁.run stmt tr)).run' (← init)] = 1 :=
  Verifier.pure_accepting_of_mem init impl V₁ stmt tr lang (out₁ stmt tr)
    (by rw [hV₁ stmt tr, if_pos hc]) hmem

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- A guarded verifier's verdict **is** reachable where its check passes, as soon as the sampling
can produce a seed: the guarded analogue of `pure_verdict_mem_outputs`, and what makes a composed
prefix witnessing valid across a guarded seam. -/
theorem guarded_verdict_mem_outputs
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (hinit : (support init).Nonempty)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (hc : check₁ stmt tr = true) :
      out₁ stmt tr ∈ Outputs init impl V₁ stmt tr := by
  obtain ⟨s, hs⟩ := hinit
  simp only [Outputs, Set.mem_setOf_eq, Verifier.run, hV₁ stmt tr]
  rw [if_pos hc]
  have heq : (do (simulateQ impl
      (pure (out₁ stmt tr) : OptionT (OracleComp oSpec) Stmt₂)).run' (← init) :
      ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some (out₁ stmt tr))) := by
    congr 1
  rw [heq]
  exact (mem_support_bind_iff init _ _).2 ⟨s, hs, (mem_support_pure_iff _ _).2 rfl⟩

section GuardedAppend

open ProtocolSpec.ChallengeTree

/-- **The guarded-left composition of tree special soundness**, at the witness-only extractor. The
left factor may reject at runtime; its guard data `(check₁, out₁)` is explicit, because the composed
extractor `Extractor.TreeBased.append out₁ E₁ E₂` names the verdict map.

`hcheck` — every prefix guard passes on an accepting composed tree — comes first, learned from one
`ChallengeTree.somePath` suffix leaf (whence `harity₂`); the rest is
`append_treeSpecialSoundWith`'s skeleton with the pure seam lemmas replaced by their guarded
analogues. -/
theorem append_treeSpecialSoundWith_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < S₂.arity i)
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWith init impl S₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWith init impl S₂ rel₂ rel₃ V₂ E₂) :
      treeSpecialSoundWith init impl (S₁.append S₂) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append out₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  -- Every prefix guard passes: otherwise the composed run at one suffix leaf is `failure`, which
  -- cannot be accepted with probability one.
  have hcheck : ∀ p₁ : LeafPath tree.appendSplit.fst,
      check₁ stmt p₁.fullTranscript = true := by
    intro p₁
    by_contra hc
    have hpath₂ := ChallengeTree.somePath harity₂ (tree.appendSplit.sndAt p₁)
    have hmem : p₁.fullTranscript ++ₜ hpath₂.fullTranscript ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁
        hpath₂.mem_fullTranscripts
    exact not_accepting_of_failure
      (V := V₁.append V₂) (stmt := stmt)
      (tr := p₁.fullTranscript ++ₜ hpath₂.fullTranscript)
      (by
        have h := append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt p₁.fullTranscript
          hpath₂.fullTranscript
        rw [if_neg hc] at h
        exact h)
      (hAccept _ hmem)
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (out₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    rw [show (V₁.append V₂).run stmt (p₁.fullTranscript ++ₜ tr₂)
        = V₂.run (out₁ stmt p₁.fullTranscript) tr₂ from by
      rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁, if_pos (hcheck p₁)]] at hfull
    exact hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ∃ w₂, (out₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
    intro p₁
    obtain ⟨w₂, -, hw₂⟩ := h₂' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
    exact ⟨w₂, hw₂⟩
  have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
    intro tr₁ htr₁
    obtain ⟨p₁, rfl⟩ :=
      ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
    obtain ⟨w₂, hw₂⟩ := key0 p₁
    exact guarded_accepting_of_mem init impl V₁ check₁ out₁ hV₁ stmt p₁.fullTranscript
      (hcheck p₁) rel₂.language ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
  intro o hvalid
  have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ChallengeTree.LeafWitnesses.IsValid init impl V₂ rel₃ (out₁ stmt p₁.fullTranscript)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
    intro p₁ p₂
    obtain ⟨w, hw, out, hout, hrel⟩ :=
      hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
    refine ⟨w, hw, out, ?_, hrel⟩
    have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
        (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
        check₁ stmt q₁.fullTranscript = true →
        out ∈ Outputs init impl (V₁.append V₂) stmt
          (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
        out ∈ Outputs init impl V₂ (out₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
      intro T q₁ q₂ hcq h
      rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
      rwa [append_run_outputs_guardedLeft init impl V₁ V₂ check₁ out₁ hV₁ stmt _ _ hcq] at h
    exact key tree p₁ p₂ (hcheck p₁) hout
  have hpreValid : ChallengeTree.LeafWitnesses.IsValid init impl V₁ rel₂ stmt
      (fun p₁ => E₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
    intro p₁
    obtain ⟨w₂, hw₂, hrel₂⟩ := h₂' p₁ _ (hsuffValid p₁)
    exact ⟨w₂, hw₂, out₁ stmt p₁.fullTranscript,
      guarded_verdict_mem_outputs init impl V₁ check₁ out₁ hV₁
        (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript (hcheck p₁),
      hrel₂⟩
  exact h₁ stmt tree.appendSplit.fst
    (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc _ hpreValid

/-- **The escape-threaded guarded-left composition of tree special soundness**, at the witness-only
extractor and the UNCHANGED `ChallengeTree.EscapeEvent.append` (taken at the guard's output map
`out₁`, which `IsGuardedWith` leaves unconstrained on rejected prefixes — harmless, since escape
events must be honest at *all* `(stmt, tree)` pairs).

This is the development's fundamental composition obligation for guarded left factors. On an
accepting composed tree `hcheck` forces every prefix guard to pass, after which the escape routing
is `append_treeSpecialSoundWithEscape`'s, at the guarded seam lemmas. -/
theorem append_treeSpecialSoundWithEscape_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < S₂.arity i)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWithEscape init impl S₂ esc₂ rel₂ rel₃ V₂ E₂) :
      treeSpecialSoundWithEscape init impl (S₁.append S₂)
        (ChallengeTree.EscapeEvent.append esc₁ esc₂ out₁) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append out₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  have hcheck : ∀ p₁ : LeafPath tree.appendSplit.fst,
      check₁ stmt p₁.fullTranscript = true := by
    intro p₁
    by_contra hc
    have hpath₂ := ChallengeTree.somePath harity₂ (tree.appendSplit.sndAt p₁)
    have hmem : p₁.fullTranscript ++ₜ hpath₂.fullTranscript ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁
        hpath₂.mem_fullTranscripts
    exact not_accepting_of_failure
      (V := V₁.append V₂) (stmt := stmt)
      (tr := p₁.fullTranscript ++ₜ hpath₂.fullTranscript)
      (by
        have h := append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt p₁.fullTranscript
          hpath₂.fullTranscript
        rw [if_neg hc] at h
        exact h)
      (hAccept _ hmem)
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (out₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    rw [show (V₁.append V₂).run stmt (p₁.fullTranscript ++ₜ tr₂)
        = V₂.run (out₁ stmt p₁.fullTranscript) tr₂ from by
      rw [append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁, if_pos (hcheck p₁)]] at hfull
    exact hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  by_cases hesc₂ : ∃ p₁ : LeafPath tree.appendSplit.fst,
      esc₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
  · exact Or.inl (Or.inr hesc₂)
  · push Not at hesc₂
    have h₂'' := fun p₁ : LeafPath tree.appendSplit.fst => (h₂' p₁).resolve_left (hesc₂ p₁)
    have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
        ∃ w₂, (out₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
      intro p₁
      obtain ⟨w₂, -, hw₂⟩ := h₂'' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
      exact ⟨w₂, hw₂⟩
    have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨p₁, rfl⟩ :=
        ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
      obtain ⟨w₂, hw₂⟩ := key0 p₁
      exact guarded_accepting_of_mem init impl V₁ check₁ out₁ hV₁ stmt p₁.fullTranscript
        (hcheck p₁) rel₂.language ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
    rcases h₁ stmt tree.appendSplit.fst
      (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc with
      hesc₁ | hext₁
    · exact Or.inl (Or.inl hesc₁)
    · refine Or.inr fun o hvalid => ?_
      have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
          ChallengeTree.LeafWitnesses.IsValid init impl V₂ rel₃ (out₁ stmt p₁.fullTranscript)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
        intro p₁ p₂
        obtain ⟨w, hw, out, hout, hrel⟩ :=
          hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
        refine ⟨w, hw, out, ?_, hrel⟩
        have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
            (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
            check₁ stmt q₁.fullTranscript = true →
            out ∈ Outputs init impl (V₁.append V₂) stmt
              (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
            out ∈ Outputs init impl V₂ (out₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
          intro T q₁ q₂ hcq h
          rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
          rwa [append_run_outputs_guardedLeft init impl V₁ V₂ check₁ out₁ hV₁ stmt _ _ hcq]
            at h
        exact key tree p₁ p₂ (hcheck p₁) hout
      have hpreValid : ChallengeTree.LeafWitnesses.IsValid init impl V₁ rel₂ stmt
          (fun p₁ => E₂ (out₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
        intro p₁
        obtain ⟨w₂, hw₂, hrel₂⟩ := h₂'' p₁ _ (hsuffValid p₁)
        exact ⟨w₂, hw₂, out₁ stmt p₁.fullTranscript,
          guarded_verdict_mem_outputs init impl V₁ check₁ out₁ hV₁
            (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript
            (hcheck p₁), hrel₂⟩
      exact hext₁ _ hpreValid

/-- **Guarded binary CWSS append at the witness-only extractor, plain form.** The CWSS-shape wrapper
of `append_treeSpecialSoundWith_guardedLeft`, transported across `CWSSStructure.toShape_append` by
`treeSpecialSoundWith_congr`.

The guard data is taken explicitly rather than as the bare `V₁.IsGuarded`, since the composed
extractor names `out₁`; and the positivity hypothesis `harity₂` is carried here, discharged at every
CWSS call site by `CWSSStructure.toShape_arity_pos`. -/
theorem append_coordinateWiseSpecialSoundWith_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < (CWSSStructure.toShape D₂).arity i)
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (h₁ : coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ V₁ E₁)
    (h₂ : coordinateWiseSpecialSoundWith init impl D₂ rel₂ rel₃ V₂ E₂) :
      coordinateWiseSpecialSoundWith init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append out₁ E₁ E₂) :=
  treeSpecialSoundWith_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm HEq.rfl
    (append_treeSpecialSoundWith_guardedLeft init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) check₁ out₁ hV₁ harity₂ E₁ E₂ h₁ h₂)

/-- **Guarded binary CWSS append at the witness-only extractor, escape-threaded form** — the
CWSS-shape wrapper of `append_treeSpecialSoundWithEscape_guardedLeft`, and the development's
fundamental guarded obligation, of which the plain form above is the never-firing corollary. Both
the extractor and the event cross `CWSSStructure.toShape_append` by `HEq.rfl`. -/
theorem append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (harity₂ : ∀ i, 0 < (CWSSStructure.toShape D₂).arity i)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (h₁ : coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : coordinateWiseSpecialSoundWithEscape init impl D₂ esc₂ rel₂ rel₃ V₂ E₂) :
      coordinateWiseSpecialSoundWithEscape init impl
        (CWSSStructure.append D₁ D₂) (esc₁.append esc₂ out₁) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append out₁ E₁ E₂) :=
  treeSpecialSoundWithEscape_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm
    HEq.rfl HEq.rfl
    (append_treeSpecialSoundWithEscape_guardedLeft init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) check₁ out₁ hV₁ harity₂
      esc₁ esc₂ E₁ E₂ h₁ h₂)

end GuardedAppend

end Append

end Verifier

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ## The guarded package

`GCWSSPackage` is `CWSSPackage` with the purity field relaxed to guardedness — and, like it, at the
*data* form: `isGuarded : verifier.GuardedForm`. The composed extractor and escape event both name
the left verdict map, which is read off that field as `L₁.isGuarded.out`.

A pure `CWSSPackage` enters the guarded world losslessly (`CWSSPackage.toGuarded`: the guard is the
trivially-true check and the certificate is unchanged). The mixed appends below insert this lift
automatically, so guarded packages need only be *defined* for the subprotocols whose checks
genuinely reject at runtime. Together with the escape-lifting appends in `Escape.lean`, every
ordered pair of package kinds (escape? × guarded?) composes at its join through the universal `▷`
elaborator defined in `Escape.lean`: two pure packages compose pure (staying on the pure append
theorem), while a single guarded factor moves the composite — visibly in its type — onto the guarded
append theorem. -/

section CanonicalPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A **bundled guarded coordinate-wise-special-sound reduction**: `CWSSPackage` with the purity
witness relaxed to a guardedness witness carrying its check and verdict map as data
(`Verifier.GuardedForm`). Compose with `GCWSSPackage.append` / the universal `▷`; a pure package
enters the guarded world via `CWSSPackage.toGuarded`. -/
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
  /-- The verifier is guarded, **with its check and verdict map as data**: composition reads the
  verdict map here, both for the composed extractor and for the composed escape event. -/
  isGuarded : verifier.GuardedForm
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn WitOut pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: `extractor` witnesses that `verifier` is coordinate-wise special sound
  for `struct`, reducing `relIn` to `relOut`. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWith init impl struct relIn relOut verifier
    extractor

namespace GCWSSPackage

/-- Forget purity: every pure `CWSSPackage` is a `GCWSSPackage` at the trivially-true check, via
`Verifier.PureForm.toGuardedForm` — which carries the verdict function over as data, so the lift is
lossless *and* computable. -/
def _root_.CoordinateWise.CWSSPackage.toGuarded
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  isGuarded := L.isPure.toGuardedForm
  extractor := L.extractor
  isCWSS := L.isCWSS

/-- **Compose two guarded packages along a matching seam** — the guarded canonical `▷`. The seam
verdict is `L₁.isGuarded.out`, the guard data composes by `Verifier.GuardedForm.append`, and the
certificate is `Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft`, whose positivity
hypothesis is discharged by `CWSSStructure.toShape_arity_pos` — every CWSS shape branches. -/
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
  isGuarded := L₁.isGuarded.append L₂.isGuarded
  extractor := L₁.extractor.append L₁.isGuarded.out L₂.extractor
  isCWSS := by
    have h₂ := L₂.isCWSS
    rw [← hseam] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct
      L₁.isGuarded.check L₁.isGuarded.out L₁.isGuarded.verify_eq
      (CWSSStructure.toShape_arity_pos L₂.struct) L₁.extractor L₂.extractor L₁.isCWSS h₂

end GCWSSPackage

@[inherit_doc GCWSSPackage.append]
scoped infixr:65 " ▷ᵍ " => GCWSSPackage.append

/-- **Pure ▷ guarded** (canonical): lift the left factor with `CWSSPackage.toGuarded`. -/
def CWSSPackage.appendGuarded {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    GCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂ hRel

/-- **Guarded ▷ pure** (canonical): lift the right factor with `CWSSPackage.toGuarded`. -/
def GCWSSPackage.appendPure {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    GCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toGuarded hRel

end CanonicalPackage

end CoordinateWise
