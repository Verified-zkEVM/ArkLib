/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Guarded verifiers and guarded CWSS composition (`GCWSSPackage`)

  Coordinate-wise special soundness (CWSS) composition where the *left* factor may **reject at
  runtime**, as needed by the Hachi sumcheck ([NOZ26]).

  ## Why guarded verifiers

  The existing composition machinery (`Verifier.append_coordinateWiseSpecialSoundWith`,
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
  * `Verifier.IsGuarded.append` — closure of guardedness under `Verifier.append`: composite check
    `check₁ s tr.fst && check₂ (out₁ s tr.fst) tr.snd`, mirroring `Verifier.IsPure.append`.
  * `Verifier.append_run_guardedLeft` — the guarded twin of `append_run_pure_left`: the composite
    run is `failure` on a rejected prefix and the right run at the left verdict otherwise.
  * `Verifier.append_treeSpecialSoundWithEscape_of_guardedLeft` and its CWSS-shape wrapper
    `Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft` — the escape-threaded
    guarded binary append, the *fundamental* obligation here, stated at explicit guard data since
    the composed escape event must name the left verdict map. The one step the pure proof does not
    have is that every prefix leaf passes `check₁`: a rejected prefix would make the composite
    `failure` on some full transcript through it (`Verifier.not_accepting_of_verify_failure`,
    `Composition.lean`), and the witnessing suffix transcript comes from
    `ChallengeTree.LeafPath.some` at the right shape's positive arity
    (`CWSSStructure.arity_pos`).
  * `Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft` — the plain guarded append,
    **proven** as a corollary of the escape-threaded one at the never-firing events.
  * `GCWSSPackage` — the guarded analogue of `CWSSPackage` (`isPure` ↝ `isGuarded`), with
    `CWSSPackage.toGuarded` and the composition `GCWSSPackage.append` = infix `▷`
    (explicit synonym `▷ᵍ`).

  As everywhere in the CWSS development, composition here is **binary only**: the Hachi composition
  builds its guarded loop by *recursion over the binary guarded append*
  (`ArkLib/Commitments/Functional/Hachi/Sumcheck/Rounds.lean`), so no `n`-ary guarded variant is
  needed (nor does an `n`-ary CWSS composition exist to mirror).

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

section Append

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- Guardedness is closed under `Verifier.append`: the composite check runs the left check on the
transcript prefix and, if it passes, the right check on the suffix from the left output — so the
composite rejects exactly when either factor does. The mirror of `Verifier.IsPure.append`. -/
theorem IsGuarded.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (h₁ : V₁.IsGuarded) (h₂ : V₂.IsGuarded) :
    (V₁.append V₂).IsGuarded := by
  obtain ⟨check₁, out₁, hV₁⟩ := h₁.is_guarded
  obtain ⟨check₂, out₂, hV₂⟩ := h₂.is_guarded
  refine ⟨fun stmt tr => check₁ stmt tr.fst && check₂ (out₁ stmt tr.fst) tr.snd,
    fun stmt tr => out₂ (out₁ stmt tr.fst) tr.snd, fun stmt tr => ?_⟩
  simp only [Verifier.append]
  rw [hV₁ stmt tr.fst]
  by_cases hc₁ : check₁ stmt tr.fst = true
  · rw [if_pos hc₁, pure_bind, hV₂ (out₁ stmt tr.fst) tr.snd]
    by_cases hc₂ : check₂ (out₁ stmt tr.fst) tr.snd = true <;> simp [hc₁, hc₂]
  · rw [if_neg hc₁]
    simp [hc₁]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- **Running an append with a guarded left factor.** The guarded twin of
`Verifier.append_run_pure_left`: on a prefix the left check rejects, the whole composite is
`failure`; otherwise it is the right verifier run at the left verdict. This is the lemma that
turns "the composite tree is accepting" into the two facts the guarded append needs — that every
surviving prefix passes `check₁`, and that the suffix subtree is accepting for `V₂` at
`out₁ stmt tr₁`. -/
theorem append_run_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt₁ : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
      (V₁.append V₂).run stmt₁ (tr₁ ++ₜ tr₂) =
        if check₁ stmt₁ tr₁ then V₂.run (out₁ stmt₁ tr₁) tr₂ else failure := by
  simp only [Verifier.append_run, Verifier.run, ProtocolSpec.FullTranscript.append_fst,
    ProtocolSpec.FullTranscript.append_snd]
  rw [hV₁ stmt₁ tr₁]
  by_cases hc : check₁ stmt₁ tr₁ = true
  · rw [if_pos hc, if_pos hc, pure_bind]
  · rw [if_neg hc, if_neg hc]
    simp

/-- A verifier run equal to `failure` cannot be accepted into any language. -/
theorem failure_not_accepting
    {pSpec : ProtocolSpec n} (V : Verifier oSpec Stmt₁ Stmt₂ pSpec)
    (stmt : Stmt₁) (tr : pSpec.FullTranscript) (lang : Set Stmt₂)
    (hrun : V.run stmt tr = (failure : OptionT (OracleComp oSpec) Stmt₂))
    (hAccept : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) :
    False := by
  have hzero : Pr[(· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 0 := by
    rw [hrun, probEvent_eq_zero_iff]
    intro x hx _
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ impl (pure none : OracleComp oSpec (Option Stmt₂))) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure none : StateT σ ProbComp (Option Stmt₂)).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure] at hx
  rw [hzero] at hAccept
  exact zero_ne_one hAccept

/-- Acceptance into any language forces a guarded verifier's check to pass. -/
theorem check_eq_true_of_guarded_accepting
    {pSpec : ProtocolSpec n} (V : Verifier oSpec Stmt₁ Stmt₂ pSpec)
    (check : Stmt₁ → pSpec.FullTranscript → Bool)
    (out : Stmt₁ → pSpec.FullTranscript → Stmt₂)
    (hV : V.IsGuardedWith check out) (stmt : Stmt₁) (tr : pSpec.FullTranscript)
    (lang : Set Stmt₂)
    (hAccept : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) :
    check stmt tr = true := by
  by_contra hcheck
  have hfalse : check stmt tr = false := Bool.eq_false_of_not_eq_true hcheck
  unfold IsGuardedWith at hV
  apply failure_not_accepting init impl V stmt tr lang ?_ hAccept
  change V.verify stmt tr = failure
  rw [hV stmt tr, hfalse]
  simp

/-- **Guarded binary CWSS append, escape-threaded named form.** Escape-threaded CWSS is
preserved by `Verifier.append` when the left factor is merely *guarded* rather than pure, at the
same composed extractor and event as the pure append.

Stated at **explicit guard data** `(check₁, out₁, hV₁)` rather than at the bare `V₁.IsGuarded`,
because the composed event has to *name* the left verdict map `out₁`. On rejected prefixes `out₁` is
unconstrained by `IsGuardedWith`, so the composed event may evaluate `esc₂` at junk intermediate
statements — harmless, since escape events must be honest breaks at *all* `(stmt, tree)` pairs.

The proof follows `Verifier.append_treeSpecialSoundWithEscape` (`Composition.lean`) — the
disjunction is handled exactly as there — with one step the pure argument does not need: every
prefix leaf is shown to pass `check₁`, since a failing leaf makes the composite `failure` on the
full transcript through it (`Verifier.append_run_guardedLeft`, at a suffix transcript supplied by
`ChallengeTree.LeafPath.some`), contradicting acceptance. From there the pure argument runs
verbatim with `out₁` in place of the left verifier's verdict, and the tree machinery
(`appendSplit` and friends) is untouched. -/
theorem append_treeSpecialSoundWithEscape_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (harity₂ : ∀ i, 0 < S₂.arity i)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ S₁.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : treeSpecialSoundEscape init impl S₂ esc₂ rel₂ rel₃ V₂) :
    treeSpecialSoundWithEscape init impl
      (S₁.append S₂) (esc₁.append esc₂ out₁) rel₁ rel₃ (V₁.append V₂)
      (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  rcases h₂ with ⟨E₂, hE₂⟩
  intro stmt tree hStructured hAccept
  by_cases hesc : ∃ path : ChallengeTree.LeafPath tree.appendSplit.fst,
      esc₂ (out₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)
  · exact Or.inl (Or.inr hesc)
  · push Not at hesc
    -- Every prefix leaf passes `check₁`: otherwise the composite would be `failure` on some full
    -- transcript through it, contradicting acceptance. This is the one step the pure proof does
    -- not have, and it is what `LeafPath.some` supplies the witness transcript for.
    have hcheck : ∀ path : ChallengeTree.LeafPath tree.appendSplit.fst,
        check₁ stmt path.fullTranscript = true := by
      intro path
      by_contra hc
      have hfail : (V₁.append V₂).verify stmt
          (path.fullTranscript ++ₜ
            (ChallengeTree.LeafPath.some
              harity₂
              (tree.appendSplit.sndAt path)).fullTranscript) = failure := by
        have := Verifier.append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt path.fullTranscript
          (ChallengeTree.LeafPath.some
            harity₂
            (tree.appendSplit.sndAt path)).fullTranscript
        rw [if_neg hc] at this
        exact this
      exact Verifier.not_accepting_of_verify_failure init impl (V₁.append V₂) stmt _
        rel₃.language hfail
        (hAccept _ (ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree path
          (ChallengeTree.LeafPath.mem_fullTranscripts _)))
    -- From here the pure argument runs verbatim, with `out₁` in place of `verify₁`.
    have hLang : ∀ path : ChallengeTree.LeafPath tree.appendSplit.fst,
        out₁ stmt path.fullTranscript ∈ rel₂.language := by
      intro path
      have hSuffixStructured : (tree.appendSplit.sndAt path).IsStructured S₂ :=
        ChallengeTree.appendSplit_sndAt_isStructured tree hStructured path
      have hSuffixAccept :
          (tree.appendSplit.sndAt path).IsAccepting init impl V₂
            (out₁ stmt path.fullTranscript) rel₃.language := by
        intro tr₂ htr₂
        have hfull := hAccept _
          (ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree path htr₂)
        rw [Verifier.append_run_guardedLeft V₁ V₂ check₁ out₁ hV₁ stmt path.fullTranscript tr₂,
          if_pos (hcheck path)] at hfull
        exact hfull
      rcases hE₂ _ _ hSuffixStructured hSuffixAccept with hbad | hwit
      · exact absurd hbad (hesc path)
      · exact (Set.mem_language_iff rel₂ _).2 ⟨_, hwit⟩
    have hPrefixAccept :
        tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨path, rfl⟩ := ChallengeTree.LeafPath.exists_of_mem_fullTranscripts htr₁
      refine Verifier.pure_accepting_of_mem init impl V₁ stmt path.fullTranscript rel₂.language
        (out₁ stmt path.fullTranscript) ?_ (hLang path)
      rw [hV₁ stmt path.fullTranscript, if_pos (hcheck path)]
    rcases h₁ stmt tree.appendSplit.fst
        (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hPrefixAccept with
      hbad | hwit
    · exact Or.inl (Or.inl hbad)
    · exact Or.inr hwit

/-- **Guarded binary CWSS append, escape-threaded named form** — the CWSS-shape wrapper of
`append_treeSpecialSoundWithEscape_of_guardedLeft`, mirroring the pure
`append_coordinateWiseSpecialSoundWithEscape`. The positivity of the right shape's arity, which
the tree-level statement takes as a hypothesis, is free here: every `CWSSStructure` branches
`ℓᵢ·(kᵢ−1)+1 ≥ 1` ways (`CWSSStructure.arity_pos`). -/
theorem append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (h₁ : coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : coordinateWiseSpecialSoundEscape init impl D₂ esc₂ rel₂ rel₃ V₂) :
    coordinateWiseSpecialSoundWithEscape init impl
      (CWSSStructure.append D₁ D₂) (esc₁.append esc₂ out₁) rel₁ rel₃ (V₁.append V₂)
      (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) :=
  treeSpecialSoundWithEscape_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm
    HEq.rfl HEq.rfl
    (append_treeSpecialSoundWithEscape_of_guardedLeft init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) (fun i => D₂.arity_pos i)
      check₁ out₁ hV₁ esc₁ esc₂ Ext₁ h₁ h₂)

/-- **Guarded binary CWSS append, plain named form** — a *proven corollary* of the escape-threaded
obligation above at `esc₁ = esc₂ = fun _ _ => False`, where the composed event is propositionally
never-firing and so eliminable. This is why the escape-threaded theorem, not this one, is the
fundamental obligation. -/
theorem append_coordinateWiseSpecialSoundWith_of_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (hV₁ : V₁.IsGuarded)
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (h₁ : coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
    coordinateWiseSpecialSoundWith init impl
      (CWSSStructure.append D₁ D₂) rel₁ rel₃ (V₁.append V₂)
      (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  obtain ⟨E₂, hE₂⟩ := h₂
  have hesc := append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft init impl V₁ V₂ D₁ D₂
    hV₁.is_guarded.choose hV₁.is_guarded.choose_spec.choose
    hV₁.is_guarded.choose_spec.choose_spec (fun _ _ => False) (fun _ _ => False) Ext₁
    (Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ h₁)
    (Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _ hE₂).toEscape
  intro stmt tree hStructured hAccept
  rcases hesc stmt tree hStructured hAccept with (hf | ⟨_, hf⟩) | hwit
  · exact hf.elim
  · exact hf.elim
  · exact hwit

end Append

end Verifier

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled guarded coordinate-wise-special-sound reduction**: `CWSSPackage` with the purity
witness relaxed to a guardedness witness. Guarded packages compose with `GCWSSPackage.append`
(infix `▷`, explicit synonym `▷ᵍ`); a pure package enters the guarded world via
`CWSSPackage.toGuarded`, or automatically through the mixed `▷` overloads below. -/
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
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: `extractor` witnesses that `verifier` is coordinate-wise special sound
  for `struct`, reducing `relIn` to `relOut`. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWith init impl struct relIn relOut verifier
    extractor

namespace GCWSSPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Forget purity: every (pure) `CWSSPackage` is a `GCWSSPackage` with the trivially-true
check; extractor and certificate carry over unchanged. -/
def _root_.CoordinateWise.CWSSPackage.toGuarded
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (L : CWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec) :
    GCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
  verifier := L.verifier
  struct := L.struct
  relIn := L.relIn
  relOut := L.relOut
  isGuarded := Verifier.IsGuarded.of_isPure L.verifier L.isPure
  extractor := L.extractor
  isCWSS := L.isCWSS

/-- **Compose two guarded packages along a matching seam** (`hseam` discharged by `rfl`): the
guarded analogue of `CWSSPackage.append`/`▷`. The composed verdict is guarded by the conjunction
of both checks (`Verifier.IsGuarded.append`), the composed extractor is the left extractor on
the prefix tree, and the composed certificate is the guarded binary append theorem
`Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft` — this definition is the
*interface* the Hachi chain composes through. Written infix
as `L₁ ▷ L₂` (explicit synonym `▷ᵍ`). -/
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
  extractor := fun stmt tree => L₁.extractor stmt tree.appendSplit.fst
  isCWSS := by
    have h₂ := L₂.isCWSS.toCWSS
    rw [← hseam] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWith_of_guardedLeft init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct L₁.isGuarded L₁.extractor L₁.isCWSS h₂

end GCWSSPackage

@[inherit_doc GCWSSPackage.append]
scoped infixr:65 " ▷ᵍ " => GCWSSPackage.append

/-! ### Lifting pure packages into a guarded chain

A pure `CWSSPackage` enters the guarded world losslessly (`CWSSPackage.toGuarded`: the guard is
the trivially-true check and the certificate is unchanged). The mixed appends below insert this
lift automatically, so guarded packages need only be *defined* for the subprotocols whose checks
genuinely reject at runtime. Together with the escape-lifting appends in `Escape.lean`, every
ordered pair of package kinds (escape? × guarded?) composes at its join through the universal
`▷` elaborator defined in `Escape.lean`: two pure packages compose pure (staying on the proven
pure append theorem), while a single guarded factor moves the composite — visibly in its type —
onto the guarded append theorem. -/

section GuardedLift

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Compose a pure left factor with a guarded right factor.** The left package is lifted with
`CWSSPackage.toGuarded`; only the relation seam `hRel` remains (discharged by `rfl`).
Dispatched by the universal `▷`. -/
def CWSSPackage.appendGuarded {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : GCWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    GCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.toGuarded.append L₂ hRel

/-- **Compose a guarded left factor with a pure right factor.** The right package is lifted with
`CWSSPackage.toGuarded`; only the relation seam `hRel` remains (discharged by `rfl`).
Dispatched by the universal `▷`. -/
def GCWSSPackage.appendPure {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : GCWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hRel : L₁.relOut = L₂.relIn := by rfl) :
    GCWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) :=
  L₁.append L₂.toGuarded hRel

end GuardedLift

end CoordinateWise

end
