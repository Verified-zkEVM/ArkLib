/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Composition for Coordinate-Wise Special Soundness

  This file contains the sequential-composition API for coordinate-wise special soundness (CWSS).
  Composition is deliberately **binary**: longer chains are built by iterating the binary append
  (the `CoordinateWise` packages' `▷`), which is all the protocol formalizations need and which
  keeps the composed extractor a nameable function rather than a transport across an `n`-ary shape
  identity. CWSS composition is factored through the generic `ChallengeTreeShape` API:

  * `CWSSStructure.append` transports intrinsic CWSS data across protocol append.
  * `CWSSStructure.toShape_append` identifies the CWSS shape of an appended structure with the
    generic appended tree shape.
  * `Verifier.pure_accepting_of_mem` / `Verifier.mem_of_pure_accepting` — the two directions of
    the pure-verifier acceptance bridge, used to certify prefix leaves' verdicts (and reused by
    the zero-round `ProofSystem/Component` reductions).
  * `Verifier.append_treeSpecialSoundWith` is the generic structured-tree preservation statement,
    and `Verifier.append_treeSpecialSoundWithEscape` its escape-threaded twin, whose composed escape
    event is `ChallengeTree.EscapeEvent.append`.
  * `Verifier.append_coordinateWiseSpecialSoundWith` / `…WithEscape` are the CWSS-specific
    wrappers, with `OracleVerifier` versions for oracle reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

universe u v

/-- Heterogeneous congruence for `Equiv` application: two heterogeneously-equal equivalences (over
equal domains and codomains) send heterogeneously-equal arguments to heterogeneously-equal
results. This is the single cast-commutation fact underlying `CWSSStructure.toShape_append`. -/
theorem heq_equiv_apply {A A' : Type u} {B B' : Type v} (hA : A = A') (hB : B = B')
    {e₁ : A ≃ B} {e₂ : A' ≃ B'}
    (he : HEq e₁ e₂) {a : A} {a' : A'} (ha : HEq a a') : HEq (e₁ a) (e₂ a') := by
  subst hA; subst hB
  exact heq_of_eq (by rw [eq_of_heq he, eq_of_heq ha])

namespace CWSSStructure

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The component coordinate decomposition selected by a sum tag. This gives `append`'s `decompose`
field a **clean** (equation-free) case split: the matcher branches mention only the bound index, so
the matcher reduces by rewriting its scrutinee with `ChallengeIdx.sumEquiv_symm_inl/inr`. The
boundary cast relating the appended challenge type to the component one is then applied once,
outside the matcher (in `append.decompose`). -/
def appendDecomposeSum (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂) :
    (s : pSpec₁.ChallengeIdx ⊕ pSpec₂.ChallengeIdx) →
      s.elim (fun i₁ => pSpec₁.Challenge i₁ ≃ (Fin (D₁.coordIndex i₁).val → D₁.alphabet i₁))
        (fun i₂ => pSpec₂.Challenge i₂ ≃ (Fin (D₂.coordIndex i₂).val → D₂.alphabet i₂))
  | Sum.inl i₁ => D₁.decompose i₁
  | Sum.inr i₂ => D₂.decompose i₂

/-- Binary append of coordinate-wise special-soundness structures.

On left challenge rounds this is `D₁`; on right challenge rounds this is `D₂`. -/
def append (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂) :
    CWSSStructure (pSpec₁ ++ₚ pSpec₂) where
  coordIndex := fun i =>
    match ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ => D₁.coordIndex i₁
    | Sum.inr i₂ => D₂.coordIndex i₂
  alphabet := fun i =>
    match ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ => D₁.alphabet i₁
    | Sum.inr i₂ => D₂.alphabet i₂
  decompose := fun i => cast (by
      rcases h : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
      · have hi : i = ChallengeIdx.inl i₁ := by
          have hi' : i = ChallengeIdx.sumEquiv (Sum.inl i₁) :=
            (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
          simpa [ChallengeIdx.sumEquiv_apply] using hi'
        subst i
        simp [ProtocolSpec.append, ChallengeIdx.inl]
      · have hi : i = ChallengeIdx.inr i₂ := by
          have hi' : i = ChallengeIdx.sumEquiv (Sum.inr i₂) :=
            (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
          simpa [ChallengeIdx.sumEquiv_apply] using hi'
        subst i
        simp [ProtocolSpec.append, ChallengeIdx.inr])
    (appendDecomposeSum D₁ D₂ (ChallengeIdx.sumEquiv.symm i))
  soundnessParam := fun i =>
    match ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ => D₁.soundnessParam i₁
    | Sum.inr i₂ => D₂.soundnessParam i₂
  arity := ChallengeTree.appendArity D₁.arity D₂.arity
  arity_eq := by
    funext i
    rcases h : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
    · simpa [ChallengeTree.appendArity, h] using congrFun D₁.arity_eq i₁
    · simpa [ChallengeTree.appendArity, h] using congrFun D₂.arity_eq i₂

/-- The arity of an appended CWSS structure is the generic appended arity. -/
theorem append_arity (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂) :
    (append D₁ D₂).arity = ChallengeTree.appendArity D₁.arity D₂.arity := rfl

section AppendChar

variable (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)

/-- The appended structure's coordinate index at a left index is the left component's. -/
@[simp] theorem append_coordIndex_inl (i₁ : pSpec₁.ChallengeIdx) :
    (append D₁ D₂).coordIndex (ChallengeIdx.inl i₁) = D₁.coordIndex i₁ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inl]

/-- The appended structure's coordinate index at a right index is the right component's. -/
@[simp] theorem append_coordIndex_inr (i₂ : pSpec₂.ChallengeIdx) :
    (append D₁ D₂).coordIndex (ChallengeIdx.inr i₂) = D₂.coordIndex i₂ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inr]

/-- The appended structure's alphabet at a left index is the left component's. -/
@[simp] theorem append_alphabet_inl (i₁ : pSpec₁.ChallengeIdx) :
    (append D₁ D₂).alphabet (ChallengeIdx.inl i₁) = D₁.alphabet i₁ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inl]

/-- The appended structure's alphabet at a right index is the right component's. -/
@[simp] theorem append_alphabet_inr (i₂ : pSpec₂.ChallengeIdx) :
    (append D₁ D₂).alphabet (ChallengeIdx.inr i₂) = D₂.alphabet i₂ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inr]

/-- The appended structure's soundness parameter at a left index is the left component's. -/
@[simp] theorem append_soundnessParam_inl (i₁ : pSpec₁.ChallengeIdx) :
    (append D₁ D₂).soundnessParam (ChallengeIdx.inl i₁) = D₁.soundnessParam i₁ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inl]

/-- The appended structure's soundness parameter at a right index is the right component's. -/
@[simp] theorem append_soundnessParam_inr (i₂ : pSpec₂.ChallengeIdx) :
    (append D₁ D₂).soundnessParam (ChallengeIdx.inr i₂) = D₂.soundnessParam i₂ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inr]

/-- The appended `decompose` at a left index is the left component's `decompose`, up to the boundary
type cast (stated as `HEq` since domain and codomain types differ propositionally). -/
theorem append_decompose_heqL {i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx} {i₁ : pSpec₁.ChallengeIdx}
    (h : ChallengeIdx.sumEquiv.symm i = Sum.inl i₁) :
    HEq ((append D₁ D₂).decompose i) (D₁.decompose i₁) := by
  simp only [append]
  refine (cast_heq _ _).trans ?_
  rw [h]
  exact HEq.rfl

/-- The appended `decompose` at a left index is the left component's `decompose`, up to cast. -/
theorem append_decompose_inl (i₁ : pSpec₁.ChallengeIdx) :
    HEq ((append D₁ D₂).decompose (ChallengeIdx.inl i₁)) (D₁.decompose i₁) :=
  append_decompose_heqL D₁ D₂ (ChallengeIdx.sumEquiv_symm_inl i₁)

theorem append_decompose_heqR {i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx} {i₂ : pSpec₂.ChallengeIdx}
    (h : ChallengeIdx.sumEquiv.symm i = Sum.inr i₂) :
    HEq ((append D₁ D₂).decompose i) (D₂.decompose i₂) := by
  simp only [append]
  refine (cast_heq _ _).trans ?_
  rw [h]
  exact HEq.rfl

/-- The appended `decompose` at a right index is the right component's `decompose`, up to cast. -/
theorem append_decompose_inr (i₂ : pSpec₂.ChallengeIdx) :
    HEq ((append D₁ D₂).decompose (ChallengeIdx.inr i₂)) (D₂.decompose i₂) :=
  append_decompose_heqR D₁ D₂ (ChallengeIdx.sumEquiv_symm_inr i₂)

end AppendChar

/-- The shape induced by appended CWSS data is the generic append of the component shapes. -/
theorem toShape_append (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂) :
    CWSSStructure.toShape (append D₁ D₂) =
      (CWSSStructure.toShape D₁).append (CWSSStructure.toShape D₂) := by
  refine ChallengeTreeShape.ext rfl (heq_of_eq ?_)
  funext i challenges
  simp only [CWSSStructure.toShape, ChallengeTreeShape.append]
  split
  · rename_i i₁ heq
    obtain rfl : i = ChallengeIdx.inl i₁ := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp heq
      simpa [ChallengeIdx.sumEquiv_apply] using this
    have hell : (append D₁ D₂).ell (ChallengeIdx.inl i₁) = D₁.ell i₁ :=
      congrArg Subtype.val (append_coordIndex_inl D₁ D₂ i₁)
    have hk : (append D₁ D₂).k (ChallengeIdx.inl i₁) = D₁.k i₁ :=
      congrArg Subtype.val (append_soundnessParam_inl D₁ D₂ i₁)
    have halpha : (append D₁ D₂).alphabet (ChallengeIdx.inl i₁) = D₁.alphabet i₁ :=
      append_alphabet_inl D₁ D₂ i₁
    unfold CWSSStructure.nodeOk
    congr 1
    refine Function.hfunext (by rw [hell, hk]) (fun j j' hj => ?_)
    refine heq_equiv_apply (by simp [ProtocolSpec.append, ChallengeIdx.inl])
      (by rw [append_coordIndex_inl, append_alphabet_inl])
      (append_decompose_inl D₁ D₂ i₁) ?_
    refine HEq.trans (heq_of_eq (congrArg challenges (Fin.ext ?_))) (cast_heq _ _).symm
    change j.val = j'.val
    exact (Fin.heq_ext_iff (by rw [hell, hk])).mp hj
  · rename_i i₂ heq
    obtain rfl : i = ChallengeIdx.inr i₂ := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp heq
      simpa [ChallengeIdx.sumEquiv_apply] using this
    have hell : (append D₁ D₂).ell (ChallengeIdx.inr i₂) = D₂.ell i₂ :=
      congrArg Subtype.val (append_coordIndex_inr D₁ D₂ i₂)
    have hk : (append D₁ D₂).k (ChallengeIdx.inr i₂) = D₂.k i₂ :=
      congrArg Subtype.val (append_soundnessParam_inr D₁ D₂ i₂)
    have halpha : (append D₁ D₂).alphabet (ChallengeIdx.inr i₂) = D₂.alphabet i₂ :=
      append_alphabet_inr D₁ D₂ i₂
    unfold CWSSStructure.nodeOk
    congr 1
    refine Function.hfunext (by rw [hell, hk]) (fun j j' hj => ?_)
    refine heq_equiv_apply (by simp [ProtocolSpec.append, ChallengeIdx.inr])
      (by rw [append_coordIndex_inr, append_alphabet_inr])
      (append_decompose_inr D₁ D₂ i₂) ?_
    refine HEq.trans (heq_of_eq (congrArg challenges (Fin.ext ?_))) (cast_heq _ _).symm
    change j.val = j'.val
    exact (Fin.heq_ext_iff (by rw [hell, hk])).mp hj

end CWSSStructure

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
  {rel₃ : Set (Stmt₃ × Wit₃)}

/-- Running an appended verifier whose left verifier is pure reduces to running the right verifier
on the deterministic left output and right transcript. -/
theorem append_run_pure_left
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (stmt₁ : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
      (V₁.append V₂).run stmt₁ (tr₁ ++ₜ tr₂) =
        V₂.run (verify₁ stmt₁ tr₁) tr₂ := by
  simp [Verifier.append_run, Verifier.run, hV₁]

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- A deterministic verifier output that lies in a language is accepted with probability one. -/
theorem pure_accepting_of_mem
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (V : Verifier oSpec Stmt₁ Stmt₂ pSpec)
    (stmt : Stmt₁) (tr : pSpec.FullTranscript)
    (lang : Set Stmt₂) (out : Stmt₂)
    (hV : V.verify stmt tr = pure out) (hout : out ∈ lang) :
      Pr[(· ∈ lang) |
        OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1 := by
  simp only [Verifier.run, hV]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ support
      (StateT.run' (simulateQ (r := StateT σ ProbComp) impl
        (pure (some out) : OracleComp oSpec (Option Stmt₂))) s) → False
    rw [simulateQ_pure]
    change none ∈ support
      (Prod.fst <$> (pure (some out) : StateT σ ProbComp (Option Stmt₂)).run s) → False
    rw [StateT.run_pure]
    simp [map_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ (r := StateT σ ProbComp) impl
        (pure (some out) : OracleComp oSpec (Option Stmt₂))) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some out) : StateT σ ProbComp (Option Stmt₂)).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    subst x
    exact hout

/-- Converse of `pure_accepting_of_mem`: if a verifier deterministically outputs `out` on
`(stmt, tr)` and its run is accepted into `lang` with probability one, then `out ∈ lang`. -/
theorem mem_of_pure_accepting
    {n : ℕ} {pSpec : ProtocolSpec n}
    (V : Verifier oSpec Stmt₁ Stmt₂ pSpec)
    (stmt : Stmt₁) (tr : pSpec.FullTranscript)
    (lang : Set Stmt₂) (out : Stmt₂)
    (hV : V.verify stmt tr = pure out)
    (hAcc : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) :
      out ∈ lang := by
  rw [probEvent_eq_one_iff] at hAcc
  obtain ⟨hFail, hmem⟩ := hAcc
  -- The underlying probabilistic computation is `init >>= fun _ => pure (some out)`.
  have hrun : (do (simulateQ impl (V.run stmt tr)).run' (← init) :
      ProbComp (Option Stmt₂)) = (init >>= fun _ => pure (some out)) := by
    simp only [Verifier.run, hV]
    congr 1
  refine hmem out ?_
  -- `init` has nonempty support, else the whole computation would fail with probability one.
  have hne : (support init).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hcfail : Pr[⊥ |
        (init >>= fun _ => pure (some out) : ProbComp (Option Stmt₂))] = 0 := by
      have h2 := hFail
      rw [OptionT.probFailure_eq, OptionT.run_mk, hrun] at h2
      exact (add_eq_zero.mp h2).1
    have hcsupp :
        support (init >>= fun _ => pure (some out) : ProbComp (Option Stmt₂)) = ∅ := by
      rw [support_bind_const, support_pure]; simp [hempty]
    rw [probFailure_eq_one hcsupp] at hcfail
    exact one_ne_zero hcfail
  rw [OptionT.mem_support_iff, OptionT.run_mk, hrun, support_bind_const, support_pure]
  exact ⟨Set.mem_singleton _, hne⟩

/-- **A rejecting verifier is never accepting.** If the verdict on `(stmt, tr)` is `failure`, the
run cannot be accepted into any language with probability one.

This is the third member of the acceptance bridge, alongside `pure_accepting_of_mem` and
`mem_of_pure_accepting`, and the one that only becomes meaningful once verifiers are allowed to
reject (`Guarded.lean`). It is what lets a *guarded* composition read "the composite tree is
accepting" as "every surviving prefix passed its check": a `failure` leaf would drive the whole
run's failure probability to one, contradicting acceptance.

Note the argument needs no assumption on `init`: whether or not the sampling itself can fail, the
total mass splits between failing and producing `none`, and acceptance forces *both* to vanish. -/
theorem not_accepting_of_verify_failure
    {n : ℕ} {pSpec : ProtocolSpec n}
    (V : Verifier oSpec Stmt₁ Stmt₂ pSpec)
    (stmt : Stmt₁) (tr : pSpec.FullTranscript) (lang : Set Stmt₂)
    (hV : V.verify stmt tr = failure) :
      Pr[ (· ∈ lang) |
        OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] ≠ 1 := by
  intro hAcc
  rw [probEvent_eq_one_iff] at hAcc
  obtain ⟨hFail, -⟩ := hAcc
  -- The underlying probabilistic computation is `init >>= fun _ => pure none`.
  have hrun : (do (simulateQ impl (V.run stmt tr)).run' (← init) :
      ProbComp (Option Stmt₂)) = (init >>= fun _ => pure none) := by
    simp only [Verifier.run, hV]
    congr 1
  rw [OptionT.probFailure_eq, OptionT.run_mk, hrun] at hFail
  obtain ⟨hbase, hnone⟩ := add_eq_zero.mp hFail
  -- All the mass sits on `none`, which acceptance has just forced to zero.
  have htsum : (∑' x : Option Stmt₂,
      Pr[= x | (init >>= fun _ => pure none : ProbComp (Option Stmt₂))]) = 0 := by
    refine (tsum_eq_single none ?_).trans hnone
    intro y hy
    refine probOutput_eq_zero_of_not_mem_support ?_
    rw [support_bind_const, support_pure]
    simp [hy]
  have htotal := probFailure_add_tsum_probOutput
    (init >>= fun _ => pure none : ProbComp (Option Stmt₂))
  rw [hbase, htsum] at htotal
  simp at htotal

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Named-extractor preservation of tree-special soundness under binary verifier append.** The
composed extractor is a named function of the *left* factor's extractor alone: it runs `Ext₁` on
the prefix tree. The right factor's extractor enters only through `rel₂.language` (certifying the
left leaves' outputs), so it may stay existential. -/
theorem append_treeSpecialSoundWith
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ S₁.arity)
    (h₁ : treeSpecialSoundWith init impl S₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : V₂.treeSpecialSound init impl S₂ rel₂ rel₃) :
      treeSpecialSoundWith init impl (S₁.append S₂) rel₁ rel₃ (V₁.append V₂)
        (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  rcases h₂ with ⟨E₂, hE₂⟩
  intro stmt tree hStructured hAccept
  apply h₁ stmt tree.appendSplit.fst
  · exact ChallengeTree.appendSplit_fst_isStructured tree hStructured
  · intro tr₁ htr₁
    obtain ⟨path, rfl⟩ :=
      ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
    have hSuffixStructured :
        (tree.appendSplit.sndAt path).IsStructured S₂ :=
      ChallengeTree.appendSplit_sndAt_isStructured tree hStructured path
    have hSuffixAccept :
        (tree.appendSplit.sndAt path).IsAccepting init impl V₂
          (verify₁ stmt path.fullTranscript) rel₃.language := by
      intro tr₂ htr₂
      have hmem :
          path.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
        ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree path htr₂
      have hfull := hAccept (path.fullTranscript ++ₜ tr₂) hmem
      simpa [append_run_pure_left V₁ V₂ verify₁ hV₁
          stmt path.fullTranscript tr₂] using hfull
    have hRel₂ :
        (verify₁ stmt path.fullTranscript,
          E₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)) ∈ rel₂ :=
      hE₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)
        hSuffixStructured hSuffixAccept
    have hLang₂ : verify₁ stmt path.fullTranscript ∈ rel₂.language :=
      (Set.mem_language_iff rel₂ (verify₁ stmt path.fullTranscript)).2
        ⟨E₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path), hRel₂⟩
    exact pure_accepting_of_mem init impl V₁ stmt path.fullTranscript rel₂.language
      (verify₁ stmt path.fullTranscript) (hV₁ stmt path.fullTranscript) hLang₂

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Escape-threaded preservation of tree special soundness under binary verifier append.** As in
the escape-free `append_treeSpecialSoundWith`, the composed extractor is the left extractor on the
prefix tree and the right factor's extractor stays existential; the composed escape event is
`ChallengeTree.EscapeEvent.append`.

The proof is the escape-free one with one extra case split up front: if some prefix leaf's suffix
tree exhibits `esc₂`, the right disjunct of the composed event fires directly; otherwise every
prefix leaf's verdict is certified into `rel₂.language` by the right factor's extraction (its escape
branch being excluded by that case assumption), and the left certificate applies. -/
theorem append_treeSpecialSoundWithEscape
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ S₁.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : treeSpecialSoundEscape init impl S₂ esc₂ rel₂ rel₃ V₂) :
      treeSpecialSoundWithEscape init impl (S₁.append S₂) (esc₁.append esc₂ verify₁)
        rel₁ rel₃ (V₁.append V₂) (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  rcases h₂ with ⟨E₂, hE₂⟩
  intro stmt tree hStructured hAccept
  by_cases hesc : ∃ path : LeafPath tree.appendSplit.fst,
      esc₂ (verify₁ stmt path.fullTranscript) (tree.appendSplit.sndAt path)
  · exact Or.inl (Or.inr hesc)
  · push Not at hesc
    have hLang : ∀ path : LeafPath tree.appendSplit.fst,
        verify₁ stmt path.fullTranscript ∈ rel₂.language := by
      intro path
      have hSuffixStructured : (tree.appendSplit.sndAt path).IsStructured S₂ :=
        ChallengeTree.appendSplit_sndAt_isStructured tree hStructured path
      have hSuffixAccept :
          (tree.appendSplit.sndAt path).IsAccepting init impl V₂
            (verify₁ stmt path.fullTranscript) rel₃.language := by
        intro tr₂ htr₂
        have hmem :=
          ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree path htr₂
        have hfull := hAccept _ hmem
        simpa [append_run_pure_left V₁ V₂ verify₁ hV₁ stmt path.fullTranscript tr₂]
          using hfull
      rcases hE₂ _ _ hSuffixStructured hSuffixAccept with hbad | hwit
      · exact absurd hbad (hesc path)
      · exact (Set.mem_language_iff rel₂ _).2 ⟨_, hwit⟩
    have hPrefixAccept :
        tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨path, rfl⟩ := ChallengeTree.LeafPath.exists_of_mem_fullTranscripts htr₁
      exact pure_accepting_of_mem init impl V₁ stmt path.fullTranscript rel₂.language
        (verify₁ stmt path.fullTranscript) (hV₁ stmt path.fullTranscript) (hLang path)
    rcases h₁ stmt tree.appendSplit.fst
        (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hPrefixAccept with
      hbad | hwit
    · exact Or.inl (Or.inl hbad)
    · exact Or.inr hwit

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Named-extractor preservation of CWSS under binary verifier append**: the composed extractor
is the left factor's extractor on the prefix tree, exactly as at the tree level
(`append_treeSpecialSoundWith`); the right factor's extractor stays existential. The shape
transport across `CWSSStructure.toShape_append` is `treeSpecialSoundWith_congr` — the arities of
the two shapes are definitionally equal, so the extractor crosses by `HEq.rfl`. -/
theorem append_coordinateWiseSpecialSoundWith
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (h₁ : coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      coordinateWiseSpecialSoundWith init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ (V₁.append V₂)
        (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) :=
  treeSpecialSoundWith_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm HEq.rfl
    (append_treeSpecialSoundWith init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) verify₁ hV₁ Ext₁ h₁ h₂)

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Escape-threaded preservation of CWSS under binary verifier append**: the CWSS-shape wrapper of
`append_treeSpecialSoundWithEscape`. Both the extractor and the event cross the shape equality
`CWSSStructure.toShape_append` by `HEq.rfl`, the two shapes' arities being definitionally equal. -/
theorem append_coordinateWiseSpecialSoundWithEscape
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased Stmt₁ Wit₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (h₁ : coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ V₁ Ext₁)
    (h₂ : coordinateWiseSpecialSoundEscape init impl D₂ esc₂ rel₂ rel₃ V₂) :
      coordinateWiseSpecialSoundWithEscape init impl (CWSSStructure.append D₁ D₂)
        (esc₁.append esc₂ verify₁) rel₁ rel₃ (V₁.append V₂)
        (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) :=
  treeSpecialSoundWithEscape_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm
    HEq.rfl HEq.rfl
    (append_treeSpecialSoundWithEscape init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) esc₁ esc₂ verify₁ hV₁ Ext₁ h₁ h₂)

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
  {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Oracle-verifier wrapper for the named binary CWSS append: the composed extractor is the left
factor's extractor on the prefix tree. -/
theorem append_coordinateWiseSpecialSoundWith
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ :
      (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hV₁ : ∀ stmt tr, V₁.toVerifier.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased (Stmt₁ × ∀ i, OStmt₁ i) Wit₁ pSpec₁
      (CWSSStructure.toShape D₁).arity)
    (h₁ : V₁.coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ Ext₁)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSoundWith init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃
        (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  unfold OracleVerifier.coordinateWiseSpecialSoundWith at h₁ ⊢
  unfold OracleVerifier.coordinateWiseSpecialSound at h₂
  rw [append_toVerifier]
  exact Verifier.append_coordinateWiseSpecialSoundWith init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ verify₁ hV₁ Ext₁ h₁ h₂

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Oracle-verifier wrapper for the escape-threaded binary CWSS append: the composed extractor is
the left factor's extractor on the prefix tree and the composed event is
`ChallengeTree.EscapeEvent.append` at the left factor's verdict map. -/
theorem append_coordinateWiseSpecialSoundWithEscape
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (esc₁ : ChallengeTree.EscapeEvent (Stmt₁ × ∀ i, OStmt₁ i) pSpec₁
      (CWSSStructure.toShape D₁).arity)
    (esc₂ : ChallengeTree.EscapeEvent (Stmt₂ × ∀ i, OStmt₂ i) pSpec₂
      (CWSSStructure.toShape D₂).arity)
    (verify₁ :
      (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hV₁ : ∀ stmt tr, V₁.toVerifier.verify stmt tr = pure (verify₁ stmt tr))
    (Ext₁ : Extractor.TreeBased (Stmt₁ × ∀ i, OStmt₁ i) Wit₁ pSpec₁
      (CWSSStructure.toShape D₁).arity)
    (h₁ : V₁.coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ Ext₁)
    (h₂ : V₂.coordinateWiseSpecialSoundEscape init impl D₂ esc₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSoundWithEscape init impl
        (CWSSStructure.append D₁ D₂) (esc₁.append esc₂ verify₁) rel₁ rel₃
        (fun stmt tree => Ext₁ stmt tree.appendSplit.fst) := by
  unfold OracleVerifier.coordinateWiseSpecialSoundWithEscape at h₁ ⊢
  unfold OracleVerifier.coordinateWiseSpecialSoundEscape at h₂
  rw [append_toVerifier]
  exact Verifier.append_coordinateWiseSpecialSoundWithEscape init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ esc₁ esc₂ verify₁ hV₁ Ext₁ h₁ h₂

end OracleVerifier

end
