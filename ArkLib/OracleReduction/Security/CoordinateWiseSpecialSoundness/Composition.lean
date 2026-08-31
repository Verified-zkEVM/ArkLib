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
    and `Verifier.append_treeSpecialSoundWithEscape` its escape-threaded twin, whose composed
    escape event is `ChallengeTree.EscapeEvent.append`.
  * `Verifier.append_coordinateWiseSpecialSoundWith` / `…WithEscape` are the CWSS-specific
    wrappers, with `OracleVerifier` versions for oracle reductions.

  ## The composed extractor

  All four statements compose the *named* extractors of both factors into
  `Extractor.TreeBased.append verify₁ E₁ E₂`, seamed by the left verifier's verdict function as
  data. `Verifier.append_run_outputs` is the seam lemma they share: it identifies the appended
  verifier's reachable outputs with the right verifier's, which is what transfers leaf-witnessing
  validity. Guarded left factors are handled in `Guarded.lean` at the same skeleton.
-/

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

/-- The appended verifier's **reachable output statements** at a glued transcript are the right
verifier's at the left verdict: the `Verifier.Outputs`-level form of `append_run_pure_left`.

This is what carries a leaf witnessing's *validity* across the seam. Validity is stated relative to
`Outputs` (`ChallengeTree.LeafWitnesses.IsValid`), so a pure left factor lets composition rewrite
the whole output set at once, with no need to identify which statement a witness was certified
at. -/
theorem append_run_outputs
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
      Outputs init impl (V₁.append V₂) stmt (tr₁ ++ₜ tr₂)
        = Outputs init impl V₂ (verify₁ stmt tr₁) tr₂ := by
  unfold Outputs
  rw [append_run_pure_left V₁ V₂ verify₁ hV₁ stmt tr₁ tr₂]

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

/-! ## Composition of tree-based certificates

The composed extractor is `Extractor.TreeBased.append`, a named function of **both** factors'
extractors: the right extractor enters the composed algorithm — it produces the leaf witnessing
the left extractor consumes — so it cannot stay existential. Its seam argument is `verify₁`,
the left verifier's verdict function *as data*; a package reads it off its `Verifier.PureForm`
field.

The four theorems (here and, for guarded left factors, in `Guarded.lean`) share one skeleton, whose
key move dissolves an apparent circularity between the two certificates: prefix acceptance is
established by running the **right** certificate at the canonical witnessing first (`key0`), and
that is what licenses the **left** certificate. The two witnessing-validity transfers ride
`ChallengeTree.AppendSplit.fullTranscript_gluePath` plus `append_run_outputs` — validity is
`Outputs`-relative, so left purity rewrites the output set directly, with no statement
identification — and the prefix witnessing's reachability comes from `pure_verdict_mem_outputs` at
the prefix tree's own acceptance. The escape twin routes the disjunction by a case split on "does
the right factor escape anywhere" before entering the plain skeleton. -/

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Preservation of tree special soundness under binary verifier append**, at the witness-only
extractor and a pure left factor. Both factors' extractors are named, and the composed one is
`Extractor.TreeBased.append verify₁ E₁ E₂`.

The right factor's extractor is named rather than existential: it *is* how the composed extraction
obtains the left factor's leaf witnessing, at the intermediate statement `verify₁` names. -/
theorem append_treeSpecialSoundWith
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWith init impl S₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWith init impl S₂ rel₂ rel₃ V₂ E₂) :
      treeSpecialSoundWith init impl (S₁.append S₂) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append verify₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  -- Every suffix tree is accepting for `V₂` at the left verdict on its prefix leaf.
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (verify₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    simpa [append_run_pure_left V₁ V₂ verify₁ hV₁
      stmt p₁.fullTranscript tr₂] using hfull
  -- The downstream certificate, instantiated at each prefix leaf's verdict.
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  -- Running it at the CANONICAL witnessing yields a `rel₂`-witness at every left verdict; this is
  -- what breaks the apparent circularity between the two certificates.
  have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ∃ w₂, (verify₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
    intro p₁
    obtain ⟨w₂, -, hw₂⟩ := h₂' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
    exact ⟨w₂, hw₂⟩
  -- Hence the prefix tree is accepting for `V₁` into `rel₂.language`.
  have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
    intro tr₁ htr₁
    obtain ⟨p₁, rfl⟩ :=
      ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
    obtain ⟨w₂, hw₂⟩ := key0 p₁
    exact pure_accepting_of_mem init impl V₁ stmt p₁.fullTranscript rel₂.language
      (verify₁ stmt p₁.fullTranscript) (hV₁ stmt p₁.fullTranscript)
      ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
  intro o hvalid
  -- Each suffix witnessing — the top witnessing read at glued paths — is valid for `V₂` at the left
  -- verdict: `fullTranscript_gluePath` and `append_run_outputs` transfer it wholesale.
  have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
      ChallengeTree.LeafWitnesses.IsValid init impl V₂ rel₃ (verify₁ stmt p₁.fullTranscript)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
    intro p₁ p₂
    obtain ⟨w, hw, out, hout, hrel⟩ :=
      hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
    refine ⟨w, hw, out, ?_, hrel⟩
    -- The transfer is authored at the `appendArity` forms, where both rewrites are syntactic, and
    -- applied to the notion-typed tree by `exact` (full definitional transparency).
    have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
        (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
        out ∈ Outputs init impl (V₁.append V₂) stmt
          (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
        out ∈ Outputs init impl V₂ (verify₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
      intro T q₁ q₂ h
      rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
      rwa [append_run_outputs init impl V₁ V₂ verify₁ hV₁] at h
    exact key tree p₁ p₂ hout
  -- The prefix witnessing — `E₂`'s output below each prefix leaf — is valid for `V₁`: the verdict
  -- is reachable, and `E₂`'s certificate makes that output a `rel₂`-witness for it.
  have hpreValid : ChallengeTree.LeafWitnesses.IsValid init impl V₁ rel₂ stmt
      (fun p₁ => E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
    intro p₁
    obtain ⟨w₂, hw₂, hrel₂⟩ := h₂' p₁ _ (hsuffValid p₁)
    exact ⟨w₂, hw₂, verify₁ stmt p₁.fullTranscript,
      pure_verdict_mem_outputs init impl verify₁ hV₁
        (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript, hrel₂⟩
  exact h₁ stmt tree.appendSplit.fst
    (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc _ hpreValid

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Escape-threaded preservation of tree special soundness under binary verifier append**, at the
witness-only extractor and a pure left factor, with the composed event the UNCHANGED
`ChallengeTree.EscapeEvent.append` at `verify₁`.

Disjunction routing: a right-factor escape below *some* prefix leaf fires the composed event's
right disjunct outright; otherwise every suffix certificate extracts, `key0` licenses the left
certificate, and that certificate's own escape fires the left disjunct or its extraction closes the
plain skeleton. The whole routing happens before any witnessing is seen. -/
theorem append_treeSpecialSoundWithEscape
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ S₁.arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ S₂.arity)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ S₁.arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ S₂.arity)
    (h₁ : treeSpecialSoundWithEscape init impl S₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : treeSpecialSoundWithEscape init impl S₂ esc₂ rel₂ rel₃ V₂ E₂) :
      treeSpecialSoundWithEscape init impl (S₁.append S₂) (esc₁.append esc₂ verify₁)
        rel₁ rel₃ (V₁.append V₂) (Extractor.TreeBased.append verify₁ E₁ E₂) := by
  intro stmt tree hStructured hAccept
  have hsuffAcc : ∀ p₁ : LeafPath tree.appendSplit.fst,
      (tree.appendSplit.sndAt p₁).IsAccepting init impl V₂
        (verify₁ stmt p₁.fullTranscript) rel₃.language := by
    intro p₁ tr₂ htr₂
    have hmem : p₁.fullTranscript ++ₜ tr₂ ∈ tree.fullTranscripts :=
      ChallengeTree.appendSplit_fullTranscripts_append_of_mem tree p₁ htr₂
    have hfull := hAccept (p₁.fullTranscript ++ₜ tr₂) hmem
    simpa [append_run_pure_left V₁ V₂ verify₁ hV₁
      stmt p₁.fullTranscript tr₂] using hfull
  have h₂' := fun p₁ : LeafPath tree.appendSplit.fst =>
    h₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
      (ChallengeTree.appendSplit_sndAt_isStructured tree hStructured p₁) (hsuffAcc p₁)
  by_cases hesc₂ : ∃ p₁ : LeafPath tree.appendSplit.fst,
      esc₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
  · exact Or.inl (Or.inr hesc₂)
  · push Not at hesc₂
    have h₂'' := fun p₁ : LeafPath tree.appendSplit.fst => (h₂' p₁).resolve_left (hesc₂ p₁)
    have key0 : ∀ p₁ : LeafPath tree.appendSplit.fst,
        ∃ w₂, (verify₁ stmt p₁.fullTranscript, w₂) ∈ rel₂ := by
      intro p₁
      obtain ⟨w₂, -, hw₂⟩ := h₂'' p₁ _ (canonWitnesses_isValid (hsuffAcc p₁))
      exact ⟨w₂, hw₂⟩
    have hpreAcc : tree.appendSplit.fst.IsAccepting init impl V₁ stmt rel₂.language := by
      intro tr₁ htr₁
      obtain ⟨p₁, rfl⟩ :=
        ChallengeTree.LeafPath.exists_of_mem_fullTranscripts (T := tree.appendSplit.fst) htr₁
      obtain ⟨w₂, hw₂⟩ := key0 p₁
      exact pure_accepting_of_mem init impl V₁ stmt p₁.fullTranscript rel₂.language
        (verify₁ stmt p₁.fullTranscript) (hV₁ stmt p₁.fullTranscript)
        ((Set.mem_language_iff rel₂ _).2 ⟨w₂, hw₂⟩)
    rcases h₁ stmt tree.appendSplit.fst
      (ChallengeTree.appendSplit_fst_isStructured tree hStructured) hpreAcc with
      hesc₁ | hext₁
    · exact Or.inl (Or.inl hesc₁)
    · refine Or.inr fun o hvalid => ?_
      have hsuffValid : ∀ p₁ : LeafPath tree.appendSplit.fst,
          ChallengeTree.LeafWitnesses.IsValid init impl V₂ rel₃ (verify₁ stmt p₁.fullTranscript)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)) := by
        intro p₁ p₂
        obtain ⟨w, hw, out, hout, hrel⟩ :=
          hvalid (ChallengeTree.AppendSplit.gluePath tree p₁ p₂)
        refine ⟨w, hw, out, ?_, hrel⟩
        have key : ∀ (T : ChallengeTree (pSpec₁ ++ₚ pSpec₂) (appendArity S₁.arity S₂.arity) 0)
            (q₁ : LeafPath T.appendSplit.fst) (q₂ : LeafPath (T.appendSplit.sndAt q₁)),
            out ∈ Outputs init impl (V₁.append V₂) stmt
              (ChallengeTree.AppendSplit.gluePath T q₁ q₂).fullTranscript →
            out ∈ Outputs init impl V₂ (verify₁ stmt q₁.fullTranscript) q₂.fullTranscript := by
          intro T q₁ q₂ h
          rw [ChallengeTree.AppendSplit.fullTranscript_gluePath] at h
          rwa [append_run_outputs init impl V₁ V₂ verify₁ hV₁] at h
        exact key tree p₁ p₂ hout
      have hpreValid : ChallengeTree.LeafWitnesses.IsValid init impl V₁ rel₂ stmt
          (fun p₁ => E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
            (fun p₂ => o (ChallengeTree.AppendSplit.gluePath tree p₁ p₂))) := by
        intro p₁
        obtain ⟨w₂, hw₂, hrel₂⟩ := h₂'' p₁ _ (hsuffValid p₁)
        exact ⟨w₂, hw₂, verify₁ stmt p₁.fullTranscript,
          pure_verdict_mem_outputs init impl verify₁ hV₁
            (support_init_nonempty_of_accepting hpreAcc p₁) stmt p₁.fullTranscript, hrel₂⟩
      exact hext₁ _ hpreValid

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Preservation of CWSS under binary verifier append** at the witness-only extractor: the
CWSS-shape wrapper of `append_treeSpecialSoundWith`. The shape transport across
`CWSSStructure.toShape_append` is `treeSpecialSoundWith_congr`; the two shapes' arities are
definitionally equal, so the extractor crosses by `HEq.rfl`. -/
theorem append_coordinateWiseSpecialSoundWith
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (h₁ : coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ V₁ E₁)
    (h₂ : coordinateWiseSpecialSoundWith init impl D₂ rel₂ rel₃ V₂ E₂) :
      coordinateWiseSpecialSoundWith init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append verify₁ E₁ E₂) :=
  treeSpecialSoundWith_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm HEq.rfl
    (append_treeSpecialSoundWith init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) verify₁ hV₁ E₁ E₂ h₁ h₂)

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Escape-threaded preservation of CWSS under binary verifier append** at the witness-only
extractor: the CWSS-shape wrapper of `append_treeSpecialSoundWithEscape`. Both the extractor and the
event cross the shape equality `CWSSStructure.toShape_append` by `HEq.rfl`. -/
theorem append_coordinateWiseSpecialSoundWithEscape
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (esc₁ : ChallengeTree.EscapeEvent Stmt₁ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (esc₂ : ChallengeTree.EscapeEvent Stmt₂ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : Extractor.TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ (CWSSStructure.toShape D₂).arity)
    (h₁ : coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ V₁ E₁)
    (h₂ : coordinateWiseSpecialSoundWithEscape init impl D₂ esc₂ rel₂ rel₃ V₂ E₂) :
      coordinateWiseSpecialSoundWithEscape init impl (CWSSStructure.append D₁ D₂)
        (esc₁.append esc₂ verify₁) rel₁ rel₃ (V₁.append V₂)
        (Extractor.TreeBased.append verify₁ E₁ E₂) :=
  treeSpecialSoundWithEscape_congr init impl (CWSSStructure.toShape_append D₁ D₂).symm
    HEq.rfl HEq.rfl
    (append_treeSpecialSoundWithEscape init impl V₁ V₂
      (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) esc₁ esc₂ verify₁ hV₁ E₁ E₂ h₁ h₂)

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

/-! ## The oracle-level mirrors

Each notion is the underlying verifier's on the combined (oracle + non-oracle) statements, so both
mirrors are `append_toVerifier` followed by the non-oracle theorem. -/

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Oracle-verifier wrapper for the binary CWSS append at the witness-only extractor: the composed
extractor is `Extractor.TreeBased.append` at the left verifier's verdict map. -/
theorem append_coordinateWiseSpecialSoundWith
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ :
      (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hV₁ : ∀ stmt tr, V₁.toVerifier.verify stmt tr = pure (verify₁ stmt tr))
    (E₁ : Extractor.TreeBased (Stmt₁ × ∀ i, OStmt₁ i) Wit₁ Wit₂ pSpec₁
      (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased (Stmt₂ × ∀ i, OStmt₂ i) Wit₂ Wit₃ pSpec₂
      (CWSSStructure.toShape D₂).arity)
    (h₁ : V₁.coordinateWiseSpecialSoundWith init impl D₁ rel₁ rel₂ E₁)
    (h₂ : V₂.coordinateWiseSpecialSoundWith init impl D₂ rel₂ rel₃ E₂) :
      (V₁.append V₂).coordinateWiseSpecialSoundWith init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃
        (Extractor.TreeBased.append verify₁ E₁ E₂) := by
  unfold OracleVerifier.coordinateWiseSpecialSoundWith at h₁ h₂ ⊢
  rw [append_toVerifier]
  exact Verifier.append_coordinateWiseSpecialSoundWith init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ verify₁ hV₁ E₁ E₂ h₁ h₂

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Oracle-verifier wrapper for the escape-threaded binary CWSS append at the witness-only
extractor: the composed extractor is `Extractor.TreeBased.append` and the composed event is
`ChallengeTree.EscapeEvent.append`, both at the left verifier's verdict map. -/
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
    (E₁ : Extractor.TreeBased (Stmt₁ × ∀ i, OStmt₁ i) Wit₁ Wit₂ pSpec₁
      (CWSSStructure.toShape D₁).arity)
    (E₂ : Extractor.TreeBased (Stmt₂ × ∀ i, OStmt₂ i) Wit₂ Wit₃ pSpec₂
      (CWSSStructure.toShape D₂).arity)
    (h₁ : V₁.coordinateWiseSpecialSoundWithEscape init impl D₁ esc₁ rel₁ rel₂ E₁)
    (h₂ : V₂.coordinateWiseSpecialSoundWithEscape init impl D₂ esc₂ rel₂ rel₃ E₂) :
      (V₁.append V₂).coordinateWiseSpecialSoundWithEscape init impl
        (CWSSStructure.append D₁ D₂) (esc₁.append esc₂ verify₁) rel₁ rel₃
        (Extractor.TreeBased.append verify₁ E₁ E₂) := by
  unfold OracleVerifier.coordinateWiseSpecialSoundWithEscape at h₁ h₂ ⊢
  rw [append_toVerifier]
  exact Verifier.append_coordinateWiseSpecialSoundWithEscape init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ esc₁ esc₂ verify₁ hV₁ E₁ E₂ h₁ h₂

end OracleVerifier
