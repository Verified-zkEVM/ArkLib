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
  CWSS composition is factored through the generic `ChallengeTreeShape` API:

  * `CWSSStructure.append` and `CWSSStructure.seqCompose` transport intrinsic CWSS data across
    protocol composition.
  * `CWSSStructure.toShape_append` identifies the CWSS shape of an appended structure with the
    generic appended tree shape.
  * `Verifier.append_treeSpecialSound` is the generic structured-tree preservation statement.
  * `Verifier.append_coordinateWiseSpecialSound` is the CWSS-specific wrapper.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

universe u v

/-- Applying a `cast` of an `Equiv` (transported along equalities of its domain and codomain) agrees
with casting the argument into the original domain and the result out of the original codomain. This
is the single cast-commutation fact underlying the CWSS shape-composition theorems. -/
theorem cast_equiv_apply {A B : Type u} {C D : Type v} (hAB : A = B) (hCD : C = D) (e : A ≃ C)
    (b : B) :
    cast (show (A ≃ C) = (B ≃ D) by rw [hAB, hCD]) e b = cast hCD (e (cast hAB.symm b)) := by
  subst hAB; subst hCD; rfl

/-- Heterogeneous congruence for `Equiv` application: two heterogeneously-equal equivalences (over
equal domains and codomains) send heterogeneously-equal arguments to heterogeneously-equal
results. -/
theorem heq_equiv_apply {A A' : Type u} {B B' : Type v} (hA : A = A') (hB : B = B')
    {e₁ : A ≃ B} {e₂ : A' ≃ B'}
    (he : HEq e₁ e₂) {a : A} {a' : A'} (ha : HEq a a') : HEq (e₁ a) (e₂ a') := by
  subst hA; subst hB
  exact heq_of_eq (by rw [eq_of_heq he, eq_of_heq ha])

namespace ChallengeTreeShape

variable {r : ℕ} {len : Fin r → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}

/-- Sequential composition of a finite family of generic challenge-tree shapes. -/
def seqCompose (S : ∀ i, ChallengeTreeShape (pSpec i)) :
    ChallengeTreeShape (ProtocolSpec.seqCompose pSpec) where
  arity := fun combinedIdx =>
    let ij := seqComposeChallengeIdxToSigma combinedIdx
    (S ij.1).arity ij.2
  nodeOk := fun combinedIdx challenges =>
    let ij := seqComposeChallengeIdxToSigma combinedIdx
    (S ij.1).nodeOk ij.2 fun j =>
      cast (seqCompose_challenge_eq combinedIdx) (challenges j)

end ChallengeTreeShape

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

variable {r : ℕ} {len : Fin r → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}

/-- Sequential composition of a finite family of CWSS structures. -/
def seqCompose (D : ∀ i, CWSSStructure (pSpec i)) :
    CWSSStructure (ProtocolSpec.seqCompose pSpec) where
  coordIndex := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).coordIndex ij.2
  alphabet := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).alphabet ij.2
  decompose := fun i =>
    cast (by rw [seqCompose_challenge_eq i])
      ((D (seqComposeChallengeIdxToSigma i).1).decompose (seqComposeChallengeIdxToSigma i).2)
  soundnessParam := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).soundnessParam ij.2
  arity := fun i =>
    let ij := seqComposeChallengeIdxToSigma i
    (D ij.1).arity ij.2
  arity_eq := by
    funext i
    exact congrFun ((D (seqComposeChallengeIdxToSigma i).1).arity_eq)
      (seqComposeChallengeIdxToSigma i).2

/-- The arity of a sequentially composed CWSS structure is the component arity at the decoded
component challenge index. -/
theorem seqCompose_arity (D : ∀ i, CWSSStructure (pSpec i)) :
    (seqCompose D).arity =
      fun combinedIdx =>
        let ij := seqComposeChallengeIdxToSigma combinedIdx
        (D ij.1).arity ij.2 := rfl

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

/-- The sequentially-composed `decompose`, applied, equals the decoded component's `decompose`
applied to the cast-in challenge. The cast-commutation `cast_equiv_apply` applies directly here
because `seqCompose.decompose` is a single cast (no case split). -/
theorem seqCompose_decompose_apply (D : ∀ i, CWSSStructure (pSpec i))
    (ci : (ProtocolSpec.seqCompose pSpec).ChallengeIdx)
    (x : (ProtocolSpec.seqCompose pSpec).Challenge ci) :
    (seqCompose D).decompose ci x =
      (D (seqComposeChallengeIdxToSigma ci).1).decompose (seqComposeChallengeIdxToSigma ci).2
        (cast (seqCompose_challenge_eq ci) x) :=
  cast_equiv_apply (seqCompose_challenge_eq ci).symm rfl
    ((D (seqComposeChallengeIdxToSigma ci).1).decompose (seqComposeChallengeIdxToSigma ci).2) x

/-- The shape induced by finite sequential CWSS data is the generic sequential composition of the
component shapes. -/
theorem toShape_seqCompose (D : ∀ i, CWSSStructure (pSpec i)) :
    CWSSStructure.toShape (seqCompose D) =
      ChallengeTreeShape.seqCompose (fun i => CWSSStructure.toShape (D i)) := by
  refine ChallengeTreeShape.ext rfl (heq_of_eq ?_)
  funext ci challenges
  change CWSSStructure.nodeOk (seqCompose D) ci challenges =
    (D (seqComposeChallengeIdxToSigma ci).1).nodeOk (seqComposeChallengeIdxToSigma ci).2
      (fun j => cast (seqCompose_challenge_eq ci) (challenges j))
  unfold CWSSStructure.nodeOk
  congr 1
  funext j
  rw [seqCompose_decompose_apply]
  rfl

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

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Generic preservation of tree-special soundness under binary verifier append. -/
theorem append_treeSpecialSound
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : ChallengeTreeShape pSpec₁) (S₂ : ChallengeTreeShape pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.treeSpecialSound init impl S₁ rel₁ rel₂)
    (h₂ : V₂.treeSpecialSound init impl S₂ rel₂ rel₃) :
      (V₁.append V₂).treeSpecialSound init impl
        (S₁.append S₂) rel₁ rel₃ := by
  rcases h₁ with ⟨E₁, hE₁⟩
  rcases h₂ with ⟨E₂, hE₂⟩
  refine ⟨fun stmt tree => E₁ stmt tree.appendSplit.fst, ?_⟩
  intro stmt tree hStructured hAccept
  apply hE₁ stmt tree.appendSplit.fst
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
/-- Coordinate-wise special soundness is preserved by binary verifier append.

The deterministic first-verifier output identifies the input statement of each suffix tree consumed
by the second verifier's extractor. -/
theorem append_coordinateWiseSpecialSound
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.coordinateWiseSpecialSound init impl D₁ rel₁ rel₂)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSound init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ := by
  change (V₁.append V₂).treeSpecialSound init impl
    (CWSSStructure.toShape (CWSSStructure.append D₁ D₂)) rel₁ rel₃
  rw [CWSSStructure.toShape_append]
  exact append_treeSpecialSound init impl V₁ V₂
    (CWSSStructure.toShape D₁) (CWSSStructure.toShape D₂) verify₁ hV₁ h₁ h₂

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
/-- Oracle-verifier wrapper for binary CWSS append. -/
theorem append_coordinateWiseSpecialSound
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂)
    (verify₁ :
      (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hV₁ : ∀ stmt tr, V₁.toVerifier.verify stmt tr = pure (verify₁ stmt tr))
    (h₁ : V₁.coordinateWiseSpecialSound init impl D₁ rel₁ rel₂)
    (h₂ : V₂.coordinateWiseSpecialSound init impl D₂ rel₂ rel₃) :
      (V₁.append V₂).coordinateWiseSpecialSound init impl
        (CWSSStructure.append D₁ D₂) rel₁ rel₃ := by
  unfold OracleVerifier.coordinateWiseSpecialSound at h₁ h₂ ⊢
  convert Verifier.append_coordinateWiseSpecialSound init impl V₁.toVerifier V₂.toVerifier
    D₁ D₂ verify₁ hV₁ h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end
