/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Composition.Sequential.IsPure

/-!
  # `n`-ary sequential composition for (coordinate-wise) special soundness

  This file lifts the binary append theory of
  `CoordinateWiseSpecialSoundness.Composition` to the finite sequential composition
  `Verifier.seqCompose`. The two ingredients are:

  * the **base case** `Verifier.id_treeSpecialSound`: the identity verifier (over the empty
    protocol `!p[]`, which has no challenge rounds) is tree-special-sound for any shape with
    `relIn = relOut`, via the no-challenge bridge `treeSpecialSound_of_isEmpty_challengeIdx`; and
  * the **step case**, threading per-factor purity (`Verifier.IsPure`, from
    `Composition.Sequential.IsPure`) into the deterministic-left hypothesis of
    `Verifier.append_treeSpecialSound`, plus the shape identity
    `ChallengeTreeShape.seqCompose_succ` that exposes the head/tail append structure of the
    sequentially-composed shape.

  ## Main results

  * `Verifier.mem_of_pure_accepting` — converse of `Verifier.pure_accepting_of_mem`: a pure
    verifier whose run is accepted with probability one has its output in the language.
  * `Verifier.id_treeSpecialSound` — the n-ary base case.
  * `ChallengeTreeShape.seqCompose_succ` — `seqCompose` of shapes unfolds to `append` of head/tail.
  * `Verifier.seqCompose_treeSpecialSound` — generic n-ary tree-soundness composition.
  * `Verifier.seqCompose_coordinateWiseSpecialSound` — the CWSS-specific wrapper.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Converse of `pure_accepting_of_mem`: if a verifier deterministically outputs `out` on
`(stmt, tr)` and its run is accepted into `lang` with probability one, then `out ∈ lang`. -/
theorem mem_of_pure_accepting
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmt : StmtIn) (tr : pSpec.FullTranscript)
    (lang : Set StmtOut) (out : StmtOut)
    (hV : V.verify stmt tr = pure out)
    (hAcc : Pr[ (· ∈ lang) |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] = 1) :
      out ∈ lang := by
  rw [probEvent_eq_one_iff] at hAcc
  obtain ⟨hFail, hmem⟩ := hAcc
  -- The underlying probabilistic computation is `init >>= fun _ => pure (some out)`.
  have hrun : (do (simulateQ impl (V.run stmt tr)).run' (← init) :
      ProbComp (Option StmtOut)) = (init >>= fun _ => pure (some out)) := by
    simp only [Verifier.run, hV]
    congr 1
  refine hmem out ?_
  -- `init` has nonempty support, else the whole computation would fail with probability one.
  have hne : (support init).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hcfail : Pr[⊥ |
        (init >>= fun _ => pure (some out) : ProbComp (Option StmtOut))] = 0 := by
      have h2 := hFail
      rw [OptionT.probFailure_eq, OptionT.run_mk, hrun] at h2
      exact (add_eq_zero.mp h2).1
    have hcsupp :
        support (init >>= fun _ => pure (some out) : ProbComp (Option StmtOut)) = ∅ := by
      rw [support_bind_const, support_pure]; simp [hempty]
    rw [probFailure_eq_one hcsupp] at hcfail
    exact one_ne_zero hcfail
  rw [OptionT.mem_support_iff, OptionT.run_mk, hrun, support_bind_const, support_pure]
  exact ⟨Set.mem_singleton _, hne⟩

end Verifier

namespace Verifier

open ProtocolSpec ProtocolSpec.ChallengeTree

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **n-ary base case.** The identity verifier is tree-special-sound for any shape `S`, with input
relation equal to output relation: the empty protocol `!p[]` has no challenge rounds, so this is the
no-challenge bridge with the extractor that noncomputably picks a witness of `stmtIn` whenever one
exists. -/
theorem id_treeSpecialSound {Statement Witness : Type} [Nonempty Witness]
    (S : ChallengeTreeShape (!p[] : ProtocolSpec 0))
    (rel : Set (Statement × Witness)) :
    (Verifier.id (oSpec := oSpec) (Statement := Statement)).treeSpecialSound
      init impl S rel rel := by
  -- For each statement, some candidate witness works as soon as any witness exists.
  have hpick : ∀ stmt : Statement, ∃ w : Witness, (∃ w', (stmt, w') ∈ rel) → (stmt, w) ∈ rel := by
    intro stmt
    rcases or_not (p := ∃ w', (stmt, w') ∈ rel) with ⟨w, hw⟩ | h
    · exact ⟨w, fun _ => hw⟩
    · exact ⟨Nonempty.some inferInstance, fun hex => absurd hex h⟩
  refine treeSpecialSound_of_isEmpty_challengeIdx init impl S Verifier.id rel rel
    (fun stmt _ => (hpick stmt).choose) ?_
  intro stmtIn tr hAcc
  have hlang : stmtIn ∈ rel.language :=
    mem_of_pure_accepting init impl Verifier.id stmtIn tr rel.language stmtIn rfl hAcc
  exact (hpick stmtIn).choose_spec ((Set.mem_language_iff rel stmtIn).1 hlang)

end Verifier

namespace ChallengeTreeShape

variable {m : ℕ} {len : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}

/-- A sigma over `Fin` whose fibers are subtypes of `Fin` is determined by the underlying
`Fin`-level data: equal first components and equal underlying second values force equality. -/
private theorem sigmaSubtype_ext {M : ℕ} {N : Fin M → ℕ} {P : (i : Fin M) → Fin (N i) → Prop}
    {a a' : Fin M} {v : Fin (N a)} {v' : Fin (N a')} {p : P a v} {p' : P a' v'}
    (ha : a = a') (hv : (v : ℕ) = (v' : ℕ)) :
    (⟨a, ⟨v, p⟩⟩ : (i : Fin M) × {x : Fin (N i) // P i x}) = ⟨a', ⟨v', p'⟩⟩ := by
  subst ha
  have : v = v' := Fin.ext hv
  subst this
  rfl

/-- Heterogeneous congruence for dependent function application. -/
private theorem heq_app.{u, v} {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v}
    (hα : α = α') (hβ : HEq β β') {f : (a : α) → β a} {f' : (a : α') → β' a}
    (hf : HEq f f') {a : α} {a' : α'} (ha : HEq a a') : HEq (f a) (f' a') := by
  subst hα
  obtain rfl := eq_of_heq hβ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq ha
  rfl

/-- Heterogeneous congruence for `nodeOk`: a `ChallengeTreeShape`'s node predicate transports
across an equality of the underlying protocol, challenge index, arity, and a heterogeneous equality
of the sibling-challenge function. -/
private theorem heq_nodeOk {n n' : ℕ} (hn : n = n') {p : ProtocolSpec n} {p' : ProtocolSpec n'}
    (hp : HEq p p') {T : ChallengeTreeShape p} {T' : ChallengeTreeShape p'} (hT : HEq T T')
    {i : p.ChallengeIdx} {i' : p'.ChallengeIdx} (hi : HEq i i')
    {f : Fin (T.arity i) → p.Challenge i} {f' : Fin (T'.arity i') → p'.Challenge i'}
    (hf : HEq f f') :
    HEq (T.nodeOk i f) (T'.nodeOk i' f') := by
  subst hn
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hf
  exact HEq.rfl

variable {a b : ℕ} {p₁ : ProtocolSpec a} {p₂ : ProtocolSpec b}

/-- The append node predicate at a left-embedded index reduces to the left shape's predicate. -/
theorem append_nodeOk_inl (S₁ : ChallengeTreeShape p₁) (S₂ : ChallengeTreeShape p₂)
    (i₁ : p₁.ChallengeIdx)
    (challenges : Fin ((S₁.append S₂).arity (ChallengeIdx.inl i₁)) →
        (p₁ ++ₚ p₂).Challenge (ChallengeIdx.inl i₁)) :
    (S₁.append S₂).nodeOk (ChallengeIdx.inl i₁) challenges
      = S₁.nodeOk i₁ (fun j => cast (by simp [ProtocolSpec.append, ChallengeIdx.inl])
          (challenges (Fin.cast (by
            change S₁.arity i₁ = ChallengeTree.appendArity S₁.arity S₂.arity (ChallengeIdx.inl i₁)
            simp only [ChallengeTree.appendArity, Function.comp_apply,
              ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl]) j))) := by
  simp only [ChallengeTreeShape.append]
  split
  · rename_i i₁' heq
    rw [ChallengeIdx.sumEquiv_symm_inl] at heq
    obtain rfl : i₁' = i₁ := by simpa using heq.symm
    rfl
  · rename_i i₂' heq
    rw [ChallengeIdx.sumEquiv_symm_inl] at heq
    simp at heq

/-- The append node predicate at a right-embedded index reduces to the right shape's predicate. -/
theorem append_nodeOk_inr (S₁ : ChallengeTreeShape p₁) (S₂ : ChallengeTreeShape p₂)
    (i₂ : p₂.ChallengeIdx)
    (challenges : Fin ((S₁.append S₂).arity (ChallengeIdx.inr i₂)) →
        (p₁ ++ₚ p₂).Challenge (ChallengeIdx.inr i₂)) :
    (S₁.append S₂).nodeOk (ChallengeIdx.inr i₂) challenges
      = S₂.nodeOk i₂ (fun j => cast (by simp [ProtocolSpec.append, ChallengeIdx.inr])
          (challenges (Fin.cast (by
            change S₂.arity i₂ = ChallengeTree.appendArity S₁.arity S₂.arity (ChallengeIdx.inr i₂)
            simp only [ChallengeTree.appendArity, Function.comp_apply,
              ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr]) j))) := by
  simp only [ChallengeTreeShape.append]
  split
  · rename_i i₁' heq
    rw [ChallengeIdx.sumEquiv_symm_inr] at heq
    simp at heq
  · rename_i i₂' heq
    rw [ChallengeIdx.sumEquiv_symm_inr] at heq
    obtain rfl : i₂' = i₂ := by simpa using heq.symm
    rfl

/-- The `seqCompose` node predicate unfolds, by definition, to the decoded component's predicate
applied to the cast-in sibling challenges. -/
theorem seqCompose_nodeOk_eq {r : ℕ} {ln : Fin r → ℕ} {ps : ∀ i, ProtocolSpec (ln i)}
    (S : ∀ i, ChallengeTreeShape (ps i)) (ci : (ProtocolSpec.seqCompose ps).ChallengeIdx)
    (f : Fin ((ChallengeTreeShape.seqCompose S).arity ci) →
        (ProtocolSpec.seqCompose ps).Challenge ci) :
    (ChallengeTreeShape.seqCompose S).nodeOk ci f
      = (S (seqComposeChallengeIdxToSigma ci).1).nodeOk (seqComposeChallengeIdxToSigma ci).2
          (fun j => cast (seqCompose_challenge_eq ci) (f j)) := rfl

/-- The decoded sigma of a left-embedded composed challenge index is `⟨0, i₁⟩`. -/
private theorem toSigma_inl (i₁ : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma
        (pSpec := pSpec)
        (ChallengeIdx.inl (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))) i₁)
      = ⟨0, i₁⟩ := by
  unfold seqComposeChallengeIdxToSigma
  dsimp only
  have hcoe : (ChallengeIdx.inl
      (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))) i₁).1
        = Fin.embedSum (0 : Fin (m + 1)) i₁.1 := rfl
  refine sigmaSubtype_ext (P := fun i x => (pSpec i).dir x = .V_to_P)
    (a' := 0) (v' := i₁.1) (p' := i₁.2) ?_ ?_
  · rw [hcoe, Fin.splitSum_embedSum]
  · rw [hcoe, Fin.splitSum_embedSum]

/-- The decoded sigma of a right-embedded composed challenge index shifts by one round. -/
private theorem toSigma_inr
    (i₂ : (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec) (ChallengeIdx.inr (pSpec₁ := pSpec 0) i₂)
      = ⟨(seqComposeChallengeIdxToSigma i₂).1.succ, (seqComposeChallengeIdxToSigma i₂).2⟩ := by
  have hcoe : (ChallengeIdx.inr (pSpec₁ := pSpec 0) i₂).1
      = Fin.natAdd (len 0) i₂.1 := rfl
  conv_lhs => unfold seqComposeChallengeIdxToSigma
  conv_rhs => unfold seqComposeChallengeIdxToSigma
  dsimp only
  refine sigmaSubtype_ext (P := fun i x => (pSpec i).dir x = .V_to_P) ?_ ?_
  · rw [hcoe, Fin.splitSum_succ]; erw [Fin.dappend_right]
  · rw [hcoe, Fin.splitSum_succ]; erw [Fin.dappend_right]

/-- **Successor unfolding of the sequentially-composed shape.** `ChallengeTreeShape.seqCompose` of
a family over `m + 1` factors is the binary `append` of the head shape with the sequential
composition of the tail. This is the shape-level analogue of
`ProtocolSpec.seqCompose_succ_eq_append`, and is what lets the `n`-ary tree-soundness induction
reduce its step to the binary `Verifier.append_treeSpecialSound`. -/
theorem seqCompose_succ (S : ∀ i, ChallengeTreeShape (pSpec i)) :
    ChallengeTreeShape.seqCompose S =
      (S 0).append (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))) := by
  have harity : (ChallengeTreeShape.seqCompose S).arity
      = ((S 0).append (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i)))).arity := by
    funext i
    change (S (seqComposeChallengeIdxToSigma i).1).arity (seqComposeChallengeIdxToSigma i).2
      = ChallengeTree.appendArity (S 0).arity
          (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity i
    rcases hsplit : (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).symm i with i₁ | i₂
    · obtain rfl : i = (ChallengeIdx.inl (pSpec₂ :=
          ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))) i₁ :
          (ProtocolSpec.seqCompose pSpec).ChallengeIdx) := by
        have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp hsplit
        simpa [ChallengeIdx.sumEquiv_apply] using this
      rw [toSigma_inl]
      simp only [ChallengeTree.appendArity, Function.comp_apply,
        ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl]
    · obtain rfl : i = (ChallengeIdx.inr (pSpec₁ := pSpec 0) i₂ :
          (ProtocolSpec.seqCompose pSpec).ChallengeIdx) := by
        have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp hsplit
        simpa [ChallengeIdx.sumEquiv_apply] using this
      rw [toSigma_inr]
      simp only [ChallengeTree.appendArity, Function.comp_apply,
        ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr]
      rfl
  refine ChallengeTreeShape.ext harity ?_
  refine Function.hfunext rfl (fun i i' hi => ?_)
  obtain rfl : i = i' := eq_of_heq hi
  refine Function.hfunext (by rw [harity]) (fun challenges challenges' hch => ?_)
  rcases hsplit : (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
      (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).symm i with i₁ | i₂
  · obtain rfl : i = (ChallengeIdx.inl (pSpec₂ :=
        ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))) i₁ :
        (ProtocolSpec.seqCompose pSpec).ChallengeIdx) := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp hsplit
      simpa [ChallengeIdx.sumEquiv_apply] using this
    apply heq_of_eq
    rw [seqCompose_nodeOk_eq, append_nodeOk_inl]
    have hsig := toSigma_inl (pSpec := pSpec) i₁
    have hfst := congrArg Sigma.fst hsig
    have hsnd := (Sigma.ext_iff.mp hsig).2
    refine eq_of_heq (heq_nodeOk (congrArg len hfst) ?_ ?_ hsnd ?_)
    · rw [hfst]
    · rw [hfst]
    · refine Function.hfunext (congrArg Fin ?hdom) (fun j j' hj => ?_)
      case hdom =>
        change (ChallengeTreeShape.seqCompose S).arity _ = (S 0).arity i₁
        rw [harity]
        change ChallengeTree.appendArity (S 0).arity
          (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity (ChallengeIdx.inl i₁)
            = (S 0).arity i₁
        simp only [ChallengeTree.appendArity, Function.comp_apply,
          ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      refine heq_app (by rw [harity]) ?_ hch ?_
      · rw [harity]
      · refine HEq.trans hj ?_
        exact (Fin.heq_ext_iff (by
          change (S 0).arity i₁ = ChallengeTree.appendArity (S 0).arity
            (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity (ChallengeIdx.inl i₁)
          simp only [ChallengeTree.appendArity, Function.comp_apply,
            ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl])).mpr rfl
  · obtain rfl : i = (ChallengeIdx.inr (pSpec₁ := pSpec 0) i₂ :
          (ProtocolSpec.seqCompose pSpec).ChallengeIdx) := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp hsplit
      simpa [ChallengeIdx.sumEquiv_apply] using this
    apply heq_of_eq
    rw [seqCompose_nodeOk_eq, append_nodeOk_inr, seqCompose_nodeOk_eq]
    have hsig := toSigma_inr (pSpec := pSpec) i₂
    have hfst := congrArg Sigma.fst hsig
    have hsnd := (Sigma.ext_iff.mp hsig).2
    refine eq_of_heq (heq_nodeOk (congrArg len hfst) ?_ ?_ hsnd ?_)
    · rw [hfst]
    · rw [hfst]
    · refine Function.hfunext (congrArg Fin ?hdomr) (fun j j' hj => ?_)
      case hdomr =>
        change (ChallengeTreeShape.seqCompose S).arity _
          = (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity i₂
        rw [harity]
        change ChallengeTree.appendArity (S 0).arity
          (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity (ChallengeIdx.inr i₂)
            = (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity i₂
        simp only [ChallengeTree.appendArity, Function.comp_apply,
          ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr]
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans ?_ (HEq.trans (cast_heq _ _) (cast_heq _ _)).symm
      refine heq_app (by rw [harity]) ?_ hch ?_
      · rw [harity]
      · refine HEq.trans hj ?_
        exact (Fin.heq_ext_iff (by
          change (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity i₂
            = ChallengeTree.appendArity (S 0).arity
              (ChallengeTreeShape.seqCompose (fun i => S (Fin.succ i))).arity (ChallengeIdx.inr i₂)
          simp only [ChallengeTree.appendArity, Function.comp_apply,
            ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr])).mpr rfl

end ChallengeTreeShape

section NaryCompose

variable {ι : Type} {oSpec : OracleSpec ι}
  {m : ℕ} {Stmt : Fin (m + 1) → Type} {Wit : Fin (m + 1) → Type}
  {len : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (len i)}
  [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **`n`-ary generic tree-soundness composition.** If each factor verifier is pure (`IsPure`) and
tree-special-sound for the seam relations `rel i.castSucc ↦ rel i.succ`, then the sequential
composition `Verifier.seqCompose` is tree-special-sound for the sequentially-composed shape from
`rel 0` to `rel (Fin.last m)`. The induction's base case is `Verifier.id_treeSpecialSound` and its
step is `Verifier.append_treeSpecialSound`, with the head's purity discharging the
deterministic-left hypothesis and `ChallengeTreeShape.seqCompose_succ` exposing the appended
shape. -/
theorem Verifier.seqCompose_treeSpecialSound
    (S : ∀ i, ChallengeTreeShape (pSpec i))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (hWit : Nonempty (Wit (Fin.last m)))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (hV : ∀ i, (V i).IsPure)
    (h : ∀ i, (V i).treeSpecialSound init impl (S i) (rel i.castSucc) (rel i.succ)) :
      (Verifier.seqCompose Stmt V).treeSpecialSound init impl
        (ChallengeTreeShape.seqCompose S) (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    haveI : Nonempty (Wit 0) := hWit
    rw [Verifier.seqCompose_zero]
    exact Verifier.id_treeSpecialSound init impl (ChallengeTreeShape.seqCompose S) (rel 0)
  | succ m ih =>
    rw [Verifier.seqCompose_succ, ChallengeTreeShape.seqCompose_succ]
    obtain ⟨f₀, hf₀⟩ := (hV 0).is_pure
    have htail := ih (fun i => S i.succ) (fun i => rel i.succ) hWit
      (fun i => V i.succ) (fun i => hV i.succ) (fun i => h i.succ)
    refine Verifier.append_treeSpecialSound init impl (V 0)
      (Verifier.seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (S 0) (ChallengeTreeShape.seqCompose (fun i => S i.succ)) f₀ hf₀ (h 0) ?_
    simpa using htail

/-- **`n`-ary CWSS composition.** The coordinate-wise special-soundness wrapper of
`seqCompose_treeSpecialSound`, obtained by unfolding `coordinateWiseSpecialSound` to tree-soundness
of the induced shape and rewriting with `CWSSStructure.toShape_seqCompose`. -/
theorem Verifier.seqCompose_coordinateWiseSpecialSound
    (D : ∀ i, CWSSStructure (pSpec i))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (hWit : Nonempty (Wit (Fin.last m)))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (hV : ∀ i, (V i).IsPure)
    (h : ∀ i, (V i).coordinateWiseSpecialSound init impl (D i) (rel i.castSucc) (rel i.succ)) :
      (Verifier.seqCompose Stmt V).coordinateWiseSpecialSound init impl
        (CWSSStructure.seqCompose D) (rel 0) (rel (Fin.last m)) := by
  change (Verifier.seqCompose Stmt V).treeSpecialSound init impl
    (CWSSStructure.toShape (CWSSStructure.seqCompose D)) (rel 0) (rel (Fin.last m))
  rw [CWSSStructure.toShape_seqCompose]
  exact Verifier.seqCompose_treeSpecialSound init impl
    (fun i => CWSSStructure.toShape (D i)) rel hWit V hV h

end NaryCompose

end
