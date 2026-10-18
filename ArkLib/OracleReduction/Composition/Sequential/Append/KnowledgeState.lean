/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Security.GuardedTerminal

/-!
# Knowledge-state composition with a guarded first verifier

A guarded verifier neither queries nor changes the ambient oracle state. Its accepting output
therefore gives the same terminal knowledge obligation under fresh and actual initialization.
These facts supply the boundary condition needed for knowledge-state composition.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} {V : Verifier oSpec StmtIn StmtOut pSpec}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

section Append

variable {Stmt₁ Stmt₂ Stmt₃ Wit₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
  {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}

/-- Stateful append passes the actual intermediate oracle state to the second verifier.
This execution identity does not require either verifier to be guarded. -/
theorem append_run_stateful (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (s : σ) :
    (simulateQ impl ((V₁.append V₂).run stmt tr).run).run s = (do
      let (mid, s') ← (simulateQ impl (V₁.run stmt tr.fst).run).run s
      match mid with
      | none => pure (none, s')
      | some mid => (simulateQ impl (V₂.run mid tr.snd).run).run s') := by
  simp only [run, append, OptionT.run_bind]
  simp only [simulateQ_option_elimM, simulateQ_pure]
  change (do
    let p ← (simulateQ impl (V₁.run stmt tr.fst).run).run s
    (p.1.elim (pure none) fun mid =>
      simulateQ impl (V₂.run mid tr.snd).run).run p.2) = _
  congr 1
  funext p
  cases p.1 <;> rfl

/-- An accepting composed execution factors through an accepting first execution and the
second execution started at precisely its reachable intermediate state. -/
theorem append_accepting_support_iff (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (s sOut : σ) (out : Stmt₃) :
    (some out, sOut) ∈ support
      ((simulateQ impl ((V₁.append V₂).run stmt tr).run).run s) ↔
    ∃ mid sMid,
      (some mid, sMid) ∈ support ((simulateQ impl (V₁.run stmt tr.fst).run).run s) ∧
      (some out, sOut) ∈ support ((simulateQ impl (V₂.run mid tr.snd).run).run sMid) := by
  rw [append_run_stateful]
  simp only [mem_support_bind_iff]
  constructor
  · rintro ⟨⟨mid, sMid⟩, hmid, hout⟩
    cases mid with
    | none => simp at hout
    | some mid => exact ⟨mid, sMid, hmid, hout⟩
  · rintro ⟨mid, sMid, hmid, hout⟩
    exact ⟨(some mid, sMid), hmid, hout⟩

/-- A guarded first verifier passes the very same shared state to the suffix verifier.
In particular, no assumption of fresh reinitialization is used at the composition boundary. -/
theorem GuardedForm.append_run (G : V₁.GuardedForm)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run stmt tr =
      if G.check stmt tr.fst then V₂.run (G.out stmt tr.fst) tr.snd else failure := by
  change (do
    let mid ← V₁.verify stmt tr.fst
    V₂.verify mid tr.snd) = _
  rw [G.verify_eq stmt tr.fst]
  split <;> simp_all [run]

/-- Positive related-output probability of the append is exactly passage of the first guard
and positive related-output probability of the suffix under the unchanged initialization. -/
theorem GuardedForm.append_related_output_pos_iff (G : V₁.GuardedForm)
    (rel : Set (Stmt₃ × Wit₃)) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (wit : Wit₃) :
    (Pr{let out ← OptionT.mk do
      (simulateQ impl ((V₁.append V₂).run stmt tr)).run' (← init)}[(out, wit) ∈ rel] > 0) ↔
      G.check stmt tr.fst = true ∧
      Pr{let out ← OptionT.mk do
        (simulateQ impl (V₂.run (G.out stmt tr.fst) tr.snd)).run'
          (← init)}[(out, wit) ∈ rel] > 0 := by
  rw [G.append_run stmt tr]
  by_cases h : G.check stmt tr.fst = true
  · simp only [h, ite_true, true_and]
  · simp only [h, Bool.false_eq_true, ite_false, false_and, iff_false]
    change ¬ Pr{let out ← OptionT.mk do
      (simulateQ impl (pure none : OracleComp oSpec (Option Stmt₃))).run'
        (← init)}[(out, wit) ∈ rel] > 0
    rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff]
    simp [StateT.run'_eq]

end Append

section Predicate

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
  {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {W₁ : Fin (m + 1) → Type} {W₂ : Fin (k + 1) → Type}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- Before and at the boundary use the first certificate. After the boundary require its
guard to pass and use the second certificate on the remaining transcript. Unlike ordinary
language-state composition, backward witness extraction supplies the relation at the boundary. -/
def KnowledgeStateFunction.appendPredicate
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (i : Fin (m + k + 1)) (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript i)
    (wit : (Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (by omega)) i) : Prop :=
  if h : i.val ≤ m then
    K₁ ⟨i.val, by omega⟩ stmt
      (fun j => cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        ⟨j.val, by have := j.isLt; omega⟩) (tr ⟨j.val, j.isLt⟩))
      (cast (Extractor.wit_mid_append_left i ⟨i.val, by omega⟩ rfl) wit)
  else
    have hbound : i.val - m < k + 1 := by have := i.isLt; omega
    let tr₁ : pSpec₁.FullTranscript := fun j =>
      cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j)
        (tr ⟨j.val, by have := j.isLt; omega⟩)
    G.check stmt tr₁ = true ∧
      K₂ ⟨i.val - m, hbound⟩ (G.out stmt tr₁)
        (show pSpec₂.Transcript ⟨i.val - m, hbound⟩ from fun j =>
          cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            ⟨j.val, by have hj : j.val < i.val - m := j.isLt; omega⟩)
            (tr ⟨m + j.val, by have hj : j.val < i.val - m := j.isLt; omega⟩))
        (cast (Extractor.wit_mid_append_right i (⟨i.val - m, hbound⟩ : Fin (k + 1))
          (by simp; omega) (by simp; omega)) wit)

/-- The composed predicate has exactly the first input relation at round zero. -/
theorem KnowledgeStateFunction.appendPredicate_zero
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (stmt : Stmt₁)
    (wit : (Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (by omega)) 0) :
    (stmt, cast (E₁.append E₂ G.out).eqIn wit) ∈ rel₁ ↔
      appendPredicate init impl G K₁ K₂ 0 stmt default wit := by
  unfold appendPredicate
  split_ifs with h
  · convert K₁.toFun_empty stmt
      (cast (Extractor.wit_mid_append_left (WitMid₁ := W₁) (WitMid₂ := W₂)
        (0 : Fin (m + k + 1)) 0 rfl) wit) using 1
    · simp only [cast_cast]
    · apply Iff.of_eq
      congr 1
      funext j
      exact Fin.elim0 j
  · exact (h (show (0 : Fin (m + k + 1)).val ≤ m from Nat.zero_le m)).elim

/-- Compare dependent transcripts after identifying their round indices. -/
private theorem transcript_heq_of_val_eq {N : ℕ} {p : ProtocolSpec N}
    {a b : Fin (N + 1)} {t : p.Transcript a} {u : p.Transcript b}
    (hab : a.val = b.val)
    (h : ∀ j (hj : j < a.val) (hj' : j < b.val), HEq (t ⟨j, hj⟩) (u ⟨j, hj'⟩)) :
    HEq t u := by
  obtain rfl := Fin.ext hab
  exact heq_of_eq (funext fun j => eq_of_heq (h j.val j.isLt j.isLt))

/-- Acceptance establishes terminal knowledge, including when the suffix has no messages. -/
theorem KnowledgeStateFunction.appendPredicate_full
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (wit : Wit₃)
    (h : Pr{let out ← OptionT.mk do
      (simulateQ impl ((V₁.append V₂).run stmt tr)).run' (← init)}[(out, wit) ∈ rel₃] > 0) :
    appendPredicate init impl G K₁ K₂ (.last (m + k)) stmt tr
      ((E₁.append E₂ G.out).extractOut stmt tr wit) := by
  obtain ⟨hcheck, hpos⟩ := (G.append_related_output_pos_iff init impl rel₃ stmt tr wit).mp h
  have hK₂ := K₂.toFun_full (G.out stmt tr.fst) tr.snd wit hpos
  by_cases hk : k = 0
  · subst k
    have hrel : (G.out stmt tr.fst,
        cast E₂.eqIn (E₂.extractOut (G.out stmt tr.fst) tr.snd wit)) ∈ rel₂ := by
      apply (K₂.toFun_empty _ _).mpr
      convert hK₂ using 1
      apply Iff.of_eq
      congr 1
      funext j
      exact Fin.elim0 j
    have hK₁ := G.knowledgeState_of_related_output init impl K₁ stmt tr.fst _ hcheck hrel
    simp only [appendPredicate, Extractor.RoundByRound.append, Fin.val_last,
      Nat.add_zero, le_refl, dite_true, Nat.lt_irrefl, dite_false, cast_cast, cast_eq]
    convert hK₁ using 1
    apply Iff.of_eq
    congr 1
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    unfold appendPredicate
    rw [dite_eq_right (show ¬ (Fin.last (m + k)).val ≤ m by simp; omega)]
    constructor
    · exact hcheck
    · simp only [Extractor.RoundByRound.append, dite_eq_left hkpos, cast_cast]
      convert hK₂ using 1
      apply Iff.of_eq
      congr 1
      · apply Fin.ext
        simp
      · apply transcript_heq_of_val_eq (p := pSpec₂)
          (a := ⟨(m + k) - m, by omega⟩) (b := Fin.last k) (by simp)
        intro j hj hj'
        exact (cast_heq _ _).trans (cast_heq _ _).symm
      · exact cast_heq _ _

/-- A prover message strictly inside the first protocol preserves composed knowledge backwards. -/
theorem KnowledgeStateFunction.appendPredicate_next_left
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (j : Fin (m + k)) (hlt : j.val < m)
    (hdir : (pSpec₁ ++ₚ pSpec₂).dir j = .P_to_V)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type j)
    (wit : (Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (by omega)) j.succ)
    (hK : appendPredicate init impl G K₁ K₂ j.succ stmt (tr.concat msg) wit) :
    appendPredicate init impl G K₁ K₂ j.castSucc stmt tr
      ((E₁.append E₂ G.out).extractMid j stmt (tr.concat msg) wit) := by
  have hdir₁ : pSpec₁.dir ⟨j.val, hlt⟩ = .P_to_V := by
    change Fin.vappend pSpec₁.dir pSpec₂.dir j = .P_to_V at hdir
    rwa [Fin.vappend_left_of_lt _ _ j hlt] at hdir
  have htype : (pSpec₁ ++ₚ pSpec₂).Type j = pSpec₁.Type ⟨j.val, hlt⟩ :=
    append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ⟨j.val, hlt⟩
  let T : pSpec₁.Transcript (⟨j.val, hlt⟩ : Fin m).castSucc := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; omega⟩) (tr q)
  let w : W₁ (⟨j.val, hlt⟩ : Fin m).succ :=
    cast (Extractor.wit_mid_append_left j.succ (⟨j.val, hlt⟩ : Fin m).succ rfl) wit
  let U : pSpec₁.Transcript (⟨j.val, hlt⟩ : Fin m).succ := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; omega⟩) (tr.concat msg q)
  have hT : U = T.concat (cast htype msg) := by
    funext q
    apply eq_of_heq
    by_cases hq : q.val < j.val
    · exact ((cast_heq _ _).trans
        (Transcript.concat_apply_lt tr msg q.val hq q.isLt)).trans
        ((Transcript.concat_apply_lt T (cast htype msg) q.val hq q.isLt).trans
          (cast_heq _ _)).symm
    · have heq : q.val = j.val := by have := q.isLt; simp at *; omega
      exact ((cast_heq _ _).trans
        (Transcript.concat_apply_last tr msg q.val heq q.isLt)).trans
        ((Transcript.concat_apply_last T (cast htype msg) q.val heq q.isLt).trans
          (cast_heq _ _)).symm
  have hInner : K₁ (⟨j.val, hlt⟩ : Fin m).succ stmt (T.concat (cast htype msg)) w := by
    unfold appendPredicate at hK
    rw [dite_eq_left (show j.succ.val ≤ m by simp; omega)] at hK
    convert hK using 1
    · rfl
    · exact hT.symm
  have hPrev := K₁.toFun_next ⟨j.val, hlt⟩ hdir₁ stmt T (cast htype msg) w hInner
  unfold appendPredicate
  rw [dite_eq_left (show j.castSucc.val ≤ m from Nat.le_of_lt hlt)]
  simp only [Extractor.RoundByRound.append, dite_eq_left hlt, cast_cast, cast_eq]
  convert hPrev using 1
  · rfl
  · rfl
  · congr 1

/-- A bad transition before the seam is a bad transition of the first component.
This is pointwise in the message, so it also applies to fresh verifier challenges. -/
theorem KnowledgeStateFunction.appendPredicate_badEvent_left
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (j : Fin (m + k)) (hlt : j.val < m)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type j)
    (hbad : ∃ wit,
      ¬ appendPredicate init impl G K₁ K₂ j.castSucc stmt tr
        ((E₁.append E₂ G.out).extractMid j stmt (tr.concat msg) wit) ∧
      appendPredicate init impl G K₁ K₂ j.succ stmt (tr.concat msg) wit) :
    let r : Fin m := ⟨j.val, hlt⟩
    let T : pSpec₁.Transcript r.castSucc := fun q =>
      cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        ⟨q.val, by have := q.isLt; omega⟩) (tr q)
    let c := cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) r) msg
    ∃ w, ¬ K₁ r.castSucc stmt T (E₁.extractMid r stmt (T.concat c) w) ∧
      K₁ r.succ stmt (T.concat c) w := by
  dsimp only
  obtain ⟨wit, hnot, hK⟩ := hbad
  have htype : (pSpec₁ ++ₚ pSpec₂).Type j = pSpec₁.Type ⟨j.val, hlt⟩ :=
    append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) ⟨j.val, hlt⟩
  let T : pSpec₁.Transcript (⟨j.val, hlt⟩ : Fin m).castSucc := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; omega⟩) (tr q)
  let w : W₁ (⟨j.val, hlt⟩ : Fin m).succ :=
    cast (Extractor.wit_mid_append_left j.succ (⟨j.val, hlt⟩ : Fin m).succ rfl) wit
  let U : pSpec₁.Transcript (⟨j.val, hlt⟩ : Fin m).succ := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; omega⟩) (tr.concat msg q)
  have hT : U = T.concat (cast htype msg) := by
    funext q
    apply eq_of_heq
    by_cases hq : q.val < j.val
    · exact ((cast_heq _ _).trans
        (Transcript.concat_apply_lt tr msg q.val hq q.isLt)).trans
        ((Transcript.concat_apply_lt T (cast htype msg) q.val hq q.isLt).trans
          (cast_heq _ _)).symm
    · have heq : q.val = j.val := by have := q.isLt; simp at *; omega
      exact ((cast_heq _ _).trans
        (Transcript.concat_apply_last tr msg q.val heq q.isLt)).trans
        ((Transcript.concat_apply_last T (cast htype msg) q.val heq q.isLt).trans
          (cast_heq _ _)).symm
  refine ⟨w, ?_, ?_⟩
  · intro hPrev
    apply hnot
    unfold appendPredicate
    rw [dite_eq_left (show j.castSucc.val ≤ m from Nat.le_of_lt hlt)]
    simp only [Extractor.RoundByRound.append, dite_eq_left hlt, cast_cast, cast_eq]
    convert hPrev using 1
    · rfl
    · rfl
    · congr 1
  · unfold appendPredicate at hK
    rw [dite_eq_left (show j.succ.val ≤ m by simp; omega)] at hK
    convert hK using 1
    · rfl
    · exact hT.symm

/-- The knowledge-state prover-step rule in terms of an already extended transcript. -/
private theorem knowledge_next_init
    {W : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec W}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (K : V.KnowledgeStateFunction init impl relIn relOut E)
    (j : Fin n) (hdir : pSpec.dir j = .P_to_V) (stmt : StmtIn)
    (tr : pSpec.Transcript j.succ) (wit : W j.succ) (h : K j.succ stmt tr wit) :
    K j.castSucc stmt (Fin.init tr) (E.extractMid j stmt tr wit) := by
  have h' := K.toFun_next j hdir stmt (Fin.init tr) (tr (Fin.last j.val)) wit
  simp only [Transcript.concat, Fin.snoc_init_self] at h'
  exact h' h

/-- At the seam, the suffix's input witness is extracted and then passed to the prefix's
terminal extractor. The guard ensures that this intermediate relation is actually accepted. -/
theorem KnowledgeStateFunction.appendPredicate_next_seam
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (hk : 0 < k) (hdir : pSpec₂.dir ⟨0, hk⟩ = .P_to_V)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ⟨m, by omega⟩)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type ⟨m, by omega⟩)
    (wit : (Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (by omega))
      ⟨m + 1, by omega⟩)
    (hK : appendPredicate init impl G K₁ K₂ ⟨m + 1, by omega⟩ stmt
      (Transcript.concat (m := ⟨m, by omega⟩) msg tr) wit) :
    appendPredicate init impl G K₁ K₂ ⟨m, by omega⟩ stmt tr
      ((E₁.append E₂ G.out).extractMid ⟨m, by omega⟩ stmt (tr.concat msg) wit) := by
  let full : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (Transcript.concat (m := ⟨m, by omega⟩) msg tr
        ⟨q.val, by change q.val < m + 1; have := q.isLt; omega⟩)
  let tail : pSpec₂.Transcript (⟨0, hk⟩ : Fin k).succ := fun q =>
    cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; omega⟩)
      (Transcript.concat (m := ⟨m, by omega⟩) msg tr
        ⟨m + q.val, by change m + q.val < m + 1; have hq : q.val < 1 := q.isLt; omega⟩)
  let w : W₂ (⟨0, hk⟩ : Fin k).succ :=
    cast (Extractor.wit_mid_append_right ⟨m + 1, by omega⟩
      (⟨0, hk⟩ : Fin k).succ (by simp) (by simp)) wit
  have hGood : G.check stmt full = true ∧ K₂ (⟨0, hk⟩ : Fin k).succ
      (G.out stmt full) tail w := by
    unfold appendPredicate at hK
    rw [dite_eq_right (show ¬ (⟨m + 1, by omega⟩ : Fin (m + k + 1)).val ≤ m by simp)] at hK
    convert hK using 1
    apply Iff.of_eq
    congr 1
    · apply Fin.ext
      simp
    · apply transcript_heq_of_val_eq (p := pSpec₂)
        (a := (⟨0, hk⟩ : Fin k).succ) (b := ⟨m + 1 - m, by omega⟩) (by simp)
      intro q hq hq'
      exact (cast_heq _ _).trans (cast_heq _ _).symm
    · exact (cast_heq _ _).trans (cast_heq _ _).symm
  have hPrev := knowledge_next_init init impl K₂ ⟨0, hk⟩ hdir
    (G.out stmt full) tail w hGood.2
  have hrel : (G.out stmt full, cast E₂.eqIn
      (E₂.extractMid ⟨0, hk⟩ (G.out stmt full) tail w)) ∈ rel₂ := by
    apply (K₂.toFun_empty _ _).mpr
    convert hPrev using 1
    apply Iff.of_eq
    congr 1
    funext q
    exact Fin.elim0 q
  have hPrefix := G.knowledgeState_of_related_output init impl K₁ stmt full _ hGood.1 hrel
  unfold appendPredicate
  rw [dite_eq_left (show (⟨m, by omega⟩ : Fin (m + k + 1)).val ≤ m from le_refl m)]
  simp only [Extractor.RoundByRound.append, Nat.lt_irrefl, dite_false, dite_true,
    cast_cast, cast_eq]
  convert hPrefix using 1
  apply Iff.of_eq
  congr 1
  funext q
  exact eq_of_heq ((cast_heq _ _).trans
    ((cast_heq _ _).trans (Transcript.concat_apply_lt tr msg q.val q.isLt
      (by change q.val < m + 1; have := q.isLt; omega))).symm)

/-- Strictly after the seam, a prover step uses the suffix's backward extraction rule.
The first component's completed transcript and guard remain unchanged. -/
theorem KnowledgeStateFunction.appendPredicate_next_right
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (j : Fin (m + k)) (hgt : m < j.val)
    (hdir : (pSpec₁ ++ₚ pSpec₂).dir j = .P_to_V)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type j)
    (wit : (Fin.append (m := m + 1) W₁ (Fin.tail W₂) ∘ Fin.cast (by omega)) j.succ)
    (hK : appendPredicate init impl G K₁ K₂ j.succ stmt (tr.concat msg) wit) :
    appendPredicate init impl G K₁ K₂ j.castSucc stmt tr
      ((E₁.append E₂ G.out).extractMid j stmt (tr.concat msg) wit) := by
  have hb : j.val - m < k := by have := j.isLt; omega
  let r : Fin k := ⟨j.val - m, hb⟩
  have hdir₂ : pSpec₂.dir r = .P_to_V := by
    change Fin.vappend pSpec₁.dir pSpec₂.dir j = .P_to_V at hdir
    rwa [Fin.vappend_right_of_not_lt _ _ j (by omega)] at hdir
  let full : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (tr.concat msg ⟨q.val, by have := q.isLt; change q.val < j.val + 1; omega⟩)
  let before : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (tr ⟨q.val, by have := q.isLt; change q.val < j.val; omega⟩)
  have hfull : before = full := by
    funext q
    exact eq_of_heq ((cast_heq _ _).trans
      ((cast_heq _ _).trans (Transcript.concat_apply_lt tr msg q.val
        (by have := q.isLt; omega) (by have := q.isLt; change q.val < j.val + 1; omega))).symm)
  let tail : pSpec₂.Transcript r.succ := fun q =>
    cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have hq : q.val < j.val - m + 1 := q.isLt; omega⟩)
      (tr.concat msg ⟨m + q.val, by
        have hq : q.val < j.val - m + 1 := q.isLt
        change m + q.val < j.val + 1
        omega⟩)
  let w : W₂ r.succ := cast (Extractor.wit_mid_append_right j.succ r.succ
    (by dsimp [r]; omega) (by simp)) wit
  have hGood : G.check stmt full = true ∧ K₂ r.succ (G.out stmt full) tail w := by
    unfold appendPredicate at hK
    rw [dite_eq_right (show ¬ j.succ.val ≤ m by simp; omega)] at hK
    convert hK using 1
    apply Iff.of_eq
    congr 1
    · apply Fin.ext
      dsimp [r]
      omega
    · apply transcript_heq_of_val_eq (p := pSpec₂) (a := r.succ)
        (b := ⟨j.succ.val - m, by have := j.isLt; simp; omega⟩)
        (by dsimp [r]; omega)
      intro q hq hq'
      exact (cast_heq _ _).trans (cast_heq _ _).symm
    · exact (cast_heq _ _).trans (cast_heq _ _).symm
  have hPrev := knowledge_next_init init impl K₂ r hdir₂ (G.out stmt full) tail w hGood.2
  unfold appendPredicate
  rw [dite_eq_right (show ¬ j.castSucc.val ≤ m from Nat.not_le.mpr hgt)]
  constructor
  · change G.check stmt before = true
    rw [hfull]
    exact hGood.1
  · simp only [Extractor.RoundByRound.append, dite_eq_right (show ¬ j.val < m by omega),
      dite_eq_right (show ¬ j.val = m by omega), cast_cast, cast_eq]
    convert hPrev using 1
    apply Iff.of_eq
    congr 1
    · exact congrArg (G.out stmt) hfull
    · funext q
      exact eq_of_heq ((cast_heq _ _).trans
        ((cast_heq _ _).trans (Transcript.concat_apply_lt tr msg (m + q.val)
          (by have hq : q.val < j.val - m := q.isLt; omega)
          (by have hq : q.val < j.val - m := q.isLt
              change m + q.val < j.val + 1
              omega))).symm)

/-- Compose knowledge certificates when the first verifier is guarded and has no oracle effects.
This certificate alone does not supply the challenge-transition probability bounds. -/
def KnowledgeStateFunction.appendGuarded
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃ (E₁.append E₂ G.out) where
  toFun := appendPredicate init impl G K₁ K₂
  toFun_empty := appendPredicate_zero init impl G K₁ K₂
  toFun_full := appendPredicate_full init impl G K₁ K₂
  toFun_next := by
    intro j hdir stmt tr msg wit hK
    rcases lt_trichotomy j.val m with hlt | heq | hgt
    · exact appendPredicate_next_left init impl G K₁ K₂ j hlt hdir stmt tr msg wit hK
    · have hk : 0 < k := by have := j.isLt; omega
      rcases j with ⟨j, hj⟩
      dsimp at heq
      subst j
      have hdir₂ : pSpec₂.dir ⟨0, hk⟩ = .P_to_V := by
        change Fin.vappend pSpec₁.dir pSpec₂.dir ⟨m, _⟩ = .P_to_V at hdir
        rw [Fin.vappend_right_of_not_lt _ _ ⟨m, hj⟩ (by simp)] at hdir
        simpa only [Nat.sub_self] using hdir
      exact appendPredicate_next_seam init impl G K₁ K₂ hk hdir₂ stmt tr msg wit hK
    · exact appendPredicate_next_right init impl G K₁ K₂ j hgt hdir stmt tr msg wit hK

/-- Every bad transition in the suffix, including its first round, is a suffix bad transition.
The completed first transcript is fixed before the suffix message is sampled. -/
theorem KnowledgeStateFunction.appendPredicate_badEvent_right
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (j : Fin k) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (j.natAdd m).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type (j.natAdd m))
    (hbad : ∃ wit,
      ¬ appendPredicate init impl G K₁ K₂ (j.natAdd m).castSucc stmt tr
        ((E₁.append E₂ G.out).extractMid (j.natAdd m) stmt (tr.concat msg) wit) ∧
      appendPredicate init impl G K₁ K₂ (j.natAdd m).succ stmt (tr.concat msg) wit) :
    let full : pSpec₁.FullTranscript := fun q =>
      cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
        (tr ⟨q.val, by have := q.isLt; change q.val < m + j.val; omega⟩)
    let T : pSpec₂.Transcript j.castSucc := fun q =>
      cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        ⟨q.val, by have hq : q.val < j.val := q.isLt; have := j.isLt; omega⟩)
        (tr ⟨m + q.val, by have hq : q.val < j.val := q.isLt
                           change m + q.val < m + j.val; omega⟩)
    let c := cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j) msg
    ∃ w, ¬ K₂ j.castSucc (G.out stmt full) T
        (E₂.extractMid j (G.out stmt full) (T.concat c) w) ∧
      K₂ j.succ (G.out stmt full) (T.concat c) w := by
  dsimp only
  obtain ⟨wit, hnot, hK⟩ := hbad
  let full : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (tr ⟨q.val, by have := q.isLt; change q.val < m + j.val; omega⟩)
  let after : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (tr.concat msg ⟨q.val, by have := q.isLt; change q.val < m + j.val + 1; omega⟩)
  have hfull : after = full := by
    funext q
    exact eq_of_heq ((cast_heq _ _).trans
      ((Transcript.concat_apply_lt tr msg q.val
        (by have := q.isLt; change q.val < m + j.val; omega)
        (by have := q.isLt; change q.val < m + j.val + 1; omega)).trans
        (cast_heq _ _).symm))
  let T : pSpec₂.Transcript j.castSucc := fun q =>
    cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have hq : q.val < j.val := q.isLt; have := j.isLt; omega⟩)
      (tr ⟨m + q.val, by have hq : q.val < j.val := q.isLt
                         change m + q.val < m + j.val; omega⟩)
  let c := cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j) msg
  let U : pSpec₂.Transcript j.succ := fun q =>
    cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have hq : q.val < j.val + 1 := q.isLt; have := j.isLt; omega⟩)
      (tr.concat msg ⟨m + q.val, by
        have hq : q.val < j.val + 1 := q.isLt
        change m + q.val < m + j.val + 1; omega⟩)
  have hT : U = T.concat c := by
    funext q
    apply eq_of_heq
    by_cases hq : q.val < j.val
    · exact ((cast_heq _ _).trans (Transcript.concat_apply_lt tr msg (m + q.val)
        (by change m + q.val < m + j.val; omega)
        (by change m + q.val < m + j.val + 1; omega))).trans
        ((Transcript.concat_apply_lt T c q.val hq q.isLt).trans (cast_heq _ _)).symm
    · have heq : q.val = j.val := by have := q.isLt; simp at *; omega
      exact ((cast_heq _ _).trans (Transcript.concat_apply_last tr msg (m + q.val)
        (by change m + q.val = m + j.val; omega)
        (by change m + q.val < m + j.val + 1; omega))).trans
        ((Transcript.concat_apply_last T c q.val heq q.isLt).trans (cast_heq _ _)).symm
  let w : W₂ j.succ := cast (Extractor.wit_mid_append_right (j.natAdd m).succ j.succ
    (by simp; omega) (by simp)) wit
  have hGood : G.check stmt full = true ∧ K₂ j.succ (G.out stmt full) (T.concat c) w := by
    unfold appendPredicate at hK
    rw [dite_eq_right (show ¬ (j.natAdd m).succ.val ≤ m by simp)] at hK
    rw [← hfull, ← hT]
    convert hK using 1
    apply Iff.of_eq
    congr 1
    · apply Fin.ext
      simp
      omega
    · apply transcript_heq_of_val_eq (p := pSpec₂) (a := j.succ)
        (b := ⟨(j.natAdd m).succ.val - m, by have := j.isLt; simp; omega⟩)
        (by simp; omega)
      intro q hq hq'
      exact (cast_heq _ _).trans (cast_heq _ _).symm
    · exact (cast_heq _ _).trans (cast_heq _ _).symm
  refine ⟨w, ?_, hGood.2⟩
  intro hPrev
  change K₂ j.castSucc (G.out stmt full) T
    (E₂.extractMid j (G.out stmt full) (T.concat c) w) at hPrev
  apply hnot
  by_cases hj : j.val = 0
  · rcases j with ⟨j, hjlt⟩
    dsimp at hj
    subst j
    have hrel : (G.out stmt full,
        cast E₂.eqIn (E₂.extractMid ⟨0, hjlt⟩ (G.out stmt full) (T.concat c) w)) ∈ rel₂ := by
      apply (K₂.toFun_empty _ _).mpr
      convert hPrev using 1
      apply Iff.of_eq
      congr 1
      funext q
      exact Fin.elim0 q
    have hPrefix := G.knowledgeState_of_related_output init impl K₁ stmt full _ hGood.1 hrel
    unfold appendPredicate
    rw [dite_eq_left (show (Fin.natAdd m (⟨0, hjlt⟩ : Fin k)).castSucc.val ≤ m by simp)]
    simp only [Extractor.RoundByRound.append, Fin.val_natAdd, Fin.val_mk, Nat.add_zero,
      Nat.lt_irrefl, dite_false, dite_true, cast_cast, cast_eq]
    convert hPrefix using 1
    apply Iff.of_eq
    congr 1
    change E₁.extractOut stmt after
      (cast E₂.eqIn (E₂.extractMid ⟨0, hjlt⟩ (G.out stmt after) U w)) = _
    rw [hfull, hT]
  · unfold appendPredicate
    rw [dite_eq_right (show ¬ (j.natAdd m).castSucc.val ≤ m by simp; omega)]
    constructor
    · exact hGood.1
    · simp only [Extractor.RoundByRound.append,
        dite_eq_right (show ¬ (j.natAdd m).val < m by simp),
        dite_eq_right (show ¬ (j.natAdd m).val = m by simp; omega), cast_cast, cast_eq]
      have hsub : m + j.val - m = j.val := by omega
      convert hPrev using 1
      · apply Fin.ext
        exact hsub
      · apply transcript_heq_of_val_eq (p := pSpec₂)
          (a := ⟨(j.natAdd m).castSucc.val - m, by have := j.isLt; simp⟩)
          (b := j.castSucc) hsub
        intro q hq hq'
        exact (cast_heq _ _).trans (cast_heq _ _).symm
      · congr 1
        · exact Fin.ext hsub
        · exact congrArg (G.out stmt) hfull
        · rw [← hT]
          apply transcript_heq_of_val_eq (p := pSpec₂)
            (a := (⟨(j.natAdd m).val - m, by simp⟩ : Fin k).succ)
            (b := j.succ) (by simp)
          intro q hq hq'
          exact (cast_heq _ _).trans (cast_heq _ _).symm
        · exact (cast_heq _ _).trans (cast_heq _ _).symm

variable [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- At each left-component challenge, guarded composition preserves its fixed-prefix error. -/
theorem KnowledgeStateFunction.appendGuarded_bound_left
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (ε₁ : pSpec₁.ChallengeIdx → ℝ≥0)
    (h₁ : V₁.rbrKnowledgeSoundnessWith init impl rel₁ rel₂ W₁ E₁ K₁ ε₁)
    (stmt : Stmt₁) (i : pSpec₁.ChallengeIdx)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl i).1.castSucc) :
    Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))}[
      ∃ wit, ¬ appendPredicate init impl G K₁ K₂ (ChallengeIdx.inl i).1.castSucc stmt tr
        ((E₁.append E₂ G.out).extractMid (ChallengeIdx.inl i).1 stmt (tr.concat c) wit) ∧
        appendPredicate init impl G K₁ K₂ (ChallengeIdx.inl i).1.succ stmt
          (tr.concat c) wit] ≤ ε₁ i := by
  let T : pSpec₁.Transcript i.1.castSucc := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have := q.isLt; have := i.1.isLt; omega⟩) (tr q)
  calc
    _ ≤ Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))}[
          ∃ w, ¬ K₁ i.1.castSucc stmt T
            (E₁.extractMid i.1 stmt (T.concat (cast (challenge_append_inl i) c)) w) ∧
            K₁ i.1.succ stmt (T.concat (cast (challenge_append_inl i) c)) w] := by
      apply prEvent_mono
      intro c hc
      exact appendPredicate_badEvent_left init impl G K₁ K₂
        (ChallengeIdx.inl i).1 i.1.isLt stmt tr c hc
    _ = Pr{let c ← $ᵗ (pSpec₁.Challenge i)}[
          ∃ w, ¬ K₁ i.1.castSucc stmt T (E₁.extractMid i.1 stmt (T.concat c) w) ∧
            K₁ i.1.succ stmt (T.concat c) w] := by
      rw [← uniformSample_challenge_append_inl (pSpec₂ := pSpec₂) i, prEvent_map]
    _ ≤ _ := h₁ stmt i T

/-- At each suffix challenge, including the seam, preserve the suffix's fixed-prefix error. -/
theorem KnowledgeStateFunction.appendGuarded_bound_right
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessWith init impl rel₂ rel₃ W₂ E₂ K₂ ε₂)
    (stmt : Stmt₁) (i : pSpec₂.ChallengeIdx)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr i).1.castSucc) :
    Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
      ∃ wit, ¬ appendPredicate init impl G K₁ K₂ (ChallengeIdx.inr i).1.castSucc stmt tr
        ((E₁.append E₂ G.out).extractMid (ChallengeIdx.inr i).1 stmt (tr.concat c) wit) ∧
        appendPredicate init impl G K₁ K₂ (ChallengeIdx.inr i).1.succ stmt
          (tr.concat c) wit] ≤ ε₂ i := by
  let full : pSpec₁.FullTranscript := fun q =>
    cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) q)
      (tr ⟨q.val, by have := q.isLt; change q.val < m + i.1.val; omega⟩)
  let T : pSpec₂.Transcript i.1.castSucc := fun q =>
    cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      ⟨q.val, by have hq : q.val < i.1.val := q.isLt; have := i.1.isLt; omega⟩)
      (tr ⟨m + q.val, by have hq : q.val < i.1.val := q.isLt
                         change m + q.val < m + i.1.val; omega⟩)
  calc
    _ ≤ Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
          ∃ w, ¬ K₂ i.1.castSucc (G.out stmt full) T
            (E₂.extractMid i.1 (G.out stmt full) (T.concat (cast (challenge_append_inr i) c)) w) ∧
            K₂ i.1.succ (G.out stmt full) (T.concat (cast (challenge_append_inr i) c)) w] := by
      apply prEvent_mono
      intro c hc
      exact appendPredicate_badEvent_right init impl G K₁ K₂ i.1 stmt tr c hc
    _ = Pr{let c ← $ᵗ (pSpec₂.Challenge i)}[
          ∃ w, ¬ K₂ i.1.castSucc (G.out stmt full) T
            (E₂.extractMid i.1 (G.out stmt full) (T.concat c) w) ∧
            K₂ i.1.succ (G.out stmt full) (T.concat c) w] := by
      rw [← uniformSample_challenge_append_inr (pSpec₁ := pSpec₁) i, prEvent_map]
    _ ≤ _ := h₂ (G.out stmt full) i T

/-- Guarded-first append preserves fixed-prefix round-by-round knowledge errors.
The suffix may query the shared oracle; the first verifier cannot alter its starting state. -/
theorem append_rbrKnowledgeSoundness_of_guarded_first
    (G : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨W₁, E₁, K₁, h₁⟩ := h₁
  obtain ⟨W₂, E₂, K₂, h₂⟩ := h₂
  refine ⟨_, E₁.append E₂ G.out, K₁.appendGuarded init impl G K₂, ?_⟩
  intro stmt i
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    convert
      KnowledgeStateFunction.appendGuarded_bound_left init impl G K₁ K₂ ε₁ h₁ stmt i
      using 1
    rfl
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    convert
      KnowledgeStateFunction.appendGuarded_bound_right init impl G K₁ K₂ ε₂ h₂ stmt i
      using 1
    rfl

/-- The fixed-prefix guarded composition theorem also supplies the averaged RBR contract. -/
theorem append_rbrKnowledgeSoundnessAveraged_of_guarded_first
    (G : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessAveraged init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl
    (append_rbrKnowledgeSoundness_of_guarded_first init impl G h₁ h₂)

end Predicate

end Verifier
