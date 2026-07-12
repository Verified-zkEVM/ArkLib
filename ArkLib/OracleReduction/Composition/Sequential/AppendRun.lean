/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-! # Running an Appended Prover: the Challenge-Free Composition Theorem

This file proves `Prover.append_run` (stated with a `sorry` in
`Composition/Sequential/Append.lean`) for **challenge-free** (message-only)
protocols — the class produced by the commitment / BCS transform — at fully
general arity: `append_run_of_challenge_free` (right protocol non-empty),
`append_run_of_challenge_free_zero` (empty right protocol, vacuously
challenge-free), and `append_run_of_challenge_free_liftM` (the statement
spelled exactly as the library's `Prover.append_run`).

The proof is a three-layer construction:
1. a per-round **field layer** (send/receive/output equations for
   `Prover.append` at abstract indices, `HEq`-stated to stay transport-free);
2. two **run invariants**: the left region (`runToRound` below the boundary is
   `P₁`'s run, lifted and transported) and the right region (past the boundary
   it is `P₁`'s full run, the `P₁.output ∘ P₂.input` handoff, then `P₂`'s run,
   glued along `trGlue` — the library's `happend` transported along the
   spec-level right-prefix identity `take_append_add`);
3. the **assembly** at `Fin.last`.

All theorems carry the standard axiom footprint
`[propext, Classical.choice, Quot.sound]` (checked with `#print axioms`), and
the top-level statements are verified non-vacuous (not closed by `rfl`).

The general (non-challenge-free) case additionally needs an alignment of the
composed challenge oracle with the components' — a separate development.
-/

open ProtocolSpec OracleSpec OracleComp

namespace AppendGeneral

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

/-- **G-L1 (left region, general)**: the appended prover's message at a
left-embedded index is P₁'s, up to the state/result transports. Stated with
`HEq` on the payload to stay cast-free at abstract indices. -/
theorem append_sendMessage_left_general
    {i : ℕ} (hi : i < m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨i, by omega⟩ = .P_to_V)
    (hDir₁ : pSpec₁.dir ⟨i, hi⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨i, by omega⟩)) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨i, by omega⟩, hDir⟩ st)
      (P₁.sendMessage ⟨⟨i, hi⟩, hDir₁⟩
        (cast (by
          simp only [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT,
            Fin.castSucc, Fin.castAdd, Function.comp]
          rw [dif_pos (show ((Fin.castLE (by omega) (⟨i, by omega⟩ : Fin (m + n))) :
            Fin (m + n + 1)).val < m + 1 from Nat.lt_succ_of_lt hi)]
          rfl) st)) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_pos (show (⟨i, by omega⟩ : Fin (m + n)).val < m from hi)]
  refine (cast_heq _ _).trans ?_
  congr 1

/-- **G-L2 (left region, challenges)**: same recipe for receiveChallenge. -/
theorem append_receiveChallenge_left_general
    {i : ℕ} (hi : i < m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨i, by omega⟩ = .V_to_P)
    (hDir₁ : pSpec₁.dir ⟨i, hi⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨i, by omega⟩)) :
    HEq ((P₁.append P₂).receiveChallenge ⟨⟨i, by omega⟩, hDir⟩ st)
      (P₁.receiveChallenge ⟨⟨i, hi⟩, hDir₁⟩
        (cast (by
          simp only [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT,
            Fin.castSucc, Fin.castAdd, Function.comp]
          rw [dif_pos (show ((Fin.castLE (by omega) (⟨i, by omega⟩ : Fin (m + n))) :
            Fin (m + n + 1)).val < m + 1 from Nat.lt_succ_of_lt hi)]
          rfl) st)) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_pos (show (⟨i, by omega⟩ : Fin (m + n)).val < m from hi)]
  refine (cast_heq _ _).trans ?_
  congr 1

/-- **G-L3 (the boundary, general)**: at index m (requires n ≠ 0 so index m is
a real round), the appended message is the fused handoff. -/
theorem append_sendMessage_boundary_general (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨m, by omega⟩)) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩ st)
      ((do
        let ctx₂ ← P₁.output (cast (by
          simp only [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT,
            Fin.castSucc, Fin.castAdd, Function.comp]
          rw [dif_pos (show ((Fin.castLE (by omega) (⟨m, by omega⟩ : Fin (m + n))) :
            Fin (m + n + 1)).val < m + 1 from Nat.lt_succ_self m)]
          rfl) st)
        P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctx₂)) :
          OracleComp oSpec _) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (show ¬ (⟨m, by omega⟩ : Fin (m + n)).val < m from Nat.lt_irrefl m)]
  rw [dif_pos trivial]
  refine (cast_heq _ _).trans ?_
  congr 1

/-- **G-L4 (right region, general)**: transport-free form — the two states
are given at their own natural types, related by `HEq`. -/
theorem append_sendMessage_right_general
    {j : ℕ} (hj : j + 1 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + 1 + j, by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨1 + j, by omega⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨m + 1 + j, by omega⟩))
    (st₂ : P₂.PrvState (Fin.castSucc ⟨1 + j, by omega⟩))
    (hst : HEq st st₂) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m + 1 + j, by omega⟩, hDir⟩ st)
      (P₂.sendMessage ⟨⟨1 + j, by omega⟩, hDir₂⟩ st₂) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (show ¬ m + 1 + j < m from Nat.not_lt.mpr (by omega))]
  rw [dif_neg (show ¬ m + 1 + j = m from by omega)]
  refine (cast_heq _ _).trans ?_
  congr 1
  · exact Subtype.ext (Fin.ext (show m + 1 + j - m = 1 + j by omega))
  · exact (heq_of_dcast _ rfl).symm.trans ((cast_heq _ _).trans hst)

/-- **G-L4c (right region, challenges)**: transport-free form. -/
theorem append_receiveChallenge_right_general
    {j : ℕ} (hj : j + 1 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + 1 + j, by omega⟩ = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨1 + j, by omega⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨m + 1 + j, by omega⟩))
    (st₂ : P₂.PrvState (Fin.castSucc ⟨1 + j, by omega⟩))
    (hst : HEq st st₂) :
    HEq ((P₁.append P₂).receiveChallenge ⟨⟨m + 1 + j, by omega⟩, hDir⟩ st)
      (P₂.receiveChallenge ⟨⟨1 + j, by omega⟩, hDir₂⟩ st₂) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (show ¬ m + 1 + j < m from Nat.not_lt.mpr (by omega))]
  rw [dif_neg (show ¬ m + 1 + j = m from by omega)]
  refine (cast_heq _ _).trans ?_
  congr 1
  · exact Subtype.ext (Fin.ext (show m + 1 + j - m = 1 + j by omega))
  · exact (heq_of_dcast _ rfl).symm.trans ((cast_heq _ _).trans hst)

/-- **G-L5 (output, n ≠ 0)**: the appended output is P₂'s, transport-free. -/
theorem append_output_general (hn : n ≠ 0)
    (st : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (st₂ : P₂.PrvState (Fin.last n))
    (hst : HEq st st₂) :
    (P₁.append P₂).output st = P₂.output st₂ := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg hn]
  congr 1
  exact eq_of_heq ((heq_of_dcast _ rfl).symm.trans ((cast_heq _ _).trans hst))

/-! ## Induction prerequisites: direction alignment + transcript embedding -/

/-- Directions agree on the left region. -/
theorem dir_left {i : ℕ} (hi : i < m) :
    (pSpec₁ ++ₚ pSpec₂).dir ⟨i, by omega⟩ = pSpec₁.dir ⟨i, hi⟩ := by
  simp only [ProtocolSpec.append, Fin.vappend_eq_append]
  exact congrArg _ (by
    rw [show (⟨i, by omega⟩ : Fin (m + n)) = Fin.castAdd n ⟨i, hi⟩ from rfl])
    |>.trans (Fin.append_left _ _ _)

/-- Directions agree on the right region (past the boundary). -/
theorem dir_right {j : ℕ} (hj : j < n) :
    (pSpec₁ ++ₚ pSpec₂).dir ⟨m + j, by omega⟩ = pSpec₂.dir ⟨j, hj⟩ := by
  simp only [ProtocolSpec.append, Fin.vappend_eq_append]
  exact congrArg _ (by
    rw [show (⟨m + j, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨j, hj⟩ from rfl])
    |>.trans (Fin.append_right _ _ _)

/-- **G-S1 (left-region state reduction, full range)**: the appended prover's
state type on the entire closed left region [0,m] is P₁'s. Extends the
per-index field lemmas to a uniform statement over the whole region --- the
shape a left-phase induction consumes. -/
theorem PrvState_left (k : Fin (m + 1)) :
    (P₁.append P₂).PrvState (Fin.castLE (by omega) k) = P₁.PrvState k := by
  simp only [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, Function.comp]
  split
  · congr 1
  · rename_i h
    exact absurd (a := (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) k).val < m + 1)
      (by simpa using k.isLt) h

/-! ## Phase 1 bricks (unblocked 2026-07-11 by the SeqCompose splitter repair,
    ArkLib PR #641): the left-region transcript transport. -/

/-- **B0**: the `k ≤ m` prefix of an appended protocol IS the `k`-prefix of the
left protocol. Generalizes `take_append_left` (the `k = m` case). -/
theorem take_append_of_le {k : ℕ} (hk : k ≤ m) :
    (pSpec₁ ++ₚ pSpec₂).take k (by omega) = pSpec₁.take k hk := by
  ext i
  · show (pSpec₁ ++ₚ pSpec₂).dir (Fin.castLE (by omega) i) = pSpec₁.dir (Fin.castLE hk i)
    rw [show Fin.castLE (show k ≤ m + n by omega) i
      = Fin.castAdd n (Fin.castLE hk i) from rfl]
    simp only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
  · show (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castLE (by omega) i) = pSpec₁.«Type» (Fin.castLE hk i)
    rw [show Fin.castLE (show k ≤ m + n by omega) i
      = Fin.castAdd n (Fin.castLE hk i) from rfl]
    exact ProtocolSpec.append_Type_castAdd _

/-- **B1**: transcript transport along B0 — for `k ≤ m`, a partial transcript of
`pSpec₁` is a partial transcript of the appended protocol at the same round. -/
def trLeft (k : Fin (m + 1)) (T : pSpec₁.Transcript k) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castLE (by omega) k) :=
  _root_.cast (congrArg FullTranscript (take_append_of_le k.is_le).symm) T

/-- **B1'**: pointwise behavior of a spec-cast on full transcripts. -/
theorem cast_fullTranscript_apply {N : ℕ} {s t : ProtocolSpec N} (h : s = t)
    (T : FullTranscript s) (j : Fin N) :
    HEq ((_root_.cast (congrArg FullTranscript h) T) j) (T j) := by
  subst h; rfl

/-- **B2**: the left transcript transport commutes with `concat` (= `Fin.snoc`):
transporting after appending a message equals appending the (type-transported)
message after transporting. -/
theorem trLeft_concat (i : Fin m) (T : pSpec₁.Transcript i.castSucc)
    (msg : pSpec₁.«Type» i) :
    trLeft (pSpec₂ := pSpec₂) i.succ (T.concat msg) =
      Transcript.concat (m := Fin.castAdd n i)
        (_root_.cast (ProtocolSpec.append_Type_castAdd i).symm msg)
        (trLeft i.castSucc T) := by
  funext j
  refine eq_of_heq ((cast_fullTranscript_apply
    ((take_append_of_le (pSpec₂ := pSpec₂) (i.succ).is_le).symm)
    (T.concat msg) j).trans ?_)
  induction j using Fin.lastCases with
  | last =>
    rw [show (T.concat msg) (Fin.last _) = msg from Fin.snoc_last _ _]
    rw [show Transcript.concat (m := Fin.castAdd n i)
        (_root_.cast (ProtocolSpec.append_Type_castAdd i).symm msg)
        (trLeft i.castSucc T) (Fin.last _)
      = _root_.cast (ProtocolSpec.append_Type_castAdd i).symm msg from Fin.snoc_last _ _]
    exact (cast_heq _ _).symm
  | cast j' =>
    rw [show (T.concat msg) (Fin.castSucc j') = T j' from Fin.snoc_castSucc _ _ _]
    rw [show Transcript.concat (m := Fin.castAdd n i)
        (_root_.cast (ProtocolSpec.append_Type_castAdd i).symm msg)
        (trLeft i.castSucc T) (Fin.castSucc j')
      = trLeft i.castSucc T j' from Fin.snoc_castSucc _ _ _]
    exact (cast_fullTranscript_apply
      ((take_append_of_le (pSpec₂ := pSpec₂) (i.castSucc).is_le).symm)
      T j').symm

/-- **B5**: `liftM` commutes with a result-type cast. -/
theorem liftM_cast_comm {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery S₁) (OracleQuery S₂)]
    {α β : Type} (h : α = β) (x : OracleComp S₁ α) :
    (liftM (_root_.cast (congrArg (OracleComp S₁) h) x) : OracleComp S₂ β)
      = _root_.cast (congrArg (OracleComp S₂) h) (liftM x) := by
  subst h; rfl

/-- **B6**: a result-type cast on the source of a bind moves into the
continuation. -/
theorem cast_bind {ι₂ : Type} {S₂ : OracleSpec ι₂}
    {α β γ : Type} (h : α = β) (x : OracleComp S₂ α)
    (f : β → OracleComp S₂ γ) :
    (_root_.cast (congrArg (OracleComp S₂) h) x) >>= f
      = x >>= (fun a => f (_root_.cast h a)) := by
  subst h; rfl

/-- **B7**: a cast along a product-type equality acts componentwise. -/
theorem cast_prod_fst {α α' β β' : Type} (h₁ : α = α') (h₂ : β = β') (p : α × β) :
    (_root_.cast (congrArg₂ Prod h₁ h₂) p).1 = _root_.cast h₁ p.1 := by
  subst h₁; subst h₂; rfl

theorem cast_prod_snd {α α' β β' : Type} (h₁ : α = α') (h₂ : β = β') (p : α × β) :
    (_root_.cast (congrArg₂ Prod h₁ h₂) p).2 = _root_.cast h₂ p.2 := by
  subst h₁; subst h₂; rfl

/-- **B3**: the appended prover's input is P₁'s input, transport-free. -/
theorem append_input_general (ctx : Stmt₁ × Wit₁) :
    HEq ((P₁.append P₂).input ctx) (P₁.input ctx) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  exact cast_heq _ _

/-- **B4**: the two lift routes from `oSpec` into the composed challenge sum
agree (query-level `rfl` + induction). -/
theorem liftM_liftM_challenge {α : Type} (x : OracleComp oSpec α) :
    (liftM (liftM x : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
    = liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
  induction x using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih => simp [ih]; rfl

/-- **PHASE 1 invariant (challenge-free, DEVELOPMENT — succ case open)**:
on the left region, the appended prover's partial run is P₁'s partial run,
lifted into the composed challenge sum and transported along B1/G-S1. -/
theorem append_runToRound_left_of_challenge_free
    (hCF : ∀ i, pSpec₁.dir i = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁) (k : Fin (m + 1)) :
    (P₁.append P₂).runToRound (Fin.castLE (by omega) k) stmt wit
      = (fun p => (trLeft k p.1, _root_.cast (PrvState_left P₁ P₂ k).symm p.2)) <$>
          (liftM (P₁.runToRound k stmt wit) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  induction k using Fin.induction with
  | zero =>
    show Prover.runToRound 0 stmt wit (P₁.append P₂) = _
    rw [Prover.runToRound_zero_of_prover_first, Prover.runToRound_zero_of_prover_first]
    rw [liftM_pure, map_pure]
    refine congrArg pure (Prod.ext ?_ ?_)
    · exact Subsingleton.elim _ _
    · exact eq_of_heq ((append_input_general P₁ P₂ (stmt, wit)).trans
        (cast_heq ((PrvState_left P₁ P₂ 0).symm) (P₁.input (stmt, wit))).symm)
  | succ i ih =>
    show Prover.runToRound (Fin.castAdd n i).succ stmt wit (P₁.append P₂) = _
    rw [Prover.runToRound_succ]
    rw [show Prover.runToRound (Fin.castAdd n i).castSucc stmt wit (P₁.append P₂)
        = Prover.runToRound (Fin.castLE (by omega : m + 1 ≤ m + n + 1) i.castSucc)
            stmt wit (P₁.append P₂) from rfl]
    rw [ih]
    rw [Prover.runToRound_succ]
    simp only [Prover.processRound]
    erw [bind_map_left]
    erw [liftM_bind]
    erw [map_bind]
    apply bind_congr
    intro a
    have hDirApp : (pSpec₁.dir ++ᵛ pSpec₂.dir) (Fin.castAdd n i) = Direction.P_to_V := by
      rw [Fin.vappend_eq_append, Fin.append_left]; exact hCF i
    split
    · rename_i hDir
      rw [hDirApp] at hDir
      exact absurd hDir (by simp)
    rename_i hDir
    split
    · rename_i hDir₁
      rw [hCF i] at hDir₁
      exact absurd hDir₁ (by simp)
    rename_i hDir₁
    -- Field lemma: the appended sendMessage is P₁'s, with the state casts collapsed
    have hsend : HEq
        ((P₁.append P₂).sendMessage ⟨Fin.castAdd n i, hDir⟩
          (_root_.cast (PrvState_left P₁ P₂ i.castSucc).symm a.2))
        (P₁.sendMessage ⟨i, hDir₁⟩ a.2) := by
      refine (append_sendMessage_left_general P₁ P₂ i.isLt hDir hDir₁ _).trans ?_
      refine heq_of_eq (congrArg _ ?_)
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    have hMsg : pSpec₁.«Type» i = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n i) :=
      (ProtocolSpec.append_Type_castAdd i).symm
    have hSt : P₁.PrvState i.succ = (P₁.append P₂).PrvState (Fin.castAdd n i).succ :=
      (PrvState_left P₁ P₂ i.succ).symm
    have hXeq : (P₁.append P₂).sendMessage ⟨Fin.castAdd n i, hDir⟩
          (_root_.cast (PrvState_left P₁ P₂ i.castSucc).symm a.2)
        = _root_.cast (congrArg (OracleComp oSpec) (congrArg₂ Prod hMsg hSt))
            (P₁.sendMessage ⟨i, hDir₁⟩ a.2) :=
      (cast_eq_iff_heq.mpr hsend.symm).symm
    simp only []
    erw [hXeq]
    rw [liftM_cast_comm (congrArg₂ Prod hMsg hSt),
      cast_bind (congrArg₂ Prod hMsg hSt)]
    erw [liftM_bind, map_bind]
    rw [liftM_liftM_challenge]
    congr 1
    funext r
    rw [liftM_pure, map_pure]
    simp only []
    refine congrArg pure (Prod.ext ?_ ?_)
    · simp only []
      rw [cast_prod_fst hMsg hSt]
      exact (trLeft_concat i a.1 r.1).symm
    · simp only []
      rw [cast_prod_snd hMsg hSt]
      rfl

/-! ## Phase 2 bricks (2026-07-12 session): boundary handoff + right region.
    Categorical shape: the right region is P₂'s machine under the décalage
    functor (`Fin.tail` in `PrvState`); the glue transport is the library's
    own `happend`, transported along a spec-level right-prefix identity
    (mirror of B0); `happend_succ` is the snoc-interchange cell. -/

/-- **R-V**: `Fin.take` distributes over `Fin.vappend` at split point `m + j`
(non-dependent families — no motive hazards). -/
theorem vappend_take {γ : Sort*} (f : Fin m → γ) (g : Fin n → γ) {j : ℕ} (hj : j ≤ n) :
    Fin.take (m + j) (by omega) (Fin.vappend f g) = Fin.vappend f (Fin.take j hj g) := by
  funext i
  simp only [Fin.take_apply, Fin.vappend_eq_append]
  by_cases hi : i.val < m
  · rw [show Fin.castLE (show m + j ≤ m + n by omega) i = Fin.castAdd n ⟨i.val, hi⟩ from rfl]
    conv_rhs => rw [show i = Fin.castAdd j ⟨i.val, hi⟩ from rfl]
    rw [Fin.append_left, Fin.append_left]
  · have h1 : Fin.castLE (show m + j ≤ m + n by omega) i
      = Fin.natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    have h2 : i = Fin.natAdd m ⟨i.val - m, by omega⟩ := by ext; simp; omega
    rw [h1]
    conv_rhs => rw [h2]
    rw [Fin.append_right, Fin.append_right, Fin.take_apply]
    rfl

/-- **R0 (spec-level right-prefix identity)**: the `(m+j)`-prefix of an appended
protocol is the left protocol appended with the `j`-prefix of the right. Mirror
of B0 (`take_append_of_le`); B0 is the `j = 0` shadow, `take_append_left` the
`j = n` full case — this is the general interpolant. -/
theorem take_append_add {j : ℕ} (hj : j ≤ n) :
    (pSpec₁ ++ₚ pSpec₂).take (m + j) (by omega) = pSpec₁ ++ₚ (pSpec₂.take j hj) := by
  simp only [ProtocolSpec.take, ProtocolSpec.append]
  congr 1
  · exact vappend_take pSpec₁.dir pSpec₂.dir hj
  · exact vappend_take pSpec₁.«Type» pSpec₂.«Type» hj

/-- **R1 (the glue transport)**: a full left transcript and a partial right
transcript glue to a partial transcript of the appended protocol past the
boundary. Constructively this is the library's `happend` transported along R0
— no new data, only a change of presentation. -/
def trGlue (j : Fin (n + 1)) (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript j) :
    (pSpec₁ ++ₚ pSpec₂).Transcript ⟨m + j.val, by omega⟩ :=
  _root_.cast (congrArg FullTranscript (take_append_add j.is_le).symm)
    (FullTranscript.append T₁ T₂)

/-- **R2 (glue–concat interchange)**: gluing after appending a message on the
right equals appending the (type-transported) message after gluing. -/
theorem trGlue_concat (r : Fin n) (T₁ : pSpec₁.FullTranscript)
    (T₂ : pSpec₂.Transcript r.castSucc) (msg : pSpec₂.«Type» r) :
    trGlue r.succ T₁ (T₂.concat msg) =
      Transcript.concat (m := Fin.natAdd m r)
        (_root_.cast (ProtocolSpec.append_Type_natAdd r).symm msg)
        (trGlue r.castSucc T₁ T₂) := by
  funext i
  refine eq_of_heq ((cast_fullTranscript_apply
    ((take_append_add (pSpec₁ := pSpec₁) (r.succ).is_le).symm)
    (FullTranscript.append T₁ (T₂.concat msg)) i).trans ?_)
  induction i using Fin.lastCases with
  | last =>
    refine (heq_of_eq (Fin.happend_right T₁ (Transcript.concat msg T₂)
      (Fin.last r.val))).trans ((cast_heq _ _).trans ?_)
    refine (heq_of_eq (Fin.snoc_last _ _)).trans ?_
    exact ((cast_heq ((ProtocolSpec.append_Type_natAdd r).symm) msg).symm).trans
      (heq_of_eq (Fin.snoc_last
        (α := fun j => ((pSpec₁ ++ₚ pSpec₂)⟦:(m + r.val + 1)⟧).«Type» j)
        (_root_.cast (ProtocolSpec.append_Type_natAdd r).symm msg)
        (trGlue r.castSucc T₁ T₂))).symm
  | cast i' =>
    by_cases hi : i'.val < m
    · refine (heq_of_eq (Fin.happend_left T₁ (Transcript.concat msg T₂)
        ⟨i'.val, hi⟩)).trans ((cast_heq _ _).trans (HEq.symm ?_))
      refine (heq_of_eq (Fin.snoc_castSucc _ _ i')).trans ?_
      refine (cast_fullTranscript_apply
        ((take_append_add (pSpec₁ := pSpec₁) (r.castSucc).is_le).symm)
        (FullTranscript.append T₁ T₂) i').trans ?_
      exact (heq_of_eq (Fin.happend_left T₁ T₂ ⟨i'.val, hi⟩)).trans (cast_heq _ _)
    · obtain ⟨d, hd⟩ : ∃ d, i'.val = m + d := ⟨i'.val - m, by omega⟩
      have hlt : i'.val < m + r.val := i'.isLt
      have hd' : d < r.val := by omega
      have hidx : i' = Fin.natAdd m ⟨d, hd'⟩ := by ext; simp [hd]
      subst hidx
      refine (heq_of_eq (Fin.happend_right T₁ (Transcript.concat msg T₂)
        (Fin.castSucc ⟨d, hd'⟩))).trans ((cast_heq _ _).trans ?_)
      refine (heq_of_eq (Fin.snoc_castSucc _ _ ⟨d, hd'⟩)).trans (HEq.symm ?_)
      refine (heq_of_eq (Fin.snoc_castSucc _ _ (Fin.natAdd m ⟨d, hd'⟩))).trans ?_
      refine (cast_fullTranscript_apply
        ((take_append_add (pSpec₁ := pSpec₁) (r.castSucc).is_le).symm)
        (FullTranscript.append T₁ T₂) (Fin.natAdd m ⟨d, hd'⟩)).trans ?_
      exact (heq_of_eq (Fin.happend_right T₁ T₂ ⟨d, hd'⟩)).trans (cast_heq _ _)

/-- **R3 (glue at zero is the left transport at the boundary)**. -/
theorem trGlue_zero (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript 0) :
    trGlue 0 T₁ T₂ = trLeft (pSpec₂ := pSpec₂) (Fin.last m) T₁ := by
  funext i
  have hi : i.val < m := i.isLt
  refine eq_of_heq (((cast_fullTranscript_apply
    ((take_append_add (pSpec₁ := pSpec₁) (0 : Fin (n+1)).is_le).symm)
    (FullTranscript.append T₁ T₂) i).trans ?_).trans
    (cast_fullTranscript_apply
      ((take_append_of_le (pSpec₂ := pSpec₂) (Fin.last m).is_le).symm) T₁ i).symm)
  exact (heq_of_eq (Fin.happend_left T₁ T₂ ⟨i.val, hi⟩)).trans (cast_heq _ _)

/-- **R4 (glue at full length is the library append)**. -/
theorem trGlue_full (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript (Fin.last n)) :
    trGlue (Fin.last n) T₁ T₂
      = (FullTranscript.append (pSpec₂ := pSpec₂) T₁ T₂ :
          (i : Fin (m + n)) → ((pSpec₁ ++ₚ pSpec₂).«Type» i)) :=
  cast_eq_iff_heq.mpr HEq.rfl

/-- **R5 (right-region state décalage)**: past the boundary, the appended
prover's state is P₂'s, shifted by one (`Fin.tail` in `Prover.append`). -/
theorem PrvState_right {jv : ℕ} (hjv : jv < n) :
    (P₁.append P₂).PrvState ⟨m + (jv + 1), by omega⟩ = P₂.PrvState ⟨jv + 1, by omega⟩ := by
  show Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState)
    (Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (⟨m + (jv + 1), by omega⟩ : Fin (m + n + 1))) = _
  rw [show (Fin.cast (by omega : m + n + 1 = m + 1 + n)
      (⟨m + (jv + 1), by omega⟩ : Fin (m + n + 1)) : Fin (m + 1 + n))
    = Fin.natAdd (m + 1) ⟨jv, hjv⟩ from Fin.ext (by simp; omega)]
  rw [Fin.append_right]
  show P₂.PrvState (⟨jv, hjv⟩ : Fin n).succ = _
  rfl

/-- **R6 (B4 mirror for the right challenge sum)**. -/
theorem liftM_liftM_challenge₂ {α : Type} (x : OracleComp oSpec α) :
    (liftM (liftM x : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
    = liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
  induction x using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih => simp [ih]; rfl

/-- **R7 (G-L4 at the reducing spelling)**: right-region sendMessage, indices
pinned at `jv+1` (the spelling `m + (jv+1)` definitionally reduces to
`(m+jv)+1`, which `runToRound_succ` needs; `m+1+jv` does not). -/
theorem append_sendMessage_right' {jv : ℕ} (hj : jv + 1 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + (jv + 1), by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨jv + 1, hj⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState (Fin.castSucc ⟨m + (jv + 1), by omega⟩))
    (st₂ : P₂.PrvState (Fin.castSucc ⟨jv + 1, by omega⟩))
    (hst : HEq st st₂) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m + (jv + 1), by omega⟩, hDir⟩ st)
      (P₂.sendMessage ⟨⟨jv + 1, by omega⟩, hDir₂⟩ st₂) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_neg (show ¬ m + (jv + 1) < m from by omega)]
  rw [dif_neg (show ¬ m + (jv + 1) = m from by omega)]
  refine (cast_heq _ _).trans ?_
  congr 1
  · exact Subtype.ext (Fin.ext (show m + (jv + 1) - m = jv + 1 by omega))
  · exact (heq_of_dcast _ rfl).symm.trans ((cast_heq _ _).trans hst)

include P₁ P₂ in
/-- **R6' (R6 with `liftComp`-spelled outer lift)**. -/
theorem liftComp_liftM_challenge₂ {α : Type} (x : OracleComp oSpec α) :
    liftComp (liftM x : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α)
      (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    = liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :=
  liftM_liftM_challenge₂ x

/-- **PHASE 2 invariant (challenge-free, right region)**: past the boundary,
the appended prover's partial run is P₁'s full run, the handoff, and P₂'s
partial run — glued and transported. All indices pinned at the reducing
`jv+1` spelling. DEVELOPMENT: succ case open. -/
theorem append_runToRound_right_of_challenge_free
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V) (hCF₂ : ∀ i, pSpec₂.dir i = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁) (jv : ℕ) (hjv : jv < n) :
    (P₁.append P₂).runToRound ⟨m + (jv + 1), by omega⟩ stmt wit
      = (do
          let p₁ ← (liftM (P₁.runToRound (Fin.last m) stmt wit) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (pSpec₁.Transcript (Fin.last m) × P₁.PrvState (Fin.last m)))
          let ctx₂ ← liftComp (P₁.output p₁.2)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          let p₂ ← liftComp (P₂.runToRound ⟨jv + 1, by omega⟩ ctx₂.1 ctx₂.2)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          pure (trGlue ⟨jv + 1, by omega⟩ p₁.1 p₂.1,
            _root_.cast (PrvState_right P₁ P₂ hjv).symm p₂.2)) := by
  induction jv with
  | zero =>
    have hn : 0 < n := hjv
    show Prover.runToRound (⟨m, by omega⟩ : Fin (m + n)).succ stmt wit (P₁.append P₂) = _
    rw [Prover.runToRound_succ]
    rw [show Prover.runToRound (Fin.castSucc ⟨m, by omega⟩) stmt wit (P₁.append P₂)
      = Prover.runToRound (Fin.castLE (by omega) (Fin.last m)) stmt wit (P₁.append P₂) from rfl]
    rw [append_runToRound_left_of_challenge_free P₁ P₂ hCF₁ stmt wit (Fin.last m)]
    simp only [Prover.processRound]
    erw [bind_map_left]
    congr 1
    funext a
    simp only []
    -- refute the challenge branch at the boundary round
    have hDirApp : (pSpec₁.dir ++ᵛ pSpec₂.dir) (⟨m, by omega⟩ : Fin (m + n))
        = Direction.P_to_V := by
      rw [Fin.vappend_eq_append,
        show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨0, hn⟩ from Fin.ext (by simp),
        Fin.append_right]
      exact hCF₂ _
    split
    · rename_i hDir
      rw [hDirApp] at hDir
      exact absurd hDir (by simp)
    rename_i hDir
    -- G-L3 surgery: the fused boundary handoff, state casts collapsed
    have hbnd : HEq
        ((P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩
          (_root_.cast (PrvState_left P₁ P₂ (Fin.last m)).symm a.2))
        ((do
          let ctx₂ ← P₁.output a.2
          P₂.sendMessage ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ (P₂.input ctx₂)) :
            OracleComp oSpec _) := by
      refine (append_sendMessage_boundary_general P₁ P₂ hn hDir (hCF₂ ⟨0, hn⟩) _).trans ?_
      refine heq_of_eq (congrArg (fun s => ((do
        let ctx₂ ← P₁.output s
        P₂.sendMessage ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ (P₂.input ctx₂)) :
          OracleComp oSpec _)) ?_)
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    have hMsg₀ : pSpec₂.«Type» ⟨0, hn⟩
        = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m ⟨0, hn⟩) :=
      (ProtocolSpec.append_Type_natAdd ⟨0, hn⟩).symm
    have hSt₀ : P₂.PrvState ⟨0 + 1, by omega⟩
        = (P₁.append P₂).PrvState ⟨m + (0 + 1), by omega⟩ :=
      (PrvState_right P₁ P₂ (jv := 0) hn).symm
    have hXeq₀ : (P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩
          (_root_.cast (PrvState_left P₁ P₂ (Fin.last m)).symm a.2)
        = _root_.cast (congrArg (OracleComp oSpec) (congrArg₂ Prod hMsg₀ hSt₀))
            ((do
              let ctx₂ ← P₁.output a.2
              P₂.sendMessage ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ (P₂.input ctx₂)) :
                OracleComp oSpec _) :=
      (cast_eq_iff_heq.mpr hbnd.symm).symm
    erw [hXeq₀]
    erw [liftM_cast_comm (congrArg₂ Prod hMsg₀ hSt₀)]
    erw [cast_bind (congrArg₂ Prod hMsg₀ hSt₀)]
    have hdist : (liftComp ((do
          let ctx₂ ← P₁.output a.2
          P₂.sendMessage ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ (P₂.input ctx₂)) : OracleComp oSpec _)
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        = liftComp (P₁.output a.2) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            >>= fun ctx₂ => liftComp
              (P₂.sendMessage ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ (P₂.input ctx₂))
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :=
      liftComp_bind _ _ _
    refine Eq.trans (congrArg
      (fun (src : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (pSpec₂.Message ⟨⟨0, hn⟩, hCF₂ ⟨0, hn⟩⟩ × P₂.PrvState ⟨0 + 1, by omega⟩)) =>
        src >>= fun a_1 => pure
          (Transcript.concat (_root_.cast (congrArg₂ Prod hMsg₀ hSt₀) a_1).1
            (trLeft (Fin.last m) a.1),
           (_root_.cast (congrArg₂ Prod hMsg₀ hSt₀) a_1).2))
      hdist) ((bind_assoc _ _ _).trans ?_)
    congr 1
    funext c
    rw [show Prover.runToRound (⟨0 + 1, by omega⟩ : Fin (n + 1)) c.1 c.2 P₂
      = Prover.processRound ⟨0, hn⟩ P₂ (Prover.runToRound (Fin.castSucc ⟨0, hn⟩) c.1 c.2 P₂)
      from Prover.runToRound_succ ⟨0, hn⟩ c.1 c.2 P₂]
    rw [show Prover.runToRound (Fin.castSucc ⟨0, hn⟩) c.1 c.2 P₂
      = pure ((default : pSpec₂.Transcript 0), P₂.input (c.1, c.2))
      from Prover.runToRound_zero_of_prover_first c.1 c.2 P₂]
    simp only [Prover.processRound, pure_bind]
    split
    · rename_i hd
      rw [hCF₂ ⟨0, hn⟩] at hd
      exact absurd hd (by simp)
    rename_i hd
    -- Splice 1: distribute liftComp over the (definitionally pure-bind-reduced)
    -- inner block, and collapse the two-hop lift (R6').
    have hInner : liftComp
          ((liftM (P₂.sendMessage ⟨⟨0, hn⟩, hd⟩ (P₂.input (c.1, c.2))) :
              OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) >>= fun r =>
            (pure (Transcript.concat r.1 (default : pSpec₂.Transcript 0), r.2) :
              OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        = liftComp (P₂.sendMessage ⟨⟨0, hn⟩, hd⟩ (P₂.input (c.1, c.2)))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun r =>
            liftComp ((pure (Transcript.concat r.1 (default : pSpec₂.Transcript 0), r.2) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
      refine Eq.trans (liftComp_bind _ _ _) ?_
      exact congrArg (fun z => z >>=
        fun (r : pSpec₂.Message ⟨⟨0, hn⟩, hd⟩ × P₂.PrvState ⟨0 + 1, by omega⟩) =>
        liftComp ((pure (Transcript.concat r.1 (default : pSpec₂.Transcript 0), r.2) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (liftComp_liftM_challenge₂ P₁ P₂ _)
    refine Eq.trans ?_ (congrArg (fun z => z >>= fun p₂ =>
      pure (trGlue (⟨0 + 1, by omega⟩ : Fin (n + 1)) a.1 p₂.1,
        _root_.cast (PrvState_right P₁ P₂ (jv := 0) hn).symm p₂.2)) hInner).symm
    -- Splice 2: reassociate, then pointwise.
    refine Eq.trans ?_ (bind_assoc _ _ _).symm
    congr 1
    funext r
    refine congrArg pure (Prod.ext ?_ ?_)
    · simp only []
      rw [cast_prod_fst hMsg₀ hSt₀]
      exact ((congrArg (fun z => Transcript.concat (m := Fin.natAdd m ⟨0, hn⟩)
        (_root_.cast (ProtocolSpec.append_Type_natAdd ⟨0, hn⟩).symm r.1) z)
        (trGlue_zero a.1 (default : pSpec₂.Transcript 0)).symm).trans
        (trGlue_concat ⟨0, hn⟩ a.1 (default : pSpec₂.Transcript 0) r.1).symm)
    · simp only []
      rw [cast_prod_snd hMsg₀ hSt₀]
  | succ jw ih =>
    have hjw : jw < n := by omega
    show Prover.runToRound (⟨m + (jw + 1), by omega⟩ : Fin (m + n)).succ stmt wit
      (P₁.append P₂) = _
    rw [Prover.runToRound_succ]
    rw [show Prover.runToRound (Fin.castSucc ⟨m + (jw + 1), by omega⟩) stmt wit (P₁.append P₂)
      = Prover.runToRound (⟨m + (jw + 1), by omega⟩ : Fin (m + n + 1)) stmt wit (P₁.append P₂)
      from rfl]
    rw [ih hjw]
    simp only [Prover.processRound]
    refine Eq.trans (bind_assoc _ _ _) ?_
    congr 1
    funext p₁
    refine Eq.trans (bind_assoc _ _ _) ?_
    congr 1
    funext c
    refine Eq.trans (bind_assoc _ _ _) ?_
    -- unfold P₂'s runToRound successor on the RHS (term splice, no matching)
    refine Eq.trans ?_ (congrArg (fun z =>
      liftComp (z : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
            (pSpec₂.Transcript ⟨jw + 1 + 1, by omega⟩ × P₂.PrvState ⟨jw + 1 + 1, by omega⟩))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun p₂ =>
        pure (trGlue (⟨jw + 1 + 1, by omega⟩ : Fin (n + 1)) p₁.1 p₂.1,
          _root_.cast (PrvState_right P₁ P₂ (jv := jw + 1) hjv).symm p₂.2))
      (show Prover.runToRound (⟨jw + 1 + 1, by omega⟩ : Fin (n + 1)) c.1 c.2 P₂
        = Prover.processRound ⟨jw + 1, hjv⟩ P₂
            (Prover.runToRound (Fin.castSucc ⟨jw + 1, hjv⟩) c.1 c.2 P₂)
        from Prover.runToRound_succ ⟨jw + 1, hjv⟩ c.1 c.2 P₂)).symm
    -- distribute the outer liftComp over processRound's bind
    refine Eq.trans ?_ (congrArg (fun z => z >>=
      fun (p₂ : pSpec₂.Transcript ⟨jw + 1 + 1, by omega⟩
          × P₂.PrvState ⟨jw + 1 + 1, by omega⟩) =>
      pure (trGlue (⟨jw + 1 + 1, by omega⟩ : Fin (n + 1)) p₁.1 p₂.1,
        _root_.cast (PrvState_right P₁ P₂ (jv := jw + 1) hjv).symm p₂.2))
      (liftComp_bind _ _ _)).symm
    refine Eq.trans ?_ (bind_assoc _ _ _).symm
    congr 1
    funext p₂
    -- LHS: perRound-append applied to the glued pair; split the boundary match
    simp only [Prover.processRound]
    have hDirApp : (pSpec₁.dir ++ᵛ pSpec₂.dir) (⟨m + (jw + 1), by omega⟩ : Fin (m + n))
        = Direction.P_to_V := by
      have h := dir_right (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (j := jw + 1) hjv
      exact h.trans (hCF₂ _)
    split
    · rename_i hDir
      rw [hDirApp] at hDir
      exact absurd hDir (by simp)
    rename_i hDir
    split
    · rename_i hd
      rw [hCF₂ ⟨jw + 1, hjv⟩] at hd
      exact absurd hd (by simp)
    rename_i hd
    refine Eq.trans (pure_bind _ _) ?_
    simp only []
    -- R7 surgery (mirror of phase-1's field-lemma step)
    have hsend : HEq
        ((P₁.append P₂).sendMessage ⟨⟨m + (jw + 1), by omega⟩, hDir⟩
          (_root_.cast (PrvState_right P₁ P₂ hjw).symm p₂.2))
        (P₂.sendMessage ⟨⟨jw + 1, hjv⟩, hd⟩ p₂.2) := by
      refine (append_sendMessage_right' P₁ P₂ hjv hDir hd _ p₂.2 ?_).trans (HEq.refl _)
      exact cast_heq _ _
    have hMsg' : pSpec₂.«Type» ⟨jw + 1, hjv⟩
        = (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m ⟨jw + 1, hjv⟩) :=
      (ProtocolSpec.append_Type_natAdd ⟨jw + 1, hjv⟩).symm
    have hSt' : P₂.PrvState ⟨jw + 1 + 1, by omega⟩
        = (P₁.append P₂).PrvState ⟨m + (jw + 1 + 1), by omega⟩ :=
      (PrvState_right P₁ P₂ (jv := jw + 1) hjv).symm
    have hXeq : (P₁.append P₂).sendMessage ⟨⟨m + (jw + 1), by omega⟩, hDir⟩
          (_root_.cast (PrvState_right P₁ P₂ hjw).symm p₂.2)
        = _root_.cast (congrArg (OracleComp oSpec) (congrArg₂ Prod hMsg' hSt'))
            (P₂.sendMessage ⟨⟨jw + 1, hjv⟩, hd⟩ p₂.2) :=
      (cast_eq_iff_heq.mpr hsend.symm).symm
    erw [hXeq]
    refine Eq.trans (congrArg (fun z => z >>=
      fun (d : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m ⟨jw + 1, hjv⟩)
          × (P₁.append P₂).PrvState ⟨m + (jw + 1 + 1), by omega⟩) =>
        pure (Transcript.concat d.1 (trGlue (⟨jw + 1, by omega⟩ : Fin (n + 1)) p₁.1 p₂.1),
          d.2))
      (liftM_cast_comm (congrArg₂ Prod hMsg' hSt')
        (P₂.sendMessage ⟨⟨jw + 1, hjv⟩, hd⟩ p₂.2))) ?_
    refine Eq.trans (cast_bind (congrArg₂ Prod hMsg' hSt') _ _) ?_
    -- RHS: distribute + collapse the two-hop
    have hInner : liftComp ((do
          let r ← liftM (P₂.sendMessage ⟨⟨jw + 1, hjv⟩, hd⟩ p₂.2)
          pure (Transcript.concat r.1 p₂.1, r.2)) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        = liftComp (P₂.sendMessage ⟨⟨jw + 1, hjv⟩, hd⟩ p₂.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun r =>
            liftComp ((pure (Transcript.concat r.1 p₂.1, r.2) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
      refine Eq.trans (liftComp_bind _ _ _) ?_
      exact congrArg (fun z => z >>=
        fun (r : pSpec₂.Message ⟨⟨jw + 1, hjv⟩, hd⟩ × P₂.PrvState ⟨jw + 1 + 1, by omega⟩) =>
        liftComp ((pure (Transcript.concat r.1 p₂.1, r.2) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (liftComp_liftM_challenge₂ P₁ P₂ _)
    refine Eq.trans ?_ (congrArg (fun z => z >>=
      fun (p₃ : pSpec₂.Transcript ⟨jw + 1 + 1, by omega⟩
          × P₂.PrvState ⟨jw + 1 + 1, by omega⟩) =>
      pure (trGlue (⟨jw + 1 + 1, by omega⟩ : Fin (n + 1)) p₁.1 p₃.1,
        _root_.cast (PrvState_right P₁ P₂ (jv := jw + 1) hjv).symm p₃.2))
      hInner).symm
    refine Eq.trans ?_ (bind_assoc _ _ _).symm
    congr 1
    funext r
    refine congrArg pure (Prod.ext ?_ ?_)
    · simp only []
      rw [cast_prod_fst hMsg' hSt']
      exact (trGlue_concat ⟨jw + 1, hjv⟩ p₁.1 p₂.1 r.1).symm
    · simp only []
      rw [cast_prod_snd hMsg' hSt']

include P₁ P₂ in
/-- **B4' (B4 with `liftComp`-spelled outer lift)**. -/
theorem liftComp_liftM_challenge₁ {α : Type} (x : OracleComp oSpec α) :
    liftComp (liftM x : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α)
      (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    = liftComp x (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :=
  liftM_liftM_challenge (pSpec₂ := pSpec₂) x

/-- **A0**: `liftComp` distributes over a prover's `run` (which is
definitionally `runToRound (last) >>= output`-packaging). -/
theorem liftComp_prover_run {ιT : Type} {tSpec : OracleSpec ιT}
    {A B C D : Type} {N : ℕ} {ps : ProtocolSpec N}
    [MonadLift (OracleQuery (oSpec + [ps.Challenge]ₒ)) (OracleQuery tSpec)]
    [MonadLift (OracleQuery oSpec) (OracleQuery tSpec)]
    (P : Prover oSpec A B C D ps) (x : A) (y : B) :
    liftComp (P.run x y) tSpec
      = liftComp (P.runToRound (Fin.last N) x y) tSpec >>= fun p =>
          liftComp ((liftM (P.output p.2) : OracleComp (oSpec + [ps.Challenge]ₒ) (C × D))) tSpec
            >>= fun o => pure (p.1, o) := by
  refine Eq.trans (liftComp_bind _ _ _) ?_
  refine bind_congr fun p => ?_
  refine Eq.trans (liftComp_bind _ _ _) ?_
  refine bind_congr fun o => ?_
  exact liftComp_pure _ _

set_option maxHeartbeats 1000000 in
/-- **THE ASSEMBLY (challenge-free `Prover.append_run`)**: for challenge-free
protocols (the commitment-transform class) with a non-empty right protocol,
running the appended prover IS running P₁, then P₂ on its output, with the
transcripts appended — the upstream `Prover.append_run` statement
(Append.lean:360, a library `sorry`), challenge-free instance, with
deterministic (`liftComp`) lift spelling. -/
theorem append_run_of_challenge_free
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V) (hCF₂ : ∀ i, pSpec₂'.dir i = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂').run stmt wit
      = (do
        let r₁ ← liftComp (P₁.run stmt wit)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
        let r₂ ← liftComp (P₂'.run r₁.2.1 r₁.2.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
        pure (r₁.1 ++ₜ r₂.1, r₂.2)) := by
  simp only [Prover.run]
  rw [show Prover.runToRound (Fin.last (m + (n' + 1))) stmt wit (P₁.append P₂')
    = Prover.runToRound (⟨m + (n' + 1), by omega⟩ : Fin (m + (n' + 1) + 1)) stmt wit
        (P₁.append P₂') from rfl]
  rw [append_runToRound_right_of_challenge_free P₁ P₂' hCF₁ hCF₂ stmt wit n' (by omega)]
  -- RHS: distribute the two lifted runs (A0), collapse the two-hop output lifts
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun r₁ =>
    liftComp (P₂'.run r₁.2.1 r₁.2.2) (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
      >>= fun r₂ => pure (r₁.1 ++ₜ r₂.1, r₂.2))
    (liftComp_prover_run P₁ stmt wit)).symm
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  -- descend the shared P₁-run prefix
  refine Eq.trans (bind_assoc _ _ _) ?_
  congr 1
  funext p₁
  refine Eq.trans (bind_assoc _ _ _) ?_
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  -- collapse the two-hop lift of P₁.output on the RHS
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun (o : Stmt₂ × Wit₂) =>
    liftComp (P₂'.run o.1 o.2) (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
      >>= fun r₂ => pure (p₁.1 ++ₜ r₂.1, r₂.2))
    (liftComp_liftM_challenge₁ (pSpec₂ := pSpec₂') P₁ P₂' (P₁.output p₁.2))).symm
  congr 1
  funext c
  -- RHS: pure-bind is definitional; distribute P₂'.run and collapse its output lift
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun r₂ =>
    (pure (p₁.1 ++ₜ r₂.1, r₂.2) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (liftComp_prover_run P₂' c.1 c.2)).symm
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  refine Eq.trans (bind_assoc _ _ _) ?_
  congr 1
  funext p₂
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun (o₂ : Stmt₃ × Wit₃) =>
    (pure (p₁.1 ++ₜ p₂.1, o₂) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (liftComp_liftM_challenge₂ (pSpec₂ := pSpec₂') P₁ P₂' (P₂'.output p₂.2))).symm
  -- LHS: pure-bind is definitional; the composed output IS P₂'s (G-L5)
  refine Eq.trans (pure_bind _ _) ?_
  simp only []
  have hjvN : n' < n' + 1 := Nat.lt_succ_self n'
  have hnz : n' + 1 ≠ 0 := Nat.succ_ne_zero n'
  have houtEq : (P₁.append P₂').output
        (_root_.cast (PrvState_right P₁ P₂' (jv := n') hjvN).symm p₂.2)
      = P₂'.output p₂.2 :=
    append_output_general P₁ P₂' hnz
      (_root_.cast (PrvState_right P₁ P₂' (jv := n') hjvN).symm p₂.2) p₂.2
      (cast_heq (PrvState_right P₁ P₂' (jv := n') hjvN).symm p₂.2)
  refine Eq.trans (congrArg (fun (z : OracleComp oSpec (Stmt₃ × Wit₃)) =>
      liftComp z (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= fun o =>
      pure (trGlue (⟨n' + 1, Nat.lt_succ_self (n' + 1)⟩ : Fin (n' + 1 + 1)) p₁.1 p₂.1, o))
    houtEq) rfl

/-! ## The n = 0 degenerate case (closure phase, 2026-07-12). At arity 0 the
    right protocol is challenge-free VACUOUSLY, everything is left-region, and
    the composed machine is P₁ with a post-composed output transformer. -/

/-- **Z1**: the appended output at `n = 0` is the fused
`P₁.output ∘ P₂.input ∘ P₂.output` handoff, transport-free. -/
theorem append_output_zero {pSpec₂' : ProtocolSpec 0}
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (st : (P₁.append P₂').PrvState (Fin.last (m + 0)))
    (st₁ : P₁.PrvState (Fin.last m)) (hst : HEq st st₁) :
    (P₁.append P₂').output st
      = P₁.output st₁ >>= fun ctx => P₂'.output (P₂'.input ctx) := by
  simp only [Prover.append, eq_mpr_eq_cast, eq_mp_eq_cast]
  rw [dif_pos trivial]
  congr 1
  exact congrArg P₁.output (eq_of_heq ((cast_heq _ _).trans hst))

/-- **Z-ASSEMBLY (challenge-free `append_run`, empty right protocol)**: the
degenerate companion of `append_run_of_challenge_free`, needing only hCF₁
(the right protocol is vacuously message-only over `Fin 0`). -/
theorem append_run_of_challenge_free_zero
    {pSpec₂' : ProtocolSpec 0}
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂').run stmt wit
      = (do
        let r₁ ← liftComp (P₁.run stmt wit)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
        let r₂ ← liftComp (P₂'.run r₁.2.1 r₁.2.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
        pure (r₁.1 ++ₜ r₂.1, r₂.2)) := by
  simp only [Prover.run]
  rw [show Prover.runToRound (Fin.last (m + 0)) stmt wit (P₁.append P₂')
    = Prover.runToRound (Fin.castLE (by omega) (Fin.last m)) stmt wit (P₁.append P₂')
    from rfl]
  rw [append_runToRound_left_of_challenge_free P₁ P₂' hCF₁ stmt wit (Fin.last m)]
  erw [bind_map_left]
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun r₁ =>
    liftComp (P₂'.run r₁.2.1 r₁.2.2) (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
      >>= fun r₂ => pure (r₁.1 ++ₜ r₂.1, r₂.2))
    (liftComp_prover_run P₁ stmt wit)).symm
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  congr 1
  funext p
  simp only []
  have houtEq : (P₁.append P₂').output
        (_root_.cast (PrvState_left P₁ P₂' (Fin.last m)).symm p.2)
      = P₁.output p.2 >>= fun ctx => P₂'.output (P₂'.input ctx) :=
    append_output_zero P₁ P₂' _ p.2 (cast_heq _ _)
  refine Eq.trans (congrArg (fun (z : OracleComp oSpec (Stmt₃ × Wit₃)) =>
      liftComp z (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= fun o =>
      pure (trLeft (Fin.last m) p.1, o)) houtEq) ?_
  refine Eq.trans (congrArg (fun z => z >>= fun (o : Stmt₃ × Wit₃) =>
    (pure (trLeft (Fin.last m) p.1, o) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (liftComp_bind _ (P₁.output p.2) (fun ctx => P₂'.output (P₂'.input ctx)))) ?_
  refine Eq.trans (bind_assoc _ _ _) ?_
  refine Eq.trans ?_ (bind_assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun (o : Stmt₂ × Wit₂) =>
    liftComp (P₂'.run o.1 o.2) (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ)
      >>= fun r₂ => pure (p.1 ++ₜ r₂.1, r₂.2))
    (liftComp_liftM_challenge₁ (pSpec₂ := pSpec₂') P₁ P₂' (P₁.output p.2))).symm
  congr 1
  funext ctx
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun r₂ =>
    (pure (p.1 ++ₜ r₂.1, r₂.2) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (liftComp_prover_run P₂' ctx.1 ctx.2)).symm
  refine Eq.trans ?_ (congrArg (fun (z : OracleComp (oSpec + [pSpec₂'.Challenge]ₒ)
      (pSpec₂'.Transcript (Fin.last 0) × P₂'.PrvState (Fin.last 0))) =>
    (liftComp z (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= fun q =>
      liftComp ((liftM (P₂'.output q.2) :
          OracleComp (oSpec + [pSpec₂'.Challenge]ₒ) (Stmt₃ × Wit₃)))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= fun o =>
      pure (q.1, o)) >>= fun r₂ =>
      (pure (p.1 ++ₜ r₂.1, r₂.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (show Prover.runToRound (Fin.last 0) ctx.1 ctx.2 P₂'
      = pure ((default : pSpec₂'.Transcript 0), P₂'.input (ctx.1, ctx.2))
      from Prover.runToRound_zero_of_prover_first ctx.1 ctx.2 P₂')).symm
  refine Eq.trans ?_ (bind_assoc
    (liftComp ((liftM (P₂'.output (P₂'.input (ctx.1, ctx.2))) :
        OracleComp (oSpec + [pSpec₂'.Challenge]ₒ) (Stmt₃ × Wit₃)))
      (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ))
    (fun o => pure ((default : pSpec₂'.Transcript 0), o))
    (fun r₂ => pure (((p.1 : pSpec₁.FullTranscript) ++ₜ r₂.1 :
        (i : Fin (m + 0)) → (pSpec₁ ++ₚ pSpec₂').«Type» i), r₂.2))).symm
  show liftComp (P₂'.output (P₂'.input ctx))
      (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= (fun o =>
        pure (trLeft (pSpec₂ := pSpec₂') (Fin.last m) p.1, o))
    = liftComp ((liftM (P₂'.output (P₂'.input (ctx.1, ctx.2))) :
        OracleComp (oSpec + [pSpec₂'.Challenge]ₒ) (Stmt₃ × Wit₃)))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) >>= fun o₂ =>
        pure (((p.1 : pSpec₁.FullTranscript) ++ₜ (default : pSpec₂'.FullTranscript) :
          (i : Fin (m + 0)) → (pSpec₁ ++ₚ pSpec₂').«Type» i), o₂)
  refine Eq.trans ?_ (congrArg (fun z => z >>= fun (o₂ : Stmt₃ × Wit₃) =>
    (pure (((p.1 : pSpec₁.FullTranscript) ++ₜ (default : pSpec₂'.FullTranscript) :
        (i : Fin (m + 0)) → (pSpec₁ ++ₚ pSpec₂').«Type» i), o₂) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _))
    (liftComp_liftM_challenge₂ (pSpec₂ := pSpec₂') P₁ P₂'
      (P₂'.output (P₂'.input (ctx.1, ctx.2))))).symm
  congr 1

/-- **UPSTREAM-SPELLED COROLLARY**: `append_run_of_challenge_free` restated
with the exact do-block shape of the library's `Prover.append_run` statement
(Append.lean:360) — destructuring lets and ambient `liftM`. If the ambient
`MonadLiftT` route resolves one-hop this is a definitional restatement;
otherwise the B4/R6 collapses bridge. -/
theorem append_run_of_challenge_free_liftM
    {n' : ℕ} {pSpec₂' : ProtocolSpec (n' + 1)}
    (P₂' : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂')
    (hCF₁ : ∀ i, pSpec₁.dir i = .P_to_V) (hCF₂ : ∀ i, pSpec₂'.dir i = .P_to_V)
    (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂').run stmt wit = (do
      let ⟨transcript₁, stmt₂, wit₂⟩ ← (liftM (P₁.run stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)
      let ⟨transcript₂, stmt₃, wit₃⟩ ← (liftM (P₂'.run stmt₂ wit₂) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂').Challenge]ₒ) _)
      return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :=
  append_run_of_challenge_free P₁ P₂' hCF₁ hCF₂ stmt wit

/- ------------------------------------------------------------------------
   STATUS OF THE FULL `Prover.append_run` (updated 2026-07-12).

   ### THE CHALLENGE-FREE GENERAL ASSEMBLY IS PROVEN. ###

   `append_run_of_challenge_free` (this file, 0 sorries, house footprint
   [propext, Classical.choice, Quot.sound] — verified by #print axioms, and
   NON-VACUITY verified: the statement is NOT closed by rfl):
   for challenge-free (message-only) protocols — the commitment-transform /
   BCS class — at fully general arity m ≥ 0, n = n'+1 ≥ 1, the composed
   prover's run IS: run P₁, hand off through P₁.output ∘ P₂.input, run P₂,
   append the transcripts. This is the upstream `Prover.append_run` sorry
   (Append.lean:360) in its challenge-free instance, with deterministic
   `liftComp` lift spelling.

   Proof chain (all in this file, all house-footprint):
   1. append_runToRound_left_of_challenge_free  — phase 1, left region.
   2. append_runToRound_right_of_challenge_free — boundary handoff (base,
      via G-L3) + right region (step, via R7), Nat-induction with all
      indices pinned at the reducing `jv+1` spelling.
   3. append_run_of_challenge_free — assembly at Fin.last, via A0
      (liftComp-of-run distribution), G-L5, and trGlue_full (≡ rfl by
      proof irrelevance).
   Supporting brick layers: B0–B7 (left) and R-V/R0–R7 + B4'/R6' (right:
   vappend_take, take_append_add, trGlue + concat/zero/full laws,
   PrvState_right décalage, lift-route coherence at both challenge sums).

   HONEST FENCES:
   (a) n = 0 (empty right protocol): different code path in Prover.append
       (output composes P₁.output∘P₂.input∘P₂.output); small separate
       theorem, NOT covered here.
   (b) The upstream statement spells its lifts with ambient liftM; ours pins
       liftComp. Bridging is defeq at the one-hop route (liftComp_eq_liftM
       is rfl); an upstream PR should state whichever the maintainers want.
   (c) General (non-challenge-free) case: still gated on the challenge-lift
       alignment sub-development (research-grade), unchanged.

   TOOLING LESSON (cost: one false "proven" claim mid-session, caught and
   remediated before landing): Lean 4.30 emits BOTH `error:` and
   `error(lean.kind):` diagnostics; grep for `error:` silently passes the
   latter, and elaboration-recovery can inject sorryAx WITHOUT a
   "declaration uses sorry" warning. The ONLY trustworthy completion checks
   are `grep -cE "error"` = 0 AND `#print axioms` showing the expected
   footprint. Both are now part of this file's verification ritual.
   ------------------------------------------------------------------------ -/

end AppendGeneral
