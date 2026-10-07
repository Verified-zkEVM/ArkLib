/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Worst-case round-by-round knowledge soundness of a guarded sequential composition

If the first verifier is **guarded** (`Verifier.GuardedForm`: it returns a deterministic verdict
when its check passes and aborts otherwise) and both components are worst-case round-by-round
knowledge sound, then so is their sequential composition, with each challenge's error inherited
from its component. The components share only the intermediate relation.

The composed extractor is `Extractor.RoundByRound.append` at the guarded verdict map. The composed
knowledge state function `Verifier.KnowledgeStateFunction.appendGuarded` is the first one up to
and including the seam; after the seam it is the first guard on the first protocol's transcript
together with the second knowledge state function, started from the first verdict. The guard
conjunct is necessary: without it a rejected first transcript could satisfy the second knowledge
state at a fallback verdict while the first knowledge state fails.

The seam step (`KnowledgeStateFunction.appendGuarded_seam`) chains the second knowledge state
function's round-`0` value into the intermediate relation (`toFun_empty`). A passing guard makes the
first verifier output that statement with positive probability. The first knowledge state
function's `toFun_full` then applies.

## Main results

* `Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`: the composition theorem
  with the extractor and knowledge state function named, so that it iterates.
* `Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first` and
  `Verifier.append_rbrKnowledgeSoundness_of_worst_case_of_guarded_first`: the existential and
  averaged corollaries, with `OracleVerifier` wrappers.

## Supporting API

* `ProtocolSpec.Transcript.fstUpTo` / `sndUpTo`: the two protocols' parts of a partial transcript
  of an appended protocol, at an explicit round, with their `concat` laws; `fst_eq_fstUpTo` and
  `snd_eq_sndUpTo` relate them to `Transcript.fst` / `snd`.
* `Extractor.RoundByRound.append_extractMid_castAdd`, `append_extractMid_seam`,
  `append_extractMid_natAdd`, `append_extractOut_of_pos`, `append_extractOut_of_eq_zero`: the
  composed extractor, region by region.
* `Verifier.GuardedForm.append_prEvent_pos`: a positive-probability output of an append with a
  guarded first factor passes the first guard. It is used with
  `Verifier.GuardedForm.prEvent_pos_of_check` (`Security/Guarded.lean`) and
  `Verifier.KnowledgeStateFunction.toFun_congr` (`Security/RoundByRound.lean`).

The `n`-ary form is `Verifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded` in
`Composition/Sequential/GuardedRoundByRound.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace ProtocolSpec.Transcript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {k : Fin (m + n + 1)}

/-- The first `j` rounds of a partial transcript of an appended protocol, as a partial transcript
of the first protocol, for any `j` not exceeding the rounds already played. Unlike
`Transcript.fst`, which stops at the round `min k m` fixed by `k`, the target round is explicit, so
statements can name it directly (`fst_eq_fstUpTo`). -/
def fstUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (m + 1)) (hj : j.val ≤ k.val) :
    pSpec₁.Transcript j :=
  fun i => _root_.cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; omega⟩) (T ⟨i.val, by have := i.isLt; omega⟩)

/-- The first `j` rounds of the second protocol's part of a partial transcript of an appended
protocol, for any `j` such that those rounds have already been played. Unlike `Transcript.snd`,
which stops at the round `k - m`, the target round is explicit (`snd_eq_sndUpTo`). -/
def sndUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (j : Fin (n + 1)) (hj : m + j.val ≤ k.val) :
    pSpec₂.Transcript j :=
  fun i => _root_.cast (append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    ⟨i.val, by have := i.isLt; omega⟩) (T ⟨m + i.val, by have := i.isLt; omega⟩)

/-- `Transcript.fst`, which stops at round `min k m`, is `fstUpTo` at that round. -/
theorem fst_eq_fstUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) :
    T.fst = T.fstUpTo ⟨min k.val m, by omega⟩ (min_le_left _ _) := rfl

/-- At or after the seam, `Transcript.snd`, which stops at round `k - m`, is `sndUpTo` at that
round. (Before the seam `snd` is empty, `Transcript.snd_of_le`, while `sndUpTo` is not defined.) -/
theorem snd_eq_sndUpTo (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (hk : m ≤ k.val) :
    T.snd = T.sndUpTo ⟨k.val - m, by omega⟩ (by simp; omega) := rfl

/-- Appending a message does not change rounds that were already played. -/
theorem fstUpTo_concat_of_le {j : Fin (m + n)} (T : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (J : Fin (m + 1)) (hJ : J.val ≤ j.val) :
    (T.concat msg).fstUpTo J (by simp; omega) = T.fstUpTo J hJ := by
  funext i
  have := i.isLt
  exact eq_of_heq ((cast_heq _ _).trans ((Transcript.concat_apply_lt T msg i.val
    (by omega) _).trans (cast_heq _ _).symm))

/-- Appending a message in the first protocol extends the first protocol's transcript by it. -/
theorem fstUpTo_concat_castAdd (j : Fin m)
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castAdd n j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n j)) :
    (T.concat msg).fstUpTo j.succ (by simp) =
      (T.fstUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_castAdd j) msg) := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  rcases Nat.lt_or_ge i.val j.val with hij | hij
  · exact (Transcript.concat_apply_lt T msg i.val (by simpa using hij) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_lt (T.fstUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_castAdd j) msg) i.val hij i.isLt).symm)
  · exact (Transcript.concat_apply_last T msg i.val (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_last (T.fstUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_castAdd j) msg) i.val (by omega) i.isLt).symm)

/-- Appending a message does not change the second protocol's rounds that were already played. -/
theorem sndUpTo_concat_of_le {j : Fin (m + n)} (T : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (J : Fin (n + 1)) (hJ : m + J.val ≤ j.val) :
    (T.concat msg).sndUpTo J (by simp; omega) = T.sndUpTo J hJ := by
  funext i
  have := i.isLt
  exact eq_of_heq ((cast_heq _ _).trans ((Transcript.concat_apply_lt T msg (m + i.val)
    (by omega) _).trans (cast_heq _ _).symm))

/-- Appending a message in the second protocol extends the second protocol's transcript by it. -/
theorem sndUpTo_concat_natAdd (j : Fin n)
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m j)) :
    (T.concat msg).sndUpTo j.succ (by simp; omega) =
      (T.sndUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_natAdd j) msg) := by
  funext i
  have hi : i.val < j.val + 1 := i.isLt
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  rcases Nat.lt_or_ge i.val j.val with hij | hij
  · exact (Transcript.concat_apply_lt T msg (m + i.val) (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_lt (T.sndUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_natAdd j) msg) i.val hij i.isLt).symm)
  · exact (Transcript.concat_apply_last T msg (m + i.val) (by simp; omega) _).trans
      ((cast_heq _ _).symm.trans (Transcript.concat_apply_last (T.sndUpTo j.castSucc (by simp))
        (_root_.cast (append_Type_natAdd j) msg) i.val (by omega) i.isLt).symm)

/-- On a full transcript, the whole first-protocol part is `FullTranscript.fst`. -/
theorem fstUpTo_last (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    Transcript.fstUpTo (k := Fin.last (m + n)) T (Fin.last m) (by simp) = T.fst := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  unfold FullTranscript.fst
  exact (cast_heq _ _).symm

/-- On a full transcript, the whole second-protocol part is `FullTranscript.snd`. -/
theorem sndUpTo_last (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    Transcript.sndUpTo (k := Fin.last (m + n)) T (Fin.last n) (by simp) = T.snd := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  unfold FullTranscript.snd
  exact (cast_heq _ _).symm

end ProtocolSpec.Transcript

namespace Extractor.RoundByRound

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
  (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
  (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
  (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)

/-- Before the seam, the composed extractor is the first extractor. -/
theorem append_extractMid_castAdd (j : Fin m) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castAdd n j).succ) (w) :
    HEq ((E₁.append E₂ verify).extractMid (Fin.castAdd n j) stmt tr w)
      (E₁.extractMid j stmt (tr.fstUpTo j.succ (by simp))
        (_root_.cast (wit_mid_append_left (WitMid₂ := WitMid₂) _ j.succ rfl) w)) := by
  simp only [Extractor.RoundByRound.append]
  rw [dite_eq_left (show (Fin.castAdd n j).val < m from j.isLt)]
  exact cast_heq _ _

/-- At the seam, the composed extractor runs the second extractor's first step from the
intermediate statement `verify` assigns to the first protocol's transcript, and then the first
extractor's output step. -/
theorem append_extractMid_seam (hn : 0 < n) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m (⟨0, hn⟩ : Fin n)).succ) (w) :
    HEq ((E₁.append E₂ verify).extractMid (Fin.natAdd m ⟨0, hn⟩) stmt tr w)
      (E₁.extractOut stmt (tr.fstUpTo (Fin.last m) (by simp))
        (_root_.cast ((congrArg WitMid₂ (Fin.ext (by simp))).trans E₂.eqIn)
          (E₂.extractMid ⟨0, hn⟩ (verify stmt (tr.fstUpTo (Fin.last m) (by simp)))
            (tr.sndUpTo (⟨0, hn⟩ : Fin n).succ (by simp))
            (_root_.cast (wit_mid_append_right (WitMid₁ := WitMid₁) _ (⟨0, hn⟩ : Fin n).succ
              (by simp) (by simp)) w)))) := by
  simp only [Extractor.RoundByRound.append]
  rw [dite_eq_right (show ¬ (Fin.natAdd m (⟨0, hn⟩ : Fin n)).val < m by simp),
    dite_eq_left (show (Fin.natAdd m (⟨0, hn⟩ : Fin n)).val = m by simp)]
  exact cast_heq _ _

/-- After the seam, the composed extractor is the second extractor, run from the intermediate
statement `verify` assigns to the first protocol's transcript. -/
theorem append_extractMid_natAdd (j : Fin n) (hj : 0 < j.val) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m j).succ) (w) :
    HEq ((E₁.append E₂ verify).extractMid (Fin.natAdd m j) stmt tr w)
      (E₂.extractMid j (verify stmt (tr.fstUpTo (Fin.last m) (by simp; omega)))
        (tr.sndUpTo j.succ (by simp; omega))
        (_root_.cast (wit_mid_append_right (WitMid₁ := WitMid₁) _ j.succ (by simp; omega)
          (by simp)) w)) := by
  simp only [Extractor.RoundByRound.append]
  rw [dite_eq_right (show ¬ (Fin.natAdd m j).val < m by simp),
    dite_eq_right (show ¬ (Fin.natAdd m j).val = m by simp; omega)]
  refine (cast_heq _ _).trans ?_
  have hj' : (⟨(Fin.natAdd m j).val - m, by simp⟩ : Fin n) = j := Fin.ext (by simp)
  congr 1
  · refine Transcript.heq_ext
      (k := (⟨(Fin.natAdd m j).val - m, by simp⟩ : Fin n).succ) (by simp)
      fun i _ _ => ?_
    exact (cast_heq _ _).trans (cast_heq _ _).symm
  · exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- When the second protocol has rounds, the composed extractor's output step is the second
extractor's. -/
theorem append_extractOut_of_pos (hn : 0 < n) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (w : Wit₃) :
    HEq ((E₁.append E₂ verify).extractOut stmt tr w)
      (E₂.extractOut (verify stmt tr.fst) tr.snd w) := by
  simp only [Extractor.RoundByRound.append]
  rw [dite_eq_left hn]
  exact cast_heq _ _

/-- When the second protocol has no rounds, the composed extractor's output step passes the second
extractor's output to the first extractor's. -/
theorem append_extractOut_of_eq_zero (hn : n = 0) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (w : Wit₃) :
    HEq ((E₁.append E₂ verify).extractOut stmt tr w)
      (E₁.extractOut stmt tr.fst (_root_.cast
        ((congrArg WitMid₂ (Fin.ext (by simp [hn]))).trans E₂.eqIn)
        (E₂.extractOut (verify stmt tr.fst) tr.snd w))) := by
  simp only [Extractor.RoundByRound.append]
  rw [dite_eq_right (show ¬ 0 < n by omega)]
  exact cast_heq _ _

end Extractor.RoundByRound

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

section GuardedRun

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}

/-- A positive-probability output event of an appended verifier whose first factor is guarded
forces the first guard to pass, and the event then has positive probability for the second
verifier started from the first verdict. -/
theorem GuardedForm.append_prEvent_pos (G₁ : V₁.GuardedForm) {stmt : Stmt₁}
    {tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript} {p : Stmt₃ → Prop}
    (h : Pr{let s ← OptionT.mk do
      (simulateQ impl ((V₁.append V₂).run stmt tr)).run' (← init)}[p s] > 0) :
    G₁.check stmt tr.fst = true ∧
      Pr{let s ← OptionT.mk do
        (simulateQ impl (V₂.run (G₁.out stmt tr.fst) tr.snd)).run' (← init)}[p s] > 0 := by
  have hrun := append_run_guardedLeft V₁ V₂ G₁.check G₁.out G₁.verify_eq stmt tr.fst tr.snd
  rw [FullTranscript.append_fst_snd] at hrun
  rw [hrun] at h
  by_cases hc : G₁.check stmt tr.fst = true
  · simp only [hc, ite_true] at h
    exact ⟨hc, h⟩
  · exfalso
    simp only [hc, Bool.false_eq_true, ite_false] at h
    rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, -⟩ := h
    have hfail : ((failure : OptionT (OracleComp oSpec) Stmt₃) : OracleComp oSpec (Option Stmt₃))
        = pure none := rfl
    rw [hfail] at hx
    simp only [simulateQ_pure, support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨s, -, hs⟩ := hx
    simp [StateT.run'_eq] at hs

end GuardedRun

section AppendGuarded

variable {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
  (G₁ : V₁.GuardedForm)
  (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
  (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)

/-- The predicate underlying `KnowledgeStateFunction.appendGuarded`. Up to the seam it is the first
knowledge state function. After the seam it requires the first verifier's guard to pass on the first
protocol's transcript, and the second knowledge state function from the first verifier's verdict. -/
def KnowledgeStateFunction.appendGuardedToFun (k : Fin (m + n + 1)) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (w : (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) k) : Prop :=
  if h : k.val ≤ m then
    K₁.toFun ⟨k.val, by omega⟩ stmt (tr.fstUpTo ⟨k.val, by omega⟩ le_rfl)
      (_root_.cast (Extractor.wit_mid_append_left k ⟨k.val, by omega⟩ rfl) w)
  else
    G₁.check stmt (tr.fstUpTo (Fin.last m) (by simp; omega)) = true ∧
      K₂.toFun ⟨k.val - m, by omega⟩ (G₁.out stmt (tr.fstUpTo (Fin.last m) (by simp; omega)))
        (tr.sndUpTo ⟨k.val - m, by omega⟩ (by simp; omega))
        (_root_.cast (Extractor.wit_mid_append_right k ⟨k.val - m, by omega⟩ (by simp; omega)
          (by simp; omega)) w)

/-- Up to and including the seam, `appendGuardedToFun` is the first knowledge state function on
the first protocol's transcript. -/
theorem KnowledgeStateFunction.appendGuardedToFun_of_le (k : Fin (m + n + 1)) (k₁ : Fin (m + 1))
    (hk : k.val = k₁.val) (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (w) :
    appendGuardedToFun G₁ K₁ K₂ k stmt tr w ↔
      K₁.toFun k₁ stmt (tr.fstUpTo k₁ hk.ge)
        (_root_.cast (Extractor.wit_mid_append_left k k₁ hk) w) := by
  unfold appendGuardedToFun
  rw [dite_eq_left (show k.val ≤ m by omega)]
  exact K₁.toFun_congr (Fin.ext hk) stmt
    (Transcript.heq_ext hk fun _ _ _ => (cast_heq _ _).trans (cast_heq _ _).symm)
    ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- After the seam, `appendGuardedToFun` is the first guard together with the second knowledge state
function from the first verdict, on the second protocol's transcript. -/
theorem KnowledgeStateFunction.appendGuardedToFun_of_gt (k : Fin (m + n + 1)) (k₂ : Fin (n + 1))
    (hk : k.val = m + k₂.val) (h0 : 0 < k₂.val) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k) (w) :
    appendGuardedToFun G₁ K₁ K₂ k stmt tr w ↔
      G₁.check stmt (tr.fstUpTo (Fin.last m) (by simp; omega)) = true ∧
        K₂.toFun k₂ (G₁.out stmt (tr.fstUpTo (Fin.last m) (by simp; omega)))
          (tr.sndUpTo k₂ hk.ge)
          (_root_.cast (Extractor.wit_mid_append_right k k₂ hk h0) w) := by
  unfold appendGuardedToFun
  rw [dite_eq_right (show ¬ k.val ≤ m by omega)]
  refine and_congr Iff.rfl (K₂.toFun_congr (Fin.ext (by simp; omega)) _
    (Transcript.heq_ext (by simp; omega) fun _ _ _ =>
      (cast_heq _ _).trans (cast_heq _ _).symm)
    ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- **The seam step.** At the second protocol's first round, a passing first guard and a true
second knowledge state give the first knowledge state at the end of the first protocol, for the
witness the composed extractor hands back. Chain: the second state function's round-`0` value puts
the intermediate statement in `rel₂`, and the passing guard makes that statement a
positive-probability verdict of the first verifier, so the first state function's `toFun_full`
applies. -/
theorem KnowledgeStateFunction.appendGuarded_seam (hn : 0 < n) (stmt : Stmt₁)
    (tr₁ : pSpec₁.FullTranscript) (hc : G₁.check stmt tr₁ = true)
    (T₂ : pSpec₂.Transcript (⟨0, hn⟩ : Fin n).castSucc) (w₂ : WitMid₂ (⟨0, hn⟩ : Fin n).castSucc)
    (h : K₂.toFun (⟨0, hn⟩ : Fin n).castSucc (G₁.out stmt tr₁) T₂ w₂) :
    K₁.toFun (Fin.last m) stmt tr₁ (E₁.extractOut stmt tr₁
      (_root_.cast ((congrArg WitMid₂ (Fin.ext (by simp))).trans E₂.eqIn) w₂)) := by
  have h0 : (⟨0, hn⟩ : Fin n).castSucc = 0 := Fin.ext (by simp)
  have hmem := (K₂.toFun_empty (G₁.out stmt tr₁) (_root_.cast (congrArg WitMid₂ h0) w₂)).mpr
    ((K₂.toFun_congr h0 _ (Transcript.heq_ext (congrArg Fin.val h0) fun i hi _ => by simp at hi)
      (cast_heq _ _).symm).mp h)
  rw [cast_cast] at hmem
  exact K₁.toFun_full stmt tr₁ _ (G₁.prEvent_pos_of_check hc hmem)

/-- After a first-protocol move, the composed knowledge state is the first one on the extended
first-protocol transcript. -/
theorem KnowledgeStateFunction.appendGuardedToFun_succ_castAdd (j : Fin m) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castAdd n j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n j)) (w) :
    appendGuardedToFun G₁ K₁ K₂ (Fin.castAdd n j).succ stmt (tr.concat msg) w ↔
      K₁.toFun j.succ stmt ((tr.fstUpTo j.castSucc (by simp)).concat
        (_root_.cast (append_Type_castAdd j) msg))
        (_root_.cast (Extractor.wit_mid_append_left _ j.succ rfl) w) := by
  rw [appendGuardedToFun_of_le G₁ K₁ K₂ _ j.succ rfl, Transcript.fstUpTo_concat_castAdd]

/-- Before a first-protocol move, the first knowledge state at the witness extracted by the first
extractor gives the composed knowledge state at the witness extracted by the composed one. -/
theorem KnowledgeStateFunction.appendGuardedToFun_castSucc_castAdd (j : Fin m) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.castAdd n j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.castAdd n j)) (w)
    (h : K₁.toFun j.castSucc stmt (tr.fstUpTo j.castSucc (by simp))
      (E₁.extractMid j stmt ((tr.fstUpTo j.castSucc (by simp)).concat
        (_root_.cast (append_Type_castAdd j) msg))
        (_root_.cast (Extractor.wit_mid_append_left _ j.succ rfl) w))) :
    appendGuardedToFun G₁ K₁ K₂ (Fin.castAdd n j).castSucc stmt tr
      ((E₁.append E₂ G₁.out).extractMid (Fin.castAdd n j) stmt (tr.concat msg) w) := by
  have hx := Extractor.RoundByRound.append_extractMid_castAdd E₁ E₂ G₁.out j stmt
    (tr.concat msg) w
  rw [Transcript.fstUpTo_concat_castAdd] at hx
  rw [appendGuardedToFun_of_le G₁ K₁ K₂ _ j.castSucc rfl]
  exact (K₁.toFun_congr rfl stmt HEq.rfl ((cast_heq _ _).trans hx).symm).mp h

/-- After a second-protocol move, the composed knowledge state is the first guard together with
the second knowledge state on the extended second-protocol transcript. -/
theorem KnowledgeStateFunction.appendGuardedToFun_succ_natAdd (j : Fin n) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m j)) (w) :
    appendGuardedToFun G₁ K₁ K₂ (Fin.natAdd m j).succ stmt (tr.concat msg) w ↔
      G₁.check stmt (tr.fstUpTo (Fin.last m) (by simp)) = true ∧
        K₂.toFun j.succ (G₁.out stmt (tr.fstUpTo (Fin.last m) (by simp)))
          ((tr.sndUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_natAdd j) msg))
          (_root_.cast (Extractor.wit_mid_append_right _ j.succ (by simp; omega) (by simp))
            w) := by
  rw [appendGuardedToFun_of_gt G₁ K₁ K₂ _ j.succ (by simp; omega) (by simp),
    Transcript.fstUpTo_concat_of_le tr msg (Fin.last m) (by simp),
    Transcript.sndUpTo_concat_natAdd]

/-- Before a second-protocol move, a passing first guard and the second knowledge state at the
witness extracted by the second extractor give the composed knowledge state at the witness
extracted by the composed one. At the seam this is `appendGuarded_seam`. -/
theorem KnowledgeStateFunction.appendGuardedToFun_castSucc_natAdd (j : Fin n) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m j).castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» (Fin.natAdd m j)) (w)
    (hc : G₁.check stmt (tr.fstUpTo (Fin.last m) (by simp)) = true)
    (h : K₂.toFun j.castSucc (G₁.out stmt (tr.fstUpTo (Fin.last m) (by simp)))
      (tr.sndUpTo j.castSucc (by simp))
      (E₂.extractMid j (G₁.out stmt (tr.fstUpTo (Fin.last m) (by simp)))
        ((tr.sndUpTo j.castSucc (by simp)).concat (_root_.cast (append_Type_natAdd j) msg))
        (_root_.cast (Extractor.wit_mid_append_right _ j.succ (by simp; omega) (by simp))
          w))) :
    appendGuardedToFun G₁ K₁ K₂ (Fin.natAdd m j).castSucc stmt tr
      ((E₁.append E₂ G₁.out).extractMid (Fin.natAdd m j) stmt (tr.concat msg) w) := by
  rcases Nat.eq_zero_or_pos j.val with h0 | h0
  · have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    obtain rfl : j = ⟨0, hn⟩ := Fin.ext h0
    have hx := Extractor.RoundByRound.append_extractMid_seam E₁ E₂ G₁.out hn stmt
      (tr.concat msg) w
    rw [Transcript.fstUpTo_concat_of_le tr msg (Fin.last m) (by simp),
      Transcript.sndUpTo_concat_natAdd] at hx
    rw [appendGuardedToFun_of_le G₁ K₁ K₂ _ (Fin.last m) (by simp)]
    exact (K₁.toFun_congr rfl stmt HEq.rfl ((cast_heq _ _).trans hx).symm).mp
      (appendGuarded_seam G₁ K₁ K₂ _ stmt _ hc _ _ h)
  · have hx := Extractor.RoundByRound.append_extractMid_natAdd E₁ E₂ G₁.out j h0 stmt
      (tr.concat msg) w
    rw [Transcript.fstUpTo_concat_of_le tr msg (Fin.last m) (by simp),
      Transcript.sndUpTo_concat_natAdd] at hx
    rw [appendGuardedToFun_of_gt G₁ K₁ K₂ _ j.castSucc (by simp) h0]
    exact ⟨hc, (K₂.toFun_congr rfl _ HEq.rfl ((cast_heq _ _).trans hx).symm).mp h⟩

/-- The prover-move obligation of `KnowledgeStateFunction.appendGuarded`: inside each protocol it is
that protocol's own obligation, and at the seam it is `appendGuarded_seam`. -/
theorem KnowledgeStateFunction.appendGuardedToFun_next (j : Fin (m + n))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir j = .P_to_V) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript j.castSucc) (msg : (pSpec₁ ++ₚ pSpec₂).«Type» j) (w)
    (h : appendGuardedToFun G₁ K₁ K₂ j.succ stmt (tr.concat msg) w) :
    appendGuardedToFun G₁ K₁ K₂ j.castSucc stmt tr
      ((E₁.append E₂ G₁.out).extractMid j stmt (tr.concat msg) w) := by
  rcases lt_or_ge j.val m with hlt | hge
  · obtain ⟨j₁, rfl⟩ : ∃ j₁ : Fin m, j = Fin.castAdd n j₁ := ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    have hDir₁ : pSpec₁.dir j₁ = .P_to_V :=
      (Fin.vappend_left pSpec₁.dir pSpec₂.dir j₁).symm.trans hDir
    exact appendGuardedToFun_castSucc_castAdd G₁ K₁ K₂ j₁ stmt tr msg w
      (K₁.toFun_next j₁ hDir₁ stmt _ _ _
        ((appendGuardedToFun_succ_castAdd G₁ K₁ K₂ j₁ stmt tr msg w).mp h))
  · obtain ⟨j₂, rfl⟩ : ∃ j₂ : Fin n, j = Fin.natAdd m j₂ :=
      ⟨⟨j.val - m, by omega⟩, Fin.ext (by simp; omega)⟩
    have hDir₂ : pSpec₂.dir j₂ = .P_to_V :=
      (Fin.vappend_right pSpec₁.dir pSpec₂.dir j₂).symm.trans hDir
    obtain ⟨hc, h⟩ := (appendGuardedToFun_succ_natAdd G₁ K₁ K₂ j₂ stmt tr msg w).mp h
    exact appendGuardedToFun_castSucc_natAdd G₁ K₁ K₂ j₂ stmt tr msg w hc
      (K₂.toFun_next j₂ hDir₂ _ _ _ _ h)

/-- The terminal obligation of `KnowledgeStateFunction.appendGuarded`. A related output of the
composed verifier with positive probability forces the first guard to pass, and the second
knowledge state function's `toFun_full` applies; with no second rounds, the seam step finishes. -/
theorem KnowledgeStateFunction.appendGuardedToFun_full (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (witOut : Wit₃)
    (h : Pr{let stmtOut ← OptionT.mk do
      (simulateQ impl ((V₁.append V₂).run stmt tr)).run' (← init)}[(stmtOut, witOut) ∈ rel₃]
        > 0) :
    appendGuardedToFun G₁ K₁ K₂ (Fin.last (m + n)) stmt tr
      ((E₁.append E₂ G₁.out).extractOut stmt tr witOut) := by
  obtain ⟨hc, hpos⟩ := G₁.append_prEvent_pos h
  have h₂ := K₂.toFun_full _ _ _ hpos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hl : Fin.last n = 0 := Fin.ext (by simp [hn])
    have hmem := (K₂.toFun_empty _ (_root_.cast (congrArg WitMid₂ hl)
      (E₂.extractOut (G₁.out stmt tr.fst) tr.snd witOut))).mpr ((K₂.toFun_congr hl _
        (Transcript.heq_ext (congrArg Fin.val hl) fun i hi _ => by simp [hn] at hi)
        (cast_heq _ _).symm).mp h₂)
    rw [cast_cast] at hmem
    have h₁ := K₁.toFun_full stmt tr.fst _ (G₁.prEvent_pos_of_check hc hmem)
    refine (appendGuardedToFun_of_le G₁ K₁ K₂ (Fin.last (m + n)) (Fin.last m) (by simp [hn])
      stmt tr _).mpr ?_
    rw [Transcript.fstUpTo_last]
    exact (K₁.toFun_congr rfl stmt HEq.rfl ((cast_heq _ _).trans
      (Extractor.RoundByRound.append_extractOut_of_eq_zero E₁ E₂ G₁.out hn stmt tr
        witOut)).symm).mp h₁
  · refine (appendGuardedToFun_of_gt G₁ K₁ K₂ (Fin.last (m + n)) (Fin.last n) (by simp)
      (by simpa) stmt tr _).mpr ?_
    rw [Transcript.fstUpTo_last, Transcript.sndUpTo_last]
    exact ⟨hc, (K₂.toFun_congr rfl _ HEq.rfl ((cast_heq _ _).trans
      (Extractor.RoundByRound.append_extractOut_of_pos E₁ E₂ G₁.out hn stmt tr
        witOut)).symm).mp h₂⟩

/-- **The composed knowledge state function of a guarded sequential composition.** Up to and
including the seam it is the first knowledge state function `K₁`. After the seam it is the
conjunction of the first verifier's guard on the first protocol's transcript with the second
knowledge state function `K₂`, started from the first verifier's verdict. It is a knowledge state
function for the composed extractor `Extractor.RoundByRound.append E₁ E₂ G₁.out`. The only
compatibility it needs between the two components is the shared intermediate relation. -/
def KnowledgeStateFunction.appendGuarded :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃ (E₁.append E₂ G₁.out) where
  toFun := appendGuardedToFun G₁ K₁ K₂
  toFun_empty stmt w := by
    rw [appendGuardedToFun_of_le G₁ K₁ K₂ 0 0 (by simp),
      show Transcript.fstUpTo (default : (pSpec₁ ++ₚ pSpec₂).Transcript 0) 0 (by simp) = default
        from Subsingleton.elim _ _, ← K₁.toFun_empty, cast_cast]
  toFun_next j hDir stmt tr msg w h := appendGuardedToFun_next G₁ K₁ K₂ j hDir stmt tr msg w h
  toFun_full stmt tr witOut h := appendGuardedToFun_full G₁ K₁ K₂ stmt tr witOut h

variable [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- A first-protocol challenge of the composition: the composed extraction-failure event projects
to the first component's, so its probability is bounded by the first component's error. -/
theorem KnowledgeStateFunction.appendGuarded_extractionFailure_inl {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCaseWith init impl rel₁ rel₂ WitMid₁ E₁ K₁ ε₁)
    (i : pSpec₁.ChallengeIdx) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl i).1.castSucc) :
    Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))}[
      rbrExtractionFailureEvent (K₁.appendGuarded G₁ K₂).toFun (E₁.append E₂ G₁.out)
        (ChallengeIdx.inl i) stmt tr c] ≤ ε₁ i := by
  calc
    _ ≤ Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))}[
          rbrExtractionFailureEvent K₁.toFun E₁ i stmt (tr.fstUpTo i.1.castSucc le_rfl)
            (_root_.cast (challenge_append_inl i) c)] := by
      refine prEvent_mono _ _ _ fun c ⟨w, hnot, hsucc⟩ => ⟨_, fun h => hnot ?_,
        (appendGuardedToFun_succ_castAdd G₁ K₁ K₂ i.1 stmt tr c w).mp hsucc⟩
      exact appendGuardedToFun_castSucc_castAdd G₁ K₁ K₂ i.1 stmt tr c w h
    _ = Pr{let c ← $ᵗ (pSpec₁.Challenge i)}[
          rbrExtractionFailureEvent K₁.toFun E₁ i stmt (tr.fstUpTo i.1.castSucc le_rfl) c] := by
      rw [← uniformSample_challenge_append_inl (pSpec₂ := pSpec₂) i, prEvent_map]
    _ ≤ ε₁ i := h₁ stmt i _

/-- A second-protocol challenge of the composition: the composed extraction-failure event is
empty when the first guard fails, and otherwise implies the second component's event from the
first verifier's verdict, so its probability is bounded by the second component's error. At the
seam challenge the implication goes through `appendGuarded_seam`. -/
theorem KnowledgeStateFunction.appendGuarded_extractionFailure_inr {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCaseWith init impl rel₂ rel₃ WitMid₂ E₂ K₂ ε₂)
    (i : pSpec₂.ChallengeIdx) (stmt : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr i).1.castSucc) :
    Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
      rbrExtractionFailureEvent (K₁.appendGuarded G₁ K₂).toFun (E₁.append E₂ G₁.out)
        (ChallengeIdx.inr i) stmt tr c] ≤ ε₂ i := by
  calc
    _ ≤ Pr{let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
          rbrExtractionFailureEvent K₂.toFun E₂ i
            (G₁.out stmt (tr.fstUpTo (Fin.last m) (Nat.le_add_right _ _)))
            (tr.sndUpTo i.1.castSucc le_rfl) (_root_.cast (challenge_append_inr i) c)] := by
      refine prEvent_mono _ _ _ fun c ⟨w, hnot, hsucc⟩ => ?_
      obtain ⟨hc, hsucc⟩ := (appendGuardedToFun_succ_natAdd G₁ K₁ K₂ i.1 stmt tr c w).mp hsucc
      exact ⟨_, fun h => hnot (appendGuardedToFun_castSucc_natAdd G₁ K₁ K₂ i.1 stmt tr c w hc h),
        hsucc⟩
    _ = Pr{let c ← $ᵗ (pSpec₂.Challenge i)}[
          rbrExtractionFailureEvent K₂.toFun E₂ i
            (G₁.out stmt (tr.fstUpTo (Fin.last m) (Nat.le_add_right _ _)))
            (tr.sndUpTo i.1.castSucc le_rfl) c] := by
      rw [← uniformSample_challenge_append_inr (pSpec₁ := pSpec₁) i, prEvent_map]
    _ ≤ ε₂ i := h₂ _ i _

end AppendGuarded

end Verifier

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **Worst-case round-by-round knowledge soundness composes when the first verifier is
guarded.** The composed extractor is `Extractor.RoundByRound.append` at the first verifier's
verdict map, and the composed knowledge state function is
`KnowledgeStateFunction.appendGuarded`. The challenge error at each round is inherited from the
corresponding component. The two components share only the intermediate relation `rel₂`; no
assumption on an honest prover or on the shared oracle's state is needed. -/
theorem append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (G₁ : V₁.GuardedForm)
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    {K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁}
    {K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂}
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCaseWith init impl rel₁ rel₂ WitMid₁ E₁ K₁ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCaseWith init impl rel₂ rel₃ WitMid₂ E₂ K₂ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCaseWith init impl rel₁ rel₃ _
      (E₁.append E₂ G₁.out) (K₁.appendGuarded G₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  intro stmt i tr
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · exact (KnowledgeStateFunction.appendGuarded_extractionFailure_inl G₁ K₁ K₂ h₁ i stmt
      tr).trans_eq (by simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl])
  · exact (KnowledgeStateFunction.appendGuarded_extractionFailure_inr G₁ K₁ K₂ h₂ i stmt
      tr).trans_eq (by simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr])

/-- Existential form of `append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first`. -/
theorem append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (G₁ : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCase init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨_, _, _, h₁⟩ := (rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mp h₁
  obtain ⟨_, _, _, h₂⟩ := (rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mp h₂
  exact (rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first V₁ V₂ G₁ h₁ h₂⟩

/-- The guarded composition theorem also supplies the prover-averaged round-by-round knowledge
soundness contract, with the same per-round errors. -/
theorem append_rbrKnowledgeSoundness_of_worst_case_of_guarded_first
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (G₁ : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessWorstCase init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (append_rbrKnowledgeSoundnessWorstCase_of_guarded_first V₁ V₂ G₁ h₁ h₂)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [∀ i, OracleInterface (OStmt₃ i)]
  [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)} {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- Oracle verifiers inherit the guarded worst-case composition theorem through their ordinary
verifier semantics. The guard and the component hypotheses concern the converted verifiers. -/
theorem append_rbrKnowledgeSoundnessWorstCase_of_guarded_first
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (G₁ : V₁.toVerifier.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.toVerifier.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.toVerifier.rbrKnowledgeSoundnessWorstCase init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).toVerifier.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_toVerifier]
  exact Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _ G₁ h₁ h₂

/-- Averaged form of `OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`. -/
theorem append_rbrKnowledgeSoundness_of_worst_case_of_guarded_first
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (G₁ : V₁.toVerifier.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.toVerifier.rbrKnowledgeSoundnessWorstCase init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.toVerifier.rbrKnowledgeSoundnessWorstCase init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (append_rbrKnowledgeSoundnessWorstCase_of_guarded_first V₁ V₂ G₁ h₁ h₂)

end OracleVerifier
