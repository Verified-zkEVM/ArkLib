/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Execution
public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.LiftContext.Reduction

/-!
# Pure challenge slots of composed legacy provers

A legacy prover has pure challenge slots (`PureChallengeSlots`) when receiving a challenge has no
effect before the challenge arrives. This is the hypothesis under which the legacy run of a prover
equals the counterpart-first run of its embedding as a program. This file shows that the
composition operations of legacy provers preserve it:

* `pureChallengeSlots_append`: appending, when the first prover's output is pure;
* `pureChallengeSlots_id`: the identity prover;
* `pureChallengeSlots_liftContext`: lifting to an outer context;
* `pureChallengeSlots_seqCompose`: sequential composition of provers with pure outputs.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}

/-- A computation heterogeneously equal to `pure f` is `pure`. -/
private theorem pure_of_heq {X Y : Type} (hXY : X = Y) {x : OracleComp oSpec Y} {f : X}
    (h : HEq x (pure f : OracleComp oSpec X)) : ∃ g, x = pure g := by
  subst hXY; exact ⟨f, eq_of_heq h⟩

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {S₁ W₁ S₂ W₂ S₃ W₃ : Type}

/-- Appending legacy provers keeps every challenge slot `pure` when the first prover's output is
pure. -/
theorem pureChallengeSlots_append (P₁ : _root_.Prover oSpec S₁ W₁ S₂ W₂ pSpec₁)
    (P₂ : _root_.Prover oSpec S₂ W₂ S₃ W₃ pSpec₂) [h : P₁.OutputIsPure]
    (h₁ : PureChallengeSlots P₁) (h₂ : PureChallengeSlots P₂) :
    PureChallengeSlots (P₁.append P₂) := by
  rintro ⟨i, hDir⟩ st
  by_cases hi : i.val < m
  · have hDir₁ : pSpec₁.dir ⟨i.val, hi⟩ = .V_to_P := by
      simpa [Fin.vappend_left_of_lt, hi] using hDir
    obtain ⟨f, hf⟩ := h₁ ⟨⟨i.val, hi⟩, hDir₁⟩
      (cast (_root_.Prover.append_prvState_left _ _ rfl) st)
    refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
    · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₁.«Type» ⟨i.val, hi⟩ := by
        exact (congrArg (pSpec₁ ++ₚ pSpec₂).«Type»
          (Fin.ext rfl : i = Fin.castAdd n ⟨i.val, hi⟩)).trans (append_Type_castAdd _)
      have hS := _root_.Prover.append_prvState_left (P₁ := P₁) (P₂ := P₂) i.succ
        (⟨i.val, hi⟩ : Fin m).succ rfl
      exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
    · conv_lhs => unfold _root_.Prover.append
      dsimp only
      rw [dite_eq_left hi]
      refine (cast_heq _ _).trans (heq_of_eq ?_)
      congr 1
  by_cases him : i.val = m
  · have hn : 0 < n := by have := i.isLt; omega
    have hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P := by
      have := (congrArg (pSpec₁ ++ₚ pSpec₂).dir
        (Fin.ext (by simp [him]) : i = Fin.natAdd m ⟨0, hn⟩)).symm.trans hDir
      simpa [Fin.vappend_right_of_not_lt] using this
    obtain ⟨out, hout⟩ := h.output_is_pure
    have hS₁ := _root_.Prover.append_prvState_left (P₁ := P₁) (P₂ := P₂) i.castSucc
      (Fin.last m)
      (by simp [him])
    obtain ⟨f, hf⟩ := h₂ ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (out (cast hS₁ st)))
    refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
    · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₂.«Type» ⟨0, hn⟩ :=
        (congrArg (pSpec₁ ++ₚ pSpec₂).«Type»
          (Fin.ext (by simp [him]) : i = Fin.natAdd m ⟨0, hn⟩)).trans (append_Type_natAdd _)
      have hS := _root_.Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.succ
        (⟨0, hn⟩ : Fin n).succ (by simp; omega) (by simp; omega)
      exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
    · conv_lhs => unfold _root_.Prover.append
      dsimp only
      rw [dite_eq_right hi, dite_eq_left him]
      refine (cast_heq _ _).trans (heq_of_eq ?_)
      rw [hout]
      simp only [LawfulMonad.pure_bind]
      exact congrArg (fun z => P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input (out z)))
        (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm))
  have hik : i.val - m < n := by have := i.isLt; omega
  have hidx : i = Fin.natAdd m ⟨i.val - m, hik⟩ := Fin.ext (by simp; omega)
  have hDir₂ : pSpec₂.dir ⟨i.val - m, hik⟩ = .V_to_P := by
    have := (congrArg (pSpec₁ ++ₚ pSpec₂).dir hidx).symm.trans hDir
    simpa [Fin.vappend_right_of_not_lt] using this
  have hS₂ := _root_.Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.castSucc
    (⟨i.val - m, hik⟩ : Fin n).castSucc (by simp; omega) (by simp; omega)
  obtain ⟨f, hf⟩ := h₂ ⟨⟨i.val - m, hik⟩, hDir₂⟩ (cast hS₂ st)
  refine pure_of_heq ?_ (HEq.trans ?_ (heq_of_eq hf))
  · have hT : (pSpec₁ ++ₚ pSpec₂).«Type» i = pSpec₂.«Type» ⟨i.val - m, hik⟩ :=
      (congrArg (pSpec₁ ++ₚ pSpec₂).«Type» hidx).trans (append_Type_natAdd _)
    have hS := _root_.Prover.append_prvState_right (P₁ := P₁) (P₂ := P₂) i.succ
      (⟨i.val - m, hik⟩ : Fin n).succ (by simp; omega) (by simp; omega)
    exact congrArg₂ (fun A B => A → B) hT.symm hS.symm
  · conv_lhs => unfold _root_.Prover.append
    dsimp only
    rw [dite_eq_right hi, dite_eq_right him]
    refine (cast_heq _ _).trans (heq_of_eq ?_)
    congr 1
    exact eq_of_heq ((heq_dcast _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- The identity prover has no challenge slots. -/
theorem pureChallengeSlots_id {S W : Type} :
    PureChallengeSlots (_root_.Prover.id : _root_.Prover oSpec S W S W !p[]) :=
  fun i => Fin.elim0 i.1

/-- Lifting a legacy prover to an outer context keeps its challenge slots `pure`. -/
theorem pureChallengeSlots_liftContext {n : ℕ} {pSpec : ProtocolSpec n}
    {OS OW IS IW OS' OW' IS' IW' : Type}
    (lens : Context.Lens OS OS' IS IS' OW OW' IW IW')
    (P : _root_.Prover oSpec IS IW IS' IW' pSpec) (h : PureChallengeSlots P) :
    PureChallengeSlots (P.liftContext lens) := by
  rintro i ⟨st, s, w⟩
  obtain ⟨f, hf⟩ := h i st
  exact ⟨fun chal => ⟨f chal, s, w⟩, by simp [_root_.Prover.liftContext, hf]⟩

/-- Sequentially composing legacy provers with pure outputs keeps every challenge slot `pure`. -/
theorem pureChallengeSlots_seqCompose : ∀ {k : ℕ} (Stmt Wit : Fin (k + 1) → Type)
    {n : Fin k → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin k) →
      _root_.Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
        (pSpec i))
    (_ : ∀ i, (P i).OutputIsPure) (_ : ∀ i, PureChallengeSlots (P i)),
    PureChallengeSlots (_root_.Prover.seqCompose Stmt Wit P)
  | 0, _, _, _, _, _, _, _ => pureChallengeSlots_id
  | _ + 1, Stmt, Wit, _, _, P, hO, hP => by
    exact pureChallengeSlots_append _ _ (h := hO 0) (hP 0)
      (pureChallengeSlots_seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P i.succ)
        (fun i => hO i.succ) (fun i => hP i.succ))

end Interaction.Core.Legacy
