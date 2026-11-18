/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.Basic

/-!
# Appended legacy protocol specifications

Protocol-independent facts about an appended legacy specification `p₁ ++ₚ p₂`, used when an
interaction-layer protocol is related to a legacy protocol built by appending.

* `appendRoute` answers the message queries of `p₁ ++ₚ p₂` with handlers for the two halves;
  `appendRoute_sumEquiv` routes a query named by its half to that half's handler.
* `simulateQ_queryAlongHEq` answers a query transported along an equality of oracle interfaces
  by answering the original query.
* `ChallengeFn` lists the challenge entries of a legacy specification, one at each
  verifier-to-prover position.
* `challenges_append_fst` and `challenges_append_snd` split the challenges of an appended full
  transcript into those of its two parts.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open OracleComp OracleSpec ProtocolSpec

/-! ## Routing an appended message spec -/

section Append

variable {m₁ m₂ : ℕ} {p₁ : ProtocolSpec m₁} {p₂ : ProtocolSpec m₂}
  [O₁ : ∀ i, OracleInterface (p₁.Message i)] [O₂ : ∀ i, OracleInterface (p₂.Message i)]
  {ι : Type} {spec : OracleSpec ι}

/-- Route a query of an appended spec, given by its half, to the handler of that half. -/
def routePart (f : QueryImpl [p₁.Message]ₒ (OracleComp spec))
    (g : QueryImpl [p₂.Message]ₒ (OracleComp spec)) :
    (s : p₁.MessageIdx ⊕ p₂.MessageIdx) →
    (q : OracleInterface.Query ((p₁ ++ₚ p₂).Message (MessageIdx.sumEquiv s))) →
      OracleComp spec (OracleInterface.Response q)
  | .inl i, q => OracleVerifier.queryAlongHEq inferInstance (O₁ i)
      (by simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left])
      (message_interface_inl i).symm (fun q' => f ⟨i, q'⟩) q
  | .inr i, q => OracleVerifier.queryAlongHEq inferInstance (O₂ i)
      (by simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right])
      (message_interface_inr i).symm (fun q' => g ⟨i, q'⟩) q

/-- Route a query along an equation naming its half. -/
def routeAlong (f : QueryImpl [p₁.Message]ₒ (OracleComp spec))
    (g : QueryImpl [p₂.Message]ₒ (OracleComp spec)) {s : p₁.MessageIdx ⊕ p₂.MessageIdx}
    {j : (p₁ ++ₚ p₂).MessageIdx} (e : MessageIdx.sumEquiv s = j)
    (q : OracleInterface.Query ((p₁ ++ₚ p₂).Message j)) :
    OracleComp spec (OracleInterface.Response q) := by
  subst e
  exact routePart f g s q

/-- Route the message queries of an appended spec to the handlers of its two halves. -/
def appendRoute (f : QueryImpl [p₁.Message]ₒ (OracleComp spec))
    (g : QueryImpl [p₂.Message]ₒ (OracleComp spec)) :
    QueryImpl [(p₁ ++ₚ p₂).Message]ₒ (OracleComp spec) :=
  fun q => routeAlong f g (MessageIdx.sumEquiv.apply_symm_apply q.1) q.2

/-- A query named by its half is routed to the handler of that half. -/
theorem appendRoute_sumEquiv (f : QueryImpl [p₁.Message]ₒ (OracleComp spec))
    (g : QueryImpl [p₂.Message]ₒ (OracleComp spec)) (s : p₁.MessageIdx ⊕ p₂.MessageIdx)
    (q : OracleInterface.Query ((p₁ ++ₚ p₂).Message (MessageIdx.sumEquiv s))) :
    appendRoute f g ⟨MessageIdx.sumEquiv s, q⟩ = routePart f g s q := by
  have key : ∀ s' (e : MessageIdx.sumEquiv s' = MessageIdx.sumEquiv s),
      routeAlong f g e q = routePart f g s q := by
    intro s' e
    obtain rfl := MessageIdx.sumEquiv.injective e
    rfl
  exact key _ _

/-- Answering a transported query agrees with answering the original data. -/
theorem simulateQ_queryAlongHEq {A B : Type} (OA : OracleInterface A) (OB : OracleInterface B)
    (hType : A = B) (h : HEq OA OB) (impl : QueryImpl spec Id)
    (k : (q : OB.Query) → OracleComp spec (OB.Response q)) (x : A) (y : B) (hxy : HEq x y)
    (hk : ∀ q, simulateQ impl (k q) = OB.answer y q) (q : OA.Query) :
    simulateQ impl (OracleVerifier.queryAlongHEq OA OB hType h k q) = OA.answer x q := by
  subst hType
  cases eq_of_heq h
  cases eq_of_heq hxy
  exact hk q

end Append

/-! ## Challenges of an appended transcript -/

/-- Challenge entries of a legacy spec: a value at each verifier-to-prover position. -/
abbrev ChallengeFn {k : ℕ} (pSpec : ProtocolSpec k) :=
  (i : Fin k) → pSpec.dir i = .V_to_P → pSpec.Type i

/-- The first-part challenges of an appended transcript are those of its first part. -/
theorem challenges_append_fst {m k : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec k}
    (A : FullTranscript p₁) (B : FullTranscript p₂) :
    Challenges.fst (A ++ₜ B).challenges = A.challenges := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  exact (FullTranscript.fst_apply_heq _ _).symm.trans
    (heq_of_eq (congrFun (FullTranscript.append_fst A B) i.1))

/-- The second-part challenges of an appended transcript are those of its second part. -/
theorem challenges_append_snd {m k : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec k}
    (A : FullTranscript p₁) (B : FullTranscript p₂) :
    Challenges.snd (A ++ₜ B).challenges = B.challenges := by
  funext i
  refine eq_of_heq ((cast_heq _ _).trans ?_)
  exact (FullTranscript.snd_apply_heq _ _).symm.trans
    (heq_of_eq (congrFun (FullTranscript.append_snd A B) i.1))

end Interaction.Core.Legacy
