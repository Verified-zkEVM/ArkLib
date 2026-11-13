/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Accumulation
public import VCVio.EvalDist.Monad.DependentTable

/-!
# Presampling ordered protocol challenges

Ambient oracle calls may be arbitrary and stateful. Only protocol challenge calls are ordered:
each index lies in the given half-open interval and every later challenge has a larger index.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}

/-- A computation asks protocol challenges in strictly increasing round order inside `[lo, hi)`.
Ambient queries do not advance the challenge position. -/
inductive OrderedChallenges {α : Type} :
    ℕ → ℕ → OracleComp (oSpec + [pSpec.Challenge]ₒ) α → Prop
  | pure {lo hi} (a : α) (h : lo ≤ hi) : OrderedChallenges lo hi (pure a)
  | ambient {lo hi} (t : oSpec.Domain)
      (k : oSpec.Range t → OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
      (h : ∀ u, OrderedChallenges lo hi (k u)) :
      OrderedChallenges lo hi (liftM ((oSpec + [pSpec.Challenge]ₒ).query (.inl t)) >>= k)
  | challenge {lo hi} (i : pSpec.ChallengeIdx)
      (k : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
      (hlo : lo ≤ i.1.val) (hhi : i.1.val < hi)
      (h : ∀ c, OrderedChallenges (i.1.val + 1) hi (k c)) :
      OrderedChallenges lo hi
        ((liftM (pSpec.getChallenge i) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) >>= k)

namespace OrderedChallenges

/-- Ordered computations compose on adjacent intervals. -/
theorem bind {α β : Type} {lo mid hi : ℕ}
    {oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α}
    {f : α → OracleComp (oSpec + [pSpec.Challenge]ₒ) β}
    (h : OrderedChallenges lo mid oa)
    (hf : ∀ a, OrderedChallenges mid hi (f a)) (hm : mid ≤ hi) :
    OrderedChallenges lo hi (oa >>= f) := by
  induction h with
  | pure a h =>
    simp only [pure_bind]
    have weaken {l r : ℕ} {ob : OracleComp (oSpec + [pSpec.Challenge]ₒ) β}
        (hb : OrderedChallenges l r ob) (l' : ℕ) (hl : l' ≤ l) :
        OrderedChallenges l' r ob := by
      induction hb with
      | pure b hb => exact .pure b (hl.trans hb)
      | ambient t k _ ih => exact .ambient t k (fun u => ih u hl)
      | challenge i k hlo hhi hc ih => exact .challenge i k (hl.trans hlo) hhi hc
    exact weaken (hf a) _ h
  | ambient t k _ ih =>
    rw [bind_assoc]
    exact .ambient t _ (fun u => ih u hf hm)
  | challenge i k hlo hhi _ ih =>
    rw [bind_assoc]
    exact .challenge i _ hlo (hhi.trans_le hm) (fun c => ih c hf hm)

/-- Lifting ambient queries adds no challenge calls. -/
theorem lift {α : Type} (oa : OracleComp oSpec α) (lo hi : ℕ) (h : lo ≤ hi) :
    OrderedChallenges (oSpec := oSpec) (pSpec := pSpec) lo hi (liftM oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [liftM_pure] using OrderedChallenges.pure a h
  | query_bind t k ih =>
    simp only [liftM_bind]
    exact .ambient t _ ih

end OrderedChallenges

/-- Answer protocol challenges from a fixed vector and leave ambient queries in place. -/
def fixedChallengeImpl (c : ∀ i, pSpec.Challenge i) :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (OracleComp oSpec)
  | .inl t => liftM (oSpec.query t)
  | .inr ⟨i, ()⟩ => pure (c i)

@[simp]
theorem simulateQ_fixed_challenge (c : ∀ i, pSpec.Challenge i) (i : pSpec.ChallengeIdx) :
    simulateQ (fixedChallengeImpl (oSpec := oSpec) c)
      (liftM (pSpec.getChallenge i) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) =
      pure (c i) := by
  exact (simulateQ_spec_query (fixedChallengeImpl (oSpec := oSpec) c)
    (.inr ⟨i, ()⟩)).trans rfl

/-- An ordered computation cannot distinguish vectors agreeing on its challenge interval. -/
theorem OrderedChallenges.fixed_congr {α : Type} {lo hi : ℕ}
    {oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α}
    (h : OrderedChallenges lo hi oa) (c d : ∀ i, pSpec.Challenge i)
    (hcd : ∀ i, lo ≤ i.1.val → i.1.val < hi → c i = d i) :
    simulateQ (fixedChallengeImpl c) oa = simulateQ (fixedChallengeImpl d) oa := by
  induction h with
  | pure a _ => simp only [simulateQ_pure]
  | ambient t k _ ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, fixedChallengeImpl]
    congr 1
    funext u
    exact ih u hcd
  | challenge i k hlo hhi _ ih =>
    simp only [simulateQ_bind, simulateQ_fixed_challenge, pure_bind]
    rw [hcd i hlo hhi]
    exact ih _ (fun j hj hj' => hcd j (by omega) hj')

/-- Uniform presampling of the entire challenge vector is equivalent in distribution to lazy
sampling for any ordered computation. The full final ambient state is retained. -/
theorem OrderedChallenges.presample {α σ : Type} {lo hi : ℕ}
    [∀ i, SampleableType (pSpec.Challenge i)]
    [SampleableType (∀ i, pSpec.Challenge i)]
    {oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α}
    (h : OrderedChallenges lo hi oa) (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ) :
    (do let c ← $ᵗ (∀ i, pSpec.Challenge i)
        (simulateQ impl (simulateQ (fixedChallengeImpl c) oa)).run s) =ᵈ
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa).run s := by
  classical
  induction h generalizing s with
  | pure a _ =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  | ambient t k h ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, fixedChallengeImpl, StateT.run_bind]
    change (do let c ← $ᵗ (∀ i, pSpec.Challenge i)
               let z ← (impl t).run s
               (simulateQ impl (simulateQ (fixedChallengeImpl c) (k z.1))).run z.2) =ᵈ _
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    exact EvalDistEq.bind_right ((impl t).run s) (fun z => ih z.1 z.2)
  | challenge i k hlo hhi h ih =>
    simp only [simulateQ_bind, simulateQ_fixed_challenge, pure_bind]
    let : ∀ j, MeasurableSpace (pSpec.Challenge j) := fun _ => ⊤
    let : MeasurableSpace (α × σ) := ⊤
    have hcell := evalDist_bind_bind_update_dependent i ($ᵗ (pSpec.Challenge i))
      ($ᵗ (∀ j, pSpec.Challenge j)) SampleableType.evalDist_uniformSample
      SampleableType.evalDist_uniformSample
      (fun c => (simulateQ impl (simulateQ (fixedChallengeImpl c) (k (c i)))).run s)
    refine (EvalDistEq.of_evalDist_eq hcell).symm.trans ?_
    simp only [Function.update_self]
    have hignore (u : pSpec.Challenge i) (c : ∀ j, pSpec.Challenge j) :
        simulateQ (fixedChallengeImpl (Function.update c i u)) (k u) =
          simulateQ (fixedChallengeImpl c) (k u) := by
      apply (h u).fixed_congr
      intro j hj _
      apply Function.update_of_ne
      intro he
      subst j
      omega
    simp_rw [hignore]
    have hz := EvalDistEq.bind_right ($ᵗ (pSpec.Challenge i)) (fun u => ih u s)
    have hget : simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (liftM (pSpec.getChallenge i) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) =
        (liftM ($ᵗ (pSpec.Challenge i)) : StateT σ ProbComp _) :=
      simulateQ_addLift_challengeQueryImpl_getChallenge impl i
    rw [hget]
    simpa only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind] using hz

end ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- A protocol round asks only its own challenge, if it is a challenge round. -/
theorem orderedChallenges_processRound (j : Fin n)
    (z : pSpec.Transcript j.castSucc × P.PrvState j.castSucc) :
    OrderedChallenges j.val (j.val + 1) (P.processRound j (pure z)) := by
  cases hd : pSpec.dir j with
  | P_to_V =>
    rw [processRound_of_dir_eq_P_to_V _ hd]
    simp only [pure_bind]
    apply (OrderedChallenges.lift _ j.val j.val le_rfl).bind
    · intro r
      exact .pure _ (by omega)
    · omega
  | V_to_P =>
    rw [processRound_of_dir_eq_V_to_P _ hd]
    simp only [pure_bind]
    apply OrderedChallenges.challenge ⟨j, hd⟩ _ le_rfl (Nat.lt_succ_self j.val)
    intro c
    apply (OrderedChallenges.lift _ (j.val + 1) (j.val + 1) le_rfl).bind
    · intro f
      exact .pure _ le_rfl
    · exact le_rfl

/-- Prefix execution asks its protocol challenges once each, in increasing round order. -/
theorem orderedChallenges_runToRound (i : Fin (n + 1)) (stmt : StmtIn) (aux : WitIn) :
    OrderedChallenges 0 i.val (P.runToRound i stmt aux) := by
  induction i using Fin.induction with
  | zero => exact .pure _ le_rfl
  | succ j ih =>
    rw [runToRound_succ, processRound_bind]
    exact ih.bind (P.orderedChallenges_processRound j) (by simp)

/-- Output computation only makes ambient queries, so the full run also has ordered challenges. -/
theorem orderedChallenges_run (stmt : StmtIn) (aux : WitIn) :
    OrderedChallenges 0 n (P.run stmt aux) := by
  unfold run
  apply (P.orderedChallenges_runToRound (Fin.last n) stmt aux).bind
  · intro z
    exact (OrderedChallenges.lift _ n n le_rfl).bind (fun _ => .pure _ le_rfl) le_rfl
  · exact le_rfl

end Prover
