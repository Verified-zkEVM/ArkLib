/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Generic.Program
import all VCVio.CryptoFoundations.GroupModel.Instances

/-!
# Exact implementation of the KZG algebraic recovery reduction

Real execution of the generic program agrees with first-claim recovery after the FKL
translation. The proof tracks coefficient metadata and preserves the two verifier-key handles.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace KZG.Generic

attribute [local implicit_reducible] spec handleSpec PFam

variable {F G₁ G₂ Gₜ D : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]

omit [DecidableEq F] in
/-- A forwarded query has exactly the tracked pairing step's real semantics. -/
theorem runGen_groupQuery (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (t : GroupModel.Query F pairingSig) (st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ) :
    runGen (pairingReal e) (fun _ => id)
      (liftM ((genSpec F pairingSig).query (.inl t))) (Pairing.table st) =
      pure ((Pairing.step e t st).1, Pairing.table (Pairing.step e t st).2) := by
  simpa only [runGen, GroupModel.run, simulateQ_spec_query, QueryImpl.add_apply_inl] using
    Pairing.step_projection (G := AGM.Group G₁ G₂) (N := ProbComp) e t st

omit [DecidableEq F] in
/-- Each tracked step extends the real table, so existing key handles remain valid. -/
theorem step_table_extends (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (t : GroupModel.Query F pairingSig) (st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ) :
    Tbl.Extends (Pairing.table st) (Pairing.table (Pairing.step e t st).2) := by
  apply impl_extends (pairingReal e) (fun _ => id) (m := ProbComp) t (Pairing.table st)
    ((Pairing.step e t st).1, Pairing.table (Pairing.step e t st).2)
  rw [Pairing.step_projection (G := AGM.Group G₁ G₂) (N := ProbComp) e t st]
  simp

omit [DecidableEq F] in
/-- Candidate testing implements the ordinary list search against the two fixed source keys. -/
theorem runGen_testRoots (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (rs : List F)
    (tbl : Tbl (PFam G₁ G₂ Gₜ)) (g₂ y : G₂)
    (hlen : 2 ≤ (tbl .g₂).length)
    (hzero : lookup tbl .g₂ 0 = g₂) (hone : lookup tbl .g₂ 1 = y) :
    Prod.fst <$> runGen (pairingReal e) (fun _ => id) (testRoots rs) tbl =
      pure ((rs.find? fun r => decide (r • g₂ = y)).getD 0) := by
  induction rs generalizing tbl with
  | nil => rfl
  | cons r rs ih =>
      let tbl' := append tbl .g₂ (r • lookup tbl .g₂ 0)
      have hz : lookup tbl' .g₂ 0 = g₂ :=
        (lookup_append_old tbl .g₂ _ .g₂ 0 (by change 0 < (tbl .g₂).length; omega)).trans hzero
      have ho : lookup tbl' .g₂ 1 = y :=
        (lookup_append_old tbl .g₂ _ .g₂ 1 (by change 1 < (tbl .g₂).length; omega)).trans hone
      have hf : lookup tbl' .g₂ (tbl .g₂).length = r • g₂ := by
        rw [lookup_append_fresh, hzero]
        rfl
      have hl : 2 ≤ (tbl' .g₂).length := by simp [tbl', append]; omega
      have heq : runGen (pairingReal e) (fun _ => id)
          (liftM ((genSpec F pairingSig).query (.inl (.eq .g₂ (tbl .g₂).length 1)))) tbl' =
          pure (decide (r • g₂ = y), tbl') := by
        change (pure (decide (lookup tbl' .g₂ (tbl .g₂).length =
          lookup tbl' .g₂ 1), tbl') : ProbComp _) = _
        rw [hf, ho]
      rw [testRoots, runGen_bind, runGen_smul, pure_bind]
      change Prod.fst <$> runGen (pairingReal e) (fun _ => id)
        (liftM ((genSpec F pairingSig).query (.inl (.eq .g₂ (tbl .g₂).length 1))) >>= _) tbl' = _
      rw [runGen_bind, heq, pure_bind]
      by_cases hr : r • g₂ = y
      · simp [hr, runGen_pure]
      · simpa [hr, List.find?_cons] using ih tbl' hl hz ho

/-- The real recovery execution equals the FKL explanation run followed by first-claim search. -/
theorem runGen_reductionProgram (n : ℕ) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (p : OracleComp (adversarySpec F) (Message D (fun _ : PSort => Handle)))
    (st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ) (g₂ : G₂) (vk : Fin 2 → G₂)
    (hlen : 2 ≤ (Pairing.table st .g₂).length)
    (hzero : lookup (Pairing.table st) .g₂ 0 = g₂)
    (hone : lookup (Pairing.table st) .g₂ 1 = vk 1) :
    Prod.fst <$> runGen (pairingReal e) (fun _ => id)
      (reductionProgram n roots claims p (Pairing.eraseValues st)) (Pairing.table st) =
    AGM.recoverFirst (n := n) g₂ vk roots claims <$>
      simulateQ (fun q => withCoins (QueryImpl.ofLift unifSpec ProbComp)
        sourceOracle q.value) (Pairing.explainProgram e p st) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure msg =>
      change Prod.fst <$> runGen (pairingReal e) (fun _ => id) (testRoots _) _ =
        AGM.recoverFirst (n := n) g₂ vk roots claims <$> pure (explain st.1 _)
      rw [runGen_testRoots e _ _ g₂ (vk 1) hlen hzero hone, map_pure]
      congr 1
      unfold AGM.recoverFirst AGM.candidatesFirst AGM.coefficients
      simp only [Pairing.eraseValues]
      rw [Pairing.explain_eraseSourceValues_coefficients]
      rfl
  | query_bind t next ih =>
      rcases t with t | t | k | t
      · change Prod.fst <$> runGen (pairingReal e) (fun _ => id)
          (liftM ((genSpec F pairingSig).query (.inl t)) >>= fun a =>
            reductionProgram n roots claims (next a)
              (Pairing.step 0 t (Pairing.eraseValues st)).2) _ = _
        rw [runGen_bind, runGen_groupQuery, pure_bind,
          ← Pairing.eraseValues_step (G := AGM.Group G₁ G₂) e t st]
        have hext := step_table_extends e t st
        exact ih _ _ (hlen.trans (hext .g₂).length_le)
          ((lookup_eq_of_prefix (tbl := Pairing.table st) PSort.g₂ (hext .g₂) 0
            (by change 0 < (Pairing.table st .g₂).length; omega)).trans hzero)
          ((lookup_eq_of_prefix (tbl := Pairing.table st) PSort.g₂ (hext .g₂) 1
            (by change 1 < (Pairing.table st .g₂).length; omega)).trans hone)
      · exact ih () st hlen hzero hone
      · change Prod.fst <$> runGen (pairingReal e) (fun _ => id)
          (liftM ((genSpec F pairingSig).query (.inr k)) >>= fun a =>
            reductionProgram n roots claims (next a) (Pairing.eraseValues st)) _ =
          AGM.recoverFirst (n := n) g₂ vk roots claims <$>
            simulateQ _ (liftM ((explainedSpec F (AGM.Group G₁ G₂) (CoinQuery Empty)
              (CoinReply (fun _ => Unit))).query
              ⟨⟨.inr k, fun _ => []⟩, fun _ => []⟩) >>= _)
        simp only [runGen_bind, simulateQ_bind, simulateQ_spec_query,
          withCoins_apply_inr, map_bind, bind_assoc, pure_bind, receive_empty]
        change (do
          let a ← (liftM (unifSpec.query k) : ProbComp _)
          Prod.fst <$> runGen (pairingReal e) (fun _ => id)
            (reductionProgram n roots claims (next a) (Pairing.eraseValues st))
            (Pairing.table st)) = _
        apply bind_congr
        intro a
        exact ih a st hlen hzero hone
      · exact t.data.elim

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] in
/-- The real key basis erases to metadata determined solely by its lengths. -/
theorem erase_initial (n : ℕ) (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    Pairing.eraseValues (T := Gₜ)
      ((fun b => List.range ((AGM.initialInput ck vk).groups b).length,
        trackInputs (AGM.initialInput ck vk).groups), []) = initialMetadata (F := F) n := by
  apply Prod.ext
  · apply Prod.ext
    · funext b
      cases b <;> simp [Pairing.eraseValues, Pairing.eraseSourceValues, initialMetadata,
        AGM.initialInput, AGM.groupInputs]
    · funext b
      cases b <;>
        simp only [Pairing.eraseValues, Pairing.eraseSourceValues, initialMetadata,
          AGM.initialInput, AGM.groupInputs, trackInputs, mapTbl, Bool.false_eq_true,
          ↓reduceIte] <;>
        apply List.ext_getElem
      all_goals simp only [List.length_map, List.length_mapIdx,
        List.length_ofFn, List.length_replicate]
      all_goals
        intro i hi hj
        simp only [List.getElem_map, List.getElem_mapIdx, List.getElem_replicate]
  · rfl

/-- First-claim recovery of the translated adversary equals the explicit generic program.
The generator is the first verifier-key entry, as it is in every KZG and PairingDLog game. -/
theorem reductionFirst_toAlgebraic (n : ℕ) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (A : Adversary F D) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (ck : Fin (n + 1) → G₁) (vk : Fin 2 → G₂) :
    AGM.reductionFirst (n := n) (vk 0) roots claims (A.toAlgebraic e) ck vk =
      PairingDLog.Adversary.ofGeneric (q₁ := n) (q₂ := 1) e
        (program n roots claims A) ck vk := by
  let st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ :=
    ((fun b => List.range ((AGM.initialInput ck vk).groups b).length,
      trackInputs (AGM.initialInput ck vk).groups), [])
  have ht : Pairing.table st = (Pairing.pairingMessage (T := Gₜ)
      (AGM.initialInput ck vk)).groups := by
    have h := initial_projection (F := F) (AGM.initialInput ck vk).groups
    funext s
    cases s with
    | g₁ => exact congrFun h false
    | g₂ => exact congrFun h true
    | gₜ => rfl
  have hz : lookup (Pairing.table st) .g₂ 0 = vk 0 := by
    rw [ht]
    simp [lookup, Pairing.pairingMessage, AGM.initialInput, AGM.groupInputs, List.getD]
  have ho : lookup (Pairing.table st) .g₂ 1 = vk 1 := by
    rw [ht]
    simp [lookup, Pairing.pairingMessage, AGM.initialInput, AGM.groupInputs, List.getD]
  have hl : 2 ≤ (Pairing.table st .g₂).length := by
    rw [ht]
    simp [Pairing.pairingMessage, AGM.initialInput, AGM.groupInputs]
  have h := runGen_reductionProgram n roots claims e (A (input n)) st (vk 0) vk hl hz ho
  rw [erase_initial n ck vk, ht] at h
  unfold AGM.reductionFirst AGM.run Adversary.toAlgebraic
  rw [relabel_run]
  change _ = Prod.fst <$> runGen (pairingReal e) (fun _ => id)
    (program n roots claims A) (Pairing.pairingMessage (AGM.initialInput ck vk)).groups
  rw [program, h]
  congr 2
  change Pairing.explainProgram e (A _) st = Pairing.explainProgram e (A (input n)) st
  congr 2
  congr 1
  funext s
  cases s <;> simp [AGM.initialInput, AGM.groupInputs]

/-- The two reductions have exactly the same PairingDLog experiment. -/
theorem experiment_reductionFirst_toAlgebraic [SampleableType F]
    (n : ℕ) (roots : CPolynomial F → List F) (claims : D → List (F × F))
    (A : Adversary F D) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    PairingDLog.experiment g₁ g₂ (AGM.reductionFirst (n := n) g₂ roots claims (A.toAlgebraic e)) =
      PairingDLog.experiment g₁ g₂
        (PairingDLog.Adversary.ofGeneric (q₁ := n) (q₂ := 1) e (program n roots claims A)) := by
  unfold PairingDLog.experiment
  apply bind_congr
  intro a
  have h := reductionFirst_toAlgebraic n roots claims A e
    (fun j => a ^ (j : ℕ) • g₁) (fun j => a ^ (j : ℕ) • g₂)
  simpa using congrArg (fun p => p >>= fun x => pure (decide (x = a))) h

end KZG.Generic
