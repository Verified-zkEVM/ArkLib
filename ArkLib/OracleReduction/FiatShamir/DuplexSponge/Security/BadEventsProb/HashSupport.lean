/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SampleProduct

/-!
# Generic random-function support for Lemma 5.8

The paper-facing hash bounds use only these reusable facts: a patched random-function coordinate
is uniform under a prefix invariant, the same result survives an independent side sample, and
per-target atom bounds lift to a finite family of targets.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

/-- A predicate-conditioned fresh optional readout can hit at most `m` targets. -/
lemma probEvent_pred_fresh_hits_fin_targets_le {α β : Type} [Fintype β]
    (exp : ProbComp α) (P : α → Prop) (fresh : α → Option β) (m : ℕ)
    (target : Fin m → α → Option β) (D : ℝ≥0∞)
    (hAtom : ∀ i c,
      Pr[ fun a => P a ∧ fresh a = some c ∧ target i a = some c | exp]
        ≤ Pr[ fun a => target i a = some c | exp] / D) :
    Pr[ fun a => P a ∧ ∃ i : Fin m, ∃ c : β,
        fresh a = some c ∧ target i a = some c | exp]
      ≤ (m : ℝ≥0∞) / D := by
  classical
  have hPerTarget : ∀ i : Fin m,
      Pr[ fun a => P a ∧ ∃ c : β, fresh a = some c ∧ target i a = some c | exp]
        ≤ 1 / D := by
    intro i
    calc
      Pr[ fun a => P a ∧ ∃ c : β, fresh a = some c ∧ target i a = some c | exp]
          ≤ Pr[ fun a => ∃ c ∈ (Finset.univ : Finset β),
              P a ∧ fresh a = some c ∧ target i a = some c | exp] := by
            apply probEvent_mono
            intro a _ha h
            obtain ⟨hP, c, hc⟩ := h
            exact ⟨c, Finset.mem_univ c, hP, hc⟩
      _ ≤ ∑ c : β,
              Pr[ fun a => P a ∧ fresh a = some c ∧ target i a = some c | exp] :=
            probEvent_exists_finset_le_sum (Finset.univ : Finset β) exp
              (fun c a => P a ∧ fresh a = some c ∧ target i a = some c)
      _ ≤ ∑ c : β, Pr[ fun a => target i a = some c | exp] / D := by
            apply Finset.sum_le_sum
            intro c _hc
            exact hAtom i c
      _ = (∑ c : β, Pr[ fun a => target i a = some c | exp]) / D := by
            calc
              ∑ c : β, Pr[ fun a => target i a = some c | exp] / D
                  = ∑ c : β, Pr[ fun a => target i a = some c | exp] * D⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro c _hc
                    rw [div_eq_mul_inv]
              _ = (∑ c : β, Pr[ fun a => target i a = some c | exp]) * D⁻¹ := by
                    rw [Finset.sum_mul]
              _ = (∑ c : β, Pr[ fun a => target i a = some c | exp]) / D := by
                    rw [div_eq_mul_inv]
      _ ≤ 1 / D := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul' (sum_probEvent_eq_some_le_one exp (target i)) le_rfl
  calc
    Pr[ fun a => P a ∧ ∃ i : Fin m, ∃ c : β,
        fresh a = some c ∧ target i a = some c | exp]
        ≤ Pr[ fun a => ∃ i ∈ (Finset.univ : Finset (Fin m)),
            P a ∧ ∃ c : β, fresh a = some c ∧ target i a = some c | exp] := by
          apply probEvent_mono
          intro a _ha h
          obtain ⟨hP, i, hi⟩ := h
          exact ⟨i, Finset.mem_univ i, hP, hi⟩
    _ ≤ ∑ i : Fin m,
            Pr[ fun a => P a ∧ ∃ c : β,
              fresh a = some c ∧ target i a = some c | exp] :=
          probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin m)) exp
            (fun i a => P a ∧ ∃ c : β, fresh a = some c ∧ target i a = some c)
    _ ≤ ∑ _i : Fin m, 1 / D := by
          apply Finset.sum_le_sum
          intro i _hi
          exact hPerTarget i
    _ = (m : ℝ≥0∞) / D := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [div_eq_mul_inv, one_mul]
          exact (div_eq_mul_inv (m : ℝ≥0∞) D).symm

/-- An unconditioned fresh optional readout can hit at most `m` targets. -/
lemma probEvent_fresh_hits_fin_targets_le {α β : Type} [Fintype β]
    (exp : ProbComp α) (fresh : α → Option β) (m : ℕ)
    (target : Fin m → α → Option β) (D : ℝ≥0∞)
    (hAtom : ∀ i c,
      Pr[ fun a => fresh a = some c ∧ target i a = some c | exp]
        ≤ Pr[ fun a => target i a = some c | exp] / D) :
    Pr[ fun a => ∃ i : Fin m, ∃ c : β,
        fresh a = some c ∧ target i a = some c | exp]
      ≤ (m : ℝ≥0∞) / D := by
  have hEvent :
      (fun a => ∃ i : Fin m, ∃ c : β,
        fresh a = some c ∧ target i a = some c) =
      fun a => True ∧ ∃ i : Fin m, ∃ c : β,
        fresh a = some c ∧ target i a = some c := by
    funext a
    apply propext
    constructor
    · intro h
      exact ⟨True.intro, h⟩
    · intro h
      exact h.2
  rw [hEvent]
  exact probEvent_pred_fresh_hits_fin_targets_le exp (fun _ => True) fresh m target D
    (by
      intro i c
      have hEvent :
          (fun a => True ∧ fresh a = some c ∧ target i a = some c) =
            fun a => fresh a = some c ∧ target i a = some c := by
          funext a
          apply propext
          constructor
          · intro h
            exact h.2
          · intro h
            exact ⟨True.intro, h⟩
      rw [hEvent]
      exact hAtom i c)

/-- A patched coordinate of a random function is uniform under an update-invariant predicate. -/
lemma probEvent_uniformFn_freshCoord_le
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
    [SampleableType B] [SampleableType (A → B)]
    (P : (A → B) → Prop) (q : A) (c : B)
    (hinv : ∀ (g : A → B) (v : B), P (Function.update g q v) ↔ P g) :
    Pr[ fun h => P h ∧ h q = c | ($ᵗ (A → B)) ]
      ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] / (Fintype.card B : ℝ≥0∞) := by
  classical
  have hsymm : ∀ c' : B,
      Pr[ fun h => P h ∧ h q = c' | ($ᵗ (A → B)) ]
        = Pr[ fun h => P h ∧ h q = c | ($ᵗ (A → B)) ] := by
    intro c'
    let e : B ≃ B := Equiv.swap c c'
    let T : (A → B) ≃ (A → B) :=
      { toFun := fun h => Function.update h q (e (h q))
        invFun := fun h => Function.update h q (e.symm (h q))
        left_inv := by
          intro h
          funext a
          by_cases ha : a = q <;> simp [Function.update, ha]
        right_inv := by
          intro h
          funext a
          by_cases ha : a = q <;> simp [Function.update, ha] }
    rw [probEvent_uniformSample_equiv_invariant T (fun h => P h ∧ h q = c')]
    have hpred : (fun h => P (T h) ∧ (T h) q = c') = fun h => P h ∧ h q = c := by
      funext h
      apply propext
      have hTq : (T h) q = e (h q) := by
        simp [T, Function.update]
      have hTP : P (T h) ↔ P h := by
        change P (Function.update h q (e (h q))) ↔ P h
        exact hinv h (e (h q))
      rw [hTq, hTP]
      constructor
      · rintro ⟨hp, he⟩
        refine ⟨hp, ?_⟩
        dsimp [e] at he
        rw [Equiv.swap_apply_eq_iff] at he
        rw [show Equiv.swap c c' c' = c by simp] at he
        exact he
      · rintro ⟨hp, he⟩
        refine ⟨hp, ?_⟩
        rw [he]
        simp [e]
    rw [hpred]
  have hsum : (Fintype.card B : ℝ≥0∞) * Pr[ fun h => P h ∧ h q = c | ($ᵗ (A → B)) ]
      ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] := by
    calc
      (Fintype.card B : ℝ≥0∞) * Pr[ fun h => P h ∧ h q = c | ($ᵗ (A → B)) ]
          = ∑ _c' : B, Pr[ fun h => P h ∧ h q = c | ($ᵗ (A → B)) ] := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ c' : B, Pr[ fun h => P h ∧ h q = c' | ($ᵗ (A → B)) ] :=
          Finset.sum_congr rfl (fun c' _ => (hsymm c').symm)
      _ ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] :=
          sum_probEvent_and_eq_le _ (fun h => P h) (fun h => h q)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [Fintype.card_ne_zero]))
    (Or.inl (by simp)), mul_comm]
  exact hsum

/-- An adaptively selected random-function coordinate is uniform under its fiber invariant. -/
lemma probEvent_uniformFn_freshOptionalCoord_le
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
    [SampleableType B] [SampleableType (A → B)]
    (P : (A → B) → Prop) (read : (A → B) → Option A) (c : B)
    (hinv : ∀ (g : A → B) (q : A) (v : B),
      (P (Function.update g q v) ∧ read (Function.update g q v) = some q) ↔
        (P g ∧ read g = some q)) :
    Pr[ fun h => P h ∧ ∃ q : A, read h = some q ∧ h q = c | ($ᵗ (A → B)) ]
      ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] / (Fintype.card B : ℝ≥0∞) := by
  classical
  calc
    Pr[ fun h => P h ∧ ∃ q : A, read h = some q ∧ h q = c | ($ᵗ (A → B)) ]
        ≤ Pr[ fun h => ∃ q ∈ (Finset.univ : Finset A),
            (P h ∧ read h = some q) ∧ h q = c | ($ᵗ (A → B)) ] := by
          apply probEvent_mono
          intro h _hh hEvent
          obtain ⟨hP, q, hread, hval⟩ := hEvent
          exact ⟨q, Finset.mem_univ q, ⟨hP, hread⟩, hval⟩
    _ ≤ ∑ q : A,
          Pr[ fun h => (P h ∧ read h = some q) ∧ h q = c | ($ᵗ (A → B)) ] :=
        probEvent_exists_finset_le_sum (Finset.univ : Finset A) _ _
    _ ≤ ∑ q : A,
          Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ] /
            (Fintype.card B : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact probEvent_uniformFn_freshCoord_le
          (P := fun h => P h ∧ read h = some q) (q := q) (c := c)
          (by
            intro g v
            exact hinv g q v)
    _ = (∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ]) /
          (Fintype.card B : ℝ≥0∞) := by
        calc
          ∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ] /
              (Fintype.card B : ℝ≥0∞)
              = ∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ] *
                  (Fintype.card B : ℝ≥0∞)⁻¹ := by
                apply Finset.sum_congr rfl
                intro q _hq
                rw [div_eq_mul_inv]
          _ = (∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ]) *
                (Fintype.card B : ℝ≥0∞)⁻¹ := by
              rw [Finset.sum_mul]
          _ = (∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ]) /
                (Fintype.card B : ℝ≥0∞) := by
              rw [div_eq_mul_inv]
    _ ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] / (Fintype.card B : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul' ?_ le_rfl
        calc
          ∑ q : A, Pr[ fun h => P h ∧ read h = some q | ($ᵗ (A → B)) ]
              ≤ ∑ o : Option A, Pr[ fun h => P h ∧ read h = o | ($ᵗ (A → B)) ] := by
                rw [Fintype.sum_option]
                exact le_add_self
          _ ≤ Pr[ fun h => P h | ($ᵗ (A → B)) ] :=
                sum_probEvent_and_eq_le ($ᵗ (A → B)) P read

/-- Adaptive fresh-coordinate uniformity survives an independent product-side sample. -/
lemma probEvent_uniformFn_prod_freshOptionalCoord_le
    {A B Γ : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
    [SampleableType B] [SampleableType (A → B)]
    (side : ProbComp Γ)
    (P : (A → B) × Γ → Prop) (read : (A → B) × Γ → Option A) (c : B)
    (hinv : ∀ (y : Γ) (g : A → B) (q : A) (v : B),
      (P (Function.update g q v, y) ∧ read (Function.update g q v, y) = some q) ↔
        (P (g, y) ∧ read (g, y) = some q)) :
    Pr[ fun hy => P hy ∧ ∃ q : A, read hy = some q ∧ hy.1 q = c |
        (do
          let h ← ($ᵗ (A → B))
          let y ← side
          pure (h, y)) ]
      ≤ Pr[ fun hy => P hy |
          (do
            let h ← ($ᵗ (A → B))
            let y ← side
            pure (h, y)) ] / (Fintype.card B : ℝ≥0∞) := by
  classical
  let sampleH : ProbComp (A → B) := ($ᵗ (A → B))
  let Q : (A → B) × Γ → Prop :=
    fun hy => P hy ∧ ∃ q : A, read hy = some q ∧ hy.1 q = c
  have hswapQ :
      Pr[ Q |
          (do
            let h ← sampleH
            let y ← side
            pure (h, y)) ]
        =
      Pr[ Q |
          (do
            let y ← side
            let h ← sampleH
            pure (h, y)) ] := by
    exact probEvent_bind_bind_swap sampleH side (fun h y => pure (h, y)) Q
  have hswapP :
      Pr[ P |
          (do
            let h ← sampleH
            let y ← side
            pure (h, y)) ]
        =
      Pr[ P |
          (do
            let y ← side
            let h ← sampleH
            pure (h, y)) ] := by
    exact probEvent_bind_bind_swap sampleH side (fun h y => pure (h, y)) P
  change Pr[ Q |
      (do
        let h ← sampleH
        let y ← side
        pure (h, y)) ]
    ≤ Pr[ P |
      (do
        let h ← sampleH
        let y ← side
        pure (h, y)) ] / (Fintype.card B : ℝ≥0∞)
  rw [hswapQ, hswapP]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  calc
    ∑' y : Γ, Pr[= y | side] *
        Pr[ Q | sampleH >>= fun h => pure (h, y)]
        ≤
      ∑' y : Γ, Pr[= y | side] *
        (Pr[ fun h => P (h, y) | sampleH] / (Fintype.card B : ℝ≥0∞)) := by
        apply ENNReal.tsum_le_tsum
        intro y
        apply mul_le_mul' le_rfl
        rw [probEvent_bind_pure_pair sampleH y Q]
        exact probEvent_uniformFn_freshOptionalCoord_le
          (P := fun h => P (h, y)) (read := fun h => read (h, y)) (c := c)
          (by
            intro g q v
            exact hinv y g q v)
    _ = (∑' y : Γ, Pr[= y | side] * Pr[ fun h => P (h, y) | sampleH]) /
          (Fintype.card B : ℝ≥0∞) := by
        calc
          ∑' y : Γ, Pr[= y | side] *
              (Pr[ fun h => P (h, y) | sampleH] / (Fintype.card B : ℝ≥0∞))
              =
            ∑' y : Γ, (Pr[= y | side] * Pr[ fun h => P (h, y) | sampleH]) *
              (Fintype.card B : ℝ≥0∞)⁻¹ := by
              apply tsum_congr
              intro y
              rw [div_eq_mul_inv]
              ac_rfl
          _ = (∑' y : Γ, Pr[= y | side] * Pr[ fun h => P (h, y) | sampleH]) *
                (Fintype.card B : ℝ≥0∞)⁻¹ := by
              rw [ENNReal.tsum_mul_right]
          _ = (∑' y : Γ, Pr[= y | side] * Pr[ fun h => P (h, y) | sampleH]) /
                (Fintype.card B : ℝ≥0∞) := by
              rw [div_eq_mul_inv]
    _ = (∑' y : Γ, Pr[= y | side] *
          Pr[ P | sampleH >>= fun h => pure (h, y)]) /
          (Fintype.card B : ℝ≥0∞) := by
        congr 1
        apply tsum_congr
        intro y
        rw [probEvent_bind_pure_pair sampleH y P]

end BadEventDS

end DuplexSpongeFS
