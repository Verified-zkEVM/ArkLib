/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.Chernoff

/-!
# Entropy of a Bernoulli vector shifted by one symbol

Let `v ∼ Ber_q(p)^J` and `α ∼ Ber_q(p')` be independent, with `p ≤ p' ≤ 1 - 1/q`, and let
`w_i ≠ 0` for `i ∈ J`. This file proves that `H_q((v_i + w_i α)_{i ∈ J}) ≥ |J| (h + h/(L + δ'))`
with `h = H_q(p)`, for every `|J| ≤ L` once `L` is large. [GLMRSW22], Section 4, proves this
lemma for the proof of their Theorem 4.1.

## Main statements

* `CodingTheory.RandomLinearInternal.entQ_add_mul_ber_ge_pstar`: the bound `(|J| - 1) h +
  H_q(pstar)`. It is used for small `|J|`.
* `CodingTheory.RandomLinearInternal.entQ_add_mul_ber_ge_sub_errEnt`: the bound `|J| h + h -
  errEnt`. It is used for large `|J|`. The error term comes from the plurality decoder.
* `CodingTheory.RandomLinearInternal.entQ_add_mul_ber_lower`: the combined bound.

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

/-- The Fano error term `(t + (q-1) negMulLog t) / log q`. -/
noncomputable def errEnt (q : ℕ) (t : ℝ) : ℝ :=
  (t + ((q : ℝ) - 1) * Real.negMulLog t) / Real.log q

/-- `pstar` lies strictly above `p` and at most `1 - 1/q`. -/
theorem lt_pstar_and_pstar_le {q : ℕ} (hq : 2 ≤ q) {p p' : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q)
    (hp' : p ≤ p') (hp'1 : p' ≤ 1 - 1 / q) :
    p < pstar q p p' ∧ pstar q p p' ≤ 1 - 1 / q := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hqq : (0 : ℝ) < q := by linarith
  have hc : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by field_simp
  rw [hc] at hp1 hp'1
  have hp1' : p * q < (q : ℝ) - 1 := by
    have := (lt_div_iff₀ hqq).1 hp1; linarith
  have hp'0 : 0 < p' := lt_of_lt_of_le hp0 hp'
  have e : pstar q p p' = p + p' * (((q : ℝ) - 1 - p * q) / ((q : ℝ) - 1)) := by
    unfold pstar; field_simp; ring
  have hpos : 0 < ((q : ℝ) - 1 - p * q) / ((q : ℝ) - 1) := div_pos (by linarith) hq0
  refine ⟨?_, ?_⟩
  · rw [e]; nlinarith [mul_pos hp'0 hpos]
  · rw [e, hc, le_div_iff₀ hqq]
    have h2 : (p + p' * (((q : ℝ) - 1 - p * q) / ((q : ℝ) - 1))) * q =
        p * q + p' * q * ((q : ℝ) - 1 - p * q) / ((q : ℝ) - 1) := by
      field_simp
    have h3 : p' * q * ((q : ℝ) - 1 - p * q) / ((q : ℝ) - 1) ≤ ((q : ℝ) - 1 - p * q) := by
      rw [div_le_iff₀ hq0]
      have := (le_div_iff₀ hqq).1 hp'1
      nlinarith [(sub_pos.2 hp1')]
    rw [h2]; linarith

/-- A uniform entropy gap `H_q(pstar) ≥ H_q(p) + ε₀`. -/
theorem exists_qEntropy_pstar_gap {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q) :
    ∃ ε₀ > 0, ∀ p' ∈ Set.Icc p (1 - 1 / (q : ℝ)),
      qEntropy q p + ε₀ ≤ qEntropy q (pstar q p p') := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  obtain ⟨h1, h2⟩ := lt_pstar_and_pstar_le hq hp0 hp1 le_rfl hp1.le
  have hmono := qEntropy_strictMonoOn hq
  have hpm : p ∈ Set.Icc (0 : ℝ) (1 - 1 / q) := ⟨hp0.le, hp1.le⟩
  have hpp : pstar q p p ∈ Set.Icc (0 : ℝ) (1 - 1 / q) := ⟨by linarith, h2⟩
  refine ⟨qEntropy q (pstar q p p) - qEntropy q p, sub_pos.2 (hmono hpm hpp h1), ?_⟩
  intro p' hp'
  obtain ⟨h1', h2'⟩ := lt_pstar_and_pstar_le hq hp0 hp1 hp'.1 hp'.2
  have hle : pstar q p p ≤ pstar q p p' := by
    unfold pstar
    have : 0 < (q : ℝ) - 1 - p * q := by
      have hc : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by field_simp
      rw [hc, lt_div_iff₀ (by linarith)] at hp1; linarith
    have e : p * p' * q / ((q : ℝ) - 1) = p' * (p * q / (q - 1)) := by ring
    have e2 : p * p * q / ((q : ℝ) - 1) = p * (p * q / (q - 1)) := by ring
    rw [e, e2]
    have : p * q / ((q : ℝ) - 1) < 1 := by rw [div_lt_one hq0]; linarith
    nlinarith [hp'.1]
  have := hmono.monotoneOn hpp ⟨by linarith, h2'⟩ hle
  linarith

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- If `w_i ≠ 0` on `J ≠ ∅`, the coordinates `i ∈ J` are `Ber_q(p)`, `a ∉ J` is `Ber_q(p')` and the
weight is a product, then `H((ω_i + w_i ω_a)_{i ∈ J}) ≥ (|J| - 1) H_q(p) + H_q(pstar q p p')`. -/
theorem entQ_add_mul_ber_ge_pstar {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) {p p' : ℝ}
    (b : I → F → ℝ) (hb : ∀ i, IsProb (b i)) (J : Finset I) (a : I) (haJ : a ∉ J)
    (hJ : ∀ i ∈ J, b i = ber q p) (ha : b a = ber q p') (w : I → F) (hw : ∀ i ∈ J, w i ≠ 0)
    (hd : 1 ≤ J.card) :
    ((J.card : ℝ) - 1) * qEntropy q p + qEntropy q (pstar q p p') ≤
      entQ q (prodLaw b) (fun ω (i : J) => ω i + w i * ω a) := by
  have hq1 : 1 < q := by omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 hd
  have hbp := isProb_prodLaw b hb
  have hia : i₀ ≠ a := fun h => haJ (h ▸ hi₀)
  let J' := J.erase i₀
  let Z : (I → F) → F × F := fun ω => (ω i₀, ω a)
  let V : (I → F) → (J' → F) := fun ω i => ω i
  let ψ : F × F → (J' → F) := fun z i => w i * z.2
  let φ : F × F → F := fun z => z.1 + w i₀ * z.2
  let Y₁ : (I → F) → F := fun ω => ω i₀ + w i₀ * ω a
  have hind : entQ q (prodLaw b) (fun ω => (V ω, Z ω)) =
      entQ q (prodLaw b) V + entQ q (prodLaw b) Z := by
    refine entQ_pair_eq_add_of_disjoint q b hb (P := (J' : Set I)) (Q := {i₀, a}) ?_ ?_ ?_
    · intro x y hxy
      exact funext fun i => hxy i i.2
    · intro x y hxy
      exact Prod.ext (hxy i₀ (by simp)) (hxy a (by simp))
    · rw [Set.disjoint_left]
      intro i hi hi2
      have hi' : i ∈ J' := hi
      rcases hi2 with rfl | rfl
      · simp [J'] at hi'
      · exact haJ (Finset.mem_of_mem_erase hi')
  have key := entQ_peel (q := q) (μ := prodLaw b) hbp hq1 Y₁ V Z φ ψ (fun ω => rfl) hind
  have hY1 : entQ q (prodLaw b) Y₁ = qEntropy q (pstar q p p') := by
    obtain ⟨l0, l1⟩ := law_add_smul_ber hF p p' b hb hia (hJ i₀ hi₀) ha (hw i₀ hi₀)
    exact entQ_ber_shape hF Y₁ _ l0 l1
  have hV : entQ q (prodLaw b) V = ((J.card : ℝ) - 1) * qEntropy q p := by
    have := entQ_ber_block hF p b hb J' (fun i hi => hJ i (Finset.mem_of_mem_erase hi))
    have hc : (J'.card : ℝ) = (J.card : ℝ) - 1 := by
      simp only [J', Finset.card_erase_of_mem hi₀]
      rw [Nat.cast_sub hd]; simp
    rw [← hc]; exact this
  let f : (J → F) → F × (J' → F) := fun y =>
    (y ⟨i₀, hi₀⟩, fun i => y ⟨i, Finset.mem_of_mem_erase i.2⟩)
  let g : F × (J' → F) → (J → F) := fun u i =>
    if h : (i : I) = i₀ then u.1 else u.2 ⟨i, Finset.mem_erase.2 ⟨h, i.2⟩⟩
  have hinv := entQ_eq_of_inverse (q := q) hbp hq1
    (fun ω (i : J) => ω i + w i * ω a) f g (by
      intro ω
      funext i
      by_cases h : (i : I) = i₀
      · have : i = ⟨i₀, hi₀⟩ := Subtype.ext h
        subst this
        simp [g, f]
      · simp [g, f, h])
  have hfeq : (f ∘ fun ω (i : J) => ω i + w i * ω a) =
      fun ω => (Y₁ ω, V ω + ψ (Z ω)) := rfl
  rw [hfeq] at hinv
  linarith

/-- Under the hypotheses of `entQ_add_mul_ber_ge_pstar` with `p ≤ p' ≤ 1 - 1/q`,
`H((ω_i + w_i ω_a)_{i ∈ J}) ≥ |J| H_q(p) + H_q(p) - errEnt q t` for `t = q e^{-|J| κ}`. -/
theorem entQ_add_mul_ber_ge_sub_errEnt {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) {p p' : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1 - 1 / q) (hp' : p ≤ p') (hp'1 : p' ≤ 1 - 1 / q)
    (b : I → F → ℝ) (hb : ∀ i, IsProb (b i)) (J : Finset I) (a : I) (haJ : a ∉ J)
    (hJ : ∀ i ∈ J, b i = ber q p) (ha : b a = ber q p') (w : I → F) (hw : ∀ i ∈ J, w i ≠ 0)
    (ht : (q : ℝ) * Real.exp (-(J.card * kappa q p)) ≤ Real.exp (-1)) :
    (J.card : ℝ) * qEntropy q p + qEntropy q p -
        errEnt q ((q : ℝ) * Real.exp (-(J.card * kappa q p))) ≤
      entQ q (prodLaw b) (fun ω (i : J) => ω i + w i * ω a) := by
  have hq1 : 1 < q := by omega
  have hbp := isProb_prodLaw b hb
  let t : ℝ := (q : ℝ) * Real.exp (-(J.card * kappa q p))
  let α : (I → F) → F := fun ω => ω a
  let Y : (I → F) → (J → F) := fun ω i => ω i + w i * ω a
  let v : (I → F) → (J → F) := fun ω i => ω i
  have h1 := entQ_cond_le_err (q := q) (μ := prodLaw b) hbp hq1 α Y (plurality J w)
  have h2 : entQ q (prodLaw b) (fun ω => (α ω, Y ω)) =
      entQ q (prodLaw b) (fun ω => (v ω, α ω)) := by
    have := entQ_eq_of_inverse (q := q) hbp hq1 (fun ω => (v ω, α ω))
      (fun x => (x.2, fun i => x.1 i + w i * x.2))
      (fun y => (fun i => y.2 i - w i * y.1, y.1)) (by intro ω; simp [v, α])
    exact this
  have h3 : entQ q (prodLaw b) (fun ω => (v ω, α ω)) =
      entQ q (prodLaw b) v + entQ q (prodLaw b) α := by
    refine entQ_pair_eq_add_of_disjoint q b hb (P := (J : Set I)) (Q := {a}) ?_ ?_ ?_
    · intro x y hxy
      exact funext fun i => hxy i i.2
    · intro x y hxy
      exact hxy a (by simp)
    · rw [Set.disjoint_left]
      intro i hi hi2
      rw [Set.mem_singleton_iff] at hi2
      exact haJ (hi2 ▸ hi)
  have h4 : entQ q (prodLaw b) v = J.card * qEntropy q p :=
    entQ_ber_block hF p b hb J hJ
  have h5 : entQ q (prodLaw b) α = qEntropy q p' := by
    refine entQ_ber_shape hF α p' ?_ ?_
    · have := law_coord b hb a 0
      simp only [α]; rw [this, ha]; simp [ber]
    · intro c hc
      have := law_coord b hb a c
      simp only [α]; rw [this, ha]; simp [ber, hc]
  have h6 : qEntropy q p ≤ qEntropy q p' := by
    have hmono := qEntropy_strictMonoOn hq
    exact hmono.monotoneOn ⟨hp0.le, hp1.le⟩ ⟨by linarith, hp'1⟩ hp'
  have h7 : entQ q (prodLaw b) (fun ω => α ω - plurality J w (Y ω)) ≤ errEnt q t := by
    refine entQ_le_of_law_zero hbp hF _ t ht ?_
    have herr := law_plurality_err_le hF hp0 hp1 b hb J a hJ w hw
    have hsum := hbp.2
    unfold law
    rw [Finset.sum_filter]
    have : ∑ ω, prodLaw b ω *
        (if plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a then (1 : ℝ) else 0) =
        ∑ ω, (prodLaw b ω - if α ω - plurality J w (Y ω) = 0 then prodLaw b ω else 0) := by
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases h : plurality J w (Y ω) = ω a
      · have h0 : α ω - plurality J w (Y ω) = 0 := by simp [α, h]
        have h' : plurality J w (fun i : J => ω i + w i * ω a) = ω a := h
        simp [h0, h']
      · have h0 : ¬ (α ω - plurality J w (Y ω) = 0) := by
          intro h'; exact h (sub_eq_zero.1 h').symm
        have h' : plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a := h
        simp [h0, h']
    rw [this, Finset.sum_sub_distrib, hsum] at herr
    linarith
  linarith

private theorem tendsto_pow_mul_exp_neg_mul {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => x ^ n * Real.exp (-(x * κ))) Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (Filter.tendsto_id.atTop_mul_const hκ)
  have h2 := h.const_mul ((κ ^ n)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp, id, mul_pow]
  field_simp

private theorem exists_errEnt_tail {q : ℕ} (hq : 2 ≤ q) {κ c h δ' : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hδ' : 0 < δ') (hh : 0 < h) :
    ∃ D : ℝ, ∀ x : ℝ, D ≤ x →
      (q : ℝ) * Real.exp (-(x * κ)) ≤ Real.exp (-1) ∧
      0 ≤ errEnt q ((q : ℝ) * Real.exp (-(x * κ))) ∧
      errEnt q ((q : ℝ) * Real.exp (-(x * κ))) * (x / c + δ') ≤ h * δ' := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log q := Real.log_pos hq1
  let G : ℝ → ℝ := fun x =>
    ((q : ℝ) / Real.log q) *
      ((x / c + δ') * (1 + ((q : ℝ) - 1) * (x * κ)) * Real.exp (-(x * κ)))
  have e0 := tendsto_pow_mul_exp_neg_mul hκ 0
  have e1 := tendsto_pow_mul_exp_neg_mul hκ 1
  have e2 := tendsto_pow_mul_exp_neg_mul hκ 2
  set K : ℝ := (q : ℝ) / Real.log q with hK
  have hGeq : G = fun x => (K * δ') * (x ^ 0 * Real.exp (-(x * κ))) +
      (K * (1 / c + δ' * (((q : ℝ) - 1) * κ))) * (x ^ 1 * Real.exp (-(x * κ))) +
      (K * (((q : ℝ) - 1) * κ / c)) * (x ^ 2 * Real.exp (-(x * κ))) := by
    funext x; simp only [G]; ring
  have hG : Filter.Tendsto G Filter.atTop (nhds 0) := by
    rw [hGeq]
    simpa using ((e0.const_mul (K * δ')).add (e1.const_mul _)).add (e2.const_mul _)
  have ev1 := hG.eventually (gt_mem_nhds (mul_pos hh hδ'))
  have ev2 : ∀ᶠ x : ℝ in Filter.atTop,
      (q : ℝ) * Real.exp (-(x * κ)) ≤ Real.exp (-1) := by
    have := (e0.const_mul (q : ℝ))
    simp only [pow_zero, one_mul, mul_zero] at this
    exact this.eventually (ge_mem_nhds (Real.exp_pos _))
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.1 (ev1.and (ev2.and (Filter.eventually_ge_atTop 0)))
  refine ⟨D, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hD x hx
  have hexp : 0 < Real.exp (-(x * κ)) := Real.exp_pos _
  have ht0 : 0 < (q : ℝ) * Real.exp (-(x * κ)) := by positivity
  have ht1 : (q : ℝ) * Real.exp (-(x * κ)) ≤ 1 :=
    h2.trans (Real.exp_le_one_iff.2 (by norm_num))
  refine ⟨h2, ?_, ?_⟩
  · unfold errEnt
    have := Real.negMulLog_nonneg ht0.le ht1
    have : 0 ≤ (q : ℝ) - 1 := by linarith
    positivity
  · have hneg : Real.negMulLog ((q : ℝ) * Real.exp (-(x * κ))) ≤
        ((q : ℝ) * Real.exp (-(x * κ))) * (x * κ) := by
      simp only [Real.negMulLog]
      rw [Real.log_mul (by positivity) hexp.ne', Real.log_exp]
      nlinarith [mul_nonneg ht0.le hlog.le]
    have hE : errEnt q ((q : ℝ) * Real.exp (-(x * κ))) ≤
        (((q : ℝ) * Real.exp (-(x * κ))) +
          ((q : ℝ) - 1) * (((q : ℝ) * Real.exp (-(x * κ))) * (x * κ))) / Real.log q := by
      unfold errEnt
      gcongr
    have hpos : 0 ≤ x / c + δ' := by positivity
    calc errEnt q ((q : ℝ) * Real.exp (-(x * κ))) * (x / c + δ')
        ≤ ((((q : ℝ) * Real.exp (-(x * κ))) +
          ((q : ℝ) - 1) * (((q : ℝ) * Real.exp (-(x * κ))) * (x * κ))) / Real.log q) *
            (x / c + δ') := by gcongr
      _ = G x := by simp only [G]; field_simp
      _ ≤ h * δ' := h1.le

/-- Let the coordinates in `J` be `Ber_q(p)`, let `a ∉ J` be `Ber_q(p')` with
`p ≤ p' ≤ 1 - 1/q`, and let `w ≠ 0` on `J`. For every `δ' > 0` there is `L₀` such that
`H((ω_i + w_i ω_a)_{i ∈ J}) ≥ |J| (H_q(p) + H_q(p)/(L + δ'))` for all `L ≥ L₀` and `|J| ≤ L`. -/
theorem entQ_add_mul_ber_lower (q : ℕ) (hq : 2 ≤ q) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 - 1 / q)
    (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F],
      Fintype.card F = q → ∀ b : I → F → ℝ, (∀ i, IsProb (b i)) →
      ∀ (J : Finset I) (a : I), a ∉ J → (∀ i ∈ J, b i = ber q p) →
      (∃ p', p ≤ p' ∧ p' ≤ 1 - 1 / q ∧ b a = ber q p') → J.card ≤ L →
      ∀ w : I → F, (∀ i ∈ J, w i ≠ 0) →
        (J.card : ℝ) * (qEntropy q p + qEntropy q p / ((L : ℝ) + δ')) ≤
          entQ q (prodLaw b) (fun ω (i : J) => ω i + w i * ω a) := by
  have hq1 : 1 < q := by omega
  have hqr : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hh : 0 < qEntropy q p := qEntropy_pos hq hp0 (by linarith)
  obtain ⟨ε₀, hε₀, hgap⟩ := exists_qEntropy_pstar_gap hq hp0 hp1
  have hκ := kappa_pos hq hp0 hp1
  obtain ⟨D, hD⟩ := exists_errEnt_tail hq hκ (c := ε₀ / qEntropy q p) (h := qEntropy q p)
    (div_pos hε₀ hh) hδ' hh
  refine ⟨⌈D * qEntropy q p / ε₀⌉₊ + 1, fun L hL => ?_⟩
  intro I F _ _ _ _ _ hF b hb J a haJ hJ hp'' hJL w hw
  obtain ⟨p', hp', hp'1, ha⟩ := hp''
  set h := qEntropy q p with hhdef
  have hbp := isProb_prodLaw b hb
  have hLr : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hdL : (J.card : ℝ) ≤ L := by exact_mod_cast hJL
  by_cases hd0 : J.card = 0
  · rw [hd0]
    simpa using entQ_nonneg (q := q) (isProb_prodLaw b hb) hq1
      (fun ω (i : J) => ω i + w i * ω a)
  have hd : 1 ≤ J.card := Nat.pos_of_ne_zero hd0
  have hd1 : (1 : ℝ) ≤ J.card := by exact_mod_cast hd
  have hLpos : 0 < (L : ℝ) + δ' := by linarith
  by_cases hs : (J.card : ℝ) ≤ ε₀ / h * L
  · have hsm := entQ_add_mul_ber_ge_pstar hq hF b hb J a haJ hJ ha w hw hd
    have hg := hgap p' ⟨hp', hp'1⟩
    have h1 : (J.card : ℝ) * h ≤ ε₀ * ((L : ℝ) + δ') := by
      have : (J.card : ℝ) * h ≤ ε₀ / h * L * h := by gcongr
      have e : ε₀ / h * L * h = ε₀ * L := by field_simp
      nlinarith
    have h2 : (J.card : ℝ) * (h / ((L : ℝ) + δ')) ≤ ε₀ := by
      rw [← mul_div_assoc, div_le_iff₀ hLpos]; linarith
    nlinarith
  · replace hs := not_le.1 hs
    have hLge : (⌈D * h / ε₀⌉₊ : ℝ) ≤ L := by
      have : ((⌈D * h / ε₀⌉₊ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hL
      push_cast at this; linarith
    have hDL : D ≤ J.card := by
      have h1 : D * h / ε₀ ≤ L := (Nat.le_ceil _).trans hLge
      rw [div_le_iff₀ hε₀] at h1
      have h2 : D ≤ ε₀ / h * L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hh]; linarith
      linarith
    obtain ⟨ht, hE0, hE⟩ := hD _ hDL
    have hlg := entQ_add_mul_ber_ge_sub_errEnt hq hF hp0 hp1 hp' hp'1 b hb J a haJ hJ ha w hw ht
    have hLd : (L : ℝ) < J.card / (ε₀ / h) := by
      rw [lt_div_iff₀ (div_pos hε₀ hh)]; linarith
    have hE' : errEnt q ((q : ℝ) * Real.exp (-(J.card * kappa q p))) * ((L : ℝ) + δ') ≤
        h * δ' := by
      refine le_trans ?_ hE
      gcongr
    have h6 : qEntropy q p ≤ qEntropy q p' := by
      have hmono := qEntropy_strictMonoOn hq
      exact hmono.monotoneOn ⟨hp0.le, hp1.le⟩ ⟨by linarith, hp'1⟩ hp'
    have key : (J.card : ℝ) * h / ((L : ℝ) + δ') ≤
        h - errEnt q ((q : ℝ) * Real.exp (-(J.card * kappa q p))) := by
      rw [div_le_iff₀ hLpos]
      nlinarith [mul_le_mul_of_nonneg_left hdL hh.le]
    have : (J.card : ℝ) * (h + h / ((L : ℝ) + δ')) =
        J.card * h + (J.card : ℝ) * h / ((L : ℝ) + δ') := by ring
    linarith

end CodingTheory.RandomLinearInternal
