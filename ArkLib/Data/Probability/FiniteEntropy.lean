/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Shannon entropy of finite weights

Real weights on a finite type, the law of a random variable under a weight, its base-`q` Shannon
entropy, and product weights.

## Main definitions

* `Probability.IsProb`: a probability weight on a finite type.
* `Probability.law`, `Probability.entQ`: the law and the base-`q` entropy of a random variable.
* `Probability.prodLaw`: the product weight on `I → A`.

## Main statements

* `Probability.entQ_comp_le`: data processing, `H(f ∘ X) ≤ H(X)`.
* `Probability.entQ_submodular`: `H(X, Y, Z) + H(Z) ≤ H(X, Z) + H(Y, Z)`.
* `Probability.entQ_pair_le`: subadditivity.
* `Probability.entQ_peel`: entropy of `(Y₁, V + ψ Z)` when `Y₁` is a function of `Z` and `V` is
  independent of `Z`.
* `Probability.entQ_pushforward_close`: uniform continuity of the entropy of push-forwards, with a
  modulus independent of the spaces.
* `Probability.entQ_le_of_law_zero`: a Fano-type bound for a variable that is zero with high
  probability.
* `Probability.entQ_pair_eq_add_of_disjoint`: under a product weight, entropy is additive on
  variables that depend on disjoint sets of coordinates.

The weights are real-valued, so `law`, `entQ` and `prodLaw` are noncomputable.
-/

@[expose] public section

namespace Probability

variable {Ω : Type*} [Fintype Ω]

/-- A probability weight on a finite type. -/
def IsProb (μ : Ω → ℝ) : Prop := (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1

/-- The law (push-forward weight) of `X` under `μ`. -/
noncomputable def law {β : Type*} [DecidableEq β] (μ : Ω → ℝ) (X : Ω → β) (b : β) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => X ω = b), μ ω

/-- Base-`q` Shannon entropy of `X` under `μ`. -/
noncomputable def entQ (q : ℕ) {β : Type*} [Fintype β] [DecidableEq β]
    (μ : Ω → ℝ) (X : Ω → β) : ℝ :=
  (∑ b, Real.negMulLog (law μ X b)) / Real.log q

/-- The product weight on `I → A`. -/
noncomputable def prodLaw {I A : Type*} [Fintype I] (b : I → A → ℝ) : (I → A) → ℝ :=
  fun ω => ∏ i, b i (ω i)

section Entropy

variable {μ : Ω → ℝ} {q : ℕ}
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

omit [Fintype β] in
/-- Laws of a probability weight are nonnegative. -/
theorem law_nonneg (hμ : IsProb μ) (X : Ω → β) (b : β) : 0 ≤ law μ X b :=
  Finset.sum_nonneg fun ω _ => hμ.1 ω

/-- A law sums to one. -/
theorem sum_law (hμ : IsProb μ) (X : Ω → β) : ∑ b, law μ X b = 1 := by
  rw [← hμ.2]
  exact Finset.sum_fiberwise Finset.univ X μ

omit [Fintype β] in
private theorem law_le_one [Finite β] (hμ : IsProb μ) (X : Ω → β) (b : β) :
    law μ X b ≤ 1 := by
  cases nonempty_fintype β
  rw [← sum_law hμ X]
  exact Finset.single_le_sum (f := law μ X) (fun c _ => law_nonneg hμ X c) (Finset.mem_univ b)

private theorem log_cast_pos (hq : 1 < q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast hq)

/-- Entropy is nonnegative. -/
theorem entQ_nonneg (hμ : IsProb μ) (hq : 1 < q) (X : Ω → β) : 0 ≤ entQ q μ X :=
  div_nonneg (Finset.sum_nonneg fun b _ =>
    Real.negMulLog_nonneg (law_nonneg hμ X b) (law_le_one hμ X b)) (log_cast_pos hq).le

/-- The law of `g ∘ T` is the push-forward of the law of `T`. -/
theorem law_comp {δ ε : Type*} [Fintype δ] [DecidableEq δ] [DecidableEq ε]
    (T : Ω → δ) (g : δ → ε) (e : ε) :
    law μ (g ∘ T) e = ∑ d ∈ Finset.univ.filter (fun d => g d = e), law μ T d := by
  unfold law
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter fun ω => (g ∘ T) ω = e)
    (t := Finset.univ.filter fun d => g d = e) (g := T)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hd, h⟩
  · intro ω hω
    simpa using hω

private theorem sum_law_mul_comp {δ ε : Type*} [Fintype δ] [DecidableEq δ] [Fintype ε]
    [DecidableEq ε] (T : Ω → δ) (g : δ → ε) (φ : ε → ℝ) :
    ∑ d, law μ T d * φ (g d) = ∑ e, law μ (g ∘ T) e * φ e := by
  calc ∑ d, law μ T d * φ (g d)
      = ∑ e, ∑ d ∈ Finset.univ.filter (fun d => g d = e), law μ T d * φ (g d) :=
        (Finset.sum_fiberwise Finset.univ g _).symm
    _ = ∑ e, law μ (g ∘ T) e * φ e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [law_comp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [hd]

private theorem law_le_law_comp {δ ε : Type*} [Finite δ] [DecidableEq δ] [DecidableEq ε]
    (hμ : IsProb μ) (T : Ω → δ) (g : δ → ε) (d : δ) :
    law μ T d ≤ law μ (g ∘ T) (g d) := by
  cases nonempty_fintype δ
  rw [law_comp]
  exact Finset.single_le_sum (f := law μ T) (fun c _ => law_nonneg hμ T c)
    (by simp : d ∈ Finset.univ.filter fun d' => g d' = g d)

private theorem sum_negMulLog_law_comp {δ ε : Type*} [Fintype δ] [DecidableEq δ] [Fintype ε]
    [DecidableEq ε] (T : Ω → δ) (g : δ → ε) :
    ∑ e, Real.negMulLog (law μ (g ∘ T) e) =
      ∑ d, law μ T d * -Real.log (law μ (g ∘ T) (g d)) := by
  rw [sum_law_mul_comp T g (fun e => -Real.log (law μ (g ∘ T) e))]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Real.negMulLog]

private theorem mul_neg_log_le_mul_neg_log {p P : ℝ} (h0 : 0 ≤ p) (h : p ≤ P) :
    p * -Real.log P ≤ p * -Real.log p := by
  rcases h0.eq_or_lt with rfl | hp
  · simp
  · exact mul_le_mul_of_nonneg_left (neg_le_neg (Real.log_le_log hp h)) h0

private theorem sum_negMulLog_law_comp_le {δ ε : Type*} [Fintype δ] [DecidableEq δ] [Fintype ε]
    [DecidableEq ε] (hμ : IsProb μ) (T : Ω → δ) (g : δ → ε) :
    ∑ e, Real.negMulLog (law μ (g ∘ T) e) ≤ ∑ d, Real.negMulLog (law μ T d) := by
  rw [sum_negMulLog_law_comp]
  refine Finset.sum_le_sum fun d _ => ?_
  have := mul_neg_log_le_mul_neg_log (law_nonneg hμ T d) (law_le_law_comp hμ T g d)
  simpa [Real.negMulLog] using this

/-- Data processing: `H(f ∘ X) ≤ H(X)`. -/
theorem entQ_comp_le (hμ : IsProb μ) (hq : 1 < q) (X : Ω → β) (f : β → γ) :
    entQ q μ (f ∘ X) ≤ entQ q μ X :=
  div_le_div_of_nonneg_right (sum_negMulLog_law_comp_le hμ X f) (log_cast_pos hq).le

/-- Entropy is invariant under maps injective on the range. -/
theorem entQ_eq_of_inverse (hμ : IsProb μ) (hq : 1 < q) (X : Ω → β) (f : β → γ) (g : γ → β)
    (hX : ∀ ω, g (f (X ω)) = X ω) : entQ q μ (f ∘ X) = entQ q μ X := by
  refine le_antisymm (entQ_comp_le hμ hq X f) ?_
  have h : X = g ∘ (f ∘ X) := funext fun ω => (hX ω).symm
  calc entQ q μ X = entQ q μ (g ∘ (f ∘ X)) := by rw [← h]
    _ ≤ entQ q μ (f ∘ X) := entQ_comp_le hμ hq _ g

private theorem sum_law_prod_mk {δ : Type*} [Finite δ] [DecidableEq δ]
    (T' : Ω → α × δ) (z : δ) : ∑ x, law μ T' (x, z) = law μ (Prod.snd ∘ T') z := by
  cases nonempty_fintype δ
  have := sum_law_mul_comp (μ := μ) T' Prod.snd (fun z' => if z' = z then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  rw [Fintype.sum_prod_type] at this
  simpa [Finset.sum_ite_eq'] using this

private theorem sub_mul_div_le_mul_log {p a b c : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) (hpb : p ≤ b)
    (hpc : p ≤ c) :
    p - a * b / c ≤ p * (Real.log p + Real.log c - Real.log a - Real.log b) := by
  rcases hp.eq_or_lt with rfl | hp'
  · have ha : 0 ≤ a := hpa
    have hb : 0 ≤ b := hpb
    have hc : 0 ≤ c := hpc
    simpa using div_nonneg (mul_nonneg ha hb) hc
  · have ha : 0 < a := hp'.trans_le hpa
    have hb : 0 < b := hp'.trans_le hpb
    have hc : 0 < c := hp'.trans_le hpc
    have hx := Real.log_le_sub_one_of_pos (x := a * b / (p * c)) (by positivity)
    have hlog : Real.log (a * b / (p * c)) =
        Real.log a + Real.log b - Real.log p - Real.log c := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha.ne' hb.ne',
        Real.log_mul hp'.ne' hc.ne']
      ring
    have h2 : p * (a * b / (p * c)) = a * b / c := by field_simp
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - a * b / (p * c) ≤
      -Real.log (a * b / (p * c))) hp'.le
    rw [hlog] at this
    nlinarith [this, h2]

private theorem sum_negMulLog_submodular (hμ : IsProb μ) (T : Ω → α × β × γ) :
    ∑ d, Real.negMulLog (law μ T d) +
        ∑ z, Real.negMulLog (law μ ((fun t : α × β × γ => t.2.2) ∘ T) z) ≤
      ∑ e, Real.negMulLog (law μ ((fun t : α × β × γ => (t.1, t.2.2)) ∘ T) e) +
        ∑ e, Real.negMulLog (law μ ((fun t : α × β × γ => (t.2.1, t.2.2)) ∘ T) e) := by
  set g1 : α × β × γ → α × γ := fun t => (t.1, t.2.2) with hg1
  set g2 : α × β × γ → β × γ := fun t => (t.2.1, t.2.2) with hg2
  set g3 : α × β × γ → γ := fun t => t.2.2 with hg3
  set a := law μ (g1 ∘ T) with ha
  set b := law μ (g2 ∘ T) with hb
  set c := law μ (g3 ∘ T) with hc
  set p := law μ T with hp
  rw [sum_negMulLog_law_comp T g1, sum_negMulLog_law_comp T g2,
    sum_negMulLog_law_comp T g3]
  have hmA : ∀ z, ∑ x, a (x, z) = c z := fun z => sum_law_prod_mk (g1 ∘ T) z
  have hmB : ∀ z, ∑ y, b (y, z) = c z := fun z => sum_law_prod_mk (g2 ∘ T) z
  have hsum : ∑ d : α × β × γ, a (g1 d) * b (g2 d) / c (g3 d) ≤ 1 := by
    have e1 : ∑ d : α × β × γ, a (g1 d) * b (g2 d) / c (g3 d) =
        ∑ x, ∑ y, ∑ z, a (x, z) * b (y, z) / c z := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl
    have e2 : ∑ x, ∑ y, ∑ z, a (x, z) * b (y, z) / c z =
        ∑ z, ∑ x, ∑ y, a (x, z) * b (y, z) / c z := by
      rw [Finset.sum_congr rfl fun x _ =>
        Finset.sum_comm (f := fun y z => a (x, z) * b (y, z) / c z)]
      exact Finset.sum_comm
    have e3 : ∀ z, ∑ x, ∑ y, a (x, z) * b (y, z) / c z ≤ c z := by
      intro z
      have : ∑ x, ∑ y, a (x, z) * b (y, z) / c z = (∑ x, a (x, z)) * (∑ y, b (y, z)) / c z := by
        rw [Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_div]
      rw [this, hmA z, hmB z]
      have hc0 : 0 ≤ c z := law_nonneg hμ _ _
      rcases hc0.eq_or_lt with h | h
      · rw [← h]; simp
      · rw [mul_div_cancel_right₀ _ h.ne']
    rw [e1, e2]
    calc _ ≤ ∑ z, c z := Finset.sum_le_sum fun z _ => e3 z
      _ = 1 := sum_law hμ _
  have hone : ∑ d, p d = 1 := sum_law hμ T
  suffices h : 0 ≤ ∑ d, (p d * -Real.log (a (g1 d)) + p d * -Real.log (b (g2 d)) -
      (p d * -Real.log (p d) + p d * -Real.log (c (g3 d)))) by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    have hT : ∑ d, Real.negMulLog (p d) = ∑ d, p d * -Real.log (p d) :=
      Finset.sum_congr rfl fun d _ => by simp [Real.negMulLog]
    rw [hT]
    linarith
  calc (0 : ℝ) ≤ ∑ d, (p d - a (g1 d) * b (g2 d) / c (g3 d)) := by
        rw [Finset.sum_sub_distrib, hone]; linarith
    _ ≤ _ := Finset.sum_le_sum fun d _ => by
        have := sub_mul_div_le_mul_log (law_nonneg hμ T d) (law_le_law_comp hμ T g1 d)
          (law_le_law_comp hμ T g2 d) (law_le_law_comp hμ T g3 d)
        linarith

/-- Submodularity: `H(X,Y,Z) + H(Z) ≤ H(X,Z) + H(Y,Z)`. -/
theorem entQ_submodular (hμ : IsProb μ) (hq : 1 < q) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    entQ q μ (fun ω => (X ω, Y ω, Z ω)) + entQ q μ Z ≤
      entQ q μ (fun ω => (X ω, Z ω)) + entQ q μ (fun ω => (Y ω, Z ω)) := by
  unfold entQ
  rw [← add_div, ← add_div]
  exact div_le_div_of_nonneg_right (sum_negMulLog_submodular hμ fun ω => (X ω, Y ω, Z ω))
    (log_cast_pos hq).le

private theorem entQ_unit (hμ : IsProb μ) (q : ℕ) : entQ q μ (fun _ : Ω => ()) = 0 := by
  have h := sum_law hμ (fun _ : Ω => ())
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  simp [entQ, h]

/-- Subadditivity: `H(X,Y) ≤ H(X) + H(Y)`. -/
theorem entQ_pair_le (hμ : IsProb μ) (hq : 1 < q) (X : Ω → α) (Y : Ω → β) :
    entQ q μ (fun ω => (X ω, Y ω)) ≤ entQ q μ X + entQ q μ Y := by
  have h := entQ_submodular hμ hq X Y (fun _ : Ω => ())
  have e1 : entQ q μ (fun ω => (X ω, Y ω, ())) = entQ q μ (fun ω => (X ω, Y ω)) :=
    entQ_eq_of_inverse hμ hq (fun ω => (X ω, Y ω)) (fun p => (p.1, p.2, ()))
      (fun t => (t.1, t.2.1)) fun ω => rfl
  have e2 : entQ q μ (fun ω => (X ω, ())) = entQ q μ X :=
    entQ_eq_of_inverse hμ hq X (fun a => (a, ())) Prod.fst fun ω => rfl
  have e3 : entQ q μ (fun ω => (Y ω, ())) = entQ q μ Y :=
    entQ_eq_of_inverse hμ hq Y (fun a => (a, ())) Prod.fst fun ω => rfl
  rw [e1, e2, e3, entQ_unit hμ] at h
  linarith

/-- Peeling: if `Y₁` is a function of `Z` and `V` is independent of `Z`, then
`H(Y₁) + H(V) ≤ H(Y₁, V + ψ Z)`. -/
theorem entQ_peel [AddCommGroup β] (hμ : IsProb μ) (hq : 1 < q) (Y₁ : Ω → α) (V : Ω → β)
    (Z : Ω → γ) (φ : γ → α) (ψ : γ → β) (hY : ∀ ω, Y₁ ω = φ (Z ω))
    (hind : entQ q μ (fun ω => (V ω, Z ω)) = entQ q μ V + entQ q μ Z) :
    entQ q μ Y₁ + entQ q μ V ≤ entQ q μ (fun ω => (Y₁ ω, V ω + ψ (Z ω))) := by
  obtain rfl : Y₁ = fun ω => φ (Z ω) := funext hY
  have h := entQ_submodular hμ hq (fun ω => V ω + ψ (Z ω)) Z fun ω => φ (Z ω)
  have e1 : entQ q μ (fun ω => (V ω + ψ (Z ω), Z ω, φ (Z ω))) = entQ q μ (fun ω => (V ω, Z ω)) :=
    entQ_eq_of_inverse hμ hq (fun ω => (V ω, Z ω)) (fun p => (p.1 + ψ p.2, p.2, φ p.2))
      (fun t => (t.1 - ψ t.2.1, t.2.1)) fun ω => by simp
  have e2 : entQ q μ (fun ω => (Z ω, φ (Z ω))) = entQ q μ Z :=
    entQ_eq_of_inverse hμ hq Z (fun z => (z, φ z)) Prod.fst fun ω => rfl
  have e3 : entQ q μ (fun ω => (φ (Z ω), V ω + ψ (Z ω))) =
      entQ q μ (fun ω => (V ω + ψ (Z ω), φ (Z ω))) :=
    entQ_eq_of_inverse hμ hq (fun ω => (V ω + ψ (Z ω), φ (Z ω))) Prod.swap Prod.swap
      fun ω => rfl
  rw [e1, e2, hind] at h
  rw [e3]
  linarith

/-- Conditional entropy is at most the entropy of the error of any estimator. -/
theorem entQ_cond_le_err {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]
    (hμ : IsProb μ) (hq : 1 < q) (A : Ω → F) (Y : Ω → β) (f : β → F) :
    entQ q μ (fun ω => (A ω, Y ω)) - entQ q μ Y ≤ entQ q μ (fun ω => A ω - f (Y ω)) := by
  have e1 : entQ q μ (fun ω => (A ω - f (Y ω), Y ω)) = entQ q μ (fun ω => (A ω, Y ω)) :=
    entQ_eq_of_inverse hμ hq (fun ω => (A ω, Y ω)) (fun p => (p.1 - f p.2, p.2))
      (fun t => (t.1 + f t.2, t.2)) fun ω => by simp
  have e2 := entQ_pair_le hμ hq (fun ω => A ω - f (Y ω)) Y
  linarith

private theorem negMulLog_le_negMulLog {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ Real.exp (-1)) : Real.negMulLog x ≤ Real.negMulLog y := by
  have := Real.mul_log_strictAntiOn.antitoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
  simp only [Real.negMulLog]
  linarith

/-- Fano-type bound: a variable that is `0` with probability `≥ 1 - t` has small entropy. -/
theorem entQ_le_of_law_zero {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]
    (hμ : IsProb μ) (hF : Fintype.card F = q) (E : Ω → F) (t : ℝ) (ht : t ≤ Real.exp (-1))
    (h0 : 1 - t ≤ law μ E 0) :
    entQ q μ E ≤ (t + ((q : ℝ) - 1) * Real.negMulLog t) / Real.log q := by
  have hq1 : 1 ≤ q := hF ▸ Fintype.card_pos
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  refine div_le_div_of_nonneg_right ?_ hlog
  have hs := sum_law hμ E
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))] at hs
  have hp1 : law μ E 0 ≤ 1 := law_le_one hμ E 0
  have ht0 : 0 ≤ t := by linarith
  have hz : Real.negMulLog (law μ E 0) ≤ t :=
    (Real.negMulLog_le_one_sub_self (law_nonneg hμ E 0)).trans (by linarith)
  have hr : ∑ a ∈ Finset.univ.erase (0 : F), Real.negMulLog (law μ E a) ≤
      ∑ a ∈ Finset.univ.erase (0 : F), Real.negMulLog t := by
    refine Finset.sum_le_sum fun a ha => ?_
    have : law μ E a ≤ ∑ a ∈ Finset.univ.erase (0 : F), law μ E a :=
      Finset.single_le_sum (f := law μ E) (fun c _ => law_nonneg hμ E c) ha
    exact negMulLog_le_negMulLog (law_nonneg hμ E a) (by linarith) ht
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hF,
    nsmul_eq_mul, Nat.cast_sub hq1] at hr
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  push_cast at hr
  linarith

/-- Uniform continuity of entropy of push-forwards, with a modulus independent of the spaces. -/
theorem entQ_pushforward_close (η : ℝ) (hη : 0 < η) :
    ∃ θ > 0, ∀ {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] (μ ν : Ω → ℝ),
      IsProb μ → IsProb ν → ∀ f : Ω → β, (∀ ω, |μ ω - ν ω| ≤ θ / Fintype.card Ω) →
        |∑ b, Real.negMulLog (law μ f b) - ∑ b, Real.negMulLog (law ν f b)| ≤
          Fintype.card β * η := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous
    Real.continuous_negMulLog.continuousOn
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  refine ⟨d / 2, by positivity, fun {Ω β} _ _ _ μ ν hμ hν f hclose => ?_⟩
  classical
  have hΩ : 0 < Fintype.card Ω := by
    rw [Fintype.card_pos_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    have := hμ.2
    simp at this
  have hΩR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hΩ
  have hmem : ∀ (ρ : Ω → ℝ), IsProb ρ → ∀ b, law ρ f b ∈ Set.Icc (0 : ℝ) 1 := by
    intro ρ hρ b
    refine ⟨Finset.sum_nonneg fun ω _ => hρ.1 ω, ?_⟩
    rw [← hρ.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun ω _ _ => hρ.1 ω
  have hlaw : ∀ b, |law μ f b - law ν f b| ≤ d / 2 := by
    intro b
    unfold law
    rw [← Finset.sum_sub_distrib]
    calc |∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), (μ ω - ν ω)|
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), |μ ω - ν ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), (d / 2) / Fintype.card Ω :=
          Finset.sum_le_sum fun ω _ => hclose ω
      _ ≤ ∑ ω : Ω, (d / 2) / Fintype.card Ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = d / 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
  rw [← Finset.sum_sub_distrib]
  calc |∑ b, (Real.negMulLog (law μ f b) - Real.negMulLog (law ν f b))|
      ≤ ∑ b, |Real.negMulLog (law μ f b) - Real.negMulLog (law ν f b)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : β, η := Finset.sum_le_sum fun b _ => by
        have := hdist _ (hmem μ hμ b) _ (hmem ν hν b)
          (by rw [Real.dist_eq]; linarith [hlaw b])
        rw [Real.dist_eq] at this
        exact this.le
    _ = Fintype.card β * η := by simp

end Entropy

section ProductLaw

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
variable {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

omit [DecidableEq A] in
private theorem sum_prodLaw_mul_eq_split (b : I → A → ℝ) (p : I → Prop) [DecidablePred p]
    (h : (I → A) → ℝ) :
    ∑ ω, prodLaw b ω * h ω = ∑ x : ({i // p i} → A) × ({i // ¬p i} → A),
      ((∏ i : {i // p i}, b i (x.1 i)) * ∏ i : {i // ¬p i}, b i (x.2 i)) *
        h ((Equiv.piEquivPiSubtypeProd p fun _ => A).symm x) := by
  rw [← (Equiv.piEquivPiSubtypeProd p fun _ => A).symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [prodLaw, ← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]

omit [DecidableEq A] in
private theorem sum_prodLaw_mul_mul_of_disjoint (b : I → A → ℝ) (hb : ∀ i, IsProb (b i))
    {f g : (I → A) → ℝ} {P Q : Set I} (hPQ : Disjoint P Q) (hf : DependsOn f P)
    (hg : DependsOn g Q) :
    ∑ ω, prodLaw b ω * (f ω * g ω) =
      (∑ ω, prodLaw b ω * f ω) * ∑ ω, prodLaw b ω * g ω := by
  classical
  rcases isEmpty_or_nonempty (I → A) with hE | ⟨⟨ω0⟩⟩
  · simp
  set e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ P) fun _ : I => A with he
  set f' : ({i // i ∈ P} → A) → ℝ := fun u => f (e.symm (u, (e ω0).2)) with hf'
  set g' : ({i // ¬ i ∈ P} → A) → ℝ := fun v => g (e.symm ((e ω0).1, v)) with hg'
  have hf1 : ∀ u v, f (e.symm (u, v)) = f' u := fun u v =>
    hf fun i hi => by simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hg1 : ∀ u v, g (e.symm (u, v)) = g' v := fun u v =>
    hg fun i hi => by
      have : i ∉ P := Set.disjoint_right.1 hPQ hi
      simp [he, Equiv.piEquivPiSubtypeProd_symm_apply, this]
  rw [sum_prodLaw_mul_eq_split b (· ∈ P), sum_prodLaw_mul_eq_split b (· ∈ P) f,
    sum_prodLaw_mul_eq_split b (· ∈ P) g]
  simp only [Fintype.sum_prod_type, ← he, hf1, hg1]
  have hQ : ∑ v : {i // ¬ i ∈ P} → A, ∏ i : {i // ¬ i ∈ P}, b i (v i) = 1 := by
    rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun i _ => (hb i).2
  have hP : ∑ u : {i // i ∈ P} → A, ∏ i : {i // i ∈ P}, b i (u i) = 1 := by
    rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun i _ => (hb i).2
  have h1 : ∀ u : {i // i ∈ P} → A, ∑ v : {i // ¬ i ∈ P} → A,
      ((∏ i : {i // i ∈ P}, b i (u i)) * ∏ i : {i // ¬ i ∈ P}, b i (v i)) * f' u =
      (∏ i : {i // i ∈ P}, b i (u i)) * f' u := fun u => by
    rw [← mul_one ((∏ i : {i // i ∈ P}, b i (u i)) * f' u), ← hQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∀ u : {i // i ∈ P} → A, ∑ v : {i // ¬ i ∈ P} → A,
      ((∏ i : {i // i ∈ P}, b i (u i)) * ∏ i : {i // ¬ i ∈ P}, b i (v i)) * g' v =
      (∏ i : {i // i ∈ P}, b i (u i)) * ∑ v : {i // ¬ i ∈ P} → A,
        (∏ i : {i // ¬ i ∈ P}, b i (v i)) * g' v := fun u => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  simp only [h1, h2]
  rw [← Finset.sum_mul, hP, one_mul, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

omit [DecidableEq A] in
private theorem law_eq_sum_mul_ite {Ω : Type*} [Fintype Ω] {β : Type*} [DecidableEq β] (μ : Ω → ℝ)
    (Y : Ω → β) (y : β) : law μ Y y = ∑ ω, μ ω * if Y ω = y then 1 else 0 := by
  simp [law, Finset.sum_filter]

omit [DecidableEq I] [DecidableEq A] in
/-- A product of probability weights is nonnegative. -/
theorem prodLaw_nonneg (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (ω : I → A) :
    0 ≤ prodLaw b ω :=
  Finset.prod_nonneg fun i _ => (hb i).1 _

omit [DecidableEq A] in
/-- A product of probability weights is a probability weight. -/
theorem isProb_prodLaw (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) : IsProb (prodLaw b) := by
  refine ⟨prodLaw_nonneg b hb, ?_⟩
  simp only [prodLaw, ← Fintype.prod_sum, (hb _).2, Finset.prod_const_one]

omit [DecidableEq A] [Fintype β] [Fintype γ] in
/-- Variables depending on disjoint coordinate sets are independent under a product weight. -/
theorem law_pair_eq_mul_of_disjoint (b : I → A → ℝ) (hb : ∀ i, IsProb (b i))
    {X : (I → A) → β} {Z : (I → A) → γ} {P Q : Set I} (hX : DependsOn X P)
    (hZ : DependsOn Z Q) (hPQ : Disjoint P Q) (x : β) (z : γ) :
    law (prodLaw b) (fun ω => (X ω, Z ω)) (x, z) = law (prodLaw b) X x * law (prodLaw b) Z z := by
  simp only [law_eq_sum_mul_ite]
  rw [← sum_prodLaw_mul_mul_of_disjoint b hb hPQ (f := fun ω => if X ω = x then 1 else 0)
    (g := fun ω => if Z ω = z then 1 else 0)
    (fun u v h => by simp [hX h]) (fun u v h => by simp [hZ h])]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h1 : X ω = x <;> by_cases h2 : Z ω = z <;> simp [h1, h2]

omit [DecidableEq A] in
/-- Entropy is additive on variables depending on disjoint coordinate sets. -/
theorem entQ_pair_eq_add_of_disjoint (q : ℕ) (b : I → A → ℝ) (hb : ∀ i, IsProb (b i))
    {X : (I → A) → β} {Z : (I → A) → γ} {P Q : Set I} (hX : DependsOn X P)
    (hZ : DependsOn Z Q) (hPQ : Disjoint P Q) :
    entQ q (prodLaw b) (fun ω => (X ω, Z ω)) =
      entQ q (prodLaw b) X + entQ q (prodLaw b) Z := by
  have hμ := isProb_prodLaw b hb
  have hX1 := sum_law hμ X
  have hZ1 := sum_law hμ Z
  have : ∑ p : β × γ, Real.negMulLog (law (prodLaw b) (fun ω => (X ω, Z ω)) p) =
      ∑ x, Real.negMulLog (law (prodLaw b) X x) +
        ∑ z, Real.negMulLog (law (prodLaw b) Z z) := by
    rw [Fintype.sum_prod_type]
    simp only [law_pair_eq_mul_of_disjoint b hb hX hZ hPQ, Real.negMulLog_mul]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hX1, hZ1]
    simp
  rw [entQ, entQ, entQ, this, add_div]

/-- The law of a coordinate under a product weight is its factor. -/
theorem law_coord (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (i : I) (a : A) :
    law (prodLaw b) (fun ω => ω i) a = b i a := by
  have h : ∑ ω ∈ Fintype.piFinset (fun j => if j = i then {a} else (Finset.univ : Finset A)),
      prodLaw b ω = ∏ j, ∑ x ∈ if j = i then {a} else Finset.univ, b j x :=
    (Finset.prod_univ_sum _ fun j x => b j x).symm
  have hs : Fintype.piFinset (fun j => if j = i then {a} else (Finset.univ : Finset A)) =
      Finset.univ.filter (fun ω : I → A => ω i = a) := by
    ext ω
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hω; simpa using hω i
    · intro hω j
      by_cases hj : j = i
      · subst hj; simp [hω]
      · simp [hj]
  rw [law, ← hs, h, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj, (hb j).2]
  · simp

end ProductLaw

end Probability
