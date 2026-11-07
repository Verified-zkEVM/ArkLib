/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.Entropy

/-!
# Product weights

Product weights on `I → A` and the entropy of `q`-ary Bernoulli coordinates.

## Main statements

* `CodingTheory.RandomLinearInternal.entQ_pair_eq_add_of_disjoint`: under a product weight, the
  entropy is additive on variables that depend on disjoint sets of coordinates.
* `CodingTheory.RandomLinearInternal.entQ_ber_block`: `d` independent `Ber_q(p)` coordinates have
  entropy `d · H_q(p)`.
* `CodingTheory.RandomLinearInternal.law_add_smul_ber`: if `w ≠ 0`, then `Ber_q(p) + w · Ber_q(p')`
  is `Ber_q(pstar q p p')`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

omit [DecidableEq A] [Fintype A] in
private theorem sum_piFinset_prodLaw (b : I → A → ℝ) (t : I → Finset A) :
    ∑ ω ∈ Fintype.piFinset t, prodLaw b ω = ∏ i, ∑ a ∈ t i, b i a :=
  (Finset.prod_univ_sum t fun i a => b i a).symm

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
private theorem sum_prod_subtype_eq_one (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (p : I → Prop)
    [DecidablePred p] :
    ∑ u : {i // p i} → A, ∏ i : {i // p i}, b i (u i) = 1 := by
  have := Finset.prod_univ_sum (fun _ : {i // p i} => (Finset.univ : Finset A))
    fun (i : {i // p i}) a => b i a
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  exact Finset.prod_eq_one fun i _ => (hb i).2

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
  have hQ := sum_prod_subtype_eq_one b hb (fun i => ¬ i ∈ P)
  have hP := sum_prod_subtype_eq_one b hb (fun i => i ∈ P)
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
private theorem law_eq_sum_mul_ite {Ω : Type} [Fintype Ω] {β : Type} [DecidableEq β] (μ : Ω → ℝ)
    (Y : Ω → β) (y : β) : law μ Y y = ∑ ω, μ ω * if Y ω = y then 1 else 0 := by
  simp [law, Finset.sum_filter]

omit [DecidableEq A] in
/-- A product of probability weights is a probability weight. -/
theorem isProb_prodLaw (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) : IsProb (prodLaw b) := by
  refine ⟨fun ω => Finset.prod_nonneg fun i _ => (hb i).1 _, ?_⟩
  have := sum_piFinset_prodLaw b (fun _ => Finset.univ)
  simpa [Fintype.piFinset_univ, (hb _).2] using this

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
  have h := sum_piFinset_prodLaw b (fun j => if j = i then {a} else Finset.univ)
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

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}

/-- `Ber_q(t)` sums to one over a field with `q` elements. -/
theorem sum_ber (hq : 2 ≤ q) (hF : Fintype.card F = q) (t : ℝ) : ∑ a : F, ber q t a = 1 := by
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  have : ∑ a ∈ Finset.univ.erase (0 : F), ber q t a =
      q * (t / ((q : ℝ) - 1)) - t / ((q : ℝ) - 1) := by
    rw [Finset.sum_congr rfl (fun a ha => (by simp [ber, Finset.ne_of_mem_erase ha] :
      ber q t a = t / ((q : ℝ) - 1))),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hF,
      nsmul_eq_mul, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [this]
  have e : ((q : ℝ) - 1) * (t / ((q : ℝ) - 1)) = t := by field_simp
  simp only [ber, ite_true]
  linarith

/-- `Ber_q(t)` is a probability weight for `t ∈ [0, 1]`. -/
theorem isProb_ber (hq : 2 ≤ q) (hF : Fintype.card F = q) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsProb (ber q t : F → ℝ) := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  refine ⟨fun a => ?_, sum_ber hq hF t⟩
  unfold ber
  split_ifs
  · linarith
  · positivity

/-- A `Ber_q(t)`-shaped law has entropy `H_q(t)`. -/
theorem entQ_ber_shape {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} (hF : Fintype.card F = q)
    (X : Ω → F) (t : ℝ) (h0 : law μ X 0 = 1 - t)
    (h1 : ∀ a ≠ 0, law μ X a = t / ((q : ℝ) - 1)) : entQ q μ X = qEntropy q t := by
  have hq1 : (1 : ℝ) < q := by
    rw [← hF]; exact_mod_cast Fintype.one_lt_card
  have hq0 : ((q : ℝ) - 1) ≠ 0 := by linarith
  have hqn : 1 ≤ q := by exact_mod_cast hq1.le
  rw [entQ, qEntropy_eq_logb_form]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), h0,
    Finset.sum_congr rfl (fun a ha => by rw [h1 a (Finset.ne_of_mem_erase ha)])]
  have hc : (Finset.univ.erase (0 : F)).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hF]
  rw [Finset.sum_const, hc, nsmul_eq_mul, Nat.cast_sub hqn, Nat.cast_one]
  simp only [Real.negMulLog, Real.logb]
  by_cases ht : t = 0
  · simp [ht]
  rw [Real.log_div ht hq0]
  field_simp
  ring

/-- A block of i.i.d. `Ber_q(p)` coordinates has entropy `|J| · H_q(p)`. -/
theorem entQ_ber_block (hF : Fintype.card F = q) (p : ℝ) (b : I → F → ℝ)
    (hb : ∀ i, IsProb (b i)) (J : Finset I) (hJ : ∀ i ∈ J, b i = ber q p) :
    entQ q (prodLaw b) (fun ω (i : J) => ω i) = J.card * qEntropy q p := by
  have hq1 : 1 < q := by rw [← hF]; exact Fintype.one_lt_card
  have hμ := isProb_prodLaw b hb
  induction J using Finset.induction_on with
  | empty =>
    have h1 := sum_law hμ (fun (ω : I → F) (i : (∅ : Finset I)) => ω i)
    rw [Fintype.sum_subsingleton _ default] at h1
    simp [entQ, h1]
  | insert a J ha ih =>
    have ih := ih fun i hi => hJ i (Finset.mem_insert_of_mem hi)
    have hba : b a = ber q p := hJ a (Finset.mem_insert_self a J)
    let f : F × (J → F) → (↥(insert a J : Finset I) → F) := fun x i =>
      if h : i.1 = a then x.1 else x.2 ⟨i.1, (Finset.mem_insert.1 i.2).resolve_left h⟩
    let g : (↥(insert a J : Finset I) → F) → F × (J → F) := fun w =>
      (w ⟨a, Finset.mem_insert_self a J⟩, fun i => w ⟨i, Finset.mem_insert_of_mem i.2⟩)
    have hfX : f ∘ (fun ω => (ω a, fun i : J => ω i)) =
        fun (ω : I → F) (i : ↥(insert a J : Finset I)) => ω i := by
      funext ω ⟨i, hi⟩
      by_cases h : i = a
      · subst h; simp [f]
      · simp [f, h]
    have h0 : law (prodLaw b) (fun ω : I → F => ω a) 0 = 1 - p := by
      rw [law_coord b hb, hba]; simp [ber]
    have h1 : ∀ c ≠ 0, law (prodLaw b) (fun ω : I → F => ω a) c = p / ((q : ℝ) - 1) := by
      intro c hc; rw [law_coord b hb, hba]; simp [ber, hc]
    rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, ← hfX,
      entQ_eq_of_inverse hμ hq1 _ f g (fun ω => Prod.ext (by simp [f, g]) (funext fun i => by
        have : (i : I) ≠ a := fun h => ha (h ▸ i.2)
        simp [f, g, this])),
      entQ_pair_eq_add_of_disjoint q b hb (X := fun ω => ω a)
        (Z := fun ω (i : J) => ω i) (P := {a}) (Q := (J : Set I))
        (fun x y h => h a rfl) (fun x y h => funext fun i => h i i.2)
        (Set.disjoint_singleton_left.2 (by simpa using ha)), ih,
      entQ_ber_shape hF (μ := prodLaw b) (fun ω : I → F => ω a) p h0 h1]
    ring

/-- `Ber_q(p) + w · Ber_q(p')` with `w ≠ 0` is `Ber_q(pstar q p p')`. -/
theorem law_add_smul_ber (hF : Fintype.card F = q) (p p' : ℝ) (b : I → F → ℝ)
    (hb : ∀ i, IsProb (b i)) {i a : I} (hia : i ≠ a) (hi : b i = ber q p)
    (ha : b a = ber q p') {w : F} (hw : w ≠ 0) :
    law (prodLaw b) (fun ω => ω i + w * ω a) 0 = 1 - pstar q p p' ∧
      ∀ c ≠ 0, law (prodLaw b) (fun ω => ω i + w * ω a) c = pstar q p p' / ((q : ℝ) - 1) := by
  have hq1 : (1 : ℝ) < q := by
    rw [← hF]; exact_mod_cast Fintype.one_lt_card
  have hq0 : ((q : ℝ) - 1) ≠ 0 := by linarith
  have hpair : ∀ x z, law (prodLaw b) (fun ω => (ω i, ω a)) (x, z) =
      ber q p x * ber q p' z := by
    intro x z
    rw [law_pair_eq_mul_of_disjoint b hb (X := fun ω => ω i) (Z := fun ω => ω a)
      (P := {i}) (Q := {a}) (fun x y h => h i rfl) (fun x y h => h a rfl)
      (Set.disjoint_singleton.2 hia), law_coord b hb, law_coord b hb, hi, ha]
  have hlaw : ∀ c, law (prodLaw b) (fun ω => ω i + w * ω a) c =
      ∑ z : F, ber q p (c - w * z) * ber q p' z := by
    intro c
    have := (law_comp (μ := prodLaw b) (fun ω => (ω i, ω a))
      (fun y : F × F => y.1 + w * y.2) c).trans (Finset.sum_filter _ _)
    rw [show (fun ω : I → F => ω i + w * ω a) =
      (fun y : F × F => y.1 + w * y.2) ∘ fun ω => (ω i, ω a) from rfl, this,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h2 : ∀ x : F, (x + w * z = c) ↔ (x = c - w * z) := fun x => by
      constructor
      · intro h; exact eq_sub_of_add_eq h
      · intro h; rw [h]; ring
    simp only [hpair, h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hber : ∀ (t : ℝ) (x : F), ber q t x =
      t / ((q : ℝ) - 1) + (1 - t - t / ((q : ℝ) - 1)) * if x = 0 then 1 else 0 := by
    intro t x; by_cases hx : x = 0 <;> simp [ber, hx]
  have hconv : ∀ c, ∑ z : F, ber q p (c - w * z) * ber q p' z =
      q * (p / ((q : ℝ) - 1)) * (p' / ((q : ℝ) - 1)) +
      p / ((q : ℝ) - 1) * (1 - p' - p' / ((q : ℝ) - 1)) +
      (1 - p - p / ((q : ℝ) - 1)) * (p' / ((q : ℝ) - 1)) +
      (1 - p - p / ((q : ℝ) - 1)) * (1 - p' - p' / ((q : ℝ) - 1)) *
        (if c = 0 then 1 else 0) := by
    intro c
    simp only [hber]
    have e1 : ∑ z : F, (if c - w * z = 0 then (1 : ℝ) else 0) = 1 := by
      have : ∀ z : F, (c - w * z = 0) ↔ (z = c / w) := fun z => by
        rw [sub_eq_zero, eq_div_iff hw, eq_comm, mul_comm]
      simp [this]
    have e2 : ∑ z : F, (if c - w * z = 0 then (1 : ℝ) else 0) * (if z = 0 then 1 else 0) =
        if c = 0 then 1 else 0 := by
      simp
    have e3 : ∑ z : F, (if z = 0 then (1 : ℝ) else 0) = 1 := by simp
    have key : ∀ α s α' s' : ℝ, ∑ z : F, (α + s * if c - w * z = 0 then 1 else 0) *
        (α' + s' * if z = 0 then 1 else 0) =
        q * α * α' + α * s' + s * α' + s * s' * (if c = 0 then 1 else 0) := by
      intro α s α' s'
      have : ∀ z : F, (α + s * if c - w * z = 0 then 1 else 0) *
          (α' + s' * if z = 0 then 1 else 0) = α * α' + α * s' * (if z = 0 then 1 else 0) +
          s * α' * (if c - w * z = 0 then 1 else 0) +
          s * s' * ((if c - w * z = 0 then 1 else 0) * (if z = 0 then 1 else 0)) :=
        fun z => by ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, e3, Finset.sum_const,
        Finset.card_univ, hF, nsmul_eq_mul]
      ring
    exact key _ _ _ _
  refine ⟨?_, fun c hc => ?_⟩
  · rw [hlaw, hconv]
    simp only [pstar, ite_true]
    field_simp
    ring
  · rw [hlaw, hconv]
    simp only [pstar, hc, ite_false]
    field_simp
    ring

end CodingTheory.RandomLinearInternal
