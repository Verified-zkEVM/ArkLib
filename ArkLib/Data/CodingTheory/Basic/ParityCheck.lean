/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Codes cut out by parity checks

The code `pcCode m H` of `m` parity checks `H : Fin m → Module.Dual F (ι → F)`, and counts of
parity-check tuples over a finite field.

## Main statements

* `CodingTheory.card_pc_contains`: `#{H | V ≤ pcCode m H} = q^{m (n - dim V)}`.
* `CodingTheory.finrank_pcCode`: independent parity checks cut out a code of dimension `n - m`.
* `CodingTheory.card_fiber_pcCode`: every `(n - m)`-dimensional code has the same number of
  independent parity-check tuples.
* `CodingTheory.card_linIndep_ge`: at least half of all parity-check tuples are independent.
* `CodingTheory.ncard_subspace_le_of_pc`: the fraction of `k`-dimensional codes with a property is
  at most twice the fraction of parity-check tuples whose code has it.
-/

@[expose] public section

namespace CodingTheory

/-- The code cut out by `m` parity checks. -/
def pcCode {ι F : Type*} [Field F] (m : ℕ) (H : Fin m → Module.Dual F (ι → F)) :
    Submodule F (ι → F) :=
  ⨅ i, LinearMap.ker (H i)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem pcCode_eq_dualCoannihilator (m : ℕ) (H : Fin m → Module.Dual F (ι → F)) :
    pcCode m H = (Submodule.span F (Set.range H)).dualCoannihilator := by
  ext x
  have : x ∈ (Submodule.span F (Set.range H)).dualCoannihilator ↔ ∀ i, H i x = 0 := by
    rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
    simp
  rw [this, pcCode, Submodule.mem_iInf]
  simp [LinearMap.mem_ker]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem le_pcCode_iff (m : ℕ) (V : Submodule F (ι → F))
    (H : Fin m → Module.Dual F (ι → F)) :
    V ≤ pcCode m H ↔ ∀ i, H i ∈ V.dualAnnihilator := by
  refine ⟨fun h i => ?_, fun h x hx => ?_⟩
  · rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have := h hx
    simp only [pcCode, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this i
  · simp only [pcCode, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun i => (Submodule.mem_dualAnnihilator _).1 (h i) x hx

omit [DecidableEq ι] [DecidableEq F] in
/-- `#{H | V ≤ C(H)} = q^{m (n - dim V)}`. -/
theorem card_pc_contains (m : ℕ) (V : Submodule F (ι → F)) :
    Nat.card {H : Fin m → Module.Dual F (ι → F) // V ≤ pcCode m H} =
      Fintype.card F ^ (m * (Fintype.card ι - Module.finrank F V)) := by
  have e : {H : Fin m → Module.Dual F (ι → F) // V ≤ pcCode m H} ≃
      (Fin m → V.dualAnnihilator) :=
    (Equiv.subtypeEquivRight (fun H => le_pcCode_iff m V H)).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Module.natCard_eq_pow_finrank (K := F) (V := V.dualAnnihilator),
    Nat.card_eq_fintype_card (α := F), ← pow_mul, mul_comm]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq V
  rw [Module.finrank_fintype_fun_eq_card] at h
  congr 2
  omega

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Linearly independent parity checks cut out a code of dimension `n - m`. -/
theorem finrank_pcCode {m : ℕ} (H : Fin m → Module.Dual F (ι → F)) (hH : LinearIndependent F H) :
    Module.finrank F (pcCode m H) + m = Fintype.card ι := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span F (Set.range H))
  rw [finrank_span_eq_card hH, Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
  rw [pcCode_eq_dualCoannihilator]
  omega

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem linearIndependent_subtype_coe_iff {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V)
    {m : ℕ} (s : Fin m → W) :
    LinearIndependent F s ↔ LinearIndependent F (fun i => (s i : V)) :=
  (LinearMap.linearIndependent_iff W.subtype (Submodule.ker_subtype _)).symm

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem pcCode_eq_of_dualAnnihilator [Finite ι] {m : ℕ} (C : Submodule F (ι → F))
    (hW : Module.finrank F C.dualAnnihilator = m)
    (s : {s : Fin m → C.dualAnnihilator // LinearIndependent F s}) :
    LinearIndependent F (fun i => (s.1 i : Module.Dual F (ι → F))) ∧
      pcCode m (fun i => (s.1 i : Module.Dual F (ι → F))) = C := by
  have hli : LinearIndependent F (fun i => (s.1 i : Module.Dual F (ι → F))) :=
    (linearIndependent_subtype_coe_iff C.dualAnnihilator s.1).1 s.2
  have := Fintype.ofFinite ι
  refine ⟨hli, ?_⟩
  have hle : Submodule.span F (Set.range fun i => (s.1 i : Module.Dual F (ι → F))) ≤
      C.dualAnnihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (s.1 i).2
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [finrank_span_eq_card hli, Fintype.card_fin, hW])
  rw [pcCode_eq_dualCoannihilator, heq, Subspace.dualAnnihilator_dualCoannihilator_eq]

omit [DecidableEq ι] [DecidableEq F] in
/-- Every `(n-m)`-dimensional code has the same number of independent parity-check tuples. -/
theorem card_fiber_pcCode (m : ℕ) (C : Submodule F (ι → F))
    (hC : Module.finrank F C + m = Fintype.card ι) :
    Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧ pcCode m H = C} =
      ∏ i : Fin m, (Fintype.card F ^ m - Fintype.card F ^ (i : ℕ)) := by
  have hW : Module.finrank F C.dualAnnihilator = m := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq C
    rw [Module.finrank_fintype_fun_eq_card] at h
    omega
  let e : {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧ pcCode m H = C} ≃
      {s : Fin m → C.dualAnnihilator // LinearIndependent F s} :=
    { toFun := fun H => ⟨fun i => ⟨H.1 i, (le_pcCode_iff m C H.1).1 H.2.2.ge i⟩,
        (linearIndependent_subtype_coe_iff C.dualAnnihilator _).2 H.2.1⟩
      invFun := fun s =>
        ⟨fun i => (s.1 i : Module.Dual F (ι → F)), pcCode_eq_of_dualAnnihilator C hW s⟩
      left_inv := fun H => rfl
      right_inv := fun s => rfl }
  have : Finite C.dualAnnihilator := Module.finite_of_finite F
  rw [Nat.card_congr e, card_linearIndependent (K := F) (V := C.dualAnnihilator) hW.ge, hW]

private theorem pow_mul_le_prod_range (q n : ℕ) (hq : 1 ≤ q) (j : ℕ) (hj : j ≤ n) :
    ((q : ℝ) ^ n) ^ j * (((q : ℝ) - 1) * (q : ℝ) ^ n - ((q : ℝ) ^ j - 1)) ≤
      (∏ i ∈ Finset.range j, ((q ^ n - q ^ i : ℕ) : ℝ)) * (((q : ℝ) - 1) * (q : ℝ) ^ n) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hle : q ^ j ≤ q ^ n := Nat.pow_le_pow_right hq (by omega)
    have hsub : (((q ^ n - q ^ j : ℕ)) : ℝ) = (q : ℝ) ^ n - (q : ℝ) ^ j := by
      rw [Nat.cast_sub hle]; push_cast; rfl
    rw [Finset.prod_range_succ, hsub]
    have h0 : (0 : ℝ) ≤ (q : ℝ) ^ n - (q : ℝ) ^ j := by
      have : ((q ^ j : ℕ) : ℝ) ≤ ((q ^ n : ℕ) : ℝ) := by exact_mod_cast hle
      push_cast at this; linarith
    have h1 : (0 : ℝ) ≤ (q : ℝ) ^ j * ((q : ℝ) ^ j - 1) :=
      mul_nonneg (by positivity) (by linarith [one_le_pow₀ (n := j) hq'])
    have := mul_le_mul_of_nonneg_left ih h0
    rw [pow_succ, pow_succ]
    have h2 := mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ n) j) h1
    nlinarith [this, h2]

omit [DecidableEq ι] [DecidableEq F] in
/-- At least half of all parity-check tuples are linearly independent when `k ≥ 1`. -/
theorem card_linIndep_ge (k m : ℕ) (hk : 1 ≤ k) (hkm : k + m = Fintype.card ι) :
    Fintype.card F ^ (Fintype.card ι * m) ≤
      2 * Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H} := by
  have hfin : Finite (Module.Dual F (ι → F)) := Module.finite_of_finite F
  have hrank : Module.finrank F (Module.Dual F (ι → F)) = Fintype.card ι := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [card_linearIndependent (K := F) (V := Module.Dual F (ι → F)) (by omega), hrank,
    Fin.prod_univ_eq_prod_range (fun i => Fintype.card F ^ Fintype.card ι - Fintype.card F ^ i) m]
  set q := Fintype.card F with hqdef
  set n := Fintype.card ι with hn
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have key := pow_mul_le_prod_range q n (by omega) m (by omega)
  have ht : (2 : ℝ) * (q : ℝ) ^ m ≤ ((q : ℝ) - 1) * (q : ℝ) ^ n := by
    have hqk : (q : ℝ) ^ n = (q : ℝ) ^ k * (q : ℝ) ^ m := by rw [← pow_add]; congr 1; omega
    have hk : (q : ℝ) ≤ (q : ℝ) ^ k := by
      simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q) hk
    have htpos : (0 : ℝ) < (q : ℝ) ^ m := by positivity
    rw [hqk]
    have h2 : (2 : ℝ) ≤ ((q : ℝ) - 1) * (q : ℝ) ^ k := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 htpos.le]
  have hpos : (0 : ℝ) < ((q : ℝ) - 1) * (q : ℝ) ^ n := by
    have : (0 : ℝ) < (q : ℝ) ^ n := by positivity
    nlinarith
  have ha : (0 : ℝ) ≤ ((q : ℝ) ^ n) ^ m := by positivity
  set P : ℝ := ∏ i ∈ Finset.range m, ((q ^ n - q ^ i : ℕ) : ℝ) with hP
  have hmain : ((q : ℝ) ^ n) ^ m ≤ 2 * P := by
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [mul_nonneg ha (sub_nonneg.2 ht)]
  have : ((q ^ (n * m) : ℕ) : ℝ) ≤ ((2 * ∏ i ∈ Finset.range m, (q ^ n - q ^ i) : ℕ) : ℝ) := by
    push_cast
    rw [← pow_mul] at hmain
    exact hmain
  exact_mod_cast this

omit [DecidableEq ι] [DecidableEq F] in
private theorem card_linIndep_pc_eq (Q : Submodule F (ι → F) → Prop) (k m : ℕ)
    (hkm : k + m = Fintype.card ι) :
    Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧ Q (pcCode m H)} =
      (∏ i : Fin m, (Fintype.card F ^ m - Fintype.card F ^ (i : ℕ))) *
        Nat.card {C : Submodule F (ι → F) // Module.finrank F C = k ∧ Q C} := by
  have hfinS : Finite (Submodule F (ι → F)) :=
    Finite.of_injective (fun C : Submodule F (ι → F) => (C : Set (ι → F)))
      SetLike.coe_injective
  have hfin : Finite (Module.Dual F (ι → F)) := Module.finite_of_finite F
  let f : {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧ Q (pcCode m H)} →
      {C : Submodule F (ι → F) // Module.finrank F C = k ∧ Q C} := fun H =>
    ⟨pcCode m H.1, by have := finrank_pcCode H.1 H.2.1; omega, H.2.2⟩
  have hfib : ∀ c : {C : Submodule F (ι → F) // Module.finrank F C = k ∧ Q C},
      Nat.card {a // f a = c} =
        ∏ i : Fin m, (Fintype.card F ^ m - Fintype.card F ^ (i : ℕ)) := by
    intro c
    rw [← card_fiber_pcCode m c.1 (by have := c.2.1; omega)]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2.1, congrArg Subtype.val a.2⟩
        invFun := fun H => ⟨⟨H.1, H.2.1, by rw [H.2.2]; exact c.2.2⟩, Subtype.ext H.2.2⟩
        left_inv := fun a => rfl
        right_inv := fun H => rfl }
  have : Fintype {C : Submodule F (ι → F) // Module.finrank F C = k ∧ Q C} :=
    Fintype.ofFinite _
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp_rw [hfib]
  simp [Nat.card_eq_fintype_card, mul_comm]

omit [DecidableEq ι] [DecidableEq F] in
/-- Transfer: the fraction of `k`-dimensional codes with property `P` is at most twice the
fraction of parity-check tuples whose code has `P`. -/
theorem ncard_subspace_le_of_pc (P : Submodule F (ι → F) → Prop) (k m : ℕ)
    (hkm : k + m = Fintype.card ι) (hk : 1 ≤ k) :
    ({C : Submodule F (ι → F) | Module.finrank F C = k ∧ P C}.ncard : ℝ) ≤
      2 * ((Nat.card {H : Fin m → Module.Dual F (ι → F) // P (pcCode m H)} : ℝ) /
          (Fintype.card F : ℝ) ^ (Fintype.card ι * m)) *
        {C : Submodule F (ι → F) | Module.finrank F C = k}.ncard := by
  have hfinS : Finite (Submodule F (ι → F)) :=
    Finite.of_injective (fun C : Submodule F (ι → F) => (C : Set (ι → F)))
      SetLike.coe_injective
  have hfin : Finite (Module.Dual F (ι → F)) := Module.finite_of_finite F
  set g := ∏ i : Fin m, (Fintype.card F ^ m - Fintype.card F ^ (i : ℕ)) with hg
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hgpos : 0 < g := by
    refine Finset.prod_pos fun i _ => Nat.sub_pos_of_lt ?_
    exact Nat.pow_lt_pow_right hq2 i.2
  have h1 := card_linIndep_pc_eq P k m hkm
  have h2 := card_linIndep_pc_eq (ι := ι) (F := F) (fun _ => True) k m hkm
  have h3 := card_linIndep_ge (ι := ι) (F := F) k m hk hkm
  have h4 : Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧
      P (pcCode m H)} ≤ Nat.card {H : Fin m → Module.Dual F (ι → F) // P (pcCode m H)} :=
    Nat.card_le_card_of_injective (fun H => ⟨H.1, H.2.2⟩) fun a b h =>
      Subtype.ext (Subtype.mk.inj h)
  have h2' : Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H} =
      g * {C : Submodule F (ι → F) | Module.finrank F C = k}.ncard := by
    rw [← Nat.card_coe_set_eq]
    simp only [and_true] at h2
    exact h2
  have h1' : Nat.card {H : Fin m → Module.Dual F (ι → F) // LinearIndependent F H ∧
      P (pcCode m H)} = g * {C : Submodule F (ι → F) | Module.finrank F C = k ∧ P C}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h1
  rw [h2'] at h3
  rw [h1'] at h4
  set A := {C : Submodule F (ι → F) | Module.finrank F C = k ∧ P C}.ncard
  set S := {C : Submodule F (ι → F) | Module.finrank F C = k}.ncard
  set N := Nat.card {H : Fin m → Module.Dual F (ι → F) // P (pcCode m H)}
  have hQ : (0 : ℝ) < (Fintype.card F : ℝ) ^ (Fintype.card ι * m) := by positivity
  have h5 : ((A : ℝ) * (Fintype.card F : ℝ) ^ (Fintype.card ι * m)) ≤ 2 * N * S := by
    have h3' : (Fintype.card F : ℝ) ^ (Fintype.card ι * m) ≤ 2 * (g * S) := by exact_mod_cast h3
    have h4' : (g : ℝ) * A ≤ N := by exact_mod_cast h4
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3' hA, mul_le_mul_of_nonneg_left h4'
      (Nat.cast_nonneg S : (0 : ℝ) ≤ S)]
  have : 2 * ((N : ℝ) / (Fintype.card F : ℝ) ^ (Fintype.card ι * m)) * S =
      2 * N * S / (Fintype.card F : ℝ) ^ (Fintype.card ι * m) := by ring
  rw [this, le_div_iff₀ hQ]
  exact h5

end CodingTheory
