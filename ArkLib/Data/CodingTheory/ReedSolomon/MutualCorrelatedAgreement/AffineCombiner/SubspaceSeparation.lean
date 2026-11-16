/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import ArkLib.Data.FieldTheory.BinaryAddSubgroup
public import ArkLib.Data.Polynomial.SubspacePolynomial

/-!
# A lower bound for scalar combiners on additive domains

Scalar combiners keep an error of order `n / q`, even with a constant fraction of agreement loss.

The domain is an additive subgroup `D` of a field of characteristic two, of size `n = 2 ^ k ≥ 16`.

## The construction

Fix a subgroup `U ≤ D` of index `8`, with subspace polynomial `W`.

The received words are `f = W X ^ (n / 2)` and `g = W X ^ (n / 4)` on `D`.

A polynomial of degree at most `n / 4` agrees with `g` on at most `3n / 8` points.

Each index-two subgroup `H` has subspace polynomial `X ^ (n / 2) + α_H X ^ (n / 4) + R_H`.

The remainder `R_H` has degree at most `n / 8`, and `α_H` determines `H`.

The candidate `-W R_H` agrees with `f + α_H g` exactly on `U ∪ H`.

When `H` does not contain `U`, this set has `9n / 16` points.

So each of these `n - 8` subgroups gives an exceptional challenge `α_H`.

## Main statements

* `ReedSolomon.scalarMCAError_ge_of_addSubgroup`: on an additive domain of size `n = 2 ^ k ≥ 16`,
  with `d = n / 4`, `A ≤ 9n / 16` and `s < 3n / 16`, the scalar error is at least `(n - 8) / q`
  (Proposition 6.3 of [CWYZ26]).

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

/-- The coordinate space `(ZMod 2) ^ 3 × (ZMod 2) ^ (m + 1)` of a domain of size `2 ^ (m + 4)`. -/
private abbrev BinarySpace (m : ℕ) := (Fin 3 → ZMod 2) × (Fin (m + 1) → ZMod 2)

/-- The functional `x ↦ c₁ ⬝ x₁ + c₂ ⬝ x₂` on the coordinate space. -/
private def dotHom {m : ℕ} (c : BinarySpace m) : BinarySpace m →+ ZMod 2 :=
  AddMonoidHom.mk' (fun x ↦ c.1 ⬝ᵥ x.1 + c.2 ⬝ᵥ x.2) fun x y ↦ by
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]
    ring

/-- The coordinate space has `2 ^ (m + 4)` elements. -/
private theorem card_binarySpace (m : ℕ) : Nat.card (BinarySpace m) = 2 ^ (m + 4) := by
  simp [Nat.card_eq_fintype_card, ZMod.card]
  ring

/-- A nonzero `c₂` makes the pair of the first block and the functional surjective. -/
private theorem surjective_fst_prod_dotHom {m : ℕ} {c : BinarySpace m} (hc : c.2 ≠ 0) :
    Function.Surjective ((AddMonoidHom.fst _ _).prod (dotHom c)) := by
  obtain ⟨j, hj⟩ : ∃ j, c.2 j = 1 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    rw [Pi.zero_apply] at hj
    exact ⟨j, by revert hj; generalize c.2 j = a; revert a; decide⟩
  rintro ⟨u, t⟩
  refine ⟨(u, Pi.single j (t - c.1 ⬝ᵥ u)), ?_⟩
  simp [dotHom, hj]

/-- Over `ZMod 2`, a functional is determined by its kernel. -/
private theorem dotHom_ker_injective {m : ℕ} {c c' : BinarySpace m}
    (h : (dotHom c).ker = (dotHom c').ker) : c = c' := by
  have key : ∀ x, dotHom c x = dotHom c' x := by
    intro x
    have hx : x ∈ (dotHom c).ker ↔ x ∈ (dotHom c').ker := by rw [h]
    simp only [AddMonoidHom.mem_ker] at hx
    revert hx
    generalize dotHom c x = a
    generalize dotHom c' x = b
    revert a b
    decide
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
  · simpa [dotHom] using key (Pi.single i 1, 0)
  · simpa [dotHom] using key (0, Pi.single i 1)

/-- A surjective map from the coordinate space has kernel size times image size `2 ^ (m + 4)`. -/
private theorem card_ker_mul_card {m : ℕ} {K : Type*} [AddGroup K] (φ : BinarySpace m →+ K)
    (hφ : Function.Surjective φ) : Nat.card φ.ker * Nat.card K = 16 * 2 ^ m := by
  rw [AddSubgroup.card_ker_mul_card_of_surjective hφ, card_binarySpace, pow_add]
  ring

/-- The vectors with zero first block form a subgroup of index `8`. -/
private theorem card_ker_fst (m : ℕ) :
    Nat.card (AddMonoidHom.fst (Fin 3 → ZMod 2) (Fin (m + 1) → ZMod 2)).ker = 2 * 2 ^ m := by
  have h := card_ker_mul_card (m := m) (AddMonoidHom.fst _ _) Prod.fst_surjective
  rw [show Nat.card (Fin 3 → ZMod 2) = 8 by simp [Nat.card_eq_fintype_card, ZMod.card]] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8) (h.trans (by ring))

/-- A functional with `c₂ ≠ 0` has a kernel of index `2`. -/
private theorem card_ker_dotHom {m : ℕ} {c : BinarySpace m} (hc : c.2 ≠ 0) :
    Nat.card (dotHom c).ker = 8 * 2 ^ m := by
  have hs : Function.Surjective (dotHom c) := fun t ↦ by
    obtain ⟨x, hx⟩ := surjective_fst_prod_dotHom hc (0, t)
    exact ⟨x, congrArg Prod.snd hx⟩
  have h := card_ker_mul_card (dotHom c) hs
  rw [show Nat.card (ZMod 2) = 2 by simp [Nat.card_eq_fintype_card, ZMod.card]] at h
  omega

/-- A functional with `c₂ ≠ 0` cuts the first-block kernel in half. -/
private theorem card_ker_fst_inf_ker_dotHom {m : ℕ} {c : BinarySpace m} (hc : c.2 ≠ 0) :
    Nat.card ((AddMonoidHom.fst (Fin 3 → ZMod 2) (Fin (m + 1) → ZMod 2)).ker ⊓
      (dotHom c).ker : AddSubgroup (BinarySpace m)) = 2 ^ m := by
  have h := card_ker_mul_card _ (surjective_fst_prod_dotHom hc)
  rw [AddMonoidHom.ker_prod, show Nat.card ((Fin 3 → ZMod 2) × ZMod 2) = 16 by
    simp [Nat.card_eq_fintype_card, ZMod.card]] at h
  omega

/-- Two kernels of functionals meet in at least a quarter of the space. -/
private theorem card_ker_inf_ker_dotHom {m : ℕ} (c c' : BinarySpace m) :
    4 * 2 ^ m ≤ Nat.card ((dotHom c).ker ⊓ (dotHom c').ker : AddSubgroup (BinarySpace m)) := by
  have h := AddSubgroup.card_ker_mul_card_range ((dotHom c).prod (dotHom c'))
  have hr : Nat.card ((dotHom c).prod (dotHom c')).range ≤ 4 :=
    (Finite.card_subtype_le _).trans_eq (by simp [Nat.card_eq_fintype_card, ZMod.card])
  rw [AddMonoidHom.ker_prod, card_binarySpace, pow_add] at h
  have := Nat.mul_le_mul_left (Nat.card ((dotHom c).ker ⊓ (dotHom c').ker :
    AddSubgroup (BinarySpace m))) hr
  omega

/-- On an additive domain of size `n = 2 ^ k ≥ 16`, the scalar error at degree `n / 4` is large.

It is at least `(n - 8) / q` for every threshold `A ≤ 9n / 16` and loss `s < 3n / 16`. -/
theorem scalarMCAError_ge_of_addSubgroup {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    [CharP F 2] {ι : Type*} [Fintype ι] (V : AddSubgroup F) (domain : ι ↪ F)
    (hV : ∀ x, x ∈ V ↔ ∃ i, domain i = x) (h16 : 16 ≤ Fintype.card ι)
    (hpow : ∃ k, Fintype.card ι = 2 ^ k) {A s : ℕ} (hA : A ≤ 9 * Fintype.card ι / 16)
    (hs : s < 3 * Fintype.card ι / 16) :
    ((Fintype.card ι - 8 : ℕ) : ℝ) / Fintype.card F ≤
      scalarMCAError domain (Fintype.card ι / 4) A s := by
  classical
  -- Write `n = 16 N` with `N = 2 ^ m`.
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := by
    refine ⟨k - 4, ?_⟩
    by_contra hk4
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn : Fintype.card ι = 16 * 2 ^ m := by rw [hk, pow_add]; ring
  set N := 2 ^ m with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  -- Coordinates: an injective additive map `ψ` from the coordinate space onto `V`.
  have hVcard : Nat.card V = 2 ^ (3 + (m + 1)) := by
    have hbij : Function.Bijective fun i : ι ↦ (⟨domain i, (hV _).2 ⟨i, rfl⟩⟩ : V) :=
      ⟨fun i j h ↦ domain.injective (congrArg Subtype.val h), fun x ↦ by
        obtain ⟨i, hi⟩ := (hV x).1 x.2
        exact ⟨i, Subtype.ext hi⟩⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, hk]
    ring_nf
  obtain ⟨e⟩ := AddCommGroup.nonempty_addEquiv_zmod_two_prod
    (fun x : V ↦ Subtype.ext (CharTwo.add_self_eq_zero (x : F))) hVcard
  set ψ : BinarySpace m →+ F := V.subtype.comp e.symm.toAddMonoidHom
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hpt : ∀ i, ∃ x, ψ x = domain i := fun i ↦
    ⟨e ⟨domain i, (hV _).2 ⟨i, rfl⟩⟩, by simp [ψ]⟩
  choose crd hcrd using hpt
  have hcrd_bij : Function.Bijective crd := by
    refine ⟨fun i j h ↦ domain.injective (by rw [← hcrd, ← hcrd, h]), fun x ↦ ?_⟩
    obtain ⟨i, hi⟩ := (hV (ψ x)).1 (e.symm x).2
    exact ⟨i, hψinj (by rw [hcrd, hi])⟩
  have hcount : ∀ (p : BinarySpace m → Prop) [DecidablePred p],
      #{i | p (crd i)} = #{x | p x} := fun p _ ↦
    card_equiv (Equiv.ofBijective crd hcrd_bij) (by simp)
  have hsub : ∀ (K : AddSubgroup (BinarySpace m)) [DecidablePred (· ∈ K)],
      #{x | x ∈ K} = Nat.card K := fun K _ ↦ by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmem : ∀ (K : AddSubgroup (BinarySpace m)) i, domain i ∈ K.map ψ ↔ crd i ∈ K := by
    intro K i
    rw [← hcrd i, AddSubgroup.mem_map_iff_mem hψinj]
  rw [hn] at hA hs ⊢
  rw [show 16 * N / 4 = 4 * N by omega]
  replace hA : A ≤ 9 * N := by omega
  replace hs : s < 3 * N := by omega
  -- The subgroup `U` of index `8` and its subspace polynomial `W`.
  set U₀ : AddSubgroup (BinarySpace m) :=
    (AddMonoidHom.fst (Fin 3 → ZMod 2) (Fin (m + 1) → ZMod 2)).ker with hU₀
  set W : F[X] := subspacePolynomial (U₀.map ψ) with hW
  have hWdeg : W.natDegree = 2 * N := by
    rw [hW, natDegree_subspacePolynomial, AddSubgroup.card_map_of_injective hψinj, card_ker_fst]
  have hWeval : ∀ i, W.eval (domain i) = 0 ↔ crd i ∈ U₀ := fun i ↦ by
    rw [hW, eval_subspacePolynomial_eq_zero_iff, hmem]
  set f : ι → F := fun i ↦ W.eval (domain i) * domain i ^ (8 * N) with hf
  set g : ι → F := fun i ↦ W.eval (domain i) * domain i ^ (4 * N) with hg
  -- The index-two subgroup cut out by a functional `c`, and its candidate.
  set L : BinarySpace m → F[X] := fun c ↦ subspacePolynomial ((dotHom c).ker.map ψ) with hL
  set α : BinarySpace m → F := fun c ↦ (L c).coeff (4 * N)
  set R : BinarySpace m → F[X] := fun c ↦ L c - X ^ (8 * N) - C (α c) * X ^ (4 * N) with hR
  set P : BinarySpace m → F[X] := fun c ↦ -(W * R c) with hP
  have h8 : 2 ^ (m + 1 + 2) = 8 * N := by rw [hN, pow_add]; ring
  have h4 : 2 ^ (m + 1 + 1) = 4 * N := by rw [hN, pow_add]; ring
  have h2 : 2 ^ (m + 1) = 2 * N := by rw [hN, pow_add]; ring
  have hRdeg : ∀ c : BinarySpace m, c.2 ≠ 0 → (R c).degree ≤ ((2 * N : ℕ) : WithBot ℕ) := by
    intro c hc
    have := (isTwoLinearized_subspacePolynomial ((dotHom c).ker.map ψ)).degree_sub_top_two_le
      (monic_subspacePolynomial _) (v := m + 1) (by
        rw [natDegree_subspacePolynomial, AddSubgroup.card_map_of_injective hψinj,
          card_ker_dotHom hc, h8])
    rwa [h8, h4, h2] at this
  have hPdeg : ∀ c : BinarySpace m, c.2 ≠ 0 → (P c).degree ≤ ((4 * N : ℕ) : WithBot ℕ) := by
    intro c hc
    calc (P c).degree = (W * R c).degree := degree_neg _
      _ ≤ W.degree + (R c).degree := degree_mul_le _ _
      _ ≤ ((2 * N : ℕ) : WithBot ℕ) + ((2 * N : ℕ) : WithBot ℕ) :=
          add_le_add (hWdeg ▸ degree_le_natDegree) (hRdeg c hc)
      _ = ((4 * N : ℕ) : WithBot ℕ) := by rw [← Nat.cast_add]; congr 1; ring
  -- The candidate agrees with `f + α g` exactly on `U ∪ H`.
  have hkey : ∀ c i, f i + α c * g i - (P c).eval (domain i) =
      W.eval (domain i) * (L c).eval (domain i) := by
    intro c i
    simp only [hf, hg, hP, hR, eval_neg, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    ring
  have hagree : ∀ c i, i ∈ polynomialAgreementSet domain (combinedWord domain f g (C (α c))) (P c)
      ↔ crd i ∈ U₀ ∨ crd i ∈ (dotHom c).ker := by
    intro c i
    rw [mem_polynomialAgreementSet, combinedWord_C, eq_comm, ← sub_eq_zero, hkey, mul_eq_zero,
      hWeval, hL, eval_subspacePolynomial_eq_zero_iff, hmem]
  -- When `H` does not contain `U`, the agreement set has `9N` points.
  have hcard : ∀ c : BinarySpace m, c.2 ≠ 0 →
      #(polynomialAgreementSet domain (combinedWord domain f g (C (α c))) (P c)) = 9 * N := by
    intro c hc
    have hset : polynomialAgreementSet domain (combinedWord domain f g (C (α c))) (P c) =
        ({i | crd i ∈ U₀ ∨ crd i ∈ (dotHom c).ker} : Finset ι) := by
      ext i
      rw [hagree c i]
      simp
    rw [hset, hcount (fun x ↦ x ∈ U₀ ∨ x ∈ (dotHom c).ker)]
    have hu := card_union_add_card_inter ({x | x ∈ U₀} : Finset (BinarySpace m))
      {x | x ∈ (dotHom c).ker}
    have e1 : #({x | x ∈ U₀} : Finset (BinarySpace m)) = 2 * N :=
      (hsub U₀).trans (card_ker_fst m)
    have e2 : #({x | x ∈ (dotHom c).ker} : Finset (BinarySpace m)) = 8 * N :=
      (hsub _).trans (card_ker_dotHom hc)
    have e3 : #(({x | x ∈ U₀} : Finset (BinarySpace m)) ∩
        ({x | x ∈ (dotHom c).ker} : Finset (BinarySpace m))) = N := by
      rw [← filter_and]
      convert (hsub (U₀ ⊓ (dotHom c).ker)).trans (card_ker_fst_inf_ker_dotHom hc) using 2
      ext x
      simp [AddSubgroup.mem_inf]
    have e4 : #({x | x ∈ U₀ ∨ x ∈ (dotHom c).ker} : Finset (BinarySpace m)) =
        #(({x | x ∈ U₀} : Finset (BinarySpace m)) ∪
          ({x | x ∈ (dotHom c).ker} : Finset (BinarySpace m))) := by
      congr 1
      ext x
      simp
    omega
  -- No witness pair of degree at most `4N` has loss at most `s`.
  have hexc : ∀ c : BinarySpace m, c.2 ≠ 0 →
      IsScalarExceptional domain f g (4 * N) A s (α c) (P c) := by
    intro c hc
    refine ⟨hPdeg c hc, by rw [hcard c hc]; exact hA, ?_⟩
    rintro F₀ G₀ - hG ⟨-, hloss⟩
    have hsplit := card_filter_add_card_filter_not
      (s := polynomialAgreementSet domain (combinedWord domain f g (C (α c))) (P c))
      fun i ↦ F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i
    unfold agreementLoss at hloss
    have hS := hcard c hc
    have hGdeg := natDegree_le_of_degree_le hG
    have hWX : (W * X ^ (4 * N)).natDegree = 6 * N := by
      rw [natDegree_mul_X_pow _ (monic_subspacePolynomial _).ne_zero, hWdeg]
      ring
    have hzero : W * X ^ (4 * N) - G₀ = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        (((polynomialAgreementSet domain (combinedWord domain f g (C (α c))) (P c)).filter
          fun i ↦ ¬(F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i)).map domain) ?_ ?_
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
        have hi := (mem_filter.mp hi).2
        simp only [ne_eq, not_or, not_not] at hi
        simp [hi.2, hg]
      · rw [card_map]
        have := natDegree_sub_le (W * X ^ (4 * N)) G₀
        omega
    have := congrArg natDegree (sub_eq_zero.mp hzero)
    omega
  -- The functionals with `c₂ ≠ 0` number `n - 8` and give distinct challenges.
  set T : Finset (BinarySpace m) := univ ×ˢ univ.erase 0 with hT
  have hTcard : #T = 16 * N - 8 := by
    rw [hT, card_product, card_erase_of_mem (mem_univ _), card_univ, card_univ]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [h2]
    omega
  have hinj : Set.InjOn α T := by
    intro c hcT c' hc'T hcc
    have hc : c.2 ≠ 0 := (mem_erase.mp (mem_product.mp hcT).2).1
    have hc' : c'.2 ≠ 0 := (mem_erase.mp (mem_product.mp hc'T).2).1
    have hLL : L c - L c' = R c - R c' := by
      simp only [hR]
      rw [hcc]
      ring
    have hzero : L c - L c' = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        (({x | x ∈ (dotHom c).ker ⊓ (dotHom c').ker} : Finset (BinarySpace m)).map
          ⟨ψ, hψinj⟩) ?_ ?_
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
        have hy : y ∈ (dotHom c).ker ∧ y ∈ (dotHom c').ker := by simpa using hy
        have h1 := (eval_subspacePolynomial_eq_zero_iff _ _).2
          ((AddSubgroup.mem_map_iff_mem hψinj).2 hy.1)
        have h2 := (eval_subspacePolynomial_eq_zero_iff _ _).2
          ((AddSubgroup.mem_map_iff_mem hψinj).2 hy.2)
        simp only [hL, eval_sub, Function.Embedding.coeFn_mk]
        rw [h1, h2, sub_zero]
      · rw [card_map, hsub, hLL]
        have h1 := natDegree_le_of_degree_le
          ((degree_sub_le _ _).trans (max_le (hRdeg c hc) (hRdeg c' hc')))
        have h2 := card_ker_inf_ker_dotHom c c'
        omega
    apply dotHom_ker_injective
    apply AddSubgroup.map_injective hψinj
    ext y
    rw [← eval_subspacePolynomial_eq_zero_iff, ← eval_subspacePolynomial_eq_zero_iff]
    have := sub_eq_zero.mp hzero
    simp only [hL] at this
    rw [this]
  refine le_trans ?_ (le_scalarMCAError domain (4 * N) A s f g)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : #T ≤ #{a | ∃ Q, IsScalarExceptional domain f g (4 * N) A s a Q} :=
    card_le_card_of_injOn α (fun c hc ↦ mem_filter.mpr
      ⟨mem_univ _, P c, hexc c (mem_erase.mp (mem_product.mp hc).2).1⟩) hinj
  rw [← hTcard]
  exact_mod_cast this

end ReedSolomon
