/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami
/-! # BCIKS20 List-Decoding Extraction -/


namespace ProximityGap

open NNReal Finset Function
open Polynomial
open Polynomial.Bivariate
open scoped BigOperators
open NNReal Finset Function ProbabilityTheory Finset
open scoped BigOperators LinearCode
open Code

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

omit [DecidableEq (RatFunc F)] in
/-- The equation 5.12 from [BCIKS20]. -/
lemma irreducible_factorization_of_gs_solution
    {k : ℕ}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    ∀ eᵢ ∈ e, 1 ≤ eᵢ ∧
    ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
    ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
    Q = (Polynomial.C C) *
        ∏ (Rᵢ ∈ R.toFinset) (fᵢ ∈ f.toFinset) (eᵢ ∈ e.toFinset),
          (Rᵢ.comp ((Polynomial.X : F[Z][X][Y]) ^ fᵢ))^eᵢ := sorry

omit [DecidableEq (RatFunc F)] in
/-- Claim 5.6 of [BCIKS20]. -/
lemma discr_of_irred_components_nonzero
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : ∃ x₀,
      ∀ R ∈ (irreducible_factorization_of_gs_solution _h_gs).choose_spec.choose,
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

noncomputable def pg_Rset
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F[Z][X][Y] :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_Rset_irreducible (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      Irreducible R := by
  intro R hR
  classical
  -- unfold the definition of `pg_Rset`
  unfold pg_Rset at hR
  -- `hR` is membership in the `toFinset` of the multiset of normalized factors
  have hR' : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
    simpa using hR
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor (a := Q) R hR'

noncomputable def pg_candidatePairs
    (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Finset (F[Z][X][Y] × F[Z][X]) :=
  let Rset := pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs
  Rset.biUnion (fun R =>
    (UniqueFactorizationMonoid.normalizedFactors
        (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H)))

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_card_normalizedFactors_toFinset_le_natDegree (p : F[Z][X]) (hp : p.Separable) :
    #((UniqueFactorizationMonoid.normalizedFactors p).toFinset) ≤ p.natDegree := by
  classical
  let s : Multiset (F[Z][X]) := UniqueFactorizationMonoid.normalizedFactors p
  have hs0 : (0 : F[Z][X]) ∉ s := by
    simpa [s] using (UniqueFactorizationMonoid.zero_notMem_normalizedFactors p)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpos : ∀ q ∈ s, 1 ≤ q.natDegree := by
    intro q hq
    have hq' : q ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      simpa [s] using hq
    have hq_irred : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq'
    have hq_dvd : q ∣ p :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq'
    have hq_sep : q.Separable :=
      Polynomial.Separable.of_dvd hp hq_dvd
    have hq_natDegree_ne_zero : q.natDegree ≠ 0 := by
      intro hdeg0
      have hconst : q = Polynomial.C (q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hdeg0
      have hsepC : (Polynomial.C (q.coeff 0) : F[Z][X]).Separable := by
        -- rewrite `hq_sep` using `hconst`
        exact hconst ▸ hq_sep
      have hunitCoeff : IsUnit (q.coeff 0) :=
        (Polynomial.separable_C (q.coeff 0)).1 hsepC
      have hunitC : IsUnit (Polynomial.C (q.coeff 0) : F[Z][X]) :=
        (Polynomial.isUnit_C).2 hunitCoeff
      have hunit : IsUnit q := by
        -- rewrite back using `hconst`
        exact hconst.symm ▸ hunitC
      exact hq_irred.not_isUnit hunit
    exact Nat.one_le_iff_ne_zero.2 hq_natDegree_ne_zero
  have hcard_le_sum : s.card ≤ (s.map Polynomial.natDegree).sum := by
    -- prove a general statement by induction
    have : (∀ q ∈ s, 1 ≤ q.natDegree) → s.card ≤ (s.map Polynomial.natDegree).sum := by
      refine Multiset.induction_on s ?_ ?_
      · intro _
        simp
      · intro a t ih ht
        have ha : 1 ≤ a.natDegree := ht a (by simp)
        have ht' : ∀ q ∈ t, 1 ≤ q.natDegree := by
          intro q hq
          exact ht q (Multiset.mem_cons_of_mem hq)
        have ih' : t.card ≤ (t.map Polynomial.natDegree).sum := ih ht'
        have hstep : t.card + 1 ≤ (t.map Polynomial.natDegree).sum + a.natDegree :=
          Nat.add_le_add ih' ha
        -- rewrite goal
        simpa [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, Nat.add_comm] using hstep
    exact this hpos
  have hassoc : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hp0)
  have hnatDegree_prod : s.prod.natDegree = p.natDegree := by
    apply Polynomial.natDegree_eq_of_degree_eq
    exact Polynomial.degree_eq_degree_of_associated hassoc
  have hcard_le : s.card ≤ p.natDegree := by
    have hnat : s.prod.natDegree = (s.map Polynomial.natDegree).sum :=
      Polynomial.natDegree_multiset_prod (t := s) hs0
    have h1 : s.card ≤ s.prod.natDegree := by
      simpa [hnat.symm] using hcard_le_sum
    simpa [hnatDegree_prod] using h1
  have hfin : #s.toFinset ≤ p.natDegree :=
    (Multiset.toFinset_card_le (m := s)).trans hcard_le
  simpa [s] using hfin

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_evalX_eq_map_evalRingHom (x₀ : F) (R : F[Z][X][Y]) :
    Bivariate.evalX (Polynomial.C x₀) R = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) := by
  classical
  ext n n'
  · simp [Bivariate.evalX, Polynomial.coeff_map]
    simp [Polynomial.coeff]

open scoped Polynomial.Bivariate in
noncomputable def pg_eval_on_Z (p : F[Z][X][Y]) (z : F) : Polynomial (Polynomial F) :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_H_of_R_eval_zero (δ : ℚ) (x₀ : F)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
  (R : F[Z][X][Y]) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) R z.1).eval P = 0 →
  Bivariate.evalX (Polynomial.C x₀) R ≠ 0 →
  ∃ H,
    H ∈ UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
  classical
  dsimp
  set P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2 with hP
  intro hR hNZ
  -- handy lemma: ArkLib's `Bivariate.evalX` agrees with `Polynomial.map` via `evalRingHom`.
  have evalX_eq_map {R : Type} [CommSemiring R] (a : R) (f : Polynomial (Polynomial R)) :
      Bivariate.evalX a f = f.map (Polynomial.evalRingHom a) := by
    ext n
    simp [Bivariate.evalX, Polynomial.coeff_map]
    simp [Polynomial.coeff]
  -- abbreviate p := evalX at x₀ (this is a bivariate poly in Z,Y)
  set p := Bivariate.evalX (Polynomial.C x₀) R with hp
  have hp_root : (Bivariate.evalX z.1 p).eval (P.eval x₀) = 0 := by
    -- evaluate the hypothesis at x₀
    have hx : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = 0 := by
      have := congrArg (fun g : F[X] => g.eval x₀) hR
      simpa using this
    -- set up abbreviations
    let fZ : F[X] →+* F := Polynomial.evalRingHom z.1
    let q : F[Z][X] := P.map (Polynomial.C)
    let r : F[X] := Polynomial.C x₀
    have hqmap : q.map fZ = P := by
      -- `(P.map C).map fZ = P.map (fZ.comp C)` and `fZ.comp C = id`.
      have hf : fZ.comp (Polynomial.C) = (RingHom.id F) := by
        ext a
        simp [fZ]
      -- now simplify
      simp [q, Polynomial.map_map, hf]
    have hr : fZ r = x₀ := by
      simp [fZ, r]
    -- rewrite the left-hand evaluation using `map_mapRingHom_eval_map_eval`
    have hcommZ : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = fZ ((R.eval q).eval r) := by
      have h := Polynomial.map_mapRingHom_eval_map_eval (f := fZ) (p := R) (q := q) r
      simpa [pg_eval_on_Z, fZ, hqmap, hr] using h
    have hfz0 : fZ ((R.eval q).eval r) = 0 := by
      -- combine `hx` and `hcommZ`
      calc
        fZ ((R.eval q).eval r) = ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ := by
          simp [hcommZ]
        _ = 0 := hx
    -- show `fZ ((R.eval q).eval r)` is the desired evaluation of `p`
    have hp_map : p = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) := by
      exact hp.trans (pg_evalX_eq_map_evalRingHom (F := F) x₀ R)
    -- commute evaluation in Y then X with evaluation in X then Y
    have hYX : (R.eval q).eval r = (p.eval (q.eval r)) := by
      have h := (Polynomial.eval₂_hom (p := R) (f := Polynomial.evalRingHom r) q)
      have h' : (R.map (Polynomial.evalRingHom r)).eval ((Polynomial.evalRingHom r) q) =
          (Polynomial.evalRingHom r) (R.eval q) := by
        simpa [Polynomial.eval₂_eq_eval_map] using h
      have h'' : (R.eval q).eval r = (R.map (Polynomial.evalRingHom r)).eval (q.eval r) := by
        simpa [Polynomial.coe_evalRingHom] using h'.symm
      simpa [hp_map, Polynomial.coe_evalRingHom] using h''
    have hfz_eq : fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := by
      have : fZ ((R.eval q).eval r) = fZ (p.eval (q.eval r)) := by
        simp [hYX]
      have h := (Polynomial.eval₂_hom (p := p) (f := fZ) (q.eval r))
      have h' : (p.map fZ).eval (fZ (q.eval r)) = fZ (p.eval (q.eval r)) := by
        simp
      simp [this]
    have hfz_q : fZ (q.eval r) = P.eval x₀ := by
      simp [fZ, q, r]
    have hp_eval_as : fZ ((R.eval q).eval r) = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by
      have : Bivariate.evalX z.1 p = p.map fZ := by
        simpa [fZ] using (evalX_eq_map (R := F) z.1 p)
      calc
        fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := hfz_eq
        _ = (p.map fZ).eval (P.eval x₀) := by simp [hfz_q]
        _ = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by simp [this]
    -- finish
    calc
      (Bivariate.evalX z.1 p).eval (P.eval x₀) = fZ ((R.eval q).eval r) := by
        simp [hp_eval_as]
      _ = 0 := hfz0
  -- use normalized factorization of nonzero p
  have hAssoc : Associated (UniqueFactorizationMonoid.normalizedFactors p).prod p :=
    UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hNZ
  let φ : _ →+* F :=
    (Polynomial.evalRingHom (P.eval x₀)).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
  have hφp : φ p = 0 := by
    -- rewrite `hp_root` using `evalX_eq_map` and unfold `φ`
    have hp_root' : (p.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by
      simpa [evalX_eq_map (R := F) z.1 p] using hp_root
    simpa [φ] using hp_root'
  have hφprod : φ (UniqueFactorizationMonoid.normalizedFactors p).prod = 0 := by
    have hAssoc' : Associated (φ (UniqueFactorizationMonoid.normalizedFactors p).prod) (φ p) :=
      Associated.map (φ : _ →* F) hAssoc
    have : φ (UniqueFactorizationMonoid.normalizedFactors p).prod = 0 ↔ φ p = 0 :=
      hAssoc'.eq_zero_iff
    exact this.mpr hφp
  have hmap_prod : ((UniqueFactorizationMonoid.normalizedFactors p).map φ).prod = 0 := by
    simpa [map_multiset_prod] using hφprod
  have hmem0 : (0 : F) ∈ (UniqueFactorizationMonoid.normalizedFactors p).map φ := by
    exact (Multiset.prod_eq_zero_iff).1 hmap_prod
  rcases (Multiset.mem_map.1 hmem0) with ⟨H, hHmem, hHφ⟩
  refine ⟨H, hHmem, ?_⟩
  -- turn the `φ`-evaluation into the desired statement
  have hHφ' : (H.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by
    simpa [φ] using hHφ
  simpa [evalX_eq_map (R := F) z.1 H] using hHφ'

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_R_of_Q_eval_zero (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) Q z.1).eval P = 0 →
  ∃ R,
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs ∧
    (pg_eval_on_Z (F := F) R z.1).eval P = 0 := by
  classical
  dsimp
  intro hQ
  set P : F[X] :=
    Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  have hQ' : (pg_eval_on_Z (F := F) Q z.1).eval P = 0 := by
    simpa [P] using hQ
  -- Define the ring hom φ : F[Z][X][Y] →+* F[X]
  let evZ : F[Z][X] →+* F[X] := Polynomial.mapRingHom (Polynomial.evalRingHom z.1)
  let evZ' : F[Z][X][Y] →+* Polynomial (Polynomial F) := Polynomial.mapRingHom evZ
  let φ : F[Z][X][Y] →+* F[X] := (Polynomial.evalRingHom P).comp evZ'
  have hφQ : φ Q = 0 := by
    simpa [φ, evZ', evZ, pg_eval_on_Z] using hQ'
  -- Use associated product of normalizedFactors
  have hassoc : Associated ((UniqueFactorizationMonoid.normalizedFactors Q).prod) Q :=
    UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) h_gs.Q_ne_0
  rcases hassoc with ⟨u, hu⟩
  -- Apply φ to the equation
  have hmul : φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) * φ (↑u) = 0 := by
    have h := congrArg φ hu
    have h' :
        φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) * φ (↑u) = φ Q := by
      simpa [map_mul] using h
    simpa [hφQ] using h'
  -- φ (↑u) is a unit hence nonzero, so the other factor is 0
  have hu_ne0 : φ (↑u : F[Z][X][Y]) ≠ (0 : F[X]) := by
    have hu_unit : IsUnit (φ (↑u : F[Z][X][Y])) := (RingHom.isUnit_map φ) u.isUnit
    exact IsUnit.ne_zero hu_unit
  have hprod0 : φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_right hu_ne0
  -- rewrite φ(prod) as product over mapped factors
  have hprod0' : ((UniqueFactorizationMonoid.normalizedFactors Q).map φ).prod = 0 := by
    simpa [map_multiset_prod] using hprod0
  -- extract some factor with φ R = 0
  have hz0 : (0 : F[X]) ∈ (UniqueFactorizationMonoid.normalizedFactors Q).map φ := by
    exact (Multiset.prod_eq_zero_iff).1 hprod0'
  rcases (Multiset.mem_map.1 hz0) with ⟨R, hRmem, hR0⟩
  refine ⟨R, ?_, ?_⟩
  · -- show R ∈ pg_Rset = (normalizedFactors Q).toFinset
    dsimp [pg_Rset]
    exact (Multiset.mem_toFinset).2 hRmem
  · -- show (pg_eval_on_Z R z.1).eval P = 0
    simpa [φ, evZ', evZ, pg_eval_on_Z] using hR0

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_pair_for_z (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (hx0 : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) Q z.1).eval P = 0 →
  ∃ R H,
    (R, H) ∈ pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) x₀ h_gs ∧
    let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
    (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
    (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
  classical
  -- Unfold the outer `let P := ...` so we can introduce the hypothesis.
  simp only
  intro hQ
  -- Name the interpolation polynomial associated to `z`.
  let P : F[X] :=
    Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  have hQ' : (pg_eval_on_Z (F := F) Q z.1).eval P = 0 := by
    simpa [P] using hQ
  -- 1) Extract `R ∈ pg_Rset` with the same vanishing property.
  have hRfun :=
    (pg_exists_R_of_Q_eval_zero (F := F) (k := k) (δ := δ) (h_gs := h_gs) (z := z))
  have hR' :
      ∃ R,
        R ∈
            pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
              h_gs ∧
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 := by
    -- `hRfun` has a `let P := ...` binder; rewrite using our local `P`.
    simpa [P] using hRfun hQ'
  obtain ⟨R, hRmem, hRzero⟩ := hR'
  -- 2) Nonzeroness of `evalX` at `x₀` from the hypothesis `hx0`.
  have hNZ : Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
    hx0 R hRmem
  -- 3) Extract a normalized factor `H` of `evalX x₀ R` with the desired vanishing.
  have hHfun :=
    (pg_exists_H_of_R_eval_zero (F := F) (k := k) (δ := δ) (x₀ := x₀) (_h_gs := h_gs)
      (z := z) (R := R))
  have hH' :
      ∃ H,
        H ∈
            UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
          (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
    simpa [P] using hHfun hRzero hNZ
  obtain ⟨H, hHmem, hHzero⟩ := hH'
  -- 4) Show `(R, H)` lies in `pg_candidatePairs`.
  have hPairMem :
      (R, H) ∈
        pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
          x₀ h_gs := by
    have h' :
        R ∈
            pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
              h_gs ∧
          H ∈
            UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) :=
      And.intro hRmem hHmem
    simpa [pg_candidatePairs] using h'
  -- 5) Package everything.
  refine ⟨R, H, hPairMem, ?_⟩
  -- Discharge the inner `let P := ...` binder using our local `P`.
  simpa [P] using And.intro hRzero hHzero


omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_natDegree_evalX_le_natDegreeY (x₀ : F) (R : F[Z][X][Y]) :
    (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ Bivariate.natDegreeY R := by
  classical
  -- Rewrite `evalX` in terms of `map`.
  rw [pg_evalX_eq_map_evalRingHom (x₀ := x₀) (R := R)]
  -- `natDegreeY` is definitional.
  unfold Bivariate.natDegreeY
  -- Apply the standard degree bound for `Polynomial.map`.
  simpa using
    (Polynomial.natDegree_map_le (p := R)
      (f := Polynomial.evalRingHom (Polynomial.C x₀)))

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_sum_natDegreeY_Rset_le_natDegreeY_Q (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Finset.sum (pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs)
      (fun R => Bivariate.natDegreeY R)
    ≤ Bivariate.natDegreeY Q := by
  classical
  -- Unfold the definition of `pg_Rset`.
  simp only [pg_Rset]
  -- Abbreviate the multiset of normalized factors.
  set s : Multiset F[Z][X][Y] := UniqueFactorizationMonoid.normalizedFactors Q with hs
  -- Rewrite the goal in terms of `s`.
  simp only [hs, ge_iff_le]
  have hQ0 : Q ≠ 0 := h_gs.Q_ne_0
  have hs0 : (0 : F[Z][X][Y]) ∉ s := by
    simpa [hs] using (UniqueFactorizationMonoid.zero_notMem_normalizedFactors (x := Q))
  have hsum_le :
      Finset.sum s.toFinset (fun R => Bivariate.natDegreeY R)
        ≤ Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) := by
    refine Finset.sum_le_sum ?_
    intro R hR
    have hmem : R ∈ s := (Multiset.mem_toFinset.1 hR)
    have hcount : 0 < s.count R := (Multiset.count_pos.2 hmem)
    exact Nat.le_mul_of_pos_left (Bivariate.natDegreeY R) hcount
  have hsum_count :
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) =
        (s.map fun R => Bivariate.natDegreeY R).sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count (s := s) (f := fun R => Bivariate.natDegreeY R)).symm
  have hdeg_prod :
      (s.map fun R => Bivariate.natDegreeY R).sum = Bivariate.natDegreeY s.prod := by
    simpa [Bivariate.natDegreeY] using
      (Polynomial.natDegree_multiset_prod (t := s) hs0).symm
  have hfinset_eq_prod :
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) =
        Bivariate.natDegreeY s.prod := by
    calc
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R)
          = (s.map fun R => Bivariate.natDegreeY R).sum := hsum_count
      _ = Bivariate.natDegreeY s.prod := hdeg_prod
  have hleft_le_prod :
      Finset.sum s.toFinset (fun R => Bivariate.natDegreeY R) ≤ Bivariate.natDegreeY s.prod := by
    simpa [hfinset_eq_prod] using hsum_le
  have hassoc : Associated s.prod Q := by
    -- `prod_normalizedFactors` gives association between the product of normalized factors and `Q`.
    simpa [hs] using (UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ0)
  have hdeg_assoc : (s.prod).degree = Q.degree :=
    Polynomial.degree_eq_degree_of_associated hassoc
  have hnat_assoc : (s.prod).natDegree = Q.natDegree :=
    Polynomial.natDegree_eq_natDegree (p := s.prod) (q := Q) hdeg_assoc
  have hnatY_assoc : Bivariate.natDegreeY s.prod = Bivariate.natDegreeY Q := by
    simp [Bivariate.natDegreeY, hnat_assoc]
  simpa [hnatY_assoc] using hleft_le_prod

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_card_candidatePairs_le_natDegreeY (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hsep : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      (Bivariate.evalX (Polynomial.C x₀) R).Separable) :
  #(pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) x₀ h_gs) ≤ Bivariate.natDegreeY Q := by
  classical
  -- Shorthands for the set of candidate polynomials `R` and the corresponding set of
  -- pairs for each `R`.
  set Rset : Finset F[Z][X][Y] :=
    pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs with hRset
  set t : F[Z][X][Y] → Finset (F[Z][X][Y] × F[Z][X]) := fun R =>
    (UniqueFactorizationMonoid.normalizedFactors
        (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H)) with ht
  -- Unfold `pg_candidatePairs` as a `biUnion` over `Rset`.
  have hcp :
      pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) x₀ h_gs
        = Rset.biUnion t := by
    simp [pg_candidatePairs, pg_Rset, hRset, ht]
  -- Cardinality bound for a `biUnion`.
  have hcard_biUnion :
      #(pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) x₀ h_gs)
        ≤ ∑ R ∈ Rset, #(t R) := by
    simpa [hcp] using (Finset.card_biUnion_le (s := Rset) (t := t))
  -- Pointwise bound: for each `R ∈ Rset`, `#(t R)` is bounded by `natDegreeY R`.
  have hpoint : ∀ R : F[Z][X][Y], R ∈ Rset → #(t R) ≤ Bivariate.natDegreeY R := by
    intro R hR
    -- `t R` is an injective image of the factor set.
    have hinj : Function.Injective (fun H : F[Z][X] => (R, H)) := by
      intro H1 H2 h
      simpa using congrArg Prod.snd h
    have hcard_image :
        #(t R) =
          #((UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset) := by
      simpa [ht] using
        (Finset.card_image_of_injective
          (s := (UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset)
          (f := fun H : F[Z][X] => (R, H)) hinj)
    have hR' : R ∈
        pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs := by
      simpa [hRset] using hR
    have hcard_nf :
        #((UniqueFactorizationMonoid.normalizedFactors
            (Bivariate.evalX (Polynomial.C x₀) R)).toFinset)
          ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree :=
      pg_card_normalizedFactors_toFinset_le_natDegree (F := F)
        (p := (Bivariate.evalX (Polynomial.C x₀) R)) (hp := hsep R hR')
    have hdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ Bivariate.natDegreeY R :=
      pg_natDegree_evalX_le_natDegreeY (F := F) x₀ R
    -- Combine the bounds.
    calc
      #(t R) =
          #((UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset) := hcard_image
      _ ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree := hcard_nf
      _ ≤ Bivariate.natDegreeY R := hdeg
  have hsum : (∑ R ∈ Rset, #(t R)) ≤ ∑ R ∈ Rset, Bivariate.natDegreeY R := by
    refine Finset.sum_le_sum ?_
    intro R hR
    exact hpoint R hR
  have hsum_Rset_le : (∑ R ∈ Rset, Bivariate.natDegreeY R) ≤ Bivariate.natDegreeY Q := by
    -- This is exactly the provided axiom, after rewriting `Rset`.
    simpa [hRset] using
      (pg_sum_natDegreeY_Rset_le_natDegreeY_Q (m := m) (n := n) (k := k)
        (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs)
  -- Put everything together.
  exact (hcard_biUnion.trans (hsum.trans hsum_Rset_le))

end BCIKS20ProximityGapSection5

end ProximityGap
