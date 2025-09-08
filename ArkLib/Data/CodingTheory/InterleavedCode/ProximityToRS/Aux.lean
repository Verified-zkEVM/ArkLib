/-
Auxiliary lemmas for the Proximity-to-RS results.
Some are placeholders to be filled in subsequent iterations.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open scoped Polynomial BigOperators

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {deg : ℕ} {α : ι ↪ F}

/-! Reindexing helpers -/

private def reindex {ι ι' F} (e : ι ≃ ι') (f : ι → F) : ι' → F := fun j => f (e.symm j)

lemma wt_reindex_eq {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  {F : Type*} [Zero F] [DecidableEq F] (e : ι ≃ ι') (f : ι → F) :
  Code.wt (reindex e f) = Code.wt f := by
  classical
  unfold Code.wt
  -- Compare supports via map along the embedding of the equivalence.
  have hset :
      ({j : ι' | reindex e f j ≠ 0} : Finset ι')
        = (Finset.map e.toEmbedding ({i : ι | f i ≠ 0} : Finset ι)) := by
    ext j; constructor
    · intro hj
      refine Finset.mem_map.mpr ?_
      refine ⟨e.symm j, ?_, by simp⟩
      simpa [reindex] using hj
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      -- From `hij : e.toEmbedding i = j`, derive `e.symm j = i`.
      have h_ei : e i = j := by simpa using hij
      have hsymm : e.symm j = i := by simpa [h_ei] using e.left_inv i
      -- And `hi : f i ≠ 0` gives the desired predicate at `j`.
      have hi' : f i ≠ 0 := by simpa using hi
      simpa [reindex, hsymm]
  -- Cardinalities of mapped finsets are equal to the source
  simpa [hset]
    using (Finset.card_map (s := ({i : ι | f i ≠ 0} : Finset ι)) (f := e.toEmbedding))

lemma hammingDist_reindex_eq {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  {F : Type*} [DecidableEq F]
  (e : ι ≃ ι') (u v : ι → F) :
  hammingDist (reindex e u) (reindex e v) = hammingDist u v := by
  classical
  -- Compare the filtered supports defining Hamming distance under reindexing
  have hset :
    (Finset.univ.filter fun j : ι' => reindex e u j ≠ reindex e v j)
      = Finset.map e.toEmbedding
          (Finset.univ.filter fun i : ι => u i ≠ v i) := by
    ext j; constructor
    · intro hj
      refine Finset.mem_map.mpr ?_
      refine ⟨e.symm j, ?_, by simp⟩
      simpa [reindex] using hj
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      have h_ei : e i = j := by simpa using hij
      have hsymm : e.symm j = i := by simpa [h_ei] using e.left_inv i
      have hi' : u i ≠ v i := by simpa using hi
      simpa [reindex, hsymm, hi']
  -- Cardinalities of mapped finsets are equal to the source
  simpa [hammingDist, hset]
    using (Finset.card_map (s := (Finset.univ.filter fun i : ι => u i ≠ v i)) (f := e.toEmbedding))

/-- Translation invariance of distance to the RS code: adding a codeword does not change
the distance to the code. -/
lemma translate_invariant_RS (w c : ι → F)
  (hc : c ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F))) :
  Code.distFromCode (w + c) (ReedSolomon.code α deg)
    = Code.distFromCode w (ReedSolomon.code α deg) := by
  classical
  -- Direct application of the general translation invariance for linear codes
  simpa using
    Code.distFromCode_add_codeword_eq
      (LC := ReedSolomon.code α deg) (w := w) (c := c) hc

/-- If a vector is within distance `e` from a code `C`, there exists a codeword within
that distance. -/
lemma exists_codeword_close_of_dist_le {u : ι → F} {C : Set (ι → F)} {e : ℕ}
  (h : Code.distFromCode u C ≤ e) : ∃ w ∈ C, Δ₀(u, w) ≤ e := by
  classical
  -- If C were empty, Δ₀(u,C) = ⊤, contradicting h ≤ e. Hence C is nonempty.
  have hCne : C.Nonempty := by
    by_cases hCempty : C = (∅ : Set (ι → F))
    · have htop : Code.distFromCode u C = ⊤ := by
        simpa [hCempty] using (Code.distFromCode_of_empty (u := u))
      have htople : (⊤ : ℕ∞) ≤ e := by simpa [htop] using h
      -- ⊤ ≤ e is impossible
      have : False := by simpa using htople
      exact this.elim
    · exact Set.nonempty_iff_ne_empty.mpr hCempty
  -- Pick v ∈ C minimizing d(v) = hammingDist u v
  have hCfin : (C : Set (ι → F)).Finite := Set.toFinite _
  obtain ⟨w0, hw0C⟩ := hCne
  have hw0mem : w0 ∈ hCfin.toFinset := by simpa using hCfin.mem_toFinset.mpr hw0C
  obtain ⟨v, hv_in, hmin⟩ :=
    Finset.exists_min_image (s := hCfin.toFinset) (f := fun x : (ι → F) => hammingDist u x)
      (by exact ⟨w0, hw0mem⟩)
  have hvC : v ∈ C := hCfin.mem_toFinset.mp hv_in
  have hminC : ∀ w ∈ C, hammingDist u v ≤ hammingDist u w := by
    intro w hwC
    have hw_in : w ∈ hCfin.toFinset := hCfin.mem_toFinset.mpr hwC
    exact hmin w hw_in
  -- Let S be the witness set defining Δ₀(u,C); show (Δ₀(u,v)) is a lower bound of S.
  let S : Set ℕ∞ := {d | ∃ w ∈ C, hammingDist u w ≤ d}
  have hLB : ∀ d ∈ S, (hammingDist u v : ℕ∞) ≤ d := by
    intro d hd; rcases hd with ⟨w, hwC, hdle⟩
    have : hammingDist u v ≤ hammingDist u w := hminC w hwC
    exact le_trans (by exact_mod_cast this) hdle
  -- Therefore (Δ₀(u,v)) ≤ sInf S = Δ₀(u,C) ≤ e
  have hv_le_dist : (hammingDist u v : ℕ∞) ≤ Code.distFromCode u C := by
    -- sInf S is the greatest lower bound of S
    have hv_le_sInf : (hammingDist u v : ℕ∞) ≤ sInf S := by
      apply le_csInf
      · refine ⟨(hammingDist u w0 : ℕ∞), ?_⟩; exact ⟨w0, hw0C, by simpa⟩
      · intro d hd; exact hLB d hd
    simpa [Code.distFromCode, S] using hv_le_sInf
  have : (hammingDist u v : ℕ∞) ≤ e := le_trans hv_le_dist h
  exact ⟨v, hvC, by exact_mod_cast this⟩

/-- Minimal distance of a Reed–Solomon code over a general index type `ι`.
This transports the known `Fin`-indexed statement via a reindexing equivalence. -/
lemma minDist_RS_general [NeZero deg] [Nonempty ι] :
  Code.minDist ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F))
    = Fintype.card ι - deg + 1 := by
  classical
  -- Reindex to `Fin m` and apply the Fin-indexed theorem.
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  -- Reindexed evaluation domain on `Fin m` as a function with injectivity.
  let αfun' : Fin m → F := fun j => α (e.symm j)
  have inj' : Function.Injective αfun' := by
    intro i j h
    have h' : α (e.symm i) = α (e.symm j) := h
    have : e.symm i = e.symm j := by exact α.injective h'
    simpa using congrArg e this
  let αemb' : (Fin m) ↪ F := ⟨αfun', inj'⟩
  -- Transport codewords via the reindexing equivalence on coordinates.
  let φ : (ι → F) → (Fin m → F) := fun f j => f (e.symm j)
  have hφ_dist : ∀ u v, hammingDist (φ u) (φ v) = hammingDist u v := by
    intro u v; classical
    -- Specialize the general reindexing lemma to `e : ι ≃ Fin m`.
    simpa [φ, reindex] using
      (hammingDist_reindex_eq (ι := ι) (ι' := Fin m) (F := F) e u v)
  -- Characterize membership under φ: RS over α maps to RS over α'.
  have hmem : ∀ f, f ∈ (ReedSolomon.code α deg : Submodule F (ι → F))
                 ↔ (φ f) ∈ (ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) := by
    intro f; constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, by ext j; rfl⟩
    · rintro ⟨p, hp, hfp⟩; refine ⟨p, hp, ?_⟩; ext i
      have hx := congrArg (fun g => g (e i)) hfp
      -- (φ f) (e i) = f i; RHS evaluates via αemb'
      simpa [φ, ReedSolomon.evalOnPoints, αemb', αfun'] using hx
  -- Distances are preserved by φ, hence minDist of the code equals that of the image code.
  have hdist_eq :
    Code.minDist ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F))
      = Code.minDist ((ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) : Set (Fin m → F)) := by
    -- Show the witness sets for sInf are the same via φ on pairs.
    unfold Code.minDist
    apply congrArg sInf
    ext d; constructor <;> intro hd
    · rcases hd with ⟨u, hu, v, hv, hne, hle⟩
      refine ⟨φ u, (hmem u).mp hu, φ v, (hmem v).mp hv, ?_, ?_⟩
      · intro h; apply hne; ext i
        have := congrArg (fun g => g (e i)) h
        simpa [φ] using this
      · simpa [hφ_dist u v] using hle
    · rcases hd with ⟨u, hu, v, hv, hne, hle⟩
      -- pull back witnesses by φ⁻¹ = precompose with e
      refine ⟨(fun i => u (e i)), ?_, (fun i => v (e i)), ?_, ?_, ?_⟩
      · have hφu : φ (fun i => u (e i)) = u := by funext j; simp [φ]
        have : (φ (fun i => u (e i))) ∈ (ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) := by
          simpa [hφu] using hu
        exact (hmem (fun i => u (e i))).mpr this
      · have hφv : φ (fun i => v (e i)) = v := by funext j; simp [φ]
        have : (φ (fun i => v (e i))) ∈ (ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) := by
          simpa [hφv] using hv
        exact (hmem (fun i => v (e i))).mpr this
      · intro h; apply hne; ext j; simpa using congrArg (fun g => g (e.symm j)) h
      · have hΔ := hammingDist_reindex_eq (ι := Fin m) (ι' := ι) (F := F) e.symm u v
        have hΔ' : Δ₀((fun i => u (e i)), (fun i => v (e i))) = Δ₀(u, v) := by
          simpa [reindex] using hΔ
        calc
          Δ₀((fun i => u (e i)), (fun i => v (e i))) = Δ₀(u, v) := hΔ'
          _ = d := hle
  -- Apply the Fin-indexed theorem.
  -- Handle both cases uniformly: ReedSolomonCode.minDist expects `deg ≤ m`.
  by_cases hle : deg ≤ m
  · -- Use the Fin-indexed minDist theorem and transport back.
    have hfin :=
      (ReedSolomonCode.minDist (F := F) (α := αfun') (inj := inj') (n := deg) (m := m) (h := hle))
    simpa [hdist_eq] using hfin
  · -- deg > m: the code equals the full space, so minDist = 1
    -- We avoid reconstructing a basis; this follows from standard RS theory.
    -- It also matches the right-hand side since m - deg + 1 = 1 in this case.
    have hgt : m < deg := Nat.lt_of_not_ge hle
    have hrhs : m - deg + 1 = 1 := by
      have : m ≤ deg := le_of_lt hgt
      simpa [m, Nat.sub_eq_zero_of_le this]
    -- Show the RS code at degree m equals the full space, hence at degree deg (> m) as well.
    have hdim_code_m : Module.finrank F (ReedSolomon.code αemb' m) = m := by
      simpa using (ReedSolomonCode.dim_eq_deg_of_le (F := F) (α := αfun') (inj := inj') (n := m)
        (m := m) (h := le_rfl))
    have hfinrank_ambient : Module.finrank F (Fin m → F) = m := by
      classical
      simpa using (Pi.finrank (Fin m) F)
    have htop : (ReedSolomon.code αemb' m) = ⊤ := by
      classical
      -- both finranks are equal to m
      have : Module.finrank F (ReedSolomon.code αemb' m) = Module.finrank F (Fin m → F) := by
        simpa [hfinrank_ambient] using hdim_code_m
      exact Submodule.eq_top_of_finrank_eq (K := F) (V := (Fin m → F)) this
    -- Monotonicity in degree gives: code m ⊆ code deg, hence code deg = ⊤ as well
    have htop_deg : (ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) = ⊤ := by
      -- `degreeLT _ m ≤ degreeLT _ deg` since m < deg
      have hsub : (Polynomial.degreeLT F m) ≤ (Polynomial.degreeLT F deg) := by
        intro p hp
        have hp' : p.degree < (m : WithBot ℕ) := by simpa [Polynomial.mem_degreeLT] using hp
        have hmle : ((m : ℕ) : WithBot ℕ) ≤ deg := by exact_mod_cast (le_of_lt hgt)
        have : p.degree < deg := lt_of_lt_of_le hp' hmle
        simpa [Polynomial.mem_degreeLT] using this
      -- map preserves ≤, so codes are nested
      have hle := Submodule.map_mono (f := ReedSolomon.evalOnPoints αemb') hsub
      -- from code m = ⊤ and code m ≤ code deg, deduce code deg = ⊤
      apply top_unique
      have : (ReedSolomon.code αemb' m : Submodule F (Fin m → F)) ≤ (ReedSolomon.code αemb' deg) := by
        simpa [ReedSolomon.code] using hle
      simpa [htop] using this
    -- Full space has minimum distance 1 from the definition of Δ₀
    have hfin_eq :
      Code.minDist ((ReedSolomon.code αemb' deg : Submodule F (Fin m → F)) : Set (Fin m → F)) = 1 := by
      classical
      -- Upper bound: exhibit 0 and a one-sparse delta vector at distance 1
      have hUB : Code.minDist ((⊤ : Submodule F (Fin m → F)) : Set (Fin m → F)) ≤ 1 := by
        unfold Code.minDist
        refine Nat.sInf_le ?_
        -- pick i0 and delta
        let i0 : Fin m := ⟨0, by
          have : 0 < m := by simpa [m] using Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)
          simpa⟩
        let δ : Fin m → F := fun j => if j = i0 then 1 else 0
        have hδ_ne : (0 : Fin m → F) ≠ δ := by
          intro h; have := congrArg (fun f => f i0) h; simpa [δ] using this
        have hdist_delta : hammingDist (0 : Fin m → F) δ = 1 := by
          unfold δ
          -- Show directly that exactly one coordinate differs from zero
          have hsetU :
              (Finset.univ.filter
                (fun i : Fin m => (0 : F) ≠ (if i = i0 then (1 : F) else 0)))
              = {i0} := by
            ext j; by_cases hji : j = i0 <;> simp [hji]
          -- Also record the cardinality of the equality-locus set for simp's alternative normalization
          have hEqCard : (({i : Fin m | i = i0} : Finset (Fin m)).card) = 1 := by
            classical
            have hEq : ({i : Fin m | i = i0} : Finset (Fin m)) = ({i0} : Finset (Fin m)) := by
              ext j; by_cases hji : j = i0 <;> simp [hji]
            simpa [hEq, Finset.card_singleton]
          simpa [hammingDist, hsetU, Finset.card_singleton]
        exact ⟨0, by simp, δ, by simp [δ], by exact hδ_ne, hdist_delta⟩
      -- Lower bound: any two distinct vectors differ in ≥ 1 coordinate
      have hLB : 1 ≤ Code.minDist ((⊤ : Submodule F (Fin m → F)) : Set (Fin m → F)) := by
        unfold Code.minDist
        -- Nonempty set of distances (reuse delta witness)
        let i0 : Fin m := ⟨0, by
          have : 0 < m := by simpa [m] using Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)
          simpa⟩
        let δ : Fin m → F := fun j => if j = i0 then 1 else 0
        have hδ_ne : (0 : Fin m → F) ≠ δ := by
          intro h; have := congrArg (fun f => f i0) h; simpa [δ] using this
        have hne : {d | ∃ u ∈ ((⊤ : Submodule F (Fin m → F)) : Set (Fin m → F)), ∃ v ∈ ((⊤ : Submodule F (Fin m → F)) : Set (Fin m → F)), u ≠ v ∧ hammingDist u v = d}.Nonempty := by
          refine ⟨1, 0, by simp, δ, by simp [δ], hδ_ne, ?_⟩
          have hset2U :
              (Finset.univ.filter (fun i : Fin m => (0 : F) ≠ δ i))
              = {i0} := by
            ext j; by_cases hji : j = i0 <;> simp [δ, hji]
          -- And the alternative normalization
          have hEqCard : (({i : Fin m | i = i0} : Finset (Fin m)).card) = 1 := by
            classical
            have hEq : ({i : Fin m | i = i0} : Finset (Fin m)) = ({i0} : Finset (Fin m)) := by
              ext j; by_cases hji : j = i0 <;> simp [hji]
            simpa [hEq, Finset.card_singleton]
          simpa [hammingDist, hset2U, Finset.card_singleton]
        apply sInf.le_sInf_of_LB hne
        intro d hd
        rcases hd with ⟨u, -, v, -, hneuv, rfl⟩
        -- show 1 ≤ hammingDist u v
        have hex : ∃ j : Fin m, u j ≠ v j := by
          by_contra hnone
          have : u = v := by
            funext j; by_contra hj; exact hnone ⟨j, by simpa using hj⟩
          exact hneuv this
        rcases hex with ⟨j, hj⟩
        have : 1 ≤ ({i : Fin m | u i ≠ v i} : Finset (Fin m)).card := by
          have hne' : ({i : Fin m | u i ≠ v i} : Finset (Fin m)).Nonempty := ⟨j, by simpa using hj⟩
          exact Nat.succ_le_of_lt (Finset.card_pos.mpr hne')
        simpa [hammingDist] using this
      have htop_minDist : Code.minDist ((⊤ : Submodule F (Fin m → F)) : Set (Fin m → F)) = 1 :=
        le_antisymm hUB hLB
      simpa [htop_deg] using htop_minDist
    simpa [hdist_eq, hrhs, m] using hfin_eq

/-- Any nonzero codeword in an RS code has weight at least `n - deg + 1`. -/
lemma wt_nonzero_ge_minDist_RS [NeZero deg] [Nonempty ι] {c : ι → F}
  (hc : c ∈ (ReedSolomon.code α deg : Submodule F (ι → F))) (hc0 : c ≠ 0) :
  Fintype.card ι - deg + 1 ≤ Code.wt c := by
  classical
  -- From the definition of `minDist`, any nonzero codeword witnesses `minDist ≤ wt c`.
  have hmin : Code.minDist (ReedSolomon.code α deg : Set (ι → F)) ≤ Code.wt c := by
    unfold Code.minDist
    refine Nat.sInf_le ?_
    exact ⟨c, by simp [hc], 0, by simp, hc0, by simp [Code.wt, hammingDist]⟩
  -- Rewrite `minDist` for RS codes to `|ι| - deg + 1`.
  have hmin_eq :
      Code.minDist (ReedSolomon.code α deg : Set (ι → F))
        = Fintype.card ι - deg + 1 := by
    simpa using (ProximityToRS.minDist_RS_general (α := α) (deg := deg) (F := F) (ι := ι))
  simpa [hmin_eq] using hmin

/-- Weight is subadditive under addition. -/
lemma wt_add_le {x y : ι → F} : Code.wt (x + y) ≤ Code.wt x + Code.wt y := by
  classical
  -- wt (x + y) = Δ₀(x + y, 0) = Δ₀(x, -y)
  have hsum : Code.wt (x + y) = hammingDist (x + y) 0 := by simp [Code.wt, hammingDist]
  have hx : hammingDist x 0 = Code.wt x := by simp [Code.wt, hammingDist]
  have hyn : hammingDist 0 (-y) = Code.wt y := by simp [Code.wt, hammingDist]
  calc
    Code.wt (x + y) = hammingDist (x + y) 0 := hsum
    _ = hammingDist x (-y) := by
      simpa [sub_eq_add_neg] using
        (Code.hammingDist_add_right_eq_sub (u := x) (v := 0) (c := y))
    _ ≤ hammingDist x 0 + hammingDist 0 (-y) := hammingDist_triangle x 0 (-y)
    _ = Code.wt x + Code.wt y := by simp [hx, hyn]

/-- Nonzero scalar multiplication preserves the Hamming weight (support). -/
lemma wt_smul_eq_of_ne_zero {a : F} {x : ι → F} (ha : a ≠ 0) :
  Code.wt (a • x) = Code.wt x := by
  classical
  unfold Code.wt
  have hsubset₁ : ({i : ι | (a • x) i ≠ 0} : Finset ι) ⊆ ({i : ι | x i ≠ 0} : Finset ι) := by
    intro i hi; simpa [Pi.smul_apply, smul_eq_mul, mul_eq_zero, ha] using hi
  have hsubset₂ : ({i : ι | x i ≠ 0} : Finset ι) ⊆ ({i : ι | (a • x) i ≠ 0} : Finset ι) := by
    intro i hi; simpa [Pi.smul_apply, smul_eq_mul, mul_eq_zero, ha] using hi
  apply le_antisymm
  · exact Finset.card_mono hsubset₁
  · exact Finset.card_mono hsubset₂

end ProximityToRS
