/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov,
Mirco Richter, Chung Thai Nguyen, Aristotle (Harmonic)
-/
module

public import ArkLib.Data.Matrix.Vandermonde
public import ArkLib.Data.MvPolynomial.LinearMvExtension
public import ArkLib.Data.Polynomial.Interface
public import ArkLib.ToMathlib.Polynomial.DegreeLT
public import CompPoly.Data.Polynomial.MonomialBasis
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Henselian
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.NNReal.Basic -- for instFloorSemiring of ℝ≥0

/-!
# Reed-Solomon Codes

- The lemmas with suffix `'` (e.g. dim_eq_deg_of_le', minDist', ...) are generalizations of
  their corresponding non-suffixed versions from `Fin m` index to arbitrary finite index type `ι`.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial NNReal

variable {F : Type*} {ι : Type*} (domain : ι ↪ F)

/-- The evaluation of a polynomial at a set of points specified by `domain : ι ↪ F`, as a linear
map. -/
def evalOnPoints [Semiring F] : F[X] →ₗ[F] (ι → F) where
  toFun p x := p.eval (domain x)
  map_add'  := by aesop
  map_smul' := by aesop

/-- Proves that `evalOnPoints` preserves multiplication as well. -/
def evalOnPointsRingHom [CommSemiring F] : F[X] →+* (ι → F) where
  toFun p x := p.eval (domain x)
  map_zero' := by aesop
  map_one'  := by aesop
  map_add'  := by aesop
  map_mul'  := by aesop

lemma evalOnPointsRingHom_eq_evalOnPoints [CommSemiring F] {p : F[X]} {domain : ι ↪ F} :
    evalOnPointsRingHom domain p = evalOnPoints domain p := rfl

@[simp]
lemma evalOnPoints_mul [CommSemiring F] {domain : ι ↪ F} {p q : F[X]} :
    evalOnPoints domain (p * q) = evalOnPoints domain p * evalOnPoints domain q :=
  map_mul (evalOnPointsRingHom domain) p q

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
-/
noncomputable def code (deg : ℕ) [Semiring F] : Submodule F (ι → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

/-- If a linear encoder `enc : F[X] →ₗ[F] (ι → Fin 1 → F)` agrees with plain evaluation at
its single index, `enc p x 0 = p.eval (domain x)`, then the code it cuts out of
`Polynomial.degreeLT F k` is `code domain k`, up to erasing the trivial `Fin 1` index.

This is the shared content of the degenerate-parameter collapse for the Reed-Solomon
variants over the alphabet `Fin s → F`. -/
lemma mem_map_degreeLT_one_iff_mem_code [CommSemiring F] (k : ℕ)
    (enc : F[X] →ₗ[F] (ι → Fin 1 → F))
    (henc : ∀ (p : F[X]) (x : ι), enc p x 0 = p.eval (domain x))
    (f : ι → Fin 1 → F) :
    f ∈ (Polynomial.degreeLT F k).map enc ↔ (fun x ↦ f x 0) ∈ code domain k := by
  simp only [Submodule.mem_map, code, evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, funext fun x ↦ (henc p x).symm⟩
  · rintro ⟨p, hp, hp_eval⟩
    refine ⟨p, hp, ?_⟩
    funext x j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [henc p x]
    exact congrFun hp_eval x

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `domain`. -/
def genMatrix (deg : ℕ) [Semiring F] : Matrix (Fin deg) ι F :=
  .of fun i j => domain j ^ (i : ℕ)

/-- The (parity)-check matrix of the Reed-Solomon code, assuming `ι` is finite. -/
noncomputable def checkMatrix (deg : ℕ) [Fintype ι] [Field F] :
  Matrix (Fin (Fintype.card ι - deg)) ι F :=
  let P := Finset.univ.prod fun j => (X - C (domain j))
  .of fun i j => domain j ^ (i : ℕ) * (P.derivative.eval (domain j))⁻¹

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}
         {C : Set (ι → F)}

section

open Finset Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F]

abbrev RScodeSet (domain : ι ↪ F) (deg : ℕ) : Set (ι → F) := ReedSolomon.code domain deg

open Classical in
noncomputable def toFinset (domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (RScodeSet domain deg).toFinset

end

section

variable {deg m n : ℕ} {α : Fin m → F}

section

variable [Semiring F] {p : F[X]}

@[simp]
lemma evalOnPoints_C {domain : ι ↪ F} {a : F} :
    evalOnPoints domain (Polynomial.C a) = fun _ ↦ a := by simp [evalOnPoints]

@[simp]
lemma evalOnPoints_X {domain : ι ↪ F} :
    evalOnPoints domain Polynomial.X = domain := by simp [evalOnPoints]

/-- For a nonzero bound `n`, the degree of `p` is below `n` exactly when its natural degree is. -/
private lemma degree_lt_iff_natDegree_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    p.degree < n ↔ p.natDegree < n := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [degree_zero, natDegree_zero]
    exact ⟨fun _ ↦ Nat.pos_of_ne_zero hn, fun _ ↦ WithBot.bot_lt_coe n⟩
  · exact (natDegree_lt_iff_degree_lt hp).symm

lemma natDegree_lt_of_mem_degreeLT [NeZero deg] (h : p ∈ degreeLT F deg) : p.natDegree < deg :=
  (degree_lt_iff_natDegree_lt_of_ne_zero (NeZero.ne deg)).1 (mem_degreeLT.1 h)

def encode [DecidableEq F] (msg : Fin deg → F) (domain : Fin m ↪ F) : Fin m → F :=
  (polynomialOfCoeffs msg).eval ∘ ⇑domain

lemma encode_mem_ReedSolomon_code [DecidableEq F] [NeZero deg]
    {msg : Fin deg → F} {domain : Fin m ↪ F} :
  encode msg domain ∈ ReedSolomon.code domain deg :=
  ⟨polynomialOfCoeffs msg, ⟨by simp, by ext i; simp [encode, ReedSolomon.evalOnPoints]⟩⟩

end

def makeZero (ι : ℕ) (F : Type*) [Zero F] : Fin ι → F := fun _ ↦ 0

@[simp]
lemma codewordIsZero_makeZero {ι : ℕ} {F : Type*} [Zero F] :
    makeZero ι F = 0 := by unfold makeZero; ext; rfl

open LinearCode

/-- The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Fintype ι] [Field F] [inst : NeZero m] {α : ι ↪ F} :
    fromColGenMat (Vandermonde.nonsquare (ι' := m) α) = ReedSolomon.code α m := by
  classical
  unfold fromColGenMat ReedSolomon.code
  ext x; rw [LinearMap.mem_range, Submodule.mem_map]
  refine ⟨
    fun ⟨coeffs, h⟩ ↦ ⟨polynomialOfCoeffs coeffs, h.symm ▸ ?p₁⟩,
    fun ⟨p, h⟩ ↦ ⟨Fin.liftF' p.coeff, ?p₂⟩
  ⟩
  · rw [
      ←coeff_polynomialOfCoeffs_eq_coeffs (coeffs := coeffs),
      Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials (by simp)
    ]
    simp [ReedSolomon.evalOnPoints]
  · exact h.2 ▸ Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
                  (natDegree_lt_of_mem_degreeLT h.1)

section

variable [Semiring F]

lemma mem_code_of_polynomial_of_degree_lt_of_eval {n : ℕ} {α : ι ↪ F} {f : ι → F}
    (p : Polynomial F)
  (hdeg : p.degree < n) (heval : ∀ i, f i = p.eval (α i)) :
  f ∈ code α n :=
  Submodule.mem_map.2 ⟨p, mem_degreeLT.2 hdeg, funext fun i ↦ (heval i).symm⟩

lemma mem_code_of_polynomial_of_natDegree_lt_of_eval {n : ℕ} {α : ι ↪ F} {f : ι → F}
    (p : Polynomial F)
  (hdeg : p.natDegree < n) (heval : ∀ i, f i = p.eval (α i)) :
  f ∈ code α n :=
  mem_code_of_polynomial_of_degree_lt_of_eval p
    (degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2 hdeg)) heval

lemma mem_code_iff_exists_polynomial {n : ℕ} {α : ι ↪ F} {f : ι → F} :
    f ∈ code α n ↔ ∃ p : Polynomial F, p.degree < n ∧ f = evalOnPoints α p :=
  Submodule.mem_map.trans <| exists_congr fun _ ↦ and_congr mem_degreeLT eq_comm

theorem mem_code_iff_eval {n : ℕ} {α : ι ↪ F} {f : ι → F} :
    f ∈ ReedSolomon.code α n ↔
    ∃ p : F[X], p.degree < n ∧ ∀ x, p.eval (α x) = f x :=
  Submodule.mem_map.trans <| exists_congr fun _ ↦ and_congr mem_degreeLT funext_iff

lemma mem_code_iff_exists_polynomial_of_ne_zero {n : ℕ} [ne : NeZero n] {α : ι ↪ F} {f : ι → F} :
    f ∈ code α n ↔ ∃ p : Polynomial F, p.natDegree < n ∧ f = evalOnPoints α p :=
  mem_code_iff_exists_polynomial.trans <| exists_congr fun _ ↦
    and_congr_left' (degree_lt_iff_natDegree_lt_of_ne_zero ne.out)

theorem mem_code_iff_eval_of_ne_zero {n : ℕ} [NeZero n] {α : ι ↪ F} {f : ι → F} :
    f ∈ ReedSolomon.code α n ↔
    ∃ p : F[X], p.natDegree < n ∧ ∀ x, p.eval (α x) = f x :=
  mem_code_iff_eval.trans <| exists_congr fun _ ↦
    and_congr_left' (degree_lt_iff_natDegree_lt_of_ne_zero (NeZero.ne n))

/-- `evalOnPoints α p` belongs to an RS-code of degree `n`,
  if `p.degree < n`. -/
lemma evalOnPoints_mem_code_of_degree_lt {α : ι ↪ F} {p : F[X]} (h_deg : p.degree < n) :
    evalOnPoints α p ∈ code α n :=
  mem_code_of_polynomial_of_degree_lt_of_eval p h_deg (by simp [evalOnPoints])

/-- `evalOnPoints α p` belongs to an RS-code of degree `n`,
  if `p.natDegree < n`. -/
lemma evalOnPoints_mem_code_of_natDegree_lt {α : ι ↪ F} {p : F[X]} (h_deg : p.natDegree < n) :
    evalOnPoints α p ∈ code α n :=
  mem_code_of_polynomial_of_natDegree_lt_of_eval p h_deg (by simp [evalOnPoints])

/-- **Monotonicity of `code` in the degree bound.** If `n ≤ m`, the degree-`n` Reed-Solomon code
is contained in the degree-`m` code over the same domain. -/
@[mono]
lemma code_mono {n m : ℕ} (h : n ≤ m) (α : ι ↪ F) :
    code α n ≤ code α m :=
  Submodule.map_mono (Polynomial.degreeLT_mono h)

/-- **The degree-zero Reed-Solomon code is trivial.** Only the zero word is a codeword of
`code α 0`. A direct corollary of `Polynomial.degreeLT_zero` (general polynomial fact) +
`Submodule.map_bot` (general linear-algebra fact). -/
@[simp]
lemma code_zero (α : ι ↪ F) : code α 0 = ⊥ := by
  rw [code, Polynomial.degreeLT_zero, Submodule.map_bot]

end

section

open NNReal

variable [Field F]

/-- Dimension formula for RS code with arbitrary finite index type `ι`. -/
lemma dim_eq_deg_of_le [Fintype ι]
    {α : ι ↪ F} (h : n ≤ Fintype.card ι) :
  LinearCode.dim (ReedSolomon.code α n) = n := by
  rw [LinearCode.dim, code, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj,
    Polynomial.finrank_degreeLT_n]
  refine LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun ⟨p, hp⟩ hfp ↦ Subtype.ext ?_
  change p = 0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rwa [degreeLT_zero, Submodule.mem_bot] at hp
  · have : NeZero n := ⟨hn.ne'⟩
    exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero p α.injective (fun i ↦ congrFun hfp i)
      ((natDegree_lt_of_mem_degreeLT hp).trans_le h)

/-- The dimension of an RS-code equals the cardinality
  of the evaluation points if the original degree exceeds the cardinality. -/
lemma dim_eq_card_of_lt [Fintype ι] {α : ι ↪ F} (h : Fintype.card ι < n) :
    LinearCode.dim (ReedSolomon.code α n) = Fintype.card ι :=
  le_antisymm ((Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card F).le) <|
    (dim_eq_deg_of_le (α := α) le_rfl).symm.trans_le <| Submodule.finrank_mono (code_mono h.le α)

/-- Assumption-less expression for the dimension of an RS-code.
  The dimension equals the minimum of the degree and the cardinality
  of the evaluation set. -/
theorem dim_eq_min_deg_card {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    {n : ℕ} {α : ι ↪ F} :
  LinearCode.dim (ReedSolomon.code α n) = min n (Fintype.card ι) := by
  rcases le_or_gt n (Fintype.card ι) with hle | hlt
  · rw [dim_eq_deg_of_le hle, min_eq_left hle]
  · rw [dim_eq_card_of_lt hlt, min_eq_right hlt.le]

@[simp]
lemma length_eq_domain_card [Fintype ι] {deg : ℕ} {α : ι ↪ F} :
    length (ReedSolomon.code α deg) = Fintype.card ι := rfl

/- The usual formula for the rate of an RS-code: the degree divided by
  the cardinality of the evaluation set. -/
lemma rateOfLinearCode_eq_div [Fintype ι] {α : ι ↪ F} (h : n ≤ Fintype.card ι) :
    rate (ReedSolomon.code α n) = n / Fintype.card ι := by
  rw [rate, dim_eq_deg_of_le h, length_eq_domain_card]

/- Assumption-less formula for the rate of an RS-code: the minimun of degree
  and the cardinality of the evaluation set divided by the cardinality. -/
lemma rateOfLinearCode_eq_min_div [Fintype ι] {α : ι ↪ F} :
    rate (ReedSolomon.code α n) = (min n (Fintype.card ι)) / Fintype.card ι := by
  rw [rate, dim_eq_min_deg_card, length_eq_domain_card]

@[simp]
lemma dist_le_length [DecidableEq F] (inj : Function.Injective α) :
    minDist ((ReedSolomon.code ⟨α, inj⟩ n) : Set (Fin m → F)) ≤ m :=
  dist_UB.trans_eq (Fintype.card_fin m)

noncomputable abbrev sqrtRate [Fintype ι] (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt

@[simp]
lemma sqrtRate_nonneg [Fintype ι] (m : ℕ) (domain : ι ↪ F) :
    0 ≤ (sqrtRate m domain : ℝ) := (sqrtRate m domain).coe_nonneg

lemma sqrtRate_sq [Fintype ι] (m : ℕ) (domain : ι ↪ F) :
    (sqrtRate m domain : ℝ) ^ 2 =
    (min m (Fintype.card ι) : ℝ) / (Fintype.card ι : ℝ) := by
  rw [sqrtRate, ←NNReal.coe_pow, NNReal.sq_sqrt,
    ReedSolomon.rateOfLinearCode_eq_min_div]
  push_cast
  ring

lemma sqrtRate_pos [Fintype ι] [Nonempty ι] {m : ℕ}
    (hm : 0 < m) {domain : ι ↪ F} :
  0 < (sqrtRate m domain : ℝ) := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hsq : 0 < (sqrtRate m domain : ℝ) ^ 2 := by
    rw [sqrtRate_sq]
    have : 0 < min m (Fintype.card ι) := lt_min hm hcard
    positivity
  rcases (sqrtRate_nonneg m domain).lt_or_eq with h | h
  · exact h
  · rw [←h] at hsq
    simp at hsq

@[simp]
lemma sqrtRate_sq_le_one [Fintype ι] (m : ℕ) (domain : ι ↪ F) :
    (sqrtRate m domain : ℝ) ^ 2 ≤ 1 := by
  rw [sqrtRate_sq]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast min_le_right _ _

@[simp high]
lemma sqrtRate_le_one [Fintype ι] (m : ℕ) (domain : ι ↪ F) :
    ReedSolomon.sqrtRate m domain ≤ 1 :=
  pow_le_one_iff_of_nonneg (sqrtRate_nonneg m domain) two_ne_zero |>.mp
    (sqrtRate_sq_le_one m domain)

@[simp high]
lemma sqrtRate_le_one' [Fintype ι] (m : ℕ) (domain : ι ↪ F) :
    (ReedSolomon.sqrtRate m domain : ℝ) ≤ 1 := by
  norm_cast
  simp

end

lemma card_le_card_of_count_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Multiset α} {s' : Multiset β}
  {f : α → β} (inj : Function.Injective f) (h : ∀ a : α, s.count a ≤ s'.count (f a)) :
  s.card ≤ s'.card := by
    rw [← Multiset.card_map f s]
    refine Multiset.card_le_card (Multiset.le_iff_count.2 fun b ↦ ?_)
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      exact (Multiset.count_map_eq_count' f s inj a).trans_le (h a)
    · rw [Multiset.count_eq_zero_of_notMem fun hmem ↦ ?_]
      · exact Nat.zero_le _
      · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hmem
        exact hb ⟨a, rfl⟩

section

def constantCode {α : Type*} (x : α) (ι' : Type*) [Fintype ι'] : ι' → α := fun _ ↦ x

variable [Semiring F] {x : F} [Fintype ι] {α : ι ↪ F}

@[simp]
lemma weight_constantCode [DecidableEq F] :
    wt (constantCode x ι) = 0 ↔ IsEmpty ι ∨ x = 0 := by
  rw [wt_eq_zero_iff, Fintype.card_eq_zero_iff]
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact iff_of_true (.inl h) (.inl h)
  · exact or_congr_right ⟨fun hx ↦ hx i, fun hx _ ↦ hx⟩

@[simp]
lemma constantCode_mem_code [NeZero n] :
    constantCode x ι ∈ ReedSolomon.code α n :=
  Submodule.mem_map.2 ⟨C x, mem_degreeLT.2 <| degree_C_le.trans_lt <|
    WithBot.coe_lt_coe.2 (Nat.pos_of_ne_zero (NeZero.ne n)), evalOnPoints_C⟩

@[simp]
lemma constantCode_eq_ofNat_zero_iff [Nonempty ι] :
    constantCode x ι = 0 ↔ x = 0 := by
  unfold constantCode
  exact ⟨fun x ↦ Eq.mp (by simp) (congrFun x), (· ▸ rfl)⟩

@[simp]
lemma wt_constantCode [DecidableEq F] [NeZero x] :
    wt (constantCode x ι) = Fintype.card ι := by
  simp [constantCode, wt, NeZero.ne x]

end

theorem minDist_of_le [Fintype ι] [Field F] [DecidableEq F]
    {α : ι ↪ F} [nz : NeZero n] (h : n ≤ Fintype.card ι) :
  Code.minDist (ReedSolomon.code α n : Set (ι → F)) = Fintype.card ι - n + 1 := by
  have hn := nz.out
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  apply le_antisymm
  · have distUB := singletonBound (ReedSolomon.code α n)
    have h_le_len : Code.minDist ((ReedSolomon.code α n) : Set (ι → F)) ≤ Fintype.card ι := dist_UB
    rw [dim_eq_deg_of_le h, length_eq_domain_card] at distUB
    omega
  · rw [dist_eq_minWtCodewords]
    refine le_csInf ⟨_, constantCode 1 ι, constantCode_mem_code,
      constantCode_eq_ofNat_zero_iff.not.2 one_ne_zero, rfl⟩ ?_
    rintro b ⟨msg, ⟨p, p_deg, p_eval_on_α_eq_msg⟩, msg_neq_0, rfl⟩
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact msg_neq_0 (p_eval_on_α_eq_msg ▸ (evalOnPoints α).map_zero)
    let zeroes : Finset ι := {i | msg i = 0}
    have msg_zeros_lt_deg : zeroes.card < n := by
      rw [← Finset.card_map α]
      refine (card_le_degree_of_subset_roots fun x hx ↦ ?_).trans_lt
        (natDegree_lt_of_mem_degreeLT p_deg)
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
      exact (mem_roots hp0).2 ((congrFun p_eval_on_α_eq_msg i).trans (Finset.mem_filter.1 hi).2)
    have : zeroes.card + wt msg = Fintype.card ι := Finset.card_filter_add_card_filter_not _
    omega

@[simp]
theorem code_Nontrivial [Field F] [nz : NeZero n] [Inhabited ι] {α : ι ↪ F} :
    (ReedSolomon.code α n : Set (ι → F)).Nontrivial := by
  refine ⟨0, (code α n).zero_mem, evalOnPoints α 1,
    evalOnPoints_mem_code_of_natDegree_lt (natDegree_one.trans_lt (Nat.pos_of_ne_zero nz.out)),
    fun contra ↦ zero_ne_one ((congrFun contra default).trans (eval_one (x := α default)))⟩

@[simp]
theorem minDist_n_0 [Fintype ι] [Field F] [DecidableEq F] {α : ι ↪ F} :
    minDist (ReedSolomon.code α 0 : Set (ι → F)) = 0 := by simp [minDist]

theorem minDist_eq_card_sub_min_add_1 [Fintype ι] [Inhabited ι] [Field F] [DecidableEq F]
    {α : ι ↪ F} [nz : NeZero n] :
  minDist (ReedSolomon.code α n : Set (ι → F)) = Fintype.card ι - min n (Fintype.card ι) + 1 := by
  rcases le_or_gt n (Fintype.card ι) with hle | hlt
  · rw [min_eq_left hle, minDist_of_le hle]
  · rw [min_eq_right hlt.le]
    have distUB := singletonBound (ReedSolomon.code α n)
    have h_le_len : minDist ((ReedSolomon.code α n) : Set (ι → F)) ≤ Fintype.card ι := dist_UB
    have hpos := dist_pos_of_Nontrivial (ReedSolomon.code α n : Set (ι → F)) code_Nontrivial
    rw [dim_eq_card_of_lt hlt, length_eq_domain_card] at distUB
    rw [dist_eq_minDist] at hpos
    omega

/-- Two distinct Reed–Solomon codewords of degree `< m` agree in fewer than `m` positions. -/
lemma agree_lt_of_mem_code {F : Type*} [Fintype ι] [Field F] [DecidableEq F]
    {α : ι ↪ F} {n : ℕ} {c c' : ι → F}
  (hc : c ∈ ReedSolomon.code α n) (hc' : c' ∈ ReedSolomon.code α n) (hne : c ≠ c') :
  Code.agree c c' < n := by
  by_cases hn : n = 0
  · subst hn
    rw [code_zero, Submodule.mem_bot] at hc hc'
    exact absurd (hc.trans hc'.symm) hne
  · by_cases hcard : Fintype.card ι = 0
    · exfalso
      rw [Fintype.card_eq_zero_iff] at hcard
      exact hne (funext isEmptyElim)
    · have : NeZero n := ⟨hn⟩
      have : Inhabited ι :=
        ⟨Classical.choice (Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hcard))⟩
      have hmin := minDist_eq_card_sub_min_add_1 (n := n) (α := α)
      have hdist := minDist_le_dist hc hc' hne
      have hsum := Code.agree_add_hammingDist (u := c) (v := c')
      rcases le_or_gt n (Fintype.card ι) with hle | hlt
      · rw [min_eq_left hle] at hmin
        omega
      · rw [min_eq_right hlt.le] at hmin
        omega

/-- Two Reed-Solomon codewords of degree `< m` that agree on at least `m` positions
  are equal. -/
lemma eq_of_agree_of_card_le {ι : Type} [Finite ι] [Field F]
    {α : ι ↪ F} {n : ℕ} {c c' : ι → F}
  (hc : c ∈ code α n) (hc' : c' ∈ code α n)
  {T : Finset ι} (hT : n ≤ T.card) (hagree : ∀ t ∈ T, c t = c' t) : c = c' := by
  classical
  have := Fintype.ofFinite
  by_contra hne
  have hlt := ReedSolomon.agree_lt_of_mem_code hc hc' hne
  have hsub : T ⊆ ({i | c i = c' i} : Finset _) := fun t ht ↦
    Finset.mem_filter.2 ⟨Finset.mem_univ t, hagree t ht⟩
  exact absurd (hT.trans (Finset.card_le_card hsub)) (not_le.2 hlt)

/-- Reed-Solomon codes are maximum distance separable (MDS). -/
lemma isMDS_code {ι : Type*} [Fintype ι] [Inhabited ι] [Field F] [DecidableEq F]
    {α : ι ↪ F} [NeZero n] : LinearCode.IsMDS (ReedSolomon.code α n) := by
  simp only [IsMDS, Submodule.carrier_eq_coe, length_eq_domain_card]
  rw [dist_eq_minDist, minDist_eq_card_sub_min_add_1, dim_eq_min_deg_card]

/-- Distance equality for RS code with arbitrary finite index type `ι`. -/
theorem dist_eq_of_le [Fintype ι] {α : ι ↪ F}
    [Field F] [DecidableEq F] [NeZero n] (h : n ≤ Fintype.card ι) :
  dist ((ReedSolomon.code α n) : Set (ι → F)) = Fintype.card ι - n + 1 := by
  rw [dist_eq_minDist, ReedSolomon.minDist_of_le h]

/-- Distance equality for RS code with arbitrary finite index type `ι`. -/
theorem dist_eq [Fintype ι] [Inhabited ι] {α : ι ↪ F}
    [Field F] [DecidableEq F] [NeZero n] :
  dist ((ReedSolomon.code α n) : Set (ι → F)) = Fintype.card ι - min n (Fintype.card ι) + 1 := by
  rw [dist_eq_minDist, ReedSolomon.minDist_eq_card_sub_min_add_1]

/-- Unique decoding radius for RS code with arbitrary finite index type `ι`. -/
theorem uniqueDecodingRadius_RS_eq [Fintype ι]
    {α : ι ↪ F} [Field F] [DecidableEq F] [NeZero n]
  (h : n ≤ Fintype.card ι) :
  Code.uniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code α n) =
    (Fintype.card ι - n) / 2 := by
  simp_all only [uniqueDecodingRadius, dist_eq_minDist, minDist_of_le, add_tsub_cancel_right]

open NNReal in
/-- Relative unique decoding radius for RS code with arbitrary finite index type `ι`. -/
theorem relativeUniqueDecodingRadius_RS_eq [Fintype ι]
    {α : ι ↪ F} [Field F] [DecidableEq F] [NeZero n]
  (h : n ≤ Fintype.card ι) :
  Code.relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code α n) =
    ((1 : ℝ≥0) - n / Fintype.card ι) / 2 := by
  have h_card_ne_zero: Fintype.card ι ≠ 0 := by
    by_contra h_card_eq_zero
    have h_n_eq_0 : n = 0 := by omega
    have h_n_ne_0 : n ≠ 0 := by exact Ne.symm (NeZero.ne' n)
    exact h_n_ne_0 h_n_eq_0
  rw [Code.relativeUniqueDecodingRadius, ReedSolomon.dist_eq_of_le h]
  simp only [Nat.cast_add, Nat.cast_tsub, Nat.cast_one, add_tsub_cancel_right]
  conv_lhs =>
    rw [NNReal.sub_div, NNReal.sub_div, div_div, mul_comm, ←div_div]
    rw [div_self (Nat.cast_ne_zero.mpr h_card_ne_zero)]
  conv_rhs => rw [NNReal.sub_div, div_div, mul_comm, ←div_div]

end

noncomputable scoped instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s :=
  Fintype.ofFinite _

open NNReal Finset Function Finset in
noncomputable def finCarrier {ι : Type} [Fintype ι]
               {F : Type} [Field F] [Fintype F]
               (domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (ReedSolomon.code domain deg).carrier.toFinset

section

open LinearMap Finset Polynomial

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]
         {domain : ι ↪ F}
         {deg : ℕ}

/-- The linear map that maps a codeword `f : ι → F` to a degree < |ι| polynomial p,
such that `p(x) = f(x)` for all `x ∈ ι`. -/
noncomputable def interpolate : (ι → F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

/-- The linear map that maps a Reed-Solomon codeword to its associated polynomial. -/
noncomputable def toPolynomial : (ReedSolomon.code domain deg) →ₗ[F] F[X] :=
  domRestrict
    (interpolate (domain := domain))
    (ReedSolomon.code domain deg)

lemma toPolynomial_def {f : ReedSolomon.code domain deg} :
    toPolynomial f = Lagrange.interpolate univ domain f := rfl

/-- The interpolating polynomial of a codeword has degree smaller than the domain size. -/
private lemma degree_toPolynomial_lt_card (c : ReedSolomon.code domain deg) :
    (toPolynomial c).degree < Fintype.card ι :=
  Lagrange.degree_interpolate_lt _ domain.injective.injOn

/-- The polynomials corresponding to Reed-Solomon codewords are of degree smaller than `deg`. -/
lemma toPolynomial_mem_lt_deg (c : ReedSolomon.code domain deg) :
    toPolynomial c ∈ (degreeLT F deg : Submodule F F[X]) := by
  rcases c with ⟨c, p, hp_deg, rfl⟩
  rcases le_or_gt deg (Fintype.card ι) with hle | hlt
  · -- `p` has degree `< |ι|`, so it is the interpolant of its own values.
    have hp_eq : toPolynomial ⟨evalOnPoints domain p, p, hp_deg, rfl⟩ = p :=
      (Lagrange.eq_interpolate domain.injective.injOn
        ((mem_degreeLT.1 hp_deg).trans_le (WithBot.coe_le_coe.2 hle))).symm
    rwa [hp_eq]
  · -- Otherwise, `deg > |ι|`, and interpolation has degree < |ι| ≤ deg
    exact mem_degreeLT.2 ((degree_toPolynomial_lt_card _).trans (WithBot.coe_lt_coe.2 hlt))

@[simp]
lemma toPolynomial_lt_deg (c : ReedSolomon.code domain deg) :
    (toPolynomial c).degree < deg :=
  mem_degreeLT.1 (toPolynomial_mem_lt_deg c)

@[simp]
lemma toPolynomial_lt_min_deg_card (c : ReedSolomon.code domain deg) :
    (toPolynomial c).degree < min deg (Fintype.card ι) := by
  rcases le_total deg (Fintype.card ι) with h | h
  · rw [min_eq_left h]
    exact toPolynomial_lt_deg c
  · rw [min_eq_right h]
    exact degree_toPolynomial_lt_card c

lemma toPolynomial_evalWord_of_degree_lt
    {p : F[X]} (hp_deg : p.degree < deg) (hdeg : deg ≤ Fintype.card ι)
  {hcode : evalOnPoints domain p ∈ ReedSolomon.code domain deg} :
  toPolynomial ⟨evalOnPoints domain p, hcode⟩ = p :=
  (Lagrange.eq_interpolate domain.injective.injOn
    (hp_deg.trans_le (WithBot.coe_le_coe.2 hdeg))).symm

lemma toPolynomial_eval_at_domain
    {c : ReedSolomon.code domain deg} {i : ι} :
  (toPolynomial c).eval (domain i) = c.1 i :=
  Lagrange.eval_interpolate_at_node _ domain.injective.injOn (Finset.mem_univ i)

omit [DecidableEq ι] in
lemma mem_code_iff_exists_polynomial' {n : ℕ} {α : ι ↪ F} {f : ι → F} :
    f ∈ code α n ↔
    ∃ p : Polynomial F, p.degree < min n (Fintype.card ι) ∧
      f = evalOnPoints α p := by
  classical
  refine ⟨fun h ↦ ⟨toPolynomial ⟨f, h⟩, toPolynomial_lt_min_deg_card _,
    funext fun i ↦ (toPolynomial_eval_at_domain (c := ⟨f, h⟩)).symm⟩, fun ⟨p, hp, hf⟩ ↦
    mem_code_iff_exists_polynomial.2 ⟨p, hp.trans_le (WithBot.coe_le_coe.2 (min_le_left _ _)), hf⟩⟩

/-- The linear map that maps a Reed-Solomon codeword to its associated polynomial of degree less
than `deg`. -/
noncomputable def toPolynomialLT :
  (ReedSolomon.code domain deg) →ₗ[F] (Polynomial.degreeLT F deg) :=
  codRestrict
    (Polynomial.degreeLT F deg)
    toPolynomial
    toPolynomial_mem_lt_deg


variable {F : Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and there exists a subgroup
 `H` in the group of units `Rˣ` and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  (domain : ι ↪ F) where
    H : Subgroup (Units F)
    a           : Units F
    h_coset     : Finset.image domain Finset.univ
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F))
    h_card_pow2 : ∃ k : ℕ, Fintype.card ι = 2 ^ k

end
end ReedSolomon
