/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.CandidatePool
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!
# Executable square-row enumeration and the full candidate pool

The finite producer in this file is independent of a polynomial representation. Given a supplied
computable initial row and pool, it enumerates every `r`-element subset of the pool labels and
forms the resulting `(r+1)`-row square systems in the ambient label order. The semantic
Reed--Solomon pool has one
agreement row for every received position and every coefficient-tail row from `k` through `K-1`.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SquareSystems

open MvPolynomial

/-- The square system formed from an initial row and `r` distinctly selected pool rows. -/
def squareSystemRows {P ι : Type*} {r : ℕ} (initial : P) (pool : ι → P)
    (selected : Fin r ↪ ι) : Fin (r + 1) → P :=
  Fin.cases initial (fun j ↦ pool (selected j))

/-- All `r`-element subsets of a finite row-label pool. -/
def rowSubsets (ι : Type*) [Fintype ι] [DecidableEq ι] (r : ℕ) :
    Finset (Finset ι) :=
  Finset.univ.powersetCard r

@[simp]
theorem mem_rowSubsets_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (selected : Finset ι) :
    selected ∈ rowSubsets ι r ↔ selected.card = r := by
  simp [rowSubsets]

/-- Canonical increasing enumeration of a subset with the requested size. -/
def rowSubsetEmbedding {ι : Type*} [LinearOrder ι] {r : ℕ} (selected : Finset ι)
    (hcard : selected.card = r) : Fin r ↪ ι :=
  (selected.orderEmbOfFin hcard).toEmbedding

theorem card_map_univ_embedding {ι : Type*} {r : ℕ}
    (selected : Fin r ↪ ι) : (Finset.univ.map selected).card = r := by
  classical
  simp

/-- Materialize every square system over a supplied computable row representation. Duplicate
systems caused by coincident rows are removed by `Finset.image`. -/
def enumerateSquareSystems {P ι : Type*} [DecidableEq P] [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) : Finset (Fin (r + 1) → P) :=
  (rowSubsets ι r).attach.image fun selected : {s // s ∈ rowSubsets ι r} ↦
    squareSystemRows initial pool
      (rowSubsetEmbedding selected.1 ((mem_rowSubsets_iff selected.1).mp selected.2))

theorem squareSystemRows_mem_enumerate {P ι : Type*} [DecidableEq P]
    [Fintype ι] [LinearOrder ι] {r : ℕ} (initial : P) (pool : ι → P)
    (selected : Finset ι) (hselected : selected.card = r) :
    squareSystemRows initial pool (rowSubsetEmbedding selected hselected) ∈
      enumerateSquareSystems r initial pool := by
  apply Finset.mem_image.mpr
  let selected' : {s // s ∈ rowSubsets ι r} :=
    ⟨selected, (mem_rowSubsets_iff selected).mpr hselected⟩
  exact ⟨selected', Finset.mem_attach _ _, rfl⟩

/-- Reordering an injective selected coordinate family into the canonical order of its underlying
subset preserves injectivity. -/
theorem rowSubsetEmbedding_preserves_injective {F V ι : Type*} [Field F]
    [AddCommGroup V] [Module F V] [LinearOrder ι] {r : ℕ}
    (normal : V →ₗ[F] F) (pool : V →ₗ[F] (ι → F)) (selected : Fin r ↪ ι)
    (hinjective : Function.Injective (normalSelectedMap normal pool selected)) :
    Function.Injective
      (normalSelectedMap normal pool
        (rowSubsetEmbedding (Finset.univ.map selected) (card_map_univ_embedding selected))) := by
  intro direction direction' hequal
  apply hinjective
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hequal
    exact hfirst
  · funext j
    let rows : Finset ι := Finset.univ.map selected
    have hcard : rows.card = r := card_map_univ_embedding selected
    have hjmem : selected j ∈ rows := by
      simp [rows]
    have hjrange : selected j ∈ Set.range
        (rows.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact hjmem
    obtain ⟨i, hi⟩ := hjrange
    have hrow := congrFun (congrArg Prod.snd hequal) i
    change pool direction
        (rowSubsetEmbedding rows hcard i) =
      pool direction' (rowSubsetEmbedding rows hcard i) at hrow
    change rows.orderEmbOfFin hcard i = selected j at hi
    change pool direction (selected j) = pool direction' (selected j)
    rw [← hi]
    exact hrow

variable {F : Type*} [Field F] {r : ℕ}

/-- The full paper pool: all `n` received-position equations and the `K-k` coefficient tails. -/
noncomputable def fullCandidatePoolEquation (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) :
    Fin n ⊕ Fin (K - k) → MvPolynomial (Fin (r + 1)) F
  | Sum.inl i => taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  | Sum.inr j => commonTaylorNumerator center Q K (tailIndex hk j) (τ := τ)

/-- Formal differential of the full received-position-and-tail pool. -/
noncomputable def fullCandidatePoolDifferential (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) (jet : Fin (r + 1) → F) :
    (Fin (r + 1) → F) →ₗ[F] (Fin n ⊕ Fin (K - k) → F) :=
  LinearMap.pi fun equation ↦
    mvPolynomialDifferential jet
      (fullCandidatePoolEquation center Q K k n τ hk domain received equation)

/-- The inclusion of the first `k` indices into `Fin A`. -/
def finEmbeddingOfLE {k A : ℕ} (hkA : k ≤ A) : Fin k ↪ Fin A where
  toFun i := ⟨i, i.isLt.trans_le hkA⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin A => x.val) hij

/-- Embed a chosen set of `k` agreeing positions into the full agreement-and-tail pool. -/
def agreementPoolEmbedding {K k n : ℕ} (_hk : k ≤ K) (positions : Fin k ↪ Fin n) :
    Fin k ⊕ Fin (K - k) ↪ Fin n ⊕ Fin (K - k) where
  toFun := Sum.map positions id
  inj' := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (positions.injective (Sum.inl.inj hxy))
        | inr j => simp at hxy
    | inr i =>
        cases y with
        | inl j => simp at hxy
        | inr j => exact congrArg Sum.inr (Sum.inr.inj hxy)

@[simp]
theorem fullCandidatePoolEquation_agreementPoolEmbedding (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) (positions : Fin k ↪ Fin n)
    (equation : Fin k ⊕ Fin (K - k)) :
    fullCandidatePoolEquation center Q K k n τ hk domain received
        (agreementPoolEmbedding hk positions equation) =
      candidatePoolEquation center Q K k τ hk (positions.trans domain)
        (fun i => received (positions i)) equation := by
  cases equation <;> rfl

@[simp]
theorem fullCandidatePoolDifferential_agreementPoolEmbedding (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) (positions : Fin k ↪ Fin n)
    (jet direction : Fin (r + 1) → F) (equation : Fin k ⊕ Fin (K - k)) :
    fullCandidatePoolDifferential center Q K k n τ hk domain received jet direction
        (agreementPoolEmbedding hk positions equation) =
      candidatePoolDifferential center Q K k τ hk (positions.trans domain)
        (fun i => received (positions i)) jet direction equation := by
  change mvPolynomialDifferential jet
      (fullCandidatePoolEquation center Q K k n τ hk domain received
        (agreementPoolEmbedding hk positions equation)) direction =
    mvPolynomialDifferential jet
      (candidatePoolEquation center Q K k τ hk (positions.trans domain)
        (fun i => received (positions i)) equation) direction
  rw [fullCandidatePoolEquation_agreementPoolEmbedding]

/-- Common zeros of a selected agreement-and-tail system remain zeros after embedding its labels
in the full received-position-and-tail pool. -/
theorem squareSystemRows_agreementPoolEmbedding_zero (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) (positions : Fin k ↪ Fin n)
    (jet : Fin (r + 1) → F) (selected : Fin r ↪ (Fin k ⊕ Fin (K - k)))
    (hinitial : aeval jet (initialJetEquation center Q) = 0)
    (hpool : ∀ equation, aeval jet
      (candidatePoolEquation center Q K k τ hk (positions.trans domain)
        (fun i => received (positions i)) equation) = 0) :
    ∀ i, aeval jet
      (squareSystemRows (initialJetEquation center Q)
        (fullCandidatePoolEquation center Q K k n τ hk domain received)
        (selected.trans (agreementPoolEmbedding hk positions)) i) = 0 := by
  intro i
  refine Fin.cases hinitial (fun j => ?_) i
  change aeval jet
    (fullCandidatePoolEquation center Q K k n τ hk domain received
      (agreementPoolEmbedding hk positions (selected j))) = 0
  rw [fullCandidatePoolEquation_agreementPoolEmbedding]
  exact hpool (selected j)

/-- Injectivity of selected agreement-and-tail rows is preserved by their inclusion in the full
received-position-and-tail pool. -/
theorem normalSelectedMap_agreementPoolEmbedding_injective (center : F)
    (Q : DifferentialPolynomial F r) (K k n τ : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) (positions : Fin k ↪ Fin n)
    (jet : Fin (r + 1) → F) (selected : Fin r ↪ (Fin k ⊕ Fin (K - k)))
    (hinjective : Function.Injective
      (normalSelectedMap (initialJetDifferential center Q jet)
        (candidatePoolDifferential center Q K k τ hk (positions.trans domain)
          (fun i => received (positions i)) jet) selected)) :
    Function.Injective
      (normalSelectedMap (initialJetDifferential center Q jet)
        (fullCandidatePoolDifferential center Q K k n τ hk domain received jet)
        (selected.trans (agreementPoolEmbedding hk positions))) := by
  intro direction direction' hequal
  apply hinjective
  apply Prod.ext
  · have hfirst := congrArg Prod.fst hequal
    change initialJetDifferential center Q jet direction =
      initialJetDifferential center Q jet direction' at hfirst
    exact hfirst
  · funext j
    have hrow := congrFun (congrArg Prod.snd hequal) j
    change fullCandidatePoolDifferential center Q K k n τ hk domain received jet direction
        (agreementPoolEmbedding hk positions (selected j)) =
      fullCandidatePoolDifferential center Q K k n τ hk domain received jet direction'
        (agreementPoolEmbedding hk positions (selected j)) at hrow
    rw [fullCandidatePoolDifferential_agreementPoolEmbedding,
      fullCandidatePoolDifferential_agreementPoolEmbedding] at hrow
    exact hrow

/-- If `A >= k` received positions agree with a wanted candidate, some `r` distinct labels in the
full `n`-position-and-tail pool capture it with injective square differential. -/
theorem exists_fullCandidateSquareRows_at_solution (center : F)
    (Q : DifferentialPolynomial F r) (K k n A τ : ℕ) (hK : r < K) (hk : k ≤ K)
    (hkA : k ≤ A) (hτ : TaylorExponentSufficient r K τ) (domain : Fin n ↪ F)
    (received : Fin n → F) (agreementPositions : Fin A ↪ Fin n) (P : Polynomial F)
    (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k)
    (hagreement : ∀ i, P.eval (domain (agreementPositions i)) =
      received (agreementPositions i)) :
    ∃ selected : Fin r ↪ (Fin n ⊕ Fin (K - k)),
      (∀ i, aeval (polynomialJet center P)
        (squareSystemRows (initialJetEquation center Q)
          (fullCandidatePoolEquation center Q K k n τ hk domain received) selected i) = 0) ∧
      Function.Injective
        (normalSelectedMap
          (initialJetDifferential center Q (polynomialJet center P))
          (fullCandidatePoolDifferential center Q K k n τ hk domain received
            (polynomialJet center P)) selected) := by
  let firstPositions : Fin k ↪ Fin n :=
    (finEmbeddingOfLE hkA).trans agreementPositions
  have hfirstAgreement : ∀ i, P.eval (domain (firstPositions i)) =
      received (firstPositions i) := by
    intro i
    exact hagreement (finEmbeddingOfLE hkA i)
  obtain ⟨selected, hinitial, hpool, hinjective⟩ :=
    exists_candidateSquareRows_at_solution center Q K k τ hK hk hτ
      (firstPositions.trans domain) (fun i ↦ received (firstPositions i)) P
      hsolution hseparant hbinomial hdegree hfirstAgreement
  let fullSelected : Fin r ↪ (Fin n ⊕ Fin (K - k)) :=
    selected.trans (agreementPoolEmbedding hk firstPositions)
  refine ⟨fullSelected, ?_, ?_⟩
  · exact squareSystemRows_agreementPoolEmbedding_zero center Q K k n τ hk domain received
      firstPositions (polynomialJet center P) selected hinitial hpool
  · exact normalSelectedMap_agreementPoolEmbedding_injective center Q K k n τ hk domain received
      firstPositions (polynomialJet center P) selected hinjective

/-- Formal Jacobian matrix of a square multivariate polynomial system. -/
noncomputable def formalJacobian {s : ℕ} (point : Fin s → F)
    (equations : Fin s → MvPolynomial (Fin s) F) : Matrix (Fin s) (Fin s) F :=
  fun i j ↦ aeval point (pderiv j (equations i))

/-- Injectivity of the formal square differential is exactly the nonvanishing determinant
condition required by the square-capture argument. -/
theorem formalJacobian_det_ne_zero_of_injective {s : ℕ} (point : Fin s → F)
    (equations : Fin s → MvPolynomial (Fin s) F)
    (hinjective : Function.Injective
      (LinearMap.pi fun i ↦ mvPolynomialDifferential point (equations i))) :
    (formalJacobian point equations).det ≠ 0 := by
  have hmulVec : Function.Injective (formalJacobian point equations).mulVec := by
    intro direction direction' hequal
    apply hinjective
    funext i
    have hi := congrFun hequal i
    simpa [formalJacobian, Matrix.mulVec, dotProduct, mvPolynomialDifferential,
      mul_comm] using hi
  have hunit : IsUnit (formalJacobian point equations) :=
    Matrix.mulVec_injective_iff_isUnit.mp hmulVec
  exact ((formalJacobian point equations).isUnit_iff_isUnit_det.mp hunit).ne_zero

/-- The product-indexed initial-plus-selected differential used in row selection yields a literal
square system with nonzero formal Jacobian determinant. -/
theorem formalJacobian_squareSystemRows_ne_zero {ι : Type*}
    (point : Fin (r + 1) → F)
    (initial : MvPolynomial (Fin (r + 1)) F)
    (pool : ι → MvPolynomial (Fin (r + 1)) F) (selected : Fin r ↪ ι)
    (hinjective : Function.Injective
      (normalSelectedMap (mvPolynomialDifferential point initial)
        (LinearMap.pi fun i ↦ mvPolynomialDifferential point (pool i)) selected)) :
    (formalJacobian point (squareSystemRows initial pool selected)).det ≠ 0 := by
  apply formalJacobian_det_ne_zero_of_injective
  intro direction direction' hequal
  apply hinjective
  apply Prod.ext
  · have hzero := congrFun hequal 0
    exact hzero
  · funext j
    have hsucc := congrFun hequal j.succ
    exact hsucc

local instance sumFinLinearOrder (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- Full executable-family coverage. From any `A >= k` agreeing positions, one emitted
`r`-subset system contains the candidate as a common zero with nonzero Jacobian determinant.
The enumeration itself is computable whenever its supplied polynomial rows are computable. -/
theorem exists_emittedCandidateSquareSystem [DecidableEq F] (center : F)
    (Q : DifferentialPolynomial F r) (K k n A τ : ℕ) (hK : r < K) (hk : k ≤ K)
    (hkA : k ≤ A) (hτ : TaylorExponentSufficient r K τ) (domain : Fin n ↪ F)
    (received : Fin n → F) (agreementPositions : Fin A ↪ Fin n) (P : Polynomial F)
    (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k)
    (hagreement : ∀ i, P.eval (domain (agreementPositions i)) =
      received (agreementPositions i)) :
    ∃ selected : Finset (Fin n ⊕ Fin (K - k)),
      ∃ hselected : selected.card = r,
        let rows := squareSystemRows (initialJetEquation center Q)
          (fullCandidatePoolEquation center Q K k n τ hk domain received)
          (rowSubsetEmbedding selected hselected)
        (∀ i, aeval (polynomialJet center P) (rows i) = 0) ∧
          rows ∈ enumerateSquareSystems r (initialJetEquation center Q)
            (fullCandidatePoolEquation center Q K k n τ hk domain received) ∧
          (formalJacobian (polynomialJet center P) rows).det ≠ 0 := by
  obtain ⟨selected, hzero, hinjective⟩ :=
    exists_fullCandidateSquareRows_at_solution center Q K k n A τ hK hk hkA hτ
      domain received agreementPositions P hsolution hseparant hbinomial hdegree hagreement
  let selectedSet : Finset (Fin n ⊕ Fin (K - k)) := Finset.univ.map selected
  have hcard : selectedSet.card = r := card_map_univ_embedding selected
  let canonical := rowSubsetEmbedding selectedSet hcard
  have hcanonicalInjective : Function.Injective
      (normalSelectedMap
        (initialJetDifferential center Q (polynomialJet center P))
        (fullCandidatePoolDifferential center Q K k n τ hk domain received
          (polynomialJet center P)) canonical) := by
    exact rowSubsetEmbedding_preserves_injective _ _ selected hinjective
  refine ⟨selectedSet, hcard, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases (hzero 0) (fun j ↦ ?_) i
    have hjmem : canonical j ∈ selectedSet := by
      exact Finset.orderEmbOfFin_mem selectedSet hcard j
    dsimp only [selectedSet] at hjmem
    rw [Finset.mem_map] at hjmem
    obtain ⟨source, _, hsource⟩ := hjmem
    change aeval (polynomialJet center P)
      (fullCandidatePoolEquation center Q K k n τ hk domain received (canonical j)) = 0
    rw [← hsource]
    simpa only [squareSystemRows, Fin.cases_succ] using hzero source.succ
  · exact squareSystemRows_mem_enumerate _ _ selectedSet hcard
  · apply formalJacobian_squareSystemRows_ne_zero
    simpa only [initialJetDifferential, fullCandidatePoolDifferential] using
      hcanonicalInjective

end ReedSolomon.HiddenDerivative.SquareSystems
