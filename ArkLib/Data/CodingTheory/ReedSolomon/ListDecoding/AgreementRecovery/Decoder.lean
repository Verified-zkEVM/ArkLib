/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Correctness
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Batched
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FiniteRepresentation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SampleInterpolation

/-!
# Recovering base-field messages from finite representations

For each pair `(h,C)`, the decoder forms the residuals `C(xᵢ)-yᵢ` modulo `h` and splits
by their gcds. A branch stops after `k` distinct agreements. Those positions determine a
unique polynomial of degree below `k`, so interpolation uses the original base-field
received values even when the representation coefficients lie in a larger field.

The final check is exactly degree and full received-word agreement. It does not test a
differential equation or enumerate roots of the representation modulus. Constructor coverage
is a proof hypothesis; it is never passed to the executable program.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery

open Polynomial JetHornerMachine CompPoly SampleInterpolation

variable {F E : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] {n : ℕ}

/-- Indexed agreement equations for one representation. Keeping the position indices makes
stopped branches usable directly by base-field interpolation. -/
def equations (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (r : FiniteRepresentation E) : List (Fin n × CPolynomial E) :=
  List.ofFn fun i => (i, r.residual (base (domain i)) (base (received i)))

/-- Recover one representation with explicit multiplication and monic-remainder backends.
The backend laws are used in `Batched.run_eq`, so changing a correct backend preserves the
actual messages and their order. -/
def recoverWith (M : CPolynomial.MulContext E) (D : CPolynomial.ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (r : FiniteRepresentation E) : List (List F) :=
  (Batched.run M D k (equations base domain received r) r.modulus).filterMap fun block =>
    checkedCandidate domain received k A block.positions.toFinset

/-- Recover and check the messages using canonical multiplication and remainder-only division. -/
def recover (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (r : FiniteRepresentation E) : List (List F) :=
  recoverWith .naive .remainderOnly base domain received k A r

/-- Correct polynomial backends preserve the complete recovered message list. -/
@[simp]
theorem recoverWith_eq (M : CPolynomial.MulContext E) (D : CPolynomial.ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (r : FiniteRepresentation E) :
    recoverWith M D base domain received k A r = recover base domain received k A r := by
  simp [recover, recoverWith]

/-- Recover every representation and remove repeated fixed-width coefficient vectors. -/
def decode (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (representations : List (FiniteRepresentation E)) : List (List F) :=
  (representations.flatMap (recover base domain received k A)).dedup

/-- Shared decoding with caller-selected, certified polynomial backends. -/
def decodeWith (M : CPolynomial.MulContext E) (D : CPolynomial.ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (representations : List (FiniteRepresentation E)) : List (List F) :=
  (representations.flatMap (recoverWith M D base domain received k A)).dedup

/-- Backend substitution preserves the total decoder function, hence all exactness theorems. -/
@[simp]
theorem decodeWith_eq (M : CPolynomial.MulContext E) (D : CPolynomial.ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (representations : List (FiniteRepresentation E)) :
    decodeWith M D base domain received k A representations =
      decode base domain received k A representations := by
  unfold decodeWith decode
  congr 1
  apply List.flatMap_congr
  intro r _
  exact recoverWith_eq M D base domain received k A r

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The stopped sample contains exactly `k` distinct input positions. -/
theorem stopped_card (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (r : FiniteRepresentation E) (block : Block E (Fin n))
    (hblock : block ∈ run k (equations base domain received r) r.modulus) :
    block.positions.toFinset.card = k := by
  have hindices : ((equations base domain received r).map Prod.fst).Nodup := by
    simp only [equations, List.map_ofFn]
    exact List.nodup_ofFn.mpr Function.injective_id
  have hpositions := run_positions k _ r.modulus hindices block hblock
  rw [List.toFinset_card_of_nodup hpositions.2, hpositions.1]

/-- Every returned vector passes the exact output tests, regardless of constructor coverage. -/
theorem mem_decode_properties (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (representations : List (FiniteRepresentation E))
    (cs : List F) (hcs : cs ∈ decode base domain received k A representations) :
    cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  simp only [decode, List.mem_dedup, List.mem_flatMap] at hcs
  obtain ⟨r, _, hcs⟩ := hcs
  simp only [recover, recoverWith, Batched.run_eq] at hcs
  obtain ⟨block, hblock, hchecked⟩ := List.mem_filterMap.mp hcs
  have hp := checkedCandidate_properties domain received k A block.positions.toFinset
    (stopped_card base domain received k r block hblock) cs hchecked
  exact ⟨hp.1, hp.2.2⟩

/-- Recovery makes at most `deg h` interpolation attempts for one representation. Filtering
can only remove attempts, including attempts associated with unwanted specializations. -/
theorem recover_length_le (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (r : FiniteRepresentation E) :
    (recover base domain received k A r).length ≤ r.modulus.natDegree := by
  rw [recover, recoverWith, Batched.run_eq]
  exact (List.length_filterMap_le _ _).trans
    (split_length_le k (equations base domain received r) ⟨r.modulus, []⟩)

/-- The paper's total representation degree `Δ = ∑ deg h` bounds the number of recovered
messages. This is a finite cardinality bound; arithmetic running time is a separate claim. -/
theorem decode_length_le (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k A : ℕ) (representations : List (FiniteRepresentation E)) :
    (decode base domain received k A representations).length ≤
      (representations.map fun r => r.modulus.natDegree).sum := by
  apply (List.dedup_sublist _).length_le.trans
  rw [List.length_flatMap]
  exact List.sum_le_sum (fun r _ => recover_length_le base domain received k A r)

noncomputable section

variable {L : Type*} [Field L]

omit [BEq F] [LawfulBEq F] in
/-- A covered message reaches a stopped sample consisting entirely of its agreement positions.
The root is used only to prove this path exists; the executable split tree never computes it. -/
theorem exists_stopped_sample (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (r : FiniteRepresentation E) (hr : r.WellFormed k) (θ : L) (p : F[X])
    (hrep : r.Represents ι θ (p.map (ι.comp base)))
    (hagreement : A ≤ Code.agree (evalOnPoints domain p) received) :
    ∃ block ∈ run k (equations base domain received r) r.modulus,
      ∀ i ∈ block.positions, p.eval (domain i) = received i := by
  classical
  let good : Fin n → Prop := fun i => p.eval (domain i) = received i
  have hequations : ∀ row ∈ equations base domain received r,
      row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1 := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    rw [FiniteRepresentation.residual_eq_zero_iff r ι θ hr.1 hrep.1, hrep.2]
    change (p.map (ι.comp base)).eval ((ι.comp base) (domain i)) =
      (ι.comp base) (received i) ↔ _
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact (ι.comp base).injective.eq_iff
  have hcount : (equations base domain received r).countP
      (fun row => decide (good row.1)) = Code.agree (evalOnPoints domain p) received := by
    have hcard := (List.nodup_ofFn.mpr
      (Function.injective_id : Function.Injective (@id (Fin n)))).card_eq_countP (P := good)
    have huniv : (List.ofFn (@id (Fin n))).toFinset = Finset.univ := by
      ext i
      simp
    rw [huniv] at hcard
    have heq : equations base domain received r =
        (List.ofFn (@id (Fin n))).map
          (fun i => (i, r.residual (base (domain i)) (base (received i)))) := by
      simp [equations, List.map_ofFn]
    rw [heq, List.countP_map]
    change (List.ofFn (@id (Fin n))).countP (fun i => decide (good i)) = _
    rw [← hcard]
    congr 1
  obtain ⟨block, hblock, _, hgood⟩ := exists_mem_split_of_enough_agreements
    k (equations base domain received r) ⟨r.modulus, []⟩ ι θ good hr.2.1 hrep.1
    (by simp) hequations (by simpa [hcount] using hAk.trans hagreement)
  exact ⟨block, hblock, hgood⟩

/-- Each covered base-field message is recovered from a stopped block and survives the final
agreement check. The proof does not require every represented specialization to be wanted. -/
theorem exists_mem_decode_of_coverage (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k)
    (hcover : FiniteRepresentation.Covers representations base ι
      {p | p.degree < k ∧ A ≤ Code.agree (evalOnPoints domain p) received})
    (p : F[X]) (hdegree : p.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain p) received) :
    ∃ cs ∈ decode base domain received k A representations, coefficientPolynomial cs = p := by
  obtain ⟨r, hr, θ, hrep⟩ := hcover p ⟨hdegree, hagreement⟩
  obtain ⟨block, hblock, hgood⟩ := exists_stopped_sample base ι domain received k A hAk
    r (hwell r hr) θ p hrep hagreement
  have hcard := stopped_card base domain received k r block hblock
  have hinterp := interpolate_eq_of_agrees_on domain received k block.positions.toFinset
    hcard p hdegree (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood i (List.mem_toFinset.mp hi)⟩)
  have hpoly : coefficientPolynomial
      (sampleCandidate domain received k block.positions.toFinset) = p :=
    (sampleCandidate_polynomial domain received k block.positions.toFinset).trans hinterp
  have hchecked := checkedCandidate_of_agreement domain received k A block.positions.toFinset
    hcard (by simpa [hpoly] using hagreement)
  refine ⟨sampleCandidate domain received k block.positions.toFinset, ?_, hpoly⟩
  simp only [decode, List.mem_dedup, List.mem_flatMap]
  refine ⟨r, hr, ?_⟩
  simp only [recover, recoverWith, Batched.run_eq]
  exact List.mem_filterMap.mpr ⟨block, hblock, hchecked⟩

/-- **Exact recovery from a finite cover.** Each constructor supplies monic squarefree pairs
`(h,C)` covering every message of degree below `k` with at least `A` agreements. The same
executable consumer then returns precisely those messages, as duplicate-free vectors of width
`k`. Extra represented roots and repeated message images are harmless.

The threshold assumption `k ≤ A` supplies the `k` agreeing positions needed for interpolation.
There is no hypothesis that roots lie in the base field, and no root enumeration in `decode`.
-/
theorem decode_exact_of_coverage
    (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k)
    (hcover : FiniteRepresentation.Covers representations base ι
      {p | p.degree < k ∧ A ≤ Code.agree (evalOnPoints domain p) received}) :
    ExactOutput domain received k A
      (decode base domain received k A representations) := by
  apply exactOutput_of_sound_complete
  · exact List.nodup_dedup _
  · exact mem_decode_properties base domain received k A representations
  · exact exists_mem_decode_of_coverage base ι domain received k A hAk
      representations hwell hcover

end
end ReedSolomon.ListDecoding.AgreementRecovery
