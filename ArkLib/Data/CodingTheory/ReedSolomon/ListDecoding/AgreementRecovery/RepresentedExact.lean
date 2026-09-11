/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exact agreement recovery inside a represented candidate family

Agreement recovery is exact even before a constructor proves that its finite representations
cover every wanted message. Relative to any common algebraically closed extension, it returns
exactly the represented base-field polynomials that have degree below the requested width and
pass the full received-word agreement test.

The reverse direction is substantive: every stopped positive-degree block has a root, and that
root is traced backwards through the actual gcd split tree. Roots in a zero child satisfy the
tested residual, while roots in a complementary child do not. The recorded positions therefore
identify the recovered interpolant with a specialization of the supplied representation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery

open CompPoly Polynomial JetHornerMachine SampleInterpolation

variable {F E L index : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] [Field L] [IsAlgClosed L] {n : ℕ}

/-! ### Root semantics of stopped blocks -/

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [IsAlgClosed L] in
/-- A root of an emitted block traces back to a root of the input block. Every newly recorded
position satisfies its corresponding equation at that root; positions present before the call
are reported separately. -/
theorem root_and_recorded_of_mem_split (k : ℕ)
    (equations : List (index × CPolynomial E)) (block out : Block E index)
    (ι : E →+* L) (θ : L) (good : index → Prop)
    (hsquarefree : Squarefree block.factor.toPoly)
    (hequations : ∀ row ∈ equations, row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1)
    (hout : out ∈ split k equations block)
    (hroot : out.factor.toPoly.eval₂ ι θ = 0) :
    block.factor.toPoly.eval₂ ι θ = 0 ∧
      ∀ i ∈ out.positions, i ∈ block.positions ∨ good i := by
  induction equations generalizing block out with
  | nil =>
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        exact ⟨hroot, fun i hi ↦ Or.inl hi⟩
      · simp at hout
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      have hrest : ∀ row ∈ rest, row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1 := by
        intro row hrow
        exact hequations row (List.mem_cons_of_mem _ hrow)
      have hcurrent : e.toPoly.eval₂ ι θ = 0 ↔ good i :=
        hequations (i, e) (by simp)
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        exact ⟨hroot, fun j hj ↦ Or.inl hj⟩
      · rcases List.mem_append.mp hout with hleft | hright
        · have hchild := ih
            ⟨CPolynomial.gcdFactor block.factor e, i :: block.positions⟩ out
            (CPolynomial.gcdFactor_squarefree hsquarefree) hrest hleft hroot
          have hsplit := (CPolynomial.eval₂_gcdFactor_eq_zero_iff_left_right
            ι θ block.factor e).mp hchild.1
          refine ⟨hsplit.1, ?_⟩
          intro j hj
          rcases hchild.2 j hj with hrecorded | hgood
          · simp only [List.mem_cons] at hrecorded
            rcases hrecorded with rfl | hold
            · exact Or.inr (hcurrent.mp hsplit.2)
            · exact Or.inl hold
          · exact Or.inr hgood
        · have hne : block.factor ≠ 0 :=
            (CPolynomial.toPoly_eq_zero_iff block.factor).not.mp hsquarefree.ne_zero
          have hchild := ih
            ⟨CPolynomial.gcdComplement block.factor e, block.positions⟩ out
            (CPolynomial.gcdComplement_squarefree hne hsquarefree) hrest hright hroot
          have hsplit :=
            (CPolynomial.eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
              ι θ hne hsquarefree).mp hchild.1
          exact ⟨hsplit.1, hchild.2⟩

/-! ### The represented family -/

/-- A base-field polynomial belongs to the candidate family represented over `L` when it is the
specialization of one supplied finite representation at a root of that representation's modulus.
The extension `L` need not be the coefficient field's canonical algebraic closure. -/
def RepresentedBy (base : F →+* E) (ι : E →+* L)
    (representations : List (FiniteRepresentation E)) (p : F[X]) : Prop :=
  ∃ r ∈ representations, ∃ θ : L, r.Represents ι θ (p.map (ι.comp base))

/-- Exact output restricted to a finite represented family. It retains both duplicate-freedom
clauses and both physical-vector and mathematical-polynomial membership presentations from
`ExactOutput`. -/
def RepresentedExactOutput (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (representations : List (FiniteRepresentation E)) (out : List (List F)) : Prop :=
  (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
    (∀ p : F[X], p ∈ out.map coefficientPolynomial ↔
      p.degree < k ∧ A ≤ Code.agree (evalOnPoints domain p) received ∧
        RepresentedBy base ι representations p) ∧
    (∀ cs : List F, cs ∈ out ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
          RepresentedBy base ι representations (coefficientPolynomial cs))

/-! ### Soundness into the represented family -/

/-- Every recovered candidate comes from an actual root of the representation whose split tree
emitted its interpolation sample. -/
theorem representedBy_of_mem_decode (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k)
    (cs : List F) (hcs : cs ∈ decode base domain received k A representations) :
    RepresentedBy base ι representations (coefficientPolynomial cs) := by
  simp only [decode, List.mem_dedup, List.mem_flatMap] at hcs
  obtain ⟨r, hr, hcs⟩ := hcs
  simp only [recover, recoverWith, Batched.run_eq] at hcs
  obtain ⟨block, hblock, hchecked⟩ := List.mem_filterMap.mp hcs
  have hpositive := split_factor_natDegree_pos k (equations base domain received r)
    ⟨r.modulus, []⟩ block hblock
  have hdegree : block.factor.toPoly.degree ≠ 0 := by
    apply ne_of_gt
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    simpa only [CPolynomial.natDegree_toPoly] using hpositive
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective
    ι ι.injective block.factor.toPoly hdegree
  let good : Fin n → Prop := fun i ↦
    (r.residual (base (domain i)) (base (received i))).toPoly.eval₂ ι θ = 0
  have hequations : ∀ row ∈ equations base domain received r,
      row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1 := by
    intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    rfl
  have htrace := root_and_recorded_of_mem_split k (equations base domain received r)
    ⟨r.modulus, []⟩ block ι θ good (hwell r hr).2.1 hequations hblock hθ
  have hcard := stopped_card base domain received k r block hblock
  have hproperties := checkedCandidate_properties domain received k A
    block.positions.toFinset hcard cs hchecked
  refine ⟨r, hr, θ, htrace.1, ?_⟩
  apply FiniteRepresentation.specialize_eq_base_map_of_shared_agreements
    r base ι θ block.positions.toFinset domain received domain.injective.injOn
  · exact (hwell r hr).2.2.1.trans hcard.symm
  · simpa only [hcard] using hproperties.2.2.1
  · intro i hi
    rw [hproperties.2.1, Lagrange.eval_interpolate_at_node received
      domain.injective.injOn hi]
  · intro i hi
    apply (FiniteRepresentation.residual_eq_zero_iff r ι θ
      (hwell r hr).1 htrace.1 _ _).mp
    exact htrace.2 i (List.mem_toFinset.mp hi) |>.resolve_left (by simp)

/-! ### Completeness inside the represented family -/

omit [IsAlgClosed L] in
/-- Every represented qualifying polynomial reaches a stopped block and is returned. This is
pointwise represented-family completeness, with no global coverage assumption. -/
theorem exists_mem_decode_of_representedBy (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k)
    (p : F[X]) (hdegree : p.degree < k)
    (hagreement : A ≤ Code.agree (evalOnPoints domain p) received)
    (hrepresented : RepresentedBy base ι representations p) :
    ∃ cs ∈ decode base domain received k A representations,
      coefficientPolynomial cs = p := by
  obtain ⟨r, hr, θ, hrep⟩ := hrepresented
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
    hcard (by simpa only [hpoly] using hagreement)
  refine ⟨sampleCandidate domain received k block.positions.toFinset, ?_, hpoly⟩
  simp only [decode, List.mem_dedup, List.mem_flatMap]
  refine ⟨r, hr, ?_⟩
  simp only [recover, recoverWith, Batched.run_eq]
  exact List.mem_filterMap.mpr ⟨block, hblock, hchecked⟩

/-- Physical-vector membership in agreement recovery is exactly qualification plus membership in
the represented candidate family. -/
theorem mem_decode_iff_representedBy (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k) (cs : List F) :
    cs ∈ decode base domain received k A representations ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
          RepresentedBy base ι representations (coefficientPolynomial cs) := by
  constructor
  · intro hcs
    have hp := mem_decode_properties base domain received k A representations cs hcs
    exact ⟨hp.1, hp.2.1, hp.2.2,
      representedBy_of_mem_decode base ι domain received k A representations hwell cs hcs⟩
  · rintro ⟨hlength, hdegree, hagreement, hrepresented⟩
    obtain ⟨candidate, hcandidate, hpolynomial⟩ := exists_mem_decode_of_representedBy
      base ι domain received k A hAk representations hwell (coefficientPolynomial cs)
      hdegree hagreement hrepresented
    have hcandLength :=
      (mem_decode_properties base domain received k A representations candidate hcandidate).1
    have heq : candidate = cs :=
      coefficientVectors_eq (hcandLength.trans hlength.symm) hpolynomial
    rwa [← heq]

/-- Agreement recovery is exact relative to the family encoded by the supplied finite
representations. No constructor coverage premise occurs in this theorem. -/
theorem decode_represented_exact (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (representations : List (FiniteRepresentation E))
    (hwell : ∀ r ∈ representations, r.WellFormed k) :
    RepresentedExactOutput base ι domain received k A representations
      (decode base domain received k A representations) := by
  let out := decode base domain received k A representations
  have hvector := mem_decode_iff_representedBy base ι domain received k A hAk
    representations hwell
  have hnodup : out.Nodup := List.nodup_dedup _
  have hpolyNodup : (out.map coefficientPolynomial).Nodup := by
    apply hnodup.map_on
    intro xs hxs ys hys hpoly
    exact coefficientVectors_eq
      (((hvector xs).mp hxs).1.trans ((hvector ys).mp hys).1.symm) hpoly
  refine ⟨hpolyNodup, hnodup, ?_, hvector⟩
  intro p
  constructor
  · intro hp
    obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hp
    exact ((hvector cs).mp hcs).2
  · rintro ⟨hdegree, hagreement, hrepresented⟩
    obtain ⟨cs, hcs, hcsPolynomial⟩ := exists_mem_decode_of_representedBy
      base ι domain received k A hAk representations hwell p hdegree hagreement hrepresented
    exact List.mem_map.mpr ⟨cs, hcs, hcsPolynomial⟩

omit [BEq F] [LawfulBEq F] [IsAlgClosed L] in
/-- If the represented family covers all qualifying messages, represented exactness specializes
to the ordinary full-list `ExactOutput` contract. -/
theorem RepresentedExactOutput.toExactOutput
    {base : F →+* E} {ι : E →+* L} {domain : Fin n ↪ F} {received : Fin n → F}
    {k A : ℕ} {representations : List (FiniteRepresentation E)} {out : List (List F)}
    (hexact : RepresentedExactOutput base ι domain received k A representations out)
    (hcover : ∀ p : F[X], p.degree < k →
      A ≤ Code.agree (evalOnPoints domain p) received →
      RepresentedBy base ι representations p) :
    ExactOutput domain received k A out := by
  refine ⟨hexact.1, hexact.2.1, ?_, ?_⟩
  · intro p
    rw [hexact.2.2.1]
    constructor
    · rintro ⟨hdegree, hagreement, _⟩
      exact ⟨hdegree, hagreement⟩
    · rintro ⟨hdegree, hagreement⟩
      exact ⟨hdegree, hagreement, hcover p hdegree hagreement⟩
  · intro cs
    rw [hexact.2.2.2]
    constructor
    · rintro ⟨hlength, hdegree, hagreement, _⟩
      exact ⟨hlength, hdegree, hagreement⟩
    · rintro ⟨hlength, hdegree, hagreement⟩
      exact ⟨hlength, hdegree, hagreement,
        hcover (coefficientPolynomial cs) hdegree hagreement⟩

end ReedSolomon.ListDecoding.AgreementRecovery
