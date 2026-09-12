/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Tower
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput

/-!
# Exact recovery inside a tower family

Theorems here trace actual zero/unit splits in both directions. A positive retained tower has a
geometric point; its `k` recorded positions force its represented message to be the base-field
interpolant. Conversely every represented qualifying message follows a split path to `k`
agreements. Constructor coverage then promotes this exact recovery to `ExactOutput`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.Tower

open CompPoly Polynomial Polynomial.JetHornerMachine SampleInterpolation TowerAlgebra

variable {F E L : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] [Field L] {n : ℕ}

/-- A base-field message is represented when one supplied tower has a geometric point with that
message. Geometric points are proof witnesses, never runtime candidate inputs. -/
def RepresentedBy (base : F →+* E) (ι : E →+* L) (k : ℕ)
    (families : List (Component E k)) (p : F[X]) : Prop :=
  ∃ r ∈ families, ∃ u v : L, r.val.Represents ι u v (p.map (ι.comp base))

/-- Exactness within the represented family, before a constructor proves full coverage. -/
def RepresentedExactOutput (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (families : List (Component E k)) (out : List (List F)) : Prop :=
  (out.map coefficientPolynomial).Nodup ∧ out.Nodup ∧
    (∀ p : F[X], p ∈ out.map coefficientPolynomial ↔
      p.degree < k ∧ A ≤ Code.agree (evalOnPoints domain p) received ∧
        RepresentedBy base ι k families p) ∧
    (∀ cs : List F, cs ∈ out ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
          RepresentedBy base ι k families (coefficientPolynomial cs))

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- A split child represents the same message as its parent, and its tag tests that message's
agreement at the current received position. -/
theorem splitAt_represents_sound (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k : ℕ)
    (s : Component E k) (i : Fin n) (child : Bool × Component E k)
    (hc : child ∈ splitAt base domain received k s i) (u v : L) (p : L[X])
    (hp : child.2.val.Represents ι u v p) :
    s.val.Represents ι u v p ∧
      (child.1 = true ↔ p.eval (ι (base (domain i))) = ι (base (received i))) := by
  simp only [splitAt, List.mem_map, List.mem_attach, true_and] at hc
  obtain ⟨out, rfl⟩ := hc
  have hs := splitZeroUnit_point_sound s.val _ s.property out.val out.property ι u v hp.1
  have he := splitZeroUnit_specialize s.val _ s.property out.val out.property ι u v hp.1
  have hrep : s.val.specialize ι u v = p := he.trans hp.2
  refine ⟨⟨hs.1, hrep⟩, ?_⟩
  have ht : out.val.tag.isZero = true ↔ out.val.tag = .zero := by
    cases out.val.tag <;> simp [SplitTag.isZero]
  rw [ht, hs.2, TowerRepresentation.residual_eq_zero_iff, hrep]

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Each represented point follows a child of the executed split with the correct agreement tag.
This is local algebraic coverage, derived from D5 rather than assumed of a candidate generator. -/
theorem splitAt_represents_complete (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k : ℕ)
    (s : Component E k) (i : Fin n) (u v : L) (p : L[X])
    (hp : s.val.Represents ι u v p) :
    ∃ child ∈ splitAt base domain received k s i, child.2.val.Represents ι u v p ∧
      (child.1 = true ↔ p.eval (ι (base (domain i))) = ι (base (received i))) := by
  obtain ⟨out, ho, hpoint, htag⟩ :=
    splitZeroUnit_point_complete s.val _ s.property ι u v hp.1
  let child : Bool × Component E k := (out.tag.isZero,
    ⟨out.tower, splitZeroUnit_wellFormed s.val _ s.property out ho⟩)
  have hc : child ∈ splitAt base domain received k s i := by
    simp only [splitAt, List.mem_map, List.mem_attach, true_and]
    exact ⟨⟨out, ho⟩, rfl⟩
  have he := splitZeroUnit_specialize s.val _ s.property out ho ι u v hpoint
  refine ⟨child, hc, ⟨hpoint, he.symm.trans hp.2⟩, ?_⟩
  change out.tag.isZero = true ↔ _
  have ht : out.tag.isZero = true ↔ out.tag = .zero := by
    cases out.tag <;> simp [SplitTag.isZero]
  rw [ht, htag, TowerRepresentation.residual_eq_zero_iff, hp.2]

omit [BEq F] [LawfulBEq F] in
/-- A wanted point reaches a stopped sample made entirely of its agreement positions. -/
theorem exists_stopped_sample (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (r : Component E k) (u v : L) (p : F[X])
    (hp : r.val.Represents ι u v (p.map (ι.comp base)))
    (hag : A ≤ Code.agree (evalOnPoints domain p) received) :
    ∃ out ∈ ComponentScan.scan (fun _ => true) (splitAt base domain received k) k
      (List.ofFn (@id (Fin n))) ⟨r, []⟩,
      ∀ i ∈ out.positions, p.eval (domain i) = received i := by
  classical
  let good : Unit → Fin n → Prop := fun _ i => p.eval (domain i) = received i
  let point : Component E k → Unit → Prop := fun s _ =>
    s.val.Represents ι u v (p.map (ι.comp base))
  have hstep : ∀ s i θ, point s θ → ∃ child ∈ splitAt base domain received k s i,
      point child.2 θ ∧ (child.1 = true ↔ good θ i) := by
    intro s i θ hs
    obtain ⟨child, hc, hpoint, ht⟩ :=
      splitAt_represents_complete base ι domain received k s i u v _ hs
    refine ⟨child, hc, hpoint, ?_⟩
    rw [ht, Polynomial.eval_map]
    change p.eval₂ (ι.comp base) ((ι.comp base) (domain i)) =
      (ι.comp base) (received i) ↔ _
    rw [Polynomial.eval₂_at_apply]
    exact (ι.comp base).injective.eq_iff
  have hcount : (List.ofFn (@id (Fin n))).countP (fun i => decide (good () i)) =
      Code.agree (evalOnPoints domain p) received := by
    have hcard := (List.nodup_ofFn.mpr
      (Function.injective_id : Function.Injective (@id (Fin n)))).card_eq_countP
      (P := good ())
    have huniv : (List.ofFn (@id (Fin n))).toFinset = Finset.univ := by ext i; simp
    rw [huniv] at hcard
    rw [← hcard]
    rfl
  obtain ⟨out, hout, _, hgood⟩ := ComponentScan.point_complete
    (fun _ => true) (splitAt base domain received k) point good (by intros; rfl) hstep
    k (List.ofFn (@id (Fin n))) ⟨r, []⟩ () hp (by simp)
    (by simpa [hcount] using hAk.trans hag)
  exact ⟨out, hout, hgood⟩

/-- Every qualifying represented message survives interpolation and the final agreement test. -/
theorem exists_mem_recoverAgreement_of_representedBy (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Component E k)) (p : F[X]) (hdegree : p.degree < k)
    (hag : A ≤ Code.agree (evalOnPoints domain p) received)
    (hp : RepresentedBy base ι k families p) :
    ∃ cs ∈ recoverAgreement base domain received k A families,
      coefficientPolynomial cs = p := by
  obtain ⟨r, hr, u, v, hp⟩ := hp
  obtain ⟨out, hout, hgood⟩ := exists_stopped_sample base ι domain received k A hAk r u v p hp hag
  have hblock : out ∈ blocks base domain received k families := by
    rw [blocks_eq]
    exact List.mem_flatMap.mpr ⟨r, hr, hout⟩
  have hcard := stopped_card base domain received k families out hblock
  have hinterp := interpolate_eq_of_agrees_on domain received k out.positions.toFinset
    hcard p hdegree (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood i (List.mem_toFinset.mp hi)⟩)
  have hpoly : coefficientPolynomial
      (sampleCandidate domain received k out.positions.toFinset) = p :=
    (sampleCandidate_polynomial domain received k out.positions.toFinset).trans hinterp
  have hchecked := checkedCandidate_of_agreement domain received k A out.positions.toFinset hcard
    (by simpa only [hpoly] using hag)
  refine ⟨sampleCandidate domain received k out.positions.toFinset, ?_, hpoly⟩
  simp only [recoverAgreement, List.mem_dedup]
  exact List.mem_filterMap.mpr ⟨out, hblock, hchecked⟩

/-- Every returned message is genuinely represented by an input tower. Positive component
sizes provide proof-only geometric roots, and `k` agreements identify the interpolation result. -/
theorem representedBy_of_mem_recoverAgreement [IsAlgClosed L]
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (families : List (Component E k)) (cs : List F)
    (hcs : cs ∈ recoverAgreement base domain received k A families) :
    RepresentedBy base ι k families (coefficientPolynomial cs) := by
  simp only [recoverAgreement, List.mem_dedup, List.mem_filterMap] at hcs
  obtain ⟨out, hout, hc⟩ := hcs
  have hcard := stopped_card base domain received k families out hout
  have hproperties := checkedCandidate_properties domain received k A
    out.positions.toFinset hcard cs hc
  rw [blocks_eq] at hout
  obtain ⟨r, hr, hout⟩ := List.mem_flatMap.mp hout
  obtain ⟨u, v, hpoint⟩ := out.component.val.exists_point ι out.component.property
  let message := out.component.val.specialize ι u v
  let point : Component E k → Unit → Prop := fun s _ => s.val.Represents ι u v message
  let good : Unit → Fin n → Prop := fun _ i =>
    message.eval (ι (base (domain i))) = ι (base (received i))
  have hstep : ∀ s i child θ, child ∈ splitAt base domain received k s i →
      point child.2 θ → point s θ ∧ (child.1 = true → good θ i) := by
    intro s i child θ hchild hp
    have hs := splitAt_represents_sound base ι domain received k s i child hchild u v message hp
    exact ⟨hs.1, hs.2.mp⟩
  have htrace := ComponentScan.point_sound (fun _ => true) (splitAt base domain received k)
    point good hstep k (List.ofFn (@id (Fin n))) ⟨r, []⟩ out () hout ⟨hpoint, rfl⟩
  have heq : message = (coefficientPolynomial cs).map (ι.comp base) := by
    apply out.component.val.specialize_eq_base_map_of_shared_agreements base ι u v
      out.positions.toFinset domain received domain.injective.injOn
    · exact out.component.property.2.2.2.2.2.2.2.1.trans hcard.symm
    · simpa only [hcard] using hproperties.2.2.1
    · intro i hi
      rw [hproperties.2.1, Lagrange.eval_interpolate_at_node received domain.injective.injOn hi]
    · intro i hi
      exact (htrace.2 i (List.mem_toFinset.mp hi)).resolve_left (by simp)
  exact ⟨r, hr, u, v, htrace.1.1, htrace.1.2.trans heq⟩

/-- Recovery returns exactly the fixed-width vectors represented by the supplied tower family
that pass the full received-word agreement test. -/
theorem mem_recoverAgreement_iff [IsAlgClosed L]
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (families : List (Component E k)) (cs : List F) :
    cs ∈ recoverAgreement base domain received k A families ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
          RepresentedBy base ι k families (coefficientPolynomial cs) := by
  constructor
  · intro hcs
    have hp := mem_recoverAgreement_properties base domain received k A families cs hcs
    exact ⟨hp.1, hp.2.1, hp.2.2,
      representedBy_of_mem_recoverAgreement base ι domain received k A families cs hcs⟩
  · rintro ⟨hl, hd, ha, hr⟩
    obtain ⟨candidate, hc, he⟩ := exists_mem_recoverAgreement_of_representedBy
      base ι domain received k A hAk families (coefficientPolynomial cs) hd ha hr
    have hcl := (mem_recoverAgreement_properties base domain received k A families candidate hc).1
    have heq : candidate = cs := coefficientVectors_eq (hcl.trans hl.symm) he
    rwa [← heq]

/-- `RecoverAgreement` is exact in both directions within the concrete finite tower family.
Duplicate parameter points and duplicate message images cause no duplicate physical outputs. -/
theorem recoverAgreement_represented_exact [IsAlgClosed L]
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (families : List (Component E k)) :
    RepresentedExactOutput base ι domain received k A families
      (recoverAgreement base domain received k A families) := by
  have hvector := mem_recoverAgreement_iff base ι domain received k A hAk families
  have hnodup : (recoverAgreement base domain received k A families).Nodup := List.nodup_dedup _
  refine ⟨?_, hnodup, ?_, hvector⟩
  · apply hnodup.map_on
    intro xs hxs ys hys heq
    exact coefficientVectors_eq (((hvector xs).mp hxs).1.trans ((hvector ys).mp hys).1.symm) heq
  · intro p
    constructor
    · intro hp
      obtain ⟨cs, hc, rfl⟩ := List.mem_map.mp hp
      exact ((hvector cs).mp hc).2
    · rintro ⟨hd, ha, hr⟩
      obtain ⟨cs, hc, he⟩ := exists_mem_recoverAgreement_of_representedBy
        base ι domain received k A hAk families p hd ha hr
      exact List.mem_map.mpr ⟨cs, hc, he⟩

/-- Concrete constructor coverage promotes tower recovery to the existing complete-list
`ExactOutput` contract. Coverage is a theorem obligation of later constructor milestones. -/
theorem recoverAgreement_exact_of_coverage
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (families : List (Component E k))
    (hcover : ∀ p : F[X], p.degree < k →
      A ≤ Code.agree (evalOnPoints domain p) received → RepresentedBy base ι k families p) :
    ExactOutput domain received k A (recoverAgreement base domain received k A families) := by
  apply exactOutput_of_sound_complete
  · exact List.nodup_dedup _
  · exact mem_recoverAgreement_properties base domain received k A families
  · intro p hd ha
    exact exists_mem_recoverAgreement_of_representedBy base ι domain received k A hAk
      families p hd ha (hcover p hd ha)

end ReedSolomon.ListDecoding.AgreementRecovery.Tower
