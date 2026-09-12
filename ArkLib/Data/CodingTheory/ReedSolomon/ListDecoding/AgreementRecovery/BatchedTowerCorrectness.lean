/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.BatchedTower
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerCorrectness

/-!
# Correctness of batched tower agreement recovery

The executable row operation in `BatchedTower` uses one product tree for the common ancestor
residual. The first part of this file proves that the ordered batch is exactly the collection scan
whose per-component residual is the corresponding canonical base restriction followed by local
fiber reduction. The second part proves the same represented-family exactness contract as the
existing tower scan.

Because the two scans may partition their internal tower components differently, the final
refinement theorem intentionally states membership equivalence of deduplicated physical outputs
rather than list equality. No output-order claim or asymptotic running-time claim is made.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.BatchedTower

open CompPoly CompPoly.CPolynomial Polynomial Polynomial.JetHornerMachine
  SampleInterpolation TowerAlgebra

variable {F E L : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
  [Field E] [BEq E] [LawfulBEq E] [Field L] {n : ℕ}

/-- Every modulus put into the product tree is monic because it belongs to a retained component. -/
theorem liveModuli_monic {I : Type} (k : ℕ)
    (blocks : List (ComponentScan.Block (Tower.Component E k) I)) :
    ∀ g ∈ liveModuli k blocks, g.monic := by
  induction blocks with
  | nil => simp [liveModuli]
  | cons block rest ih =>
      by_cases hstop : k ≤ block.positions.length
      · simpa [liveModuli, hstop] using ih
      · intro g hg
        simp only [liveModuli, hstop, ↓reduceIte, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact block.component.property.1
        · exact ih _ hg

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Feeding the ordered individual base restrictions to the batch-result consumer gives exactly
one ordinary collection-advance step with `splitAtSource`. This lemma isolates the list alignment:
stopped blocks consume no remainder, repeated moduli consume distinct ordered slots. -/
theorem advanceWithRestricted_eq (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k : ℕ) (source : Tower.Component E k) (i : Fin n)
    (blocks : List (ComponentScan.Block (Tower.Component E k) (Fin n))) :
    advanceWithRestricted k i blocks
        ((liveModuli k blocks).map fun G => TowerRepresentation.reduceBase G
          (source.val.residual (base (domain i)) (base (received i)))) =
      blocks.flatMap (ComponentScan.advance (fun _ => true)
        (splitAtSource base domain received k source) k i) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      by_cases hstop : k ≤ block.positions.length
      · simp [liveModuli, advanceWithRestricted, ComponentScan.advance, hstop, ih]
      · simp [liveModuli, advanceWithRestricted, ComponentScan.advance, splitRestricted,
          splitAtSource, restrictedResidual, hstop, ih]

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- One executable batched row is the pointwise source-residual collection step. The equality is
functional, not a cost statement: its left side is the implementation that calls the product
remainder tree, while its right side is the proof interface used by `ComponentScan`. -/
theorem advanceFamily_eq (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (source : Tower.Component E k) (i : Fin n)
    (blocks : List (ComponentScan.Block (Tower.Component E k) (Fin n))) :
    advanceFamily M D base domain received k source i blocks =
      blocks.flatMap (ComponentScan.advance (fun _ => true)
        (splitAtSource base domain received k source) k i) := by
  simp only [advanceFamily]
  rw [TowerBatch.restrictBases_eq M D _ _ (liveModuli_monic k blocks)]
  simpa only [TowerRepresentation.reduceBase] using
    advanceWithRestricted_eq base domain received k source i blocks

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The full executable family scan refines the generic row-wise collection scan. -/
theorem scanFamily_eq_scanMany (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (source : Tower.Component E k) (rows : List (Fin n))
    (blocks : List (ComponentScan.Block (Tower.Component E k) (Fin n))) :
    scanFamily M D base domain received k source rows blocks =
      ComponentScan.scanMany (fun _ => true)
        (splitAtSource base domain received k source) k rows blocks := by
  induction rows generalizing blocks with
  | nil => rfl
  | cons i rest ih =>
      rw [scanFamily, advanceFamily_eq, ih]
      rfl

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Batched blocks are the ordered concatenation of one generic scan for each initial family.
This exposes the same sample-position geometry as the existing proof infrastructure. -/
theorem blocks_eq (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Tower.Component E k)) :
    blocks M D base domain received k families = families.flatMap fun source =>
      ComponentScan.scan (fun _ => true) (splitAtSource base domain received k source) k
        (List.ofFn (@id (Fin n))) ⟨source, []⟩ := by
  unfold blocks
  apply List.flatMap_congr
  intro source _
  rw [scanFamily_eq_scanMany, ComponentScan.scanMany_eq]
  simp

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Local base and fiber reduction of the common ancestor residual preserves its value at every
point of the current live component. -/
theorem restrictedResidual_specialize (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) {k : ℕ} (source current : Tower.Component E k) (i : Fin n)
    (ι : E →+* L) (u v : L) (hpoint : current.val.Point ι u v) :
    TowerRepresentation.evalNested
        (restrictedResidual base domain received source current i) ι u v =
      TowerRepresentation.evalNested
        (source.val.residual (base (domain i)) (base (received i))) ι u v := by
  unfold restrictedResidual
  rw [TowerRepresentation.evalNested_reduceElement ι u v current.property.1 hpoint.1
    current.property.2.2.2.1 hpoint.2]
  exact TowerRepresentation.evalNested_reduceBase ι u v current.property.1 hpoint.1 _

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- `splitWithResidual` inherits the sound geometric semantics of executable D5 splitting. -/
theorem splitWithResidual_point_sound (k : ℕ) (current : Tower.Component E k)
    (residual : CPolynomial (CPolynomial E)) (child : Bool × Tower.Component E k)
    (hc : child ∈ splitWithResidual k current residual)
    (ι : E →+* L) (u v : L) (hp : child.2.val.Point ι u v) :
    current.val.Point ι u v ∧
      (child.1 = true ↔ TowerRepresentation.evalNested residual ι u v = 0) := by
  simp only [splitWithResidual, List.mem_map, List.mem_attach, true_and] at hc
  obtain ⟨out, rfl⟩ := hc
  have hs := splitZeroUnit_point_sound current.val residual current.property
    out.val out.property ι u v hp
  refine ⟨hs.1, ?_⟩
  have ht : out.val.tag.isZero = true ↔ out.val.tag = .zero := by
    cases out.val.tag <;> simp [SplitTag.isZero]
  exact ht.trans hs.2

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Every point of the current component follows a `splitWithResidual` child with the correct
zero/unit tag. -/
theorem splitWithResidual_point_complete (k : ℕ) (current : Tower.Component E k)
    (residual : CPolynomial (CPolynomial E)) (ι : E →+* L) (u v : L)
    (hp : current.val.Point ι u v) :
    ∃ child ∈ splitWithResidual k current residual,
      child.2.val.Point ι u v ∧
        (child.1 = true ↔ TowerRepresentation.evalNested residual ι u v = 0) := by
  obtain ⟨out, ho, hpoint, ht⟩ :=
    splitZeroUnit_point_complete current.val residual current.property ι u v hp
  let child : Bool × Tower.Component E k :=
    (out.tag.isZero,
      ⟨out.tower, splitZeroUnit_wellFormed current.val residual current.property out ho⟩)
  have hc : child ∈ splitWithResidual k current residual := by
    simp only [splitWithResidual, List.mem_map, List.mem_attach, true_and]
    exact ⟨⟨out, ho⟩, rfl⟩
  refine ⟨child, hc, hpoint, ?_⟩
  change out.tag.isZero = true ↔ _
  have hz : out.tag.isZero = true ↔ out.tag = .zero := by
    cases out.tag <;> simp [SplitTag.isZero]
  exact hz.trans ht

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- A batched source split is sound: child points remain parent points, and the tag tests the
common ancestor message at the current received coordinate. -/
theorem splitAtSource_point_sound (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k : ℕ) (source current : Tower.Component E k)
    (i : Fin n) (child : Bool × Tower.Component E k)
    (hc : child ∈ splitAtSource base domain received k source current i)
    (ι : E →+* L) (u v : L) (hp : child.2.val.Point ι u v) :
    current.val.Point ι u v ∧
      (child.1 = true ↔
        (source.val.specialize ι u v).eval (ι (base (domain i))) =
          ι (base (received i))) := by
  have hs := splitWithResidual_point_sound k current
    (restrictedResidual base domain received source current i) child hc ι u v hp
  refine ⟨hs.1, ?_⟩
  calc
    child.1 = true ↔ TowerRepresentation.evalNested
        (restrictedResidual base domain received source current i) ι u v = 0 := hs.2
    _ ↔ TowerRepresentation.evalNested
        (source.val.residual (base (domain i)) (base (received i))) ι u v = 0 := by
          rw [restrictedResidual_specialize base domain received source current i ι u v hs.1]
    _ ↔ (source.val.specialize ι u v).eval (ι (base (domain i))) =
        ι (base (received i)) :=
      source.val.residual_eq_zero_iff ι u v _ _

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- A point of a live component follows an executed batched-source child, with a tag matching the
common ancestor message. -/
theorem splitAtSource_point_complete (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (k : ℕ) (source current : Tower.Component E k)
    (i : Fin n) (ι : E →+* L) (u v : L) (hp : current.val.Point ι u v) :
    ∃ child ∈ splitAtSource base domain received k source current i,
      child.2.val.Point ι u v ∧
        (child.1 = true ↔
          (source.val.specialize ι u v).eval (ι (base (domain i))) =
            ι (base (received i))) := by
  obtain ⟨child, hc, hpoint, ht⟩ := splitWithResidual_point_complete k current
    (restrictedResidual base domain received source current i) ι u v hp
  refine ⟨child, hc, hpoint, ?_⟩
  calc
    child.1 = true ↔ TowerRepresentation.evalNested
        (restrictedResidual base domain received source current i) ι u v = 0 := ht
    _ ↔ TowerRepresentation.evalNested
        (source.val.residual (base (domain i)) (base (received i))) ι u v = 0 := by
          rw [restrictedResidual_specialize base domain received source current i ι u v hp]
    _ ↔ (source.val.specialize ι u v).eval (ι (base (domain i))) =
        ι (base (received i)) :=
      source.val.residual_eq_zero_iff ι u v _ _

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Every interpolation attempt uses exactly `k` distinct received positions. -/
theorem stopped_card (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k : ℕ) (families : List (Tower.Component E k))
    (out : ComponentScan.Block (Tower.Component E k) (Fin n))
    (hout : out ∈ blocks M D base domain received k families) :
    out.positions.toFinset.card = k := by
  rw [blocks_eq] at hout
  obtain ⟨source, _, hout⟩ := List.mem_flatMap.mp hout
  have hlen := ComponentScan.positions_length (fun _ => true)
    (splitAtSource base domain received k source) k _ ⟨source, []⟩ out (by simp) hout
  have hsub := ComponentScan.positions_sublist (fun _ => true)
    (splitAtSource base domain received k source) k _ ⟨source, []⟩ out hout
  have hnodup : out.positions.Nodup := hsub.nodup (by
    simpa using (List.nodup_ofFn.mpr (Function.injective_id : Function.Injective (@id (Fin n)))))
  rw [List.toFinset_card_of_nodup hnodup, hlen]

/-- Every returned physical vector has width `k` and passes the final full-word agreement test. -/
theorem mem_recoverAgreement_properties (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (families : List (Tower.Component E k)) (cs : List F)
    (hcs : cs ∈ recoverAgreement M D base domain received k A families) :
    cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
      A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received := by
  simp only [recoverAgreement, List.mem_dedup, List.mem_filterMap] at hcs
  obtain ⟨block, hblock, hc⟩ := hcs
  have hp := checkedCandidate_properties domain received k A block.positions.toFinset
    (stopped_card M D base domain received k families block hblock) cs hc
  exact ⟨hp.1, hp.2.2⟩

omit [BEq F] [LawfulBEq F] in
/-- Every represented message with enough agreements follows the batched source scan to a stopped
sample made only of genuine agreement positions. -/
theorem exists_stopped_sample (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (source : Tower.Component E k) (u v : L) (p : F[X])
    (hp : source.val.Represents ι u v (p.map (ι.comp base)))
    (hag : A ≤ Code.agree (evalOnPoints domain p) received) :
    ∃ out ∈ ComponentScan.scan (fun _ => true)
      (splitAtSource base domain received k source) k
      (List.ofFn (@id (Fin n))) ⟨source, []⟩,
      ∀ i ∈ out.positions, p.eval (domain i) = received i := by
  classical
  let good : Unit → Fin n → Prop := fun _ i => p.eval (domain i) = received i
  let point : Tower.Component E k → Unit → Prop := fun s _ => s.val.Point ι u v
  have hstep : ∀ s i θ, point s θ →
      ∃ child ∈ splitAtSource base domain received k source s i,
        point child.2 θ ∧ (child.1 = true ↔ good θ i) := by
    intro s i θ hs
    obtain ⟨child, hc, hpoint, ht⟩ :=
      splitAtSource_point_complete base domain received k source s i ι u v hs
    refine ⟨child, hc, hpoint, ?_⟩
    rw [ht, hp.2, Polynomial.eval_map]
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
    (fun _ => true) (splitAtSource base domain received k source) point good
    (by intros; rfl) hstep k (List.ofFn (@id (Fin n))) ⟨source, []⟩ () hp.1
    (by simp) (by simpa [hcount] using hAk.trans hag)
  exact ⟨out, hout, hgood⟩

/-- Every qualifying represented message survives interpolation and final agreement checking. -/
theorem exists_mem_recoverAgreement_of_representedBy (M : MulContext E) (D : ModContext E)
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (families : List (Tower.Component E k)) (p : F[X])
    (hdegree : p.degree < k) (hag : A ≤ Code.agree (evalOnPoints domain p) received)
    (hp : Tower.RepresentedBy base ι k families p) :
    ∃ cs ∈ recoverAgreement M D base domain received k A families,
      coefficientPolynomial cs = p := by
  obtain ⟨source, hsource, u, v, hp⟩ := hp
  obtain ⟨out, hout, hgood⟩ :=
    exists_stopped_sample base ι domain received k A hAk source u v p hp hag
  have hblock : out ∈ blocks M D base domain received k families := by
    rw [blocks_eq]
    exact List.mem_flatMap.mpr ⟨source, hsource, hout⟩
  have hcard := stopped_card M D base domain received k families out hblock
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

/-- Every returned message is represented by the initial source family. The proof traces a point
of the final component back through `splitAtSource`, so it never assumes that the current component
stores the same residual representative as the ancestor. -/
theorem representedBy_of_mem_recoverAgreement [IsAlgClosed L]
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (families : List (Tower.Component E k)) (cs : List F)
    (hcs : cs ∈ recoverAgreement M D base domain received k A families) :
    Tower.RepresentedBy base ι k families (coefficientPolynomial cs) := by
  simp only [recoverAgreement, List.mem_dedup, List.mem_filterMap] at hcs
  obtain ⟨out, hout, hc⟩ := hcs
  have hcard := stopped_card M D base domain received k families out hout
  have hproperties := checkedCandidate_properties domain received k A
    out.positions.toFinset hcard cs hc
  rw [blocks_eq] at hout
  obtain ⟨source, hsource, hout⟩ := List.mem_flatMap.mp hout
  obtain ⟨u, v, hpoint⟩ := out.component.val.exists_point ι out.component.property
  let point : Tower.Component E k → Unit → Prop := fun s _ => s.val.Point ι u v
  let good : Unit → Fin n → Prop := fun _ i =>
    (source.val.specialize ι u v).eval (ι (base (domain i))) = ι (base (received i))
  have hstep : ∀ s i child θ,
      child ∈ splitAtSource base domain received k source s i →
      point child.2 θ → point s θ ∧ (child.1 = true → good θ i) := by
    intro s i child θ hchild hp
    have hs := splitAtSource_point_sound base domain received k source s i child
      hchild ι u v hp
    exact ⟨hs.1, hs.2.mp⟩
  have htrace := ComponentScan.point_sound (fun _ => true)
    (splitAtSource base domain received k source) point good hstep
    k (List.ofFn (@id (Fin n))) ⟨source, []⟩ out () hout hpoint
  have heq : source.val.specialize ι u v =
      (coefficientPolynomial cs).map (ι.comp base) := by
    apply source.val.specialize_eq_base_map_of_shared_agreements base ι u v
      out.positions.toFinset domain received domain.injective.injOn
    · exact source.property.2.2.2.2.2.2.2.1.trans hcard.symm
    · simpa only [hcard] using hproperties.2.2.1
    · intro i hi
      rw [hproperties.2.1, Lagrange.eval_interpolate_at_node received domain.injective.injOn hi]
    · intro i hi
      exact (htrace.2 i (List.mem_toFinset.mp hi)).resolve_left (by simp)
  exact ⟨source, hsource, u, v, htrace.1, heq⟩

/-- Exact physical-vector membership inside the represented family. -/
theorem mem_recoverAgreement_iff [IsAlgClosed L]
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Tower.Component E k)) (cs : List F) :
    cs ∈ recoverAgreement M D base domain received k A families ↔
      cs.length = k ∧ (coefficientPolynomial cs).degree < k ∧
        A ≤ Code.agree (evalOnPoints domain (coefficientPolynomial cs)) received ∧
          Tower.RepresentedBy base ι k families (coefficientPolynomial cs) := by
  constructor
  · intro hcs
    have hp := mem_recoverAgreement_properties M D base domain received k A families cs hcs
    exact ⟨hp.1, hp.2.1, hp.2.2,
      representedBy_of_mem_recoverAgreement M D base ι domain received k A families cs hcs⟩
  · rintro ⟨hl, hd, ha, hr⟩
    obtain ⟨candidate, hc, he⟩ := exists_mem_recoverAgreement_of_representedBy
      M D base ι domain received k A hAk families (coefficientPolynomial cs) hd ha hr
    have hcl := (mem_recoverAgreement_properties M D base domain received k A families
      candidate hc).1
    have heq : candidate = cs := coefficientVectors_eq (hcl.trans hl.symm) he
    rwa [← heq]

/-- Batched recovery has the same represented-family exactness contract as the existing scan. -/
theorem recoverAgreement_represented_exact [IsAlgClosed L]
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Tower.Component E k)) :
    Tower.RepresentedExactOutput base ι domain received k A families
      (recoverAgreement M D base domain received k A families) := by
  have hvector := mem_recoverAgreement_iff M D base ι domain received k A hAk families
  have hnodup : (recoverAgreement M D base domain received k A families).Nodup :=
    List.nodup_dedup _
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
        M D base ι domain received k A hAk families p hd ha hr
      exact List.mem_map.mpr ⟨cs, hc, he⟩

/-- Observable refinement to the existing tower scan. Internal component order is intentionally
not identified; after deduplication the two implementations contain exactly the same vectors. -/
theorem mem_recoverAgreement_iff_tower [IsAlgClosed L]
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Tower.Component E k)) (cs : List F) :
    cs ∈ recoverAgreement M D base domain received k A families ↔
      cs ∈ Tower.recoverAgreement base domain received k A families := by
  rw [mem_recoverAgreement_iff M D base ι domain received k A hAk families,
    Tower.mem_recoverAgreement_iff base ι domain received k A hAk families]

/-- Set-level restatement of the refinement theorem, avoiding any unsupported list-order claim. -/
theorem recoverAgreement_toFinset_eq_tower [IsAlgClosed L]
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Tower.Component E k)) :
    (recoverAgreement M D base domain received k A families).toFinset =
      (Tower.recoverAgreement base domain received k A families).toFinset := by
  ext cs
  simp only [List.mem_toFinset]
  exact mem_recoverAgreement_iff_tower M D base ι domain received k A hAk families cs

/-- Constructor coverage promotes batched recovery to the repository's complete-list contract. -/
theorem recoverAgreement_exact_of_coverage
    (M : MulContext E) (D : ModContext E) (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (hAk : k ≤ A)
    (families : List (Tower.Component E k))
    (hcover : ∀ p : F[X], p.degree < k →
      A ≤ Code.agree (evalOnPoints domain p) received → Tower.RepresentedBy base ι k families p) :
    ExactOutput domain received k A (recoverAgreement M D base domain received k A families) := by
  apply exactOutput_of_sound_complete
  · exact List.nodup_dedup _
  · exact mem_recoverAgreement_properties M D base domain received k A families
  · intro p hd ha
    exact exists_mem_recoverAgreement_of_representedBy M D base ι domain received k A hAk
      families p hd ha (hcover p hd ha)

end ReedSolomon.ListDecoding.AgreementRecovery.BatchedTower
