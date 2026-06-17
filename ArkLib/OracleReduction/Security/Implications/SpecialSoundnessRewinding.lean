/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.SpecialSoundness
import ArkLib.OracleReduction.Security.Implications.CoordinateWiseSpecialSoundnessRewinding

/-!
  # (Plain) Special Soundness ⇒ Rewinding Knowledge Soundness

  Plain `(k₁, …, k_μ)`-special soundness is the `ℓᵢ = 1` case of coordinate-wise special
  soundness, and its rewinding implication is obtained as a corollary of the CWSS one rather than
  through a parallel development: whole-challenge forking *is* coordinate forking at `ℓᵢ = 1`
  (the fork oracle is `(CWSSStructure.ofSpecialSound k).forkOracle`, whose single coordinate
  carries the whole challenge).

  The bridge is `specialSound_implies_coordinateWiseSpecialSound`: a `k`-distinct tree
  (`ChallengeTree.IsDistinct`) is exactly a `(CWSSStructure.ofSpecialSound k)`-structured tree —
  at `ℓ = 1` the `SS(S, 1, k)` condition collapses to "`k` pairwise-distinct challenges"
  (cf. `CoordinateWise.isSpecialSoundFamily_one`) — up to the arity identification
  `1·(kᵢ-1)+1 = kᵢ` (whence the hypothesis `1 ≤ kᵢ`).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Casting a `ChallengeTree` along an equality of branching arities preserves `IsDistinct`: the
  predicate reads only the tree's challenge structure, not the arity values. -/
private theorem isDistinct_cast {a a' : pSpec.ChallengeIdx → ℕ} (h : a = a')
    {m : Fin (n + 1)} (tree : ChallengeTree pSpec a m) :
    (h ▸ tree).IsDistinct a' ↔ tree.IsDistinct a := by
  subst h; exact Iff.rfl

/-- Casting a `ChallengeTree` along an equality of branching arities preserves its root-to-leaf
  transcripts (and hence acceptance). -/
private theorem fullTranscripts_cast {a a' : pSpec.ChallengeIdx → ℕ} (h : a = a')
    (tree : ChallengeTree pSpec a 0) :
    (h ▸ tree).fullTranscripts = tree.fullTranscripts := by
  subst h; rfl

/-- **The bridge from plain to coordinate-wise special soundness**: a `(k₁, …, k_μ)`-special-sound
  verifier is coordinate-wise special sound for the canonical single-coordinate structure
  `CWSSStructure.ofSpecialSound k`.

  *Proof route:* a `(ofSpecialSound k)`-structured tree has, at each challenge round, sibling
  challenges forming an `SS(Challenge i, 1, kᵢ)` family, i.e. `kᵢ` pairwise-distinct challenges
  (`CoordinateWise.isSpecialSoundFamily_one` and injectivity); transporting along the arity
  identity `1·(kᵢ-1)+1 = kᵢ` (using `1 ≤ kᵢ`) turns it into a `k`-distinct tree consumable by the
  `specialSound` extractor. -/
theorem specialSound_implies_coordinateWiseSpecialSound
    (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 1 ≤ k i)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.specialSound init impl k relIn langOut →
      verifier.coordinateWiseSpecialSound init impl (CWSSStructure.ofSpecialSound k)
        relIn langOut := by
  intro h
  obtain ⟨E, hE⟩ := h
  -- The branching arity of `ofSpecialSound k` is `1·(kᵢ-1)+1 = kᵢ` (using `1 ≤ kᵢ`).
  have harity : (CWSSStructure.ofSpecialSound k).arity = k := by
    funext i
    show 1 * (k i - 1) + 1 = k i
    rw [Nat.one_mul, Nat.sub_add_cancel (hk i)]
  -- A `(ofSpecialSound k)`-structured tree is `k`-distinct: at `ℓ = 1` the special-sound family
  -- condition gives injectivity of the (single-coordinate) sibling challenges.
  have struct_imp_distinct : ∀ {m : Fin (n + 1)}
      (t : ChallengeTree pSpec (CWSSStructure.ofSpecialSound k).arity m),
      t.IsStructured (CWSSStructure.ofSpecialSound k) →
        t.IsDistinct ((CWSSStructure.ofSpecialSound k).arity) := by
    intro m t
    induction t with
    | leaf => intro _; simp only [ChallengeTree.IsDistinct]
    | msgNode m h msg child ih =>
      intro hs
      simp only [ChallengeTree.IsStructured] at hs
      simp only [ChallengeTree.IsDistinct]
      exact ih hs
    | chalNode m h challenges children ih =>
      intro hs
      simp only [ChallengeTree.IsStructured, CoordinateWise.IsSpecialSoundFamily] at hs
      simp only [ChallengeTree.IsDistinct]
      obtain ⟨⟨hinjc, -⟩, hch⟩ := hs
      refine ⟨fun a b hab => ?_, fun j => ih j (hch j)⟩
      have hdec : (CWSSStructure.ofSpecialSound k).decompose ⟨m, h⟩ (challenges a)
                = (CWSSStructure.ofSpecialSound k).decompose ⟨m, h⟩ (challenges b) := by rw [hab]
      exact hinjc hdec
  -- The extractor: transport the structured tree along the arity identity and feed it to `E`.
  refine ⟨fun stmtIn tree' => E stmtIn (harity ▸ tree'),
    fun stmtIn tree' hStruct hAcc => ?_⟩
  refine hE stmtIn (harity ▸ tree') ?_ ?_
  · exact (isDistinct_cast harity tree').mpr (struct_imp_distinct tree' hStruct)
  · intro tr htr
    rw [fullTranscripts_cast harity tree'] at htr
    exact hAcc tr htr

/- DEPRECATED (single-shot forking route) — superseded by the seeded-replay architecture.
  This `ℓᵢ = 1` corollary depended on the (now-deprecated) single-shot
  `coordinateWiseSpecialSound_implies_knowledgeSoundnessRewinding` and `forkBound`. The seeded
  route will re-expose it as a corollary concluding `knowledgeSoundnessRewindingWithError`.
  The bridge `specialSound_implies_coordinateWiseSpecialSound` above stays LIVE (route-independent,
  reused by the seeded implication). Commented out (not deleted) for reference.

/-- **Plain special soundness implies rewinding knowledge soundness**, as the `ℓᵢ = 1` corollary
  of `coordinateWiseSpecialSound_implies_knowledgeSoundnessRewinding`: the fork oracle resamples
  the whole challenge of a round (the single coordinate of `CWSSStructure.ofSpecialSound k`), and
  the extraction bound is the corresponding `forkBound`. The expected-time reference error is
  `∑ᵢ (kᵢ-1)/|Challenge i|` ([FMN24] Lemma 2.31 at `ℓᵢ = 1`; cf. [AFK22]). -/
theorem specialSound_implies_knowledgeSoundnessRewinding
    (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 1 ≤ k i)
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl relOut.language) :
    verifier.specialSound init impl k relIn relOut.language →
      verifier.knowledgeSoundnessRewinding init impl
        ((CWSSStructure.ofSpecialSound k).forkOracle StmtOut)
        (CWSSStructure.cwssForkImpl (CWSSStructure.ofSpecialSound k) impl verifier)
        relIn relOut (CWSSStructure.ofSpecialSound k).forkBound :=
  fun h =>
    coordinateWiseSpecialSound_implies_knowledgeSoundnessRewinding init impl
      (CWSSStructure.ofSpecialSound k) relIn relOut verifier hImpl hVer
      (specialSound_implies_coordinateWiseSpecialSound init impl k hk relIn
        relOut.language verifier h)
-/

end Verifier
