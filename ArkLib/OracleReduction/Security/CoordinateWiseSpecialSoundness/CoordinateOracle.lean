/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic
import VCVio.OracleComp.Constructions.SampleableType

/-!
  # Coordinate-indexed challenge oracle (substrate for rewinding extraction)

  The protocol's challenge oracle `[pSpec.Challenge]ₒ` samples each round's challenge *atomically*
  as a whole vector `Sᵢ^{ℓᵢ}` (its `challengeQueryImpl` does `$ᵗ (pSpec.Challenge i)`). A faithful
  CWSS rewinding extractor instead needs to resample a *single coordinate* of that vector while
  holding the others fixed, so that two resulting runs differ in exactly one coordinate — i.e. are
  related by `CoordinateWise.CoordEq`. The `CWSSStructure.coordChallengeOracle` below exposes that
  granularity: one oracle per `(round, coordinate)` pair `⟨i, j⟩`, returning a uniform element of
  `Sᵢ = alphabet i`. Against it the stock whole-answer `VCVio.CryptoFoundations.forkReplay` already
  forks at coordinate granularity — no projection-aware fork primitive is required.

  `challenge_uniform_eq_bundle_coords` (**Bridge 1**) is the distribution bridge: atomic sampling
  of round `i`'s challenge equals coordinate-wise sampling bundled through `decompose i`, so a
  rewinding reduction may run the protocol over this oracle without changing its distribution. The
  companion structure bridge `forkReplay_coordEq` (Bridge 2) lives with the CWSS implication in
  `Security.Implications.CoordinateWiseSpecialSoundnessRewinding`, since it needs `forkReplay`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace CWSSStructure

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Index of the coordinate-challenge oracle: a challenge round `i` paired with a coordinate
  `j ∈ Fin ℓᵢ`. -/
@[reducible] def CoordIdx (D : CWSSStructure pSpec) : Type :=
  (i : pSpec.ChallengeIdx) × Fin (D.coordIndex i)

/-- Per-coordinate challenge family: coordinate `⟨i, j⟩` carries the alphabet `Sᵢ = alphabet i`. -/
@[reducible] def coordChallenge (D : CWSSStructure pSpec) : D.CoordIdx → Type :=
  fun s => D.alphabet s.1

/-- Trivial-input oracle interface for each coordinate: querying `⟨i, j⟩` (with unit input) returns
  its `Sᵢ` value. The per-coordinate analogue of `challengeOracleInterface`. -/
@[reducible] def coordChallengeOracleInterface (D : CWSSStructure pSpec) :
    ∀ s, OracleInterface (D.coordChallenge s) :=
  fun _ => OracleInterface.instDefault

/-- The **coordinate-indexed challenge oracle**: one oracle per `(round, coordinate)` pair `⟨i, j⟩`,
  with range `alphabet i`. This refines `[pSpec.Challenge]ₒ` — whose single oracle per round returns
  the whole vector `Sᵢ^{ℓᵢ}` — down to per-coordinate granularity, so that `forkReplay` resamples
  one coordinate at a time. -/
@[reducible] def coordChallengeOracle (D : CWSSStructure pSpec) :
    OracleSpec ((s : D.CoordIdx) × (D.coordChallengeOracleInterface s).Query) :=
  [D.coordChallenge]ₒ'(D.coordChallengeOracleInterface)

/-- Uniform query implementation for the coordinate oracle: each coordinate is sampled uniformly
  from its alphabet `Sᵢ`. The per-coordinate analogue of `challengeQueryImpl`. -/
def coordChallengeQueryImpl (D : CWSSStructure pSpec) [∀ i, SampleableType (D.alphabet i)] :
    QueryImpl D.coordChallengeOracle ProbComp :=
  fun q => $ᵗ (D.alphabet q.1.1)

/-- **Bridge 1 — distribution equivalence.** Sampling a full round-`i` challenge uniformly has the
  same distribution as sampling its `ℓᵢ` coordinates independently (uniformly over `Sᵢ`) and
  bundling them back through `decompose`. This licenses a rewinding reduction to simulate the
  protocol's atomic challenge oracle by the coordinate oracle without changing any output
  distribution.

  *Proof.* `decompose i` is an equivalence between finite types and uniform sampling is preserved by
  it: pointwise both sides assign probability `(card)⁻¹` to every outcome (`probOutput_map_equiv`,
  `probOutput_uniformSample`), and the cardinalities agree by `Fintype.card_congr`. -/
theorem challenge_uniform_eq_bundle_coords (D : CWSSStructure pSpec)
    [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, Finite (pSpec.Challenge i)]
    [∀ i, Finite (D.alphabet i)]
    (i : pSpec.ChallengeIdx) [SampleableType (Fin (D.coordIndex i) → D.alphabet i)] :
    evalDist ($ᵗ (pSpec.Challenge i) : ProbComp (pSpec.Challenge i))
      = evalDist ((D.decompose i).symm <$> ($ᵗ (Fin (D.coordIndex i) → D.alphabet i))
          : ProbComp (pSpec.Challenge i)) := by
  classical
  haveI : Fintype (pSpec.Challenge i) := Fintype.ofFinite _
  haveI : Fintype (D.alphabet i) := Fintype.ofFinite _
  refine evalDist_ext (fun a => ?_)
  simp only [probOutput_map_equiv, probOutput_uniformSample]
  rw [Fintype.card_congr (D.decompose i)]

end CWSSStructure
