/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveComparison

/-!
# Frozen legacy curve-count snapshots

These 17 rows preserve the exact rational geometric bounds and their integer ceilings from
the manuscript artifact at commit 8972b99c703801c95271e85fab79c61e6f7854b2.
The source JSON filenames are attached to each row below. They are historical capped-method
comparators, not relabeled outputs of the revised hybrid or squarefree evaluator.

Only geometric-bound equality is asserted here; source/rank metadata and measured experiments
are not inferred from these arithmetic declarations.
-/

@[expose] public section

namespace ArkLibExamples.ReedSolomon.LegacyCurveSnapshots

open _root_.ReedSolomon.HiddenDerivative

/-- Literal fields needed to replay one historical geometric bound. -/
structure Snapshot where
  n : ℕ
  k : ℕ
  agreement : ℕ
  multiplicity : ℕ
  derivativeCap : ℕ
  totalCap : ℕ
  curveDegree : ℕ
  height : ℕ
  split : ℕ
  exactBound : ℚ
  ceiling : ℕ

/-- Original row order within the four pinned artifact files. -/
def rows : Fin 17 → Snapshot := ![
  -- 0: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 512754, multiplicity := 13,
    derivativeCap := 5, totalCap := 24, curveDegree := 1,
    height := 215, split := 270283,
    exactBound := 6131813541150761812807195313585 / 6182955802386,
    ceiling := 991728509329550373 },
  -- 1: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 504366, multiplicity := 21,
    derivativeCap := 9, totalCap := 40, curveDegree := 1,
    height := 563, split := 266913,
    exactBound := 217103325972178689037006461770317 / 15241957364130,
    ceiling := 14243795648130051783 },
  -- 2: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 500171, multiplicity := 32,
    derivativeCap := 14, totalCap := 60, curveDegree := 1,
    height := 1188, split := 265339,
    exactBound := 702900064881294339508357107363307 / 6380223804268,
    ceiling := 110168559355409277051 },
  -- 3: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 495453, multiplicity := 64,
    derivativeCap := 27, totalCap := 120, curveDegree := 1,
    height := 15650, split := 262999,
    exactBound := 10090562911463821354773069079697 / 911998450,
    ceiling := 11064232523052886060030 },
  -- 4: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 492831, multiplicity := 384,
    derivativeCap := 168, totalCap := 688, curveDegree := 1,
    height := 867623, split := 262256,
    exactBound := 7539544713027866144574336337049381419 / 55653667968,
    ceiling := 135472557125309116599183150 },
  -- 5: combination-protocol-quarter-rate.json
  { n := 1048576, k := 262144, agreement := 492307, multiplicity := 3072,
    derivativeCap := 1344, totalCap := 5504, curveDegree := 1,
    height := 6874774, split := 262183,
    exactBound := 1042567393109621233364769872716135668238 / 1891660375,
    ceiling := 551138780982088940444592160322 },
  -- 6: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 368575, multiplicity := 16,
    derivativeCap := 4, totalCap := 22, curveDegree := 1,
    height := 298, split := 264227,
    exactBound := 90986329617777343035435694591 / 180820747254,
    ceiling := 503185231780777315 },
  -- 7: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 366216, multiplicity := 26,
    derivativeCap := 7, totalCap := 36, curveDegree := 1,
    height := 599, split := 263551,
    exactBound := 6363018252981294466468421378659 / 1253678344512,
    ceiling := 5075479113789851953 },
  -- 8: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 364381, multiplicity := 45,
    derivativeCap := 13, totalCap := 62, curveDegree := 1,
    height := 1580, split := 262982,
    exactBound := 1017560903351541627733143280529 / 12790966110,
    ceiling := 79553091971372725945 },
  -- 9: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 362808, multiplicity := 128,
    derivativeCap := 39, totalCap := 176, curveDegree := 1,
    height := 6805, split := 262536,
    exactBound := 774183038881065787562846684892844 / 88154105493,
    ceiling := 8782155233173353159316 },
  -- 10: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 362021, multiplicity := 384,
    derivativeCap := 118, totalCap := 530, curveDegree := 1,
    height := 113902, split := 262238,
    exactBound := 96571952628633666870057189218367125 / 23669787586,
    ceiling := 4079967016085653641237421 },
  -- 11: combination-protocol-half-rate.json
  { n := 524288, k := 262144, agreement := 361759, multiplicity := 2048,
    derivativeCap := 634, totalCap := 2826, curveDegree := 1,
    height := 5741208, split := 262156,
    exactBound := 14292469476734140271786190022740042939 / 451006912,
    ceiling := 31690134001170563593903833613 },
  -- 12: larger-domain-affine-screens.json
  { n := 4194304, k := 2097152, agreement := 3007316, multiplicity := 10,
    derivativeCap := 0, totalCap := 14, curveDegree := 1,
    height := 1606, split := 2097152,
    exactBound := 553799757013111127 / 182033,
    ceiling := 3042304181183 },
  -- 13: larger-domain-affine-screens.json
  { n := 8388608, k := 4194304, agreement := 6014632, multiplicity := 10,
    derivativeCap := 0, totalCap := 14, curveDegree := 1,
    height := 1606, split := 4194304,
    exactBound := 1582285194631748157 / 260047,
    ceiling := 6084612376347 },
  -- 14: larger-domain-affine-screens.json
  { n := 524288, k := 32768, agreement := 121373, multiplicity := 14,
    derivativeCap := 7, totalCap := 50, curveDegree := 1,
    height := 749, split := 35133,
    exactBound := 22067193957022704614877969482 / 30747819947,
    ceiling := 717683204697435931 },
  -- 15: beyond-johnson-powers.json
  { n := 1048576, k := 262144, agreement := 492831, multiplicity := 384,
    derivativeCap := 168, totalCap := 688, curveDegree := 511,
    height := 443355791, split := 262256,
    exactBound := 3852711153213193332794984940552589513327 / 55653667968,
    ceiling := 69226545057702985087011344218 },
  -- 16: beyond-johnson-powers.json
  { n := 1048576, k := 262144, agreement := 492307, multiplicity := 3072,
    derivativeCap := 1344, totalCap := 5504, curveDegree := 511,
    height := 3513009939, split := 262183,
    exactBound := 532752002322862870579547737715223373008593 / 1891660375,
    ceiling := 281631951149192344095883352060607 }
]

/-- The historical full-differentiation expression, without a changed method label. -/
def legacyBound (s : Snapshot) : ℚ :=
  firstOrderCurveBound s.n s.k s.k s.split s.agreement s.totalCap s.derivativeCap
    s.curveDegree s.height (2 * s.k - 3)
      (firstOrderCurveDirectRatio s.n s.k s.agreement)

set_option maxRecDepth 16384 in
/-- Every saved rational bound is reproduced exactly, not merely bounded from above. -/
theorem legacyBound_eq_snapshot (i : Fin 17) :
    legacyBound (rows i) = (rows i).exactBound := by
  fin_cases i <;> decide +kernel

/-- Every stored integer is the literal ceiling of the corresponding saved rational bound. -/
theorem snapshot_ceiling_exact (i : Fin 17) :
    Int.ceil (rows i).exactBound = ((rows i).ceiling : ℤ) := by
  fin_cases i <;> decide +kernel

/-- The revised hybrid bound is no larger than each literal historical rational bound.
The minimizations remain inside the maximum over actual derivative degrees. -/
theorem hybridCurveOptimized_le_snapshot (i : Fin 17) :
    _root_.ReedSolomon.hybridCurveOptimized (rows i).n ((rows i).k - 1)
      (rows i).curveDegree (rows i).agreement (rows i).height (rows i).totalCap
      (rows i).derivativeCap ≤ ((rows i).exactBound : ℝ) := by
  rw [← legacyBound_eq_snapshot i]
  unfold legacyBound
  apply _root_.ReedSolomon.hybridCurveOptimized_le_firstOrderCurveBound
  all_goals fin_cases i <;> decide +kernel

end ArkLibExamples.ReedSolomon.LegacyCurveSnapshots
