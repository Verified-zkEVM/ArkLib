/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVMInterpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite

/-!
# Exact polynomial-curve interpolation for LambdaVM

The interpolation equation must hold on the polynomial received curve used by powers
batching, not only on an affine line. At batching degree `ℓ`, the shifted engine assigns
weight `ℓ * t` to total jet grade `t` on both source columns and compressed local-image rows.
This module checks that finite height test at the exact heights recorded in the certificates.

The LambdaVM family contains all five equality-table configurations, with their initial
degree-17 curves and every binary fold down to domain size 256. Rows are ordered first by
increasing initial table size and then by decreasing folding domain size.

## Reading the statements

For each row, the field, domain embedding, and received curve are arbitrary. The only
condition on the received curve is its pointwise challenge-degree bound. The constructed
single equation is primitive, has the recorded support and height, and has a nonzero
specialization vanishing on every sufficiently agreeing candidate of degree below `k`,
over every extension field. Thus batching degree is proved data, not descriptive metadata.

These are the interpolation inputs to the geometric transfer. Exceptional-set counts and
query error estimates are distinct conclusions and are not asserted by this module.
-/

open PolynomialDifferential Polynomial
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ConcreteCurves

open CurveProfile LambdaVMInterpolation

/-- All 35 LambdaVM initial and binary-fold profiles. -/
def lambdaVM : Fin 35 → LineProfile := ![
  { n := 4096, k := 2048, agreement := 2843, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 17,
    supportDimension := 67077768, localRank := 16336,
    columnY₀Weight := 1408668240, height := 144686, heightSlots := 9703872350376 },
  { n := 2048, k := 1024, agreement := 1422, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 33588032, localRank := 16336,
    columnY₀Weight := 706043520, height := 5352, heightSlots := 179090691776 },
  { n := 1024, k := 512, agreement := 711, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 16817256, localRank := 16336,
    columnY₀Weight := 353917200, height := 3968, heightSlots := 66393771864 },
  { n := 512, k := 256, agreement := 356, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 8457776, localRank := 16336,
    columnY₀Weight := 178668000, height := 1905, heightSlots := 15941853056 },
  { n := 256, k := 128, agreement := 178, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 4252128, localRank := 16336,
    columnY₀Weight := 90229440, height := 1286, heightSlots := 5382259296 },
  { n := 8192, k := 4096, agreement := 5697, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 17,
    supportDimension := 71073457, localRank := 8645,
    columnY₀Weight := 1198289092, height := 80321, heightSlots := 5707563924062 },
  { n := 4096, k := 2048, agreement := 2849, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 35562449, localRank := 8645,
    columnY₀Weight := 599860612, height := 3932, heightSlots := 139267251305 },
  { n := 2048, k := 1024, agreement := 1425, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 17806945, localRank := 8645,
    columnY₀Weight := 300646372, height := 2947, heightSlots := 52194227488 },
  { n := 1024, k := 512, agreement := 713, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 8929193, localRank := 8645,
    columnY₀Weight := 151039252, height := 1968, heightSlots := 17430541765 },
  { n := 512, k := 256, agreement := 357, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 4490317, localRank := 8645,
    columnY₀Weight := 76235692, height := 1189, heightSlots := 5267241538 },
  { n := 256, k := 128, agreement := 179, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 2270879, localRank := 8645,
    columnY₀Weight := 38833912, height := 672, heightSlots := 1489467655 },
  { n := 16384, k := 8192, agreement := 11415, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 17,
    supportDimension := 67832160, localRank := 4125,
    columnY₀Weight := 893393400, height := 61201, heightSlots := 4150570462920 },
  { n := 8192, k := 4096, agreement := 5708, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 33928320, localRank := 4125,
    columnY₀Weight := 446966520, height := 3278, heightSlots := 110803994760 },
  { n := 4096, k := 2048, agreement := 2854, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 16969920, localRank := 4125,
    columnY₀Weight := 223624440, height := 3025, heightSlots := 51127353480 },
  { n := 2048, k := 1024, agreement := 1427, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 8490720, localRank := 4125,
    columnY₀Weight := 111953400, height := 2620, heightSlots := 22142223720 },
  { n := 1024, k := 512, agreement := 714, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 4257600, localRank := 4125,
    columnY₀Weight := 56246520, height := 1674, heightSlots := 7075233480 },
  { n := 512, k := 256, agreement := 357, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 2134560, localRank := 4125,
    columnY₀Weight := 28264440, height := 1252, heightSlots := 2646339240 },
  { n := 256, k := 128, agreement := 179, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 1079520, localRank := 4125,
    columnY₀Weight := 14402040, height := 612, heightSlots := 647343720 },
  { n := 32768, k := 16384, agreement := 22878, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 17,
    supportDimension := 79267236, localRank := 2408,
    columnY₀Weight := 885610404, height := 41601, heightSlots := 3296789941668 },
  { n := 16384, k := 8192, agreement := 11439, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 39636864, localRank := 2408,
    columnY₀Weight := 442873136, height := 2404, heightSlots := 94883784784 },
  { n := 8192, k := 4096, agreement := 5720, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 19825404, localRank := 2408,
    columnY₀Weight := 221567196, height := 2236, heightSlots := 44127861552 },
  { n := 4096, k := 2048, agreement := 2860, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 9915948, localRank := 2408,
    columnY₀Weight := 110851532, height := 2100, heightSlots := 20722555216 },
  { n := 2048, k := 1024, agreement := 1430, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 4961220, localRank := 2408,
    columnY₀Weight := 55493700, height := 1872, heightSlots := 9236871360 },
  { n := 1024, k := 512, agreement := 715, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 2483856, localRank := 2408,
    columnY₀Weight := 27814784, height := 1539, heightSlots := 3797323456 },
  { n := 512, k := 256, agreement := 358, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 1248900, localRank := 2408,
    columnY₀Weight := 14038020, height := 877, heightSlots := 1082496180 },
  { n := 256, k := 128, agreement := 179, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 627696, localRank := 2408,
    columnY₀Weight := 7086944, height := 630, heightSlots := 388989232 },
  { n := 65536, k := 32768, agreement := 45910, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 17,
    supportDimension := 92454740, localRank := 1400,
    columnY₀Weight := 835652580, height := 20169, heightSlots := 1863976453220 },
  { n := 32768, k := 16384, agreement := 22955, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 46229260, localRank := 1400,
    columnY₀Weight := 417858140, height := 1180, heightSlots := 54178897920 },
  { n := 16384, k := 8192, agreement := 11478, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 23118676, localRank := 1400,
    columnY₀Weight := 208990180, height := 1154, heightSlots := 26493080600 },
  { n := 8192, k := 4096, agreement := 5739, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 11561228, localRank := 1400,
    columnY₀Weight := 104526940, height := 1130, heightSlots := 12971221928 },
  { n := 4096, k := 2048, agreement := 2870, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 5784660, localRank := 1400,
    columnY₀Weight := 52324580, height := 1041, heightSlots := 5975291140 },
  { n := 2048, k := 1024, agreement := 1435, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 2894220, localRank := 1400,
    columnY₀Weight := 26194140, height := 969, heightSlots := 2781199260 },
  { n := 1024, k := 512, agreement := 718, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 1451156, localRank := 1400,
    columnY₀Weight := 13158180, height := 749, heightSlots := 1075208820 },
  { n := 512, k := 256, agreement := 359, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 727468, localRank := 1400,
    columnY₀Weight := 6610940, height := 619, heightSlots := 444419220 },
  { n := 256, k := 128, agreement := 180, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 367780, localRank := 1400,
    columnY₀Weight := 3366580, height := 358, heightSlots := 128666440 }
]

/-- Each lambdaVM row passes the exact polynomial-curve height test. -/
theorem lambdaVM_verified (i : Fin 35) : (lambdaVM i).CurveVerification := by
  fin_cases i <;> decide +kernel

/-- Every lambdaVM row supplies an actual curve equation at its stated batching degree. -/
theorem lambdaVM_exists_certificate {F : Type*} [Field F] (i : Fin 35)
    (domain : Fin (lambdaVM i).n ↪ F) (w : Fin (lambdaVM i).n → F[X])
    (hw : ∀ j, (w j).natDegree ≤ (lambdaVM i).batchingDegree) :
    Nonempty (FirstOrderCurveCertificate (lambdaVM i).D (lambdaVM i).agreement
      (lambdaVM i).multiplicity (lambdaVM i).firstDerivativeCap (lambdaVM i).totalJetCap
      (lambdaVM i).k (lambdaVM i).height domain w (lambdaVM i).columns) :=
  LineProfile.CurveVerification.exists_certificate (lambdaVM_verified i) domain w hw

end ArkLibExamples.ReedSolomon.ConcreteCurves
