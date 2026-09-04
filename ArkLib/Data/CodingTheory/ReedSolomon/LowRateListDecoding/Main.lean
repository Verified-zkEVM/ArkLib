/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Contracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Low-rate Reed–Solomon list decoding up to capacity

This file states the source-fidelity corollary from [BCPZZ26]. It includes every explicit hypothesis
of the paper's main result and strengthens the asymptotic list-size conclusion to the exact
`q ^ (4 * derivativeOrder ε θ + 6)` bound supplied by the root-finding theorem [Kop15].

The theorem exposes two views of the result:

* a decoder certificate saying that one finite list contains exactly all degree-`< messageDim`
  polynomials with the required agreement, with the exact list-size bound; and
* the corresponding statement in ArkLib's canonical `Code.IsListDecodable` API.

The paper additionally claims running time `q ^ O(ε ^ (-12 / θ))`. That clause is not represented
here because ArkLib does not yet have a machine-cost model for the interpolation and root-finding
algorithms. It must not be inferred from the existence of the decoder certificate.

This theorem is not the integration boundary for the formalization. The hidden-derivative engine
uses the exact natural-number `HiddenDerivative.Parameters`, `InterpolationContract`, and
`RootSolverContract`, joined by `HiddenDerivative.exists_decoderCertificate_of_contracts`. In
particular, the core keeps the derivative order, multiplicity, support caps, design dimension, and
solver list bound free. This real-parameter theorem is a later specialization of that interface.

## Source fidelity

The proof of the interpolation proposition in [BCPZZ26] uses
`messageDim = floor ((1 - θ) * ε * blockLength)`, while its statement and the main theorem assume
only an upper bound on the rate. The expected repair is to interpolate at that larger design
dimension and filter to degree `< messageDim`; the public theorem below retains the paper's stated
quantifiers. The blueprint also records an exact `5 / 4` replacement for the lattice estimate's
hidden constant and the repaired ceiling calculation required by the support bound. These are
parameter-discharge obligations rather than changes to the public theorem.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26]
* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace ReedSolomon
namespace LowRateListDecoding

open ListDecoding

/-- The largest Hasse-derivative order used by the hidden-derivative interpolant. -/
noncomputable def derivativeOrder (ε θ : ℝ) : ℕ :=
  Nat.ceil (Real.rpow ε (-3 / θ))

/-- The integral agreement threshold corresponding to agreement at least `ε * blockLength`. -/
noncomputable def agreementThreshold (blockLength : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (ε * blockLength)

/-- The explicit candidate bound obtained from Kopparty's differential-equation root finder. -/
noncomputable def listSizeBound (fieldSize : ℕ) (ε θ : ℝ) : ℕ :=
  fieldSize ^ (4 * derivativeOrder ε θ + 6)

/-- The explicit upper bound on `ε` appearing in the low-rate theorem. -/
noncomputable def smallEpsilonBound (θ : ℝ) : ℝ :=
  Real.rpow (θ ^ 3 * (1 - θ) / 768) ((5 + θ) / (1 - θ))

/-- The non-integral part of the paper's lower bound on the prime-field size. -/
noncomputable def fieldSizeLowerBound
    (blockLength messageDim : ℕ) (ε θ : ℝ) : ℝ :=
  4 * Real.rpow ε (1 - 9 / θ) * blockLength / messageDim

/-- **Published corollary: low-rate Reed–Solomon list decoding up to capacity.**

This is the extensional and list-size content of the main theorem of [BCPZZ26]. Primality is
expressed by `[Fact q.Prime]`, distinct evaluation points by the embedding `domain`, degree `< k`
by the decoder's output type, and agreement at least `ε * n` by `agreementThreshold n ε`.

The source's field-size condition `q ≥ max (n, 4 * ε ^ (1 - 9 / θ) * n / k)` is split into
`hnq` and `hq`. The conclusion gives the exact `q ^ (4 * derivativeOrder ε θ + 6)` bound from
[Kop15], which implies the paper's asymptotic list-size claim.

The running-time claim is deliberately outside this statement; see the module docstring. -/
theorem exists_decoderCertificate_of_low_rate
    (n k q : ℕ) (ε θ : ℝ) [Fact q.Prime]
    (hk : 0 < k) (hkn : k ≤ n)
    (hε : ε ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1)
    (hdk : derivativeOrder ε θ < k)
    (hrate : (k : ℝ) / n ≤ (1 - θ) * ε)
    (hεSmall : ε < smallEpsilonBound θ)
    (hnq : n ≤ q)
    (hq : fieldSizeLowerBound n k ε θ ≤ q)
    (domain : Fin n ↪ ZMod q) :
    Nonempty
        (DecoderCertificate domain k (agreementThreshold n ε) (listSizeBound q ε θ)) ∧
      Code.IsListDecodable
        (ReedSolomon.code domain k : Set (Fin n → ZMod q)) (1 - ε)
        (listSizeBound q ε θ : NNReal) := by
  sorry

end LowRateListDecoding
end ReedSolomon
