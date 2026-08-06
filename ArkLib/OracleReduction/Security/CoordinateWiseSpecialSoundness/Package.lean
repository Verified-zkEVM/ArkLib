/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Composition.Sequential.IsPure

/-!
# Composable coordinate-wise-special-sound reductions (`CWSSPackage`)

A `CWSSPackage` bundles a verifier with everything needed to state and reuse its coordinate-wise
special soundness (CWSS): the challenge structure `struct`, the input/output relations
`relIn`/`relOut`, a purity witness `isPure`, the named extraction algorithm `extractor`, and the
CWSS certificate `isCWSS`, all with respect to a fixed sampling `(init, impl)`.

The point is composition. `CWSSPackage.append` — written with the infix `▷` — chains two packages
along a matching seam (`L₁.relOut = L₂.relIn`, discharged by `rfl`): it appends the verifiers
(`Verifier.append`), appends the structures (`CWSSStructure.append`), composes the purity witnesses
(`Verifier.IsPure.append`), and threads the two certificates through
`Verifier.append_coordinateWiseSpecialSoundWith`. Because purity is a package field, the composed
package is itself pure and can be a left factor again, so a multi-step reduction reads as a single
pleasant chain:

```
def chain := head ▷ middle ▷ tail
theorem chain_cwss := chain.isCWSS
```

Each protocol component exports its own package next to its CWSS theorem; the composition site only
imports and chains them. The universal `▷` is a single elaborator defined in `Escape.lean` (it
dispatches over all four package kinds — pure, guarded, escape-aware, or both); it is `scoped` in
`CoordinateWise`, so `open scoped CoordinateWise` (or `open CoordinateWise`) activates it.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

universe u

namespace CoordinateWise

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A **bundled coordinate-wise-special-sound reduction**: a verifier together with its CWSS
structure, input/output relations, a purity witness, the **named extraction algorithm**
`extractor`, and the certificate `isCWSS` that this extractor witnesses CWSS, all with respect
to a fixed sampling `(init, impl)`. Compose packages with `CWSSPackage.append` / the infix `▷`.

Carrying the extractor as a *field* (rather than existentially inside the certificate) means a
composed chain exposes an actual end-to-end extractor — `chain.extractor` — which is what a
later knowledge-error accounting must run, and what makes the certificate content-bearing
(see `Verifier.treeSpecialSoundWith`). The existential form remains available as
`L.isCWSS.toCWSS`. -/
structure CWSSPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The package's verifier. -/
  verifier : Verifier oSpec StmtIn StmtOut pSpec
  /-- The coordinate-wise structure the verifier is special sound for. -/
  struct : CWSSStructure pSpec
  /-- The input relation. -/
  relIn : Set (StmtIn × WitIn)
  /-- The output relation. -/
  relOut : Set (StmtOut × WitOut)
  /-- The verifier is pure: its verdict is a deterministic function of statement and transcript.
  Needed to place this package as the left factor of an `append`. -/
  isPure : verifier.IsPure
  /-- The package's named extraction algorithm. -/
  extractor : Extractor.TreeBased StmtIn WitIn pSpec (CWSSStructure.toShape struct).arity
  /-- The certificate: `extractor` witnesses that `verifier` is coordinate-wise special sound
  for `struct`, reducing `relIn` to `relOut`. -/
  isCWSS : Verifier.coordinateWiseSpecialSoundWith init impl struct relIn relOut verifier
    extractor

namespace CWSSPackage

variable {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- **Compose two packages along a matching seam.** Given a left package `L₁ : relIn ⇒ mid`, a right
package `L₂ : mid ⇒ relOut` whose seam agrees (`hseam : L₁.relOut = L₂.relIn`, discharged by `rfl`),
this produces the composed package `relIn ⇒ relOut` over `pSpec₁ ++ₚ pSpec₂`: the verifiers are
chained by `Verifier.append`, the structures by `CWSSStructure.append`, the purity witnesses by
`Verifier.IsPure.append`, the extractors by running the left extractor on the prefix tree, and
the certificates by `Verifier.append_coordinateWiseSpecialSoundWith` (the left package's `isPure`
discharges its purity hypothesis). Written infix as `L₁ ▷ L₂`. -/
noncomputable def append {StmtA WitA StmtB WitB StmtC WitC : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (L₁ : CWSSPackage init impl StmtA WitA StmtB WitB pSpec₁)
    (L₂ : CWSSPackage init impl StmtB WitB StmtC WitC pSpec₂)
    (hseam : L₁.relOut = L₂.relIn := by rfl) :
    CWSSPackage init impl StmtA WitA StmtC WitC (pSpec₁ ++ₚ pSpec₂) where
  verifier := L₁.verifier.append L₂.verifier
  struct := L₁.struct.append L₂.struct
  relIn := L₁.relIn
  relOut := L₂.relOut
  isPure := Verifier.IsPure.append L₁.verifier L₂.verifier L₁.isPure L₂.isPure
  extractor := fun stmt tree => L₁.extractor stmt tree.appendSplit.fst
  isCWSS := by
    have h₂ := L₂.isCWSS.toCWSS
    rw [← hseam] at h₂
    exact Verifier.append_coordinateWiseSpecialSoundWith init impl
      L₁.verifier L₂.verifier L₁.struct L₂.struct
      L₁.isPure.is_pure.choose L₁.isPure.is_pure.choose_spec L₁.extractor L₁.isCWSS h₂

end CWSSPackage

end CoordinateWise

end
