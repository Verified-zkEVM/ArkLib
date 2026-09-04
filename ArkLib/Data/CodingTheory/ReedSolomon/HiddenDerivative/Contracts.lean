/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Specification

/-!
# Contracts joining hidden-derivative interpolation and root finding

This file freezes the central integration boundary without fixing the paper's analytic parameter
choices or Kopparty's particular root solver.

An `InterpolationContract` constructs, for every received word, a valid differential equation and
proves that every sufficiently agreeing degree-`< designDim` polynomial satisfies it. A
`RootSolverContract` exactly enumerates the degree-bounded solutions of every valid equation under
an arbitrary list bound. Their composition produces an ambient candidate certificate; generic
filtering then gives an exact decoder at any `messageDim ≤ designDim`.

The equation representation, its validity predicate, its satisfaction relation, and the list bound
are parameters. Consequently, improvements to interpolation geometry, hitting extensions, small-
characteristic handling, or the root list bound do not change the decoder theorem.
-/

namespace ReedSolomon
namespace HiddenDerivative

open ListDecoding

noncomputable section

/-- The exact interface supplied by the interpolation proof.

`Valid` should contain the structural facts needed by the chosen root solver, such as nonzeroness,
weighted-degree bounds, and characteristic side conditions. Those facts are intentionally not
encoded as rates or asymptotic estimates here. -/
structure InterpolationContract {F ι Equation : Type*} [Semiring F] [DecidableEq F]
    [Fintype ι] (domain : ι ↪ F) (params : Parameters)
    (Valid : Equation → Prop)
    (Satisfies : Equation → MessagePolynomial F params.designDim → Prop) where
  /-- The differential equation produced from a received word. -/
  equation : (ι → F) → Equation
  /-- Every produced equation meets the solver's exact structural preconditions. -/
  valid : ∀ received, Valid (equation received)
  /-- High agreement forces the candidate polynomial to satisfy the produced equation. -/
  satisfies_of_agreement : ∀ (received : ι → F)
      (p : MessagePolynomial F params.designDim),
    params.minAgreement ≤ Code.agree (ReedSolomon.evalOnPoints domain p) received →
      Satisfies (equation received) p

/-- A root solver that exactly enumerates degree-bounded solutions of every valid equation.

The arbitrary `listBound` parameter is the only list-size fact consumed by decoder integration.
Concrete instances may expose further parameters—candidate degree, characteristic, weighted-degree
cap, or hitting-extension degree—through `Equation` and `Valid`, without changing this contract. -/
structure RootSolverContract {F Equation : Type*} [Semiring F] [DecidableEq F]
    (designDim listBound : ℕ) (Valid : Equation → Prop)
    (Satisfies : Equation → MessagePolynomial F designDim → Prop) where
  /-- Enumerate candidate solutions of an equation. -/
  solve : Equation → Finset (MessagePolynomial F designDim)
  /-- On valid equations, solver membership is exactly equation satisfaction. -/
  isExact : ∀ (equation : Equation), Valid equation → ∀ p,
    p ∈ solve equation ↔ Satisfies equation p
  /-- Valid equations have uniformly bounded solution lists. -/
  card_le : ∀ (equation : Equation), Valid equation → (solve equation).card ≤ listBound

/-- Compose interpolation with exact root finding to obtain a bounded ambient candidate
generator. -/
def InterpolationContract.toCandidateCertificate {F ι Equation : Type*} [Semiring F]
    [DecidableEq F] [Fintype ι] {domain : ι ↪ F} {params : Parameters}
    {Valid : Equation → Prop}
    {Satisfies : Equation → MessagePolynomial F params.designDim → Prop}
    {listBound : ℕ}
    (interpolation : InterpolationContract domain params Valid Satisfies)
    (rootSolver : RootSolverContract params.designDim listBound Valid Satisfies) :
    CandidateCertificate domain params.designDim params.minAgreement listBound where
  candidates received :=
    (rootSolver.solve (interpolation.equation received)).map
      (messagePolynomialValue params.designDim)
  complete received p hp := by
    rw [Finset.mem_map]
    exact ⟨p,
      (rootSolver.isExact (interpolation.equation received) (interpolation.valid received) p).mpr
        (interpolation.satisfies_of_agreement received p hp), rfl⟩
  card_le received := by
    rw [Finset.card_map]
    exact rootSolver.card_le (interpolation.equation received) (interpolation.valid received)

/-- **Central conditional decoder theorem.**

Given the exact interpolation and root-solver contracts, root-find at `params.designDim`, filter to
`messageDim` and actual agreement, and obtain an exact decoder with the solver's arbitrary list
bound. This is the theorem on which decoder integration should depend; real-valued rates and the
published low-rate choices are later corollaries. The existential inputs let the interpolation and
root-solver trunks construct their certificates independently. -/
theorem exists_decoderCertificate_of_contracts {F ι Equation : Type*} [Semiring F]
    [DecidableEq F] [Fintype ι] {domain : ι ↪ F} (messageDim listBound : ℕ)
    (params : Parameters) (hmessageDim : messageDim ≤ params.designDim)
    {Valid : Equation → Prop}
    {Satisfies : Equation → MessagePolynomial F params.designDim → Prop}
    (hInterpolation : Nonempty (InterpolationContract domain params Valid Satisfies))
    (hRootSolver : Nonempty
      (RootSolverContract params.designDim listBound Valid Satisfies)) :
    Nonempty (DecoderCertificate domain messageDim params.minAgreement listBound) := by
  let ⟨interpolation⟩ := hInterpolation
  let ⟨rootSolver⟩ := hRootSolver
  exact ⟨(interpolation.toCandidateCertificate rootSolver).toDecoderCertificate hmessageDim⟩

end
end HiddenDerivative
end ReedSolomon
