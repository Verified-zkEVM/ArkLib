/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound

/-!
  # Scalar single-challenge-round CWSS assembly (generic building block)

  **Skeleton of milestone F4.1** of the Hachi sumcheck track (`HACHI_SUMCHECK_TRACK_PLAN.md`
  §5): the `(ℓ = 1, k)` twin of `CoordinateWise.SingleRound` (which stays pinned to the
  vector-challenge `(ℓ, k) = (2^r, 2)` fold shape of `QuadEval`).

  Several Hachi subprotocols are two-round reductions "one prover message, then one **scalar**
  challenge" whose special soundness is plain `k`-special soundness (`ℓ = 1`) at various `k`:

  * the HMZ25 lift (Figure 4 / Lemma 9): message `t = Com(w̃)`, challenge `α ← F`, `k = 2d`;
  * each paired sumcheck round (Figure 6 / Lemma 11): message = round-polynomial pair,
    challenge `aᵢ ← F`, `k = max-degree + 1`.

  This file provides their shared wire format `pSpecScalar`, the CWSS structure
  `scalarStructure k` (= `CWSSStructure.ofSpecialSound`, arity `k`), the per-round instances,
  and the **sorried** generic assembly `coordinateWiseSpecialSound_of_mkWitness_scalar`: any pure
  statement-extending verifier of this shape is CWSS for `scalarStructure k`, given only a witness
  assembler `mkWitness` that turns `k` per-branch `relOut`-witnesses at *pairwise-distinct*
  challenges into a `relIn`-witness.

  Proof plan (F4.1): transplant `SingleRound.lean`'s tree readers/shape recovery at arity `k`
  (`Fin.cast` along `1*(k−1)+1 = k`); at `ℓ = 1` the star machinery collapses to injectivity of
  the challenge family (`isSpecialSoundFamily_one_iff_injective`), so `hmk` receives plain
  `Function.Injective fam` instead of `StarAt`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp OracleSpec ProtocolSpec CoordinateWise

namespace CoordinateWise.ScalarRound

/-- The two-round scalar-challenge protocol: the prover sends a message `Msg` (round 0,
`P_to_V`), the verifier replies with a single scalar challenge `C` (round 1, `V_to_P`). -/
@[reducible] def pSpecScalar (Msg C : Type) : ProtocolSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Msg, C]⟩

variable {Msg C : Type}

/-- The scalar-round CWSS structure at soundness parameter `k`: a single challenge coordinate
(`ℓ = 1`) over the alphabet `C`, i.e. plain `k`-special soundness — the shape of Hachi
Lemmas 9 and 11. Arity `1·(k−1)+1 = k`. -/
@[reducible] def scalarStructure (k : ℕ) (hk : 2 ≤ k) :
    CWSSStructure (pSpecScalar Msg C) :=
  CWSSStructure.ofSpecialSound (fun _ => k) (fun _ => hk)

section Instances

variable [SampleableType C] [OracleInterface Msg]

/-- Hand-written 2-round instances (not auto-derived for `ProtocolSpec 2`). -/
instance : ∀ i, SampleableType ((pSpecScalar Msg C).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType C)

instance : ∀ i, OracleInterface ((pSpecScalar Msg C).Message i)
  | ⟨0, _⟩ => (inferInstance : OracleInterface Msg)
  | ⟨1, h⟩ => nomatch h

end Instances

section Assembly

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn WitOut : Type} [Nonempty WitOut]
  {σ : Type} [SampleableType C]

/-- **Generic scalar-round CWSS assembly (skeleton, F4.1).** Any pure statement-extending
verifier of the two-round scalar `pSpecScalar` is coordinate-wise special sound for
`scalarStructure k`, provided a witness assembler `mkWitness` that turns `k` per-branch
`relOut`-witnesses at pairwise-distinct challenges into a `relIn`-witness. This is the engine
behind Hachi Lemma 9 (`k = 2d`, interpolation) and Lemma 11 (`k = deg + 1`, per sumcheck round).

**Sorried.** Proof plan: transplant `SingleRound.coordinateWiseSpecialSound_of_mkWitness` — the
tree at arity `k` is one message node over one challenge node over leaves (`tree_shape` at
arity `k`); the `SS(C, 1, k)` node predicate is injectivity of the challenge family
(`isSpecialSoundFamily_one_iff_injective` composed with the `Equiv.funUnique` decomposition of
`scalarStructure`); branch acceptance yields per-branch `relOut`-membership via
`mem_of_pure_accepting`. -/
theorem coordinateWiseSpecialSound_of_mkWitness_scalar
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {k : ℕ} (hk : 2 ≤ k)
    (V : Verifier oSpec StmtIn (StmtIn × Msg × C) (pSpecScalar Msg C))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set ((StmtIn × Msg × C) × WitOut))
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn)
    (hmk : ∀ s v (fam : Fin k → C) (resp : Fin k → WitOut),
      (∀ j, ((s, v, fam j), resp j) ∈ relOut) → Function.Injective fam →
      (s, mkWitness s v fam resp) ∈ relIn) :
    V.coordinateWiseSpecialSound init impl (scalarStructure k hk) relIn relOut := by
  sorry

end Assembly

end CoordinateWise.ScalarRound
