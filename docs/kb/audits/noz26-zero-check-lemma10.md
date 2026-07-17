# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

> **Status (integrated).** The corrected Lemma 10 is now formalized *inside* the escape-threaded
> opening chain: `zeroCheckPackage` reduces `relBatchedE → relZeroCheckE` and is composed as
> `batchPackage ▷ zeroCheckPackage ▷ sumcheckBridgePackage` in `Composition.lean` (`openCore`).
> The CWSS theorem `zeroCheck_coordinateWiseSpecialSound` is **proof-`sorry`-free**. The
> weak-binding seam that earlier blocked composition is discharged by the modelling decision
> recorded below (resolution option 2). All declarations live in the chain's namespace
> `ArkLib.Lattices.Ajtai.InnerOuter` (`Hachi/ZeroCheck/{Constraints,Batch,Reduction}.lean`); the
> generic engine is `OracleReduction/…/CoordinateWiseSpecialSoundness/ChallengeRound.lean`.

## Paper claim

Figure 5 samples two uniform vector challenges `τ₀` and `τ₁`, receives a table `w̃`, checks
`t = Com(w̃)`, reconstructs the batched polynomials from Equations (22)–(23), and checks
`H₀(τ₀) = 0` and `Hα(τ₁) = 0`. Lemma 10 claims that a coordinate-wise special-sound family either
yields one opening satisfying both polynomial identities or breaks commitment binding. Remark 2
says the final instantiation should use the inner-outer commitment's weak binding from Lemma 7.

## Paper-to-Lean ledger

| Paper object or claim | Lean declaration | Status | Concern |
| --- | --- | --- | --- |
| Batched range identity, Eq. (23) | `ZeroCheck.hZero` (via `MvPolynomial.MLE`) | represented | `eq̃`-batching is the real `MLE`, so multilinearity (`hZero_degreeOf_le`) is sorry-free; entry content is `wTable` (F5). |
| Batched row identity, Eq. (22) | `ZeroCheck.hAlpha` (via `MvPolynomial.MLE`) | represented | Multilinearity sorry-free; coefficient content is `hAlphaEvals` (F5). |
| Figure-5 point checks | `ZeroCheck.relZeroCheck` / `relZeroCheckE` | deliberately repaired | Points are derived from scalar Kronecker seeds, not sampled uniformly as vectors; escape-threaded (`Set.withEscape K.esc`). |
| Axis-cross counterexample | `LinearMvExtension.exists_nonzero_vanishing_on_axis_cross` | proven | Formally refutes the identity-testing step used by the uniform-vector argument. |
| Kronecker root-counting kernel | `LinearMvExtension.multilinear_eq_zero_of_kronecker_roots`, `ZeroCheck.arm_eq_zero_of_family` | proven, **axiom-clean** | `D ≥ 2^m` univariate roots + Kronecker injectivity; no `sorryAx`. |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.buildWitnessE`, `buildWitnessE_mem_relBatchedE` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `LiftCom.escOfCollision` via `K.collision_mem` | integrated | Distinct short openings of the shared `t` become an escape `e ∈ K.esc` (Hachi weak binding). |
| Corrected Lemma 10 CWSS | `ZeroCheck.zeroCheck_coordinateWiseSpecialSound` | proof-sorry-free | `(ℓ, k) = (2, D)`; assembled by the generic `ChallengeRound.coordinateWiseSpecialSound_of_mkWitness`. |
| Link-5/link-6/link-7 composition | `batchPackage ▷ zeroCheckPackage ▷ sumcheckBridgePackage` (`openCore`) | **defined, compiles** | The seam relations match by `rfl`; the whole chain builds. |

## Uniform-vector challenge gap (why the repair is needed)

A coordinate-wise star of vector challenges fixes all but one scalar coordinate on each arm. It
therefore proves vanishing only on the axis cross through its center. For at least two variables,
the nonzero multilinear polynomial `(X₁-a)(X₂-b)` vanishes on that entire cross. Increasing the
number of points on the same arms does not repair the argument.

ArkLib's repair samples scalar seeds `ρ₀, ρα` and evaluates on Kronecker curves
`κ_m(ρ) = (ρ, ρ², ρ⁴, ...)`. A multilinear polynomial pulls back injectively to a univariate
polynomial of degree below `2^m`; `2^m` distinct seeds then determine the identity. This changes
the challenge distribution and raises the soundness parameter to `D = max(2, 2^{m₀}, 2^{mα})`.

## Weak-binding seam — resolution adopted (option 2)

The differing-witness branch of the paper's Lemma 10 gives two tables with the same commitment.
The concrete `LiftCom.collision_mem` axiom (matching Hachi Remark 2 / Lemma 7) is
**norm-conditioned**: it turns a collision into an escape only when *both* openings are short.
A single accepting Figure-5 branch pins two point evaluations, which do not by themselves imply
shortness.

**Adopted fix.** The zero-check's output relation `relZeroCheck` carries the conjunct
`liftShort Φ bound ρBound w̃` (and `relZeroCheckE` its escape-threaded widening). Two accepting
branches therefore both certify short openings, so `K.collision_mem` applies and the binding
break becomes an escape. This is completeness-preserving (the honestly committed `w̃` is short),
and the conjunct is threaded onward through the sumcheck seam relation `roundRel` so every
downstream seam keeps the weak-binding escape available. This is *resolution option 2* below:
change the relation so every differing opening is known short before invoking weak binding.

## Residual gaps (out of Lemma-10 scope)

- **F5 encoding.** `hZero`/`hAlpha` are genuine multilinear extensions, but their coefficient
  functions — `wTable` (the Eq. (21) `Zq`-table with the `ρ`-digit decomposition) and
  `hAlphaEvals` (the `M̃_α` contraction) — are still `sorry` (milestone F5). Consequently
  `zeroCheck_coordinateWiseSpecialSound` is proof-`sorry`-free but not yet *axiom-clean*: its
  `#print axioms` reports `sorryAx` transitively through those encoding defs. The Lemma-10
  argument itself is parametric in them; the standalone kernel `arm_eq_zero_of_family` is
  axiom-clean.
- **Constructivity.** `buildWitnessE` (and the generic `treeExtractor`) select per-branch
  witnesses with classical choice. A constructive extractor would need witness-bearing trees or a
  decidable enumeration interface.
- **Sumcheck seam.** `roundRel` now carries the `liftShort` conjunct, but the sumcheck bridge's
  pull-back `mem_relZeroCheckE_of_roundRelE` that must re-supply it remains a skeleton `sorry`
  (milestone F7).

## Resolution options (for the record)

1. assume full binding for arbitrary tables and accept a standalone abstract theorem;
2. **[adopted]** change the relation so every differing opening is known short before invoking weak
   binding (`liftShort` in `relZeroCheck` / `roundRel`);
3. redesign the composed extraction interface so the zero-check consumes downstream
   witness/extractor evidence constructively.
