# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 416 files, 7381 declarations

## Same short-name across multiple files (211 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (15 declarations, 14 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CoordinateWise.CommittedScalar.reduction` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:307](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L307) — **The committed scalar phase as a protocol object**: the honest prover shell paired with the stateme
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:70](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L70) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:43](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L43) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:59](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L59) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:77](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L77) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:98](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L98) — (no docstring)
- `def RingSwitching.Lift.reduction` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:254](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L254) — **The switch as a protocol object**: the honest prover at `honestWitness` paired with the statement-
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:413](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L413) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1006](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1006) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.reduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:262](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L262) — The honest toy-problem reduction instantiated with the executable interleaved-RS encoder.
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:419](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L419) — Honest reduction for the toy protocol: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:227](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L227) — Honest reduction for the simplified IOR.

### `oracleReduction` (14 declarations, 12 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:234](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L234) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:82](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L82) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:119](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L119) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:295](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L295) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleReduction` [ArkLib/ProofSystem/Component/SendChallenge.lean:97](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L97) — The oracle reduction for `SendChallenge`.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:116](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L116) — The oracle reduction for `SendClaim`.
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:373](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L373) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:300](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L300) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:447](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L447) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1012](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1012) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:273](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L273) — Oracle-flavoured honest toy-problem reduction instantiated with the executable interleaved-RS encode
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:534](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L534) — Honest oracle reduction for the toy protocol: the `OracleProver` / `OracleVerifier` pair packaged as
- `def ToyProblem.SimplifiedIOR.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:312](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L312) — The simplified protocol as a genuine interactive oracle reduction.

### `verifier` (14 declarations, 12 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifier` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:400](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L400) — The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the statemen
- `def CoordinateWise.CommittedScalar.verifier` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L132) — Pure statement-extending verifier shared by committed scalar phases.
- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:65](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L65) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:34](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L34) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:55](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L55) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:73](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L73) — (no docstring)
- `def RingSwitching.Lift.verifier` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:138](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L138) — The switch's pure statement-extending verifier, from the committed-scalar shell.
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:404](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L404) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:994](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L994) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1254](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1254) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:405](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L405) — Honest verifier for the toy protocol. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:216](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L216) — Honest verifier for the simplified IOR. Reads `γ` from the transcript and produces the new statement

### `oracleVerifier` (13 declarations, 12 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:214](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L214) — (no docstring)
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:72](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L72) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:86](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L86) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:285](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L285) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleVerifier` [ArkLib/ProofSystem/Component/SendChallenge.lean:77](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L77) — (no docstring)
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:108](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L108) — (no docstring)
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:349](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L349) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean:167](../../../ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean#L167) — The batching-phase verifier as an instance of the family-shared check-then-update scalar-round verif
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:426](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L426) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1000](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1000) — The oracle verifier for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:512](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L512) — Oracle verifier for the toy protocol. Queries the prover's message `g` once and the two oracle codew
- `def ToyProblem.SimplifiedIOR.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:301](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L301) — Oracle verifier for the simplified IOR. The explicit output is the combined linear claim; the output

### `prover` (12 declarations, 11 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.prover` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:426](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L426) — The honest prover (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0 sends th
- `def CoordinateWise.CommittedScalar.prover` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:142](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L142) — Honest prover shell for a committed scalar phase. The commitment is derived from `computeW`; the API
- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:54](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L54) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:30](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L30) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:47](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L47) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:63](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L63) — (no docstring)
- `def RingSwitching.Lift.prover` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:144](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L144) — Honest prover shell. Its commitment is definitionally derived from the output opening.
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:382](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L382) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1244](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1244) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:361](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L361) — Honest prover for the toy protocol. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:185](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L185) — Honest prover for the simplified IOR. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁`

### `pSpec` (12 declarations, 10 files)

- `def CoordinateWise.SingleRound.pSpec` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:53](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L53) — The two-round single-challenge-round protocol (instantiated by Hachi's `QuadEval` reduction): the pr
- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — (no docstring)
- `def SendChallenge.pSpec` [ArkLib/ProofSystem/Component/SendChallenge.lean:49](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L49) — One `V_to_P` challenge round carrying the fold challenge vector `c : Fin ℓ → C`.
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:58](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L58) — One prover→verifier message carrying the claim of type `Message`.
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:54](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L54) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:295](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L295) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:510](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L510) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:745](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L745) — (no docstring)
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:148](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L148) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:220](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L220) — Protocol specification for the toy protocol: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:163](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L163) — Protocol specification for the simplified IOR: a single `V → P` round sending the combination random

### `oracleProver` (11 declarations, 10 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:189](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L189) — The oracle prover for the `CheckClaim` oracle reduction: it forwards the statement and all oracle st
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:67](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L67) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:66](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L66) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:275](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L275) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleProver` [ArkLib/ProofSystem/Component/SendChallenge.lean:54](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L54) — The oracle prover receives the challenge `c` and appends it to the statement (the oracle statements
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:74](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L74) — The oracle prover for `SendClaim`: it computes the claim `f stmt oStmt` and sends it as the only ora
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:213](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L213) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:311](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L311) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean:114](../../../ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean#L114) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:464](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L464) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (
- `def ToyProblem.SimplifiedIOR.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:292](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L292) — Honest prover at the oracle-reduction signature.

### `OracleStatement` (8 declarations, 8 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:40](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L40) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:488](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L488) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:87](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L87) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:144](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L144) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:135](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L135) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:184](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L184) — Oracle statements of the toy protocol: the two purported codewords `f₁, f₂ : ι → A`. The verifier on

### `oracleVerifier_rbrKnowledgeSoundness` (9 declarations, 7 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:98](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L98) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:303](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L303) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:426](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L426) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:217](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L217) — Round-by-round knowledge soundness with error `deg / \|R\|` per challenge for the (full) sum-check pro
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:767](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L767) — Round-by-round knowledge soundness for the oracle verifier
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1138](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1138) — Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by transporting t
- `theorem ToyProblem.Impl.IRS.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:1036](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L1036) — Existential averaged RBR knowledge soundness, retained as a compatibility corollary of the exact-obj
- `theorem ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1411](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1411) — Averaged round-by-round knowledge soundness, retained under the established public API name as a cor

### `relation` (7 declarations, 6 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:85](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L85) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L161) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:152](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L152) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`

### `Statement` (6 declarations, 6 files)

- `abbrev CoordinateWise.CommittedScalar.Statement` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:120](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L120) — Output statement of a committed scalar phase: input statement, commitment, challenge.
- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:78](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L78) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:140](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L140) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:233](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L233) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:178](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L178) — Input (explicit) statement of the toy protocol: the linear-constraint vector `v ∈ F^k` and the two c

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:48](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L48) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:509](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L509) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:108](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L108) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:148](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L148) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:192](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L192) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `inputRelation` (8 declarations, 5 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:40](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L40) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L80) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:37](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L37) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:274](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L274) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:487](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L487) — (no docstring)
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:724](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L724) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:242](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L242) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)

### `append` (6 declarations, 5 files)

- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:36](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L36) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:152](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L152) — Appending two transcripts for two `ProtocolSpec`s
- `def CWSSStructure.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:73](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L73) — Binary append of coordinate-wise special-soundness structures. On left challenge rounds this is `D₁`
- `def CoordinateWise.GCWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:621](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean#L621) — **Compose two guarded packages along a matching seam** — the guarded canonical `▷`. The seam verdict
- `def CoordinateWise.CWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean:102](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean#L102) — **Compose two packages along a matching seam** — the `▷` of pure packages. Every composed field is *
- `def ProtocolSpec.ChallengeTreeShape.append` [ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean:114](../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean#L114) — Append two protocol-generic tree shapes along sequential protocol append.

### `instIsPure` (6 declarations, 5 files)

- `instance CheckClaim.instIsPure` [ArkLib/ProofSystem/Component/CheckClaim.lean:256](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L256) — The `CheckClaim` oracle verifier is pure: its underlying verifier deterministically returns the comb
- `instance ReduceClaim.instIsPure` [ArkLib/ProofSystem/Component/ReduceClaim.lean:218](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L218) — The `ReduceClaim` verifier is pure: it deterministically returns `mapStmt stmt`. This discharges the
- `instance SendChallenge.instIsPure` [ArkLib/ProofSystem/Component/SendChallenge.lean:121](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L121) — The `SendChallenge` oracle verifier is pure: it deterministically appends the (transcript-read) chal
- `instance SendClaim.instIsPure` [ArkLib/ProofSystem/Component/SendClaim.lean:157](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L157) — The `SendClaim` oracle verifier is pure, discharging the deterministic-left hypothesis of the CWSS b
- `instance SendWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:92](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L92) — The `SendWitness` verifier is pure: it deterministically returns `⟨stmt, transcript 0⟩`. This discha
- `instance SendSingleWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:402](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L402) — The `SendSingleWitness` oracle verifier is pure: its underlying (non-oracle) verifier deterministica

### `reduction_perfectCompleteness` (6 declarations, 5 files)

- `theorem CoordinateWise.CommittedScalar.reduction_perfectCompleteness` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:432](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L432) — **Perfect completeness of a committed scalar phase**, at error exactly `0`. The two hypotheses are p
- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:51](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L51) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem RingSwitching.Lift.reduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:308](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L308) — **Perfect completeness at the plain linear relation `relLin`.** The specialization of `reduction_per
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:207](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L207) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:550](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L550) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1099](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1099) — (no docstring)

### `oracleVerifier_materializeOutput` (5 declarations, 5 files)

- `theorem CheckClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/CheckClaim.lean:220](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L220) — (no docstring)
- `theorem RandomQuery.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/RandomQuery.lean:103](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L103) — (no docstring)
- `theorem SendChallenge.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendChallenge.lean:83](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L83) — (no docstring)
- `theorem SendClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendClaim.lean:126](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L126) — (no docstring)
- `theorem SendSingleWitness.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendWitness.lean:356](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L356) — (no docstring)

### `oracleVerifier_toVerifier_run` (5 declarations, 5 files)

- `theorem CheckClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/CheckClaim.lean:243](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L243) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the combined input st
- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:437](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L437) — The `ReduceClaim` oracle verifier's underlying non-oracle verifier deterministically returns the map
- `theorem SendChallenge.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendChallenge.lean:110](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L110) — The pure verifier's underlying non-oracle verifier returns the statement together with the sampled c
- `theorem SendClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendClaim.lean:144](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L144) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the statement togethe
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:391](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L391) — (no docstring)

### `outputRelation` (7 declarations, 4 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L89) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:47](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L47) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:283](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L283) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:499](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L499) — (no docstring)
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:732](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L732) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:271](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L271) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:370](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L370) — (no docstring)

### `commit` (4 declarations, 4 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commit` [ArkLib/Commitments/Functional/Hachi/Commitment.lean:113](../../../ArkLib/Commitments/Functional/Hachi/Commitment.lean#L113) — Honest **commitment** to a multilinear polynomial `p`: reshape it into its `2^r × 2^m` coefficient m
- `def KZG.commit` [ArkLib/Commitments/Functional/KZG/Basic.lean:55](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def SimpleRO.commit` [ArkLib/Commitments/Ordinary/SimpleRO.lean:48](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L48) — Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`.

### `disagreementSet` (4 declarations, 4 files)

- `def BlockRelDistance.disagreementSet` [ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean:43](../../../ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean#L43) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)
- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L61) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁.
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1069](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L1069) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i+ϑ) and g^(i+
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:52](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L52) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that

### `oracleReduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:278](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L278) — **Perfect completeness of the pure pass-through `CheckClaim` oracle reduction.** Because the verifie
- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:133](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L133) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:311](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L311) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:418](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L418) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `oracleVerifier_coordinateWiseSpecialSoundWith` (4 declarations, 4 files)

- `theorem CheckClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/CheckClaim.lean:335](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L335) — **Coordinate-wise special soundness of `CheckClaim`, named form.** The verifier is a pure pass-throu
- `theorem ReduceClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:467](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L467) — **Coordinate-wise special soundness of the `ReduceClaim` oracle reduction, named form.** As in the n
- `theorem SendClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendClaim.lean:183](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L183) — **Coordinate-wise special soundness of `SendClaim`, named form.** The verifier is a pure pass-throug
- `theorem SendSingleWitness.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:445](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L445) — **Coordinate-wise special soundness of `SendSingleWitness`, named form.** The oracle verifier has no

### `outputEmbedding` (4 declarations, 4 files)

- `def CheckClaim.outputEmbedding` [ArkLib/ProofSystem/Component/CheckClaim.lean:203](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L203) — The oracle verifier for the `CheckClaim` oracle reduction is a **pure pass-through**: it returns the
- `def SendChallenge.outputEmbedding` [ArkLib/ProofSystem/Component/SendChallenge.lean:67](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L67) — The oracle verifier samples the challenge `c` (as the `V_to_P` round), reads it off the transcript,
- `def SendClaim.outputEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:91](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L91) — (no docstring)
- `def SendSingleWitness.outputEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:327](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L327) — (no docstring)

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:85](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L85) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:69](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L69) — (no docstring)
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:145](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L145) — The `ReduceClaim` reduction satisfies perfect completeness for any relation. The `↔` form of `reduct
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:98](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L98) — The `SendWitness` reduction satisfies perfect completeness.

### `relOut` (4 declarations, 4 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relOut` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:258](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L258) — **`relOut` — Hachi Eq. (20) (rows c1–c5 verbatim) plus a symmetric-`ℓ∞`-ball model of the `S_b` rang
- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:78](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L78) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:49](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L49) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def RingSwitching.Lift.relOut` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:130](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L130) — The anchored output relation of the switch, from the committed-scalar shell: commitment consistency,

### `treeExtractor` (4 declarations, 4 files)

- `def CoordinateWise.CommittedScalar.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:202](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L202) — The committed-scalar named extractor: `mkWitness` transported along `ScalarRound.treeExtractorScalar
- `def CoordinateWise.SingleRound.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:421](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L421) — **The single-round tree extractor**, generic over separate witness types: read the shared message an
- `def ReduceClaim.treeExtractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:229](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L229) — **The `ReduceClaim` tree extractor**, witness-only: the zero-round tree has a single root-to-leaf pa
- `def RingSwitching.Lift.treeExtractor` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:222](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L222) — The switch's named extractor: the committed-scalar assembler, projecting the common opening to its `

### `oracleReduction_perfectCompleteness` (6 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:92](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L92) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:312](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L312) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:753](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L753) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1117](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1117) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:114](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L114) — **Honest completeness of the three-round toy protocol** (protocol-level form). The honest oracle red
- `theorem ToyProblem.SimplifiedIOR.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:329](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L329) — **Perfect completeness of the simplified IOR** (protocol-level form). For every verifier challenge,

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:221](../../../ArkLib/Data/Hash/DomainSep.lean#L221) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:141](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L141) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L258) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L371) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:149](../../../ArkLib/AGM/Basic.lean#L149) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:107](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L107) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:57](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L57) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:100](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L100) — A Module-SIS adversary.

### `StmtIn` (4 declarations, 3 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:30](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L30) — (no docstring)
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:239](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L239) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:356](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L356) — (no docstring)

### `coordinateWiseSpecialSoundWithEscape` (4 declarations, 3 files)

- `def Verifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:321](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L321) — **Escape-threaded CWSS, named form**: `Verifier.treeSpecialSoundWithEscape` at the CWSS shape `D.toS
- `def OracleVerifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:466](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L466) — Escape-threaded CWSS of an oracle reduction, **named form**: the non-oracle escape notion of the und
- `theorem CoordinateWise.CommittedScalar.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L249) — **Generic escape-threaded CWSS certificate for committed scalar phases.** All protocol-independent e
- `theorem RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:233](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L233) — **CWSS of `Lift`**, escape-threaded, at plain `k = 2d` special soundness: on every structured accept

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:118](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L118) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:175](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L175) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L116) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:115](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L115) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:338](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L338) — The elements of a domain as a finset.
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:356](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L356) — The finset of elements of a concrete coset FFT domain.
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:165](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L165) — The finite set of field elements contained in an FFT domain.

### `verifier_rbrKnowledgeSoundness` (4 declarations, 3 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:209](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L209) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:761](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L761) — Round-by-round knowledge soundness for the verifier
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1107](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1107) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:139](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L139) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure Commitment.Opening` [ArkLib/Commitments/Functional/Basic.lean:60](../../../ArkLib/Commitments/Functional/Basic.lean#L60) — The opening protocol used to prove a claimed oracle response for committed data.
- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:115](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L115) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L130) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:197](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L197) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:93](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L93) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:94](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L94) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:110](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L110) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:182](../../../ArkLib/Data/Hash/DomainSep.lean#L182) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L105) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:217](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L217) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/Commitments/Ordinary/SimpleRO.lean:58](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L58) — The simple random-oracle commitment as an (ordinary) `CommitmentScheme`. Setup samples a uniformly r

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:794](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L794) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:753](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L753) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:531](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L531) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:778](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L778) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:735](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L735) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:522](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L522) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `escEvent` (3 declarations, 3 files)

- `def CoordinateWise.CommittedScalar.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:188](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L188) — The tree-level escape event of a committed scalar phase: `escLocal` transported along `ScalarRound.e
- `def CoordinateWise.SingleRound.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:439](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L439) — The tree-level escape event induced by a **local** (per-star) event `escLocal`: the tree's own messa
- `def RingSwitching.Lift.escEvent` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:209](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L209) — The switch's **escape event**: the committed-scalar collision event at this switch's output relation

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1068](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1068) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:650](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L650) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:429](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L429) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1102) — The knowledge state function for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:692](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L692) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:459](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L459) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:997](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L997) — The oracle reduction for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:572](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L572) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:376](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L376) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1011](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1011) — Perfect completeness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:588](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L588) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:390](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L390) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1122](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1122) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:714](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L714) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:478](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L478) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:906](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L906) — The prover for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:471](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L471) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:313](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L313) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1038](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1038) — The round-by-round extractor for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:617](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L617) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:408](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L408) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:948](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L948) — The verifier for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:515](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L515) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:357](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L357) — The verifier for the final sumcheck step, as an instance of the family-shared check-then-update one-

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:90](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L90) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:164](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L164) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:97](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L97) — The full DP24 ring-switching protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:64](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L64) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:136](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L136) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L84) — The reduction for the full DP24 ring-switching protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:105](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L105) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:179](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L179) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:136](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L136) — (no docstring)

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:42](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L42) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:66](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L66) — The oracle verifier for the full DP24 ring-switching protocol

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:136](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L136) — The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier template
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:257](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L257) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:175](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L175) — The knowledge state function for the `ReduceClaim` reduction.

### `rbrExtractor` (3 declarations, 3 files)

- `def RandomQuery.rbrExtractor` [ArkLib/ProofSystem/Component/RandomQuery.lean:250](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L250) — The round-by-round extractor is trivial since the output witness is `Unit`.
- `def ToyProblem.Impl.IRS.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:358](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L358) — Named executable round-by-round extractor for interleaved RS.
- `def ToyProblem.Spec.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1211](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1211) — The round-by-round extractor: round 0 extracts a relaxed-relation witness by choice, round 1 passes

### `relIn` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relIn` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:382](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L382) — **`relIn` — the ordinary input relation of `QuadEval`**: a weak `VerifiedOpening` for `u` under the
- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:75](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L75) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:41](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L41) — The input relation is that the two oracles are equal.

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:207](../../../ArkLib/Data/Hash/DomainSep.lean#L207) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L117) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:58](../../../ArkLib/OracleReduction/Cast.lean#L58) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:84](../../../ArkLib/OracleReduction/Cast.lean#L84) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:106](../../../ArkLib/OracleReduction/Cast.lean#L106) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:195](../../../ArkLib/OracleReduction/Cast.lean#L195) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:36](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L36) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:80](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L80) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:124](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L124) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:168](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L168) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:198](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L198) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:182](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L182) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:247](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L247) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:326](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L326) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:384](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L384) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:196](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L196) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:263](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L263) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:342](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L342) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:389](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L389) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:404](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L404) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:463](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L463) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:516](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L516) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:31](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L31) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:160](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L160) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:342](../../../ArkLib/OracleReduction/Security/Basic.lean#L342) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:498](../../../ArkLib/OracleReduction/Security/Basic.lean#L498) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:551](../../../ArkLib/OracleReduction/Security/Basic.lean#L551) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:591](../../../ArkLib/OracleReduction/Security/Basic.lean#L591) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:151](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L151) — State-restoration knowledge soundness (w/ straightline extractor). The state-restoration extractor r

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:159](../../../ArkLib/Data/Hash/DomainSep.lean#L159) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L93) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:183](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L183) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:326](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L326) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `soundness` (5 declarations, 2 files)

- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:270](../../../ArkLib/OracleReduction/Security/Basic.lean#L270) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:479](../../../ArkLib/OracleReduction/Security/Basic.lean#L479) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:545](../../../ArkLib/OracleReduction/Security/Basic.lean#L545) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:582](../../../ArkLib/OracleReduction/Security/Basic.lean#L582) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:130](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L130) — State-restoration soundness

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:114](../../../ArkLib/OracleReduction/Cast.lean#L114) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:92](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L92) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:136](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L136) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:204](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L204) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:67](../../../ArkLib/OracleReduction/Cast.lean#L67) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:88](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L88) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:132](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L132) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:200](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L200) — (no docstring)

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L114) — Given a smooth coset FFT domain `ω` of log-order `n`, return its subdomain of log-order `n - i`. The
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:609](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L609) — Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain.
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:61](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L61) — The `i`th subdomain of a smooth FFT domain, obtained by taking the corresponding coset subdomain and
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:139](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L139) — Concrete notation for the `i`th subdomain of a smooth FFT domain.

### `OStmtIn` (3 declarations, 2 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:240](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L240) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:362](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L362) — (no docstring)

### `OStmtOut` (3 declarations, 2 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:269](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L269) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)

### `StmtOut` (3 declarations, 2 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:31](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L31) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L268) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:359](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L359) — (no docstring)

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:424](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L424) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:66](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L66) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:112](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L112) — The Module-SIS advantage.

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/Commitments/Functional/Basic.lean:90](../../../ArkLib/Commitments/Functional/Basic.lean#L90) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:51](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:161](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:411](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L411) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:60](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L60) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:106](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L106) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L126) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:183](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L183) — (no docstring)

### `instIsEmptyChallengeIdx` (3 declarations, 2 files)

- `instance SendClaim.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendClaim.lean:66](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L66) — `SendClaim` is a single `P_to_V` message, so it has no challenge rounds. This makes its coordinate-w
- `instance SendWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:60](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L60) — The `SendWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This is what
- `instance SendSingleWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:303](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L303) — The `SendSingleWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This i

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:82](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L82) — Membership in the finset of elements is the same as membership in the coset FFT domain.
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:141](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L141) — Membership in the finset of elements is the same as membership in the concrete coset FFT domain.
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:85](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L85) — Membership in the finset of elements is the same as membership in the FFT domain.

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:122](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L122) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:179](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L179) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:114](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L114) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:171](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L171) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:54](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L54) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:143](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L143) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1032](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1032) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:611](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L611) — (no docstring)

### `LiftedWitness` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.LiftedWitness` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:138](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L138) — Hachi Eq. (21)'s lifted witness: the `R^lin` witness `z ∈ Rq^μ` and one quotient polynomial per row
- `structure RingSwitching.Lift.LiftedWitness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:80](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L80) — The lifted witness of `Lift`: the `S`-witness `z` of the linear relation and one **computable** quot

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L49) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:201](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L201) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:98](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L98) — Output oracle statement: the single combined codeword `f_new := f₁ + γ • f₂ : ι → A`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:208](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L208) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:108](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L108) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `Params` (2 declarations, 2 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun

### `Pr_or_le` (2 declarations, 2 files)

- `theorem Probability.Pr_or_le` [ArkLib/Data/Probability/Instances.lean:479](../../../ArkLib/Data/Probability/Instances.lean#L479) — **Union Bound (binary form)** The probability of a disjunction of two events is at most the sum of t
- `theorem ToyProblem.Pr_or_le` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:224](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L224) — Deprecated compatibility name for the general probability union bound.

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:91](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L91) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:53](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L53) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:239](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L239) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L268) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `agree` (2 declarations, 2 files)

- `def Code.agree` [ArkLib/Data/CodingTheory/Basic/Distance.lean:172](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L172) — The number of positions at which the two words `u` and `v` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:187](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L187) — Relative `μ`-agreement between words `u` and `v`.

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:250](../../../ArkLib/Data/Fin/Basic.lean#L250) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L55) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:258](../../../ArkLib/Data/Fin/Basic.lean#L258) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:65](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L65) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:96](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L96) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:74](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L74) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:82](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L82) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:57](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L57) — (no docstring)

### `binding` (2 declarations, 2 files)

- `def Commitment.binding` [ArkLib/Commitments/Functional/Basic.lean:218](../../../ArkLib/Commitments/Functional/Basic.lean#L218) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `theorem KZG.CommitmentScheme.binding` [ArkLib/Commitments/Functional/KZG/Binding.lean:746](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L746) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `biniusProfile` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L56) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- `def Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:51](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L51) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def

### `branchPath` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:220](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L220) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node.
- `def CoordinateWise.SingleRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:189](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L189) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node. Defined separately

### `branchPathOf` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:286](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L286) — The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
- `def CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:257](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L257) — The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which

### `branchTr` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:227](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L227) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.
- `def CoordinateWise.SingleRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:196](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L196) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.

### `branch_challenge` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:233](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L233) — Branch `j`'s transcript carries challenge `challenges j` at round 1.
- `theorem CoordinateWise.SingleRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:202](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L202) — Branch `j`'s transcript carries challenge `challenges j` at round 1.

### `branch_mem` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:253](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L253) — Branch `j`'s transcript is one of the star tree's leaf transcripts.
- `theorem CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:222](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L222) — Branch `j`'s transcript is one of the star tree's leaf transcripts.

### `branch_pre` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:243](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L243) — Branch `j`'s transcript carries the shared message `v` at round 0.
- `theorem CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:212](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L212) — Branch `j`'s transcript carries the shared message `v` at round 0.

### `branch_relOut_language` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:350](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L350) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- `theorem CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:381](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L381) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp

### `certifiedExtractorError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:684](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L684) — Full extractor-certified error: the spot-check failure probability combined sharply with the executa
- `def ToyProblem.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1357](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1357) — The executable extractor's full fixed-radius certificate.  Unlike `winningSetUpperBound`, its combin

### `certifiedGammaError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:662](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L662) — The certified combination-round error for the executable interleaved-RS extractor.  This is the fini
- `def ToyProblem.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1274](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1274) — The finite nonnegative-real reflection of the executable extractor's canonical affine-line MCA-plus-

### `chalPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:274](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L274) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- `def CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:245](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L245) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.

### `chal_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:178](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L178) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- `theorem CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:143](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L143) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.

### `chalsAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:121](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L121) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to
- `def CoordinateWise.SingleRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:86](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L86) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to

### `coe_certifiedGammaError` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:669](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L669) — The certified combination-round error coerces back to its defining MCA-plus-list expression.
- `theorem ToyProblem.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1284](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1284) — `certifiedGammaError` coerces to the exact MCA-plus-list certificate.

### `coeffHom` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:260](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L260) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:285](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L285) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:265](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L265) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:291](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L291) — (no docstring)

### `collect_branch_data` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:434](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L434) — **Extraction core, scalar round.** Validity at the pure verdicts yields the `k` per-branch responses
- `theorem CoordinateWise.SingleRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:462](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L462) — **Extraction core.** A leaf witnessing that is valid *at the verifier's verdicts* yields the per-bra

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L136) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:73](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L73) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `constrainedCode` (2 declarations, 2 files)

- `def ReedSolomon.constrainedCode` [ArkLib/Data/CodingTheory/ReedSolomon.lean:843](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L843) — Definition 4.5, WHIR[ACFY24] Constrained Reed-Solomon codes are smooth codes whose decoded `m`-varia
- `def ToyProblem.constrainedCode` [ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean:137](../../../ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean#L137) — **The constrained code** (scalar alphabet `A = F`). Adjoin the linear-constraint value `⟨m, v⟩ = ∑ j

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:832](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L832) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:799](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L799) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:814](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L814) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:775](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L775) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:841](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L841) — Round-by-round knowledge soundness for the core interaction oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:810](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L810) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:98](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L98) — Guruswami-Sudan decoder.  Returns all roots of the GS interpolation polynomial whose evaluation is w

### `domain_implies_2_ne_0` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L114) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/FftDomain/Ops.lean:186](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L186) — (no docstring)

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:111](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L111) — The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:161](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L161) — The existence of a nontrivial smooth FFT domain rules out characteristic `2`.

### `domain_implies_neg_x_ne_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:127](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L127) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:202](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L202) — (no docstring)

### `domain_implies_x_ne_neg_x` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L117) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/FftDomain/Ops.lean:190](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L190) — (no docstring)

### `domain_implies_x_ne_neg_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:121](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L121) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:196](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L196) — (no docstring)

### `encoder` (2 declarations, 2 files)

- `def ToyProblem.Impl.FRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:159](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L159) — The neutral `s = 32` folded encoder: the degree-`< 2^20` folded Reed–Solomon evaluation map on the `
- `def ToyProblem.Impl.IRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L116) — Executable `s`-interleaved Reed--Solomon encoder.  Its public alphabet is `Fin s → F`; interleaving

### `encoder_injective` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:182](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L182) — **Injectivity of the folded encoder** (the "code as the injective map"). Mathematically this would f
- `theorem ToyProblem.Impl.IRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:179](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L179) — Below scalar-row saturation, the executable interleaved encoder is injective.

### `encoder_range` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:197](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L197) — **The folded encoder's image is exactly the folded RS code** `FRS[domain, 2^20, 32, foldOmega]`. The
- `theorem ToyProblem.Impl.IRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:145](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L145) — The executable encoder has exactly the canonical interleaved Reed--Solomon code as its range.

### `eq_leaf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:168](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L168) — Shape recovery, level 2: every subtree at the last round is a leaf.
- `theorem CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:133](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L133) — Shape recovery, level 2: every subtree at the last round is a leaf.

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1027](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1027) — RBR knowledge error for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:606](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L606) — RBR knowledge error for the final sumcheck step

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:218](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L218) — The oracle reduction that is the `i`-th round of Binary Foldfold.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:431](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L431) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:145](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L145) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:164](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L164) — Round-by-round knowledge soundness for the full ring-switching oracle verifier

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:59](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L59) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:91](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L91) — (no docstring)

### `fullRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:135](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L135) — Combined RBR knowledge soundness error for the full protocol
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:156](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L156) — (no docstring)

### `fullTranscript_branchPathOf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:301](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L301) — The branch path's transcript **is** the branch transcript — definitional on the star tree.
- `theorem CoordinateWise.SingleRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:273](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L273) — The branch path's transcript **is** the branch transcript — definitional on the star tree, since the

### `gamma` (2 declarations, 2 files)

- `def RationalFunctions.HenselNumerators.gamma` [ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean:348](../../../ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean#L348) — The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator sequence f
- `def ToyProblem.Impl.FRS.gamma` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:83](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L83) — The shared high-order generator `γ` of `gamma_exists`.

### `gammaAgreementSet` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:210](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L210) — Maximal column agreement set computed from the fresh challenge and the prover's post-challenge messa
- `def ToyProblem.Spec.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:257](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L257) — The source-faithful maximal agreement set computed after `γ` and `g` are known.

### `gammaAgreementSet_card_of_gammaState` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:226](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L226) — A post-`γ` knowledge state makes the computed maximal interleaved agreement set large.
- `theorem ToyProblem.Spec.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:281](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L281) — A `GammaState` witness makes the computed maximal agreement set large.

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:889](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L889) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:37](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L37) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:928](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L928) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L49) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:196](../../../ArkLib/Data/Hash/DomainSep.lean#L196) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L129) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:325](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L325) — A concrete coset FFT domain is injective on every set.
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:153](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L153) — An FFT domain is injective on every set.

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:320](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L320) — A concrete coset FFT domain is injective as a function.
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:149](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L149) — An FFT domain is injective as a function.

### `instOutputOracleInterface` (2 declarations, 2 files)

- `instance SendClaim.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendClaim.lean:60](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L60) — (no docstring)
- `instance SendSingleWitness.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendWitness.lean:293](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L293) — (no docstring)

### `lastPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:267](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L267) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- `def CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:238](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L238) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:247](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L247) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:351](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L351) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:286](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L286) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:441](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L441) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:255](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L255) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:375](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L375) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:322](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L322) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:523](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L523) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:306](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L306) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:489](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L489) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:272](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L272) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:397](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L397) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:955](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L955) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:441](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L441) — (no docstring)

### `mem_gammaAgreementSet` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:217](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L217) — (no docstring)
- `theorem ToyProblem.Spec.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:263](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L263) — (no docstring)

### `minRelHammingDistCode_le_one` (2 declarations, 2 files)

- `lemma Code.minRelHammingDistCode_le_one` [ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean:639](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean#L639) — The minimum relative Hamming distance is at most `1`; the lower bound `0 ≤ δᵣ C` is automatic in `ℚ≥
- `theorem ToyProblem.minRelHammingDistCode_le_one` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:169](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L169) — Deprecated compatibility name for the general coding-theory bound.

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:269](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L269) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:294](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L294) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `oracleVerifier_rbrKnowledgeSoundnessWorstCase` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.oracleVerifier_rbrKnowledgeSoundnessWorstCase` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:982](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L982) — Existential worst-case RBR knowledge soundness, retained as a compatibility corollary of the exact-o
- `theorem ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1375](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1375) — Worst-case-per-fixed-prefix round-by-round knowledge soundness of the toy protocol in the alphabet-g

### `outputIndexEmbedding` (2 declarations, 2 files)

- `def SendClaim.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:87](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L87) — The oracle verifier for `SendClaim` is a **pure pass-through**: it returns the statement and exposes
- `def SendSingleWitness.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:323](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L323) — The index embedding that exposes every input oracle and the single witness message as output oracles

### `outputRelationFor` (2 declarations, 2 files)

- `def ToyProblem.Spec.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:289](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L289) — The IOR-shaped **fixed-encoding** *relaxed* output relation. The soundness statement of L6.6/6.8 is
- `def ToyProblem.SimplifiedIOR.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:121](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L121) — The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of the simplified IOR. Bundles the po

### `outputSimulation` (2 declarations, 2 files)

- `def BatchedFri.Spec.BatchingRound.outputSimulation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:236](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L236) — Virtual implementation of the random-linear-combination codeword.  Every downstream coordinate query
- `def ToyProblem.SimplifiedIOR.outputSimulation` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:270](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L270) — Virtual implementation of the combined C6.9 output oracle.

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:253](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L253) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:84](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L84) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:57](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L57) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:64](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L64) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:111](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L111) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `package` (2 declarations, 2 files)

- `def CoordinateWise.CommittedScalar.package` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:273](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L273) — Bundled committed scalar phase, ready for CWSS composition. This lands in the **pure, escape-aware**
- `def RingSwitching.Lift.package` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:323](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L323) — `Lift` as a composable escape-aware CWSS package. Computable: the purity field carries the verdict f

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean:222](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean#L222) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `projectToMidSumcheckPolyWithParam` (2 declarations, 2 files)

- `def Sumcheck.Structured.projectToMidSumcheckPolyWithParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:161](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L161) — Generic projection `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = H₀(r₀, …, rᵢ₋₁, Xᵢ, …, X_{ℓ-1})` for `H₀ = P · Q(t)`.
- `def Sumcheck.Structured.Prismalinear.projectToMidSumcheckPolyWithParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:100](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L100) — Generic prismalinear projection `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = H₀(r₀, …, rᵢ₋₁, Xᵢ, …, X_{ℓ-1})` for `H₀ = P

### `prover_runToRound_last` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_runToRound_last` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:267](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L267) — **Honest execution of both rounds.** Running the Figure-3 prover to the last round draws the challen
- `lemma CoordinateWise.CommittedScalar.prover_runToRound_last` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:332](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L332) — **Honest execution of both rounds.** Running the prover shell to the last round appends the commitme

### `prover_run_eq` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_run_eq` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:311](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L311) — **The honest prover's run in closed form.** `prover_runToRound_last` followed by `output`: the prove
- `lemma CoordinateWise.CommittedScalar.prover_run_eq` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:366](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L366) — **The honest prover's run in closed form**: draw `c`, then emit the transcript `⟨K.com w, c⟩`, the o

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:144](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L144) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:809](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L809) — (no docstring)

### `queryInput` (2 declarations, 2 files)

- `def BatchedFri.Spec.BatchingRound.queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:132](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L132) — Query one batched input codeword in the verifier's full oracle context.
- `def ToyProblem.SimplifiedIOR.queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:249](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L249) — Query an input codeword at one coordinate in the full verifier oracle context.

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:304](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L304) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:931](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L931) — (no docstring)

### `quotient` (2 declarations, 2 files)

- `def Polynomial.Bivariate.quotient` [ArkLib/Data/Polynomial/Bivariate.lean:137](../../../ArkLib/Data/Polynomial/Bivariate.lean#L137) — The bivariate quotient polynomial.
- `def RingSwitching.Lift.Presentation.quotient` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:293](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L293) — The **honest quotient** of row `i`: the explicit polynomial `ρ := (rowSum − rep yᵢ) /ₘ φ` that witne

### `rbrKnowledgeStateFunction` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:892](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L892) — Knowledge-state function paired with the executable interleaved-RS round-by-round extractor.  This i
- `def ToyProblem.Spec.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1229](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1229) — The round-by-round knowledge state function: relaxed-relation membership at round 0, `GammaState` af

### `rbrWitMid` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:351](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L351) — Intermediate witness types for the executable round-by-round extractor.
- `def ToyProblem.Spec.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1104](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1104) — L6.8 intermediate witness types: input witness at round 0, the γ-round candidate message during roun

### `readChallenges` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:133](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L133) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- `def CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:98](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L98) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str

### `readChallenges_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:163](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L163) — The round-1 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:128](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L128) — The round-1 reader computes on the star tree.

### `readPre` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:115](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L115) — Read the round-0 message (the pre-challenge prover message) off a full tree.
- `def CoordinateWise.SingleRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:79](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L79) — Read the round-0 message (the pre-challenge carrier commitment) off a full tree.

### `readPre_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:158](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L158) — The round-0 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:123](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L123) — The round-0 reader computes on the star tree.

### `reduction_run_support` (2 declarations, 2 files)

- `lemma CoordinateWise.CommittedScalar.reduction_run_support` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:385](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L385) — **Honest-run characterization.** Every element of the support of an honest run is a success determin
- `theorem ReduceClaim.reduction_run_support` [ArkLib/ProofSystem/Component/ReduceClaim.lean:129](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L129) — **The `ReduceClaim` reduction's honest run, in closed form.** A zero-round reduction draws nothing a

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1020](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1020) — (no docstring)

### `relaxedRelationFor_iff_exists_outputRelationFor` (2 declarations, 2 files)

- `theorem ToyProblem.Spec.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:315](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L315) — The language-level relaxed relation `RelaxedRelationFor` is precisely the existential closure of the
- `theorem ToyProblem.SimplifiedIOR.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:131](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L131) — The language-level one-word relaxed relation is precisely the existential closure of the witness-bea

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:173](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L173) — (no docstring)
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:310](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L310) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rowSum` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.rowSum` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:472](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L472) — Mathlib view of `cRowSum`, retained for degree and root-counting proofs.
- `def RingSwitching.Lift.Presentation.rowSum` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:242](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L242) — The `i`-th lifted row's left-hand side `∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) ∈ R[X]`, on the semantics of canonical r

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:164](../../../ArkLib/AGM/Basic.lean#L164) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:137](../../../ArkLib/OracleReduction/Execution.lean#L137) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `simulateQ_queryInput` (2 declarations, 2 files)

- `theorem BatchedFri.Spec.BatchingRound.simulateQ_queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:140](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L140) — (no docstring)
- `theorem ToyProblem.SimplifiedIOR.simulateQ_queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:258](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L258) — (no docstring)

### `simulateQueryAlongHEq` (2 declarations, 2 files)

- `theorem OracleVerifier.simulateQueryAlongHEq` [ArkLib/OracleReduction/Basic.lean:418](../../../ArkLib/OracleReduction/Basic.lean#L418) — (no docstring)
- `theorem simulateQueryAlongHEq` [ArkLib/OracleReduction/Composition/Sequential/Append.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean#L48) — (no docstring)

### `subgroupUnit` (2 declarations, 2 files)

- `def Domain.CosetFftDomain.subgroupUnit` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:98](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L98) — The subgroup element of a concrete coset domain at an additive index.
- `def Domain.FftDomain.subgroupUnit` [ArkLib/Data/Domain/FftDomain/Defs.lean:60](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L60) — The subgroup element of an FFT domain at an additive index.

### `subgroupUnit_add` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_add` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:106](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L106) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_add` [ArkLib/Data/Domain/FftDomain/Defs.lean:68](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L68) — (no docstring)

### `subgroupUnit_neg` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:112](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L112) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/FftDomain/Defs.lean:73](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L73) — (no docstring)

### `subgroupUnit_zero` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:102](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L102) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/FftDomain/Defs.lean:64](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L64) — (no docstring)

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:609](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L609) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:249](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L249) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:669](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L669) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:317](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L317) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:395](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L395) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:238](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L238) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:757](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L757) — Round-by-round knowledge soundness for the sumcheck fold oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:431](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L431) — (no docstring)

### `toORelOut` (2 declarations, 2 files)

- `def SendClaim.toORelOut` [ArkLib/ProofSystem/Component/SendClaim.lean:171](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L171) — The output relation of `SendClaim`: the input relation (read off the pass-through oracles at `inl`)
- `def SendSingleWitness.toORelOut` [ArkLib/ProofSystem/Component/SendWitness.lean:411](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L411) — (no docstring)

### `toPoly_injective` (2 declarations, 2 files)

- `theorem CompPoly.CPolynomial.toPoly_injective` [ArkLib/Commitments/Functional/Hachi/Sumcheck/RoundPoly.lean:74](../../../ArkLib/Commitments/Functional/Hachi/Sumcheck/RoundPoly.lean#L74) — `toPoly` is injective: it is the forward map of the ring equivalence `CPolynomial.ringEquiv`. This i
- `theorem ArkLib.Lattices.CyclotomicModulus.toPoly_injective` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:40](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L40) — `CPolynomial.toPoly` is injective (it is the forward map of a ring isomorphism).

### `toPolynomial` (2 declarations, 2 files)

- `def ArkLib.Lattices.Hachi.toPolynomial` [ArkLib/Commitments/Functional/Hachi/EvalSplit.lean:199](../../../ArkLib/Commitments/Functional/Hachi/EvalSplit.lean#L199) — Inverse reshape of `toMatrix`: read the `2 ^ nl × 2 ^ nh` matrix back into the `2 ^ (nl + nh)` coeff
- `def ReedSolomon.toPolynomial` [ArkLib/Data/CodingTheory/ReedSolomon.lean:663](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L663) — The linear map that maps a Reed-Solomon codeword to its associated polynomial.

### `topMsgAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:104](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L104) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- `def CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:68](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L68) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit

### `transitionStraightlineExtractor` (2 declarations, 2 files)

- `def ToyProblem.Spec.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean:43](../../../ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean#L43) — Turn a deterministic transition algorithm reading `(statement, γ, g)` into the straightline extracto
- `def ToyProblem.SimplifiedIOR.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:334](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L334) — Turn a deterministic C6.9 transition algorithm into the straightline extractor shape used by ArkLib'

### `tree2` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:152](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L152) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- `def CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:117](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L117) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves

### `tree_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:212](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L212) — **Shape recovery.** Every full tree of the two-round scalar `pSpecScalar` is a star tree — one messa
- `theorem CoordinateWise.SingleRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:179](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L179) — **Shape recovery.** Every full tree of the two-round `pSpec` is a star tree. This is the rewrite tha

### `tree_shape_aux` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:196](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L196) — Shape recovery, level 0: every tree at round 0 is a `tree2`.
- `theorem CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:161](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L161) — Shape recovery, level 0: every tree at round 0 is a `tree2`.

### `unflatten` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.unflatten` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean:191](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean#L191) — Un-flatten a row-major block vector into blocks — the inverse of `PolyVec.flattenBlocks`.
- `def ToyProblem.Impl.IRS.unflatten` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:83](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L83) — Split a length-`k` scalar message into `s` rows of length `k / s`.

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:121](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L121) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifierPureForm` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifierPureForm` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:414](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L414) — **The pass-through verifier's purity as data** (`Verifier.PureForm`): the verdict is the pass-throug
- `def CoordinateWise.CommittedScalar.verifierPureForm` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:241](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L241) — The committed-scalar verifier's purity **as data**: its verdict is the input statement extended by t

### `verifier_coordinateWiseSpecialSoundWith` (2 declarations, 2 files)

- `theorem ReduceClaim.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:243](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L243) — **Coordinate-wise special soundness of `ReduceClaim`, named form.** The verifier is pure with no cha
- `theorem SendWitness.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:158](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L158) — **Coordinate-wise special soundness of `SendWitness`, named form.** The verifier has no challenge ro

### `verify` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/Commitments/Ordinary/SimpleRO.lean:51](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L51) — Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash.

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:841](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L841) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:432](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L432) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `Pr_eq_zero_of_forall_not` (2 declarations, 2 files)

- `lemma ToyProblem.Spec.Pr_eq_zero_of_forall_not` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1084](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1084) — `Pr_{x ← D}[P x] = 0` for a never-satisfied predicate `P`.
- `theorem ToyProblem.Spec.Pr_eq_zero_of_forall_not` [ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean:57](../../../ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean#L57) — A predicate false at every point has probability zero.

## Near-duplicate docstrings (Jaccard ≥ 0.85, 74 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitKState` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:663](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L663) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:258](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L258)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:683](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L683) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L294)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1027](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1027) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:606](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L606)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1027](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1027) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:405](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L405)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1102) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:692](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L692)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1102) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:459](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L459)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:997](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L997) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:572](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L572)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:997](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L997) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:376](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L376)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1011](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1011) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:588](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L588)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1011](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1011) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:390](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L390)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1122](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1122) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:714](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L714)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1122](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1122) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:478](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L478)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1038](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1038) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:617](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L617)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1038](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1038) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:408](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L408)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:376](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L376) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:258](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L258)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:408](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L408) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L294)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:836](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L836) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:258](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L258)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:859](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L859) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L294)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:90](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L90) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:164](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L164)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:64](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L64) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:136](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L136)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:105](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L105) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:179](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L179)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:42](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L42) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:841](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L841) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:432](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L432)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L56) vs `Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:51](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L51)
    - a: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
    - b: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:606](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L606) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:405](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L405)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:692](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L692) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:459](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L459)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:572](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L572) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:376](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L376)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:588](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L588) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:390](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L390)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:714](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L714) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:478](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L478)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:617](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L617) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:408](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L408)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:253](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L253) vs `CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:222](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L222)
    - a: Branch `j`'s transcript is one of the star tree's leaf transcripts.
    - b: Branch `j`'s transcript is one of the star tree's leaf transcripts.
- **1.00** `CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:243](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L243) vs `CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:212](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L212)
    - a: Branch `j`'s transcript carries the shared message `v` at round 0.
    - b: Branch `j`'s transcript carries the shared message `v` at round 0.
- **1.00** `CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:350](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L350) vs `CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:381](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L381)
    - a: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
    - b: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- **1.00** `CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:274](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L274) vs `CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:245](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L245)
    - a: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
    - b: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- **1.00** `CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:178](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L178) vs `CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:143](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L143)
    - a: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
    - b: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- **1.00** `CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:168](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L168) vs `CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:133](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L133)
    - a: Shape recovery, level 2: every subtree at the last round is a leaf.
    - b: Shape recovery, level 2: every subtree at the last round is a leaf.
- **1.00** `CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:267](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L267) vs `CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:238](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L238)
    - a: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
    - b: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- **1.00** `CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:133](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L133) vs `CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:98](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L98)
    - a: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
    - b: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- **1.00** `CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:163](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L163) vs `CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:128](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L128)
    - a: The round-1 reader computes on the star tree.
    - b: The round-1 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:158](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L158) vs `CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:123](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L123)
    - a: The round-0 reader computes on the star tree.
    - b: The round-0 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:104](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L104) vs `CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:68](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L68)
    - a: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
    - b: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- **1.00** `CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:152](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L152) vs `CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:117](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L117)
    - a: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
    - b: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- **1.00** `CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:196](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L196) vs `CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:161](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L161)
    - a: Shape recovery, level 0: every tree at round 0 is a `tree2`.
    - b: Shape recovery, level 0: every tree at round 0 is a `tree2`.
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Algebra.lean:105](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Binding.lean:167](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Algebra.lean:61](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Binding.lean:157](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/Commitments/Functional/KZG/Binding.lean:648](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L648) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:535](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L535)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:272](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L272) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:397](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L397)
    - a: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
    - b: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- **1.00** `Prover.processRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:78](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L78) vs `Prover.processRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:167](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L167)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:105](../../../ArkLib/OracleReduction/Execution.lean#L105) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:105](../../../ArkLib/OracleReduction/Execution.lean#L105) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Verifier.coordinateWiseSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L278) vs `Verifier.treeSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean:793](../../../ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L793)
    - a: The existential notion is definitionally the existential closure of the named one.
    - b: The existential notion is definitionally the existential closure of the named one.
- **1.00** `coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:794](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L794) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:753](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L753)
    - a: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:814](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L814) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:775](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L775)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **1.00** `coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:778](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L778) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:735](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L735)
    - a: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:841](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L841) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:810](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L810)
    - a: Round-by-round knowledge soundness for the core interaction oracle verifier
    - b: Round-by-round knowledge soundness for the core interaction oracle verifier
- **1.00** `sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:669](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L669) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:775](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L775)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **0.94** `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l1Norm_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:316](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L316) vs `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l2NormSq_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean:306](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean#L306)
    - a: A ring element with zero centered `ℓ₁` norm is `0`: every centered coefficient representative below
    - b: A ring element with zero centered squared `ℓ₂` norm is `0`: every centered coefficient representativ
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:591](../../../ArkLib/OracleReduction/Security/Basic.lean#L591) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:806](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L806)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:591](../../../ArkLib/OracleReduction/Security/Basic.lean#L591) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:735](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L735)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:498](../../../ArkLib/OracleReduction/Security/Basic.lean#L498) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:806](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L806)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:498](../../../ArkLib/OracleReduction/Security/Basic.lean#L498) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:735](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L735)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:487](../../../ArkLib/OracleReduction/Security/Basic.lean#L487) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:806](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L806)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:487](../../../ArkLib/OracleReduction/Security/Basic.lean#L487) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:735](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L735)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.87** `ArkLib.Lattices.Ajtai.InnerOuter.partialEvalExtractor` [ArkLib/Commitments/Functional/Hachi/Recursion/PartialEval.lean:187](../../../ArkLib/Commitments/Functional/Hachi/Recursion/PartialEval.lean#L187) vs `ArkLib.Lattices.Ajtai.InnerOuter.handoffExtractor` [ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean:179](../../../ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean#L179)
    - a: **The partial-evaluation extraction algorithm.** **Sorried** — this def is the extraction *algorithm
    - b: **The trace-handoff extraction algorithm.** **Sorried** — this def is the extraction *algorithm* its
- **0.86** `CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:286](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L286) vs `CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:257](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L257)
    - a: The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
    - b: The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which
- **0.86** `Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:111](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L111) vs `Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:161](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L161)
    - a: The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
    - b: The existence of a nontrivial smooth FFT domain rules out characteristic `2`.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:582](../../../ArkLib/OracleReduction/Security/Basic.lean#L582) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:797](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L797)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:582](../../../ArkLib/OracleReduction/Security/Basic.lean#L582) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:726](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L726)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:755](../../../ArkLib/OracleReduction/Security/Basic.lean#L755) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:884](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L884)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:479](../../../ArkLib/OracleReduction/Security/Basic.lean#L479) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:797](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L797)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:479](../../../ArkLib/OracleReduction/Security/Basic.lean#L479) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:726](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L726)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:692](../../../ArkLib/OracleReduction/Security/Basic.lean#L692) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:884](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L884)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:50](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L50) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L31)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X

