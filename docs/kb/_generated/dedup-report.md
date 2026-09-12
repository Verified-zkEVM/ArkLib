# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 490 files, 8392 declarations

## Same short-name across multiple files (266 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (16 declarations, 15 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:118](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L118) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CoordinateWise.CommittedScalar.reduction` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:312](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L312) — **The committed scalar phase as a protocol object**: the honest prover shell paired with the stateme
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:77](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L77) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:49](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L49) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:68](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L68) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:85](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L85) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L107) — (no docstring)
- `def RingSwitching.Lift.reduction` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:258](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L258) — **The switch as a protocol object**: the honest prover at `honestWitness` paired with the statement-
- `def Sumcheck.Interaction.MultivariateRound.reduction` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L78) — The message is private prover input; the verifier sees only its evaluation interface.
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:172](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L172) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:410](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L410) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:971](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L971) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.reduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:265](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L265) — The honest toy-problem reduction instantiated with the executable interleaved-RS encoder.
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:420](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L420) — Honest reduction for the toy protocol: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:228](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L228) — Honest reduction for the simplified IOR.

### `verifier` (16 declarations, 14 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifier` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:432](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L432) — The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the statemen
- `def CoordinateWise.CommittedScalar.verifier` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L137) — Pure statement-extending verifier shared by committed scalar phases.
- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:72](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L72) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:40](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L40) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:59](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L59) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:62](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L62) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:81](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L81) — (no docstring)
- `def RingSwitching.Lift.verifier` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:142](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L142) — The switch's pure statement-extending verifier, from the committed-scalar shell.
- `def Sumcheck.Interaction.MultivariateRound.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:69](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L69) — A fixed-challenge verifier with a multivariate input and output interface.
- `def Sumcheck.Interaction.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:75](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L75) — The verifier receives no concrete polynomial; all polynomial use is through evaluation.
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:153](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L153) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:391](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L391) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:959](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L959) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1238](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1238) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:406](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L406) — Honest verifier for the toy protocol. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:217](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L217) — Honest verifier for the simplified IOR. Reads `γ` from the transcript and produces the new statement

### `oracleReduction` (14 declarations, 12 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:248](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L248) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:93](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L93) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:128](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L128) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:307](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L307) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleReduction` [ArkLib/ProofSystem/Component/SendChallenge.lean:106](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L106) — The oracle reduction for `SendChallenge`.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:125](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L125) — The oracle reduction for `SendClaim`.
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:395](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L395) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:184](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L184) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:306](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L306) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:444](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L444) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:990](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L990) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:276](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L276) — Oracle-flavoured honest toy-problem reduction instantiated with the executable interleaved-RS encode
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:535](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L535) — Honest oracle reduction for the toy protocol: the `OracleProver` / `OracleVerifier` pair packaged as
- `def ToyProblem.SimplifiedIOR.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:313](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L313) — The simplified protocol as a genuine interactive oracle reduction.

### `oracleVerifier` (13 declarations, 12 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:228](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L228) — (no docstring)
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:83](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L83) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:94](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L94) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:297](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L297) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleVerifier` [ArkLib/ProofSystem/Component/SendChallenge.lean:86](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L86) — (no docstring)
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:117](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L117) — (no docstring)
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:371](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L371) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean:175](../../../ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean#L175) — The batching-phase verifier as an instance of the family-shared check-then-update scalar-round verif
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:162](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L162) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:423](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L423) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:965](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L965) — The oracle verifier for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:513](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L513) — Oracle verifier for the toy protocol. Queries the prover's message `g` once and the two oracle codew
- `def ToyProblem.SimplifiedIOR.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:302](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L302) — Oracle verifier for the simplified IOR. The explicit output is the combined linear claim; the output

### `prover` (13 declarations, 12 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.prover` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:458](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L458) — The honest prover (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0 sends th
- `def CoordinateWise.CommittedScalar.prover` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L147) — Honest prover shell for a committed scalar phase. The commitment is derived from `computeW`; the API
- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:57](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L57) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:33](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L33) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:46](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L46) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:50](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L50) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:67](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L67) — (no docstring)
- `def RingSwitching.Lift.prover` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:148](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L148) — Honest prover shell. Its commitment is definitionally derived from the output opening.
- `def Sumcheck.Interaction.SingleRound.prover` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:88](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L88) — An honest prover sends its input polynomial and retains the evaluated output statement.
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1228](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1228) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:362](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L362) — Honest prover for the toy protocol. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:186](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L186) — Honest prover for the simplified IOR. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁`

### `pSpec` (12 declarations, 10 files)

- `def CoordinateWise.SingleRound.pSpec` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:57](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L57) — The two-round single-challenge-round protocol (instantiated by Hachi's `QuadEval` reduction): the pr
- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:57](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L57) — (no docstring)
- `def SendChallenge.pSpec` [ArkLib/ProofSystem/Component/SendChallenge.lean:53](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L53) — One `V_to_P` challenge round carrying the fold challenge vector `c : Fin ℓ → C`.
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:62](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L62) — One prover→verifier message carrying the claim of type `Message`.
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:58](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L58) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:298](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L298) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:513](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L513) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:755](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L755) — (no docstring)
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:129](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L129) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:154](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L154) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:221](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L221) — Protocol specification for the toy protocol: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:164](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L164) — Protocol specification for the simplified IOR: a single `V → P` round sending the combination random

### `oracleProver` (11 declarations, 10 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:198](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L198) — The oracle prover for the `CheckClaim` oracle reduction: it forwards the statement and all oracle st
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:73](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L73) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:70](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L70) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:282](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L282) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleProver` [ArkLib/ProofSystem/Component/SendChallenge.lean:58](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L58) — The oracle prover receives the challenge `c` and appends it to the statement (the oracle statements
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:78](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L78) — The oracle prover for `SendClaim`: it computes the claim `f stmt oStmt` and sends it as the only ora
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:225](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L225) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:328](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L328) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean:122](../../../ArkLib/ProofSystem/RingSwitching/Packing/BatchingPhase.lean#L122) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:465](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L465) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (
- `def ToyProblem.SimplifiedIOR.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:293](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L293) — Honest prover at the oracle-reduction signature.

### `OracleStatement` (8 declarations, 8 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:49](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L49) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:497](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L497) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:147](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L147) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:90](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L90) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:141](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L141) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:185](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L185) — Oracle statements of the toy protocol: the two purported codewords `f₁, f₂ : ι → A`. The verifier on

### `oracleVerifier_rbrKnowledgeSoundness` (9 declarations, 7 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:109](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L109) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:293](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L293) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:441](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L441) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:223](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L223) — Round-by-round knowledge soundness with error `deg / \|R\|` per challenge for the (full) sum-check pro
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:321](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L321) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:735](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L735) — Round-by-round knowledge soundness for the oracle verifier
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1122](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1122) — Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by transporting t
- `theorem ToyProblem.Impl.IRS.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:1040](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L1040) — Existential averaged RBR knowledge soundness, retained as a compatibility corollary of the exact-obj
- `theorem ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1414](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1414) — Averaged round-by-round knowledge soundness, retained under the established public API name as a cor

### `instOutputIsPure` (8 declarations, 7 files)

- `instance CheckClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/CheckClaim.lean:66](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L66) — The `CheckClaim` prover has pure output: it reads its statement off the state, with no oracle query.
- `instance DoNothing.instOutputIsPure` [ArkLib/ProofSystem/Component/DoNothing.lean:36](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L36) — The `DoNothing` prover has pure output: it is `Prover.id`, whose `output` is `pure`.
- `instance RandomQuery.instOutputIsPure` [ArkLib/ProofSystem/Component/RandomQuery.lean:88](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L88) — The `RandomQuery` oracle prover has pure output: it repackages the received challenge and the oracle
- `instance ReduceClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/ReduceClaim.lean:59](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L59) — The `ReduceClaim` prover has pure output: it applies the two plain maps `mapStmt` / `mapWit`, with n
- `instance SendChallenge.instOutputIsPure` [ArkLib/ProofSystem/Component/SendChallenge.lean:71](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L71) — The `SendChallenge` oracle prover has pure output: it appends the received challenge to the statemen
- `instance SendClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/SendClaim.lean:90](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L90) — The `SendClaim` oracle prover has pure output: it exposes the claim it already computed alongside th
- `instance SendWitness.instOutputIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:78](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L78) — The `SendWitness` prover has pure output: it pairs up the state it already holds, with no oracle que
- `instance SendSingleWitness.instOutputIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:340](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L340) — The `SendSingleWitness` oracle prover has pure output: it exposes the witness message alongside the

### `relation` (7 declarations, 6 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:89](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L89) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:28](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L28) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:131](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L131) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:164](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L164) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:165](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L165) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:64](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L64) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:155](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L155) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`

### `Statement` (6 declarations, 6 files)

- `abbrev CoordinateWise.CommittedScalar.Statement` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:125](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L125) — Output statement of a committed scalar phase: input statement, commitment, challenge.
- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:143](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L143) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:235](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L235) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:179](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L179) — Input (explicit) statement of the toy protocol: the linear-constraint vector `v ∈ F^k` and the two c

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:57](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L57) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:517](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L517) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:54](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L54) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:109](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L109) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:151](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L151) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:193](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L193) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `inputRelation` (8 declarations, 5 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:48](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L48) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L89) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:45](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L45) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:277](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L277) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:490](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L490) — (no docstring)
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:736](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L736) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:248](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L248) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:350](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L350) — (no docstring)

### `append` (6 declarations, 5 files)

- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:39](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L39) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:171](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L171) — Appending two transcripts for two `ProtocolSpec`s
- `def CWSSStructure.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:76](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L76) — Binary append of coordinate-wise special-soundness structures. On left challenge rounds this is `D₁`
- `def CoordinateWise.GCWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:625](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean#L625) — **Compose two guarded packages along a matching seam** — the guarded canonical `▷`. The seam verdict
- `def CoordinateWise.CWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean:105](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean#L105) — **Compose two packages along a matching seam** — the `▷` of pure packages. Every composed field is *
- `def ProtocolSpec.ChallengeTreeShape.append` [ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean:117](../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean#L117) — Append two protocol-generic tree shapes along sequential protocol append.

### `instIsPure` (6 declarations, 5 files)

- `instance CheckClaim.instIsPure` [ArkLib/ProofSystem/Component/CheckClaim.lean:271](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L271) — The `CheckClaim` oracle verifier is pure: its underlying verifier deterministically returns the comb
- `instance ReduceClaim.instIsPure` [ArkLib/ProofSystem/Component/ReduceClaim.lean:225](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L225) — The `ReduceClaim` verifier is pure: it deterministically returns `mapStmt stmt`. This discharges the
- `instance SendChallenge.instIsPure` [ArkLib/ProofSystem/Component/SendChallenge.lean:130](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L130) — The `SendChallenge` oracle verifier is pure: it deterministically appends the (transcript-read) chal
- `instance SendClaim.instIsPure` [ArkLib/ProofSystem/Component/SendClaim.lean:166](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L166) — The `SendClaim` oracle verifier is pure, discharging the deterministic-left hypothesis of the CWSS b
- `instance SendWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:100](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L100) — The `SendWitness` verifier is pure: it deterministically returns `⟨stmt, transcript 0⟩`. This discha
- `instance SendSingleWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:424](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L424) — The `SendSingleWitness` oracle verifier is pure: its underlying (non-oracle) verifier deterministica

### `reduction_perfectCompleteness` (6 declarations, 5 files)

- `theorem CoordinateWise.CommittedScalar.reduction_perfectCompleteness` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:437](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L437) — **Perfect completeness of a committed scalar phase**, at error exactly `0`. The two hypotheses are p
- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem RingSwitching.Lift.reduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:312](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L312) — **Perfect completeness at the plain linear relation `relLin`.** The specialization of `reduction_per
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:211](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L211) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:534](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L534) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1083](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1083) — (no docstring)

### `oracleVerifier_materializeOutput` (5 declarations, 5 files)

- `theorem CheckClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/CheckClaim.lean:234](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L234) — (no docstring)
- `theorem RandomQuery.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/RandomQuery.lean:112](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L112) — (no docstring)
- `theorem SendChallenge.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendChallenge.lean:92](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L92) — (no docstring)
- `theorem SendClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendClaim.lean:135](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L135) — (no docstring)
- `theorem SendSingleWitness.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendWitness.lean:378](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L378) — (no docstring)

### `oracleVerifier_toVerifier_run` (5 declarations, 5 files)

- `theorem CheckClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/CheckClaim.lean:257](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L257) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the combined input st
- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:452](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L452) — The `ReduceClaim` oracle verifier's underlying non-oracle verifier deterministically returns the map
- `theorem SendChallenge.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendChallenge.lean:119](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L119) — The pure verifier's underlying non-oracle verifier returns the statement together with the sampled c
- `theorem SendClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendClaim.lean:153](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L153) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the statement togethe
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:413](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L413) — (no docstring)

### `outputRelation` (7 declarations, 4 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:98](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L98) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:55](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L55) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:286](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L286) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:502](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L502) — (no docstring)
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:743](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L743) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:277](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L277) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:353](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L353) — (no docstring)

### `Message` (4 declarations, 4 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:142](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L142) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:36](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L36) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:69](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L69) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag
- `abbrev Sumcheck.Interaction.SingleRound.Message` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:32](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L32) — A degree-bounded polynomial message.

### `commit` (4 declarations, 4 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commit` [ArkLib/Commitments/Functional/Hachi/Commitment.lean:115](../../../ArkLib/Commitments/Functional/Hachi/Commitment.lean#L115) — **The honest Hachi commitment**, at the paper's balanced base-`b` digits. Reshape `p` into its `2^r
- `def KZG.commit` [ArkLib/Commitments/Functional/KZG/Basic.lean:58](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L58) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:42](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L42) — Deterministically commit by multiplying the public matrix by the message vector.
- `def SimpleRO.commit` [ArkLib/Commitments/Ordinary/SimpleRO.lean:50](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L50) — Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`.

### `disagreementSet` (4 declarations, 4 files)

- `def BlockRelDistance.disagreementSet` [ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean:46](../../../ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean#L46) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)
- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L64) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁.
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1039](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L1039) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i+ϑ) and g^(i+
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:62](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L62) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that

### `instOutputIsPureOracle` (4 declarations, 4 files)

- `instance CheckClaim.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/CheckClaim.lean:208](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L208) — The `CheckClaim` oracle prover has pure output: it forwards the statement and oracle statements with
- `instance DoNothing.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/DoNothing.lean:78](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L78) — The `DoNothing` oracle prover has pure output: it is `OracleProver.id`, which unfolds to `Prover.id`
- `instance ReduceClaim.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/ReduceClaim.lean:293](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L293) — The `ReduceClaim` oracle prover has pure output: it applies the plain maps `mapStmt`, `mapOStmt`, an
- `instance SendWitness.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/SendWitness.lean:238](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L238) — The `SendWitness` oracle prover has pure output: it exposes the witness alongside the input oracles,

### `oracleReduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:293](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L293) — **Perfect completeness of the pure pass-through `CheckClaim` oracle reduction.** Because the verifie
- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:141](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L141) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:323](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L323) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:440](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L440) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `oracleVerifier_coordinateWiseSpecialSoundWith` (4 declarations, 4 files)

- `theorem CheckClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/CheckClaim.lean:351](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L351) — **Coordinate-wise special soundness of `CheckClaim`, named form.** The verifier is a pure pass-throu
- `theorem ReduceClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:482](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L482) — **Coordinate-wise special soundness of the `ReduceClaim` oracle reduction, named form.** As in the n
- `theorem SendClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendClaim.lean:192](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L192) — **Coordinate-wise special soundness of `SendClaim`, named form.** The verifier is a pure pass-throug
- `theorem SendSingleWitness.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:467](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L467) — **Coordinate-wise special soundness of `SendSingleWitness`, named form.** The oracle verifier has no

### `outputEmbedding` (4 declarations, 4 files)

- `def CheckClaim.outputEmbedding` [ArkLib/ProofSystem/Component/CheckClaim.lean:217](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L217) — The oracle verifier for the `CheckClaim` oracle reduction is a **pure pass-through**: it returns the
- `def SendChallenge.outputEmbedding` [ArkLib/ProofSystem/Component/SendChallenge.lean:76](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L76) — The oracle verifier samples the challenge `c` (as the `V_to_P` round), reads it off the transcript,
- `def SendClaim.outputEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:100](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L100) — (no docstring)
- `def SendSingleWitness.outputEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:349](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L349) — (no docstring)

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:92](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L92) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:75](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L75) — (no docstring)
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:152](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L152) — The `ReduceClaim` reduction satisfies perfect completeness for any relation. The `↔` form of `reduct
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:106](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L106) — The `SendWitness` reduction satisfies perfect completeness.

### `relOut` (4 declarations, 4 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relOut` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:262](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L262) — **`relOut` — Hachi Eq. (20) (rows c1–c5 verbatim) plus a symmetric-`ℓ∞`-ball model of the `S_b` rang
- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:85](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L85) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def RingSwitching.Lift.relOut` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:134](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L134) — The anchored output relation of the switch, from the committed-scalar shell: commitment consistency,

### `treeExtractor` (4 declarations, 4 files)

- `def CoordinateWise.CommittedScalar.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:207](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L207) — The committed-scalar named extractor: `mkWitness` transported along `ScalarRound.treeExtractorScalar
- `def CoordinateWise.SingleRound.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:432](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L432) — **The single-round tree extractor**, generic over separate witness types: read the shared message an
- `def ReduceClaim.treeExtractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:236](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L236) — **The `ReduceClaim` tree extractor**, witness-only: the zero-round tree has a single root-to-leaf pa
- `def RingSwitching.Lift.treeExtractor` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:226](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L226) — The switch's named extractor: the committed-scalar assembler, projecting the common opening to its `

### `oracleReduction_perfectCompleteness` (5 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:103](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L103) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:721](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L721) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1101](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1101) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:117](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L117) — **Honest completeness of the three-round toy protocol** (protocol-level form). The honest oracle red
- `theorem ToyProblem.SimplifiedIOR.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:332](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L332) — **Perfect completeness of the simplified IOR** (protocol-level form). For every verifier challenge,

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:224](../../../ArkLib/Data/Hash/DomainSep.lean#L224) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:615](../../../ArkLib/Data/Hash/DuplexSponge.lean#L615) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:144](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L144) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:259](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L259) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:372](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L372) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `reindex` (5 declarations, 3 files)

- `def Interaction.Oracle.NamedContext.reindex` [ArkLib/Interaction/Oracle/Resource.lean:95](../../../ArkLib/Interaction/Oracle/Resource.lean#L95) — Reindex a named context along an injection.
- `def Interaction.Oracle.NamedContext.View.reindex` [ArkLib/Interaction/Oracle/Resource.lean:341](../../../ArkLib/Interaction/Oracle/Resource.lean#L341) — Reindex a view; a noninjective map introduces aliases.
- `def Interaction.Oracle.SourceCtx.reindex` [ArkLib/Interaction/Oracle/Source.lean:61](../../../ArkLib/Interaction/Oracle/Source.lean#L61) — Restrict or rename the query interface; noninjective maps explicitly expose aliases.
- `def Interaction.Oracle.OracleFamily.reindex` [ArkLib/Interaction/Oracle/Virtual.lean:60](../../../ArkLib/Interaction/Oracle/Virtual.lean#L60) — Pull back the indexed interface family along an arbitrary map. Repeated indices copy interface types
- `def Interaction.Oracle.VirtualOracle.reindex` [ArkLib/Interaction/Oracle/Virtual.lean:114](../../../ArkLib/Interaction/Oracle/Virtual.lean#L114) — Reindex output interfaces by reusing their query programs.

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:152](../../../ArkLib/AGM/Basic.lean#L152) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:111](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L111) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:61](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L61) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:104](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L104) — A Module-SIS adversary.

### `StmtIn` (4 declarations, 3 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:141](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L141) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:245](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L245) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:339](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L339) — (no docstring)

### `coordinateWiseSpecialSoundWithEscape` (4 declarations, 3 files)

- `def Verifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:324](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L324) — **Escape-threaded CWSS, named form**: `Verifier.treeSpecialSoundWithEscape` at the CWSS shape `D.toS
- `def OracleVerifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:469](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L469) — Escape-threaded CWSS of an oracle reduction, **named form**: the non-oracle escape notion of the und
- `theorem CoordinateWise.CommittedScalar.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:254](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L254) — **Generic escape-threaded CWSS certificate for committed scalar phases.** All protocol-independent e
- `theorem RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:237](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L237) — **CWSS of `Lift`**, escape-threaded, at plain `k = 2d` special soundness: on every structured accept

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:63](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L63) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L121) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:178](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L178) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:119](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L119) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `run` (4 declarations, 3 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:167](../../../ArkLib/AGM/Basic.lean#L167) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Interaction.Oracle.ClosedStage.run` [ArkLib/Interaction/Oracle/Composition.lean:119](../../../ArkLib/Interaction/Oracle/Composition.lean#L119) — Execute using exactly the input claim's behavior, and close with the resources of that run. The conc
- `def Interaction.Oracle.OrderedExecution.run` [ArkLib/Interaction/Oracle/Composition.lean:145](../../../ArkLib/Interaction/Oracle/Composition.lean#L145) — Execute a finite family of actual oracle reductions across explicit dependent interfaces. Each accep
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:149](../../../ArkLib/OracleReduction/Execution.lean#L149) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:118](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L118) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:341](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L341) — The elements of a domain as a finset.
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:359](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L359) — The finset of elements of a concrete coset FFT domain.
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:168](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L168) — The finite set of field elements contained in an FFT domain.

### `verifier_rbrKnowledgeSoundness` (4 declarations, 3 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:63](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L63) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:216](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L216) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:729](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L729) — Round-by-round knowledge soundness for the verifier
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1091](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1091) — (no docstring)

### `Opening` (3 declarations, 3 files)

- `structure Commitment.Opening` [ArkLib/Commitments/Functional/Basic.lean:62](../../../ArkLib/Commitments/Functional/Basic.lean#L62) — The opening protocol used to prove a claimed oracle response for committed data.
- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:118](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L118) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:47](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L47) — The simple Ajtai commitment has no auxiliary opening data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L136) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:198](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L198) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:94](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L94) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:97](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L97) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:33](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L33) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:113](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L113) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Execution.lean:257](../../../ArkLib/Interaction/Oracle/Execution.lean#L257) — A small statement/witness wrapper around oracle strategies. The verifier is built from the public st
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:133](../../../ArkLib/Interaction/Reduction.lean#L133) — A plain dependent reduction pairs a prover and verifier for one typed interaction.
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:625](../../../ArkLib/OracleReduction/Basic.lean#L625) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:185](../../../ArkLib/Data/Hash/DomainSep.lean#L185) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:419](../../../ArkLib/Data/Hash/DuplexSponge.lean#L419) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:108](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L108) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `access` (3 declarations, 3 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.access` [ArkLib/Interaction/Oracle/Prefix.lean:255](../../../ArkLib/Interaction/Oracle/Prefix.lean#L255) — The canonical access signature at the stopping boundary.
- `abbrev Sumcheck.Interaction.MultivariateRound.access` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:35](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L35) — Input access extended by the actual univariate message.
- `abbrev Sumcheck.Interaction.SingleRound.access` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L50) — The two polynomial evaluation resources available after the send.

### `closed` (3 declarations, 3 files)

- `def Interaction.Oracle.CoreRun.closed` [ArkLib/Interaction/Oracle/CoreRun.lean:69](../../../ArkLib/Interaction/Oracle/CoreRun.lean#L69) — Close using only this run's input and sent messages.
- `def Interaction.Oracle.LoggedRun.closed` [ArkLib/Interaction/Oracle/LoggedRun.lean:60](../../../ArkLib/Interaction/Oracle/LoggedRun.lean#L60) — Closing uses the core's own resources; the trace is observational evidence, not a handler.
- `def Interaction.Oracle.TerminalRun.closed` [ArkLib/Interaction/Oracle/TerminalRun.lean:68](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L68) — Close accepted claims using this run's available context, preserving rejection and returned faults.

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:220](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L220) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:60](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L60) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/Commitments/Ordinary/SimpleRO.lean:60](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L60) — The simple random-oracle commitment as an (ordinary) `CommitmentScheme`. Setup samples a uniformly r

### `comp_assoc` (3 declarations, 3 files)

- `theorem Interaction.Oracle.TypeTree.ExecutionPrefix.comp_assoc` [ArkLib/Interaction/Oracle/Prefix.lean:124](../../../ArkLib/Interaction/Oracle/Prefix.lean#L124) — Ordered concrete prefix composition is associative.
- `theorem Interaction.Oracle.NamedContext.Inclusion.comp_assoc` [ArkLib/Interaction/Oracle/Resource.lean:257](../../../ArkLib/Interaction/Oracle/Resource.lean#L257) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.comp_assoc` [ArkLib/Interaction/Oracle/Source.lean:218](../../../ArkLib/Interaction/Oracle/Source.lean#L218) — (no docstring)

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:798](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L798) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:787](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L787) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:544](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L544) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:782](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L782) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:767](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L767) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:535](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L535) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `empty` (3 declarations, 3 files)

- `def Interaction.Oracle.NamedContext.empty` [ArkLib/Interaction/Oracle/Resource.lean:85](../../../ArkLib/Interaction/Oracle/Resource.lean#L85) — The empty named context.
- `def Interaction.Oracle.SourceCtx.empty` [ArkLib/Interaction/Oracle/Source.lean:56](../../../ArkLib/Interaction/Oracle/Source.lean#L56) — A source with no queries and no backing data.
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:46](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L46) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `escEvent` (3 declarations, 3 files)

- `def CoordinateWise.CommittedScalar.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:193](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L193) — The tree-level escape event of a committed scalar phase: `escLocal` transported along `ScalarRound.e
- `def CoordinateWise.SingleRound.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:450](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L450) — The tree-level escape event induced by a **local** (per-star) event `escLocal`: the tree's own messa
- `def RingSwitching.Lift.escEvent` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:213](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L213) — The switch's **escape event**: the committed-scalar collision event at this switch's output relation

### `eval` (3 declarations, 3 files)

- `def Interaction.Oracle.SourceCtx.eval` [ArkLib/Interaction/Oracle/Source.lean:122](../../../ArkLib/Interaction/Oracle/Source.lean#L122) — Interpret a program using precisely the answers of the supplied environment.
- `def Interaction.Oracle.VirtualOracle.eval` [ArkLib/Interaction/Oracle/Virtual.lean:84](../../../ArkLib/Interaction/Oracle/Virtual.lean#L84) — Evaluate each query using a deterministic source handler.
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:57](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L57) — Evaluate a gate on a given input vector.

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1059](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1059) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:683](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L683) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:436](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L436) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1090](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1090) — The knowledge state function for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:464](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L464) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:987](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L987) — The oracle reduction for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:603](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L603) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:382](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L382) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1001](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1001) — Perfect completeness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:620](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L620) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:397](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L397) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1111) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:746](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L746) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:487](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L487) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:899](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L899) — The prover for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:501](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L501) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:319](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L319) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1028](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1028) — The round-by-round extractor for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:649](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L649) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:415](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L415) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:939](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L939) — The verifier for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:549](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L549) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:363](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L363) — The verifier for the final sumcheck step, as an instance of the family-shared check-then-update one-

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:95](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L95) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:173](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L173) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:102](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L102) — The full DP24 ring-switching protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:69](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L69) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:145](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L145) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:89](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L89) — The reduction for the full DP24 ring-switching protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:110](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L110) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:188](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L188) — The full FRI-Binius oracle proof is perfectly complete.
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:153](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L153) — (no docstring)

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:122](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L122) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:71](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L71) — The oracle verifier for the full DP24 ring-switching protocol

### `injective` (3 declarations, 3 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:323](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L323) — A concrete coset FFT domain is injective as a function.
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:152](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L152) — An FFT domain is injective as a function.
- `theorem Interaction.Oracle.NamedContext.Inclusion.injective` [ArkLib/Interaction/Oracle/Resource.lean:229](../../../ArkLib/Interaction/Oracle/Resource.lean#L229) — A name-preserving inclusion is injective.

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:145](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L145) — The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier template
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:247](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L247) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:182](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L182) — The knowledge state function for the `ReduceClaim` reduction.

### `rbrExtractor` (3 declarations, 3 files)

- `def RandomQuery.rbrExtractor` [ArkLib/ProofSystem/Component/RandomQuery.lean:240](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L240) — The round-by-round extractor is trivial since the output witness is `Unit`.
- `def ToyProblem.Impl.IRS.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:361](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L361) — Named executable round-by-round extractor for interleaved RS.
- `def ToyProblem.Spec.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1212](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1212) — The round-by-round extractor: round 0 extracts a relaxed-relation witness by choice, round 1 passes

### `relIn` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relIn` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:386](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L386) — **`relIn` — the ordinary input relation of `QuadEval`**: a weak `VerifiedOpening` for `u` under the
- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:82](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L82) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:45](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L45) — The input relation is that the two oracles are equal.

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:210](../../../ArkLib/Data/Hash/DomainSep.lean#L210) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:515](../../../ArkLib/Data/Hash/DuplexSponge.lean#L515) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:120](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L120) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:61](../../../ArkLib/OracleReduction/Cast.lean#L61) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:93](../../../ArkLib/OracleReduction/Cast.lean#L93) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:115](../../../ArkLib/OracleReduction/Cast.lean#L115) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:204](../../../ArkLib/OracleReduction/Cast.lean#L204) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:39](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L39) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:83](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L83) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L126) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:169](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L169) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:199](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L199) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:42](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L42) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:80](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L80) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:109](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L109) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:140](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L140) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:187](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L187) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:255](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L255) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:359](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L359) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:417](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L417) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:53](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L53) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:88](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L88) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:118](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L118) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:201](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L201) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:271](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L271) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:375](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L375) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:422](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L422) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:409](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L409) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:468](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L468) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:521](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L521) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:34](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L34) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:179](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L179) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:344](../../../ArkLib/OracleReduction/Security/Basic.lean#L344) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:500](../../../ArkLib/OracleReduction/Security/Basic.lean#L500) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:553](../../../ArkLib/OracleReduction/Security/Basic.lean#L553) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:593](../../../ArkLib/OracleReduction/Security/Basic.lean#L593) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:154](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L154) — State-restoration knowledge soundness (w/ straightline extractor). The state-restoration extractor r

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:141](../../../ArkLib/Data/Hash/DomainSep.lean#L141) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:162](../../../ArkLib/Data/Hash/DomainSep.lean#L162) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:96](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L96) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:186](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L186) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:327](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L327) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `soundness` (5 declarations, 2 files)

- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:272](../../../ArkLib/OracleReduction/Security/Basic.lean#L272) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:481](../../../ArkLib/OracleReduction/Security/Basic.lean#L481) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:547](../../../ArkLib/OracleReduction/Security/Basic.lean#L547) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:584](../../../ArkLib/OracleReduction/Security/Basic.lean#L584) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:133](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L133) — State-restoration soundness

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:123](../../../ArkLib/OracleReduction/Cast.lean#L123) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:94](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L94) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:137](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L137) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:205](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L205) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:75](../../../ArkLib/OracleReduction/Cast.lean#L75) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:90](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L90) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:133](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L133) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:201](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L201) — (no docstring)

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L117) — Given a smooth coset FFT domain `ω` of log-order `n`, return its subdomain of log-order `n - i`. The
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:551](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L551) — Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain.
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:64](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L64) — The `i`th subdomain of a smooth FFT domain, obtained by taking the corresponding coset subdomain and
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:142](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L142) — Concrete notation for the `i`th subdomain of a smooth FFT domain.

### `OStmtIn` (3 declarations, 2 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:37](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L37) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:246](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L246) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:345](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L345) — (no docstring)

### `OStmtOut` (3 declarations, 2 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:38](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L38) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:275](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L275) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:348](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L348) — (no docstring)

### `StmtOut` (3 declarations, 2 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:35](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L35) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:274](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L274) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:342](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L342) — (no docstring)

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:428](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L428) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:70](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L70) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:116](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L116) — The Module-SIS advantage.

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/Commitments/Functional/Basic.lean:92](../../../ArkLib/Commitments/Functional/Basic.lean#L92) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:57](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L57) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:167](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L167) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:415](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L415) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:64](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L64) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:110](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L110) — The Module-SIS experiment.

### `extend` (3 declarations, 2 files)

- `def Interaction.Oracle.Access.extend` [ArkLib/Interaction/Oracle/Access.lean:42](../../../ArkLib/Interaction/Oracle/Access.lean#L42) — Add a disjoint query slot for a newly sent oracle message. This is signature extension, not a claim
- `def ProtocolSpec.MessagesUpTo.extend` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:417](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L417) — Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a challen
- `def ProtocolSpec.ChallengesUpTo.extend` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:476](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L476) — Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a messa

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:76](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L76) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:129](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L129) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:186](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L186) — (no docstring)

### `instIsEmptyChallengeIdx` (3 declarations, 2 files)

- `instance SendClaim.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendClaim.lean:70](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L70) — `SendClaim` is a single `P_to_V` message, so it has no challenge rounds. This makes its coordinate-w
- `instance SendWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:64](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L64) — The `SendWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This is what
- `instance SendSingleWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:320](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L320) — The `SendSingleWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This i

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:85](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L85) — Membership in the finset of elements is the same as membership in the coset FFT domain.
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:147](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L147) — Membership in the finset of elements is the same as membership in the concrete coset FFT domain.
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:88](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L88) — Membership in the finset of elements is the same as membership in the FFT domain.

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:71](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L71) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — (no docstring)

### `restrict` (3 declarations, 2 files)

- `abbrev Interaction.Oracle.TypeTree.AccessDecoration.restrict` [ArkLib/Interaction/Oracle/Access.lean:234](../../../ArkLib/Interaction/Oracle/Access.lean#L234) — Restrict a presentation using PolyFun's canonical displayed restriction.
- `abbrev Interaction.Oracle.TypeTree.RoleDecoration.restrict` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:81](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L81) — Restrict roles to the residual tree selected by a structural cursor.
- `abbrev Interaction.Oracle.TypeTree.OracleDecoration.restrict` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:172](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L172) — Restrict oracle interfaces to the residual tree selected by a structural cursor.

### `restrict_comp` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_comp` [ArkLib/Interaction/Oracle/Access.lean:252](../../../ArkLib/Interaction/Oracle/Access.lean#L252) — Restriction composes without introducing another cursor representation.
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_comp` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:99](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L99) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_comp` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:190](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L190) — (no docstring)

### `restrict_down` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_down` [ArkLib/Interaction/Oracle/Access.lean:244](../../../ArkLib/Interaction/Oracle/Access.lean#L244) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_down` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:91](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L91) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_down` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:182](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L182) — (no docstring)

### `restrict_root` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_root` [ArkLib/Interaction/Oracle/Access.lean:239](../../../ArkLib/Interaction/Oracle/Access.lean#L239) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_root` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:86](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L86) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_root` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:177](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L177) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:58](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L58) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:117](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L117) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:174](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L174) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:57](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L57) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:57](../../../ArkLib/OracleReduction/VectorIOR.lean#L57) — The type of indices for challenges in a `VectorSpec`.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:146](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L146) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:39](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L39) — Commitments: row vectors over `Rq Φ`.

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1022](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1022) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:643](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L643) — (no docstring)

### `LiftedWitness` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.LiftedWitness` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:140](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L140) — Hachi Eq. (21)'s lifted witness: the `R^lin` witness `z ∈ Rq^μ` and one quotient polynomial per row
- `structure RingSwitching.Lift.LiftedWitness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:84](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L84) — The lifted witness of `Lift`: the `S`-witness `z` of the linear relation and one **computable** quot

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:52](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L52) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:53](../../../ArkLib/OracleReduction/VectorIOR.lean#L53) — The type of indices for messages in a `VectorSpec`.

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:202](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L202) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:99](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L99) — Output oracle statement: the single combined codeword `f_new := f₁ + γ • f₂ : ι → A`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:209](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L209) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:109](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L109) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `Params` (2 declarations, 2 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:41](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L41) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun

### `Pr_or_le` (2 declarations, 2 files)

- `theorem Probability.Pr_or_le` [ArkLib/Data/Probability/Instances.lean:536](../../../ArkLib/Data/Probability/Instances.lean#L536) — **Union Bound (binary form)** The probability of a disjunction of two events is at most the sum of t
- `theorem ToyProblem.Pr_or_le` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:226](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L226) — Deprecated compatibility name for the general probability union bound.

### `Problem` (2 declarations, 2 files)

- `structure ArkLib.Lattices.SIS.Problem` [ArkLib/Data/Lattices/ModuleSIS.lean:54](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L54) — A generic SIS-style problem: public challenge data `Sample` (e.g. a matrix), a `Solution` type, and
- `structure Interaction.Oracle.Problem` [ArkLib/Interaction/Oracle/Claim.lean:175](../../../ArkLib/Interaction/Oracle/Claim.lean#L175) — A claim-dependent witness relation with an explicit admissibility boundary.

### `Prover` (2 declarations, 2 files)

- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:109](../../../ArkLib/Interaction/Reduction.lean#L109) — A prover performs monadic setup and returns the focal strategy for the selected input.
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:223](../../../ArkLib/OracleReduction/Basic.lean#L223) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `Reduction.execute` (2 declarations, 2 files)

- `def Interaction.Oracle.Reduction.execute` [ArkLib/Interaction/Oracle/Execution.lean:271](../../../ArkLib/Interaction/Oracle/Execution.lean#L271) — Execute the package with arbitrary pure input behavior. This is single-run semantics, not run-derive
- `def Interaction.Reduction.execute` [ArkLib/Interaction/Reduction.lean:146](../../../ArkLib/Interaction/Reduction.lean#L146) — Execute a reduction with PolyFun's canonical two-party runner.

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:94](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L94) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L56) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:235](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L235) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:270](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L270) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `Verifier` (2 declarations, 2 files)

- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:122](../../../ArkLib/Interaction/Reduction.lean#L122) — A verifier returns the counterpart strategy for the selected input and public statement.
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:248](../../../ArkLib/OracleReduction/Basic.lean#L248) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:175](../../../ArkLib/Interaction/Reduction.lean#L175) — Run a focal strategy against an input-indexed verifier.
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:179](../../../ArkLib/OracleReduction/Execution.lean#L179) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `agree` (2 declarations, 2 files)

- `def Code.agree` [ArkLib/Data/CodingTheory/Basic/Distance.lean:175](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L175) — The number of positions at which the two words `u` and `v` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:190](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L190) — Relative `μ`-agreement between words `u` and `v`.

### `append_completeness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:161](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L161) — Sequential composition preserves completeness for guarded verifiers when the prover execution factor
- `theorem OracleReduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:39](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L39) — Oracle reductions with guarded ordinary verifiers compose with the sum of their errors when prover e

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:254](../../../ArkLib/Data/Fin/Basic.lean#L254) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:58](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L58) — (no docstring)

### `append_perfectCompleteness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:177](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L177) — Guarded verifiers compose perfectly when prover execution factors at the seam and the suffix is perf
- `theorem OracleReduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:56](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L56) — Oracle reductions with guarded ordinary verifiers compose perfectly when prover execution factors at

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:68](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L68) — (no docstring)

### `availableContext` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.availableContext` [ArkLib/Interaction/Oracle/Prefix.lean:317](../../../ArkLib/Interaction/Oracle/Prefix.lean#L317) — Input names and available tree-scoped oracle occurrences form disjoint name spaces.
- `def Interaction.Oracle.WorldPhase.availableContext` [ArkLib/Interaction/Oracle/WorldSegments.lean:183](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L183) — The available stable resource schema is determined by this action's concrete prefix.

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:105](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L105) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:79](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L79) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:91](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L91) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:62](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L62) — (no docstring)

### `binding` (2 declarations, 2 files)

- `def Commitment.binding` [ArkLib/Commitments/Functional/Basic.lean:220](../../../ArkLib/Commitments/Functional/Basic.lean#L220) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `theorem KZG.CommitmentScheme.binding` [ArkLib/Commitments/Functional/KZG/Binding.lean:749](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L749) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `biniusProfile` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:68](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L68) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- `def Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L56) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def

### `branchPath` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:224](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L224) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node.
- `def CoordinateWise.SingleRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:193](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L193) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node. Defined separately

### `branchPathOf` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:297](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L297) — The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
- `def CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:268](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L268) — The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which

### `branchTr` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:231](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L231) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.
- `def CoordinateWise.SingleRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L200) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.

### `branch_challenge` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:237](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L237) — Branch `j`'s transcript carries challenge `challenges j` at round 1.
- `theorem CoordinateWise.SingleRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:206](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L206) — Branch `j`'s transcript carries challenge `challenges j` at round 1.

### `branch_mem` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:264](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L264) — Branch `j`'s transcript is one of the star tree's leaf transcripts.
- `theorem CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:233](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L233) — Branch `j`'s transcript is one of the star tree's leaf transcripts.

### `branch_pre` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L249) — Branch `j`'s transcript carries the shared message `v` at round 0.
- `theorem CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:218](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L218) — Branch `j`'s transcript carries the shared message `v` at round 0.

### `branch_relOut_language` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:361](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L361) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- `theorem CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:392](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L392) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp

### `certifiedExtractorError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:687](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L687) — Full extractor-certified error: the spot-check failure probability combined sharply with the executa
- `def ToyProblem.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1361](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1361) — The executable extractor's full fixed-radius certificate.  Unlike `winningSetUpperBound`, its combin

### `certifiedGammaError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:665](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L665) — The certified combination-round error for the executable interleaved-RS extractor.  This is the fini
- `def ToyProblem.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1276](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1276) — The finite nonnegative-real reflection of the executable extractor's canonical affine-line MCA-plus-

### `chalPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:285](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L285) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- `def CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:256](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L256) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.

### `chal_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:182](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L182) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- `theorem CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L147) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.

### `chalsAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:125](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L125) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to
- `def CoordinateWise.SingleRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:90](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L90) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to

### `coe_certifiedGammaError` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:672](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L672) — The certified combination-round error coerces back to its defining MCA-plus-list expression.
- `theorem ToyProblem.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1286](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1286) — `certifiedGammaError` coerces to the exact MCA-plus-list certificate.

### `coeffHom` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:266](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L266) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:294](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L294) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:271](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L271) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:300](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L300) — (no docstring)

### `collect_branch_data` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:445](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L445) — **Extraction core, scalar round.** Validity at the pure verdicts yields the `k` per-branch responses
- `theorem CoordinateWise.SingleRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:473](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L473) — **Extraction core.** A leaf witnessing that is valid *at the verifier's verdicts* yields the per-bra

### `comp_id` (2 declarations, 2 files)

- `theorem Interaction.Oracle.NamedContext.Inclusion.comp_id` [ArkLib/Interaction/Oracle/Resource.lean:255](../../../ArkLib/Interaction/Oracle/Resource.lean#L255) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.comp_id` [ArkLib/Interaction/Oracle/Source.lean:214](../../../ArkLib/Interaction/Oracle/Source.lean#L214) — (no docstring)

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:139](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L139) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:76](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L76) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `constrainedCode` (2 declarations, 2 files)

- `def ReedSolomon.constrainedCode` [ArkLib/Data/CodingTheory/ReedSolomon/Constrained.lean:55](../../../ArkLib/Data/CodingTheory/ReedSolomon/Constrained.lean#L55) — Definition 4.5, WHIR[ACFY24] Constrained Reed-Solomon codes are smooth codes whose decoded `m`-varia
- `def ToyProblem.constrainedCode` [ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean:138](../../../ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean#L138) — **The constrained code** (scalar alphabet `A = F`). Adjoin the linear-constraint value `⟨m, v⟩ = ∑ j

### `contextInclusion` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedRun.contextInclusion` [ArkLib/Interaction/Oracle/PhasedRun.lean:79](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L79) — A boundary's available context embeds into the final context with unchanged stable names.
- `def Interaction.Oracle.TypeTree.ExecutionPrefix.contextInclusion` [ArkLib/Interaction/Oracle/Prefix.lean:340](../../../ArkLib/Interaction/Oracle/Prefix.lean#L340) — Structural extension includes previously available context indices without changing their names. It

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:839](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L839) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:839](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L839) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L818) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:811](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L811) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:848](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L848) — Round-by-round knowledge soundness for the core interaction oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:850](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L850) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:56](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L56) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:101](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L101) — Guruswami-Sudan decoder.  Returns all roots of the GS interpolation polynomial whose evaluation is w

### `domain_implies_2_ne_0` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L117) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/FftDomain/Ops.lean:189](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L189) — (no docstring)

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L114) — The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:164](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L164) — The existence of a nontrivial smooth FFT domain rules out characteristic `2`.

### `domain_implies_neg_x_ne_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:130](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L130) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:205](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L205) — (no docstring)

### `domain_implies_x_ne_neg_x` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:120](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L120) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/FftDomain/Ops.lean:193](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L193) — (no docstring)

### `domain_implies_x_ne_neg_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:124](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L124) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:199](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L199) — (no docstring)

### `done` (2 declarations, 2 files)

- `def Interaction.Oracle.Protocol.done` [ArkLib/Interaction/Oracle/Protocol.lean:47](../../../ArkLib/Interaction/Oracle/Protocol.lean#L47) — Terminal decorated protocol.
- `def Interaction.Oracle.TypeTree.done` [ArkLib/Interaction/Oracle/TypeTree.lean:71](../../../ArkLib/Interaction/Oracle/TypeTree.lean#L71) — Terminal oracle interaction tree.

### `encoder` (2 declarations, 2 files)

- `def ToyProblem.Impl.FRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:161](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L161) — The neutral `s = 32` folded encoder: the degree-`< 2^20` folded Reed–Solomon evaluation map on the `
- `def ToyProblem.Impl.IRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:119](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L119) — Executable `s`-interleaved Reed--Solomon encoder.  Its public alphabet is `Fin s → F`; interleaving

### `encoder_injective` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:184](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L184) — **Injectivity of the folded encoder** (the "code as the injective map"). Mathematically this would f
- `theorem ToyProblem.Impl.IRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:182](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L182) — Below scalar-row saturation, the executable interleaved encoder is injective.

### `encoder_range` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:198](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L198) — **The folded encoder's image is exactly the folded RS code** `FRS[domain, 2^20, 32, foldOmega]`. The
- `theorem ToyProblem.Impl.IRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:148](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L148) — The executable encoder has exactly the canonical interleaved Reed--Solomon code as its range.

### `eq_leaf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:172](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L172) — Shape recovery, level 2: every subtree at the last round is a leaf.
- `theorem CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L137) — Shape recovery, level 2: every subtree at the last round is a leaf.

### `executeCore_closed` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.executeCore_closed` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L125) — Programmatic perfect completeness through the new run-derived relation boundary.
- `theorem Sumcheck.Interaction.MultivariateRound.executeCore_closed` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:176](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L176) — The run-derived closed result of an accepting stage preserves its entire input interface.

### `executeCore_honest` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.executeCore_honest` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:94](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L94) — The actual executor produces the paired honest run, pointwise in the challenge.
- `theorem Sumcheck.Interaction.MultivariateRound.executeCore_honest` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:264](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L264) — Honest execution exports the original polynomial at the actual next statement.

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1017](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1017) — RBR knowledge error for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:638](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L638) — RBR knowledge error for the final sumcheck step

### `flatten` (2 declarations, 2 files)

- `def Interaction.Oracle.WorldSegments.flatten` [ArkLib/Interaction/Oracle/WorldSegments.lean:80](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L80) — Flatten local actions in actual execution order.
- `def ToyProblem.Impl.IRS.flatten` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:91](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L91) — Join `s` rows of length `k / s` into a length-`k` scalar message.

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:223](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L223) — The oracle reduction that is the `i`-th round of Binary Foldfold.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:434](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L434) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fromReindex` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.fromReindex` [ArkLib/Interaction/Oracle/Resource.lean:262](../../../ArkLib/Interaction/Oracle/Resource.lean#L262) — Include an injectively reindexed context in its original context.
- `def Interaction.Oracle.SourceHom.fromReindex` [ArkLib/Interaction/Oracle/Source.lean:222](../../../ArkLib/Interaction/Oracle/Source.lean#L222) — Canonical routing from a reindexed signature into the original source.

### `fullOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:150](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L150) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:185](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L185) — Round-by-round knowledge soundness for the full ring-switching oracle verifier

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:64](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L64) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:101](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L101) — (no docstring)

### `fullRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:140](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L140) — Combined RBR knowledge soundness error for the full protocol
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/General.lean:178](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean#L178) — (no docstring)

### `fullTranscript_branchPathOf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:312](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L312) — The branch path's transcript **is** the branch transcript — definitional on the star tree.
- `theorem CoordinateWise.SingleRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:284](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L284) — The branch path's transcript **is** the branch transcript — definitional on the star tree, since the

### `gamma` (2 declarations, 2 files)

- `def RationalFunctions.HenselNumerators.gamma` [ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean:351](../../../ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean#L351) — The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator sequence f
- `def ToyProblem.Impl.FRS.gamma` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:85](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L85) — The shared high-order generator `γ` of `gamma_exists`.

### `gammaAgreementSet` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:213](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L213) — Maximal column agreement set computed from the fresh challenge and the prover's post-challenge messa
- `def ToyProblem.Spec.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:262](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L262) — The source-faithful maximal agreement set computed after `γ` and `g` are known.

### `gammaAgreementSet_card_of_gammaState` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:229](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L229) — A post-`γ` knowledge state makes the computed maximal interleaved agreement set large.
- `theorem ToyProblem.Spec.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:286](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L286) — A `GammaState` witness makes the computed maximal agreement set large.

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:892](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L892) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:46](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L46) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:931](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L931) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:58](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L58) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:199](../../../ArkLib/Data/Hash/DomainSep.lean#L199) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L132) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `id_comp` (2 declarations, 2 files)

- `theorem Interaction.Oracle.NamedContext.Inclusion.id_comp` [ArkLib/Interaction/Oracle/Resource.lean:252](../../../ArkLib/Interaction/Oracle/Resource.lean#L252) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.id_comp` [ArkLib/Interaction/Oracle/Source.lean:209](../../../ArkLib/Interaction/Oracle/Source.lean#L209) — (no docstring)

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:328](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L328) — A concrete coset FFT domain is injective on every set.
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:156](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L156) — An FFT domain is injective on every set.

### `inl` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.inl` [ArkLib/Interaction/Oracle/Resource.lean:267](../../../ArkLib/Interaction/Oracle/Resource.lean#L267) — Include the left context in a disjoint union.
- `def Interaction.Oracle.SourceHom.inl` [ArkLib/Interaction/Oracle/Source.lean:236](../../../ArkLib/Interaction/Oracle/Source.lean#L236) — Left weakening ignores the additional right environment.

### `inr` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.inr` [ArkLib/Interaction/Oracle/Resource.lean:272](../../../ArkLib/Interaction/Oracle/Resource.lean#L272) — Include the right context in a disjoint union.
- `def Interaction.Oracle.SourceHom.inr` [ArkLib/Interaction/Oracle/Source.lean:243](../../../ArkLib/Interaction/Oracle/Source.lean#L243) — Right weakening ignores the additional left environment.

### `instOutputOracleInterface` (2 declarations, 2 files)

- `instance SendClaim.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendClaim.lean:64](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L64) — (no docstring)
- `instance SendSingleWitness.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendWitness.lean:310](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L310) — (no docstring)

### `lastPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L278) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- `def CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L249) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:99](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L99) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:28](../../../ArkLib/Data/Matrix/Basic.lean#L28) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:250](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L250) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:355](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L355) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:289](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L289) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:449](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L449) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:258](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L258) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:379](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L379) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:325](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L325) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:542](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L542) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:309](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L309) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:505](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L505) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:275](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L275) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:401](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L401) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `logView` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedResult.logView` [ArkLib/Interaction/Oracle/PhasedExecution.lean:69](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L69) — Keep the complete chronological world log paired with the source-run observations.
- `def Interaction.Oracle.PhasedRun.logView` [ArkLib/Interaction/Oracle/PhasedRun.lean:53](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L53) — All paired source observations and the complete world log.

### `map` (2 declarations, 2 files)

- `def Fin.map` [ArkLib/Data/Fin/Sigma.lean:509](../../../ArkLib/Data/Fin/Sigma.lean#L509) — (no docstring)
- `def Interaction.Oracle.Terminal.map` [ArkLib/Interaction/Oracle/Terminal.lean:39](../../../ArkLib/Interaction/Oracle/Terminal.lean#L39) — Transform accepted claims, preserving rejection and faults.

### `mapSource` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.mapSource` [ArkLib/Interaction/Oracle/Claim.lean:77](../../../ArkLib/Interaction/Oracle/Claim.lean#L77) — Route the source of a claim without altering its public statement.
- `def Interaction.Oracle.VirtualOracle.mapSource` [ArkLib/Interaction/Oracle/Virtual.lean:123](../../../ArkLib/Interaction/Oracle/Virtual.lean#L123) — Map the source along a coherent polynomial source morphism.

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:958](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L958) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:437](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L437) — (no docstring)

### `mem_gammaAgreementSet` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:220](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L220) — (no docstring)
- `theorem ToyProblem.Spec.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:268](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L268) — (no docstring)

### `minRelHammingDistCode_le_one` (2 declarations, 2 files)

- `lemma Code.minRelHammingDistCode_le_one` [ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean:642](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean#L642) — The minimum relative Hamming distance is at most `1`; the lower bound `0 ≤ δᵣ C` is automatic in `ℚ≥
- `theorem ToyProblem.minRelHammingDistCode_le_one` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:171](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L171) — Deprecated compatibility name for the general coding-theory bound.

### `observe` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedResult.observe` [ArkLib/Interaction/Oracle/PhasedExecution.lean:61](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L61) — Forget the world segmentation while retaining all source-run observations.
- `def Interaction.Oracle.Terminal.observe` [ArkLib/Interaction/Oracle/TerminalMeasure.lean:31](../../../ArkLib/Interaction/Oracle/TerminalMeasure.lean#L31) — Observe terminal outcomes after explicitly assigning execution missing mass a named fault.

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:275](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L275) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:303](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L303) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `oracleVerifier_rbrKnowledgeSoundnessWorstCase` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.oracleVerifier_rbrKnowledgeSoundnessWorstCase` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:986](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L986) — Existential worst-case RBR knowledge soundness, retained as a compatibility corollary of the exact-o
- `theorem ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1377](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1377) — Worst-case-per-fixed-prefix round-by-round knowledge soundness of the toy protocol in the alphabet-g

### `oracles` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.oracles` [ArkLib/Interaction/Oracle/Prefix.lean:198](../../../ArkLib/Interaction/Oracle/Prefix.lean#L198) — Oracle interfaces restricted to the selected residual, preserving branch dependence.
- `abbrev Interaction.Oracle.Protocol.oracles` [ArkLib/Interaction/Oracle/Protocol.lean:43](../../../ArkLib/Interaction/Oracle/Protocol.lean#L43) — Interfaces at oracle nodes; public nodes carry no interface.

### `outputIndexEmbedding` (2 declarations, 2 files)

- `def SendClaim.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:96](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L96) — The oracle verifier for `SendClaim` is a **pure pass-through**: it returns the statement and exposes
- `def SendSingleWitness.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:345](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L345) — The index embedding that exposes every input oracle and the single witness message as output oracles

### `outputOracle` (2 declarations, 2 files)

- `def Sumcheck.Interaction.SingleRound.outputOracle` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:30](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L30) — The output oracle routes queries to the original input polynomial.
- `def Sumcheck.Interaction.MultivariateRound.outputOracle` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:39](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L39) — The output oracle retains the original input behavior.

### `outputRelationFor` (2 declarations, 2 files)

- `def ToyProblem.Spec.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:290](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L290) — The IOR-shaped **fixed-encoding** *relaxed* output relation. The soundness statement of L6.6/6.8 is
- `def ToyProblem.SimplifiedIOR.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:122](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L122) — The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of the simplified IOR. Bundles the po

### `outputSimulation` (2 declarations, 2 files)

- `def BatchedFri.Spec.BatchingRound.outputSimulation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:244](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L244) — Virtual implementation of the random-linear-combination codeword.  Every downstream coordinate query
- `def ToyProblem.SimplifiedIOR.outputSimulation` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:271](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L271) — Virtual implementation of the combined C6.9 output oracle.

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:262](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L262) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:94](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L94) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:210](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L210) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:64](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L64) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean:74](../../../ArkLib/ProofSystem/RingSwitching/Packing/Spec.lean#L74) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:114](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L114) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `package` (2 declarations, 2 files)

- `def CoordinateWise.CommittedScalar.package` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L278) — Bundled committed scalar phase, ready for CWSS composition. This lands in the **pure, escape-aware**
- `def RingSwitching.Lift.package` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:327](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L327) — `Lift` as a composable escape-aware CWSS package. Computable: the purity field carries the verdict f

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean:194](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean#L194) — **Unconditional perfect correctness with Hachi's balanced decomposition.** Both message and inner de
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean:37](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean#L37) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `phases` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedRun.phases` [ArkLib/Interaction/Oracle/PhasedRun.lean:57](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L57) — Local actions and their concrete stopping boundaries, beginning with setup.
- `def Interaction.Oracle.WorldSegments.phases` [ArkLib/Interaction/Oracle/WorldSegments.lean:96](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L96) — List actual local actions with their full stopping boundaries. Sender actions occur before crossing

### `phases_flatten` (2 declarations, 2 files)

- `theorem Interaction.Oracle.PhasedRun.phases_flatten` [ArkLib/Interaction/Oracle/PhasedRun.lean:62](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L62) — The chronological regions account for the whole log without deleting duplicate queries.
- `theorem Interaction.Oracle.WorldSegments.phases_flatten` [ArkLib/Interaction/Oracle/WorldSegments.lean:113](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L113) — Decorating segments with concrete protocol boundaries preserves their chronological log.

### `phases_reached` (2 declarations, 2 files)

- `theorem Interaction.Oracle.PhasedRun.phases_reached` [ArkLib/Interaction/Oracle/PhasedRun.lean:67](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L67) — Every action boundary, including setup, extends to the same complete concrete path.
- `theorem Interaction.Oracle.WorldSegments.phases_reached` [ArkLib/Interaction/Oracle/WorldSegments.lean:135](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L135) — Every recorded action boundary is a concrete prefix of this same complete execution, including agree

### `prepend` (2 declarations, 2 files)

- `def Interaction.Oracle.WorldSegments.prepend` [ArkLib/Interaction/Oracle/WorldSegments.lean:88](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L88) — Prefix labels on a residual phase are lifted through the already crossed concrete edge.
- `def SumcheckDomain.prepend` [ArkLib/ProofSystem/Sumcheck/Domain.lean:98](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L98) — Prepend a coordinate with domain `D₀` in front of an existing `k`-coordinate domain family, yielding

### `projectToMidSumcheckPolyWithParam` (2 declarations, 2 files)

- `def Sumcheck.Structured.projectToMidSumcheckPolyWithParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:164](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L164) — Generic projection `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = H₀(r₀, …, rᵢ₋₁, Xᵢ, …, X_{ℓ-1})` for `H₀ = P · Q(t)`.
- `def Sumcheck.Structured.Prismalinear.projectToMidSumcheckPolyWithParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:103](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L103) — Generic prismalinear projection `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = H₀(r₀, …, rᵢ₋₁, Xᵢ, …, X_{ℓ-1})` for `H₀ = P

### `prover_runToRound_last` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_runToRound_last` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:343](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L343) — **Honest execution of both rounds.** Running the Figure-3 prover to the last round draws the challen
- `lemma CoordinateWise.CommittedScalar.prover_runToRound_last` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:337](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L337) — **Honest execution of both rounds.** Running the prover shell to the last round appends the commitme

### `prover_run_eq` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_run_eq` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:387](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L387) — **The honest prover's run in closed form.** `prover_runToRound_last` followed by `output`: the prove
- `lemma CoordinateWise.CommittedScalar.prover_run_eq` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:371](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L371) — **The honest prover's run in closed form**: draw `c`, then emit the transcript `⟨K.com w, c⟩`, the o

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:156](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L156) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:818](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L818) — (no docstring)

### `queryInput` (2 declarations, 2 files)

- `def BatchedFri.Spec.BatchingRound.queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:141](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L141) — Query one batched input codeword in the verifier's full oracle context.
- `def ToyProblem.SimplifiedIOR.queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:250](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L250) — Query an input codeword at one coordinate in the full verifier oracle context.

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:318](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L318) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:940](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L940) — (no docstring)

### `quotient` (2 declarations, 2 files)

- `def Polynomial.Bivariate.quotient` [ArkLib/Data/Polynomial/Bivariate.lean:140](../../../ArkLib/Data/Polynomial/Bivariate.lean#L140) — The bivariate quotient polynomial.
- `def RingSwitching.Lift.Presentation.quotient` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:297](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L297) — The **honest quotient** of row `i`: the explicit polynomial `ρ := (rowSum − rep yᵢ) /ₘ φ` that witne

### `rbrKnowledgeStateFunction` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:896](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L896) — Knowledge-state function paired with the executable interleaved-RS round-by-round extractor.  This i
- `def ToyProblem.Spec.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1230](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1230) — The round-by-round knowledge state function: relaxed-relation membership at round 0, `GammaState` af

### `rbrWitMid` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:354](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L354) — Intermediate witness types for the executable round-by-round extractor.
- `def ToyProblem.Spec.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1105](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1105) — L6.8 intermediate witness types: input witness at round 0, the γ-round candidate message during roun

### `readChallenges` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L137) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- `def CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:102](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L102) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str

### `readChallenges_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:167](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L167) — The round-1 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L132) — The round-1 reader computes on the star tree.

### `readPre` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:119](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L119) — Read the round-0 message (the pre-challenge prover message) off a full tree.
- `def CoordinateWise.SingleRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:83](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L83) — Read the round-0 message (the pre-challenge carrier commitment) off a full tree.

### `readPre_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:162](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L162) — The round-0 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:127](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L127) — The round-0 reader computes on the star tree.

### `reduction_run_support` (2 declarations, 2 files)

- `lemma CoordinateWise.CommittedScalar.reduction_run_support` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:390](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L390) — **Honest-run characterization.** Every element of the support of an honest run is a success determin
- `theorem ReduceClaim.reduction_run_support` [ArkLib/ProofSystem/Component/ReduceClaim.lean:136](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L136) — **The `ReduceClaim` reduction's honest run, in closed form.** A zero-round reduction draws nothing a

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L197) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:998](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L998) — (no docstring)

### `refl` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceEquiv.refl` [ArkLib/Interaction/Oracle/Source.lean:377](../../../ArkLib/Interaction/Oracle/Source.lean#L377) — Identity equivalence.
- `def ProtocolSpec.Equiv.refl` [ArkLib/OracleReduction/Equiv.lean:97](../../../ArkLib/OracleReduction/Equiv.lean#L97) — (no docstring)

### `relaxedRelationFor_iff_exists_outputRelationFor` (2 declarations, 2 files)

- `theorem ToyProblem.Spec.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:316](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L316) — The language-level relaxed relation `RelaxedRelationFor` is precisely the existential closure of the
- `theorem ToyProblem.SimplifiedIOR.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:132](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L132) — The language-level one-word relaxed relation is precisely the existential closure of the witness-bea

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:93](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L93) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:24](../../../ArkLib/Data/Matrix/Basic.lean#L24) — (no docstring)

### `roles` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.roles` [ArkLib/Interaction/Oracle/Prefix.lean:193](../../../ArkLib/Interaction/Oracle/Prefix.lean#L193) — Roles restricted to the exact residual selected by this prefix.
- `abbrev Interaction.Oracle.Protocol.roles` [ArkLib/Interaction/Oracle/Protocol.lean:39](../../../ArkLib/Interaction/Oracle/Protocol.lean#L39) — Roles at public nodes; oracle nodes are implicitly sender-owned.

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:184](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L184) — (no docstring)
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:312](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L312) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rowSum` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.rowSum` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:452](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L452) — Mathlib view of `cRowSum`, retained for degree and root-counting proofs.
- `def RingSwitching.Lift.Presentation.rowSum` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:246](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L246) — The `i`-th lifted row's left-hand side `∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) ∈ R[X]`, on the semantics of canonical r

### `seqCompose_completeness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.seqCompose_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean:45](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean#L45) — Pure prover outputs and guarded verifiers compose with the sum of the component errors when every co
- `theorem OracleReduction.seqCompose_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:77](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L77) — Pure prover outputs and guarded ordinary verifiers compose with the sum of the component errors when

### `seqCompose_perfectCompleteness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean:78](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean#L78) — Pure prover outputs and guarded verifiers preserve perfect completeness of a finite sequence when ev
- `theorem OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:103](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L103) — Pure prover outputs and guarded ordinary verifiers preserve perfect completeness of a finite oracle-

### `simulateQ_queryInput` (2 declarations, 2 files)

- `theorem BatchedFri.Spec.BatchingRound.simulateQ_queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:149](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L149) — (no docstring)
- `theorem ToyProblem.SimplifiedIOR.simulateQ_queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:259](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L259) — (no docstring)

### `simulate_challenge` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.simulate_challenge` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:196](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L196) — The source interpreter forwards challenge effects without reordering or interpreting them.
- `theorem Sumcheck.Interaction.MultivariateRound.simulate_challenge` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:210](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L210) — Interpreting resource reads leaves the ambient challenge effect unchanged.

### `simulate_sumQueries` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.MultivariateRound.simulate_sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:99](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L99) — Sum queries evaluate exactly the sent message, independently of the input behavior.
- `theorem Sumcheck.Interaction.SingleRound.simulate_sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:96](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L96) — Reading a list of sent evaluations computes exactly their mathematical sum.

### `simulate_terminal` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.MultivariateRound.simulate_terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:119](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L119) — The actual terminal computation reads its next target from the sent message.
- `theorem Sumcheck.Interaction.SingleRound.simulate_terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:114](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L114) — The terminal program checks and evaluates the sent polynomial.

### `spec` (2 declarations, 2 files)

- `abbrev Interaction.Oracle.OracleFamily.spec` [ArkLib/Interaction/Oracle/Virtual.lean:43](../../../ArkLib/Interaction/Oracle/Virtual.lean#L43) — The dependent query signature of the explicit interfaces.
- `def OracleInterface.spec` [ArkLib/OracleReduction/OracleInterface.lean:71](../../../ArkLib/OracleReduction/OracleInterface.lean#L71) — (no docstring)

### `subgroupUnit` (2 declarations, 2 files)

- `def Domain.CosetFftDomain.subgroupUnit` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:101](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L101) — The subgroup element of a concrete coset domain at an additive index.
- `def Domain.FftDomain.subgroupUnit` [ArkLib/Data/Domain/FftDomain/Defs.lean:63](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L63) — The subgroup element of an FFT domain at an additive index.

### `subgroupUnit_add` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_add` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:109](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L109) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_add` [ArkLib/Data/Domain/FftDomain/Defs.lean:71](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L71) — (no docstring)

### `subgroupUnit_neg` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:115](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L115) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/FftDomain/Defs.lean:76](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L76) — (no docstring)

### `subgroupUnit_zero` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:105](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L105) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/FftDomain/Defs.lean:67](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L67) — (no docstring)

### `subst` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.subst` [ArkLib/Interaction/Oracle/Claim.lean:92](../../../ArkLib/Interaction/Oracle/Claim.lean#L92) — Substitute an upstream virtual view into the downstream claim's programs.
- `def Interaction.Oracle.VirtualOracle.subst` [ArkLib/Interaction/Oracle/Virtual.lean:150](../../../ArkLib/Interaction/Oracle/Virtual.lean#L150) — Compose a derived interface with a downstream view of that interface.

### `substWithSuffix` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.substWithSuffix` [ArkLib/Interaction/Oracle/Claim.lean:107](../../../ArkLib/Interaction/Oracle/Claim.lean#L107) — Substitute the middle interface while retaining independent suffix resources.
- `def Interaction.Oracle.VirtualOracle.substWithSuffix` [ArkLib/Interaction/Oracle/Virtual.lean:166](../../../ArkLib/Interaction/Oracle/Virtual.lean#L166) — Substitution with additional downstream sources kept available.

### `sumQueries` (2 declarations, 2 files)

- `def Sumcheck.Interaction.MultivariateRound.sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:47](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L47) — Query and sum the sent message over the domain in list order.
- `def Sumcheck.Interaction.SingleRound.sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L56) — Sum the sent polynomial's answers in the supplied domain order.

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:620](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L620) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:263](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L263) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:673](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L673) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:335](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L335) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:415](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L415) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:252](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L252) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:761](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L761) — Round-by-round knowledge soundness for the sumcheck fold oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:459](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L459) — (no docstring)

### `symm` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceEquiv.symm` [ArkLib/Interaction/Oracle/Source.lean:381](../../../ArkLib/Interaction/Oracle/Source.lean#L381) — Reverse an equivalence.
- `def ProtocolSpec.Equiv.symm` [ArkLib/OracleReduction/Equiv.lean:102](../../../ArkLib/OracleReduction/Equiv.lean#L102) — (no docstring)

### `terminal` (2 declarations, 2 files)

- `def Sumcheck.Interaction.MultivariateRound.terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L56) — The terminal statement uses the sent polynomial's evaluation and extends the prefix.
- `def Sumcheck.Interaction.SingleRound.terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:65](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L65) — Query-dependent terminal output; a failed sum check is an explicit rejection.

### `toORelOut` (2 declarations, 2 files)

- `def SendClaim.toORelOut` [ArkLib/ProofSystem/Component/SendClaim.lean:180](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L180) — The output relation of `SendClaim`: the input relation (read off the pass-through oracles at `inl`)
- `def SendSingleWitness.toORelOut` [ArkLib/ProofSystem/Component/SendWitness.lean:433](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L433) — (no docstring)

### `toPoly_injective` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.toPoly_injective` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:46](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L46) — `CPolynomial.toPoly` is injective (it is the forward map of a ring isomorphism).
- `theorem CompPoly.CPolynomial.toPoly_injective` [ArkLib/ToCompPoly/Univariate/Basic.lean:357](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L357) — `toPoly` is injective: it is the forward map of the ring equivalence `CPolynomial.ringEquiv`. This i

### `toPolynomial` (2 declarations, 2 files)

- `def ArkLib.Lattices.Hachi.toPolynomial` [ArkLib/Commitments/Functional/Hachi/EvalSplit.lean:202](../../../ArkLib/Commitments/Functional/Hachi/EvalSplit.lean#L202) — Inverse reshape of `toMatrix`: read the `2 ^ nl × 2 ^ nh` matrix back into the `2 ^ (nl + nh)` coeff
- `def ReedSolomon.toPolynomial` [ArkLib/Data/CodingTheory/ReedSolomon.lean:679](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L679) — The linear map that maps a Reed-Solomon codeword to its associated polynomial.

### `topMsgAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:108](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L108) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- `def CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:72](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L72) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit

### `transitionStraightlineExtractor` (2 declarations, 2 files)

- `def ToyProblem.Spec.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean:44](../../../ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean#L44) — Turn a deterministic transition algorithm reading `(statement, γ, g)` into the straightline extracto
- `def ToyProblem.SimplifiedIOR.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:335](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L335) — Turn a deterministic C6.9 transition algorithm into the straightline extractor shape used by ArkLib'

### `tree2` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:156](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L156) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- `def CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:121](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L121) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves

### `tree_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:216](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L216) — **Shape recovery.** Every full tree of the two-round scalar `pSpecScalar` is a star tree — one messa
- `theorem CoordinateWise.SingleRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:183](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L183) — **Shape recovery.** Every full tree of the two-round `pSpec` is a star tree. This is the rewrite tha

### `tree_shape_aux` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L200) — Shape recovery, level 0: every tree at round 0 is a `tree2`.
- `theorem CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:165](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L165) — Shape recovery, level 0: every tree at round 0 is a `tree2`.

### `unflatten` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.unflatten` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean:117](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean#L117) — Un-flatten a row-major block vector into blocks — the inverse of `PolyVec.flattenBlocks`.
- `def ToyProblem.Impl.IRS.unflatten` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:86](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L86) — Split a length-`k` scalar message into `s` rows of length `k / s`.

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:125](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L125) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:84](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L84) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifierLocalView` (2 declarations, 2 files)

- `def Interaction.Oracle.LoggedRun.verifierLocalView` [ArkLib/Interaction/Oracle/LoggedRun.lean:52](../../../ArkLib/Interaction/Oracle/LoggedRun.lean#L52) — Verifier observations derived from the enclosing execution's log, without replay. This view contains
- `def Interaction.Oracle.TerminalRun.verifierLocalView` [ArkLib/Interaction/Oracle/TerminalRun.lean:110](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L110) — The local view is read from this result's source log, never obtained by replay.

### `verifierPureForm` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifierPureForm` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:446](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L446) — **The pass-through verifier's purity as data** (`Verifier.PureForm`): the verdict is the pass-throug
- `def CoordinateWise.CommittedScalar.verifierPureForm` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:246](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L246) — The committed-scalar verifier's purity **as data**: its verdict is the input statement extended by t

### `verifier_coordinateWiseSpecialSoundWith` (2 declarations, 2 files)

- `theorem ReduceClaim.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:250](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L250) — **Coordinate-wise special soundness of `ReduceClaim`, named form.** The verifier is pure with no cha
- `theorem SendWitness.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:168](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L168) — **Coordinate-wise special soundness of `SendWitness`, named form.** The verifier has no challenge ro

### `verify` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:50](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L50) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/Commitments/Ordinary/SimpleRO.lean:53](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L53) — Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash.

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:846](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L846) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:428](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L428) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `Pr_eq_zero_of_forall_not` (2 declarations, 2 files)

- `lemma ToyProblem.Spec.Pr_eq_zero_of_forall_not` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1085](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1085) — `Pr_{x ← D}[P x] = 0` for a never-satisfied predicate `P`.
- `theorem ToyProblem.Spec.Pr_eq_zero_of_forall_not` [ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean:58](../../../ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean#L58) — A predicate false at every point has probability zero.

## Near-duplicate docstrings (Jaccard ≥ 0.85, 79 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitKState` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:654](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L654) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:267](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L267)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:675](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L675) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:296](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L296)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1017](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1017) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:638](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L638)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1017](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1017) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:412](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L412)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1090](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1090) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1090](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1090) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:464](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L464)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:987](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L987) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:603](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L603)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:987](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L987) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:382](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L382)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1001](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1001) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:620](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L620)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1001](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1001) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:397](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L397)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1111) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:746](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L746)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1111) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:487](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L487)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1028](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1028) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:649](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L649)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1028](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1028) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:415](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L415)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:379](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L379) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:267](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L267)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:400](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L400) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:296](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L296)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:828](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L828) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:267](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L267)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:852](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L852) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:296](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L296)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:95](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L95) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:173](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L173)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:69](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L69) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:145](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L145)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:122](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L122)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:846](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L846) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean:428](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean#L428)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:68](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L68) vs `Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L56)
    - a: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
    - b: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:638](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L638) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:412](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L412)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:464](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L464)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:603](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L603) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:382](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L382)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:620](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L620) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:397](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L397)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:746](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L746) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:487](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L487)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:649](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L649) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean:415](../../../ArkLib/ProofSystem/RingSwitching/Packing/SumcheckPhase.lean#L415)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:264](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L264) vs `CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:233](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L233)
    - a: Branch `j`'s transcript is one of the star tree's leaf transcripts.
    - b: Branch `j`'s transcript is one of the star tree's leaf transcripts.
- **1.00** `CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L249) vs `CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:218](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L218)
    - a: Branch `j`'s transcript carries the shared message `v` at round 0.
    - b: Branch `j`'s transcript carries the shared message `v` at round 0.
- **1.00** `CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:361](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L361) vs `CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:392](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L392)
    - a: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
    - b: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- **1.00** `CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:285](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L285) vs `CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:256](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L256)
    - a: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
    - b: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- **1.00** `CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:182](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L182) vs `CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L147)
    - a: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
    - b: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- **1.00** `CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:172](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L172) vs `CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L137)
    - a: Shape recovery, level 2: every subtree at the last round is a leaf.
    - b: Shape recovery, level 2: every subtree at the last round is a leaf.
- **1.00** `CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L278) vs `CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L249)
    - a: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
    - b: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- **1.00** `CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L137) vs `CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:102](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L102)
    - a: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
    - b: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- **1.00** `CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:167](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L167) vs `CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L132)
    - a: The round-1 reader computes on the star tree.
    - b: The round-1 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:162](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L162) vs `CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:127](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L127)
    - a: The round-0 reader computes on the star tree.
    - b: The round-0 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:108](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L108) vs `CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:72](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L72)
    - a: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
    - b: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- **1.00** `CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:156](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L156) vs `CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:121](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L121)
    - a: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
    - b: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- **1.00** `CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L200) vs `CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:165](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L165)
    - a: Shape recovery, level 0: every tree at round 0 is a `tree2`.
    - b: Shape recovery, level 0: every tree at round 0 is a `tree2`.
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Algebra.lean:108](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L108) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Binding.lean:170](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L170)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Algebra.lean:64](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L64) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Binding.lean:160](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L160)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `Interaction.Oracle.PhasedRun.terminalClosed_eq_reject_iff` [ArkLib/Interaction/Oracle/PhasedRun.lean:297](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L297) vs `Interaction.Oracle.TerminalRun.closed_eq_reject_iff` [ArkLib/Interaction/Oracle/TerminalRun.lean:87](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L87)
    - a: Closing cannot create or erase verifier rejection.
    - b: Closing cannot create or erase verifier rejection.
- **1.00** `Interaction.Oracle.executeStrategiesLogged` [ArkLib/Interaction/Oracle/LoggedExecution.lean:105](../../../ArkLib/Interaction/Oracle/LoggedExecution.lean#L105) vs `Interaction.Oracle.executeStrategiesPhased` [ArkLib/Interaction/Oracle/PhasedExecution.lean:80](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L80)
    - a: Execute restricted strategies in the paired runner's ownership order, logging each verifier local ac
    - b: Execute restricted strategies in the paired runner's ownership order, logging each verifier local ac
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/Commitments/Functional/KZG/Binding.lean:651](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L651) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:538](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L538)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:275](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L275) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:401](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L401)
    - a: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
    - b: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- **1.00** `Prover.processRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:81](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L81) vs `Prover.processRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L171)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:117](../../../ArkLib/OracleReduction/Execution.lean#L117) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L203)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:117](../../../ArkLib/OracleReduction/Execution.lean#L117) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:103](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L103)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:103](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L103) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L203)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Reduction.append_completeness_of_prover_factorization` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:101](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L101) vs `Reduction.append_completeness_of_guarded_prover_factorization` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:120](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L120)
    - a: Quantitative completeness from equality of simulated prover programs at every input and initial shar
    - b: Quantitative completeness from equality of simulated prover programs at every input and initial shar
- **1.00** `Verifier.coordinateWiseSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:281](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L281) vs `Verifier.treeSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean:796](../../../ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L796)
    - a: The existential notion is definitionally the existential closure of the named one.
    - b: The existential notion is definitionally the existential closure of the named one.
- **1.00** `coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:798](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L798) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:787](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L787)
    - a: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L818) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:811](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L811)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **1.00** `coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:782](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L782) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:767](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L767)
    - a: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:848](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L848) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:850](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L850)
    - a: Round-by-round knowledge soundness for the core interaction oracle verifier
    - b: Round-by-round knowledge soundness for the core interaction oracle verifier
- **1.00** `sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:673](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L673) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:811](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L811)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **0.94** `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l1Norm_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:320](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L320) vs `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l2NormSq_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean:311](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean#L311)
    - a: A ring element with zero centered `ℓ₁` norm is `0`: every centered coefficient representative below
    - b: A ring element with zero centered squared `ℓ₂` norm is `0`: every centered coefficient representativ
- **0.94** `Reduction.append_completeness_of_pure_verifiers` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:147](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L147) vs `Reduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:161](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L161)
    - a: Sequential composition preserves completeness for pure verifiers when the prover execution factors a
    - b: Sequential composition preserves completeness for guarded verifiers when the prover execution factor
- **0.88** `Reduction.append_perfectCompleteness_of_pure_verifiers` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:163](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L163) vs `Reduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:177](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L177)
    - a: Pure verifiers compose perfectly when prover execution factors at the seam and the suffix is perfect
    - b: Guarded verifiers compose perfectly when prover execution factors at the seam and the suffix is perf
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:593](../../../ArkLib/OracleReduction/Security/Basic.lean#L593) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:809](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L809)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:593](../../../ArkLib/OracleReduction/Security/Basic.lean#L593) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:738](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L738)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:500](../../../ArkLib/OracleReduction/Security/Basic.lean#L500) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:809](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L809)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:500](../../../ArkLib/OracleReduction/Security/Basic.lean#L500) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:738](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L738)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:489](../../../ArkLib/OracleReduction/Security/Basic.lean#L489) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:809](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L809)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:489](../../../ArkLib/OracleReduction/Security/Basic.lean#L489) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:738](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L738)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `Reduction.completeness_of_pure_states` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:82](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L82) vs `Reduction.completeness_of_guarded_states` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:101](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L101)
    - a: Completeness from every deterministic oracle state implies completeness from any initial state distr
    - b: Completeness from every deterministic oracle state implies completeness from any initial state distr
- **0.87** `ArkLib.Lattices.Ajtai.InnerOuter.partialEvalExtractor` [ArkLib/Commitments/Functional/Hachi/Recursion/PartialEval.lean:191](../../../ArkLib/Commitments/Functional/Hachi/Recursion/PartialEval.lean#L191) vs `ArkLib.Lattices.Ajtai.InnerOuter.handoffExtractor` [ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean:183](../../../ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean#L183)
    - a: **The partial-evaluation extraction algorithm.** **Sorried** — this def is the extraction *algorithm
    - b: **The trace-handoff extraction algorithm.** **Sorried** — this def is the extraction *algorithm* its
- **0.86** `CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:297](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L297) vs `CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:268](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L268)
    - a: The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
    - b: The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which
- **0.86** `Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L114) vs `Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:164](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L164)
    - a: The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
    - b: The existence of a nontrivial smooth FFT domain rules out characteristic `2`.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:584](../../../ArkLib/OracleReduction/Security/Basic.lean#L584) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:800](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L800)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:584](../../../ArkLib/OracleReduction/Security/Basic.lean#L584) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:729](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L729)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:758](../../../ArkLib/OracleReduction/Security/Basic.lean#L758) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:887](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L887)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:481](../../../ArkLib/OracleReduction/Security/Basic.lean#L481) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:800](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L800)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:481](../../../ArkLib/OracleReduction/Security/Basic.lean#L481) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:729](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L729)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:695](../../../ArkLib/OracleReduction/Security/Basic.lean#L695) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:887](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L887)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:54](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L54) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L40)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X

